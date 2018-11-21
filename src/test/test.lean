import command.where

section
end

#where

namespace hi

variables (C : ℕ)
include C

#where

end hi

namespace hi.yo

variables (C : ℕ)

def b_fn (k : ℤ) : unit := let C := C in ()

def a_fn : unit := let C := C in ()

#where

end hi.yo
