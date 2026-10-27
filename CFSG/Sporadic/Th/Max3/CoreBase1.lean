
module

public import CFSG.Sporadic.Th.Max3.CoreBase
import all CFSG.Sporadic.Th.Max3.CoreBase

public import CFSG.Sporadic.Th.Max3.Data

@[expose] public section

namespace CFSG.Sporadic.Th.Max3

open CFSG.Certificates

theorem nf_eq_generic
    (s : ZMod 2) (v : Fin 8 → ZMod 2) : nf s v = ExtraspecialNF.nf z q s v :=
  rfl

private theorem nf_pow_val
    (s : ZMod 2) (w : Fin 8 → ZMod 2) (e : ZMod 2) :
    nf s w ^ e.val = nf (e * s) fun k => e * w k := by
  rcases ExtraspecialNF.zmod_two_cases e with rfl | rfl
  · simp only [ZMod.val_zero, pow_zero, zero_mul, nf_eq_generic]
    exact (ExtraspecialNF.nf_zero_zero z q).symm
  · simp [ExtraspecialNF.val_one_two]

end CFSG.Sporadic.Th.Max3
