module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.Defs

namespace CFSG
end CFSG
open CFSG

open scoped commutatorElement

section Main

public theorem CFSG.lemma_4_2_b {G : Type*} [Group G] {x y : G} (n : ℕ) (hn : 1 < n)
    (hcomm : ⁅x, y⁆ ∈ Subgroup.center G) :
    (x * y) ^ n = x ^ n * y ^ n * ⁅y, x⁆ ^ (Nat.choose n 2) := by
  let _ := hn
  have hcomm' : ⁅y, x⁆ ∈ Subgroup.center G := by
    simpa [commutatorElement_inv] using (Subgroup.center G).inv_mem hcomm
  simpa using mul_pow_eq_pow_mul_commutator_choose_of_mem_center
    (x := x) (y := y) hcomm' n

end Main
