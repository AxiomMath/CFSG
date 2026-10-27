
module

public import CFSG.CGT.T75M23.N7ModelInputs
public import CFSG.CGT.T75M23.N7Group
import Certificates.Kernel.T75M23.N7KGlue

public section

open CFSG.CGT.T75M23 CFSG.KC.N7K CFSG.KC.TabWord.M23 CFSG.Sporadic.Th

namespace Certificates

open CFSG.CGT.T75M23 in
theorem certificate271011 : (n7InvCheck = true) ∧ (n7RelCheck = true) ∧
    (∀ w w' : List (Fin 6 × Bool), n7Tab w = n7Tab w' → n7 w = n7 w') := by
  have hinj : Function.Injective (phiK n7InvCheck_eq_true n7RelCheck_eq_true) := by
    intro x y hxy
    obtain ⟨a, ha, k, hk, rfl⟩ := n7_surj' x
    obtain ⟨b, hb, l, hl, rfl⟩ := n7_surj' y
    rw [phiK_n7, phiK_n7] at hxy
    have key := img_injective letterRd_NL n7InvCheck_eq_true
      Certificates.certificate271010.2.1 n7k_ok
    have e := @key (⟨a, ha⟩, ⟨k, hk⟩) (⟨b, hb⟩, ⟨l, hl⟩) hxy
    simp only [Prod.mk.injEq, Fin.mk.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    rfl
  refine ⟨n7InvCheck_eq_true, n7RelCheck_eq_true, fun w w' h => hinj ?_⟩
  rw [phiK_n7, phiK_n7]
  refine eq_of_rep_eq (rep_img n7InvCheck_eq_true w) ?_
  rw [h]
  exact rep_img n7InvCheck_eq_true w'

end Certificates
