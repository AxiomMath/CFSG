
module

public import CFSG.Quasithin.Background.E2TwoProofSporJ1Base
import all CFSG.Quasithin.Background.E2TwoProofSporJ1Base

public import CFSG.Quasithin.Background.E2TwoProofSporGen
public import CFSG.Quasithin.Background.E2TwoProofSporJ1Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRep
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatPt
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporLatO2
public import CFSG.Sporadic.J1.Simple
public import CFSG.Sporadic.Schreier.J1Outer
public import Certificates.Certificate7124
public import CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat

namespace E2P

namespace SporB

section J1

open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.Quasithin.E2P.SporB.J1Lat CFSG.Sporadic.J1

section Over

noncomputable def j1Y (j : ℕ) : Subgroup ↥J :=
  memberOrTop 17 (Classical.choose (Certificates.certificate7124).2) j

theorem j1_card_S : Nat.card j1S = 2 ^ 3 := (Certificates.certificate7124).1

theorem j1_S_isPGroup :IsPGroup 2 j1S := IsPGroup.of_card j1_card_S

theorem j1_sylow : IsSylowTwoOf j1S ⊤ := by
  refine K1.isSylowTwoOf_top_iff.mpr ⟨j1_S_isPGroup, ?_⟩
  have h1 := Subgroup.card_mul_index j1S
  rw [j1_card_S, card_J] at h1
  norm_num at h1
  have h2 : j1S.index = 21945 := by omega
  rw [h2]
  norm_num

theorem j1_S_le_Y (j : ℕ) : j1S ≤ j1Y j := by
  unfold j1Y memberOrTop
  split_ifs with hj
  · exact ((Classical.choose_spec (Certificates.certificate7124).2).1 j hj).1
  · exact le_top

theorem j1_Y_card {j : ℕ} (hj : j < 17) :
    Nat.card (j1Y j) =
      (#[1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21] : Array ℕ)[j]! * 2 ^ 3 := by
  have h := ((Classical.choose_spec (Certificates.certificate7124).2).1 j hj).2
  unfold j1Y memberOrTop
  rw [if_pos hj, h]
  interval_cases j <;> rfl

theorem j1_cards :
    ∀ j < (#[1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21] : Array ℕ).size,
      Nat.card (j1Y j) =
        (#[1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21] : Array ℕ)[j]! * 2 ^ 3 :=
  fun _ hj => j1_Y_card hj

theorem j1_all :
    ∀ Z : Subgroup ↥J, j1S ≤ Z →
      ∃ j ≤ (#[1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21] : Array ℕ).size,
        Z = memberOrTop
          (#[1, 15, 15, 15, 15, 15, 15, 7, 3, 15, 3, 3, 3, 3, 3, 3, 21] : Array ℕ).size j1Y j := by
  intro Z hZ
  change ∃ j ≤ 17, Z = memberOrTop 17 j1Y j
  rcases (Classical.choose_spec (Certificates.certificate7124).2).2 Z hZ with h | ⟨j, hj, h⟩
  · refine ⟨17, le_rfl, ?_⟩
    rw [h]
    unfold memberOrTop
    rw [if_neg (lt_irrefl 17)]
  · refine ⟨j, hj.le, ?_⟩
    rw [h]
    unfold memberOrTop j1Y memberOrTop
    rw [if_pos hj, if_pos hj]

theorem j1_Y_zero : j1Y 0 = j1S :=
  (Subgroup.eq_of_le_of_card_ge (j1_S_le_Y 0)
    (by rw [j1_Y_card (by norm_num), j1_card_S]; decide)).symm

end Over

theorem asc86bClauseB_J1 :
    Asc86bClauseB .J1 := by
  exact @asc86bClauseB_of_inner .J1 ↥J inferInstance inferInstance nativeEquiv j1_inner
    j1S (memberOrTop _ j1Y 16) (memberOrTop _ j1Y 1) j1_sylow
    (list_S_le (fun j _ => j1_S_le_Y j) 16) (list_S_le (fun j _ => j1_S_le_Y j) 1)
    (list_ne_top' j1_cards j1_card_J (by decide)) (list_ne_top' j1_cards j1_card_J (by decide))
    (list_sup_eq_top j1_all (fun j _ => j1_S_le_Y j) j1_cards j1_card_J (by decide +kernel))

end J1

end SporB

end E2P

end CFSG.Quasithin
