module

public import CFSG.RankThree.PartOne.KS.ModelR
public import CFSG.Sporadic.HeldB.AutModel

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.HeldB
open CFSG.Sporadic.SmallOddCore

theorem closure_three_eq_heAutGroup :
    closure ({heGenPerm 0, heGenPerm 1, heAutU} : Set (Equiv.Perm (Fin 8330))) = heAutGroup := by
  have h : ({heGenPerm 0, heGenPerm 1, heAutU} : Set (Equiv.Perm (Fin 8330))) =
      {heGenPerm 0, heGenPerm 1} ∪ {heAutU} := by
    rw [Set.insert_union, Set.singleton_union]
  rw [h, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure, heAutGroup, heP]

theorem mem_heP_of_siftHe {g : Array ℕ} {G : Equiv.Perm (Fin 8330)} (hG : Rep 8330 g G)
    (h : siftA 8330 heLevels heBase.toArray 0 g = true) : G ∈ heP :=
  (mem_heP_iff_siftA hG).1 h

theorem heAutModel : AutModel heP heAutGroup := by
  obtain ⟨hbij, -⟩ := ctbh_full_automorphism_permutation_model
  exact autModel_of_conj_equiv heP_le_heAutGroup heP_normal_heAutGroup
    (MulEquiv.ofBijective heConjR hbij) (fun x p => heConjR_apply x p)

theorem heAutGroup_card_le : Nat.card heAutGroup ≤ 2 * Nat.card heP := by
  rw [card_heAutGroup, card_heP]

end CFSG.RankThree.PartOne
