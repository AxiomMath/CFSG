module

public import CFSG.RankThree.PartTwo.Sec15.Gagen155Q0Basic
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.RankThree.PartTwo.Sec15.Item155w2ProofCases

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof155Q0

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14

variable {G : Type} [Group G] [Finite G]

theorem step155YQ0W_of_front {A : Subgroup G} {c : G} {L : Subgroup G}
    (h146 : Item146 A (lB A))
    (hF : ∀ Y ∈ scriptY0 A (lB A), ∀ P : Subgroup G, P ≤ Y → IsPGroup 2 P →
      A ≤ Subgroup.normalizer (P : Set G) → P ∈ scriptQ A (lB A)) :
    Step155YQ0W A c L := by
  intro h X K Y M T hC _ _
  have hK0 : K ∈ scriptY0 A (lB A) := scriptY0Star_subset A (lB A) hC.mem_k
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) := hC.isY.1.1.1.2
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := by
    rw [← hC.res]
    exact le_normalizer_oPrimeResidualOf hAY
  have hYX : Y ≤ Subgroup.normalizer (X : Set G) := by
    rw [← hC.res]
    exact le_normalizer_oPrimeResidualOf Subgroup.le_normalizer
  have hY : Y = X ⊔ CFSG.Open.pCoreOf 2 Y := by
    have hY' := hC.isY.2.2
    rwa [hC.res] at hY'
  exact pCoreOf_mem_scriptQ_of_front h.isE27 h146 (hF K hK0) hC.le_k hK0.1.1.2 hAX hAY
    hC.norm_k hYX hC.isY.1.2 hY

theorem step155PJQ0W_of_front {A : Subgroup G} {c : G} {L : Subgroup G}
    (h146 : Item146 A (lB A))
    (hF : ∀ Y ∈ scriptY0 A (lB A), ∀ P : Subgroup G, P ≤ Y → IsPGroup 2 P →
      A ≤ Subgroup.normalizer (P : Set G) → P ∈ scriptQ A (lB A)) :
    Step155PJQ0W A c L := by
  intro h X K Y M T _ _ _ J _ hJ0 _ P hP _
  exact pCoreOf_sup_mem_scriptQ_of_front h.isE27 h146 (hF J hJ0) hJ0.1.1.2 hP.prop.1.1
    (isPGroup_of_mem_scriptQPi Nat.prime_two hP.prop) (hP.prop.1.2.trans inf_le_right)

theorem step155YQ0WR_of_front (h146 : Item146S14)
    (hF : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → ∀ Y ∈ scriptY0 A (lB A), ∀ P : Subgroup G, P ≤ Y → IsPGroup 2 P →
        A ≤ Subgroup.normalizer (P : Set G) → P ∈ scriptQ A (lB A)) :
    Step155YQ0WR :=
  fun G _ _ A c L hR => step155YQ0W_of_front (h146 G A c L hR.toSec14Std) (hF G A c L hR)

theorem step155PJQ0WR_of_front (h146 : Item146S14)
    (hF : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → ∀ Y ∈ scriptY0 A (lB A), ∀ P : Subgroup G, P ≤ Y → IsPGroup 2 P →
        A ≤ Subgroup.normalizer (P : Set G) → P ∈ scriptQ A (lB A)) :
    Step155PJQ0WR :=
  fun G _ _ A c L hR => step155PJQ0W_of_front (h146 G A c L hR.toSec14Std) (hF G A c L hR)

end CFSG.RankThree.PartTwo.Sec15.Proof155Q0
