module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartTwo.Sec15.Item155w2ProofGrow
import CFSG.RankThree.PartTwo.Sec20.Item20Res9ProofHalfOdd
import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck159

open CFSG.RankThree.PartTwo.Sec14

variable {G : Type} [Group G] [Finite G]

section Pieces

variable {A L J K : Subgroup G} [(ker148 A J).Normal]

theorem leaf2_B_le_J {n : ℕ} (hn : 1 ≤ n) (hAJ : A ≤ Subgroup.normalizer (J : Set G))
    (hL : A ≤ Subgroup.normalizer (L : Set G)) (hK : K ≤ L ⊓ J)
    (hKn : Sec4.IsoLThreePi ↥(img148 A J K) 2 n)
    (hL9 : (Nat.card L).factorization 3 = 2) (hA9 : Nat.card (A ⊓ L : Subgroup G) = 9) :
    A ⊓ L ≤ J := by
  have hXK : K ≤ J ⊔ A := hK.trans (inf_le_right.trans le_sup_left)
  have h9img : 9 ∣ Nat.card ↥(img148 A J K) :=
    Proof155w2.nine_dvd_card_of_isLThreePi ⟨2, n, ⟨Nat.prime_two⟩, hn, hKn⟩
  have h9K : 9 ∣ Nat.card K := h9img.trans (Main148.card_img148_dvd hXK)
  set D : Subgroup G := L ⊓ J
  set B : Subgroup G := A ⊓ L
  have h9D : 9 ∣ Nat.card D := h9K.trans (Subgroup.card_dvd_of_le hK)
  have hAD : A ≤ Subgroup.normalizer (D : Set G) :=
    (le_inf hL hAJ).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hBD : B ≤ Subgroup.normalizer (D : Set G) := inf_le_left.trans hAD
  set M : Subgroup G := B ⊔ D
  have hBM : B ≤ M := le_sup_left
  have hDM : D ≤ M := le_sup_right
  have hML : M ≤ L := sup_le inf_le_right inf_le_left
  have hMN : M ≤ Subgroup.normalizer (D : Set G) := sup_le hBD Subgroup.le_normalizer
  have hDn : (D.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hDM).mpr hMN
  have hDcard : Nat.card (D.subgroupOf M) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDM).toEquiv
  have hidx : (D.subgroupOf M).index * Nat.card D = Nat.card M := by
    rw [← hDcard]
    exact Subgroup.index_mul_card _
  have hLne : Nat.card L ≠ 0 := Finite.card_pos.ne'
  have hnd : ¬ 3 ∣ (D.subgroupOf M).index := by
    intro h3
    have h := mul_dvd_mul h3 h9D
    rw [hidx] at h
    have h27 : 3 ^ 3 ∣ Nat.card L := by
      rw [show (3 : ℕ) ^ 3 = 3 * 9 by norm_num]
      exact h.trans (Subgroup.card_dvd_of_le hML)
    have h3le := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hLne).mp h27
    omega
  have hBcard : Nat.card (B.subgroupOf M) = 3 ^ 2 :=
    calc Nat.card (B.subgroupOf M) = Nat.card B :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBM).toEquiv
      _ = 9 := hA9
      _ = 3 ^ 2 := by norm_num
  have hP : IsPGroup 3 (B.subgroupOf M) := IsPGroup.of_card hBcard
  have hle : B.subgroupOf M ≤ D.subgroupOf M :=
    Sec20.Res9.le_of_isPGroup_of_not_dvd_index hnd hP
  intro x hx
  have hxM : x ∈ M := hBM hx
  have hmem : (⟨x, hxM⟩ : M) ∈ B.subgroupOf M := Subgroup.mem_subgroupOf.mpr hx
  have hmem' : (⟨x, hxM⟩ : M) ∈ D.subgroupOf M := hle hmem
  exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem')).2

end Pieces

end CFSG.RankThree.PartTwo.Sec15.Liebeck159
