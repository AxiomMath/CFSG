module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.LocalAnalysis.UniquenessCase.UC22FinThreeK1
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3a
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ConjRank857
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.R8107Odd

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem three_dvd_card_of_pRank_eq_one {L : Subgroup G} (h : CFSG.Open.pRank 3 L = 1) :
    3 ∣ Nat.card L := by
  obtain ⟨E, hEL, -, hE⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) L
  rw [h, pow_one] at hE
  rw [← hE]
  exact Subgroup.card_dvd_of_le hEL

theorem not_three_dvd_card_center {M L : Subgroup G} (hL : L ∈ calC M)
    (h : CFSG.Open.pRank 3 L = 1) : ¬ 3 ∣ Nat.card (center (Bar2 L)) := by
  haveI : Group.IsPerfect (Bar2 L) := ⟨hL.2.2.1⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact PartOne.Theorem82.not_dvd_card_center_of_pRank_eq_one (by norm_num)
    ((pRank_bar2_eq_of_odd Nat.prime_three (by norm_num)).trans h)

theorem hyp81_of_three_rankOne {M L₁ L₂ L₃ : Subgroup G} (h₁ : L₁ ∈ calC M) (h₂ : L₂ ∈ calC M)
    (h₃ : L₃ ∈ calC M) (h12 : L₁ ≠ L₂) (h13 : L₁ ≠ L₃) (h23 : L₂ ≠ L₃)
    (r₁ : CFSG.Open.pRank 3 L₁ = 1) (r₂ : CFSG.Open.pRank 3 L₂ = 1)
    (r₃ : CFSG.Open.pRank 3 L₃ = 1) : F08.Hyp81 M (L₁ ⊔ L₂ ⊔ L₃) := by
  classical
  have hle₁ : L₁ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_left.trans le_sup_left
  have hle₂ : L₂ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_right.trans le_sup_left
  have hle₃ : L₃ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_right
  have hN : ∀ {A B : Subgroup G}, A ∈ calC M → B ∈ calC M → B ≤ normalizer (A : Set G) := by
    intro A B hA hB
    by_cases hAB : A = B
    · subst hAB
      exact Subgroup.le_normalizer
    · exact PartTwo.calC_le_normalizer_of_ne hA hB hAB
  have hS : ∀ L ∈ ({L₁, L₂, L₃} : Finset (Subgroup G)),
      L ∈ calC M ∧ L ≤ L₁ ⊔ L₂ ⊔ L₃ ∧ CFSG.Open.pRank 3 L = 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro L (rfl | rfl | rfl)
    exacts [⟨h₁, hle₁, r₁⟩, ⟨h₂, hle₂, r₂⟩, ⟨h₃, hle₃, r₃⟩]
  have h3 := P22fin3.card_le_pRank_of_finset (X := L₁ ⊔ L₂ ⊔ L₃) Nat.prime_three (by norm_num)
    (fun L hL => P22fin3.mem_calC_of_le_normalizer (hS L hL).1 (hS L hL).2.1
      (sup_le (sup_le (hN (hS L hL).1 h₁) (hN (hS L hL).1 h₂)) (hN (hS L hL).1 h₃)))
    (fun L hL => not_three_dvd_card_center (hS L hL).1 (hS L hL).2.2)
    (fun L hL => three_dvd_card_of_pRank_eq_one (hS L hL).2.2)
  rw [Finset.card_eq_three.2 ⟨L₁, L₂, L₃, h12, h13, h23, rfl⟩] at h3
  exact ⟨PartTwo.isSubnormal_sup_sup h₁ h₂ h₃, PartTwo.commutator_sup_sup h₁ h₂ h₃, by omega,
    Or.inr ⟨L₁, L₂, L₃, h₁, h₂, h₃, r₁, r₂, r₃, hle₁, hle₂, hle₃,
      PartTwo.coe_sup_sup_eq_mul h₁ h₂ h₃ h12 h13 h23⟩⟩

theorem ncard_conjSetOf_le_two {D : Data G} (h82 : F08.R82 D)
    (hnsp : ¬ IsStronglyPEmbedded 3 D.M) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hr : CFSG.Open.pRank 3 L = 1) : (conjSetOf D.M L).ncard ≤ 2 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨K₁, K₂, K₃, h₁, h₂, h₃, h12, h13, h23⟩ := (Set.two_lt_ncard_iff (Set.toFinite _)).1 hlt
  exact hnsp (h82 _ (hyp81_of_three_rankOne (uc22p2214_calC_of_mem_conjSetOf hL h₁)
    (uc22p2214_calC_of_mem_conjSetOf hL h₂) (uc22p2214_calC_of_mem_conjSetOf hL h₃) h12 h13 h23
    ((PartOne.Section8.pRank_three_conj_of_mem_conjSetOf h₁).trans hr)
    ((PartOne.Section8.pRank_three_conj_of_mem_conjSetOf h₂).trans hr)
    ((PartOne.Section8.pRank_three_conj_of_mem_conjSetOf h₃).trans hr)))

theorem mem_normalizer_of_odd {D : Data G} (h82 : F08.R82 D)
    (hnsp : ¬ IsStronglyPEmbedded 3 D.M) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hr : CFSG.Open.pRank 3 L = 1) {g : G} (hg : g ∈ D.M) (hodd : Odd (orderOf g)) :
    g ∈ normalizer (L : Set G) := by
  have hle := ncard_conjSetOf_le_two h82 hnsp hL hr
  have hpos : 0 < (conjSetOf D.M L).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨L, PartOne.Section8.mem_conjSetOf_self D.M L⟩
  rcases (by omega : (conjSetOf D.M L).ncard = 1 ∨ (conjSetOf D.M L).ncard = 2) with h1 | h2
  · exact PartOne.Section8.le_normalizer_of_ncard_conjSetOf_eq_one h1 hg
  · exact uc22p2214_mem_normalizer_of_odd h2 hg hodd

theorem le_normalizer_of_odd {D : Data G} (h82 : F08.R82 D)
    (hnsp : ¬ IsStronglyPEmbedded 3 D.M) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hr : CFSG.Open.pRank 3 L = 1) {H : Subgroup G} (hHM : H ≤ D.M) (hH : Odd (Nat.card H)) :
    H ≤ normalizer (L : Set G) := fun _ hh =>
  mem_normalizer_of_odd h82 hnsp hL hr (hHM hh)
    (Odd.of_dvd_nat hH (Subgroup.orderOf_dvd_natCard H hh))

end CFSG.LocalAnalysis.UniquenessCase.UC22.R8107Odd

end
