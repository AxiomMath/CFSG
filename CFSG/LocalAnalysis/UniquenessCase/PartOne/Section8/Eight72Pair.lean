module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213e
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1c
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2 calC)
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G]

theorem eight72_exists_pair {M K₁ K₂ J R : Subgroup G} (h₁ : K₁ ∈ calC M) (h₂ : K₂ ∈ calC M)
    (hne : K₁ ≠ K₂) (hZ : center (Bar2 K₁) = ⊥) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hd₁ : r ∣ Nat.card K₁) (hd₂ : r ∣ Nat.card K₂) (hR : IsSylowOf r R J) (hK₁J : K₁ ≤ J)
    (hK₂J : K₂ ≤ J) (hJ₁ : J ≤ normalizer (K₁ : Set G)) (hJ₂ : J ≤ normalizer (K₂ : Set G)) :
    ∃ a₁ a₂ : G, a₁ ∈ K₁ ∧ a₂ ∈ K₂ ∧ orderOf a₁ = r ∧ orderOf a₂ = r ∧
      zpowers a₁ ⊔ zpowers a₂ ≤ R ⊓ centralizer (R : Set G) ∧
      IsElemAbelian r (zpowers a₁ ⊔ zpowers a₂) ∧
      Nat.card ↥(zpowers a₁ ⊔ zpowers a₂) = r ^ 2 := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hRN₁ : R ≤ normalizer (K₁ : Set G) := hR.le.trans hJ₁
  have hRN₂ : R ≤ normalizer (K₂ : Set G) := hR.le.trans hJ₂
  have hRK₁ : R ⊓ K₁ ≠ ⊥ := by
    intro hbot
    have hRA := (hR.inf_of_le_normalizer hK₁J hJ₁).card_eq
    have hv : 1 ≤ (Nat.card K₁).factorization r :=
      (Nat.Prime.dvd_iff_one_le_factorization hr Nat.card_pos.ne').1 hd₁
    rw [hbot, Subgroup.card_bot] at hRA
    have h1 : r ^ 1 ≤ r ^ (Nat.card K₁).factorization r := Nat.pow_le_pow_right hr.pos hv
    rw [pow_one] at h1
    have := hr.two_le
    omega
  have hRK₂ : R ⊓ K₂ ≠ ⊥ := by
    intro hbot
    have hRA := (hR.inf_of_le_normalizer hK₂J hJ₂).card_eq
    have hv : 1 ≤ (Nat.card K₂).factorization r :=
      (Nat.Prime.dvd_iff_one_le_factorization hr Nat.card_pos.ne').1 hd₂
    rw [hbot, Subgroup.card_bot] at hRA
    have h1 : r ^ 1 ≤ r ^ (Nat.card K₂).factorization r := Nat.pow_le_pow_right hr.pos hv
    rw [pow_one] at h1
    have := hr.two_le
    omega
  obtain ⟨a₁, ha₁, ha₁o, ha₁c⟩ :=
    CFSG.AGLEmbeddingD2.exists_orderOf_eq_mem_centralizer_of_le_normalizer hr hR.isPGroup
      inf_le_left ((le_inf Subgroup.le_normalizer hRN₁).trans
        Subgroup.inf_normalizer_le_normalizer_inf) hRK₁
  obtain ⟨a₂, ha₂, ha₂o, ha₂c⟩ :=
    CFSG.AGLEmbeddingD2.exists_orderOf_eq_mem_centralizer_of_le_normalizer hr hR.isPGroup
      inf_le_left ((le_inf Subgroup.le_normalizer hRN₂).trans
        Subgroup.inf_normalizer_le_normalizer_inf) hRK₂
  have hna : a₂ ∉ zpowers a₁ := by
    intro h
    have h1 : a₂ = 1 :=
      CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p2213e_eq_one_of_mem_inf h₁ h₂ hne hZ hr hr2
      (zpowers_le.2 (Subgroup.mem_inf.1 ha₁).2 h) (Subgroup.mem_inf.1 ha₂).2
      (by rw [← ha₂o]; exact pow_orderOf_eq_one a₂)
    rw [h1, orderOf_one] at ha₂o
    have := hr.one_lt
    omega
  obtain ⟨hEel', hEc⟩ :=
    CFSG.ComponentClassification.UnbalancedGS.RankOneCenter.pair_isElementaryAbelian_card ha₁o
      ha₂o (Subgroup.mem_centralizer_iff.1 ha₂c a₁ (Subgroup.mem_inf.1 ha₁).1) hna
  refine ⟨a₁, a₂, (Subgroup.mem_inf.1 ha₁).2, (Subgroup.mem_inf.1 ha₂).2, ha₁o, ha₂o, ?_, ?_,
    hEc⟩
  · exact sup_le (zpowers_le.2 (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 ha₁).1, ha₁c⟩))
      (zpowers_le.2 (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 ha₂).1, ha₂c⟩))
  · exact (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian r
      (zpowers a₁ ⊔ zpowers a₂)).1 hEel'

theorem eight72_two_le_pRank_sup {M K₁ K₂ : Subgroup G} (h₁ : K₁ ∈ calC M) (h₂ : K₂ ∈ calC M)
    (hne : K₁ ≠ K₂) (hZ : center (Bar2 K₁) = ⊥) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hd₁ : r ∣ Nat.card K₁) (hd₂ : r ∣ Nat.card K₂) :
    2 ≤ CFSG.Open.pRank r (K₁ ⊔ K₂) := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hK₂N₁ : K₂ ≤ normalizer (K₁ : Set G) :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.calC_le_normalizer_of_ne h₁ h₂ hne
  have hK₁N₂ : K₁ ≤ normalizer (K₂ : Set G) :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.calC_le_normalizer_of_ne h₂ h₁ (Ne.symm hne)
  have hJ₁ : K₁ ⊔ K₂ ≤ normalizer (K₁ : Set G) := sup_le Subgroup.le_normalizer hK₂N₁
  have hJ₂ : K₁ ⊔ K₂ ≤ normalizer (K₂ : Set G) := sup_le hK₁N₂ Subgroup.le_normalizer
  obtain ⟨R, hR⟩ := CFSG.ABGLocalTools.exists_isSylowOf r (K₁ ⊔ K₂)
  obtain ⟨a₁, a₂, -, -, -, -, hER, hEel, hEcard⟩ :=
    eight72_exists_pair h₁ h₂ hne hZ hr hr2 hd₁ hd₂ hR le_sup_left le_sup_right hJ₁ hJ₂
  exact CFSG.SectionRank.le_pRank hr.one_lt (hER.trans (inf_le_left.trans hR.le)) hEel hEcard

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
