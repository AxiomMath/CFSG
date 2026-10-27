module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC22P22l
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.UC6Dict
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ConjSetCard
import CFSG.RankThree.GroupTheory.SteinbergBYAschCoreConjugacy
import TauCeti.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22s213_pRank_barInf_of_prime {L : Subgroup G} (hq : CFSG.Open.IsQuasisimple (Bar2 L))
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hZ : ¬ r ∣ Nat.card (center (Bar2 L))) :
    CFSG.Open.pRank r (⊤ : Subgroup (BarInf L)) = CFSG.Open.pRank r L := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨e⟩ := uc22p21k_barInf_equiv hq
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e,
    CFSG.SectionRank.pRank_quotient_eq (center (Bar2 L)) hZ, pRank_bar2_eq_of_odd hr hr2]

theorem uc22s213_four_le_pRank_of_commute {H : Type} [Group H] [Finite H] {A B : Subgroup H}
    {r : ℕ} (hr : r.Prime) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hZ : ¬ r ∣ Nat.card (center ↥A)) (hA : 2 ≤ CFSG.Open.pRank r A)
    (hB : 2 ≤ CFSG.Open.pRank r B) : 4 ≤ CFSG.Open.pRank r (⊤ : Subgroup H) := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨E, hEA, hEel, hEcard⟩ := CFSG.SectionRank.exists_pRank hr.one_lt A
  obtain ⟨F, hFB, hFel, hFcard⟩ := CFSG.SectionRank.exists_pRank hr.one_lt B
  have hcEF : ∀ a ∈ E, ∀ b ∈ F, a * b = b * a := fun a ha b hb => hcomm a (hEA ha) b (hFB hb)
  have hEFZ : E ⊓ F ≤ (center ↥A).map A.subtype := fun x hx =>
    ⟨⟨x, hEA hx.1⟩, mem_center_iff.mpr fun a => Subtype.ext (hcomm a a.2 x (hFB hx.2)), rfl⟩
  have hZr : ¬ r ∣ Nat.card ((center ↥A).map A.subtype) := by
    rwa [Subgroup.card_map_of_injective A.subtype_injective]
  have hbot : E ⊓ F = ⊥ :=
    le_bot_iff.mp ((TauCeti.disjoint_of_not_dvd_natCard_of_isPGroup hZr
      (hEel.isPGroup.to_le (inf_le_left : E ⊓ F ≤ E))) hEFZ le_rfl)
  have hcard : Nat.card ↥(E ⊔ F) = r ^ (CFSG.Open.pRank r A + CFSG.Open.pRank r B) := by
    have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute E F hcEF).1
    rw [hbot, Subgroup.card_bot, mul_one, hEcard, hFcard, ← pow_add] at h
    exact h
  have h4 := CFSG.SectionRank.le_pRank hr.one_lt le_top (hEel.sup_of_commute hFel hcEF) hcard
  omega

theorem uc22s213_four_le_pRank_of_two_conj {M L L₁ L₂ : Subgroup G} (hL : L ∈ calC M)
    (h₁ : L₁ ∈ conjSetOf M L) (h₂ : L₂ ∈ conjSetOf M L) (h₁₂ : L₁ ≠ L₂) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hrL : 2 ≤ CFSG.Open.pRank r L)
    (hZ : ¬ r ∣ Nat.card (center (Bar2 L))) : 4 ≤ CFSG.Open.pRank r M := by
  have hrank : ∀ {K : Subgroup G}, K ∈ conjSetOf M L → 2 ≤ CFSG.Open.pRank r (barImage M K) := by
    intro K hK
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv (uc22p2214_calC_of_mem_conjSetOf hL hK)
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (barImage M K),
      ← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e, pRank_bar2_eq_of_odd hr hr2]
    obtain ⟨g, -, rfl⟩ := hK
    exact hrL.trans_eq (CFSG.RankThree.GroupTheory.SteinbergBY.assembly_pRank_map_mulEquiv
      hr.one_lt (MulAut.conj g) L).symm
  have hZ₁ : ¬ r ∣ Nat.card (center ↥(barImage M L₁)) := by
    obtain ⟨e, -⟩ := uc22p22l_barImage_equiv (uc22p2214_calC_of_mem_conjSetOf hL h₁)
    rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv]
    obtain ⟨g, -, rfl⟩ := h₁
    obtain ⟨e'⟩ := uc22p20d_bar2_conj g L
    have hc : Nat.card (center (Bar2 L)) =
        Nat.card (center (Bar2 (L.map (MulAut.conj g).toMonoidHom))) :=
      Nat.card_congr (Subgroup.centerCongr e').toEquiv
    rwa [← hc]
  have h4 := uc22s213_four_le_pRank_of_commute hr
    (uc22p22l_barImage_commute (uc22p2214_calC_of_mem_conjSetOf hL h₁)
      (uc22p2214_calC_of_mem_conjSetOf hL h₂) h₁₂) hZ₁ (hrank h₁) (hrank h₂)
  rwa [pRank_bar2_eq_of_odd hr hr2] at h4

theorem uc22s213_le_normalizer_of_not_mem_sigma (hU : uniqueFourUnique G) {M L : Subgroup G}
    (hM : uniqueFourIsMaxTwoLocal M) (hL : L ∈ calC M) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrL : 2 ≤ CFSG.Open.pRank r L) (hZ : ¬ r ∣ Nat.card (center (Bar2 L)))
    (hrσ : r ∉ uniqueFourSigma M) : M ≤ normalizer (L : Set G) := by
  intro g hg
  by_contra hgN
  have hne : L ≠ L.map (MulAut.conj g).toMonoidHom := fun he =>
    hgN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr he.symm)
  exact hrσ (UC6.four_le_pRank_imp_mem_sigma hU hM hr hr2
    (uc22s213_four_le_pRank_of_two_conj hL (PartOne.Section8.mem_conjSetOf_self M L)
      ⟨g, hg, rfl⟩ hne hr hr2 hrL hZ))

end CFSG.LocalAnalysis.UniquenessCase.UC22
