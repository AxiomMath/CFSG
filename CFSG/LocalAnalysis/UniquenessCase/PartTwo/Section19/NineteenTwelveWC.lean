module

public import CFSG.GroupTheory.RankOneNormalCentralizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.ConclNineteenTwelveWC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.NOfUniqueShapesSzSp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTenTwoComponents
public import CFSG.RankThree.PartTwo.Sec15.Item1515StepsProofRead
public import CFSG.SignalizerFunctorTheorem.McBride.Models.PSL2Even.Arithmetic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open CFSG.ComponentClassification.CatLeafProof CFSG.Blueprint
open CFSG.Blueprint (LieModel)
open CFSG.SignalizerFunctorTheorem.McBride.PSL2Even
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

section Certificates


theorem exists_rankOne_pair_of_three (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (h42 : S17.R17_42At D V₀ V)
    (hj4 : S17.jM D p = 4 →
      ∃ K₁ K₂ : Subgroup G, K₁ ∈ calC D.M ∧ K₂ ∈ calC D.M ∧ K₁ ≠ K₂ ∧
        IOf D p L = K₁ ⊔ K₂ ∧ IsL2 (Bar2 K₁) (S17.nOf L) ∧
        (IsL2 (Bar2 K₂) (S17.nOf L) ∨ IsU3 (Bar2 K₂) (S17.nOf L)) ∧
        IsPowTwo (S17.nOf L) ∧ 2 < S17.nOf L)
    (h3 : 3 ∈ piSet A) :
    ∃ L₁ L₂ : Subgroup G, IOf D p L ≤ L₁ ⊔ L₂ ∧ L₂ ≤ normalizer (L₁ : Set G) ∧
      CFSG.Open.pRank 3 L₁ ≤ 1 ∧ CFSG.Open.pRank 3 L₂ ≤ 1 := by
  have h3dvdA : 3 ∣ Nat.card A := h3.2
  have hAcard : Nat.card A = (2 ^ S17.nOf L - 1) * (2 ^ S17.nOf L - 1) :=
    card_eq_of_isZModSq h.hAcard
  have h3dvd : 3 ∣ 2 ^ S17.nOf L - 1 := by
    have h : 3 ∣ (2 ^ S17.nOf L - 1) ^ 2 := by
      rw [pow_two, ← hAcard]
      exact h3dvdA
    exact Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  by_cases hj : S17.jM D p = 4
  · obtain ⟨K₁, K₂, hK₁, hK₂, hne, hIOfeq, hL₂K₁, hL₂K₂, hpow, hn2⟩ := hj4 hj
    refine ⟨K₁, K₂, hIOfeq.le, uc22p22u_calC_normalizes hK₁ hK₂ hne,
      (pRank_three_eq_one_of_isL2 hL₂K₁).le, ?_⟩
    rcases hL₂K₂ with hL₂ | hU₃
    · exact (pRank_three_eq_one_of_isL2 hL₂).le
    · exact (pRank_three_eq_one_of_isU3FourPow hU₃ hpow (by omega)).le
  · have hI : IOf D p L = conjClosure D.M L := by simp [IOf, hj]
    have h1910 := h.h1910
    simp only [Setting1910] at h1910
    obtain ⟨-, h1 | h2 | h3alt⟩ := h1910
    · exact absurd h3dvd (not_three_dvd_pow_sub_one h1.2.1)
    · obtain ⟨x, hxM, hIOfeq⟩ := (bar2_IOf_shape_of_alt2 D h h42 h2).1
      have hL2 : IsL2 (Bar2 L) (S17.nOf L) := by
        rcases h2.2.2.2 with hL₂ | hSz
        · exact hL₂.1
        · have hodd : Odd (S17.nOf L) := by
            rw [S17.nOf_eq_of_isSz hSz.1]
            have hadm := hSz.1.admissible
            simp only [StatedLieAdmissible] at hadm
            exact hadm.2.2.2.2.1
          exact absurd h3dvd (not_three_dvd_pow_sub_one hodd)
      let L₂ : Subgroup G := CFSG.Quasithin.conjSubgroup L x
      have hXeq : conjClosure D.M L = L ⊔ L₂ := h2.1.symm.trans hIOfeq
      have hcal : L₂ ∈ calC D.M :=
        (conjSubgroup_mem_calC_and_ne h.hyp.hL.1 hxM hXeq h2.2.1).1
      have hne : L ≠ L₂ :=
        (conjSubgroup_mem_calC_and_ne h.hyp.hL.1 hxM hXeq h2.2.1).2.symm
      have hL₂L2 : IsL2 (Bar2 L₂) (S17.nOf L) := by
        change IsL2 (Bar2 (L.map (MulAut.conj x⁻¹).toMonoidHom)) (S17.nOf L)
        obtain ⟨e⟩ := uc22p20d_bar2_conj x⁻¹ L
        exact LieModel.of_mulEquiv e hL2
      exact ⟨L, L₂, (hI.trans hXeq).le, uc22p22u_calC_normalizes h.hyp.hL.1 hcal hne,
        (pRank_three_eq_one_of_isL2 hL2).le, (pRank_three_eq_one_of_isL2 hL₂L2).le⟩
    · have hXne : conjClosure D.M L ≠ L := by
        intro hXL
        have hq : CFSG.Open.IsQuasisimple (Bar2 (IOf D p L)) := by
          rw [hI, hXL]
          exact h.hyp.hL.1.2.2
        rcases h3alt.1 with ⟨A', B', gA, gB, ⟨f⟩, hA', hB'⟩ |
          ⟨A', B', gA, gB, ⟨f⟩, hA', hB'⟩
        · have : IsSimpleGroup A' :=
            LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hA'
          have : IsSimpleGroup B' :=
            LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hB'
          exact (CFSG.RankThree.PartTwo.Sec15.Proof1515.isEmpty_mulEquiv_prod_of_isQuasisimple
            (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq)).false f
        · have : IsSimpleGroup A' :=
            LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hA'
          have : IsSimpleGroup B' :=
            LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hB'
          exact (CFSG.RankThree.PartTwo.Sec15.Proof1515.isEmpty_mulEquiv_prod_of_isQuasisimple
            (CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hq)).false f
      obtain ⟨m, x, hxM, hXsup, -, hshape, -⟩ :=
        p42_alt2_of_ne h42 h.hyp.hp h.hyp.hL.1 hXne
      rcases hshape with hL₂ | hSz
      · have hL2 : IsL2 (Bar2 L) m := hL₂.1
        let L₂ : Subgroup G := CFSG.Quasithin.conjSubgroup L x
        have hcal : L₂ ∈ calC D.M :=
          (conjSubgroup_mem_calC_and_ne h.hyp.hL.1 hxM hXsup hXne).1
        have hne : L ≠ L₂ :=
          (conjSubgroup_mem_calC_and_ne h.hyp.hL.1 hxM hXsup hXne).2.symm
        have hL₂L2 : IsL2 (Bar2 L₂) m := by
          change IsL2 (Bar2 (L.map (MulAut.conj x⁻¹).toMonoidHom)) m
          obtain ⟨e⟩ := uc22p20d_bar2_conj x⁻¹ L
          exact LieModel.of_mulEquiv e hL2
        exact ⟨L, L₂, (hI.trans hXsup).le, uc22p22u_calC_normalizes h.hyp.hL.1 hcal hne,
          (pRank_three_eq_one_of_isL2 hL2).le, (pRank_three_eq_one_of_isL2 hL₂L2).le⟩
      · have hoddm : Odd m := by
          have hadm := hSz.1.admissible
          simp only [StatedLieAdmissible] at hadm
          exact hadm.2.2.2.2.1
        have hoddn : Odd (S17.nOf L) := by
          rw [S17.nOf_eq_of_isSz hSz.1]
          exact hoddm
        have hn2 : 2 < S17.nOf L := h3alt.2.1
        obtain ⟨k, hk⟩ := h3alt.2.2.1
        have hk0 : k ≠ 0 := by
          rintro rfl
          rw [hk] at hn2
          norm_num at hn2
        exact absurd hoddn (by
          rw [hk]
          exact Nat.not_odd_iff_even.mpr ((Nat.even_pow' hk0).mpr even_two))

theorem nineteen_twelve_wc_at (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (h12 : Concl19_12 D A 3) (h42 : S17.R17_42At D V₀ V)
    (hj4 : S17.jM D p = 4 →
      ∃ K₁ K₂ : Subgroup G, K₁ ∈ calC D.M ∧ K₂ ∈ calC D.M ∧ K₁ ≠ K₂ ∧
        IOf D p L = K₁ ⊔ K₂ ∧ IsL2 (Bar2 K₁) (S17.nOf L) ∧
        (IsL2 (Bar2 K₂) (S17.nOf L) ∨ IsU3 (Bar2 K₂) (S17.nOf L)) ∧
        IsPowTwo (S17.nOf L) ∧ 2 < S17.nOf L) :
    Concl19_12wc A := by
  classical
  intro E hEA hEel hEcard g hg
  have h3 : 3 ∈ piSet A := by
    refine ⟨Nat.prime_three, ?_⟩
    have hdvd := Subgroup.card_dvd_of_le hEA
    rw [hEcard] at hdvd
    exact dvd_trans ⟨3, by norm_num⟩ hdvd
  have hEU : E ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M := h12 E hEA hEel hEcard
  have hNEM : normalizer (E : Set G) ≤ D.M :=
    CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal hEU
  have hEgM : E.map (MulAut.conj g).toMonoidHom ≤ D.M :=
    hg.trans ((Subgroup.centralizer_le_normalizer (E : Set G)).trans hNEM)
  have hgM : g ∈ D.M := by
    have hle : E ≤ D.M.map (MulAut.conj g⁻¹).toMonoidHom := by
      intro x hx
      refine ⟨g * x * g⁻¹, hEgM ⟨x, hx, rfl⟩, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
    have hmem : g⁻¹ ∈ normalizer (D.M : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hEU.2 g⁻¹ hle)
    rw [CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_self_normalizing D.M D.maxLocal]
      at hmem
    simpa using D.M.inv_mem hmem
  have hIM : IOf D p L ≤ D.M := IOf_le_M D p h.hyp.hL.1.1.le
  have hMNI : D.M ≤ normalizer (IOf D p L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hIM).mp (IOf_normal D p h.hyp.hL.1)
  have hEgI : E.map (MulAut.conj g).toMonoidHom ≤ IOf D p L := by
    rintro _ ⟨x, hx, rfl⟩
    exact ((Subgroup.mem_normalizer_iff.mp (hMNI hgM)) x).mp (h.hA (hEA hx))
  obtain ⟨L₁, L₂, hIle, hnorm, hrk₁, hrk₂⟩ := exists_rankOne_pair_of_three D h h42 hj4 h3
  have hW : E ⊔ E.map (MulAut.conj g).toMonoidHom ≤ L₁ ⊔ L₂ :=
    (sup_le (hEA.trans h.hA) hEgI).trans hIle
  have hEgel : IsElemAbelian 3 (E.map (MulAut.conj g).toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hEel _
  have hcomm : ∀ a ∈ E, ∀ b ∈ E.map (MulAut.conj g).toMonoidHom, a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.mp (hg hb) a ha
  have hWel : IsElemAbelian 3 (E ⊔ E.map (MulAut.conj g).toMonoidHom) :=
    hEel.sup_of_commute hEgel hcomm
  have hWcard : Nat.card ↥(E ⊔ E.map (MulAut.conj g).toMonoidHom) ≤ 9 := by
    have hM := CFSG.GroupTheory.pRank_le_two_of_relIndex_sup_le_two Nat.prime_three (by norm_num)
      le_sup_left le_sup_right (sup_le Subgroup.le_normalizer hnorm)
      (by rw [Subgroup.relIndex_self]; norm_num) hrk₁ hrk₂
    rw [CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian Nat.prime_three hWel]
    exact (Nat.pow_le_pow_right (by norm_num)
      ((CFSG.SectionRank.pRank_mono (by norm_num) hW).trans hM)).trans (by norm_num)
  have hEW : E = E ⊔ E.map (MulAut.conj g).toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hEcard]; exact hWcard)
  have hEgE : E.map (MulAut.conj g).toMonoidHom ≤ E :=
    (le_sup_right : E.map (MulAut.conj g).toMonoidHom ≤ _).trans hEW.symm.le
  exact Subgroup.eq_of_le_of_card_ge hEgE
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
