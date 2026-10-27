module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InducedQuotInfAut
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rk
public import CFSG.GroupTheory.PCore.SolvableRadical

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem center_barInf_eq_bot {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 K)) :
    Subgroup.center (BarInf K) = ⊥ := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv hq
  haveI : IsSimpleGroup (Bar2 K ⧸ Subgroup.center (Bar2 K)) := hq.2
  have hq' : CFSG.Open.IsQuasisimple (Bar2 K ⧸ Subgroup.center (Bar2 K)) :=
    uc22br4_isQuasisimple_of_surjective hq (QuotientGroup.mk' _)
      (QuotientGroup.mk'_surjective _)
  have hZ : Subgroup.center (Bar2 K ⧸ Subgroup.center (Bar2 K)) = ⊥ :=
    uc22p21k_center_eq_bot hq'
  rw [eq_bot_iff]
  intro z hz
  have h1 : e z ∈ Subgroup.center (Bar2 K ⧸ Subgroup.center (Bar2 K)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨w, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz w]
  rw [hZ, Subgroup.mem_bot] at h1
  exact e.injective (by simpa using h1)

noncomputable def quotInfEquivBar2 {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 K)) :
    (BarInf K ⧸ Subgroup.center (BarInf K)) ≃*
      (Bar2 K ⧸ Subgroup.center (Bar2 K)) := by
  haveI : (CFSG.pCore 2 ↥K).Normal := CFSG.pCore_normal
  exact ((QuotientGroup.quotientMulEquivOfEq (center_barInf_eq_bot hq)).trans
      QuotientGroup.quotientBot).trans
    ((QuotientGroup.quotientQuotientEquivQuotient (CFSG.pCore 2 ↥K)
        (CFSG.solvableRadical ↥K) (CFSG.pCore_le_solvableRadical 2 ↥K)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (uc22p21k_map_solvableRadical_eq_center hq)))

theorem quotInfEquivBar2_piBarInf {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 K)) (l : ↥K) :
    quotInfEquivBar2 hq (piBarInf K l) =
      QuotientGroup.mk (QuotientGroup.mk l) := by
  haveI : (CFSG.pCore 2 ↥K).Normal := CFSG.pCore_normal
  unfold quotInfEquivBar2
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have hA : (QuotientGroup.quotientMulEquivOfEq (center_barInf_eq_bot hq))
      (piBarInf K l) = QuotientGroup.mk (QuotientGroup.mk l) := by
    rw [piBarInf, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    exact QuotientGroup.quotientMulEquivOfEq_mk _ _
  rw [hA]
  have hB : QuotientGroup.quotientBot (QuotientGroup.mk (QuotientGroup.mk l) :
      BarInf K ⧸ (⊥ : Subgroup (BarInf K))) = QuotientGroup.mk l := by
    rw [← QuotientGroup.quotientBot_symm_apply (QuotientGroup.mk l), MulEquiv.apply_symm_apply]
  rw [hB]
  rw [QuotientGroup.quotientQuotientEquivQuotient_symm_mk]
  exact QuotientGroup.quotientMulEquivOfEq_mk _ _

noncomputable def quotCenterEquivBar2 {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 K))
    (hc : Subgroup.center (Bar2 K) = ⊥) :
    (BarInf K ⧸ Subgroup.center (BarInf K)) ≃* Bar2 K :=
  (quotInfEquivBar2 hq).trans
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot)

theorem quotCenterEquivBar2_piBarInf {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 K))
    (hc : Subgroup.center (Bar2 K) = ⊥) (l : ↥K) :
    quotCenterEquivBar2 hq hc (piBarInf K l) = QuotientGroup.mk l := by
  unfold quotCenterEquivBar2
  simp only [MulEquiv.trans_apply]
  rw [quotInfEquivBar2_piBarInf, QuotientGroup.quotientMulEquivOfEq_mk]
  rw [← QuotientGroup.quotientBot_symm_apply (QuotientGroup.mk l), MulEquiv.apply_symm_apply]

theorem quotInfEquivBar2_inducedQuotInfAut_piBarInf {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 K)) {b : G}
    (hb : b ∈ Subgroup.normalizer (K : Set G)) (l : ↥K) :
    quotInfEquivBar2 hq (inducedQuotInfAut K b hb (piBarInf K l)) =
      QuotientGroup.mk (QuotientGroup.mk
        (⟨b * (l : G) * b⁻¹, (Subgroup.mem_normalizer_iff.mp hb l).mp l.2⟩ : ↥K)) := by
  rw [inducedQuotInfAut_piBarInf, quotInfEquivBar2_piBarInf]

theorem piBarInf_surjective (K : Subgroup G) : Function.Surjective (piBarInf K) := by
  simpa [piBarInf] using
    (QuotientGroup.mk'_surjective (Subgroup.center (BarInf K))).comp
      (QuotientGroup.mk'_surjective (CFSG.solvableRadical ↥K))

theorem piBarInf_ker {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 K)) :
    (piBarInf K).ker = CFSG.solvableRadical ↥K := by
  ext y
  rw [MonoidHom.mem_ker, piBarInf, MonoidHom.comp_apply]
  constructor
  · intro h
    have h1 : (QuotientGroup.mk' (CFSG.solvableRadical ↥K)) y ∈
        Subgroup.center (BarInf K) := (QuotientGroup.eq_one_iff _).mp h
    rw [center_barInf_eq_bot hq, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff _).mp h1
  · intro h
    rw [show (QuotientGroup.mk' (CFSG.solvableRadical ↥K)) y = 1 from
      (QuotientGroup.eq_one_iff _).mpr h, map_one]

theorem solvableRadical_eq_pCore_of_center_bar2_eq_bot {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 K))
    (hc : Subgroup.center (Bar2 K) = ⊥) :
    CFSG.solvableRadical ↥K = CFSG.pCore 2 ↥K := by
  have hmap := uc22p21k_map_solvableRadical_eq_center hq
  rw [hc] at hmap
  have hle : CFSG.solvableRadical ↥K ≤ CFSG.pCore 2 ↥K := by
    have h := (Subgroup.map_eq_bot_iff (CFSG.solvableRadical ↥K)).mp hmap
    rwa [QuotientGroup.ker_mk'] at h
  refine le_antisymm hle ?_
  refine le_sSup ⟨CFSG.pCore_normal, ?_⟩
  haveI : Group.IsNilpotent ↥(CFSG.pCore 2 ↥K) :=
    (CFSG.pCore_isPGroup (p := 2)).isNilpotent
  infer_instance

theorem quotCenterEquivBar2_inducedQuotInfAut_piBarInf {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 K))
    (hc : Subgroup.center (Bar2 K) = ⊥) {b : G}
    (hb : b ∈ Subgroup.normalizer (K : Set G)) (l : ↥K) :
    quotCenterEquivBar2 hq hc (inducedQuotInfAut K b hb (piBarInf K l)) =
      QuotientGroup.mk
        (⟨b * (l : G) * b⁻¹, (Subgroup.mem_normalizer_iff.mp hb l).mp l.2⟩ : ↥K) := by
  unfold quotCenterEquivBar2
  simp only [MulEquiv.trans_apply]
  rw [quotInfEquivBar2_inducedQuotInfAut_piBarInf, QuotientGroup.quotientMulEquivOfEq_mk]
  rw [← QuotientGroup.quotientBot_symm_apply (QuotientGroup.mk _), MulEquiv.apply_symm_apply]

theorem center_eq_bot_of_isL2 {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 K)) {a : ℕ} (h : IsL2 (Bar2 K) a) :
    Subgroup.center (Bar2 K) = ⊥ := by
  haveI : IsSimpleGroup (Bar2 K) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  exact uc22p21k_center_eq_bot hq

theorem center_eq_bot_of_isSz {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 K)) {a : ℕ} (h : IsSz (Bar2 K) a) :
    Subgroup.center (Bar2 K) = ⊥ := by
  haveI : IsSimpleGroup (Bar2 K) := uc22p22r_lieModel_isSimple_twistedB2 h
  exact uc22p21k_center_eq_bot hq

theorem center_eq_bot_of_isSp4 {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 K)) {a : ℕ} (h : IsSp4 (Bar2 K) a) :
    Subgroup.center (Bar2 K) = ⊥ := by
  haveI : IsSimpleGroup (Bar2 K) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  exact uc22p21k_center_eq_bot hq

theorem center_eq_bot_of_isL2Odd {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 K)) {p : ℕ} (h : IsL2Odd (Bar2 K) p) :
    Subgroup.center (Bar2 K) = ⊥ := by
  haveI : IsSimpleGroup (Bar2 K) :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
  exact uc22p21k_center_eq_bot hq

theorem lieModel_barInf_of_lieModel_bar2 {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 K))
    (hc : Subgroup.center (Bar2 K) = ⊥) {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    {n p f : ℕ} (h : CFSG.Blueprint.LieModel (Bar2 K) t n p f) :
    CFSG.Blueprint.LieModel (BarInf K) t n p f := by
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_center_bot hq hc
  exact CFSG.Blueprint.LieModel.of_mulEquiv e.symm h

theorem lieModel_xbar_of_lieModel_bar2 {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 K))
    (hc : Subgroup.center (Bar2 K) = ⊥) {t : CFSG.Assembly.LowTwoRank.StatedLieTag}
    {n p f : ℕ} (h : CFSG.Blueprint.LieModel (Bar2 K) t n p f) :
    CFSG.Blueprint.LieModel (BarInf K ⧸ Subgroup.center (BarInf K)) t n p f :=
  CFSG.Blueprint.LieModel.of_mulEquiv (quotCenterEquivBar2 hq hc).symm h

theorem isU3_xbar_of_isSU3_bar2 {K : Subgroup G}
    (hq : CFSG.Open.IsQuasisimple (Bar2 K)) {a : ℕ} (h : IsSU3 (Bar2 K) a) :
    IsU3 (BarInf K ⧸ Subgroup.center (BarInf K)) a :=
  CFSG.Blueprint.LieModel.of_mulEquiv (quotInfEquivBar2 hq).symm h.2

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
