module

public import CFSG.LocalAnalysis.StandardType.GGHalfGraphCent
public import CFSG.LocalAnalysis.StandardType.GGHalfE6CertDefs
public import CFSG.LocalAnalysis.StandardType.GGHalfInnerPackage
public import CFSG.LocalAnalysis.StandardType.GGHalfInnerUniq
public import CFSG.LocalAnalysis.StandardType.GGHalfInnerLine
public import CFSG.LocalAnalysis.StandardType.MarkingClassical
public import CFSG.LocalAnalysis.StandardType.GGHalfRowData
public import CFSG.Adapters.LieModelOrders
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.SpecialLinear Matrix GGHalf

namespace GGHalfCtx

private theorem ggHalfGraphNbr_map_conj_map' {A : Type} {G : Type} [Group A] [Group G]
    (φ : A →* G) (s : A) (H : Subgroup A) :
    (H.map (MulAut.conj s).toMonoidHom).map φ =
      (H.map φ).map (MulAut.conj (φ s)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [map_mul, map_mul, map_inv]

private theorem ggHalfGraphNbr_mem_normalizer_zpowers_of_commute {G : Type} [Group G] {a b : G}
    (h : a * b = b * a) : a ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  simp only [MulAut.conj_apply, MonoidHom.coe_coe]
  rw [show a * b * a⁻¹ = b from by rw [h]; group]

private theorem ggHalfGraphNbr_statedClassicalModel_of_label_A {Q : Type} [Group Q]
    (h : GGHasLabel ⟨.A, 5, 1⟩ Q) : CFSG.Open.StatedClassicalModel Q .PSL 6 2 1 := by
  unfold GGHasLabel at h
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeLinear] at h
  obtain ⟨K, hF, hFin, hK, hne⟩ := h
  letI : Field K := hF
  letI : Finite K := hFin
  obtain ⟨e⟩ := hne
  have hadm : CFSG.Open.StatedLieAdmissible .PSL 6 2 1 :=
    ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩
  have hSM : CFSG.Open.StatedClassicalModel (LargeEvenProj (LargeEvenSLGroup (Fin 6) K))
      .PSL 6 2 1 := statedClassicalModel_linear 6 1 hK hadm
  exact statedClassicalModel_of_mulEquiv' e.symm hSM

private theorem ggHalfGraphNbr_statedClassicalModel_of_label_twD {Q : Type} [Group Q]
    (h : GGHasLabel ⟨.twD, 4, 1⟩ Q) : CFSG.Open.StatedClassicalModel Q .POmegaMinus 4 2 1 := by
  unfold GGHasLabel at h
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeOmegaMinus] at h
  obtain ⟨K, hF, hFin, hK, b, c, hbc, hne⟩ := h
  letI : Field K := hF
  letI : Finite K := hFin
  obtain ⟨e⟩ := hne
  have hadm : CFSG.Open.StatedLieAdmissible .POmegaMinus 4 2 1 :=
    ⟨Nat.prime_two, le_rfl, le_rfl⟩
  have hSM : CFSG.Open.StatedClassicalModel
      (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (4 - 1) b c))) .POmegaMinus 4 2 1 :=
    statedClassicalModel_omegaMinus 4 1 hK b c hbc hadm
  exact statedClassicalModel_of_mulEquiv' e.symm hSM

private theorem ggHalfGraphNbr_mixed_le_range
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂) (hRig : GGLabelRigidInput)
    (hTP : GGNbrTablePNbrInputOn GGRegimeAm2) (hLB : GGLBalanceInput)
    (m : GGHalfE6Model) (φ : GGE6Two →* G) (hinj : Function.Injective φ)
    (hv : φ (ggE6u (m.frame .L 0 1)) = vElt φ₁) (hw : φ (ggE6u (m.frame .K 6 7)) = wElt φ₂)
    (hJ : m.J0.map φ = J) {y' : G} {K' : Subgroup G} (hnbr : GGNbr p B x D J y' K')
    (hJK' : J ≤ K') (hKq : CFSG.Assembly.IsQuasisimple ↥K')
    {lab : LargeEvenLabel} (hlab : GGHasLabel lab (↥K' ⧸ Subgroup.center ↥K'))
    (hlabcases : lab = ⟨.A, 5, 1⟩ ∨ lab = ⟨.twD, 4, 1⟩)
    {ε : ℤ} (hX : GGHalfX0 m ε)
    (hzy : Subgroup.zpowers y' = Subgroup.zpowers
      (φ (ggE6u (m.frame .L 0 1) * (ggE6u (m.frame .K 6 7)) ^ ε))) :
    K' ≤ φ.range := by
  obtain ⟨r, hru, ⟨P, hPle, hPperf, hP3⟩, ⟨z, hzmem, hzorder, j, hjmem, hzj⟩, hcard⟩ := hX
  have hp3 : p = 3 := h.nbr.2.1
  have hK'p : LargeEvenPComponent 3 (Subgroup.centralizer ({y'} : Set G)) K' := by
    rw [← hp3]
    exact hnbr.1.2.2.2.2.1
  have hru' : φ r * φ (ggE6u (m.frame .L 0 1) * (ggE6u (m.frame .K 6 7)) ^ ε) =
      φ (ggE6u (m.frame .L 0 1) * (ggE6u (m.frame .K 6 7)) ^ ε) * φ r := by
    rw [← map_mul, ← map_mul, hru]
  have hr'_norm : φ r ∈ Subgroup.normalizer (Subgroup.zpowers y' : Set G) := by
    rw [hzy]
    exact ggHalfGraphNbr_mem_normalizer_zpowers_of_commute hru'
  have hPperf' : ⁅P.map φ, P.map φ⁆ = P.map φ := by
    rw [← Subgroup.map_commutator, hPperf]
  have hP3' : 3 ∣ Nat.card ↥(P.map φ) := by
    rw [Subgroup.card_map_of_injective hinj]
    exact hP3
  have hPle' : P.map φ ≤ J ⊓ J.map (MulAut.conj (φ r)).toMonoidHom := by
    refine (Subgroup.map_mono hPle).trans ?_
    rw [Subgroup.map_inf m.J0 (m.J0.map (MulAut.conj r).toMonoidHom) φ hinj, hJ,
      ggHalfGraphNbr_map_conj_map', hJ]
  have hconj : K'.map (MulAut.conj (φ r)).toMonoidHom = K' :=
    pComponent_conj_eq_of_perfect_common hK'p hJK' hr'_norm hPle' hPperf' hP3'
  have hJmap : m.J0.map φ ≤ K' := by
    rw [hJ]
    exact hJK'
  have hJr' : (m.J0.map (MulAut.conj r).toMonoidHom).map φ ≤ K' := by
    rw [ggHalfGraphNbr_map_conj_map' φ r m.J0, hJ]
    exact (Subgroup.map_mono hJK').trans (le_of_eq hconj)
  have hHle : (m.J0 ⊔ m.J0.map (MulAut.conj r).toMonoidHom).map φ ≤ K' := by
    rw [Subgroup.map_sup]
    exact sup_le hJmap hJr'
  have hzK : φ z ∈ K' := hHle (Subgroup.mem_map_of_mem φ hzmem)
  have hφjK : φ j ∈ K' := hJmap (Subgroup.mem_map_of_mem φ hjmem)
  have hzj' : φ z * φ j ≠ φ j * φ z := fun hh =>
    hzj (hinj (by rw [map_mul, map_mul, hh]))
  rcases hlabcases with hA | htwD
  ·
    have hlabA : GGHasLabel ⟨.A, 5, 1⟩ (↥K' ⧸ Subgroup.center ↥K') := hA ▸ hlab
    have hmodelA : CFSG.Open.StatedClassicalModel (↥K' ⧸ Subgroup.center ↥K') .PSL 6 2 1 :=
      ggHalfGraphNbr_statedClassicalModel_of_label_A hlabA
    have hLieA : CFSG.Blueprint.LieModel (↥K' ⧸ Subgroup.center ↥K') .PSL 6 2 1 :=
      Or.inl ⟨by decide, hmodelA⟩
    have hcardA : Nat.card (↥K' ⧸ Subgroup.center ↥K') = 20158709760 := by
      rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) hLieA]
      decide
    have hnot17 : ¬ 17 ∣ Nat.card (↥K' ⧸ Subgroup.center ↥K') := by
      rw [hcardA]
      decide
    have hz17 : z ^ 17 = 1 := by
      rw [← hzorder]
      exact pow_orderOf_eq_one z
    have hzpow : (⟨φ z, hzK⟩ : ↥K') ^ 17 = 1 := by
      apply Subtype.ext
      change (φ z) ^ 17 = 1
      rw [← map_pow, hz17, map_one]
    let π : ↥K' →* ↥K' ⧸ Subgroup.center ↥K' := QuotientGroup.mk' (Subgroup.center ↥K')
    have hq : (⟨φ z, hzK⟩ : ↥K') ∈ Subgroup.center ↥K' := by
      by_contra hmem
      have hq1 : π ⟨φ z, hzK⟩ ≠ 1 := by
        intro h1
        apply hmem
        exact (QuotientGroup.eq_one_iff (⟨φ z, hzK⟩ : ↥K')).mp
          (show (QuotientGroup.mk (⟨φ z, hzK⟩ : ↥K') : ↥K' ⧸ Subgroup.center ↥K') = 1 from h1)
      have hord : orderOf (π ⟨φ z, hzK⟩) = 17 := by
        haveI : Fact (Nat.Prime 17) := ⟨by norm_num⟩
        refine orderOf_eq_prime ?_ hq1
        rw [← map_pow, hzpow, map_one]
      have hdvd : 17 ∣ Nat.card (↥K' ⧸ Subgroup.center ↥K') := by
        rw [← hord]
        exact orderOf_dvd_natCard _
      exact hnot17 hdvd
    have hcomm : (⟨φ j, hφjK⟩ : ↥K') * (⟨φ z, hzK⟩ : ↥K') =
        (⟨φ z, hzK⟩ : ↥K') * (⟨φ j, hφjK⟩ : ↥K') :=
      Subgroup.mem_center_iff.mp hq (⟨φ j, hφjK⟩ : ↥K')
    have hcommG : φ z * φ j = φ j * φ z := by
      have := congrArg Subtype.val hcomm.symm
      simpa using this
    exact (hzj' hcommG).elim
  ·
    have hlabtwD : GGHasLabel ⟨.twD, 4, 1⟩ (↥K' ⧸ Subgroup.center ↥K') := htwD ▸ hlab
    have hmodeltwD : CFSG.Open.StatedClassicalModel
        (↥K' ⧸ Subgroup.center ↥K') .POmegaMinus 4 2 1 :=
      ggHalfGraphNbr_statedClassicalModel_of_label_twD hlabtwD
    haveI : Group.IsPerfect ↥K' := ⟨hKq.1⟩
    have hZbot : Subgroup.center ↥K' = ⊥ :=
      HalfRowData.center_eq_bot_of_pomegaMinus_two hmodeltwD
    have hLie : CFSG.Blueprint.LieModel (↥K' ⧸ Subgroup.center ↥K') .POmegaMinus 4 2 1 :=
      Or.inl ⟨by decide, hmodeltwD⟩
    have hcardQ : Nat.card (↥K' ⧸ Subgroup.center ↥K') = 197406720 := by
      rw [CFSG.Blueprint.LieModel.card_eq_lieOrd (by norm_num) hLie]
      decide
    have hcardK' : Nat.card ↥K' = 197406720 := by
      rw [← hcardQ, hZbot]
      exact (Nat.card_congr (QuotientGroup.quotientBot).toEquiv).symm
    have hcardH : Nat.card ↥((m.J0 ⊔ m.J0.map (MulAut.conj r).toMonoidHom).map φ) =
        Nat.card ↥(m.J0 ⊔ m.J0.map (MulAut.conj r).toMonoidHom) :=
      Subgroup.card_map_of_injective hinj
    have hcardHK : Nat.card ↥K' ≤
        Nat.card ↥((m.J0 ⊔ m.J0.map (MulAut.conj r).toMonoidHom).map φ) := by
      rw [hcardK']
      rw [hcardH]
      exact hcard
    have heq : (m.J0 ⊔ m.J0.map (MulAut.conj r).toMonoidHom).map φ = K' :=
      Subgroup.eq_of_le_of_card_ge hHle hcardHK
    rw [← heq]
    exact Subgroup.map_le_range φ _

theorem nbr_le_range_of_graph
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J K : Subgroup G} {y : G} {φ₁ φ₂ : SpecialLinearGroup (Fin 6) F2 →* G}
    (h : GGHalfCtx p B Bs x L D J 3 y K φ₁ φ₂) (hRig : GGLabelRigidInput)
    (hTP : GGNbrTablePNbrInputOn GGRegimeAm2) (hLB : GGLBalanceInput)
    (m : GGHalfE6Model) (hX1 : GGHalfX0 m 1) (hXm : GGHalfX0 m (-1))
    (φ : GGE6Two →* G) (hinj : Function.Injective φ)
    (hv : φ (ggE6u (m.frame .L 0 1)) = vElt φ₁) (hw : φ (ggE6u (m.frame .K 6 7)) = wElt φ₂)
    (hJ : m.J0.map φ = J) (hKrange : K ≤ φ.range) {y' : G} {K' : Subgroup G}
    (hnbr : GGNbr p B x D J y' K') :
    K' ≤ φ.range := by
  obtain ⟨hJK', -, hKq, -, lab, hlab, hlabcases⟩ := nbr_package h hRig hTP hLB hnbr
  have hlabcases' : lab = ⟨.A, 5, 1⟩ ∨ lab = ⟨.twD, 4, 1⟩ := by
    rcases hlabcases with h | h | h
    · left
      simpa using h
    · right
      exact h.2
    · exfalso
      omega
  rcases nbr_line h hnbr with hy | ⟨e, he, heq⟩
  · rw [nbr_eq_of_zpowers_eq h hLB hnbr hy]
    exact hKrange
  · have hw3 : (wElt φ₂) ^ 3 = 1 := by
      rw [wElt, ← map_pow, omegaBlock_pow_three, map_one]
    rcases he with rfl | rfl
    · have hφu : φ (ggE6u (m.frame .L 0 1) * (ggE6u (m.frame .K 6 7)) ^ (1 : ℤ)) =
          vElt φ₁ * (wElt φ₂) ^ (1 : ℕ) := by
        rw [map_mul, map_zpow, hv, hw]
        simp
      have hzy : Subgroup.zpowers y' = Subgroup.zpowers
          (φ (ggE6u (m.frame .L 0 1) * (ggE6u (m.frame .K 6 7)) ^ (1 : ℤ))) := by
        rw [heq, hφu]
      exact ggHalfGraphNbr_mixed_le_range h hRig hTP hLB m φ hinj hv hw hJ hnbr hJK' hKq
        hlab hlabcases' hX1 hzy
    · have hw2 : (wElt φ₂) ^ 2 = (wElt φ₂)⁻¹ := by
        have h : (wElt φ₂) ^ 2 * (wElt φ₂) = 1 := by
          rw [← pow_succ, hw3]
        exact eq_inv_of_mul_eq_one_left h
      have hφu : φ (ggE6u (m.frame .L 0 1) * (ggE6u (m.frame .K 6 7)) ^ (-1 : ℤ)) =
          vElt φ₁ * (wElt φ₂) ^ (2 : ℕ) := by
        rw [map_mul, map_zpow, hv, hw]
        rw [show (wElt φ₂) ^ (-1 : ℤ) = (wElt φ₂)⁻¹ by rw [_root_.zpow_neg, zpow_one]]
        rw [← hw2]
      have hzy : Subgroup.zpowers y' = Subgroup.zpowers
          (φ (ggE6u (m.frame .L 0 1) * (ggE6u (m.frame .K 6 7)) ^ (-1 : ℤ))) := by
        rw [heq, hφu]
      exact ggHalfGraphNbr_mixed_le_range h hRig hTP hLB m φ hinj hv hw hJ hnbr hJK' hKq
        hlab hlabcases' hXm hzy

end GGHalfCtx

end CFSG.StandardType

end
