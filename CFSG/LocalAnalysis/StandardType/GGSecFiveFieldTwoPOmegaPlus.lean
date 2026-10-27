module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoOmegaChart
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoPSp
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeF1POmegaPlus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepA2
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelSelfDualTwoPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelDualPairPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoPOmegaPlusRoot
public import CFSG.LocalAnalysis.StandardType.TableC.OrthGram
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGCoKleinPlus
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGCoKleinMinus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2OmegaCT
public import CFSG.RankThree.PartOne.CTP.SpinCenterEven
public import CFSG.ClassicalInvolution.WeakCT.SpinMinus6Generated
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.TransvPre
import all CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEOmegaFourMinusPOmegaPlus
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPOmegaPlus
import all CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIpFPOmegaPlusFE

public section

namespace CFSG.StandardType

namespace FieldTwoPOmega

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.StandardType.ClassicalPosition
open scoped Matrix

theorem isF2_galoisField_two_one :
    CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.IsF2 (GaloisField 2 1) := by
  refine ⟨fun c => ?_⟩
  have h : ∀ d : ZMod 2, d = 0 ∨ d = 1 := by decide
  rcases h (GaloisField.equivZmodP 2 c) with h0 | h1
  · exact Or.inl ((GaloisField.equivZmodP 2).injective (by rw [h0, map_zero]))
  · exact Or.inr ((GaloisField.equivZmodP 2).injective (by rw [h1, map_one]))

theorem center_spinGroup_eq_bot_of_gf2 {σ : Type} [Fintype σ] [DecidableEq σ]
    {Q : QuadraticForm (GaloisField 2 1) (σ → GaloisField 2 1)}
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) (hd : 3 ≤ Fintype.card σ)
    (hinjA : Function.Injective (Spin.spinAction Q))
    (hE : CFSG.ClassicalGroups.Orthogonal.elementaryGroup Q ≤ (Spin.spinAction Q).range) :
    Subgroup.center (spinGroup Q) = ⊥ := by
  have := isF2_galoisField_two_one
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  apply hinjA
  rw [map_one]
  refine CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.eq_one_of_commute_eichler hnd
    (by rw [Module.finrank_fintype_fun_eq_card]; exact hd) fun u w _ _ => ?_
  obtain ⟨y, hy⟩ := hE (CFSG.ClassicalGroups.Orthogonal.eichler_mem_elementaryGroup Q u w)
  rw [← hy, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]

theorem map_comp_symm_conj {A B C : Type*} [Group A] [Group B] [Group C] (ι : A →* C)
    (e : A ≃* B) (w : B) {X : Subgroup A} {Y : Subgroup B}
    (h : X.map e.toMonoidHom = Y.map (MulAut.conj w).toMonoidHom) :
    Y.map (ι.comp (e.symm.toMonoidHom.comp (MulAut.conj w).toMonoidHom)) = X.map ι := by
  have h1 : Y.map (ι.comp (e.symm.toMonoidHom.comp (MulAut.conj w).toMonoidHom)) =
      ((Y.map (MulAut.conj w).toMonoidHom).map e.symm.toMonoidHom).map ι := by
    simp only [Subgroup.map_map]
  rw [h1, ← h, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem range_comp_symm_conj {A B C : Type*} [Group A] [Group B] [Group C] (ι : A →* C)
    (e : A ≃* B) (w : B) :
    (ι.comp (e.symm.toMonoidHom.comp (MulAut.conj w).toMonoidHom)).range = ι.range := by
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr fun z =>
    ⟨(MulAut.conj w).symm (e z), by simp [mul_assoc]⟩, ← MonoidHom.range_eq_map]

section Cert


@[expose] def SiegelBlock (f : ℕ) {σ : Type} [Fintype σ] [DecidableEq σ]
    (Q : QuadraticForm (GaloisField 2 f) (σ → GaloisField 2 f)) (L' : Subgroup (spinGroup Q)) :
    Prop :=
  ∃ (t' : StatedLieTag) (m : ℕ) (ι : (ggU t' m f).K →* spinGroup Q)
    (β₀ : Fin (ggU t' m f).D.rank → ℤ),
    StatedLieAdmissible t' m 2 f ∧ 2 ≤ (ggU t' m f).D.rank ∧ Function.Injective ι ∧
    β₀ ∈ (ggU t' m f).D.roots ∧ ι.range = L' ∧
    ∃ a₁ a₂ b₁ b₂ : σ → GaloisField 2 f, (Q a₁ = 0 ∧ Q a₂ = 0 ∧ Q b₁ = 0 ∧ Q b₂ = 0) ∧
      QuadraticMap.polar Q a₁ b₁ = 1 ∧ QuadraticMap.polar Q a₂ b₂ = 1 ∧
      (QuadraticMap.polar Q a₁ a₂ = 0 ∧ QuadraticMap.polar Q b₁ b₂ = 0 ∧
        QuadraticMap.polar Q a₁ b₂ = 0 ∧ QuadraticMap.polar Q a₂ b₁ = 0) ∧
      (((ggU t' m f).D.rootGroup β₀).map ι).map (Spin.spinAction Q) = siegelGroup Q a₁ a₂ ∧
      (((ggU t' m f).D.rootGroup (-β₀)).map ι).map (Spin.spinAction Q) = siegelGroup Q b₁ b₂

theorem center_POmegaMinus_three_gf2 : Subgroup.center (ggU .POmegaMinus 3 1).K = ⊥ := by
  have hirr := minusCoeffs_irr 2 1
  have := Spin.isCentral_cliffordAlgebra_quadMinus 3 (minusCoeffs 2 1).1 (minusCoeffs 2 1).2 hirr
  exact center_spinGroup_eq_bot_of_gf2
    (Spin.nondegenerate_polarBilin_quadMinus_of_finite 3 (GaloisField 2 1) hirr)
    (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
    ((MonoidHom.ker_eq_bot_iff _).mp
      (Spin.ker_spinAction_eq_bot_of_isCentral _ (CharP.cast_eq_zero (GaloisField 2 1) 2)))
    (CFSG.ClassicalInvolution.WeakCT.range_spinAction_quadMinus_three hirr).ge

theorem false_of_fieldExt_model {X : Type} [Group X] {σ : Type} [Fintype σ] [DecidableEq σ]
    {f : ℕ} {Q : QuadraticForm (GaloisField 2 f) (σ → GaloisField 2 f)}
    (hZ : Subgroup.center ↥(spinGroup Q) = ⊥)
    (ψ : ↥(spinGroup Q) →* X) (hψ : ψ.ker ≤ Subgroup.center _)
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) (hn1 : lab.n = 1)
    (hne : lab ≠ ⟨.twD, 2, 1⟩) {L' : Subgroup ↥(spinGroup Q)}
    (hM : MarkedModel lab (↥(L'.map ψ) ⧸ Subgroup.center ↥(L'.map ψ)))
    {t' : StatedLieTag} {m' f' : ℕ} (hlt : f < f') (hf : 1 ≤ f) (ht' : t' = .PSL ∨ t' = .PSU)
    (hmod : CFSG.Open.StatedClassicalModel (↥L' ⧸ Subgroup.center ↥L') t' m' 2 f') : False := by
  have hinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hψ.trans hZ.le
  let e₁ : ↥L' ≃* ↥(L'.map ψ) := L'.equivMapOfInjective ψ hinj
  let ξ : ↥L' ⧸ Subgroup.center ↥L' ≃* ↥(L'.map ψ) ⧸ Subgroup.center ↥(L'.map ψ) :=
    QuotientGroup.congr _ _ e₁ (Subgroup.map_center_eq e₁)
  have h := fieldTwo_typeDet hl hn1 hne hM (ht'.imp_right Or.inl)
    (Or.inl ⟨by rcases ht' with rfl | rfl <;> decide,
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv ξ hmod⟩)
  omega

theorem false_of_dualPair_model {X : Type} [Group X] {σ : Type} [Fintype σ] [DecidableEq σ]
    {f : ℕ} (hf : 1 ≤ f) {Q : QuadraticForm (GaloisField 2 f) (σ → GaloisField 2 f)}
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate)
    (ψ : ↥(spinGroup Q) →* X) (hψ : ψ.ker ≤ Subgroup.center _)
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) (hn1 : lab.n = 1)
    (hne : lab ≠ ⟨.twD, 2, 1⟩) {L' : Subgroup ↥(spinGroup Q)} (hns : ¬ Group.IsSolvable L')
    (hM : MarkedModel lab (↥(L'.map ψ) ⧸ Subgroup.center ↥(L'.map ψ)))
    {r : ℕ} (ι : (ggU .PSL (r + 1) f).K →* ↥(spinGroup Q))
    (hcent : ∀ y, ι y ∈ Subgroup.center ↥(spinGroup Q) →
      y ∈ Subgroup.center (ggU .PSL (r + 1) f).K)
    (hrange : ι.range = L') (s : GL σ (GaloisField 2 f)) (hsU : s ∈ (Spin.spinMatrix Q).range)
    {e : Matrix σ σ (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) e)
    (hpair : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin Q)) e ≠ e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) e < 2) : False := by
  have hrange' : (ψ.comp ι).range = L'.map ψ := by rw [MonoidHom.range_comp, hrange]
  have hker' : (ψ.comp ι).ker ≤ Subgroup.center (ggU .PSL (r + 1) f).K := fun y hy =>
    hcent y (hψ hy)
  have hf1 : f = 1 := by
    by_contra hf1
    have hq4 : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    rcases Nat.eq_zero_or_pos r with hr0 | hr1
    ·
      subst hr0
      have hsub : Subsingleton (Matrix.SpecialLinearGroup (Fin 1) (GaloisField 2 f)) := by
        constructor
        intro a b
        have ha : (a : Matrix (Fin 1) (Fin 1) (GaloisField 2 f)) default default = 1 := by
          have h := Matrix.SpecialLinearGroup.det_coe a
          rwa [Matrix.det_unique] at h
        have hb : (b : Matrix (Fin 1) (Fin 1) (GaloisField 2 f)) default default = 1 := by
          have h := Matrix.SpecialLinearGroup.det_coe b
          rwa [Matrix.det_unique] at h
        ext i j
        rw [Subsingleton.elim i default, Subsingleton.elim j default, ha, hb]
      have hsolA : Group.IsSolvable (ggU .PSL (0 + 1) f).K := by
        have : Subsingleton (ggU .PSL (0 + 1) f).K := hsub
        infer_instance
      have : Group.IsSolvable ι.range := @FieldTwoPSp.isSolvable_range _ _ _ _ ι hsolA
      exact hns (hrange ▸ this)
    · have hadm : StatedLieAdmissible .PSL (r + 1) 2 f :=
        ⟨Nat.prime_two, hf, by omega, fun h => by have := (Prod.mk.inj h).2; omega,
          fun h => by have := (Prod.mk.inj h).2; omega⟩
      have hLM := RCKRP.irg_lieModel_quot (Or.inl rfl) hadm (ψ.comp ι) hrange' hker'
      exact hf1 (fieldTwo_typeDet hl hn1 hne hM (Or.inl rfl) hLM).1
  subst hf1
  have hG := CFSG.StandardType.TableC.polarGram_isUnit_det _ hnd
  obtain ⟨u, rfl⟩ := hsU
  exact hpair (formAdj_eq_self_of_blockDegree_lt_two_gf2 hG
    (CFSG.StandardType.TableC.spinMatrix_isometry _ u) he hdeg)

theorem siegelBlock_of_selfDual_model {X : Type} [Group X] {σ : Type} [Fintype σ] [DecidableEq σ]
    {f : ℕ} (hf : 1 ≤ f) {Q : QuadraticForm (GaloisField 2 f) (σ → GaloisField 2 f)}
    (ψ : ↥(spinGroup Q) →* X) (hψ : ψ.ker ≤ Subgroup.center _)
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) (hn1 : lab.n = 1)
    (hne : lab ≠ ⟨.twD, 2, 1⟩) {L' : Subgroup ↥(spinGroup Q)} (hns : ¬ Group.IsSolvable L')
    (hM : MarkedModel lab (↥(L'.map ψ) ⧸ Subgroup.center ↥(L'.map ψ)))
    {t' : StatedLieTag} {m : ℕ} (ι : (ggU t' m f).K →* ↥(spinGroup Q))
    {β₀ : Fin (ggU t' m f).D.rank → ℤ}
    (hcase : ((t' = .POmegaPlus ∨ t' = .POmegaMinus) ∧ 3 ≤ m) ∨ (t' = .PSL ∧ m = 2))
    (hlong : GGLongRoot (ggU t' m f).D β₀)
    (hcent : ∀ y, ι y ∈ Subgroup.center ↥(spinGroup Q) → y ∈ Subgroup.center (ggU t' m f).K)
    (hrange : ι.range = L') {a₁ a₂ b₁ b₂ : σ → GaloisField 2 f}
    (hQ : Q a₁ = 0 ∧ Q a₂ = 0 ∧ Q b₁ = 0 ∧ Q b₂ = 0) (h₁ : QuadraticMap.polar Q a₁ b₁ = 1)
    (h₂ : QuadraticMap.polar Q a₂ b₂ = 1)
    (h₀ : QuadraticMap.polar Q a₁ a₂ = 0 ∧ QuadraticMap.polar Q b₁ b₂ = 0 ∧
      QuadraticMap.polar Q a₁ b₂ = 0 ∧ QuadraticMap.polar Q a₂ b₁ = 0)
    (hX : (((ggU t' m f).D.rootGroup β₀).map ι).map (Spin.spinAction Q) = siegelGroup Q a₁ a₂)
    (hX' : (((ggU t' m f).D.rootGroup (-β₀)).map ι).map (Spin.spinAction Q) =
      siegelGroup Q b₁ b₂) :
    f = 1 ∧ SiegelBlock f Q L' := by
  have hrange' : (ψ.comp ι).range = L'.map ψ := by rw [MonoidHom.range_comp, hrange]
  have hker' : (ψ.comp ι).ker ≤ Subgroup.center (ggU t' m f).K := fun y hy => hcent y (hψ hy)
  have hβ₀ : β₀ ∈ (ggU t' m f).D.roots := by
    obtain ⟨w', γ₀, hγ₀, -, rfl⟩ := hlong
    exact CFSG.LieType.CurtisTits.weylAction_mem_roots hγ₀ w'
  rcases hcase with ⟨ht' | ht', hm3⟩ | ⟨ht', hm2⟩
  ·
    subst ht'
    rcases Nat.lt_or_ge m 4 with hm4 | hm4
    ·
      obtain rfl : m = 3 := by omega
      obtain ⟨eK, heK⟩ := RCKRP.irgIsoCompat_omegaPlus_three (g := f) hf
      have hadm : StatedLieAdmissible .PSL 4 2 f :=
        ⟨Nat.prime_two, hf, by norm_num, fun h => by have := (Prod.mk.inj h).1; omega,
          fun h => by have := (Prod.mk.inj h).1; omega⟩
      have hf1 : f = 1 := by
        have hLM := RCKRP.irg_lieModel_quot (Or.inl rfl) hadm
          ((ψ.comp ι).comp eK.symm.toMonoidHom)
          (by rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eK.symm.surjective,
            ← MonoidHom.range_eq_map, hrange'])
          (fun y hy => Subgroup.comap_center_le_center eK.symm.injective (hker' hy))
        exact (fieldTwo_typeDet hl hn1 hne hM (Or.inl rfl) hLM).1
      subst hf1
      have hinj : Function.Injective ι := FieldTwoPSp.injective_of_center ι hcent
        (CFSG.SeitzReduction.SymplecticPilot.q2Omega_center_spinGroup_quadPlus_eq_bot le_rfl)
      obtain ⟨γ, ⟨hγ, -⟩, w, h1, h2⟩ := heK β₀ hβ₀ hlong
      refine ⟨rfl, .PSL, 4, ι.comp (eK.symm.toMonoidHom.comp (MulAut.conj w).toMonoidHom), γ,
        hadm, by show 2 ≤ 3; norm_num,
        hinj.comp (eK.symm.injective.comp (MulAut.conj w).injective), hγ,
        (range_comp_symm_conj ι eK w).trans hrange, a₁, a₂, b₁, b₂, hQ, h₁, h₂, h₀, ?_, ?_⟩
      · rw [map_comp_symm_conj ι eK w h1]
        exact hX
      · rw [map_comp_symm_conj ι eK w h2]
        exact hX'
    ·
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
      have hadm : StatedLieAdmissible .POmegaPlus (j + 3) 2 f := ⟨Nat.prime_two, hf, hm4⟩
      have hf1 : f = 1 := (fieldTwo_typeDet hl hn1 hne hM (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
        (RCKRP.irg_lieModel_quot (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hadm (ψ.comp ι) hrange'
          hker')).1
      subst hf1
      have hinj : Function.Injective ι := FieldTwoPSp.injective_of_center ι hcent
        (CFSG.SeitzReduction.SymplecticPilot.q2Omega_center_spinGroup_quadPlus_eq_bot
          (by omega))
      exact ⟨rfl, .POmegaPlus, j + 3, ι, β₀, hadm, by show 2 ≤ j + 3; omega, hinj, hβ₀, hrange,
        a₁, a₂, b₁, b₂, hQ, h₁, h₂, h₀, hX, hX'⟩
  ·
    subst ht'
    rcases Nat.lt_or_ge m 4 with hm4 | hm4
    ·
      obtain rfl : m = 3 := by omega
      obtain ⟨eK, heK⟩ := RCKRP.irgIsoCompat_omegaMinus_three (g := f) hf
      have hadm : StatedLieAdmissible .PSU 4 2 f :=
        ⟨Nat.prime_two, hf, by norm_num, fun h => by have := (Prod.mk.inj h).1; omega⟩
      have hf1 : f = 1 := by
        have hLM := RCKRP.irg_lieModel_quot (Or.inr (Or.inl rfl)) hadm
          ((ψ.comp ι).comp eK.symm.toMonoidHom)
          (by rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eK.symm.surjective,
            ← MonoidHom.range_eq_map, hrange'])
          (fun y hy => Subgroup.comap_center_le_center eK.symm.injective (hker' hy))
        exact (fieldTwo_typeDet hl hn1 hne hM (Or.inr (Or.inl rfl)) hLM).1
      subst hf1
      have hinj : Function.Injective ι :=
        FieldTwoPSp.injective_of_center ι hcent center_POmegaMinus_three_gf2
      obtain ⟨γ, ⟨hγ, -⟩, w, h1, h2⟩ := heK β₀ hβ₀ hlong
      refine ⟨rfl, .PSU, 4, ι.comp (eK.symm.toMonoidHom.comp (MulAut.conj w).toMonoidHom), γ,
        hadm, by show 2 ≤ 4 / 2; norm_num,
        hinj.comp (eK.symm.injective.comp (MulAut.conj w).injective), hγ,
        (range_comp_symm_conj ι eK w).trans hrange, a₁, a₂, b₁, b₂, hQ, h₁, h₂, h₀, ?_, ?_⟩
      · rw [map_comp_symm_conj ι eK w h1]
        exact hX
      · rw [map_comp_symm_conj ι eK w h2]
        exact hX'
    ·
      have hadm : StatedLieAdmissible .POmegaMinus m 2 f := ⟨Nat.prime_two, hf, hm4⟩
      have hf1 : f = 1 := (fieldTwo_typeDet hl hn1 hne hM (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
        (RCKRP.irg_lieModel_quot (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hadm
          (ψ.comp ι) hrange' hker')).1
      subst hf1
      have hinj : Function.Injective ι := FieldTwoPSp.injective_of_center ι hcent
        (CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot hm4 (minusCoeffs_irr 2 1))
      exact ⟨rfl, .POmegaMinus, m, ι, β₀, hadm, by show 2 ≤ m - 1; omega, hinj, hβ₀, hrange,
        a₁, a₂, b₁, b₂, hQ, h₁, h₂, h₀, hX, hX'⟩
  ·
    exfalso
    subst ht'
    subst hm2
    rcases Nat.lt_or_ge f 2 with hf2 | hf2
    · obtain rfl : f = 1 := by omega
      obtain ⟨χ⟩ := RCKRP.rckRP_nonempty_mulEquiv_PSL_two_PSp_one (f := 1) le_rfl
      have hq2 : Nat.card (GaloisField 2 1) = 2 := by
        rw [GaloisField.card 2 1 (by norm_num)]
        norm_num
      have hsolSp : Group.IsSolvable (ggU .PSp 1 1).K :=
        CFSG.AGLEmbedding.LeviBlock.spFlag_isSolvable_Sp (Or.inr ⟨rfl, hq2⟩)
      have hsolA : Group.IsSolvable (ggU .PSL 2 1).K :=
        Group.isSolvable_of_surjective (f := χ.symm.toMonoidHom) χ.symm.surjective
      have : Group.IsSolvable ι.range := @FieldTwoPSp.isSolvable_range _ _ _ _ ι hsolA
      exact hns (hrange ▸ this)
    · have hq4 : 4 ≤ 2 ^ f := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      have hadm : StatedLieAdmissible .PSL 2 2 f :=
        ⟨Nat.prime_two, hf, le_rfl, fun h => by have := (Prod.mk.inj h).2; omega,
          fun h => by have := (Prod.mk.inj h).2; omega⟩
      have := (fieldTwo_typeDet hl hn1 hne hM (Or.inl rfl)
        (RCKRP.irg_lieModel_quot (Or.inl rfl) hadm (ψ.comp ι) hrange' hker')).1
      omega

theorem siegelBlock_of_SU_model {X : Type} [Group X] {σ : Type} [Fintype σ] [DecidableEq σ]
    {f : ℕ} (hf : 1 ≤ f) {Q : QuadraticForm (GaloisField 2 f) (σ → GaloisField 2 f)}
    (ψ : ↥(spinGroup Q) →* X) (hψ : ψ.ker ≤ Subgroup.center _)
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) (hn1 : lab.n = 1)
    (hne : lab ≠ ⟨.twD, 2, 1⟩) {L' : Subgroup ↥(spinGroup Q)}
    (hM : MarkedModel lab (↥(L'.map ψ) ⧸ Subgroup.center ↥(L'.map ψ)))
    {r : ℕ} (ι : (ggU .PSU r (max f 1)).K →* ↥(spinGroup Q))
    {β₀ : Fin (ggU .PSU r (max f 1)).D.rank → ℤ} (hinj : Function.Injective ι) (hr2 : 2 ≤ r)
    (hnq : 2 ^ max f 1 ≠ 2 ∨ 4 ≤ r) (hlong : GGLongRoot (ggU .PSU r (max f 1)).D β₀)
    (hrange : ι.range = L') {a₁ a₂ b₁ b₂ : σ → GaloisField 2 f}
    (hQ : Q a₁ = 0 ∧ Q a₂ = 0 ∧ Q b₁ = 0 ∧ Q b₂ = 0) (h₁ : QuadraticMap.polar Q a₁ b₁ = 1)
    (h₂ : QuadraticMap.polar Q a₂ b₂ = 1)
    (h₀ : QuadraticMap.polar Q a₁ a₂ = 0 ∧ QuadraticMap.polar Q b₁ b₂ = 0 ∧
      QuadraticMap.polar Q a₁ b₂ = 0 ∧ QuadraticMap.polar Q a₂ b₁ = 0)
    (hX : (((ggU .PSU r (max f 1)).D.rootGroup β₀).map ι).map (Spin.spinAction Q) =
      siegelGroup Q a₁ a₂)
    (hX' : (((ggU .PSU r (max f 1)).D.rootGroup (-β₀)).map ι).map (Spin.spinAction Q) =
      siegelGroup Q b₁ b₂) :
    f = 1 ∧ SiegelBlock f Q L' := by
  have hmax : max f 1 = f := max_eq_left hf
  have hrange' : (ψ.comp ι).range = L'.map ψ := by rw [MonoidHom.range_comp, hrange]
  have hker' : (ψ.comp ι).ker ≤ Subgroup.center (ggU .PSU r (max f 1)).K := fun y hy =>
    Subgroup.comap_center_le_center hinj (hψ hy)
  have hβ₀ : β₀ ∈ (ggU .PSU r (max f 1)).D.roots := by
    obtain ⟨w', γ₀, hγ₀, -, rfl⟩ := hlong
    exact CFSG.LieType.CurtisTits.weylAction_mem_roots hγ₀ w'
  have hf1 : f = 1 := by
    by_contra hf1
    have hq4 : 4 ≤ 2 ^ max f 1 := by
      rw [hmax]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    rcases Nat.lt_or_ge r 3 with hr3 | hr3
    ·
      obtain rfl : r = 2 := by omega
      obtain ⟨φ, hφr, hφk⟩ := FieldTwoPSp.exists_PSL_two_of_PSU_two (le_max_right f 1) (ψ.comp ι)
      have hadm : StatedLieAdmissible .PSL 2 2 (max f 1) :=
        ⟨Nat.prime_two, le_max_right f 1, le_rfl, fun h => by have := (Prod.mk.inj h).2; omega,
          fun h => by have := (Prod.mk.inj h).2; omega⟩
      have hLM := RCKRP.irg_lieModel_quot (Or.inl rfl) hadm φ (hφr.trans hrange') (hφk hker')
      have := (fieldTwo_typeDet hl hn1 hne hM (Or.inl rfl) hLM).1
      omega
    · have hadm : StatedLieAdmissible .PSU r 2 (max f 1) :=
        ⟨Nat.prime_two, le_max_right f 1, hr3, fun h => by have := (Prod.mk.inj h).2; omega⟩
      have hLM := RCKRP.irg_lieModel_quot (Or.inr (Or.inl rfl)) hadm (ψ.comp ι) hrange' hker'
      have := (fieldTwo_typeDet hl hn1 hne hM (Or.inr (Or.inl rfl)) hLM).1
      omega
  subst hf1
  have hr4 : 4 ≤ r := by
    rcases hnq with h | h
    · exact absurd (by norm_num) h
    · exact h
  let ι' : (ggU .PSU r 1).K →* ↥(spinGroup Q) := ι
  exact ⟨rfl, .PSU, r, ι', β₀,
    ⟨Nat.prime_two, le_rfl, by omega, fun h => by have := (Prod.mk.inj h).1; omega⟩,
    by show 2 ≤ r / 2; omega, hinj, hβ₀, hrange, a₁, a₂, b₁, b₂, hQ, h₁, h₂, h₀, hX, hX'⟩

theorem omegaFourMinus_false {X : Type} [Group X] {k f : ℕ} (hf : 1 ≤ f)
    (ψ : ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _)
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) (hn1 : lab.n = 1)
    (hne : lab ≠ ⟨.twD, 2, 1⟩)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f))))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    {L' : Subgroup ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)))}
    (hJe : IsComponentOf L'
      ⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε,
        glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε⁆)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε < 2)
    (hm4 : ε.rank = 4 ∧ ∀ x y : Fin (k + 3) ⊕ Fin (k + 3) → GaloisField 2 f,
      Matrix.mulVec ε x = x → Matrix.mulVec ε y = y →
      Spin.quadPlus (k + 3) (GaloisField 2 f) x = 0 →
      Spin.quadPlus (k + 3) (GaloisField 2 f) y = 0 →
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x y = 0 →
      ¬ LinearIndependent (GaloisField 2 f) ![x, y])
    (hM : MarkedModel lab (↥(L'.map ψ) ⧸ Subgroup.center ↥(L'.map ψ))) : False := by
  have hc : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨η⟩ := feomeg_component_iso (k + 3) (GaloisField 2 f) (by omega) f hc S hSU hS hodd hε
    hJe hdeg hm4.1 hm4.2
  obtain ⟨ξ⟩ := feomeg_quotientCenter ψ hψ (J' := L') hJe.2.2.1
  have h := fieldTwo_typeDet hl hn1 hne hM (t := .PSL) (m := 2) (f := 2 * f) (Or.inl rfl) (by
    refine Or.inl ⟨by decide, ?_⟩
    refine ⟨feomeg_admissible f hf, GaloisField 2 (2 * f), inferInstance, inferInstance, ?_, ?_⟩
    · rw [GaloisField.card 2 (2 * f) (by omega)]
    · exact ⟨ξ.symm.trans η⟩)
  omega

theorem fieldExt_false {X : Type} [Group X] {k f : ℕ} (hf : 1 ≤ f)
    (ψ : ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _)
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) (hn1 : lab.n = 1)
    (hne : lab ≠ ⟨.twD, 2, 1⟩)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (hε : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f))))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    {L' : Subgroup ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)))}
    (hJe : IsComponentOf L'
      ⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε,
        glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S ε⁆)
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) (heε : e * ε = e)
    (hdeg : (e = ε ∧ 4 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) ∨
      (e ≠ ε ∧ 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e))
    (hM : MarkedModel lab (↥(L'.map ψ) ⧸ Subgroup.center ↥(L'.map ψ))) : False := by
  have hc : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨t', m', f', hlt, ht', hmod⟩ :=
    RCKC1.rckIIp_component_model_PSL_or_PSU (k + 3) (by omega) f hc S hSU hS hodd hε hJe he heε
      hdeg
  exact false_of_fieldExt_model
    (CFSG.SeitzReduction.SymplecticPilot.q2Omega_center_spinGroup_quadPlus_eq_bot (by omega)) ψ hψ
    hl hn1 hne hM hlt hf ht' hmod
theorem dualPair_one_false {X : Type} [Group X] {k f : ℕ} (hf : 1 ≤ f)
    (ψ : ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _)
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) (hn1 : lab.n = 1)
    (hne : lab ≠ ⟨.twD, 2, 1⟩)
    (s : GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))
    (hsU : s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hsodd : Odd (orderOf s))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) e)
    (hpair : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e ≠ e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' {s})) e < 2)
    {L' : Subgroup ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)))}
    (hJe : IsComponentOf L'
      ⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) {s}
        (e + formAdj (RingHom.id (GaloisField 2 f))
          (LinearMap.toMatrix₂' (GaloisField 2 f)
            (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e),
        glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) {s}
          (e + formAdj (RingHom.id (GaloisField 2 f))
            (LinearMap.toMatrix₂' (GaloisField 2 f)
              (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e)⁆)
    (hM : MarkedModel lab (↥(L'.map ψ) ⧸ Subgroup.center ↥(L'.map ψ))) : False := by
  have hSU : ∀ t ∈ ({s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))),
      t ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range := by
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    exact hsU
  have hS : ∀ t ∈ ({s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))),
      ∀ t' ∈ ({s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))), Commute t t' := by
    intro t ht t' ht'
    rw [Set.mem_singleton_iff] at ht ht'
    rw [ht, ht']
  have hodd : ∀ t ∈ ({s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))),
      Odd (orderOf t) := by
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    exact hsodd
  obtain ⟨r, ι, -, -, -, hcent, hrange, -⟩ :=
    exists_blockModel_dualPair_POmegaPlus_explicit k f hf {s} hSU hS hodd he hpair hdeg hJe
  exact false_of_dualPair_model hf (Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 f))
    ψ hψ hl hn1 hne (FieldTwoPSp.not_isSolvable_of_isComponentOf hJe) hM ι hcent hrange s hsU he
    hpair hdeg
theorem selfDual_one {X : Type} [Group X] {k f : ℕ} (hf : 1 ≤ f)
    (ψ : ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _)
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) (hn1 : lab.n = 1)
    (hne : lab ≠ ⟨.twD, 2, 1⟩)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e = e)
    (hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2)
    (hnm : ¬ (e.rank = 4 ∧ ∀ x y : Fin (k + 3) ⊕ Fin (k + 3) → GaloisField 2 f,
      Matrix.mulVec e x = x → Matrix.mulVec e y = y →
      Spin.quadPlus (k + 3) (GaloisField 2 f) x = 0 →
      Spin.quadPlus (k + 3) (GaloisField 2 f) y = 0 →
      QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x y = 0 →
      ¬ LinearIndependent (GaloisField 2 f) ![x, y]))
    {L' : Subgroup ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)))}
    (hJe : IsComponentOf L'
      ⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S e,
        glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S e⁆)
    (hM : MarkedModel lab (↥(L'.map ψ) ⧸ Subgroup.center ↥(L'.map ψ))) :
    f = 1 ∧ SiegelBlock f (Spin.quadPlus (k + 3) (GaloisField 2 f)) L' := by
  obtain ⟨t', m, ι, β₀, hcase, hlong, hcent, hrange, a₁, a₂, b₁, b₂, hQ, h₁, h₂, h₀, hX, hX'⟩ :=
    exists_blockModel_selfDual_POmegaPlus_explicit k f hf S hSU hS hodd he hadj hdeg hnm hJe
  exact siegelBlock_of_selfDual_model hf ψ hψ hl hn1 hne
    (FieldTwoPSp.not_isSolvable_of_isComponentOf hJe) hM ι
    (hcase.imp (fun h => ⟨h.1, h.2.1⟩) (fun h => ⟨h.1, h.2.1⟩)) hlong hcent hrange hQ h₁ h₂ h₀ hX hX'
theorem selfDual_two {X : Type} [Group X] {k f : ℕ} (hf : 1 ≤ f)
    (ψ : ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _)
    {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab) (hn1 : lab.n = 1)
    (hne : lab ≠ ⟨.twD, 2, 1⟩)
    (S : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {e : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)}
    (he : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f)
        (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f)))) e = e)
    (hdeg₁ : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)
    (hdeg₂ : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 4)
    {L' : Subgroup ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)))}
    (hJe : IsComponentOf L'
      ⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S e,
        glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) S e⁆)
    (hM : MarkedModel lab (↥(L'.map ψ) ⧸ Subgroup.center ↥(L'.map ψ))) :
    f = 1 ∧ SiegelBlock f (Spin.quadPlus (k + 3) (GaloisField 2 f)) L' := by
  obtain ⟨r, ι, β₀, -, hlong, -, hrange, ⟨hinj, hr2, hnq⟩, a₁, a₂, b₁, b₂, hQ, h₁, h₂, h₀, hX,
    hX'⟩ := exists_blockModel_selfDualTwo_POmegaPlus_explicit_inj k f S hSU hS hodd he hadj hdeg₁
      hdeg₂ hJe
  exact siegelBlock_of_SU_model hf ψ hψ hl hn1 hne hM ι hinj hr2 hnq hlong hrange hQ h₁ h₂ h₀ hX hX'
theorem finish_POmegaPlus {G : Type} [Group G] {k : ℕ} {L : Subgroup G}
    (ψ : (ggU .POmegaPlus (k + 3) 1).K →* G)
    (hψ : ψ.ker ≤ Subgroup.center (ggU .POmegaPlus (k + 3) 1).K)
    {L' : Subgroup (ggU .POmegaPlus (k + 3) 1).K} (hL'map : L'.map ψ = L)
    (hB : SiegelBlock 1 (Spin.quadPlus (k + 3) (GaloisField 2 1)) L') :
    ∃ (t' : StatedLieTag) (n' : ℕ) (ψ' : (ggU t' n' 1).K →* G),
      StatedLieAdmissible t' n' 2 1 ∧ 2 ≤ (ggU t' n' 1).D.rank ∧
        ψ'.ker ≤ Subgroup.center (ggU t' n' 1).K ∧ ψ'.range = L ∧
        ∃ (γ : Fin (ggU .POmegaPlus (k + 3) 1).D.rank → ℤ) (δ : Fin (ggU t' n' 1).D.rank → ℤ)
          (model : SelectedRoot.SelectedSL2Model (ggU .POmegaPlus (k + 3) 1).D (GaloisField 2 1) γ)
          (model' : SelectedRoot.SelectedSL2Model (ggU t' n' 1).D (GaloisField 2 1) δ),
          ∃ u₀ : (ggU .POmegaPlus (k + 3) 1).K,
            ((ψ.comp (MulAut.conj u₀).toMonoidHom).comp model.phi).range =
              (ψ'.comp model'.phi).range := by
  obtain ⟨t', m, ι, β₀, hadm, hrank, hinj, hβ₀, hrange, a₁, a₂, b₁, b₂, hQ, h₁, h₂, h₀, hX, hX'⟩ :=
    hB
  let ψ₀ : ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 1))) →* G := ψ
  have hinjA : Function.Injective (Spin.spinAction (Spin.quadPlus (k + 3) (GaloisField 2 1))) := by
    have := Spin.isCentral_cliffordAlgebra_quadPlus (GaloisField 2 1) (k + 3)
    exact (MonoidHom.ker_eq_bot_iff _).mp
      (Spin.ker_spinAction_eq_bot_of_isCentral _ (CharP.cast_eq_zero (GaloisField 2 1) 2))
  have hE := (Spin.range_spinAction_quadPlus (n := k + 3) (K := GaloisField 2 1) (by omega)).ge
  obtain ⟨β, hβ, -, u, hu, -⟩ :=
    exists_conj_rootGroup_eq_siegelGroup_POmegaPlus (k + 3) (GaloisField 2 1) (by omega)
      a₁ a₂ b₁ b₂ hQ h₁ h₂ h₀
  obtain ⟨model, model', hpt⟩ := exists_models_of_siegel (D := (ggU .POmegaPlus (k + 3) 1).D)
    hinjA hE ι hinj hβ hβ₀ hQ h₁ h₂ h₀ hX hX' u hu
  refine ⟨t', m, ψ₀.comp ι, hadm, hrank, ?_, ?_, β, β₀, model, model', u, ?_⟩
  · intro y hy
    exact Subgroup.comap_center_le_center hinj (hψ hy)
  · rw [MonoidHom.range_comp, hrange]
    exact hL'map
  · congr 1
    ext A
    exact congrArg ψ₀ (hpt A)

theorem ggSecFiveQTwoFieldTwoSelectedAt_POmegaPlus :
    GGSecFiveQTwoFieldTwoSelectedAt .POmegaPlus := by
  intro G _ _ B Bs x L D J hC hq n f ψ hpres hdiag
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  have hf : 1 ≤ f := hadm.2.1
  have hn : 4 ≤ n := hadm.2.2
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  let ψ₀ : ↥(spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))) →* G := ψ
  have hψ : ψ₀.ker ≤ Subgroup.center _ := hker
  have hsstar := hC.1.2.2.2.2.2.2.1
  have hx3 : x ^ 3 = 1 := hsstar.1.1.2 x hsstar.2.1
  have hL : IsComponentOf L (ψ.range ⊓ Subgroup.centralizer {x}) := by
    rw [hrange]
    exact hC.isComponentOf_ggG0_inf
  obtain ⟨s, -, hsodd, ε, hε, L', hL'comp, hL'map⟩ :=
    RCKRP.rckF1_POmegaPlus Nat.prime_three (by norm_num) hx3 hf ψ rfl hker hdiag hL
  obtain ⟨lab, hl, hn1, hne, -, hM⟩ := hC.exists_markedModel_of_qTwo hq
  rw [← hL'map] at hM
  let j := Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))
  have hSU : ∀ a ∈ ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))),
      a ∈ j.range := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    exact ⟨s, ha.symm⟩
  have hS : ∀ a ∈ ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))),
      ∀ b ∈ ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))), Commute a b := by
    intro a ha b hb
    rw [Set.mem_singleton_iff] at ha hb
    rw [ha, hb]
  have hoddS : ∀ a ∈ ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))),
      Odd (orderOf a) := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    exact hsodd
  obtain ⟨e, he, heε, hcase⟩ := exists_isPrimIdemIn_of_isPrimAdjIdemIn_POmegaPlus k f _ hSU hS hε
  rcases hcase with rfl | ⟨hne', hpair, hεeq⟩
  · have hadj := hε.2.2.2.1
    by_cases hdeg2 : blockDegree (Algebra.adjoin (GaloisField 2 f)
        (Units.val '' ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))))) e < 2
    · by_cases hm4 : e.rank = 4 ∧ ∀ x y : Fin (k + 3) ⊕ Fin (k + 3) → GaloisField 2 f,
          Matrix.mulVec e x = x → Matrix.mulVec e y = y →
          Spin.quadPlus (k + 3) (GaloisField 2 f) x = 0 →
          Spin.quadPlus (k + 3) (GaloisField 2 f) y = 0 →
          QuadraticMap.polar (Spin.quadPlus (k + 3) (GaloisField 2 f)) x y = 0 →
          ¬ LinearIndependent (GaloisField 2 f) ![x, y]
      · exact (omegaFourMinus_false hf ψ₀ hψ hl hn1 hne _ hSU hS hoddS hε hL'comp hdeg2 hm4
          hM).elim
      · obtain ⟨hf1, hB⟩ :=
          selfDual_one hf ψ₀ hψ hl hn1 hne _ hSU hS hoddS he hadj hdeg2 hm4 hL'comp hM
        subst hf1
        exact finish_POmegaPlus ψ hker hL'map hB
    · by_cases hdeg4 : blockDegree (Algebra.adjoin (GaloisField 2 f)
          (Units.val '' ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))))) e < 4
      · obtain ⟨hf1, hB⟩ :=
          selfDual_two hf ψ₀ hψ hl hn1 hne _ hSU hS hoddS he hadj (by omega) hdeg4 hL'comp hM
        subst hf1
        exact finish_POmegaPlus ψ hker hL'map hB
      · exact (fieldExt_false hf ψ₀ hψ hl hn1 hne _ hSU hS hoddS hε hL'comp he heε
          (Or.inl ⟨rfl, by omega⟩) hM).elim
  · exfalso
    by_cases hdeg2 : blockDegree (Algebra.adjoin (GaloisField 2 f)
        (Units.val '' ({j s} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))))) e < 2
    · rw [hεeq] at hL'comp
      exact dualPair_one_false hf ψ₀ hψ hl hn1 hne (j s) ⟨s, rfl⟩ hsodd he hpair hdeg2 hL'comp hM
    · exact fieldExt_false hf ψ₀ hψ hl hn1 hne _ hSU hS hoddS hε hL'comp he heε
        (Or.inr ⟨hne', by omega⟩) hM

theorem ggSecFiveQTwoFieldTwoSelectedInput_of_POmegaMinus_exc
    (hMinus : GGSecFiveQTwoFieldTwoSelectedAt .POmegaMinus)
    (hEx : ∀ t, GGExcFive t → GGSecFiveQTwoFieldTwoSelectedAt t) :
    GGSecFiveQTwoFieldTwoSelectedInput :=
  FieldTwoPSp.ggSecFiveQTwoFieldTwoSelectedInput_of_POmega_exc
    ggSecFiveQTwoFieldTwoSelectedAt_POmegaPlus hMinus hEx

end Cert

end FieldTwoPOmega

end CFSG.StandardType

end
