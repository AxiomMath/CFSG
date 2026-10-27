module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DM1A
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt
public import CFSG.RankThree.GF2n.Stroth80.Sec9Defs
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.RankThree.GF2n
open scoped commutatorElement Matrix MatrixGroups

namespace HS9

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

structure ModDesc95 (hc : Ctx M Q Z B) (t : G) {K : Type} [Field K] [Finite K] {γ : G → K}
    (M₀ : Tim79.QuadModel Q Z K γ) (φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E))
    (Y₁ Y₂ : Type) [AddCommGroup Y₁] [Module K Y₁] [AddCommGroup Y₂] [Module K Y₂] where
  β₁ : Y₁ →ₗ[K] Y₁ →ₗ[K] K
  β₂ : Y₂ →ₗ[K] Y₂ →ₗ[K] K
  cV : M₀.E →ₗ[K] Matrix (Fin 2) (Fin 2) K
  cW : M₀.E →ₗ[K] (Fin 2 → Y₁) × (Fin 2 → Y₂)
  ρ : ↥(Rt M (LB M Q B) t) →* (SL(2, K) × SL(2, K))
  β₁_alt : ∀ y, β₁ y y = 0
  β₁_nd : ∀ y, (∀ y', β₁ y y' = 0) → y = 0
  β₂_alt : ∀ y, β₂ y y = 0
  β₂_nd : ∀ y, (∀ y', β₂ y y' = 0) → y = 0
  cV_inj : ∀ e ∈ M₀.img (Vt M (LB M Q B) B Z t), cV e = 0 → e = 0
  cV_surj : ∀ X : Matrix (Fin 2) (Fin 2) K, ∃ e ∈ M₀.img (Vt M (LB M Q B) B Z t), cV e = X
  cW_ker : ∀ w ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t)),
    cW w = 0 ↔ w ∈ M₀.img (Vt M (LB M Q B) B Z t)
  cW_surj : ∀ y : (Fin 2 → Y₁) × (Fin 2 → Y₂),
    ∃ w ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t)), cW w = y
  ρ_surj : Function.Surjective ρ
  cV_act : ∀ (r : ↥(Rt M (LB M Q B) t)) (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
    cV (φ ⟨(r : G), hc.Rt_le_H0 t r.2⟩ e) =
      ((ρ r).1 : Matrix (Fin 2) (Fin 2) K) * cV e * ((ρ r).2 : Matrix (Fin 2) (Fin 2) K)ᵀ
  cW_act : ∀ (r : ↥(Rt M (LB M Q B) t)) (w : M₀.E),
    w ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t)) →
    cW (φ ⟨(r : G), hc.Rt_le_H0 t r.2⟩ w) =
      (M1.smulVec ((ρ r).1 : Matrix (Fin 2) (Fin 2) K) (cW w).1,
        M1.smulVec ((ρ r).2 : Matrix (Fin 2) (Fin 2) K) (cW w).2)
  form : ∀ w ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t)),
    ∀ w' ∈ M₀.img (Wt Q (Vt M (LB M Q B) B Z t)), M₀.B w w' = M1.formW β₁ β₂ (cW w) (cW w')
  point : ∃ b : M₀.E, b ≠ 0 ∧ (∀ e, e ∈ M₀.img B ↔ ∃ c : K, e = c • b) ∧
    cV b = Matrix.single 0 0 1

section Swap

variable {hc : Ctx M Q Z B} {t : G} {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
  {Y₁ Y₂ : Type} [AddCommGroup Y₁] [Module K Y₁] [AddCommGroup Y₂] [Module K Y₂]

@[expose] noncomputable def ModDesc95.swap (D : ModDesc95 hc t M₀ φ Y₁ Y₂) :
    ModDesc95 hc t M₀ φ Y₂ Y₁ where
  β₁ := D.β₂
  β₂ := D.β₁
  cV := (Matrix.transposeLinearEquiv (Fin 2) (Fin 2) K K).toLinearMap ∘ₗ D.cV
  cW := (LinearEquiv.prodComm K (Fin 2 → Y₁) (Fin 2 → Y₂)).toLinearMap ∘ₗ D.cW
  ρ := (MonoidHom.prod (MonoidHom.snd _ _) (MonoidHom.fst _ _)).comp D.ρ
  β₁_alt := D.β₂_alt
  β₁_nd := D.β₂_nd
  β₂_alt := D.β₁_alt
  β₂_nd := D.β₁_nd
  cV_inj e he h0 := by
    refine D.cV_inj e he ?_
    simpa using h0
  cV_surj X := by
    obtain ⟨e, he, h⟩ := D.cV_surj Xᵀ
    exact ⟨e, he, by simp [h]⟩
  cW_ker w hw := by
    rw [← D.cW_ker w hw]
    simp [Prod.ext_iff]
    tauto
  cW_surj y := by
    obtain ⟨w, hw, h⟩ := D.cW_surj y.swap
    exact ⟨w, hw, by simp [h]⟩
  ρ_surj := by
    intro p
    obtain ⟨r, hr⟩ := D.ρ_surj p.swap
    exact ⟨r, by simp [hr]⟩
  cV_act r e he := by
    have h := D.cV_act r e he
    show (D.cV (φ ⟨(r : G), hc.Rt_le_H0 t r.2⟩ e))ᵀ =
      ((D.ρ r).2 : Matrix (Fin 2) (Fin 2) K) * (D.cV e)ᵀ * ((D.ρ r).1 : Matrix (Fin 2) (Fin 2) K)ᵀ
    rw [h, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.mul_assoc]
  cW_act r w hw := by
    have h := D.cW_act r w hw
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.prodComm_apply, h,
      Prod.swap, MonoidHom.comp_apply, MonoidHom.prod_apply, MonoidHom.coe_snd,
      MonoidHom.coe_fst]
  form w hw w' hw' := by
    rw [D.form w hw w' hw']
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.prodComm_apply, Prod.swap,
      M1.formW]
    ring
  point := by
    obtain ⟨b, hb, hB, hcb⟩ := D.point
    exact ⟨b, hb, hB, by simp [hcb]⟩

end Swap

end HS9


@[expose] def Step95M1Statement (n0 : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec9Hyp hc n t → n0 ≤ n →
    ∀ {K : Type} [Field K] [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ},
      GlobalModelData M Q Z γ M₀ → ∀ φ : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E),
      (∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φ m (M₀.π x)) →
      (∀ m : H0 M Z, φ m = 1 ↔ (m : G) ∈ Q) →
      ∃ (Y₁ Y₂ : Type) (_ : AddCommGroup Y₁) (_ : Module K Y₁) (_ : AddCommGroup Y₂)
        (_ : Module K Y₂), Nonempty (HS9.ModDesc95 hc t M₀ φ Y₁ Y₂)

end CFSG.RankThree.GF2n.Stroth80
