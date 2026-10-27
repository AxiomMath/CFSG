module

public import CFSG.LocalAnalysis.StandardType.TableC.POmegaLeafDefs
public import CFSG.LocalAnalysis.StandardType.TableC.GramBlockDegree
public import CFSG.LocalAnalysis.StandardType.TableC.OrthGram
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepACore
public import CFSG.ClassicalInvolution.SmallOrth.Orth3Block
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om6
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTri
public import CFSG.RankThree.PartOne.K159.RowFourFixed
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmas
public import CFSG.LocalAnalysis.ComponentInitial.BlockCentralQuotient
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageCases
public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmFix
public import CFSG.LocalAnalysis.ComponentClassification.EvenLieFieldExponent
public import CFSG.RankThree.PartOne.TCP.AlModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T123CBlockOrthA
public import CFSG.CGT.Timmesfeld75.Forms
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om5
public import CFSG.RankThree.GF2n.Stroth80.Anisotropic
public import CFSG.RankThree.GF2n.Stroth80.FrobClause
public import CFSG.RankThree.GF2n.Stroth80.GlobalModel
public import CFSG.RankThree.GF2n.Stroth80.Sec36
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel
public import CFSG.RankThree.PartOne.TCP.AlSL2

public section

namespace CFSG.StandardType

open Module QuadraticMap
open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal CFSG.RankThree.Classical2
open CFSG.StandardType.ClassicalPosition

section CaseA

private lemma a0p_spinMatrix_injective (F : Type) [Field F] [CharP F 2] (n : ℕ) :
    Function.Injective (Spin.spinMatrix (Spin.quadPlus n F)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  exact Spin.ker_spinMatrix_quadPlus_eq_bot (CharP.cast_eq_zero F 2)

private lemma a0p_conj_of_lift {F : Type} [Field F] [CharP F 2] {n : ℕ}
    {X : Type} [Group X] (ψ : spinGroup (Spin.quadPlus n F) →* X)
    {d : X} {s₀ : spinGroup (Spin.quadPlus n F)}
    (hsl : IsGLLift (Spin.spinMatrix (Spin.quadPlus n F)) ψ
      (Spin.spinMatrix (Spin.quadPlus n F) s₀) d) :
    ∀ u, d⁻¹ * ψ u * d = ψ (s₀ * u * s₀⁻¹) := by
  intro u
  obtain ⟨u', hu'j, hu'ψ⟩ := hsl u
  have h : u' = s₀ * u * s₀⁻¹ :=
    a0p_spinMatrix_injective F n (by rw [hu'j]; simp only [map_mul, map_inv])
  rw [h] at hu'ψ
  exact hu'ψ

private lemma a0p_spin_pow_eq_one {F : Type} [Field F] [CharP F 2] {n : ℕ} (hn : 3 ≤ n)
    {X : Type} [Group X] (ψ : spinGroup (Spin.quadPlus n F) →* X)
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus n F)))
    {d : X} {p : ℕ} (hdp : d ^ p = 1)
    {s₀ : spinGroup (Spin.quadPlus n F)}
    (hconj : ∀ u, d⁻¹ * ψ u * d = ψ (s₀ * u * s₀⁻¹)) :
    s₀ ^ p = 1 := by
  have hinj := a0p_spinMatrix_injective F n
  have hsl : IsGLLift (Spin.spinMatrix (Spin.quadPlus n F)) ψ
      (Spin.spinMatrix (Spin.quadPlus n F) s₀) d := by
    intro u
    exact ⟨s₀ * u * s₀⁻¹, by simp only [map_mul, map_inv], hconj u⟩
  have hslp : IsGLLift (Spin.spinMatrix (Spin.quadPlus n F)) ψ
      (Spin.spinMatrix (Spin.quadPlus n F) (s₀ ^ p)) 1 := by
    have h := hsl.pow p
    rw [hdp, ← map_pow] at h
    exact h
  apply conj_eq_unique_POmegaPlus n F hn ψ hψ (s' := 1)
  intro u
  obtain ⟨u', hu'j, hu'ψ⟩ := hslp u
  have h : u' = (s₀ ^ p) * u * (s₀ ^ p)⁻¹ :=
    hinj (by rw [hu'j]; simp only [map_mul, map_inv])
  rw [h] at hu'ψ
  simpa using hu'ψ.symm

theorem ggSixTCLiftBPOmegaPlus_holds
    {X : Type} [Group X] [Finite X] (k f : ℕ) (ψ : (ggU .POmegaPlus (k + 3) f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hpos : GGSixTCPos .POmegaPlus (k + 3) f ψ p G₀ B₁ D J L x)
    (ℓ : ↥D →* spinGroup (ggOmQuadPlus k f))
    (hℓ : ∀ d : ↥D, IsGLLift (ggOmSpinPlus k f) ψ (ggOmSpinPlus k f (ℓ d)) (d : X)) :
    ∃ ℓB : ↥B₁ →* spinGroup (ggOmQuadPlus k f),
      (∀ b : ↥B₁, IsGLLift (ggOmSpinPlus k f) ψ (ggOmSpinPlus k f (ℓB b)) (b : X)) ∧
      (∀ b : ↥B₁, ℓB b ^ p = 1) ∧ (∀ d : ↥D, ℓB ⟨(d : X), hpos.D_le d.2⟩ = ℓ d) := by
  let F := GaloisField 2 f
  let n := k + 3
  let j : spinGroup (Spin.quadPlus n F) →* GL (Fin n ⊕ Fin n) F :=
    Spin.spinMatrix (Spin.quadPlus n F)
  let ψ' : spinGroup (Spin.quadPlus n F) →* X := ψ
  have hker : ψ'.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus n F)) := hpos.ker_le
  have hchoose : ∀ b : ↥B₁, ∃ s : spinGroup (Spin.quadPlus n F),
      ∀ u : spinGroup (Spin.quadPlus n F),
        (b : X)⁻¹ * ψ' u * (b : X) = ψ' (s * u * s⁻¹) := by
    intro b
    exact exists_conj_eq_POmegaPlus n F (by omega) ψ' hker
      (hpos.innerDiag (b : X) b.2)
  let g : ↥B₁ → spinGroup (Spin.quadPlus n F) := fun b => Classical.choose (hchoose b)
  have hg : ∀ b : ↥B₁, ∀ u : spinGroup (Spin.quadPlus n F),
      (b : X)⁻¹ * ψ' u * (b : X) = ψ' (g b * u * (g b)⁻¹) :=
    fun b => Classical.choose_spec (hchoose b)
  have hiff : ∀ (s : spinGroup (Spin.quadPlus n F)) (b : X),
      IsGLLift j ψ' (j s) b ↔
        ∀ u : spinGroup (Spin.quadPlus n F), b⁻¹ * ψ' u * b = ψ' (s * u * s⁻¹) := by
    intro s b
    constructor
    · intro hs
      exact a0p_conj_of_lift ψ' hs
    · intro h u
      exact ⟨s * u * s⁻¹, by simp only [map_mul, map_inv], h u⟩
  have hg_lift : ∀ b : ↥B₁, IsGLLift j ψ' (j (g b)) (b : X) :=
    fun b => (hiff (g b) (b : X)).mpr (hg b)
  have hlift_unique : ∀ {b : X} {s s' : spinGroup (Spin.quadPlus n F)},
      IsGLLift j ψ' (j s) b → IsGLLift j ψ' (j s') b → s = s' := by
    intro b s s' hs hs'
    refine conj_eq_unique_POmegaPlus n F (by omega) ψ' hker (fun u => ?_)
    exact ((hiff s b).mp hs u).symm.trans ((hiff s' b).mp hs' u)
  have hone : g 1 = 1 := by
    refine conj_eq_unique_POmegaPlus n F (by omega) ψ' hker (fun u => ?_)
    exact (hg 1 u).symm.trans (by simp)
  have hmul : ∀ b b' : ↥B₁, g (b * b') = g b * g b' := by
    intro b b'
    have hbb' : Commute (b : X) (b' : X) :=
      congrArg Subtype.val (hpos.elemAbelian.1.is_comm.comm b b')
    have hanti : g (b * b') = g b' * g b := by
      have h1 : IsGLLift j ψ' (j (g (b * b'))) ((b : X) * (b' : X)) := by
        simpa using hg_lift (b * b')
      have h2 : IsGLLift j ψ' (j (g b' * g b)) ((b : X) * (b' : X)) := by
        have h := IsGLLift.mul (hg_lift b) (hg_lift b')
        simpa only [map_mul] using h
      exact hlift_unique h1 h2
    have hcomm : g b' * g b = g b * g b' :=
      (conj_eq_commute_POmegaPlus n F (by omega) ψ' hker hbb' (hg b) (hg b')).eq.symm
    rw [hanti, hcomm]
  have hpow : ∀ b : ↥B₁, g b ^ p = 1 := by
    intro b
    exact a0p_spin_pow_eq_one (n := n) (F := F) (by omega) ψ' hker
      (hpos.elemAbelian.2 (b : X) b.2) (hg b)
  let ℓB : ↥B₁ →* spinGroup (Spin.quadPlus n F) :=
    { toFun := g, map_one' := hone, map_mul' := hmul }
  refine ⟨ℓB, ?_, ?_, ?_⟩
  · intro b
    exact hg_lift b
  · intro b
    exact hpow b
  · intro d
    exact hlift_unique (hg_lift ⟨(d : X), hpos.D_le d.2⟩) (hℓ d)

private lemma a0m_spinMatrix_injective (F : Type) [Field F] [Finite F] [CharP F 2] (n : ℕ)
    {bq cq : F} (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) :
    Function.Injective (Spin.spinMatrix (Spin.quadMinus n F bq cq)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  exact Spin.ker_spinMatrix_quadMinus_eq_bot hirr (CharP.cast_eq_zero F 2)

private lemma a0m_conj_of_lift {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} {bq cq : F}
    (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0)
    {X : Type} [Group X] (ψ : spinGroup (Spin.quadMinus n F bq cq) →* X)
    {b : X} {s₀ : spinGroup (Spin.quadMinus n F bq cq)}
    (hsl : IsGLLift (Spin.spinMatrix (Spin.quadMinus n F bq cq)) ψ
      (Spin.spinMatrix (Spin.quadMinus n F bq cq) s₀) b) :
    ∀ u, b⁻¹ * ψ u * b = ψ (s₀ * u * s₀⁻¹) := by
  intro u
  obtain ⟨u', hu'j, hu'ψ⟩ := hsl u
  have h : u' = s₀ * u * s₀⁻¹ :=
    a0m_spinMatrix_injective F n hirr (by rw [hu'j]; simp only [map_mul, map_inv])
  rw [h] at hu'ψ
  exact hu'ψ

private lemma a0m_spin_pow_eq_one {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} {bq cq : F}
    (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n)
    {X : Type} [Group X] (ψ : spinGroup (Spin.quadMinus n F bq cq) →* X)
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadMinus n F bq cq)))
    {b : X} {p : ℕ} (hbp : b ^ p = 1)
    {s₀ : spinGroup (Spin.quadMinus n F bq cq)}
    (hconj : ∀ u, b⁻¹ * ψ u * b = ψ (s₀ * u * s₀⁻¹)) :
    s₀ ^ p = 1 := by
  have hsl : IsGLLift (Spin.spinMatrix (Spin.quadMinus n F bq cq)) ψ
      (Spin.spinMatrix (Spin.quadMinus n F bq cq) s₀) b := by
    intro u
    exact ⟨s₀ * u * s₀⁻¹, by simp only [map_mul, map_inv], hconj u⟩
  have hslp : IsGLLift (Spin.spinMatrix (Spin.quadMinus n F bq cq)) ψ
      (Spin.spinMatrix (Spin.quadMinus n F bq cq) (s₀ ^ p)) 1 := by
    have h := hsl.pow p
    rw [hbp, ← map_pow] at h
    exact h
  apply conj_eq_unique_POmegaMinus n hirr hn ψ hψ (s' := 1)
  intro u
  obtain ⟨u', hu'j, hu'ψ⟩ := hslp u
  have h : u' = (s₀ ^ p) * u * (s₀ ^ p)⁻¹ :=
    a0m_spinMatrix_injective F n hirr (by rw [hu'j]; simp only [map_mul, map_inv])
  rw [h] at hu'ψ
  simpa using hu'ψ.symm

theorem ggSixTCLiftBPOmegaMinus_holds
    {X : Type} [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .POmegaMinus n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X)
    (hpos : GGSixTCPos .POmegaMinus n f ψ p G₀ B₁ D J L x)
    (ℓ : ↥D →* spinGroup (ggOmQuadMinus n f))
    (hℓ : ∀ d : ↥D, IsGLLift (ggOmSpinMinus n f) ψ (ggOmSpinMinus n f (ℓ d)) (d : X)) :
    ∃ ℓB : ↥B₁ →* spinGroup (ggOmQuadMinus n f),
      (∀ b : ↥B₁, IsGLLift (ggOmSpinMinus n f) ψ (ggOmSpinMinus n f (ℓB b)) (b : X)) ∧
      (∀ b : ↥B₁, ℓB b ^ p = 1) ∧ (∀ d : ↥D, ℓB ⟨(d : X), hpos.D_le d.2⟩ = ℓ d) := by
  let U := ↥(spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
    (minusCoeffs 2 f).2))
  let j : U →* GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (GaloisField 2 f) :=
    Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2)
  let ψ' : U →* X := ψ
  have hirr : ∀ s : GaloisField 2 f,
      s ^ 2 + (minusCoeffs 2 f).1 * s + (minusCoeffs 2 f).2 ≠ 0 := minusCoeffs_irr 2 f
  have hn4 : 4 ≤ n := (hpos.model.admissible).2.2
  have hker : ψ'.ker ≤ Subgroup.center U := hpos.ker_le
  have hchoose : ∀ b : ↥B₁, ∃ s : U,
      ∀ u : U, (b : X)⁻¹ * ψ' u * (b : X) = ψ' (s * u * s⁻¹) := by
    intro b
    exact exists_conj_eq_POmegaMinus n hirr hn4 ψ' hker (hpos.innerDiag (b : X) b.2)
  let g : ↥B₁ → U := fun b => Classical.choose (hchoose b)
  have hg : ∀ b : ↥B₁, ∀ u : U,
      (b : X)⁻¹ * ψ' u * (b : X) = ψ' (g b * u * (g b)⁻¹) :=
    fun b => Classical.choose_spec (hchoose b)
  have hiff : ∀ (a : U) (b : X),
      IsGLLift j ψ' (j a) b ↔
        ∀ u : U, b⁻¹ * ψ' u * b = ψ' (a * u * a⁻¹) := by
    intro a b
    constructor
    · intro hs u
      exact a0m_conj_of_lift hirr ψ' hs u
    · intro h u
      exact ⟨a * u * a⁻¹, by simp [map_mul, map_inv], h u⟩
  have hlift_unique : ∀ {b : X} {a a' : U},
      IsGLLift j ψ' (j a) b → IsGLLift j ψ' (j a') b → a = a' := by
    intro b a a' ha ha'
    have h1 := (hiff a b).mp ha
    have h2 := (hiff a' b).mp ha'
    exact conj_eq_unique_POmegaMinus n hirr hn4 ψ' hker (fun u => by rw [← h1 u, ← h2 u])
  have hg_lift : ∀ b : ↥B₁, IsGLLift j ψ' (j (g b)) (b : X) :=
    fun b => (hiff (g b) (b : X)).mpr (hg b)
  have hone : g 1 = 1 := by
    apply conj_eq_unique_POmegaMinus n hirr hn4 ψ' hker
    intro u
    rw [← (hiff (g 1) (1 : X)).mp (hg_lift 1) u]
    simp
  have hmul : ∀ b b' : ↥B₁, g (b * b') = g b * g b' := by
    intro b b'
    have hbb' : Commute (b : X) (b' : X) :=
      congrArg Subtype.val (hpos.elemAbelian.1.is_comm.comm b b')
    have hanti : g (b * b') = g b' * g b := by
      have h1 : IsGLLift j ψ' (j (g (b * b'))) ((b : X) * (b' : X)) := by
        simpa using hg_lift (b * b')
      have h2 : IsGLLift j ψ' (j (g b' * g b)) ((b : X) * (b' : X)) := by
        have h := IsGLLift.mul (hg_lift b) (hg_lift b')
        simpa only [map_mul] using h
      exact hlift_unique h1 h2
    have hcomm : g b' * g b = g b * g b' :=
      (conj_eq_commute_POmegaMinus n hirr hn4 ψ' hker hbb' (hg b) (hg b')).eq.symm
    rw [hanti, hcomm]
  have hpow : ∀ b : ↥B₁, g b ^ p = 1 := by
    intro b
    exact a0m_spin_pow_eq_one hirr hn4 ψ' hker (hpos.elemAbelian.2 (b : X) b.2) (hg b)
  let ℓB : ↥B₁ →* U := { toFun := g, map_one' := hone, map_mul' := hmul }
  refine ⟨ℓB, ?_, ?_, ?_⟩
  · intro b
    change IsGLLift j ψ' (j (g b)) (b : X)
    exact hg_lift b
  · intro b
    change g b ^ p = 1
    exact hpow b
  · intro d
    change g ⟨(d : X), hpos.D_le d.2⟩ = ℓ d
    apply hlift_unique (hg_lift ⟨(d : X), hpos.D_le d.2⟩)
    exact hℓ d

section A1Helpers

open CFSG.ClassicalGroups.Orthogonal.Small

private lemma a1_polar_eq_dot {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (x y : ι → F) :
    QuadraticMap.polar Q x y =
      dotProduct x ((LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)).mulVec y) := by
  have h1 : (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Q)) =
      LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q) := rfl
  rw [h1]
  rw [← Matrix.toBilin'_apply' (LinearMap.BilinForm.toMatrix' (QuadraticMap.polarBilin Q)) x y,
    Matrix.toBilin'_toMatrix', QuadraticMap.polarBilin_apply_apply]

private lemma a1_selfadj {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (hQ : (polarBilin Q).Nondegenerate) {e : Matrix ι ι F}
    (hadj : formAdj (RingHom.id F) (LinearMap.toMatrix₂' F (polarBilin Q)) e = e)
    (v w : ι → F) :
    QuadraticMap.polar Q (e.mulVec v) w = QuadraticMap.polar Q v (e.mulVec w) := by
  set G := LinearMap.toMatrix₂' F (polarBilin Q)
  have hG : IsUnit G.det := CFSG.StandardType.TableC.polarGram_isUnit_det Q hQ
  have htrans : Matrix.transpose e * G = G * e := by
    have heid : e.map ⇑(RingHom.id F) = e := by
      ext i j
      rfl
    have h : G * (G⁻¹ * Matrix.transpose e * G) = G * e := by
      have hh := congrArg (fun M => G * M) hadj
      rw [formAdj, heid] at hh
      exact hh
    calc Matrix.transpose e * G
        = (1 : Matrix ι ι F) * (Matrix.transpose e * G) := (Matrix.one_mul _).symm
      _ = (G * G⁻¹) * (Matrix.transpose e * G) := by rw [Matrix.mul_nonsing_inv G hG]
      _ = G * (G⁻¹ * (Matrix.transpose e * G)) := by rw [Matrix.mul_assoc]
      _ = G * (G⁻¹ * Matrix.transpose e * G) := by rw [Matrix.mul_assoc]
      _ = G * e := h
  rw [a1_polar_eq_dot Q (e.mulVec v) w, a1_polar_eq_dot Q v (e.mulVec w)]
  calc (e.mulVec v) ⬝ᵥ (G.mulVec w)
      = Matrix.vecMul (e.mulVec v) G ⬝ᵥ w := Matrix.dotProduct_mulVec _ _ _
    _ = Matrix.vecMul v (Matrix.transpose e * G) ⬝ᵥ w := by rw [Matrix.vecMul_mulVec]
    _ = Matrix.vecMul v (G * e) ⬝ᵥ w := by rw [htrans]
    _ = v ⬝ᵥ (G.mulVec (e.mulVec w)) := by
          rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec]

private lemma a1_idem {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] {e : Matrix ι ι F}
    (hee : IsIdempotentElem e) : IsIdempotentElem (Matrix.mulVecLin e) := by
  rw [isIdempotentElem_iff]
  apply LinearMap.ext
  intro v
  rw [End.mul_apply, Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
    hee.eq]

private lemma a1_orth {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (hQ : (polarBilin Q).Nondegenerate) {e : Matrix ι ι F}
    (hadj : formAdj (RingHom.id F) (LinearMap.toMatrix₂' F (polarBilin Q)) e = e) :
    ∀ u ∈ LinearMap.range (Matrix.mulVecLin e),
      ∀ w ∈ LinearMap.ker (Matrix.mulVecLin e), QuadraticMap.polar Q u w = 0 := by
  rintro u ⟨v, rfl⟩ w hw
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hw
  rw [Matrix.mulVecLin_apply, a1_selfadj Q hQ hadj v w, hw]
  simp

private lemma a1_regular {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (hQ : (polarBilin Q).Nondegenerate) {e : Matrix ι ι F}
    (hee : IsIdempotentElem e)
    (hadj : formAdj (RingHom.id F) (LinearMap.toMatrix₂' F (polarBilin Q)) e = e) :
    (polarBilin (Q.comp (LinearMap.range (Matrix.mulVecLin e)).subtype)).Nondegenerate :=
  nondegenerate_comp_subtype
    (W := LinearMap.range (Matrix.mulVecLin e))
    (W' := LinearMap.ker (Matrix.mulVecLin e))
    hQ (LinearMap.IsIdempotentElem.isCompl (a1_idem hee)) (a1_orth Q hQ hadj)

private lemma a1_hns {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) {e : Matrix ι ι F}
    (hminus : ∀ U : Submodule F (ι → F), U ≤ LinearMap.range (Matrix.mulVecLin e) →
      finrank F U = 2 → ∃ u ∈ U, Q u ≠ 0) :
    ∀ U : Submodule F (LinearMap.range (Matrix.mulVecLin e)),
      finrank F U = 2 →
      ∃ u ∈ U, (Q.comp (LinearMap.range (Matrix.mulVecLin e)).subtype) u ≠ 0 := by
  intro U hU
  have hle : Submodule.map (LinearMap.range (Matrix.mulVecLin e)).subtype U ≤
      LinearMap.range (Matrix.mulVecLin e) := Submodule.map_subtype_le _ _
  have hdim : finrank F
      (Submodule.map (LinearMap.range (Matrix.mulVecLin e)).subtype U) = 2 := by
    rw [Submodule.finrank_map_subtype_eq, hU]
  obtain ⟨u, hu, hQu⟩ := hminus _ hle hdim
  obtain ⟨w, hw, hwu⟩ := Submodule.mem_map.mp hu
  exact ⟨w, hw, by
    show Q ((LinearMap.range (Matrix.mulVecLin e)).subtype w) ≠ 0
    rw [hwu]
    exact hQu⟩

private lemma a1_finrank {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] {e : Matrix ι ι F}
    (hrk : Matrix.rank e = 4) :
    Module.finrank F (LinearMap.range (Matrix.mulVecLin e)) = 4 := by
  rw [← hrk]
  rfl

private lemma a1_odd_orderOf_pow_prime {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {x : G} (hx : x ^ p = 1) : Odd (orderOf x) := by
  have hdvd : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hx
  rcases hp.eq_one_or_self_of_dvd (orderOf x) hdvd with h1 | hp'
  · rw [h1]; exact odd_one
  · rw [hp']; exact hp.odd_of_ne_two hp2

private lemma a1_rho_mem_stab {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [CharP F 2]
    (Q : QuadraticForm F (ι → F)) (E : Subgroup (spinGroup Q)) {e : Matrix ι ι F}
    (hcomm : ∀ x ∈ E, ((Spin.spinMatrix Q x : GL ι F) : Matrix ι ι F) * e =
      e * ((Spin.spinMatrix Q x : GL ι F) : Matrix ι ι F)) (x : E) :
    Spin.spinAction Q (x : spinGroup Q) ∈
      stabSub (LinearMap.range (Matrix.mulVecLin e)) := by
  rw [mem_stabSub]
  have hfwd : ∀ (g : spinGroup Q), g ∈ E →
      ∀ y ∈ LinearMap.range (Matrix.mulVecLin e),
      Spin.spinAction Q g y ∈ LinearMap.range (Matrix.mulVecLin e) := by
    intro g hg y ⟨v, hv⟩
    refine ⟨((Spin.spinMatrix Q g : GL ι F) : Matrix ι ι F).mulVec v, ?_⟩
    have hy : y = e.mulVec v := by rw [← hv, Matrix.mulVecLin_apply]
    rw [hy, ← Spin.spinMatrix_mulVec, Matrix.mulVecLin_apply]
    simp only [Matrix.mulVec_mulVec]
    rw [hcomm g hg]
  intro y
  constructor
  · exact hfwd (x : spinGroup Q) x.2 y
  · intro hy
    have h := hfwd (x : spinGroup Q)⁻¹ (E.inv_mem x.2)
      (Spin.spinAction Q (x : spinGroup Q) y) hy
    have hy' : Spin.spinAction Q ((x : spinGroup Q)⁻¹)
        (Spin.spinAction Q (x : spinGroup Q) y) = y := by
      rw [map_inv]
      simp
    rwa [hy'] at h

private noncomputable def a1_rho {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [CharP F 2]
    (Q : QuadraticForm F (ι → F)) (E : Subgroup (spinGroup Q)) {e : Matrix ι ι F}
    (hcomm : ∀ x ∈ E, ((Spin.spinMatrix Q x : GL ι F) : Matrix ι ι F) * e =
      e * ((Spin.spinMatrix Q x : GL ι F) : Matrix ι ι F)) :
    E →* (LinearMap.range (Matrix.mulVecLin e) ≃ₗ[F] LinearMap.range (Matrix.mulVecLin e)) :=
  (resHom (LinearMap.range (Matrix.mulVecLin e))).comp
    (((Spin.spinAction Q).comp E.subtype).codRestrict
      (stabSub (LinearMap.range (Matrix.mulVecLin e))) (a1_rho_mem_stab Q E hcomm))

private lemma a1_rho_mem_orthogonalGroup {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [CharP F 2] (Q : QuadraticForm F (ι → F)) (E : Subgroup (spinGroup Q)) {e : Matrix ι ι F}
    (hcomm : ∀ x ∈ E, ((Spin.spinMatrix Q x : GL ι F) : Matrix ι ι F) * e =
      e * ((Spin.spinMatrix Q x : GL ι F) : Matrix ι ι F)) (x : E) :
    a1_rho Q E hcomm x ∈ TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (LinearMap.range (Matrix.mulVecLin e)).subtype) := by
  have hmem := a1_rho_mem_stab Q E hcomm x
  have hrho : a1_rho Q E hcomm x =
      resHom (LinearMap.range (Matrix.mulVecLin e))
        ⟨Spin.spinAction Q (x : spinGroup Q), hmem⟩ := rfl
  rw [hrho]
  exact resHom_mem_orthogonalGroup
    (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr
      (fun v => Spin.map_spinAction Q (x : spinGroup Q) v)) hmem

private lemma a1_rho_eq_one_iff {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [CharP F 2]
    (Q : QuadraticForm F (ι → F)) (E : Subgroup (spinGroup Q)) {e : Matrix ι ι F}
    (hcomm : ∀ x ∈ E, ((Spin.spinMatrix Q x : GL ι F) : Matrix ι ι F) * e =
      e * ((Spin.spinMatrix Q x : GL ι F) : Matrix ι ι F)) (x : E) :
    a1_rho Q E hcomm x = 1 ↔
      ((Spin.spinMatrix Q (x : spinGroup Q) : GL ι F) : Matrix ι ι F) * e = e := by
  have hmem := a1_rho_mem_stab Q E hcomm x
  have hrho : a1_rho Q E hcomm x =
      resHom (LinearMap.range (Matrix.mulVecLin e))
        ⟨Spin.spinAction Q (x : spinGroup Q), hmem⟩ := rfl
  rw [hrho]
  constructor
  · intro hx
    have hfix : ∀ w : LinearMap.range (Matrix.mulVecLin e),
        Spin.spinAction Q (x : spinGroup Q) (w : ι → F) = (w : ι → F) := by
      intro w
      have h1 : resHom (LinearMap.range (Matrix.mulVecLin e))
          ⟨Spin.spinAction Q (x : spinGroup Q), hmem⟩ w = w := by
        have h := DFunLike.congr_fun hx w
        simpa using h
      have h2 := congrArg Subtype.val h1
      rwa [resHom_apply] at h2
    refine Matrix.mulVec_injective ?_
    funext v
    have hw : e.mulVec v ∈ LinearMap.range (Matrix.mulVecLin e) :=
      LinearMap.mem_range.mpr ⟨v, Matrix.mulVecLin_apply e v⟩
    have hv := hfix ⟨e.mulVec v, hw⟩
    rw [← Spin.spinMatrix_mulVec, Matrix.mulVec_mulVec] at hv
    exact hv
  · intro hx
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    rw [resHom_apply]
    change Spin.spinAction Q (x : spinGroup Q) (w : ι → F) = (w : ι → F)
    obtain ⟨v, hv⟩ := w.2
    rw [← hv, Matrix.mulVecLin_apply, ← Spin.spinMatrix_mulVec, Matrix.mulVec_mulVec, hx]

private lemma a1_rho_odd {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [CharP F 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (Q : QuadraticForm F (ι → F))
    (E : Subgroup (spinGroup Q)) (hE : IsElemAbelian p E) {e : Matrix ι ι F}
    (hcomm : ∀ x ∈ E, ((Spin.spinMatrix Q x : GL ι F) : Matrix ι ι F) * e =
      e * ((Spin.spinMatrix Q x : GL ι F) : Matrix ι ι F)) (x : E) :
    Odd (orderOf (a1_rho Q E hcomm x)) := by
  refine a1_odd_orderOf_pow_prime hp hp2 ?_
  have hxp : x ^ p = 1 := Subtype.ext (hE.2 (x : spinGroup Q) x.2)
  rw [← map_pow, hxp, map_one]

private lemma a1_rho_mem_orthDerived {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    [CharP F 2] (Q : QuadraticForm F (ι → F)) (hQ : (polarBilin Q).Nondegenerate)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (E : Subgroup (spinGroup Q))
    (hE : IsElemAbelian p E) {e : Matrix ι ι F} (hee : IsIdempotentElem e)
    (hadj : formAdj (RingHom.id F) (LinearMap.toMatrix₂' F (polarBilin Q)) e = e)
    (hcomm : ∀ x ∈ E, ((Spin.spinMatrix Q x : GL ι F) : Matrix ι ι F) * e =
      e * ((Spin.spinMatrix Q x : GL ι F) : Matrix ι ι F)) (hrk : Matrix.rank e = 4)
    (hminus : ∀ U : Submodule F (ι → F), U ≤ LinearMap.range (Matrix.mulVecLin e) →
      finrank F U = 2 → ∃ u ∈ U, Q u ≠ 0) (x : E) :
    a1_rho Q E hcomm x ∈
      orthDerived (Q.comp (LinearMap.range (Matrix.mulVecLin e)).subtype) := by
  refine CFSG.LocalAnalysis.GLTheoremA.Y10F.OmEngine.mem_orthDerived_of_odd_of_finrank_four
    (a1_regular Q hQ hee hadj) ?_ (a1_hns Q hminus)
    (a1_rho_mem_orthogonalGroup Q E hcomm x) ?_
  · exact a1_finrank hrk
  · exact a1_rho_odd hp hp2 Q E hE hcomm x

private lemma a1_rho_ker {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [CharP F 2]
    (Q : QuadraticForm F (ι → F)) (E : Subgroup (spinGroup Q)) {e : Matrix ι ι F}
    (hcomm : ∀ x ∈ E, ((Spin.spinMatrix Q x : GL ι F) : Matrix ι ι F) * e =
      e * ((Spin.spinMatrix Q x : GL ι F) : Matrix ι ι F)) :
    (a1_rho Q E hcomm).ker =
      ((glFixing e).comap (Spin.spinMatrix Q)).subgroupOf E := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_comap, a1_rho_eq_one_iff]
  rfl

private lemma a1_isElemAbelian_top {G : Type} [Group G] {p : ℕ} {E : Subgroup G}
    (hE : IsElemAbelian p E) : IsElemAbelian p (⊤ : Subgroup E) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    exact hE.comm (a : E).2 (b : E).2
  · intro x _
    exact Subtype.ext (hE.2 (x : G) x.2)

end A1Helpers

theorem card_le_mul_of_minusFour {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    [CharP F 2] (Q : QuadraticForm F (ι → F)) (hQ : (polarBilin Q).Nondegenerate)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (E : Subgroup (spinGroup Q)) (hE : IsElemAbelian p E)
    {e : Matrix ι ι F} (hee : IsIdempotentElem e)
    (hadj : formAdj (RingHom.id F) (LinearMap.toMatrix₂' F (polarBilin Q)) e = e)
    (hcomm : ∀ x ∈ E, ((Spin.spinMatrix Q x : GL ι F) : Matrix ι ι F) * e =
      e * ((Spin.spinMatrix Q x : GL ι F) : Matrix ι ι F))
    (hrk : Matrix.rank e = 4)
    (hminus : ∀ U : Submodule F (ι → F), U ≤ LinearMap.range (Matrix.mulVecLin e) →
      finrank F U = 2 → ∃ u ∈ U, Q u ≠ 0) :
    Nat.card ↥E ≤ p * Nat.card ↥(E ⊓ (glFixing e).comap (Spin.spinMatrix Q)) := by
  let W := LinearMap.range (Matrix.mulVecLin e)
  let K := (glFixing e).comap (Spin.spinMatrix Q)
  have hρder : ∀ x : E, a1_rho Q E hcomm x ∈ orthDerived (Q.comp W.subtype) :=
    fun x => a1_rho_mem_orthDerived Q hQ hp hp2 E hE hee hadj hcomm hrk hminus x
  let ρd : E →* orthDerived (Q.comp W.subtype) :=
    (a1_rho Q E hcomm).codRestrict (orthDerived (Q.comp W.subtype)) hρder
  obtain ⟨E', hField, hFinite, hCharP, -, he3⟩ :=
    CFSG.RankThree.PartOne.K159.exists_orthDerived_four_sl2 (Q.comp W.subtype)
      (a1_regular Q hQ hee hadj) (a1_finrank hrk) (a1_hns Q hminus)
  letI : Field E' := hField
  letI : Finite E' := hFinite
  letI : CharP E' 2 := hCharP
  obtain ⟨e3⟩ := he3
  let Ψ : E →* Matrix.SpecialLinearGroup (Fin 2) E' := e3.toMonoidHom.comp ρd
  have hA : IsElemAbelian p Ψ.range := by
    rw [MonoidHom.range_eq_map]
    exact (a1_isElemAbelian_top hE).map Ψ
  have hcardΨ : Nat.card ↥Ψ.range ≤ p :=
    CFSG.StandardType.TableBExcSmallRest.card_le_of_isElemAbelian_sl2 hp hp2 hA
  have hker : Ψ.ker = (a1_rho Q E hcomm).ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hx
      have hx' : e3 (ρd x) = 1 := by
        change e3 (ρd x) = 1 at hx
        exact hx
      have h1 : ρd x = 1 := e3.injective (by rw [hx', map_one])
      exact congrArg Subtype.val h1
    · intro hx
      have h1 : ρd x = 1 := by
        apply Subtype.ext
        change (a1_rho Q E hcomm) x = 1
        exact hx
      show Ψ x = 1
      rw [MonoidHom.comp_apply, h1, map_one]
  have hcount := Subgroup.card_ker_mul_card_range Ψ
  rw [hker, a1_rho_ker Q E hcomm] at hcount
  have hmap : (K.subgroupOf E).map E.subtype = E ⊓ K := by
    ext x
    constructor
    · intro hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_inf.mpr ⟨y.2, Subgroup.mem_subgroupOf.mp hy⟩
    · intro hx
      obtain ⟨hxE, hxK⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_map.mpr ⟨⟨x, hxE⟩, Subgroup.mem_subgroupOf.mpr hxK, rfl⟩
  have hcardker : Nat.card ↥(K.subgroupOf E) = Nat.card ↥(E ⊓ K) := by
    rw [← hmap, Subgroup.card_map_of_injective (f := E.subtype)
      (fun a b hab => Subtype.ext hab)]
  calc Nat.card ↥E
      = Nat.card ↥(K.subgroupOf E) * Nat.card ↥Ψ.range := hcount.symm
    _ = Nat.card ↥(E ⊓ K) * Nat.card ↥Ψ.range := by rw [hcardker]
    _ ≤ Nat.card ↥(E ⊓ K) * p := Nat.mul_le_mul_left _ hcardΨ
    _ = p * Nat.card ↥(E ⊓ K) := Nat.mul_comm _ _

section A2Helpers

private lemma a2_transpose_mul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (hQ : (polarBilin Q).Nondegenerate) {e : Matrix ι ι F}
    (hadj : formAdj (RingHom.id F) (LinearMap.toMatrix₂' F (polarBilin Q)) e = e) :
    Matrix.transpose e * LinearMap.toMatrix₂' F (polarBilin Q) =
      LinearMap.toMatrix₂' F (polarBilin Q) * e := by
  set G := LinearMap.toMatrix₂' F (polarBilin Q)
  have hG : IsUnit G.det := CFSG.StandardType.TableC.polarGram_isUnit_det Q hQ
  have heid : e.map ⇑(RingHom.id F) = e := by ext i j; rfl
  have h : G * (G⁻¹ * Matrix.transpose e * G) = G * e := by
    have hh := congrArg (fun M => G * M) hadj
    rw [formAdj, heid] at hh
    exact hh
  calc Matrix.transpose e * G
      = (1 : Matrix ι ι F) * (Matrix.transpose e * G) := (Matrix.one_mul _).symm
    _ = (G * G⁻¹) * (Matrix.transpose e * G) := by rw [Matrix.mul_nonsing_inv G hG]
    _ = G * (G⁻¹ * (Matrix.transpose e * G)) := by rw [Matrix.mul_assoc]
    _ = G * (G⁻¹ * Matrix.transpose e * G) := by rw [Matrix.mul_assoc]
    _ = G * e := h

private lemma a2_one_sub_transpose_mul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (hQ : (polarBilin Q).Nondegenerate) {e : Matrix ι ι F}
    (hadj : formAdj (RingHom.id F) (LinearMap.toMatrix₂' F (polarBilin Q)) e = e) :
    Matrix.transpose (1 - e) * LinearMap.toMatrix₂' F (polarBilin Q) =
      LinearMap.toMatrix₂' F (polarBilin Q) * (1 - e) := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, sub_mul, one_mul, mul_sub, mul_one,
    a2_transpose_mul Q hQ hadj]

private lemma a2_preserve {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (hQ : (polarBilin Q).Nondegenerate) {e : Matrix ι ι F}
    (hadj : formAdj (RingHom.id F) (LinearMap.toMatrix₂' F (polarBilin Q)) e = e)
    {u : spinGroup Q} (hu : Spin.spinMatrix Q u ∈ glFixing (1 - e)) :
    ((Spin.spinMatrix Q u : GL ι F) : Matrix ι ι F) * e =
      e * ((Spin.spinMatrix Q u : GL ι F) : Matrix ι ι F) := by
  set G := LinearMap.toMatrix₂' F (polarBilin Q)
  set A := ((Spin.spinMatrix Q u : GL ι F) : Matrix ι ι F)
  have hG : IsUnit G.det := CFSG.StandardType.TableC.polarGram_isUnit_det Q hQ
  have hGt : Matrix.transpose G = G := CFSG.StandardType.TableC.polarGram_transpose Q
  have hfix : A * (1 - e) = 1 - e := hu
  have hiso : Matrix.transpose A * G * A = G :=
    CFSG.StandardType.TableC.spinMatrix_isometry Q u
  have h1eadj : Matrix.transpose (1 - e) * G = G * (1 - e) :=
    a2_one_sub_transpose_mul Q hQ hadj
  have hstep : G * (1 - e) = Matrix.transpose A * G * (1 - e) := by
    calc G * (1 - e) = (Matrix.transpose A * G * A) * (1 - e) := by rw [hiso]
      _ = Matrix.transpose A * G * (A * (1 - e)) := by rw [Matrix.mul_assoc, Matrix.mul_assoc]
      _ = Matrix.transpose A * G * (1 - e) := by rw [hfix]
  have htrans : G * (1 - e) = G * (1 - e) * A := by
    have h := congrArg Matrix.transpose hstep
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at h
    rw [hGt] at h
    rw [← Matrix.mul_assoc] at h
    rw [h1eadj] at h
    exact h
  have h1eA : (1 - e) * A = 1 - e := by
    have h := congrArg (fun M => G⁻¹ * M) htrans
    simp only [← Matrix.mul_assoc] at h
    rw [Matrix.nonsing_inv_mul G hG, Matrix.one_mul] at h
    exact h.symm
  calc A * e = A * (1 - (1 - e)) := by rw [sub_sub_cancel]
    _ = A - A * (1 - e) := by rw [mul_sub, mul_one]
    _ = A - (1 - e) := by rw [hfix]
    _ = (1 - (1 - e)) * A := by rw [sub_mul, one_mul, h1eA]
    _ = e * A := by rw [sub_sub_cancel]

private noncomputable def a2_hcomm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [CharP F 2] (Q : QuadraticForm F (ι → F)) (hQ : (polarBilin Q).Nondegenerate)
    (S : Set (GL ι F)) {e : Matrix ι ι F}
    (hadj : formAdj (RingHom.id F) (LinearMap.toMatrix₂' F (polarBilin Q)) e = e) :
    ∀ x ∈ glBlockCentralizer (Spin.spinMatrix Q) S e,
      ((Spin.spinMatrix Q x : GL ι F) : Matrix ι ι F) * e =
        e * ((Spin.spinMatrix Q x : GL ι F) : Matrix ι ι F) :=
  fun x hx => a2_preserve Q hQ hadj (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp hx)).2

private noncomputable def a2_restrict {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [CharP F 2] (Q : QuadraticForm F (ι → F)) (hQ : (polarBilin Q).Nondegenerate)
    (S : Set (GL ι F)) {e : Matrix ι ι F}
    (hadj : formAdj (RingHom.id F) (LinearMap.toMatrix₂' F (polarBilin Q)) e = e) :
    glBlockCentralizer (Spin.spinMatrix Q) S e →*
      (LinearMap.range (Matrix.mulVecLin e) ≃ₗ[F] LinearMap.range (Matrix.mulVecLin e)) :=
  a1_rho Q (glBlockCentralizer (Spin.spinMatrix Q) S e) (a2_hcomm Q hQ S hadj)

private lemma a2_restrict_mem {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [CharP F 2]
    (Q : QuadraticForm F (ι → F)) (hQ : (polarBilin Q).Nondegenerate)
    (S : Set (GL ι F)) {e : Matrix ι ι F}
    (hadj : formAdj (RingHom.id F) (LinearMap.toMatrix₂' F (polarBilin Q)) e = e)
    (x : glBlockCentralizer (Spin.spinMatrix Q) S e) :
    a2_restrict Q hQ S hadj x ∈ TauCeti.QuadraticMap.orthogonalGroup
      (Q.comp (LinearMap.range (Matrix.mulVecLin e)).subtype) :=
  a1_rho_mem_orthogonalGroup Q _ (a2_hcomm Q hQ S hadj) x

private lemma a2_restrict_apply {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [CharP F 2]
    (Q : QuadraticForm F (ι → F)) (hQ : (polarBilin Q).Nondegenerate)
    (S : Set (GL ι F)) {e : Matrix ι ι F}
    (hadj : formAdj (RingHom.id F) (LinearMap.toMatrix₂' F (polarBilin Q)) e = e)
    (x : glBlockCentralizer (Spin.spinMatrix Q) S e)
    (w : LinearMap.range (Matrix.mulVecLin e)) :
    (((a2_restrict Q hQ S hadj) x) w : (ι → F)) =
      Spin.spinAction Q (x : spinGroup Q) (w : (ι → F)) := rfl

private lemma a2_restrict_injective {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    [CharP F 2] (Q : QuadraticForm F (ι → F)) (hQ : (polarBilin Q).Nondegenerate)
    (S : Set (GL ι F)) {e : Matrix ι ι F}
    (hadj : formAdj (RingHom.id F) (LinearMap.toMatrix₂' F (polarBilin Q)) e = e)
    (hj : Function.Injective (Spin.spinMatrix Q)) :
    Function.Injective (a2_restrict Q hQ S hadj) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hrho : a1_rho Q (glBlockCentralizer (Spin.spinMatrix Q) S e) (a2_hcomm Q hQ S hadj) x = 1 :=
    hx
  have he : ((Spin.spinMatrix Q x : GL ι F) : Matrix ι ι F) * e = e :=
    (a1_rho_eq_one_iff Q _ (a2_hcomm Q hQ S hadj) x).mp hrho
  have h1e : ((Spin.spinMatrix Q x : GL ι F) : Matrix ι ι F) * (1 - e) = 1 - e :=
    (Subgroup.mem_inf.mp (Subgroup.mem_comap.mp x.2)).2
  set A := ((Spin.spinMatrix Q x : GL ι F) : Matrix ι ι F)
  have hA : A = 1 := by
    calc A = A * (e + (1 - e)) := by rw [add_sub_cancel, mul_one]
      _ = A * e + A * (1 - e) := by rw [mul_add]
      _ = e + (1 - e) := by rw [he, h1e]
      _ = 1 := by rw [add_sub_cancel]
  have hGL : Spin.spinMatrix Q x = 1 := Units.ext hA
  refine Subtype.ext (hj ?_)
  rw [hGL, Subgroup.coe_one, map_one]

private lemma a2_toLin_spinMatrix {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (Q : QuadraticForm F (ι → F)) (u : spinGroup Q) :
    Matrix.toLin' ((Spin.spinMatrix Q u : GL ι F) : Matrix ι ι F) =
      (Spin.spinAction Q u : (ι → F) →ₗ[F] (ι → F)) := by
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_apply, Spin.spinMatrix_mulVec]
  rfl

private noncomputable def a2_ext {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {W K : Submodule F (ι → F)} (hc : IsCompl W K) :
    (W ≃ₗ[F] W) →* ((ι → F) ≃ₗ[F] (ι → F)) where
  toFun g := CFSG.RankThree.PartOne.KCOrthogonal.glue hc g 1
  map_one' := CFSG.RankThree.PartOne.KCOrthogonal.glue_one hc
  map_mul' g g' := by
    simpa using (CFSG.RankThree.PartOne.KCOrthogonal.glue_mul hc g g' 1 1)

private lemma a2_ext_apply_w {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {W K : Submodule F (ι → F)} (hc : IsCompl W K) (g : W ≃ₗ[F] W) (w : W) :
    a2_ext hc g (w : ι → F) = (g w : ι → F) := by
  have h := CFSG.RankThree.PartOne.KCOrthogonal.glue_apply hc g 1 w 0
  simpa [a2_ext] using h

private lemma a2_ext_apply_k {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {W K : Submodule F (ι → F)} (hc : IsCompl W K) (g : W ≃ₗ[F] W) (k : K) :
    a2_ext hc g (k : ι → F) = (k : ι → F) := by
  have h := CFSG.RankThree.PartOne.KCOrthogonal.glue_apply hc g 1 0 k
  simpa [a2_ext] using h

private lemma a2_ext_apply_add {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {W K : Submodule F (ι → F)} (hc : IsCompl W K) (g : W ≃ₗ[F] W) (w : W) (k : K) :
    a2_ext hc g ((w : ι → F) + (k : ι → F)) = (g w : ι → F) + (k : ι → F) := by
  have h := CFSG.RankThree.PartOne.KCOrthogonal.glue_apply hc g 1 w k
  simpa [a2_ext] using h

private lemma a2_ext_mem_orthogonalGroup {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {Q : QuadraticForm F (ι → F)} {W K : Submodule F (ι → F)} (hc : IsCompl W K)
    (horth : ∀ u ∈ W, ∀ k ∈ K, polar Q u k = 0) {g : W ≃ₗ[F] W}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype)) :
    a2_ext hc g ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff] at hg ⊢
  intro v
  obtain ⟨w, k, hwk⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.exists_add_of_isCompl hc v
  rw [hwk, a2_ext_apply_add hc g w k]
  have hqu : Q (g w : (ι → F)) = Q (w : (ι → F)) := hg w
  have hpol1 : polar Q (g w : (ι → F)) (k : (ι → F)) = 0 := horth _ (g w).2 _ k.2
  have hpol2 : polar Q (w : (ι → F)) (k : (ι → F)) = 0 := horth _ w.2 _ k.2
  calc Q ((g w : (ι → F)) + (k : (ι → F)))
      = Q (g w : (ι → F)) + Q (k : (ι → F)) + polar Q (g w) (k : (ι → F)) :=
        QuadraticMap.map_add Q _ _
    _ = Q (w : (ι → F)) + Q (k : (ι → F)) + 0 := by rw [hqu, hpol1]
    _ = Q ((w : (ι → F)) + (k : (ι → F))) := by
        rw [QuadraticMap.map_add Q, hpol2, add_zero]

private lemma a2_ext_mem_orthDerived {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {Q : QuadraticForm F (ι → F)} {W K : Submodule F (ι → F)} (hc : IsCompl W K)
    (horth : ∀ u ∈ W, ∀ k ∈ K, polar Q u k = 0) {g : W ≃ₗ[F] W}
    (hg : g ∈ orthDerived (Q.comp W.subtype)) :
    a2_ext hc g ∈ orthDerived Q := by
  have hle : (TauCeti.QuadraticMap.orthogonalGroup (Q.comp W.subtype)).map (a2_ext hc) ≤
      TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨g', hg', rfl⟩
    exact a2_ext_mem_orthogonalGroup hc horth hg'
  have hmap : (orthDerived (Q.comp W.subtype)).map (a2_ext hc) ≤ orthDerived Q := by
    rw [orthDerived, Subgroup.map_commutator, orthDerived]
    exact Subgroup.commutator_mono hle hle
  exact hmap ⟨g, hg, rfl⟩

private lemma a2_mat_fix_W {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {e : Matrix ι ι F} {s : GL ι F} (hse : (s : Matrix ι ι F) * e = e) :
    ∀ w ∈ LinearMap.range (Matrix.mulVecLin e),
      Matrix.toLin' (s : Matrix ι ι F) w = w := by
  rintro w ⟨x, rfl⟩
  rw [Matrix.mulVecLin_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hse]

private lemma a2_mat_stab_K {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {e : Matrix ι ι F} {s : GL ι F} (hes : e * (s : Matrix ι ι F) = e) :
    ∀ k ∈ LinearMap.ker (Matrix.mulVecLin e),
      Matrix.toLin' (s : Matrix ι ι F) k ∈ LinearMap.ker (Matrix.mulVecLin e) := by
  intro k hk
  rw [LinearMap.mem_ker] at hk ⊢
  rw [Matrix.mulVecLin_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hes]
  simpa [Matrix.mulVecLin_apply] using hk

private lemma a2_one_sub_mem_K {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {e : Matrix ι ι F} (hee : IsIdempotentElem e) (v : ι → F) :
    (1 - e).mulVec v ∈ LinearMap.ker (Matrix.mulVecLin e) := by
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
  have h : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hee.eq, sub_self]
  rw [h, Matrix.zero_mulVec]

private lemma a2_ext_commute {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {e : Matrix ι ι F} {s : GL ι F}
    (hc : IsCompl (LinearMap.range (Matrix.mulVecLin e))
      (LinearMap.ker (Matrix.mulVecLin e)))
    (hse : (s : Matrix ι ι F) * e = e) (hes : e * (s : Matrix ι ι F) = e)
    (g : LinearMap.range (Matrix.mulVecLin e) ≃ₗ[F] LinearMap.range (Matrix.mulVecLin e)) :
    (Matrix.toLin' (s : Matrix ι ι F)) *
        (a2_ext hc g : (ι → F) →ₗ[F] (ι → F)) =
      (a2_ext hc g : (ι → F) →ₗ[F] (ι → F)) * Matrix.toLin' (s : Matrix ι ι F) := by
  apply LinearMap.ext
  intro v
  obtain ⟨w, k, hwk⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.exists_add_of_isCompl hc v
  rw [hwk]
  have hfixw : Matrix.toLin' (s : Matrix ι ι F) (w : ι → F) = (w : ι → F) :=
    a2_mat_fix_W hse w w.2
  have hfixgw : Matrix.toLin' (s : Matrix ι ι F) (g w : ι → F) = (g w : ι → F) :=
    a2_mat_fix_W hse (g w) (g w).2
  have hstabk : Matrix.toLin' (s : Matrix ι ι F) (k : ι → F) ∈
      LinearMap.ker (Matrix.mulVecLin e) := a2_mat_stab_K hes k k.2
  have hL : (Matrix.toLin' (s : Matrix ι ι F))
        ((a2_ext hc g) ((w : ι → F) + (k : ι → F))) =
      (g w : ι → F) + Matrix.toLin' (s : Matrix ι ι F) (k : ι → F) := by
    rw [a2_ext_apply_add hc g w k, map_add, hfixgw]
  have hR : (a2_ext hc g)
        ((Matrix.toLin' (s : Matrix ι ι F)) ((w : ι → F) + (k : ι → F))) =
      (g w : ι → F) + Matrix.toLin' (s : Matrix ι ι F) (k : ι → F) := by
    rw [map_add, hfixw]
    rw [show Matrix.toLin' (s : Matrix ι ι F) (k : ι → F) =
        ((⟨Matrix.toLin' (s : Matrix ι ι F) (k : ι → F), hstabk⟩ :
          LinearMap.ker (Matrix.mulVecLin e)) : (ι → F)) from rfl]
    rw [a2_ext_apply_add hc g w ⟨Matrix.toLin' (s : Matrix ι ι F) (k : ι → F), hstabk⟩]
  rw [Module.End.mul_apply, Module.End.mul_apply]
  exact hL.trans hR.symm

private lemma a2_ext_mem {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    [CharP F 2] (Q : QuadraticForm F (ι → F)) (hQ : (polarBilin Q).Nondegenerate)
    (hrange : (Spin.spinAction Q).range = orthDerived Q)
    (S : Set (GL ι F)) {e : Matrix ι ι F} (hee : IsIdempotentElem e)
    (hadj : formAdj (RingHom.id F) (LinearMap.toMatrix₂' F (polarBilin Q)) e = e)
    (hse : ∀ s ∈ S, (s : Matrix ι ι F) * e = e)
    (hcomm : ∀ s ∈ S, (s : Matrix ι ι F) * e = e * (s : Matrix ι ι F)) :
    orthDerived (Q.comp (LinearMap.range (Matrix.mulVecLin e)).subtype) ≤
      (a2_restrict Q hQ S hadj).range := by
  intro g hg
  let W := LinearMap.range (Matrix.mulVecLin e)
  let K := LinearMap.ker (Matrix.mulVecLin e)
  have hc : IsCompl W K := LinearMap.IsIdempotentElem.isCompl (a1_idem hee)
  have horth : ∀ u ∈ W, ∀ k ∈ K, polar Q u k = 0 := a1_orth Q hQ hadj
  have hg' : a2_ext hc g ∈ orthDerived Q := a2_ext_mem_orthDerived hc horth hg
  rw [← hrange] at hg'
  obtain ⟨u, hu⟩ := MonoidHom.mem_range.mp hg'
  refine ⟨⟨u, ?_⟩, ?_⟩
  · refine Subgroup.mem_comap.mpr (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
    · rw [Subgroup.mem_centralizer_iff]
      intro s hs
      apply Units.ext
      apply (LinearEquiv.injective Matrix.toLin')
      rw [Units.val_mul, Units.val_mul, Matrix.toLin'_mul, Matrix.toLin'_mul,
        a2_toLin_spinMatrix, hu]
      exact a2_ext_commute hc (hse s hs) (by rw [← hcomm s hs, hse s hs]) g
    · show ((Spin.spinMatrix Q u : GL ι F) : Matrix ι ι F) * (1 - e) = 1 - e
      apply (LinearEquiv.injective Matrix.toLin')
      rw [Matrix.toLin'_mul, a2_toLin_spinMatrix, hu]
      apply LinearMap.ext
      intro v
      change (a2_ext hc g) (Matrix.toLin' (1 - e) v) = Matrix.toLin' (1 - e) v
      rw [Matrix.toLin'_apply]
      exact a2_ext_apply_k hc g ⟨(1 - e).mulVec v, a2_one_sub_mem_K hee v⟩
  · apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    rw [a2_restrict_apply, hu, a2_ext_apply_w hc g w]

end A2Helpers

theorem minus_of_fieldExt_four
    {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    [CharP F 2] {f : ℕ} (hF : Nat.card F = 2 ^ f) (Q : QuadraticForm F (ι → F))
    (hQ : (polarBilin Q).Nondegenerate) (hj : Function.Injective (Spin.spinMatrix Q))
    (hrange : (Spin.spinAction Q).range = orthDerived Q)
    {X : Type} [Group X] (ψ : spinGroup Q →* X) (hψ : Function.Injective ψ)
    (S : Set (GL ι F)) {e : Matrix ι ι F} (hee : IsIdempotentElem e)
    (hadj : formAdj (RingHom.id F) (LinearMap.toMatrix₂' F (polarBilin Q)) e = e)
    (hcomm : ∀ s ∈ S, (s : Matrix ι ι F) * e = e * (s : Matrix ι ι F))
    (hse : ∀ s ∈ S, (s : Matrix ι ι F) * e = e)
    (hrk : Matrix.rank e = 4) {J' : Subgroup (spinGroup Q)}
    (hJ' : IsComponentOf J' ⁅glBlockCentralizer (Spin.spinMatrix Q) S e,
      glBlockCentralizer (Spin.spinMatrix Q) S e⁆)
    {t : StatedLieTag} (hFE : GGSixLSevenFieldExtCase (J'.map ψ) t f) :
    ∀ U : Submodule F (ι → F), U ≤ LinearMap.range (Matrix.mulVecLin e) →
      finrank F U = 2 → ∃ u ∈ U, Q u ≠ 0 := by
  classical
  intro U hUW hUdim
  by_contra hcon
  have hcon' : ∀ u ∈ U, Q u = 0 := by
    intro u hu
    by_contra hq
    exact hcon ⟨u, hu, hq⟩
  let W := LinearMap.range (Matrix.mulVecLin e)
  let K := LinearMap.ker (Matrix.mulVecLin e)
  let R := Q.comp W.subtype
  have hc : IsCompl W K := LinearMap.IsIdempotentElem.isCompl (a1_idem hee)
  have hR : (polarBilin R).Nondegenerate := a1_regular Q hQ hee hadj
  have hRdim : finrank F W = 4 := a1_finrank hrk
  let U' : Submodule F W := U.comap W.subtype
  have hU'map : U'.map W.subtype = U := by
    refine Submodule.map_comap_eq_of_le ?_
    rintro x hx
    exact ⟨⟨x, hUW hx⟩, rfl⟩
  have hU'dim : finrank F U' = 2 := by
    rw [← Submodule.finrank_map_subtype_eq, hU'map, hUdim]
  have hU'q : ∀ x ∈ U', R x = 0 := fun x hx => hcon' (x : ι → F) hx
  have hsplit : CFSG.StandardType.OmNonsplit.SplitFour R :=
    ⟨hRdim, ⟨U', hU'dim, hU'q⟩⟩
  let G_e := glBlockCentralizer (Spin.spinMatrix Q) S e
  let r := a2_restrict Q hQ S hadj
  have hr_inj : Function.Injective r := a2_restrict_injective Q hQ S hadj hj
  have hJ'le : J' ≤ G_e := hJ'.1.trans (Subgroup.commutator_le_self G_e)
  have hcomp : CFSG.Assembly.IsComponentOf (J'.subgroupOf G_e)
      ((⁅G_e, G_e⁆).subgroupOf G_e) :=
    CFSG.StandardType.ggIsComponentOf_subgroupOf hJ' (Subgroup.commutator_le_self G_e)
  let T := (J'.subgroupOf G_e).map r
  have hcompmap : CFSG.Assembly.IsComponentOf T (((⁅G_e, G_e⁆).subgroupOf G_e).map r) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_of_injective hcomp r hr_inj
  have hTq0 : CFSG.Assembly.IsQuasisimple T := hcompmap.2.2
  have hTq : CFSG.IsQuasisimple T :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native T).mp hTq0
  have hTle : T ≤ TauCeti.QuadraticMap.orthogonalGroup R := by
    rintro _ ⟨x, -, rfl⟩
    exact a2_restrict_mem Q hQ S hadj x
  by_cases hK2 : Nat.card F = 2
  · have hplus : CFSG.GroupTheory.WeirSylow.IsPlusType R :=
      ⟨U', by rw [hU'dim, hRdim], hU'q⟩
    have hsolv : Group.IsSolvable ↥(TauCeti.QuadraticMap.orthogonalGroup R) :=
      CFSG.LocalAnalysis.GLTheoremA.T123CB.isSolvable_orthogonalGroup_of_card_two_of_plus
        R hR hK2 hRdim hplus
    exact CFSG.StandardType.OmNonsplit.not_le_of_isSolvable hTq hsolv hTle
  · have h2f3 : (2 : ℕ) ^ f ≠ 3 := by
      intro h3
      have h2dvd : 2 ∣ 3 := by
        rcases Nat.eq_zero_or_pos f with hf | hf
        · rw [hf] at h3
          norm_num at h3
        · rw [← h3]
          exact dvd_pow_self 2 (by omega : f ≠ 0)
      norm_num at h2dvd
    have hK3 : Nat.card F ≠ 3 := by rw [hF]; exact h2f3
    obtain ⟨ψ0, e0, -, -, -, -, -, -, -, -, hperf0, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.orthogonal_split_four_derived
        hK2 hK3 R hR hRdim ⟨U', hU'dim, hU'q⟩
    have hperf : Group.IsPerfect ↥(orthDerived R) := by
      haveI : Group.IsPerfect ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup R)) :=
        hperf0
      rw [orthDerived,
        ← Subgroup.map_subtype_commutator (TauCeti.QuadraticMap.orthogonalGroup R)]
      exact Group.IsPerfect.map (TauCeti.QuadraticMap.orthogonalGroup R).subtype
    have hupper : ((⁅G_e, G_e⁆).subgroupOf G_e).map r = orthDerived R := by
      rw [CFSG.StandardType.ggCommutator_subgroupOf, commutator_def, Subgroup.map_commutator,
        (MonoidHom.range_eq_map r).symm]
      apply le_antisymm
      · rw [orthDerived]
        apply Subgroup.commutator_mono
        · rintro _ ⟨x, -, rfl⟩
          exact a2_restrict_mem Q hQ S hadj x
        · rintro _ ⟨x, -, rfl⟩
          exact a2_restrict_mem Q hQ S hadj x
      · have hle : orthDerived R ≤ r.range := a2_ext_mem Q hQ hrange S hee hadj hse hcomm
        haveI : Group.IsPerfect ↥(orthDerived R) := hperf
        calc orthDerived R = ⁅orthDerived R, orthDerived R⁆ :=
              (Subgroup.commutator_eq_self (H := orthDerived R)).symm
          _ ≤ ⁅r.range, r.range⁆ := Subgroup.commutator_mono hle hle
    have hTs : CFSG.Assembly.IsSubnormal T
        (TauCeti.QuadraticMap.orthogonalGroup R) := by
      have hsub : CFSG.Assembly.IsSubnormal T (orthDerived R) := by
        rw [← hupper]
        exact hcompmap.2.1
      have hnormal : ((orthDerived R).subgroupOf
          (TauCeti.QuadraticMap.orthogonalGroup R)).Normal := by
        rw [orthDerived]
        have h := Subgroup.normal_subgroupOf_commutator_sup
          (H₁ := TauCeti.QuadraticMap.orthogonalGroup R)
          (H₂ := TauCeti.QuadraticMap.orthogonalGroup R)
        rwa [sup_idem] at h
      exact hsub.trans (CFSG.Assembly.IsSubnormal.step
        (by rw [orthDerived]; exact Subgroup.commutator_le_self _) hnormal
        (CFSG.Assembly.IsSubnormal.refl _))
    obtain ⟨-, hdisj⟩ := CFSG.StandardType.OmNonsplit.structure_of_isSubnormal hR hTq hTs
    rcases hdisj with ⟨hnsplit, -⟩ | ⟨-, h4F, ψ', hψ'inj, hψ'range⟩
    · exact hnsplit hsplit
    · have hq : 4 ≤ 2 ^ f := by rw [← hF]; exact h4F
      have eT0 : ↥(ψ'.range) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
        (MulEquiv.ofBijective ψ'.rangeRestrict
          ⟨fun a b hab => hψ'inj (Subtype.ext_iff.mp hab),
            ψ'.rangeRestrict_surjective⟩).symm
      have eT : ↥T ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
        (MulEquiv.subgroupCongr hψ'range).symm.trans eT0
      have eTsub : ↥T ≃* ↥(J'.subgroupOf G_e) :=
        (Subgroup.equivMapOfInjective (J'.subgroupOf G_e) r hr_inj).symm
      have e_sub : ↥(J'.subgroupOf G_e) ≃* ↥J' := by
        have h := Subgroup.equivMapOfInjective (J'.subgroupOf G_e) (G_e).subtype
          (G_e).subtype_injective
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hJ'le] at h
        exact h
      have eJ : ↥(J'.map ψ) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
        (Subgroup.equivMapOfInjective J' ψ hψ).symm.trans
          (e_sub.symm.trans (eTsub.symm.trans eT))
      have hLM : CFSG.Blueprint.LieModel
          (↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) .PSL 2 2 f :=
        CFSG.RankThree.PartOne.TCP.lieModel_of_equiv_SL2 hq hF eJ
      unfold CFSG.StandardType.GGSixLSevenFieldExtCase at hFE
      obtain ⟨t', m', f', hff, hL', -⟩ := hFE
      have hf'eq : f' = f :=
        CFSG.ComponentClassification.CatLeafProof.fieldExponent_eq_of_isChar2LieShape
          (X := ↥(J'.map ψ) ⧸ Subgroup.center ↥(J'.map ψ)) hLM (Or.inl ⟨rfl, rfl⟩) hL'
      omega

private lemma a3_commute {ι F : Type} [Fintype ι] [DecidableEq ι] [Ring F]
    {S Y e : Matrix ι ι F} (hee : e * e = e)
    (hSe : S * e = e) (heS : e * S = e)
    (hYe : Y * e = e * Y) (hY1e : Y * (1 - e) = 1 - e) :
    S * Y = Y * S := by
  have hsum : e + (1 - e) = (1 : Matrix ι ι F) := by
    rw [add_comm, sub_add_cancel]
  have hYdecomp : Y = e * Y + (1 - e) := by
    calc Y = Y * 1 := (mul_one Y).symm
      _ = Y * (e + (1 - e)) := by rw [hsum]
      _ = Y * e + Y * (1 - e) := by rw [mul_add]
      _ = e * Y + (1 - e) := by rw [hYe, hY1e]
  have hSdecomp : S = e + S * (1 - e) := by
    calc S = S * 1 := (mul_one S).symm
      _ = S * (e + (1 - e)) := by rw [hsum]
      _ = S * e + S * (1 - e) := by rw [mul_add]
      _ = e + S * (1 - e) := by rw [hSe]
  have h1eS : (1 - e) * S = S - e := by rw [sub_mul, one_mul, heS]
  have he1e : e * (1 - e) = 0 := by rw [mul_sub, mul_one, hee, sub_self]
  have hZ : (1 - e) * S * (1 - e) = S * (1 - e) := by
    rw [h1eS, sub_mul, he1e, sub_zero]
  have hSY : S * Y = e * Y + S * (1 - e) := by
    calc S * Y = S * (e * Y + (1 - e)) := by
          conv_lhs => rw [hYdecomp]
      _ = S * (e * Y) + S * (1 - e) := by rw [mul_add]
      _ = (S * e) * Y + S * (1 - e) := by rw [← mul_assoc]
      _ = e * Y + S * (1 - e) := by rw [hSe]
  have hYS : Y * S = e * Y + S * (1 - e) := by
    calc Y * S = Y * (e + S * (1 - e)) := by
          conv_lhs => rw [hSdecomp]
      _ = Y * e + Y * (S * (1 - e)) := by rw [mul_add]
      _ = e * Y + Y * (S * (1 - e)) := by rw [hYe]
      _ = e * Y + S * (1 - e) := by
            congr 1
            rw [← hZ, ← mul_assoc, ← mul_assoc, hY1e]
  rw [hSY, hYS]

theorem mem_of_lift_trivial_on_block {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {U X : Type} [Group U] [Group X] (j : U →* GL ι F) (hj : Function.Injective j) (ψ : U →* X)
    {B₁ D J : Subgroup X} {J' : Subgroup U} (ℓB : ↥B₁ →* U)
    (hlift : ∀ b : ↥B₁, IsGLLift j ψ (j (ℓB b)) (b : X))
    (hBJ : B₁ ⊓ Subgroup.centralizer (J : Set X) = D) (hJ' : J'.map ψ = J)
    {e : Matrix ι ι F} (hee : IsIdempotentElem e)
    (hJ'fix : ∀ u ∈ J', ((j u : GL ι F) : Matrix ι ι F) * (1 - e) = 1 - e)
    (hJ'comm : ∀ u ∈ J', ((j u : GL ι F) : Matrix ι ι F) * e = e * ((j u : GL ι F) : Matrix ι ι F))
    {b : ↥B₁} (hb : ((j (ℓB b) : GL ι F) : Matrix ι ι F) * e = e)
    (hbcomm : ((j (ℓB b) : GL ι F) : Matrix ι ι F) * e =
      e * ((j (ℓB b) : GL ι F) : Matrix ι ι F)) :
    (b : X) ∈ D := by
  have hcomm : ∀ u ∈ J', ψ u * (b : X) = (b : X) * ψ u := by
    intro u hu
    obtain ⟨u', hu'j, hu'ψ⟩ := hlift b u
    have hs_comm : j (ℓB b) * j u = j u * j (ℓB b) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      exact a3_commute hee hb (by rw [← hbcomm, hb]) (hJ'comm u hu) (hJ'fix u hu)
    have hju' : j u' = j u := by
      rw [hu'j, hs_comm, mul_assoc, mul_inv_cancel, mul_one]
    have huu' : u' = u := hj hju'
    have hconj : (b : X)⁻¹ * ψ u * (b : X) = ψ u := by rw [hu'ψ, huu']
    calc ψ u * (b : X) = (b : X) * ((b : X)⁻¹ * ψ u * (b : X)) := by
          rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul]
      _ = (b : X) * ψ u := by rw [hconj]
  have hmemC : (b : X) ∈ Subgroup.centralizer (J : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [← hJ'] at hy
    obtain ⟨u, hu, rfl⟩ := (Subgroup.mem_map.mp hy)
    exact hcomm u hu
  rw [← hBJ]
  exact ⟨b.2, hmemC⟩

private lemma a4_comm_of_mem_adjoin {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {S : Set (GL ι F)} {a : Matrix ι ι F}
    (ha : ∀ s ∈ S, Commute a (s : Matrix ι ι F))
    {b : Matrix ι ι F} (hb : b ∈ Algebra.adjoin F (Units.val '' S)) :
    a * b = b * a := by
  have hgen : (Units.val '' S : Set (Matrix ι ι F)) ⊆
      (Subalgebra.centralizer F ({a} : Set (Matrix ι ι F)) : Set (Matrix ι ι F)) := by
    rintro x ⟨s, hs, rfl⟩
    refine (Subalgebra.mem_centralizer_iff F).mpr ?_
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ha s hs
  have hA : Algebra.adjoin F (Units.val '' S) ≤
      Subalgebra.centralizer F ({a} : Set (Matrix ι ι F)) := Algebra.adjoin_le hgen
  exact (Subalgebra.mem_centralizer_iff F).mp (hA hb) a (Set.mem_singleton a)

private lemma a4_ker_trivial {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {U X : Type} [Group U] [Group X] (j : U →* GL ι F) (hj : Function.Injective j)
    (ψ : U →* X) {B₁ : Subgroup X}
    (hBG : B₁ ⊓ Subgroup.centralizer (ψ.range : Set X) = ⊥)
    (ℓB : ↥B₁ →* U)
    (hlift : ∀ b : ↥B₁, IsGLLift j ψ (j (ℓB b)) (b : X)) :
    Function.Injective ℓB := by
  have hker : ∀ c : ↥B₁, ℓB c = 1 → c = 1 := by
    intro c hc
    have hjc : j (ℓB c) = 1 := by rw [hc, map_one]
    have hlift1 : IsGLLift j ψ 1 (c : X) := by
      have h := hlift c
      rw [hjc] at h
      exact h
    apply Subtype.ext
    have hmem : (c : X) ∈ B₁ ⊓ Subgroup.centralizer (ψ.range : Set X) := by
      refine Subgroup.mem_inf.mpr ⟨c.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hy
      obtain ⟨u', hu'j, hu'psi⟩ := hlift1 u
      have hu' : u' = u := hj (by simpa using hu'j)
      rw [hu'] at hu'psi
      calc ψ u * (c : X) = (c : X) * ((c : X)⁻¹ * ψ u * (c : X)) := by group
        _ = (c : X) * ψ u := by rw [hu'psi]
    rw [hBG] at hmem
    simpa using Subgroup.mem_bot.mp hmem
  intro b b' hbb'
  have h1 : ℓB (b * b'⁻¹) = 1 := by
    rw [map_mul, map_inv, hbb', mul_inv_cancel]
  have h2 := hker (b * b'⁻¹) h1
  rw [mul_inv_eq_one] at h2
  exact h2

private lemma a4_card_E {U X : Type} [Group U] [Group X] {B₁ : Subgroup X}
    (ℓB : ↥B₁ →* U) (hinj : Function.Injective ℓB) :
    Nat.card ↥(ℓB.range) = Nat.card ↥B₁ := by
  refine (Nat.card_congr ?_).symm
  refine Equiv.ofBijective
    (fun b : ↥B₁ => (⟨ℓB b, ⟨b, rfl⟩⟩ : ↥(ℓB.range))) ?_
  constructor
  · intro b b' h
    exact hinj (Subtype.ext_iff.mp h)
  · rintro ⟨x, hx⟩
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hx
    exact ⟨b, Subtype.ext rfl⟩

private lemma a4_elemAbelian {U X : Type} [Group U] [Group X] {p : ℕ} {B₁ : Subgroup X}
    (ℓB : ↥B₁ →* U) (hBab : IsElemAbelian p B₁)
    (hpow : ∀ b : ↥B₁, ℓB b ^ p = 1) :
    IsElemAbelian p (ℓB.range) := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp a.2
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul,
      hBab.1.is_comm.comm x y]
  · intro x hx
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hx
    exact hpow b

private lemma a4_adj {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F] [CharP F 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (G : Matrix ι ι F)
    (hGt : Matrix.transpose G = G) (hGu : IsUnit G.det) {S : Set (GL ι F)}
    (hSiso : ∀ s ∈ S, Matrix.transpose (s : Matrix ι ι F) * G * (s : Matrix ι ι F) = G)
    (hScomm : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hSp : ∀ s ∈ S, s ^ p = 1)
    {e : Matrix ι ι F} (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hse : ∀ s ∈ S, (s : Matrix ι ι F) * e = e) :
    formAdj (RingHom.id F) G e = e := by
  rcases CFSG.StandardType.TableC.blockDegree_trivial_or_eq_orderOf_gram F hp hp2 G hGt hGu
    hSiso hScomm hSp he with ⟨-, -, hadj⟩ | ⟨⟨s, hs, hne⟩, -, -⟩
  · exact hadj
  · exact absurd (hse s hs) hne

private lemma a4_card_kernel_le {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {U X : Type} [Group U] [Group X] [Finite X] (j : U →* GL ι F) (hj : Function.Injective j)
    (ψ : U →* X) {B₁ D J : Subgroup X} (hDB : D ≤ B₁)
    {p : ℕ} (hBab : IsElemAbelian p B₁)
    (hBJ : B₁ ⊓ Subgroup.centralizer (J : Set X) = D)
    (ℓB : ↥B₁ →* U)
    (hlift : ∀ b : ↥B₁, IsGLLift j ψ (j (ℓB b)) (b : X))
    (S : Set (GL ι F)) (hS : S = Set.range fun d : ↥D => j (ℓB ⟨(d : X), hDB d.2⟩))
    {J' : Subgroup U} {e : Matrix ι ι F}
    (hJ'e : IsComponentOf J' ⁅glBlockCentralizer j S e, glBlockCentralizer j S e⁆)
    (hJmap : J'.map ψ = J)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) :
    Nat.card ↥(ℓB.range ⊓ (glFixing e).comap j) ≤ Nat.card ↥D := by
  classical
  have hJ'le : J' ≤ glBlockCentralizer j S e :=
    hJ'e.1.trans (Subgroup.commutator_le_self (glBlockCentralizer j S e))
  have hJ'fix : ∀ u ∈ J', ((j u : GL ι F) : Matrix ι ι F) * (1 - e) = 1 - e := by
    intro u hu
    have hu' := hJ'le hu
    rw [glBlockCentralizer, Subgroup.mem_comap] at hu'
    exact (Subgroup.mem_inf.mp hu').2
  have hJ'comm : ∀ u ∈ J', ((j u : GL ι F) : Matrix ι ι F) * e =
      e * ((j u : GL ι F) : Matrix ι ι F) := by
    intro u hu
    have hu' := hJ'le hu
    rw [glBlockCentralizer, Subgroup.mem_comap] at hu'
    have hgc := (Subgroup.mem_inf.mp hu').1
    exact a4_comm_of_mem_adjoin (fun s hs =>
      congrArg (fun w : GL ι F => (w : Matrix ι ι F))
        (Subgroup.mem_centralizer_iff.mp hgc s hs).symm) he.1
  have hee : IsIdempotentElem e := he.2.1
  let φ : ↥(ℓB.range ⊓ (glFixing e).comap j) → ↥D := fun x =>
    let b : ↥B₁ := Classical.choose (MonoidHom.mem_range.mp (Subgroup.mem_inf.mp x.2).1)
    ⟨(b : X), by
      have hspec : ℓB b = x.1 :=
        Classical.choose_spec (MonoidHom.mem_range.mp (Subgroup.mem_inf.mp x.2).1)
      have hb : ((j (ℓB b) : GL ι F) : Matrix ι ι F) * e = e := by
        have hxK : j x.1 ∈ glFixing e :=
          Subgroup.mem_comap.mp (Subgroup.mem_inf.mp x.2).2
        rw [hspec]
        exact hxK
      have hbcomm : ((j (ℓB b) : GL ι F) : Matrix ι ι F) * e =
          e * ((j (ℓB b) : GL ι F) : Matrix ι ι F) := by
        have ha : ∀ s ∈ S, Commute ((j (ℓB b) : GL ι F) : Matrix ι ι F)
            (s : Matrix ι ι F) := by
          intro s hs
          rw [hS] at hs
          obtain ⟨d, rfl⟩ := hs
          exact congrArg (fun w : GL ι F => (w : Matrix ι ι F))
            ((Commute.map (hBab.1.is_comm.comm b ⟨(d : X), hDB d.2⟩) ℓB).map j).eq
        exact a4_comm_of_mem_adjoin ha he.1
      exact mem_of_lift_trivial_on_block j hj ψ ℓB hlift hBJ hJmap hee hJ'fix hJ'comm hb hbcomm⟩
  have hinj : Function.Injective φ := by
    intro x x' h
    have hb : Classical.choose (MonoidHom.mem_range.mp (Subgroup.mem_inf.mp x.2).1) =
        Classical.choose (MonoidHom.mem_range.mp (Subgroup.mem_inf.mp x'.2).1) := by
      apply Subtype.ext
      exact congrArg (fun d : ↥D => (d : X)) h
    have hx : x.1 = x'.1 := by
      calc x.1 = ℓB (Classical.choose (MonoidHom.mem_range.mp (Subgroup.mem_inf.mp x.2).1)) :=
            (Classical.choose_spec (MonoidHom.mem_range.mp (Subgroup.mem_inf.mp x.2).1)).symm
        _ = ℓB (Classical.choose (MonoidHom.mem_range.mp (Subgroup.mem_inf.mp x'.2).1)) := by
              rw [hb]
        _ = x'.1 := Classical.choose_spec (MonoidHom.mem_range.mp (Subgroup.mem_inf.mp x'.2).1)
    exact Subtype.ext hx
  haveI : Finite ↥D := Finite.of_injective (fun d : ↥D => (d : X)) Subtype.val_injective
  exact Nat.card_le_card_of_injective φ hinj

theorem ggSixTCCaseAPOmega_false
    {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F] [CharP F 2]
    {f : ℕ} (hF : Nat.card F = 2 ^ f) (Q : QuadraticForm F (ι → F))
    (hQ : (polarBilin Q).Nondegenerate) (hj : Function.Injective (Spin.spinMatrix Q))
    (hrange : (Spin.spinAction Q).range = orthDerived Q)
    {X : Type} [Group X] [Finite X] (ψ : spinGroup Q →* X) (hψ : Function.Injective ψ)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {B₁ D J : Subgroup X} (hDB : D ≤ B₁)
    (hBab : IsElemAbelian p B₁) (hDcard : Nat.card D = p ^ 2) (hB4 : p ^ 4 ≤ Nat.card B₁)
    (hBG : B₁ ⊓ Subgroup.centralizer (ψ.range : Set X) = ⊥)
    (hBJ : B₁ ⊓ Subgroup.centralizer (J : Set X) = D)
    (ℓB : ↥B₁ →* spinGroup Q)
    (hlift : ∀ b : ↥B₁, IsGLLift (Spin.spinMatrix Q) ψ (Spin.spinMatrix Q (ℓB b)) (b : X))
    (hpow : ∀ b : ↥B₁, ℓB b ^ p = 1)
    (S : Set (GL ι F)) (hS : S = Set.range fun d : ↥D => Spin.spinMatrix Q (ℓB ⟨(d : X), hDB d.2⟩))
    {J' : Subgroup (spinGroup Q)} {e : Matrix ι ι F}
    (hJ'e : IsComponentOf J' ⁅glBlockCentralizer (Spin.spinMatrix Q) S e,
      glBlockCentralizer (Spin.spinMatrix Q) S e⁆)
    (hJmap : J'.map ψ = J) {t : StatedLieTag} (hFE : GGSixLSevenFieldExtCase J t f)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hse : ∀ s ∈ S, (s : Matrix ι ι F) * e = e)
    (hrk : Matrix.rank e = 4) : False := by
  classical
  let G := LinearMap.toMatrix₂' F (polarBilin Q)
  have hGt : Matrix.transpose G = G := CFSG.StandardType.TableC.polarGram_transpose Q
  have hGu : IsUnit G.det := CFSG.StandardType.TableC.polarGram_isUnit_det Q hQ
  have hinj : Function.Injective ℓB := a4_ker_trivial (Spin.spinMatrix Q) hj ψ hBG ℓB hlift
  have hcardE : Nat.card ↥(ℓB.range) = Nat.card ↥B₁ := a4_card_E ℓB hinj
  have hEelem : IsElemAbelian p (ℓB.range) := a4_elemAbelian ℓB hBab hpow
  have hee : IsIdempotentElem e := he.2.1
  have hSiso : ∀ s ∈ S, Matrix.transpose (s : Matrix ι ι F) * G * (s : Matrix ι ι F) = G := by
    intro s hs
    rw [hS] at hs
    obtain ⟨d, rfl⟩ := hs
    exact CFSG.StandardType.TableC.spinMatrix_isometry Q (ℓB ⟨(d : X), hDB d.2⟩)
  have hScomm : ∀ s ∈ S, ∀ s' ∈ S, Commute s s' := by
    intro s hs s' hs'
    rw [hS] at hs hs'
    obtain ⟨d, rfl⟩ := hs
    obtain ⟨d', rfl⟩ := hs'
    exact ((Commute.map (hBab.1.is_comm.comm ⟨(d : X), hDB d.2⟩ ⟨(d' : X), hDB d'.2⟩) ℓB).map
      (Spin.spinMatrix Q))
  have hSp : ∀ s ∈ S, s ^ p = 1 := by
    intro s hs
    rw [hS] at hs
    obtain ⟨d, rfl⟩ := hs
    rw [← map_pow, hpow ⟨(d : X), hDB d.2⟩, map_one]
  have hadj : formAdj (RingHom.id F) G e = e :=
    a4_adj hp hp2 G hGt hGu hSiso hScomm hSp he hse
  have hcommE : ∀ x ∈ ℓB.range, ((Spin.spinMatrix Q x : GL ι F) : Matrix ι ι F) * e =
      e * ((Spin.spinMatrix Q x : GL ι F) : Matrix ι ι F) := by
    intro x hx
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hx
    have ha : ∀ s ∈ S, Commute ((Spin.spinMatrix Q (ℓB b) : GL ι F) : Matrix ι ι F)
        (s : Matrix ι ι F) := by
      intro s hs
      rw [hS] at hs
      obtain ⟨d, rfl⟩ := hs
      exact congrArg (fun w : GL ι F => (w : Matrix ι ι F))
        ((Commute.map (hBab.1.is_comm.comm b ⟨(d : X), hDB d.2⟩) ℓB).map
          (Spin.spinMatrix Q)).eq
    exact a4_comm_of_mem_adjoin ha he.1
  have hcommS : ∀ s ∈ S, (s : Matrix ι ι F) * e = e * (s : Matrix ι ι F) := by
    intro s hs
    rw [hS] at hs
    obtain ⟨d, rfl⟩ := hs
    exact hcommE (ℓB ⟨(d : X), hDB d.2⟩) ⟨⟨(d : X), hDB d.2⟩, rfl⟩
  have hminus : ∀ U : Submodule F (ι → F), U ≤ LinearMap.range (Matrix.mulVecLin e) →
      finrank F U = 2 → ∃ u ∈ U, Q u ≠ 0 :=
    minus_of_fieldExt_four hF Q hQ hj hrange ψ hψ S hee hadj hcommS hse hrk hJ'e
      (by rw [hJmap]; exact hFE)
  have hcard_le : Nat.card ↥(ℓB.range) ≤
      p * Nat.card ↥(ℓB.range ⊓ (glFixing e).comap (Spin.spinMatrix Q)) :=
    card_le_mul_of_minusFour Q hQ hp hp2 (ℓB.range) hEelem hee hadj hcommE hrk hminus
  have hker_le : Nat.card ↥(ℓB.range ⊓ (glFixing e).comap (Spin.spinMatrix Q)) ≤
      Nat.card ↥D :=
    a4_card_kernel_le (Spin.spinMatrix Q) hj ψ hDB hBab hBJ ℓB hlift S hS hJ'e hJmap he
  have h1 : p ^ 4 ≤ Nat.card ↥(ℓB.range) := by rw [hcardE]; exact hB4
  have hchain : p ^ 4 ≤ p * Nat.card ↥D := by
    calc p ^ 4 ≤ Nat.card ↥(ℓB.range) := h1
      _ ≤ p * Nat.card ↥(ℓB.range ⊓ (glFixing e).comap (Spin.spinMatrix Q)) := hcard_le
      _ ≤ p * Nat.card ↥D := Nat.mul_le_mul_left p hker_le
  have h5 : p ^ 4 ≤ p ^ 3 := by
    have h4 : p * Nat.card ↥D = p ^ 3 := by rw [hDcard]; ring
    rwa [h4] at hchain
  exact absurd h5 (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by norm_num : 3 < 4)))

theorem ggSixTCCaseAPOmegaPlus_holds :
    GGSixTCCaseAPOmegaPlus := by
  intro X _ _ k f ψ p G₀ B₁ D J L x hpos ℓ S hS hℓ hℓp J' e hJ' hJmap hFE hJ'e he hse hrk
  have hf : 1 ≤ f := (hpos.model.admissible).2.1
  have hcF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  let Q := ggOmQuadPlus k f
  have hQnd : (QuadraticMap.polarBilin Q).Nondegenerate :=
    Spin.nondegenerate_polarBilin_quadPlus (k + 3) (GaloisField 2 f)
  have hj : Function.Injective (Spin.spinMatrix Q) := by
    simpa only [Q, ggOmQuadPlus] using a0p_spinMatrix_injective (GaloisField 2 f) (k + 3)
  have hrange : (Spin.spinAction Q).range = orthDerived Q := by
    simpa only [Q, ggOmQuadPlus, orthDerived] using
      Spin.range_spinAction_quadPlus_eq_commutator (n := k + 3) (K := GaloisField 2 f) (by omega)
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff ψ, eq_bot_iff]
    intro u hu
    have hcenter : Subgroup.center (ggU .POmegaPlus (k + 3) f).K = ⊥ :=
      RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo (n := k + 3)
        (K := GaloisField 2 f) (by omega)
    exact Subgroup.mem_bot.mp (hcenter ▸ hpos.ker_le hu)
  obtain ⟨ℓB, hlift, hpow, hext⟩ :=
    ggSixTCLiftBPOmegaPlus_holds k f ψ p G₀ B₁ D J L x hpos ℓ hℓ
  have hS' : S = Set.range (fun d : ↥D =>
      Spin.spinMatrix Q (ℓB ⟨(d : X), hpos.D_le d.2⟩)) := by
    rw [hS]
    congr 1
    funext d
    rw [hext d]
  have hBG : B₁ ⊓ Subgroup.centralizer (ψ.range : Set X) = ⊥ := by
    rw [hpos.range_eq]
    exact hpos.B_inf_C_G0
  have hFE' : GGSixLSevenFieldExtCase J .POmegaPlus f := by
    rw [← hJmap]
    exact hFE
  have hJ'e' : IsComponentOf J' ⁅glBlockCentralizer (Spin.spinMatrix Q) S e,
      glBlockCentralizer (Spin.spinMatrix Q) S e⁆ := by
    simpa only [Q, ggOmQuadPlus, ggOmSpinPlus] using hJ'e
  exact ggSixTCCaseAPOmega_false hcF Q hQnd hj hrange ψ hψ hpos.prime hpos.ne_two hpos.D_le
    hpos.elemAbelian hpos.card_D hpos.four_le hBG hpos.B_inf_C_J ℓB hlift hpow S hS'
    hJ'e' hJmap hFE' he hse hrk

theorem ggSixTCCaseAPOmegaMinus_holds :
    GGSixTCCaseAPOmegaMinus := by
  intro X _ _ n f ψ p G₀ B₁ D J L x hpos ℓ S hS hℓ hℓp J' e hJ' hJmap hFE hJ'e he hse hrk
  have hf : 1 ≤ f := (hpos.model.admissible).2.1
  have hn4 : 4 ≤ n := (hpos.model.admissible).2.2
  have hcF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  let Q := ggOmQuadMinus n f
  have hQnd : (QuadraticMap.polarBilin Q).Nondegenerate :=
    Spin.nondegenerate_polarBilin_quadMinus_of_finite n (GaloisField 2 f) (minusCoeffs_irr 2 f)
  have hj : Function.Injective (Spin.spinMatrix Q) := by
    simpa only [Q, ggOmQuadMinus] using
      a0m_spinMatrix_injective (GaloisField 2 f) n (minusCoeffs_irr 2 f)
  have hrange : (Spin.spinAction Q).range = orthDerived Q := by
    simpa only [Q, ggOmQuadMinus, orthDerived] using
      Spin.range_spinAction_quadMinus_eq_commutator (n := n) (K := GaloisField 2 f) hn4
        (minusCoeffs_irr 2 f)
  have hψ : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff ψ, eq_bot_iff]
    intro u hu
    have hcenter : Subgroup.center (ggU .POmegaMinus n f).K = ⊥ :=
      CFSG.RankThree.PartOne.CTP.center_spinGroup_quadMinus_eq_bot (F := GaloisField 2 f) hn4
        (minusCoeffs_irr 2 f)
    exact Subgroup.mem_bot.mp (hcenter ▸ hpos.ker_le hu)
  obtain ⟨ℓB, hlift, hpow, hext⟩ :=
    ggSixTCLiftBPOmegaMinus_holds n f ψ p G₀ B₁ D J L x hpos ℓ hℓ
  have hS' : S = Set.range (fun d : ↥D =>
      Spin.spinMatrix Q (ℓB ⟨(d : X), hpos.D_le d.2⟩)) := by
    rw [hS]
    congr 1
    funext d
    rw [hext d]
  have hBG : B₁ ⊓ Subgroup.centralizer (ψ.range : Set X) = ⊥ := by
    rw [hpos.range_eq]
    exact hpos.B_inf_C_G0
  have hFE' : GGSixLSevenFieldExtCase J .POmegaMinus f := by
    rw [← hJmap]
    exact hFE
  have hJ'e' : IsComponentOf J' ⁅glBlockCentralizer (Spin.spinMatrix Q) S e,
      glBlockCentralizer (Spin.spinMatrix Q) S e⁆ := by
    simpa only [Q, ggOmQuadMinus, ggOmSpinMinus] using hJ'e
  exact ggSixTCCaseAPOmega_false hcF Q hQnd hj hrange ψ hψ hpos.prime hpos.ne_two hpos.D_le
    hpos.elemAbelian hpos.card_D hpos.four_le hBG hpos.B_inf_C_J ℓB hlift hpow S hS'
    hJ'e' hJmap hFE' he hse hrk

end CaseA

end CFSG.StandardType

end
