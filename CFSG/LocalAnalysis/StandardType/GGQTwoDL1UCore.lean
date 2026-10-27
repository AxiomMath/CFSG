module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.ClassicalInvolution.Balance.StrongPowSuBlocks
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1UAut
import CFSG.LocalAnalysis.StandardType.GGQTwoDL1UMat
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosBlockAux3
import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.ClassicalInvolution.Balance.PassTwoFinal
public import CFSG.ClassicalInvolution.Models.LinearFrames
public import CFSG.ClassicalInvolution.Models.LinearPairs
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieClassical
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddLieE6E7Triality

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {K : Type} [Field K] [Finite K] [CharP K 2]

private lemma p9uUCor_val_mul_val_inv {n : ℕ} (B : GL (Fin n) K) :
    (B : Matrix (Fin n) (Fin n) K) * ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

private lemma p9uUCor_val_inv_mul_val {n : ℕ} (B : GL (Fin n) K) :
    ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

private theorem p9uUCor_unitary_mul {n : ℕ} {A B : GL (Fin n) K}
    (hA : ggIsUnitaryMat (p := 2) (f := 1) A) (hB : ggIsUnitaryMat (p := 2) (f := 1) B) :
    ggIsUnitaryMat (p := 2) (f := 1) (A * B) := by
  unfold ggIsUnitaryMat at hA hB ⊢
  rw [Units.val_mul, conjTr_mul]
  calc conjTr (unitaryInvolution K 2 1) (B : Matrix (Fin n) (Fin n) K) *
        conjTr (unitaryInvolution K 2 1) (A : Matrix (Fin n) (Fin n) K) *
        ((A : Matrix (Fin n) (Fin n) K) * (B : Matrix (Fin n) (Fin n) K))
      = conjTr (unitaryInvolution K 2 1) (B : Matrix (Fin n) (Fin n) K) *
          (conjTr (unitaryInvolution K 2 1) (A : Matrix (Fin n) (Fin n) K) *
            (A : Matrix (Fin n) (Fin n) K)) *
          (B : Matrix (Fin n) (Fin n) K) := by noncomm_ring
    _ = 1 := by rw [hA, Matrix.mul_one, hB]

private theorem p9uUCor_unitary_inv {n : ℕ} {A : GL (Fin n) K}
    (hA : ggIsUnitaryMat (p := 2) (f := 1) A) :
    ggIsUnitaryMat (p := 2) (f := 1) A⁻¹ := by
  unfold ggIsUnitaryMat at hA ⊢
  calc conjTr (unitaryInvolution K 2 1) ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
      = conjTr (unitaryInvolution K 2 1) ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          (conjTr (unitaryInvolution K 2 1) (A : Matrix (Fin n) (Fin n) K) *
            (A : Matrix (Fin n) (Fin n) K)) *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by rw [hA, Matrix.mul_one]
    _ = conjTr (unitaryInvolution K 2 1) ((A : Matrix (Fin n) (Fin n) K) *
          ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
          ((A : Matrix (Fin n) (Fin n) K) *
            ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := by
        simp only [conjTr_mul, Matrix.mul_assoc]
    _ = 1 := by rw [p9uUCor_val_mul_val_inv, conjTr_one, Matrix.one_mul]

private theorem p9uUCor_unitary_pow {n : ℕ} {g : GL (Fin n) K}
    (hg : ggIsUnitaryMat (p := 2) (f := 1) g) (m : ℕ) :
    ggIsUnitaryMat (p := 2) (f := 1) (g ^ m) := by
  induction m with
  | zero => simp [ggIsUnitaryMat, conjTr_one]
  | succ m ih => rw [pow_succ]; exact p9uUCor_unitary_mul ih hg

private lemma p9uUCor_coe_map {n : ℕ} (f : K ≃+* K) (g : GL (Fin n) K) :
    ((Matrix.GeneralLinearGroup.map (f : K →+* K) g : GL (Fin n) K) :
        Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K).map f := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply]
  rfl

private lemma p9uUCor_map_injective {n : ℕ} (τ : K ≃+* K) :
    Function.Injective (Matrix.GeneralLinearGroup.map (τ : K →+* K) :
      GL (Fin n) K → GL (Fin n) K) := by
  intro a b h
  apply Units.ext
  ext i j
  have hh : (τ : K →+* K) ((a : Matrix (Fin n) (Fin n) K) i j) =
      (τ : K →+* K) ((b : Matrix (Fin n) (Fin n) K) i j) := by
    have := congrArg (fun z : GL (Fin n) K => (z : Matrix (Fin n) (Fin n) K) i j) h
    simpa only [Matrix.GeneralLinearGroup.map_apply] using this
  exact (τ : K →+* K).injective hh

private lemma p9uUCor_det_conj {n : ℕ} (g m : GL (Fin n) K)
    (hm : (m : Matrix (Fin n) (Fin n) K).det = 1) :
    ((g * m * g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).det = 1 := by
  rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hm, mul_one,
    ← Matrix.det_mul, p9uUCor_val_mul_val_inv, Matrix.det_one]

private noncomputable def p9uUCor_conjSu {n : ℕ} {g : GL (Fin n) K}
    (hg : ggIsUnitaryMat (p := 2) (f := 1) g) (u : Su K 2 1 n) : Su K 2 1 n :=
  ⟨g * (u : GL (Fin n) K) * g⁻¹, by
    refine mem_SUid.mpr ⟨p9uUCor_det_conj g (u : GL (Fin n) K) (mem_SUid.mp u.2).1, ?_⟩
    exact p9uUCor_unitary_mul (p9uUCor_unitary_mul hg (mem_SUid.mp u.2).2)
      (p9uUCor_unitary_inv hg)⟩

private lemma p9uUCor_conjSu_coe {n : ℕ} {g : GL (Fin n) K}
    (hg : ggIsUnitaryMat (p := 2) (f := 1) g) (u : Su K 2 1 n) :
    ((p9uUCor_conjSu hg u : Su K 2 1 n) : GL (Fin n) K) =
      g * (u : GL (Fin n) K) * g⁻¹ := rfl

private noncomputable def p9uUCor_semilinSu {n : ℕ} (g : GL (Fin n) K)
    (hg : ggIsUnitaryMat (p := 2) (f := 1) g) (τ : K ≃+* K) (u : Su K 2 1 n) : Su K 2 1 n :=
  ⟨g * Matrix.GeneralLinearGroup.map (τ : K →+* K) (u : GL (Fin n) K) * g⁻¹, by
    refine mem_SUid.mpr ⟨p9uUCor_det_conj g _ (mem_SUid.mp
      (map_mem_SUid (p := 2) (f := 1) τ u.2)).1, ?_⟩
    exact p9uUCor_unitary_mul (p9uUCor_unitary_mul hg
      (mem_SUid.mp (map_mem_SUid (p := 2) (f := 1) τ u.2)).2) (p9uUCor_unitary_inv hg)⟩

private lemma p9uUCor_semilinSu_coe {n : ℕ} (g : GL (Fin n) K)
    (hg : ggIsUnitaryMat (p := 2) (f := 1) g) (τ : K ≃+* K) (u : Su K 2 1 n) :
    ((p9uUCor_semilinSu g hg τ u : Su K 2 1 n) : GL (Fin n) K) =
      g * Matrix.GeneralLinearGroup.map (τ : K →+* K) (u : GL (Fin n) K) * g⁻¹ := rfl

private lemma p9uUCor_semilin_conjSu {n : ℕ} {g : GL (Fin n) K}
    (hg : ggIsUnitaryMat (p := 2) (f := 1) g) (τ : K ≃+* K)
    (t : Su K 2 1 n) (u : Su K 2 1 n) :
    p9uUCor_semilinSu g hg τ (p9uUCor_conjSu (g := (t : GL (Fin n) K)) (mem_SUid.mp t.2).2 u) =
      p9uUCor_conjSu (g := g * Matrix.GeneralLinearGroup.map (τ : K →+* K)
          (t : GL (Fin n) K) * g⁻¹)
        (p9uUCor_unitary_mul (p9uUCor_unitary_mul hg
          (mem_SUid.mp (map_mem_SUid (p := 2) (f := 1) τ t.2)).2) (p9uUCor_unitary_inv hg))
        (p9uUCor_semilinSu g hg τ u) := by
  apply Subtype.ext
  change g * Matrix.GeneralLinearGroup.map (τ : K →+* K)
      ((t : GL (Fin n) K) * (u : GL (Fin n) K) * (t : GL (Fin n) K)⁻¹) * g⁻¹ =
    (g * Matrix.GeneralLinearGroup.map (τ : K →+* K) (t : GL (Fin n) K) * g⁻¹) *
      (g * Matrix.GeneralLinearGroup.map (τ : K →+* K) (u : GL (Fin n) K) * g⁻¹) *
      (g * Matrix.GeneralLinearGroup.map (τ : K →+* K) (t : GL (Fin n) K) * g⁻¹)⁻¹
  rw [map_mul, map_mul, map_inv]
  group

private lemma p9uUCor_conjSu_trans {n : ℕ} (A t : GL (Fin n) K)
    (hA : ggIsUnitaryMat (p := 2) (f := 1) A) (ht : ggIsUnitaryMat (p := 2) (f := 1) t)
    (u : Su K 2 1 n) :
    p9uUCor_conjSu (g := A) hA u =
      p9uUCor_conjSu (g := A * t⁻¹) (p9uUCor_unitary_mul hA (p9uUCor_unitary_inv ht))
        (p9uUCor_conjSu (g := t) ht u) := by
  apply Subtype.ext
  change A * (u : GL (Fin n) K) * A⁻¹ =
    (A * t⁻¹) * (t * (u : GL (Fin n) K) * t⁻¹) * (A * t⁻¹)⁻¹
  group

private lemma p9uUCor_mem_range {G : Type} [Group G] {X : Subgroup G} {K : Type} [Field K]
    [Finite K] [CharP K 2] {n : ℕ} {ψ : Su K 2 1 n →* G} (hrange : ψ.range = X)
    (u : Su K 2 1 n) : ψ u ∈ X := by
  rw [← hrange]
  exact MonoidHom.mem_range.mpr ⟨u, rfl⟩

private lemma p9uUCor_scalar {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs X : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {ψ : Su K 2 1 n →* G}
    (hK : Nat.card K = 4) (h : GGNSLocalHyp p B Bs K 1 n ψ) (hrange : ψ.range = X)
    (α : MulAut ↥X) {g : GL (Fin n) K} (hg : ggIsUnitaryMat (p := 2) (f := 1) g)
    {τ : K ≃+* K}
    (hφ : ∀ u : Su K 2 1 n, ∀ y : ↥X, (y : G) = ψ u →
      ((α y : ↥X) : G) = ψ (p9uUCor_semilinSu g hg τ u))
    {J : Finset (Fin n)}
    (hα : ∀ (t : Su K 2 1 n) (d : Fin n → K),
      ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d →
        (∀ l, d l ^ 3 = 1) → (∀ a ∈ J, ∀ b ∈ J, d a = d b) →
          ∀ z : ↥X, (z : G) = ψ t → ∀ y : ↥X, α (z * y * z⁻¹) = z * α y * z⁻¹)
    (d : Fin n → K) (hd3 : ∀ l, d l ^ 3 = 1) (hprod : ∏ l, d l = 1)
    (hdJ : ∀ a ∈ J, ∀ b ∈ J, d a = d b) :
    ∃ c : K, (g : Matrix (Fin n) (Fin n) K) * Matrix.diagonal (fun l => τ (d l)) =
      c • (Matrix.diagonal d * (g : Matrix (Fin n) (Fin n) K)) := by
  classical
  have hunit : ∀ l, unitaryInvolution K 2 1 (d l) * d l = 1 := by
    intro l
    rw [unitaryInvolution_apply, pow_one]
    calc d l ^ 2 * d l = d l ^ 3 := by ring
      _ = 1 := hd3 l
  let t : Su K 2 1 n := ggNSPosPB2_diagSU (f := 1) d hprod hunit
  have htd : ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d :=
    ggNSPosPB2_diagSU_coe d hprod hunit
  have htU : ggIsUnitaryMat (p := 2) (f := 1) (t : GL (Fin n) K) := (mem_SUid.mp t.2).2
  let A : GL (Fin n) K :=
    g * Matrix.GeneralLinearGroup.map (τ : K →+* K) (t : GL (Fin n) K) * g⁻¹
  have hAU : ggIsUnitaryMat (p := 2) (f := 1) A :=
    p9uUCor_unitary_mul (p9uUCor_unitary_mul hg
      (mem_SUid.mp (map_mem_SUid (p := 2) (f := 1) τ t.2)).2) (p9uUCor_unitary_inv hg)
  let N : GL (Fin n) K := A * (t : GL (Fin n) K)⁻¹
  have hNU : ggIsUnitaryMat (p := 2) (f := 1) N :=
    p9uUCor_unitary_mul hAU (p9uUCor_unitary_inv htU)
  have hmain : ∀ u : Su K 2 1 n,
      ψ (p9uUCor_conjSu hNU (p9uUCor_conjSu htU (p9uUCor_semilinSu g hg τ u))) =
        ψ (p9uUCor_conjSu htU (p9uUCor_semilinSu g hg τ u)) := by
    intro u
    have hzX : ψ t ∈ X := p9uUCor_mem_range hrange t
    have hyX : ψ u ∈ X := p9uUCor_mem_range hrange u
    have hcomm := hα t d htd hd3 hdJ ⟨ψ t, hzX⟩ rfl ⟨ψ u, hyX⟩
    have hcu : p9uUCor_conjSu htU u = t * u * t⁻¹ := by
      apply Subtype.ext
      rw [p9uUCor_conjSu_coe]
      rfl
    have h1 : ((α (⟨ψ t, hzX⟩ * ⟨ψ u, hyX⟩ * ⟨ψ t, hzX⟩⁻¹) : ↥X) : G) =
        ψ (p9uUCor_semilinSu g hg τ (p9uUCor_conjSu htU u)) := by
      refine hφ (p9uUCor_conjSu htU u) _ ?_
      rw [hcu]
      change ψ t * ψ u * (ψ t)⁻¹ = ψ (t * u * t⁻¹)
      rw [map_mul, map_mul, map_inv]
    have h2 : ((⟨ψ t, hzX⟩ * α (⟨ψ u, hyX⟩ : ↥X) * ⟨ψ t, hzX⟩⁻¹ : ↥X) : G) =
        ψ (p9uUCor_conjSu htU (p9uUCor_semilinSu g hg τ u)) := by
      change ψ t * ((α (⟨ψ u, hyX⟩ : ↥X) : ↥X) : G) * (ψ t)⁻¹ =
        ψ (p9uUCor_conjSu htU (p9uUCor_semilinSu g hg τ u))
      rw [hφ u (⟨ψ u, hyX⟩ : ↥X) rfl]
      have hcu2 : p9uUCor_conjSu htU (p9uUCor_semilinSu g hg τ u) =
          t * p9uUCor_semilinSu g hg τ u * t⁻¹ := by
        apply Subtype.ext
        rw [p9uUCor_conjSu_coe]
        rfl
      rw [hcu2, map_mul, map_mul, map_inv]
    have h3 : ψ (p9uUCor_semilinSu g hg τ (p9uUCor_conjSu htU u)) =
        ψ (p9uUCor_conjSu htU (p9uUCor_semilinSu g hg τ u)) := by
      rw [← h1, ← h2]
      exact congrArg (fun w : ↥X => (w : G)) hcomm
    rw [p9uUCor_semilin_conjSu hg τ t u,
      p9uUCor_conjSu_trans A (t : GL (Fin n) K) hAU htU (p9uUCor_semilinSu g hg τ u)] at h3
    exact h3
  have hInj : Function.Injective (fun u : Su K 2 1 n =>
      p9uUCor_conjSu htU (p9uUCor_semilinSu g hg τ u)) := by
    intro u₁ u₂ hh
    have hsem : p9uUCor_semilinSu g hg τ u₁ = p9uUCor_semilinSu g hg τ u₂ := by
      apply Subtype.ext
      have hc := congrArg (fun z : Su K 2 1 n => (z : GL (Fin n) K)) hh
      change t * (p9uUCor_semilinSu g hg τ u₁ : GL (Fin n) K) * t⁻¹ =
        t * (p9uUCor_semilinSu g hg τ u₂ : GL (Fin n) K) * t⁻¹ at hc
      exact mul_left_cancel (mul_right_cancel hc)
    apply Subtype.ext
    have hc := congrArg (fun z : Su K 2 1 n => (z : GL (Fin n) K)) hsem
    change g * Matrix.GeneralLinearGroup.map (τ : K →+* K) (u₁ : GL (Fin n) K) * g⁻¹ =
      g * Matrix.GeneralLinearGroup.map (τ : K →+* K) (u₂ : GL (Fin n) K) * g⁻¹ at hc
    exact p9uUCor_map_injective τ (mul_left_cancel (mul_right_cancel hc))
  have hψfix : ∀ w : Su K 2 1 n, ψ (p9uUCor_conjSu hNU w) = ψ w := by
    intro w
    obtain ⟨u, rfl⟩ := Finite.surjective_of_injective hInj w
    exact hmain u
  have hfix : ∀ u v : Su K 2 1 n,
      ((v : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
          (N : Matrix (Fin n) (Fin n) K) * ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((N⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) → ψ v = ψ u := by
    intro u v hv
    have hv' : v = p9uUCor_conjSu hNU u := by
      apply Subtype.ext
      apply Units.ext
      exact hv
    rw [hv']
    exact hψfix u
  obtain ⟨c, hc⟩ := qtwoDL1_unitChart_scalar_of_fix hK h hNU hfix
  refine ⟨c, ?_⟩
  have hAmat : (A : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) * Matrix.diagonal (fun l => τ (d l)) *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    show ((g * Matrix.GeneralLinearGroup.map (τ : K →+* K) (t : GL (Fin n) K) * g⁻¹ :
      GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = _
    rw [Units.val_mul, Units.val_mul, p9uUCor_coe_map, htd, Matrix.diagonal_map (map_zero τ)]
  have hAeq : (A : Matrix (Fin n) (Fin n) K) = c • Matrix.diagonal d := by
    have hNt : A = N * (t : GL (Fin n) K) := by
      change g * Matrix.GeneralLinearGroup.map (τ : K →+* K) (t : GL (Fin n) K) * g⁻¹ =
        (g * Matrix.GeneralLinearGroup.map (τ : K →+* K) (t : GL (Fin n) K) * g⁻¹ *
          (t : GL (Fin n) K)⁻¹) * (t : GL (Fin n) K)
      group
    rw [hNt, Units.val_mul, hc, htd, Matrix.smul_mul, Matrix.one_mul]
  have hfin : (g : Matrix (Fin n) (Fin n) K) * Matrix.diagonal (fun l => τ (d l)) *
      ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • Matrix.diagonal d :=
    hAmat.symm.trans hAeq
  have h1 : ((g : Matrix (Fin n) (Fin n) K) * Matrix.diagonal (fun l => τ (d l)) *
      ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) * (g : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K) * Matrix.diagonal (fun l => τ (d l)) := by
    rw [Matrix.mul_assoc, p9uUCor_val_inv_mul_val, Matrix.mul_one]
  calc (g : Matrix (Fin n) (Fin n) K) * Matrix.diagonal (fun l => τ (d l))
      = ((g : Matrix (Fin n) (Fin n) K) * Matrix.diagonal (fun l => τ (d l)) *
          ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *
          (g : Matrix (Fin n) (Fin n) K) := h1.symm
    _ = (c • Matrix.diagonal d) * (g : Matrix (Fin n) (Fin n) K) := by rw [hfin]
    _ = c • (Matrix.diagonal d * (g : Matrix (Fin n) (Fin n) K)) := by rw [Matrix.smul_mul]

theorem qtwoDL1_unitChart_fixTorus {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs X : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {ψ : Su K 2 1 n →* G}
    (hK : Nat.card K = 4) (h : GGNSLocalHyp p B Bs K 1 n ψ) (hrange : ψ.range = X)
    {J : Finset (Fin n)} (hJ : J.card = 0 ∨ J.card = 3) (α : MulAut ↥X)
    (hα : ∀ (t : Su K 2 1 n) (d : Fin n → K),
      ((t : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = Matrix.diagonal d →
        (∀ l, d l ^ 3 = 1) → (∀ a ∈ J, ∀ b ∈ J, d a = d b) →
          ∀ z : ↥X, (z : G) = ψ t → ∀ y : ↥X, α (z * y * z⁻¹) = z * α y * z⁻¹)
    {k : ℕ} (hαk : α ^ (2 ^ k) = 1) :
    ∃ s ∈ coordBlockSU K 2 1 J, s ^ (2 ^ k) = 1 ∧
      ∀ (u : Su K 2 1 n) (y : ↥X), (y : G) = ψ u → ((α y : ↥X) : G) = ψ (s * u * s⁻¹) := by
  classical
  obtain ⟨g, τ, hg, hsem⟩ := qtwoDL1_unitChart_semilin hK h hrange α
  have hφ : ∀ u : Su K 2 1 n, ∀ y : ↥X, (y : G) = ψ u →
      ((α y : ↥X) : G) = ψ (p9uUCor_semilinSu g hg τ u) := by
    intro u y hy
    refine hsem u (p9uUCor_semilinSu g hg τ u) ?_ y hy
    rw [p9uUCor_semilinSu_coe, Units.val_mul, Units.val_mul, p9uUCor_coe_map]
  obtain ⟨hτ, hoff⟩ := qtwoDL1_unitMat_block hK h.four_le hJ
    (fun d hd3 hprod hdJ => p9uUCor_scalar hK h hrange α hg hφ hα d hd3 hprod hdJ)
  have hφ0 : ∀ u : Su K 2 1 n, ∀ y : ↥X, (y : G) = ψ u →
      ((α y : ↥X) : G) = ψ (p9uUCor_conjSu hg u) := by
    intro u y hy
    rw [hφ u y hy]
    congr 1
    apply Subtype.ext
    change g * Matrix.GeneralLinearGroup.map (τ : K →+* K) (u : GL (Fin n) K) * g⁻¹ =
      g * (u : GL (Fin n) K) * g⁻¹
    rw [hτ]
    simp [Matrix.GeneralLinearGroup.map_id]
  have hpow : ∀ m : ℕ, ∀ u : Su K 2 1 n, ∀ hu : ψ u ∈ X,
      (((α ^ m) (⟨ψ u, hu⟩ : ↥X) : ↥X) : G) =
        ψ (p9uUCor_conjSu (p9uUCor_unitary_pow hg m) u) := by
    intro m
    induction m with
    | zero =>
        intro u hu
        rw [show α ^ 0 = 1 from pow_zero α, MulAut.one_apply]
        have h0 : p9uUCor_conjSu (g := g ^ 0) (p9uUCor_unitary_pow hg 0) u = u := by
          apply Subtype.ext
          rw [p9uUCor_conjSu_coe, pow_zero]
          group
        rw [h0]
    | succ m ih =>
        intro u hu
        rw [pow_succ', MulAut.mul_apply]
        have hy := hφ0 (p9uUCor_conjSu (p9uUCor_unitary_pow hg m) u)
          ((α ^ m) (⟨ψ u, hu⟩ : ↥X)) (ih u hu)
        rw [hy]
        congr 1
        apply Subtype.ext
        simp only [p9uUCor_conjSu_coe]
        rw [pow_succ']
        group
  obtain ⟨c₀, hgk⟩ : ∃ c₀ : K, ((g ^ (2 ^ k) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      c₀ • (1 : Matrix (Fin n) (Fin n) K) := by
    have hfixk : ∀ u v : Su K 2 1 n,
        ((v : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
            ((g ^ (2 ^ k) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              ((u : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              (((g ^ (2 ^ k))⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) →
            ψ v = ψ u := by
      intro u v hv
      have hv' : v = p9uUCor_conjSu (p9uUCor_unitary_pow hg (2 ^ k)) u := by
        apply Subtype.ext
        apply Units.ext
        exact hv
      rw [hv']
      have hp := hpow (2 ^ k) u (p9uUCor_mem_range hrange u)
      rw [hαk, MulAut.one_apply] at hp
      exact hp.symm
    exact qtwoDL1_unitChart_scalar_of_fix hK h (p9uUCor_unitary_pow hg (2 ^ k)) hfixk
  obtain ⟨s, hsJ, hsk, c, hsc⟩ := qtwoDL1_unitMat_mem_block hK hg hoff hgk
  refine ⟨s, hsJ, hsk, ?_⟩
  intro u y hy
  rw [hφ0 u y hy]
  have hsu : s * u * s⁻¹ = p9uUCor_conjSu hg u := by
    let z : GL (Fin n) K := g⁻¹ * (s : GL (Fin n) K)
    have hzmat : (z : Matrix (Fin n) (Fin n) K) = c • 1 := by
      show ((g⁻¹ * (s : GL (Fin n) K) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = c • 1
      rw [Units.val_mul, hsc, Matrix.mul_smul, p9uUCor_val_inv_mul_val]
    have hzcomm : ∀ w : Su K 2 1 n,
        z * (w : GL (Fin n) K) = (w : GL (Fin n) K) * z := by
      intro w
      apply Units.ext
      change (z : Matrix (Fin n) (Fin n) K) * (w : GL (Fin n) K) =
        (w : GL (Fin n) K) * (z : Matrix (Fin n) (Fin n) K)
      rw [hzmat, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one]
    have hsz : (s : GL (Fin n) K) = g * z := by
      show (s : GL (Fin n) K) = g * (g⁻¹ * (s : GL (Fin n) K))
      group
    have hzu : z * (u : GL (Fin n) K) * z⁻¹ = (u : GL (Fin n) K) := by
      rw [hzcomm u, mul_assoc, mul_inv_cancel, mul_one]
    apply Subtype.ext
    change (s : GL (Fin n) K) * (u : GL (Fin n) K) * (s : GL (Fin n) K)⁻¹ =
      g * (u : GL (Fin n) K) * g⁻¹
    calc (s : GL (Fin n) K) * (u : GL (Fin n) K) * (s : GL (Fin n) K)⁻¹
        = (g * z) * (u : GL (Fin n) K) * (g * z)⁻¹ := by rw [hsz]
      _ = g * (z * (u : GL (Fin n) K) * z⁻¹) * g⁻¹ := by group
      _ = g * (u : GL (Fin n) K) * g⁻¹ := by rw [hzu]
  rw [← hsu]

end CFSG.StandardType.QTwo

end
