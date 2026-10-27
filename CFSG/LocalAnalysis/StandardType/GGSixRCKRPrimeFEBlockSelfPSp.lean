module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPSp
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
import all CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPSp

public section

namespace CFSG.StandardType.ClassicalPosition

open scoped Matrix

private lemma rckRPfss_ringEquiv_apply_apply {K : Type} [Semiring K] (σ : K ≃+* K)
    (hσ2 : σ ^ 2 = 1) (x : K) : σ (σ x) = x := by
  have hc := congrFun (congrArg (fun e : K ≃+* K => (e : K → K)) hσ2) x
  simpa [pow_two] using hc

private lemma rckRPfss_transpose_mul_G {n : ℕ} {F : Type} [Field F] [CharP F 2]
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hadj : formAdj (RingHom.id F)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) e = e) :
    eᵀ * (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * e := by
  have hG : IsUnit (fePSp_G n F).det := fePSp_G_isUnit_det
  have h := hadj
  change formAdj (RingHom.id F) (fePSp_G n F) e = e at h
  simp only [formAdj] at h
  have h2 : fePSp_G n F *
      ((fePSp_G n F)⁻¹ * (e.map (RingHom.id F))ᵀ * fePSp_G n F) = fePSp_G n F * e :=
    congrArg (fun X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F => fePSp_G n F * X) h
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc,
    Matrix.mul_nonsing_inv (fePSp_G n F) hG, Matrix.one_mul] at h2
  simpa [fePSp_G] using h2

theorem exists_blockAction_selfDual_PSp {n f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hc : Nat.card F = 2 ^ f) {S : Set (GL (Fin n ⊕ Fin n) F)}
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n F) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s)) {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hadj : formAdj (RingHom.id F)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) e = e)
    (hd : 4 ≤ blockDegree (Algebra.adjoin F (Units.val '' S)) e) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra F K) (_ : Finite K) (l : ℕ)
      (W : Type) (_ : AddCommGroup W) (_ : Module F W) (_ : Module K W)
      (_ : IsScalarTower F K W) (_ : FiniteDimensional K W)
      (σ : K ≃+* K) (β : W →ₛₗ[σ.toRingHom] W →ₗ[K] K)
      (eW : W ≃ₗ[F] LinearMap.range (Matrix.toLin' e))
      (φ : ↥(glBlockCentralizer (CFSG.Open.StatedSp n F).subtype S e) →* (W ≃ₗ[K] W)),
      blockDegree (Algebra.adjoin F (Units.val '' S)) e = 2 * l ∧
      Nat.card K = (2 ^ (l * f)) ^ 2 ∧
      σ ^ 2 = 1 ∧ σ ≠ 1 ∧ (∀ c : F, σ (algebraMap F K c) = algebraMap F K c) ∧
      β.IsSymm ∧ β.SeparatingLeft ∧ Function.Injective φ ∧
      (∀ g w w', β (φ g w) (φ g w') = β w w') ∧
      (∀ g : W ≃ₗ[K] W, (∀ w w', β (g w) (g w') = β w w') → g ∈ φ.range) ∧
      (∀ g w, (eW (φ g w) : (Fin n ⊕ Fin n) → F) =
        (((g : ↥(CFSG.Open.StatedSp n F)) : GL (Fin n ⊕ Fin n) F) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ (eW w : (Fin n ⊕ Fin n) → F)) ∧
      (∀ w w', (eW w : (Fin n ⊕ Fin n) → F) ⬝ᵥ
        ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ
          (eW w' : (Fin n ⊕ Fin n) → F)) = Algebra.trace F K (β w w')) ∧
      ∀ m m' : (Fin n ⊕ Fin n) → F, ((1 - e) *ᵥ m) ⬝ᵥ
        ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ
          (e *ᵥ m')) = 0 := by
  obtain ⟨K, hKf, hKa, hKfin, l, hdeg, hcard, hfin, π, hπ, hker⟩ :=
    fePSp_selfDual_blockFieldAndInvolution hc hSU hS hodd he hadj hd
  letI : Field K := hKf
  letI : Algebra F K := hKa
  haveI : Finite K := hKfin
  obtain ⟨σ, hσ2, hσne, hσalg, hσπ⟩ :=
    fePSp_selfDual_adjointInvolution hdeg hSU hS he hadj hfin π hπ hker
  obtain ⟨W, hWac, hWF, hWK, hTower, hWfd, _, eW, f, hact, _, hfinj, halgact⟩ :=
    fePSp_selfDual_unitaryBlockKAction hS he π hπ hker hfin
  letI : AddCommGroup W := hWac
  letI : Module F W := hWF
  letI : Module K W := hWK
  haveI : IsScalarTower F K W := hTower
  haveI : FiniteDimensional K W := hWfd
  obtain ⟨β, ⟨hβpres, hβadd₁, hβadd₂, hβsmul₁, hβsmul₂, hβsep⟩, hβsym, hβtrace⟩ :=
    fePSp_selfDual_unitaryBlockForm hSU he hadj σ hσ2 hσalg π hπ hσπ W eW f hact halgact
  let βlin : W →ₛₗ[σ.toRingHom] W →ₗ[K] K :=
    LinearMap.mk₂'ₛₗ σ.toRingHom (RingHom.id K) β hβadd₁
      (fun c w1 w2 => hβsmul₁ w1 w2 c) hβadd₂
      (fun c w1 w2 => hβsmul₂ w1 w2 c)
  have hsymm : βlin.IsSymm := by
    refine ⟨fun x y => ?_⟩
    change σ (β x y) = β y x
    calc σ (β x y) = σ (σ (β y x)) := by rw [hβsym x y]
      _ = β y x := rckRPfss_ringEquiv_apply_apply σ hσ2 (β y x)
  have hsep : βlin.SeparatingLeft := fun x hx => hβsep x (fun y => hx y)
  have hisom : ∀ g : W ≃ₗ[K] W, (∀ w w', β (g w) (g w') = β w w') → g ∈ f.range :=
    fePSp_selfDual_unitaryBlockIsometryRange_eq hS he hadj W eW f hact β π halgact hβtrace
  have heT : eᵀ * fePSp_G n F = fePSp_G n F * e := rckRPfss_transpose_mul_G hadj
  have horth : ∀ m m' : (Fin n ⊕ Fin n) → F, ((1 - e) *ᵥ m) ⬝ᵥ
      ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ
        (e *ᵥ m')) = 0 := by
    intro m m'
    have hmat : (1 - e)ᵀ * fePSp_G n F * e = 0 := by
      have h1 : (1 - e)ᵀ = 1 - eᵀ := by rw [Matrix.transpose_sub, Matrix.transpose_one]
      rw [h1, Matrix.sub_mul, Matrix.one_mul, Matrix.sub_mul, heT, Matrix.mul_assoc, he.2.1,
        sub_self]
    have hdot : ∀ (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        (u w : (Fin n ⊕ Fin n) → F), (A *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (Aᵀ *ᵥ w) := by
      intro A u w
      rw [← Matrix.vecMul_transpose A u, ← Matrix.dotProduct_mulVec u Aᵀ w]
    calc ((1 - e) *ᵥ m) ⬝ᵥ (fePSp_G n F *ᵥ (e *ᵥ m'))
        = m ⬝ᵥ ((1 - e)ᵀ *ᵥ (fePSp_G n F *ᵥ (e *ᵥ m'))) := hdot (1 - e) m _
      _ = m ⬝ᵥ (((1 - e)ᵀ * fePSp_G n F * e) *ᵥ m') := by
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      _ = 0 := by
          rw [hmat, Matrix.zero_mulVec]
          simp [dotProduct]
  exact ⟨K, hKf, hKa, hKfin, l, W, hWac, hWF, hWK, hTower, hWfd, σ, βlin, eW, f,
    hdeg, hcard, hσ2, hσne, hσalg, hsymm, hsep, hfinj, hβpres, hisom, hact, hβtrace,
    horth⟩

end CFSG.StandardType.ClassicalPosition
