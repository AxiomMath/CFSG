module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPOmegaMinus
import all CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPOmegaMinus
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerGroup
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUTypes
import CFSG.ClassicalInvolution.QuaternionStructure
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUnitary

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition

theorem exists_blockAction_selfDual_POmegaMinus (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] {bq cq : F}
    (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n) (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadMinus n F bq cq)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (Spin.quadMinus n F bq cq))}
    {e : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq)))
      (Algebra.adjoin F (Units.val '' S)) e)
    (hJε : IsComponentOf J'
      ⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq)) S e,
        glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq)) S e⁆)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hdeg : 4 ≤ blockDegree (Algebra.adjoin F (Units.val '' S)) e) :
    ∃ (l : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : Algebra F K)
      (_ : Module K (LinearMap.range (Matrix.mulVecLin e)))
      (_ : IsScalarTower F K (LinearMap.range (Matrix.mulVecLin e)))
      (τ : K ≃+* K)
      (ρ : glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq)) S e →*
        (LinearMap.range (Matrix.mulVecLin e) ≃ₗ[K] LinearMap.range (Matrix.mulVecLin e)))
      (H : LinearMap.range (Matrix.mulVecLin e) →ₛₗ[τ.toRingHom]
        LinearMap.range (Matrix.mulVecLin e) →ₗ[K] K),
      blockDegree (Algebra.adjoin F (Units.val '' S)) e = 2 * l ∧ 2 ≤ l ∧
      Module.finrank F K = blockDegree (Algebra.adjoin F (Units.val '' S)) e ∧
      (∀ x : K, τ x = x ^ (2 ^ (l * f))) ∧ τ ^ 2 = 1 ∧ τ ≠ 1 ∧
      (∀ a : F, τ (algebraMap F K a) = algebraMap F K a) ∧ Function.Injective ρ ∧
      (∀ (u : glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq)) S e)
        (w : LinearMap.range (Matrix.mulVecLin e)),
        ((ρ u w : LinearMap.range (Matrix.mulVecLin e)) : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F) =
          ((Spin.spinMatrix (Spin.quadMinus n F bq cq)
              (u : ↥(spinGroup (Spin.quadMinus n F bq cq))) :
            Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2)
              F)).mulVec (w : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F)) ∧
      H.IsSymm ∧ H.SeparatingLeft ∧
      (∀ v w : LinearMap.range (Matrix.mulVecLin e), Algebra.trace F K (H v w) =
        QuadraticMap.polar (Spin.quadMinus n F bq cq) (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F)
          (w : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → F)) ∧
      (∀ (u : glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq)) S e)
        (x y : LinearMap.range (Matrix.mulVecLin e)), H (ρ u x) (ρ u y) = H x y) ∧
      ∀ g : LinearMap.range (Matrix.mulVecLin e) ≃ₗ[K] LinearMap.range (Matrix.mulVecLin e),
        (∀ x y, H (g x) (g y) = H x y) →
          ∃ u : glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq)) S e, ρ u = g := by
  obtain ⟨K, hKfield, hKalg, hKfin, π, hπsurj, hπker, hπdeg⟩ :=
    exists_blockField (ι := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) hS hodd he
  let := hKfield
  let := hKalg
  have := hKfin
  let π' : fepomeA n F S →ₐ[F] K := π
  have heε : e * e = e := he.2.1
  obtain ⟨l, hl, hl2, τ, hτcompat, hτ2, hτne⟩ :=
    fepome_selfDual_hermitian n hirr hn f hc S hSU hS hodd hε he heε rfl hdeg K π' hπsurj hπker
      hπdeg
  obtain ⟨W, rfl, hmod, htower, hfin, -, -, hK⟩ :=
    fepome_selfDual_blockModule n hirr hn S hSU hS hε he heε rfl K π' hπsurj hπker hπdeg
  let := hmod
  let := htower
  have := hfin
  obtain ⟨ρ, hρ⟩ :=
    fepome_selfDual_blockActionHom n hirr hn S hSU hS hε he heε rfl (by omega) K π' hπsurj hπker
      hπdeg (LinearMap.range (Matrix.mulVecLin e)) rfl hK
  obtain ⟨Φ⟩ :=
    fepome_selfDual_moduleMatrixEquiv n hirr hn S hSU hS he K
      (LinearMap.range (Matrix.mulVecLin e)) rfl
  have hinjρ :=
    fepome_selfDual_blockAction_injective n hirr hn S hSU hS hε he heε rfl (by omega) K π' hπsurj
      hπker hπdeg (LinearMap.range (Matrix.mulVecLin e)) rfl hK ρ hρ
  have hτF : ∀ a : F, τ (algebraMap F K a) = algebraMap F K a := by
    intro a
    have hπa : π' (algebraMap F (fepomeA n F S) a) = algebraMap F K a := π'.commutes a
    have hφa : fepome_formAdjAlgEquiv n hirr hn S hSU hS (algebraMap F (fepomeA n F S) a) =
        algebraMap F (fepomeA n F S) a :=
      (fepome_formAdjAlgEquiv n hirr hn S hSU hS).commutes a
    have h := hτcompat (algebraMap F (fepomeA n F S) a)
    rw [hπa, hφa, hπa] at h
    exact h
  have hdegK : Module.finrank F K = 2 * l := hπdeg.trans hl
  have hτeq : ∀ x : K, τ x = x ^ (2 ^ (l * f)) :=
    fepome_selfDual_tau_eq_frobenius f hc l hl2 hdegK τ hτF hτ2 hτne
  obtain ⟨H, hHsymm, hHnd, hHtr, hHinv⟩ :=
    fepome_selfDual_blockGroup_descentHermitianForm n hirr hn f hc S hSU hS hodd hε hJε he heε
      rfl hdeg l hl hl2 K π' hπsurj hπker hπdeg τ hτcompat hτ2 hτne
      (LinearMap.range (Matrix.mulVecLin e)) rfl ρ hρ hK Φ
  obtain ⟨ι₀, -, hι₀⟩ :=
    fepome_selfDual_blockGroup_descentCoordinateMap n hirr hn f hc S hSU hS hodd hε hJε he heε
      rfl hdeg l hl hl2 K π' hπsurj hπker hπdeg τ hτcompat hτ2 hτne
      (LinearMap.range (Matrix.mulVecLin e)) rfl hK ρ hρ hinjρ Φ
  exact ⟨l, K, hKfield, hKfin, hKalg, hmod, htower, τ, ρ, H, hl, hl2, hπdeg, hτeq, hτ2, hτne,
    hτF, hinjρ, hρ, hHsymm, hHnd, hHtr, hHinv,
    fun g hg =>
      fepome_selfDual_blockGroup_descentHIsometrySurjective n hirr hn f hc S hSU hS hodd hε hJε
        he heε rfl hdeg l hl hl2 K π' hπsurj hπker hπdeg τ hτcompat hτ2 hτne
        (LinearMap.range (Matrix.mulVecLin e)) rfl ρ hρ hK Φ hinjρ H hHinv hHtr ι₀ hι₀ hτeq g
        hg⟩

end CFSG.StandardType.RCKRP
