module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPOmegaPlus
import all CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPOmegaPlus
import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerGroup
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUTypes
import CFSG.ClassicalInvolution.QuaternionStructure
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUnitary

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition

theorem dualPair_star_POmegaPlus (n : ℕ) {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 3 ≤ n) (S : Set (GL (Fin n ⊕ Fin n) F))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus n F)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {ε e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F)))
      (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e) (hne : e ≠ ε) :
    formAdj (RingHom.id F)
        (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F))) e ∈
        Algebra.adjoin F (Units.val '' S) ∧
      IsIdempotentElem (formAdj (RingHom.id F)
        (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F))) e) ∧
      formAdj (RingHom.id F)
        (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F))) e * e = 0 ∧
      e * formAdj (RingHom.id F)
        (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F))) e = 0 ∧
      ε = e + formAdj (RingHom.id F)
        (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F))) e := by
  obtain ⟨h1, h2, -, -, -, h6, h7, h8⟩ :=
    fepomep_dualPair_star n hn S hSU hS (J' := ⊥) hε he heε hne
  exact ⟨h1, h2, h6, h7, h8⟩

theorem exists_blockAction_dualPair_POmegaPlus (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hn : 3 ≤ n) (S : Set (GL (Fin n ⊕ Fin n) F))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus n F)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {ε e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F)))
      (Algebra.adjoin F (Units.val '' S)) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e) (heε : e * ε = e) (hne : e ≠ ε)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin F (Units.val '' S)) e) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : Algebra F K)
      (_ : Module K (LinearMap.range (Matrix.mulVecLin e)))
      (_ : IsScalarTower F K (LinearMap.range (Matrix.mulVecLin e)))
      (ρ : glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε →*
        (LinearMap.range (Matrix.mulVecLin e) ≃ₗ[K] LinearMap.range (Matrix.mulVecLin e))),
      Module.finrank F K = blockDegree (Algebra.adjoin F (Units.val '' S)) e ∧
      Function.Bijective ρ ∧
      ∀ (u : glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S ε)
        (w : LinearMap.range (Matrix.mulVecLin e)),
        ((ρ u w : LinearMap.range (Matrix.mulVecLin e)) : Fin n ⊕ Fin n → F) =
          ((Spin.spinMatrix (Spin.quadPlus n F) (u : ↥(spinGroup (Spin.quadPlus n F))) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)).mulVec (w : Fin n ⊕ Fin n → F) := by
  obtain ⟨K, hKfield, hKalg, hKfin, π, hπsurj, hπker, hπdeg⟩ :=
    exists_blockField (ι := Fin n ⊕ Fin n) hS hodd he
  let := hKfield
  let := hKalg
  have := hKfin
  obtain ⟨W, rfl, hmod, htower, -, -, -, hK⟩ :=
    fepomep_dualPair_blockModule n S hS he K π hπsurj hπker hπdeg
  let := hmod
  let := htower
  obtain ⟨ρ, hρ⟩ :=
    fepomep_dualPair_blockActionHom n hn S hSU hS hε he heε hne hdeg K π hπsurj hπker hπdeg
      (LinearMap.range (Matrix.mulVecLin e)) rfl hK
  have hinj :=
    fepomep_dualPair_blockAction_injective n hn S hSU hS hε he heε hne hdeg K π hπsurj hπker
      hπdeg (LinearMap.range (Matrix.mulVecLin e)) rfl hK ρ hρ
  have hsurj :=
    fepomep_dualPair_blockAction_surjective n hn S hSU hS hε he heε hne hdeg K π hπsurj hπker
      hπdeg (LinearMap.range (Matrix.mulVecLin e)) rfl hK ρ hρ
  exact ⟨K, hKfield, hKfin, hKalg, hmod, htower, ρ, hπdeg, ⟨hinj, hsurj⟩, hρ⟩

theorem exists_blockAction_selfDual_POmegaPlus (n : ℕ) {F : Type} [Field F] [Finite F]
    [CharP F 2] (hn : 3 ≤ n) (f : ℕ) (hc : Nat.card F = 2 ^ f)
    (S : Set (GL (Fin n ⊕ Fin n) F))
    (hSU : ∀ s ∈ S, s ∈ (Spin.spinMatrix (Spin.quadPlus n F)).range)
    (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (Spin.quadPlus n F))}
    {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (hε : IsPrimAdjIdemIn (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadPlus n F)))
      (Algebra.adjoin F (Units.val '' S)) e)
    (hJε : IsComponentOf J'
      ⁅glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S e,
        glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S e⁆)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hdeg : 4 ≤ blockDegree (Algebra.adjoin F (Units.val '' S)) e) :
    ∃ (l : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : Algebra F K)
      (_ : Module K (LinearMap.range (Matrix.mulVecLin e)))
      (_ : IsScalarTower F K (LinearMap.range (Matrix.mulVecLin e)))
      (τ : K ≃+* K)
      (ρ : glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S e →*
        (LinearMap.range (Matrix.mulVecLin e) ≃ₗ[K] LinearMap.range (Matrix.mulVecLin e)))
      (H : LinearMap.range (Matrix.mulVecLin e) →ₛₗ[τ.toRingHom]
        LinearMap.range (Matrix.mulVecLin e) →ₗ[K] K),
      blockDegree (Algebra.adjoin F (Units.val '' S)) e = 2 * l ∧ 2 ≤ l ∧
      Module.finrank F K = blockDegree (Algebra.adjoin F (Units.val '' S)) e ∧
      (∀ x : K, τ x = x ^ (2 ^ (l * f))) ∧ τ ^ 2 = 1 ∧ τ ≠ 1 ∧
      (∀ a : F, τ (algebraMap F K a) = algebraMap F K a) ∧ Function.Injective ρ ∧
      (∀ (u : glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S e)
        (w : LinearMap.range (Matrix.mulVecLin e)),
        ((ρ u w : LinearMap.range (Matrix.mulVecLin e)) : Fin n ⊕ Fin n → F) =
          ((Spin.spinMatrix (Spin.quadPlus n F) (u : ↥(spinGroup (Spin.quadPlus n F))) :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)).mulVec (w : Fin n ⊕ Fin n → F)) ∧
      H.IsSymm ∧ H.SeparatingLeft ∧
      (∀ v w : LinearMap.range (Matrix.mulVecLin e), Algebra.trace F K (H v w) =
        QuadraticMap.polar (Spin.quadPlus n F) (v : Fin n ⊕ Fin n → F)
          (w : Fin n ⊕ Fin n → F)) ∧
      (∀ (u : glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S e)
        (x y : LinearMap.range (Matrix.mulVecLin e)), H (ρ u x) (ρ u y) = H x y) ∧
      ∀ g : LinearMap.range (Matrix.mulVecLin e) ≃ₗ[K] LinearMap.range (Matrix.mulVecLin e),
        (∀ x y, H (g x) (g y) = H x y) →
          ∃ u : glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus n F)) S e, ρ u = g := by
  obtain ⟨K, hKfield, hKalg, hKfin, π, hπsurj, hπker, hπdeg⟩ :=
    exists_blockField (ι := Fin n ⊕ Fin n) hS hodd he
  let := hKfield
  let := hKalg
  have := hKfin
  let π' : fepomepA n F S →ₐ[F] K := π
  have heε : e * e = e := he.2.1
  obtain ⟨l, hl, hl2, τ, hτcompat, hτ2, hτne⟩ :=
    fepomep_selfDual_hermitian n hn f hc S hSU hS hodd hε he heε rfl hdeg K π' hπsurj hπker
      hπdeg
  obtain ⟨W, rfl, hmod, htower, hfin, -, -, hK⟩ :=
    fepomep_selfDual_blockModule n hn S hSU hS hε he heε rfl K π' hπsurj hπker hπdeg
  let := hmod
  let := htower
  have := hfin
  obtain ⟨ρ, hρ⟩ :=
    fepomep_selfDual_blockActionHom n hn S hSU hS hε he heε rfl (by omega) K π' hπsurj hπker
      hπdeg (LinearMap.range (Matrix.mulVecLin e)) rfl hK
  obtain ⟨Φ⟩ :=
    fepomep_selfDual_moduleMatrixEquiv n hn S hSU hS he K
      (LinearMap.range (Matrix.mulVecLin e)) rfl
  have hinjρ :=
    fepomep_selfDual_blockAction_injective n hn S hSU hS hε he heε rfl (by omega) K π' hπsurj
      hπker hπdeg (LinearMap.range (Matrix.mulVecLin e)) rfl hK ρ hρ
  have hτF : ∀ a : F, τ (algebraMap F K a) = algebraMap F K a := by
    intro a
    have hπa : π' (algebraMap F (fepomepA n F S) a) = algebraMap F K a := π'.commutes a
    have hφa : fepomep_formAdjAlgEquiv n hn S hSU hS (algebraMap F (fepomepA n F S) a) =
        algebraMap F (fepomepA n F S) a :=
      (fepomep_formAdjAlgEquiv n hn S hSU hS).commutes a
    have h := hτcompat (algebraMap F (fepomepA n F S) a)
    rw [hπa, hφa, hπa] at h
    exact h
  have hdegK : Module.finrank F K = 2 * l := hπdeg.trans hl
  have hτeq : ∀ x : K, τ x = x ^ (2 ^ (l * f)) :=
    fepomep_selfDual_tau_eq_frobenius f hc l hl2 hdegK τ hτF hτ2 hτne
  obtain ⟨H, hHsymm, hHnd, hHtr, hHinv⟩ :=
    fepomep_selfDual_blockGroup_descentHermitianForm n hn f hc S hSU hS hodd hε hJε he heε
      rfl hdeg l hl hl2 K π' hπsurj hπker hπdeg τ hτcompat hτ2 hτne
      (LinearMap.range (Matrix.mulVecLin e)) rfl ρ hρ hK Φ
  obtain ⟨ι₀, -, hι₀⟩ :=
    fepomep_selfDual_blockGroup_descentCoordinateMap n hn f hc S hSU hS hodd hε hJε he heε
      rfl hdeg l hl hl2 K π' hπsurj hπker hπdeg τ hτcompat hτ2 hτne
      (LinearMap.range (Matrix.mulVecLin e)) rfl hK ρ hρ hinjρ Φ
  exact ⟨l, K, hKfield, hKfin, hKalg, hmod, htower, τ, ρ, H, hl, hl2, hπdeg, hτeq, hτ2, hτne,
    hτF, hinjρ, hρ, hHsymm, hHnd, hHtr, hHinv,
    fun g hg =>
      fepomep_selfDual_blockGroup_descentHIsometrySurjective n hn f hc S hSU hS hodd hε hJε
        he heε rfl hdeg l hl hl2 K π' hπsurj hπker hπdeg τ hτcompat hτ2 hτne
        (LinearMap.range (Matrix.mulVecLin e)) rfl ρ hρ hK Φ hinjρ H hHinv hHtr ι₀ hι₀ hτeq g
        hg⟩

end CFSG.StandardType.RCKRP
