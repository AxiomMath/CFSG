module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPSp
import all CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPSp

public section

namespace CFSG.StandardType.ClassicalPosition

open scoped Matrix

theorem exists_blockAction_dualPair_PSp {n f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hc : Nat.card F = 2 ^ f) {S : Set (GL (Fin n ⊕ Fin n) F)}
    (hSU : ∀ s ∈ S, s ∈ CFSG.Open.StatedSp n F) (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s)) {e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F}
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' S)) e)
    (hpair : formAdj (RingHom.id F)
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) e ≠ e) :
    ∃ (K : Type) (_ : Field K) (_ : Algebra F K) (_ : Finite K)
      (W : Type) (_ : AddCommGroup W) (_ : Module F W) (_ : Module K W)
      (_ : IsScalarTower F K W) (_ : FiniteDimensional K W)
      (eW : W ≃ₗ[F] LinearMap.range (Matrix.toLin' e))
      (φ : ↥(glBlockCentralizer (CFSG.Open.StatedSp n F).subtype S
          (e + formAdj (RingHom.id F)
            (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) e)) ≃*
        (W ≃ₗ[K] W)),
      Nat.card K = 2 ^ (blockDegree (Algebra.adjoin F (Units.val '' S)) e * f) ∧
      (∀ g w, (eW (φ g w) : (Fin n ⊕ Fin n) → F) =
        (((g : ↥(CFSG.Open.StatedSp n F)) : GL (Fin n ⊕ Fin n) F) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ (eW w : (Fin n ⊕ Fin n) → F)) ∧
      ∀ g : ↥(glBlockCentralizer (CFSG.Open.StatedSp n F).subtype S
          (e + formAdj (RingHom.id F)
            (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) e)),
        (((g : ↥(CFSG.Open.StatedSp n F)) : GL (Fin n ⊕ Fin n) F) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * e =
        e * (((g : ↥(CFSG.Open.StatedSp n F)) : GL (Fin n ⊕ Fin n) F) :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
  obtain ⟨K, hKf, hKa, hKfin, hcard, π, hπ, hker, hfin⟩ :=
    fePSp_dualPair_blockField hc hS hodd he
  letI : Field K := hKf
  letI : Algebra F K := hKa
  haveI : Finite K := hKfin
  obtain ⟨W, hWac, hWF, hWK, hTower, hWfd, -, eW, hact, -, -⟩ :=
    fePSp_dualPair_blockExists hS he K π hπ hker hfin
  letI : AddCommGroup W := hWac
  letI : Module F W := hWF
  letI : Module K W := hWK
  haveI : IsScalarTower F K W := hTower
  obtain ⟨ρ, hρ⟩ := fePSp_dualPair_blockRestrict_exists he K π hπ W eW hact
  exact ⟨K, hKf, hKa, hKfin, W, hWac, hWF, hWK, hTower, hWfd, eW,
    MulEquiv.ofBijective ρ ⟨fePSp_dualPair_blockRestrict_injective hSU he K W eW ρ hρ,
      fePSp_dualPair_blockRestrict_surjective hS hSU he hpair K π W eW hact ρ hρ⟩, hcard,
    fun g w => hρ g w, fun g => fePSp_dualPair_blockActionCompat g e he.1⟩

end CFSG.StandardType.ClassicalPosition
