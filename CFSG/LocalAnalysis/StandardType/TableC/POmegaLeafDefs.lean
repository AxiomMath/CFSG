module

public import CFSG.LocalAnalysis.StandardType.TableC.Extract
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LieType.Universal.Spin.Action
public import CFSG.LieType.Universal.Spin.Forms

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal
open CFSG.StandardType.ClassicalPosition

section POmegaLeaves

@[expose] def GGSixTCLiftPOmegaPlus
    : Prop :=
  ∀ {X : Type} [Group X] [Finite X] (k f : ℕ) (ψ : (ggU .POmegaPlus (k + 3) f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X), GGSixTCPos .POmegaPlus (k + 3) f ψ p G₀ B₁ D J L x →
    ∃ ℓ : ↥D →* spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f)),
      (∀ d : ↥D, IsGLLift (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))) ψ
        (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) (ℓ d)) (d : X)) ∧
      (∀ d : ↥D, ℓ d ^ p = 1) ∧
      ∃ J' : Subgroup (spinGroup (Spin.quadPlus (k + 3) (GaloisField 2 f))),
        IsComponentOf J' ((Subgroup.centralizer (Set.range fun d : ↥D =>
          Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) (ℓ d))).comap
            (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)))) ∧ J'.map ψ = J

@[expose] def GGSixTCLiftPOmegaMinus
    : Prop :=
  ∀ {X : Type} [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .POmegaMinus n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X), GGSixTCPos .POmegaMinus n f ψ p G₀ B₁ D J L x →
    ∃ ℓ : ↥D →* spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
        (minusCoeffs 2 f).2),
      (∀ d : ↥D, IsGLLift (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
          (minusCoeffs 2 f).2)) ψ
        (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
          (minusCoeffs 2 f).2) (ℓ d)) (d : X)) ∧
      (∀ d : ↥D, ℓ d ^ p = 1) ∧
      ∃ J' : Subgroup (spinGroup (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
          (minusCoeffs 2 f).2)),
        IsComponentOf J' ((Subgroup.centralizer (Set.range fun d : ↥D =>
          Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
            (minusCoeffs 2 f).2) (ℓ d))).comap
            (Spin.spinMatrix (Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1
              (minusCoeffs 2 f).2))) ∧ J'.map ψ = J

@[expose, reducible] def ggOmIdxPlus (k : ℕ) : Type := Fin (k + 3) ⊕ Fin (k + 3)

@[expose, reducible] def ggOmIdxMinus (n : ℕ) : Type := Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2

@[expose, reducible] noncomputable def ggOmQuadPlus (k f : ℕ) :
    QuadraticForm (GaloisField 2 f) (Fin (k + 3) ⊕ Fin (k + 3) → GaloisField 2 f) :=
  Spin.quadPlus (k + 3) (GaloisField 2 f)

@[expose, reducible] noncomputable def ggOmQuadMinus (n f : ℕ) :
    QuadraticForm (GaloisField 2 f) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → GaloisField 2 f) :=
  Spin.quadMinus n (GaloisField 2 f) (minusCoeffs 2 f).1 (minusCoeffs 2 f).2

@[expose, reducible] noncomputable def ggOmSpinPlus (k f : ℕ) :
    spinGroup (ggOmQuadPlus k f) →* GL (ggOmIdxPlus k) (GaloisField 2 f) :=
  Spin.spinMatrix (ggOmQuadPlus k f)

@[expose, reducible] noncomputable def ggOmSpinMinus (n f : ℕ) :
    spinGroup (ggOmQuadMinus n f) →* GL (ggOmIdxMinus n) (GaloisField 2 f) :=
  Spin.spinMatrix (ggOmQuadMinus n f)

@[expose] def GGSixTCBlockDegPOmegaPlus : Prop :=
  ∀ (k f : ℕ) (_ : 1 ≤ k) (_ : 1 ≤ f) {X : Type} [Group X] [Finite X]
    (ψ : ↥(spinGroup (ggOmQuadPlus k f)) →* X) (_ : ψ.ker ≤ Subgroup.center _)
    (S : Set (GL (ggOmIdxPlus k) (GaloisField 2 f))) (_ : ∀ s ∈ S, s ∈ (ggOmSpinPlus k f).range)
    (_ : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (_ : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (ggOmQuadPlus k f))}
    {ε e : Matrix (ggOmIdxPlus k) (ggOmIdxPlus k) (GaloisField 2 f)}
    (_ : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin (ggOmQuadPlus k f)))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (_ : IsComponentOf J'
      ⁅glBlockCentralizer (ggOmSpinPlus k f) S ε, glBlockCentralizer (ggOmSpinPlus k f) S ε⁆)
    (_ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) (_ : e * ε = e)
    (_ : GGSixLSevenFieldExtCase (J'.map ψ) .POmegaPlus f),
    (e = ε ∧ 4 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) ∨
      (e ≠ ε ∧ 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) ∨
      (e = ε ∧ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e = 1 ∧
        Matrix.rank e = 4)

@[expose] def GGSixTCCaseAPOmegaPlus
    : Prop :=
  ∀ {X : Type} [Group X] [Finite X] (k f : ℕ) (ψ : (ggU .POmegaPlus (k + 3) f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X), GGSixTCPos .POmegaPlus (k + 3) f ψ p G₀ B₁ D J L x →
    ∀ (ℓ : ↥D →* spinGroup (ggOmQuadPlus k f)) (S : Set (GL (ggOmIdxPlus k) (GaloisField 2 f))),
      S = Set.range (fun d : ↥D => ggOmSpinPlus k f (ℓ d)) →
      (∀ d : ↥D, IsGLLift (ggOmSpinPlus k f) ψ (ggOmSpinPlus k f (ℓ d)) (d : X)) →
      (∀ d : ↥D, ℓ d ^ p = 1) →
      ∀ (J' : Subgroup (spinGroup (ggOmQuadPlus k f)))
        (e : Matrix (ggOmIdxPlus k) (ggOmIdxPlus k) (GaloisField 2 f)),
        IsComponentOf J' ((Subgroup.centralizer S).comap (ggOmSpinPlus k f)) → J'.map ψ = J →
        GGSixLSevenFieldExtCase (J'.map ψ) .POmegaPlus f →
        IsComponentOf J'
          ⁅glBlockCentralizer (ggOmSpinPlus k f) S e, glBlockCentralizer (ggOmSpinPlus k f) S e⁆ →
        IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e →
        (∀ s ∈ S, (s : Matrix (ggOmIdxPlus k) (ggOmIdxPlus k) (GaloisField 2 f)) * e = e) →
        Matrix.rank e = 4 → False

@[expose] def GGSixTCBlockDegPOmegaMinus : Prop :=
  ∀ (n f : ℕ) (_ : 4 ≤ n) (_ : 1 ≤ f) {X : Type} [Group X] [Finite X]
    (ψ : ↥(spinGroup (ggOmQuadMinus n f)) →* X) (_ : ψ.ker ≤ Subgroup.center _)
    (S : Set (GL (ggOmIdxMinus n) (GaloisField 2 f))) (_ : ∀ s ∈ S, s ∈ (ggOmSpinMinus n f).range)
    (_ : ∀ s ∈ S, ∀ s' ∈ S, Commute s s') (_ : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup ↥(spinGroup (ggOmQuadMinus n f))}
    {ε e : Matrix (ggOmIdxMinus n) (ggOmIdxMinus n) (GaloisField 2 f)}
    (_ : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (LinearMap.toMatrix₂' (GaloisField 2 f) (QuadraticMap.polarBilin (ggOmQuadMinus n f)))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (_ : IsComponentOf J'
      ⁅glBlockCentralizer (ggOmSpinMinus n f) S ε, glBlockCentralizer (ggOmSpinMinus n f) S ε⁆)
    (_ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) (_ : e * ε = e)
    (_ : GGSixLSevenFieldExtCase (J'.map ψ) .POmegaMinus f),
    (e = ε ∧ 4 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) ∨
      (e ≠ ε ∧ 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) ∨
      (e = ε ∧ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e = 1 ∧
        Matrix.rank e = 4)

@[expose] def GGSixTCCaseAPOmegaMinus
    : Prop :=
  ∀ {X : Type} [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .POmegaMinus n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X), GGSixTCPos .POmegaMinus n f ψ p G₀ B₁ D J L x →
    ∀ (ℓ : ↥D →* spinGroup (ggOmQuadMinus n f)) (S : Set (GL (ggOmIdxMinus n) (GaloisField 2 f))),
      S = Set.range (fun d : ↥D => ggOmSpinMinus n f (ℓ d)) →
      (∀ d : ↥D, IsGLLift (ggOmSpinMinus n f) ψ (ggOmSpinMinus n f (ℓ d)) (d : X)) →
      (∀ d : ↥D, ℓ d ^ p = 1) →
      ∀ (J' : Subgroup (spinGroup (ggOmQuadMinus n f)))
        (e : Matrix (ggOmIdxMinus n) (ggOmIdxMinus n) (GaloisField 2 f)),
        IsComponentOf J' ((Subgroup.centralizer S).comap (ggOmSpinMinus n f)) → J'.map ψ = J →
        GGSixLSevenFieldExtCase (J'.map ψ) .POmegaMinus f →
        IsComponentOf J'
          ⁅glBlockCentralizer (ggOmSpinMinus n f) S e, glBlockCentralizer (ggOmSpinMinus n f) S e⁆ →
        IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e →
        (∀ s ∈ S, (s : Matrix (ggOmIdxMinus n) (ggOmIdxMinus n) (GaloisField 2 f)) * e = e) →
        Matrix.rank e = 4 → False

end POmegaLeaves

end CFSG.StandardType

end
