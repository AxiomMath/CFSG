module

public import CFSG.LocalAnalysis.StandardType.TableC.Extract
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockDegreeParity
public import CFSG.Open.StatedDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.Open (StatedSp)
open CFSG.StandardType.ClassicalPosition

section PSpLeaves

@[expose] def GGSixTCLiftPSp
    : Prop :=
  ∀ {X : Type} [Group X] [Finite X] (n f : ℕ) (ψ : (ggU .PSp n f).K →* X) (p : ℕ)
    (G₀ B₁ D J L : Subgroup X) (x : X), GGSixTCPos .PSp n f ψ p G₀ B₁ D J L x →
    ∃ ℓ : ↥D →* ↥(StatedSp n (GaloisField 2 f)),
      (∀ d : ↥D, IsGLLift (StatedSp n (GaloisField 2 f)).subtype ψ
        (ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) (d : X)) ∧
      (∀ d : ↥D, (ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f)) ^ p = 1) ∧
      ∃ J' : Subgroup ↥(StatedSp n (GaloisField 2 f)),
        IsComponentOf J' ((Subgroup.centralizer (Set.range fun d : ↥D =>
          (ℓ d : GL (Fin n ⊕ Fin n) (GaloisField 2 f)))).comap
            (StatedSp n (GaloisField 2 f)).subtype) ∧ J'.map ψ = J

@[expose] def GGSixTCBlockDegPSp
    : Prop :=
  ∀ (n f : ℕ) (_ : 1 ≤ n) (_ : 1 ≤ f) {X : Type} [Group X] [Finite X]
    (ψ : ↥(StatedSp n (GaloisField 2 f)) →* X) (_ : ψ.ker ≤ Subgroup.center _)
    (S : Set (GL (Fin n ⊕ Fin n) (GaloisField 2 f)))
    (_ : ∀ s ∈ S, s ∈ StatedSp n (GaloisField 2 f)) (_ : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (_ : ∀ s ∈ S, Odd (orderOf s)) {J' : Subgroup ↥(StatedSp n (GaloisField 2 f))}
    {ε e : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)}
    (_ : IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
      (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) ε)
    (_ : IsComponentOf J'
      ⁅glBlockCentralizer (StatedSp n (GaloisField 2 f)).subtype S ε, glBlockCentralizer
      (StatedSp n (GaloisField 2 f)).subtype S ε⁆)
    (_ : IsPrimIdemIn (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) (_ : e * ε = e)
    (_ : GGSixLSevenFieldExtCase (J'.map ψ) .PSp f),
    (e = ε ∧ 4 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e) ∨
      (e ≠ ε ∧ 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e)

end PSpLeaves

end CFSG.StandardType

end
