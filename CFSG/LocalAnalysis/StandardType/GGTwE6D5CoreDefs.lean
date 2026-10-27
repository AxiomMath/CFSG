module

public import CFSG.LocalAnalysis.StandardType.GGTwE6RootAsCoreDefs

public section

namespace CFSG.StandardType.TwE6RootAs

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


@[expose] def TwE6D5Core : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (q : ℕ), Nat.card K = q ^ 2 →
    (∀ c, σ c = c ^ q) → ringChar K = 2 → 3 ∣ q + 1 →
    ∀ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ q) →
    ∀ v : WeylGroup TwistTag.E6.tag,
      (∀ γ : Fin TwistTag.E6.tag.rank → ℤ, v • permLattice TwistTag.E6.perm γ = -γ) →
    ∀ g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K),
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v →
    ∀ t ∈ twistedE6InndiagGL K σ,
    ∀ a : Fin TwistTag.E6.tag.rank → (AlgebraicClosure K)ˣ, (∀ k, a k ^ 3 = 1) →
      Set.ncard {α : Fin TwistTag.E6.tag.rank → ℤ |
        IsRoot TwistTag.E6.tag α ∧ rootChar a α = 1} = 40 →
      g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) t * g0 =
        rootDiagUnit TwistTag.E6.tag a →
      ∃ X D : Subgroup ↥(twistedE6RootGroup K σ),
        (Subgroup.centralizer ({t} : Set (ModGL TwistTag.E6.tag K))).subgroupOf
            (twistedE6RootGroup K σ) = X ⊔ D ∧
          IsCyclic X ∧ X ≤ Subgroup.centralizer (D : Set _) ∧ CFSG.IsQuasisimple D

end CFSG.StandardType.TwE6RootAs

end
