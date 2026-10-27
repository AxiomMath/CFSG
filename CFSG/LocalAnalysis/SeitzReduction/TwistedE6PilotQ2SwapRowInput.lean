module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR6X
public import CFSG.LocalAnalysis.SeitzReduction.HypothesisOneTwistedE6TwoBasic
public import CFSG.Quasithin.Background.A3ComponentsBasic

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi
open CFSG.Quasithin (perfectCore)


@[expose] def TwistedE6TwoTriangleInput : Prop :=
  ∀ (k K : Type) [Field k] [Field K] [Algebra k K], Nat.card k = 2 ^ 1 →
    Nat.card K = (2 ^ 1) ^ 2 → ∀ σ : K →+* K, (∀ c, σ c = c ^ 2 ^ 1) →
    ∀ A : Subgroup (ModGL TwistTag.E6.tag K), A ≤ thetaRankOneGroup (algebraMap k K) →
      Nat.card A = 2 ^ 1 + 1 → IsCyclic A →
      ∃ (n₂ n₃ : graphFixedRootGroup TwistTag.E6 K σ) (q q' : ModGL TwistTag.E6.tag K),
        A.map (MulAut.conj (n₂ : ModGL TwistTag.E6.tag K)).toMonoidHom ≤ su6Levi σ ∧
        A.map (MulAut.conj (n₃ : ModGL TwistTag.E6.tag K)).toMonoidHom ≤ su6Levi σ ∧
        A ≤ (su6Levi σ).map (MulAut.conj (n₂ : ModGL TwistTag.E6.tag K)).toMonoidHom ∧
        A.map (MulAut.conj (n₃ : ModGL TwistTag.E6.tag K)).toMonoidHom ≤
          (su6Levi σ).map (MulAut.conj (n₂ : ModGL TwistTag.E6.tag K)).toMonoidHom ∧
        A ≤ (su6Levi σ).map (MulAut.conj (n₃ : ModGL TwistTag.E6.tag K)).toMonoidHom ∧
        A.map (MulAut.conj (n₂ : ModGL TwistTag.E6.tag K)).toMonoidHom ≤
          (su6Levi σ).map (MulAut.conj (n₃ : ModGL TwistTag.E6.tag K)).toMonoidHom ∧
        IsSimpleGroup (perfectCore (su6Levi σ ⊓ centralizer
          (A.map (MulAut.conj (n₂ : ModGL TwistTag.E6.tag K)).toMonoidHom :
            Set (ModGL TwistTag.E6.tag K)))) ∧
        IsSimpleGroup (perfectCore (su6Levi σ ⊓ centralizer
          (A.map (MulAut.conj (n₃ : ModGL TwistTag.E6.tag K)).toMonoidHom :
            Set (ModGL TwistTag.E6.tag K)))) ∧
        IsSimpleGroup (perfectCore
          ((su6Levi σ).map (MulAut.conj (n₂ : ModGL TwistTag.E6.tag K)).toMonoidHom ⊓
            centralizer (A.map (MulAut.conj (n₃ : ModGL TwistTag.E6.tag K)).toMonoidHom :
              Set (ModGL TwistTag.E6.tag K)))) ∧
        q ∈ perfectCore (su6Levi σ ⊓ centralizer
          (A.map (MulAut.conj (n₂ : ModGL TwistTag.E6.tag K)).toMonoidHom :
            Set (ModGL TwistTag.E6.tag K))) ∧
        q ∈ perfectCore (su6Levi σ ⊓ centralizer
          (A.map (MulAut.conj (n₃ : ModGL TwistTag.E6.tag K)).toMonoidHom :
            Set (ModGL TwistTag.E6.tag K))) ∧
        q ∈ perfectCore
          ((su6Levi σ).map (MulAut.conj (n₂ : ModGL TwistTag.E6.tag K)).toMonoidHom ⊓
            centralizer (A.map (MulAut.conj (n₃ : ModGL TwistTag.E6.tag K)).toMonoidHom :
              Set (ModGL TwistTag.E6.tag K))) ∧
        q' ∈ perfectCore (su6Levi σ ⊓ centralizer
          (A.map (MulAut.conj (n₂ : ModGL TwistTag.E6.tag K)).toMonoidHom :
            Set (ModGL TwistTag.E6.tag K))) ∧
        q' ∈ perfectCore (su6Levi σ ⊓ centralizer
          (A.map (MulAut.conj (n₃ : ModGL TwistTag.E6.tag K)).toMonoidHom :
            Set (ModGL TwistTag.E6.tag K))) ∧
        q' ∈ perfectCore
          ((su6Levi σ).map (MulAut.conj (n₂ : ModGL TwistTag.E6.tag K)).toMonoidHom ⊓
            centralizer (A.map (MulAut.conj (n₃ : ModGL TwistTag.E6.tag K)).toMonoidHom :
              Set (ModGL TwistTag.E6.tag K))) ∧
        q * q' ≠ q' * q ∧
        graphFixedRootGroup TwistTag.E6 K σ ≤
          perfectCore (su6Levi σ ⊓ centralizer
            (A.map (MulAut.conj (n₂ : ModGL TwistTag.E6.tag K)).toMonoidHom :
              Set (ModGL TwistTag.E6.tag K))) ⊔
          perfectCore (su6Levi σ ⊓ centralizer
            (A.map (MulAut.conj (n₃ : ModGL TwistTag.E6.tag K)).toMonoidHom :
              Set (ModGL TwistTag.E6.tag K))) ⊔
          perfectCore
            ((su6Levi σ).map (MulAut.conj (n₂ : ModGL TwistTag.E6.tag K)).toMonoidHom ⊓
              centralizer (A.map (MulAut.conj (n₃ : ModGL TwistTag.E6.tag K)).toMonoidHom :
                Set (ModGL TwistTag.E6.tag K)))

section Overlaps

variable {K : Type} [Field K]

@[expose] noncomputable def rootRankOneGroup {k : Type} [Field k] (ι : k →+* K)
    (δ : Fin TwistTag.E6.tag.rank → ℤ) : Subgroup (ModGL TwistTag.E6.tag K) :=
  closure (Set.range fun c : k => pinnedX TwistTag.E6.tag K δ (ι c)) ⊔
    closure (Set.range fun c : k => pinnedX TwistTag.E6.tag K (-δ) (ι c))

@[expose] def perpFixedRoots : List (Fin TwistTag.E6.tag.rank → ℤ) :=
  [![1, 0, 1, 1, 1, 1], ![0, 0, 1, 1, 1, 0], ![0, 0, 0, 1, 0, 0]]

end Overlaps

@[expose] def TwistedE6TwoOverlapFacts : Prop :=
  ∀ (k K : Type) [Field k] [Field K] [Algebra k K], Nat.card k = 2 ^ 1 →
    Nat.card K = (2 ^ 1) ^ 2 → ∀ σ : K →+* K, (∀ c, σ c = c ^ 2 ^ 1) →
    ∀ δ ∈ perpFixedRoots, ∀ Y : Subgroup (ModGL TwistTag.E6.tag K),
      Y ≤ rootRankOneGroup (algebraMap k K) δ → Nat.card Y = 3 →
      IsSimpleGroup (perfectCore (su6Levi σ ⊓ centralizer (Y : Set (ModGL TwistTag.E6.tag K)))) ∧
      ∀ β : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag β →
        CFSG.LieType.Steinberg.Adjoint.iform e6HighestRoot β = 0 →
        CFSG.LieType.Steinberg.Adjoint.iform δ β = 0 →
        (permLattice TwistTag.E6.perm β = β → ∀ s : K, σ s = s →
          pinnedX TwistTag.E6.tag K β s ∈
            perfectCore (su6Levi σ ⊓ centralizer (Y : Set (ModGL TwistTag.E6.tag K))))  ∧
        (permLattice TwistTag.E6.perm β ≠ β → ∀ s : K,
          twistedE6PairX σ β s ∈
            perfectCore (su6Levi σ ⊓ centralizer (Y : Set (ModGL TwistTag.E6.tag K))))

end CFSG.SeitzReduction.TwistedE6Pilot
