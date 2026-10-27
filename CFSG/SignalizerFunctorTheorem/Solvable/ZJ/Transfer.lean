module

public import CFSG.LocalAnalysis.SignalizerFunctor.AxiomaticZJCharacteristic
public import CFSG.LocalAnalysis.SignalizerFunctor.CompatibleFixedIntersections
public import CFSG.LocalAnalysis.SignalizerFunctor.PrimeCoreConjugation
public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerFactorizationTransfer

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers

namespace CFSG.SignalizerFunctorTheorem.Solvable

variable {G : Type*} [Group G]

theorem conjugate_zj_normalizer_completion (prime rank : ℕ) (actor : Subgroup G)
    (values : Subgroup G → Subgroup G)
    (balanced : ∀ selected ∈ signalizerFunctorEk prime rank actor,
      ∀ other ∈ signalizerFunctorEk prime rank actor,
        values selected ⊓ Subgroup.centralizer (other : Set G) ≤ values other)
    (target : Subgroup G) (element : signalizerCommonFixed prime rank actor values) :
    conjugateSubgroup element.val (signalizerNormalizerCompletion prime rank actor values
        (embeddedOrderThompsonCenter target)) =
      signalizerNormalizerCompletion prime rank actor values
        (embeddedOrderThompsonCenter (conjugateSubgroup element.val target)) := by
  rw [signalizer_normalizer_completion_conjugate prime rank actor _ values balanced element,
    show conjugateSubgroup element.val (embeddedOrderThompsonCenter target) =
      embeddedOrderThompsonCenter (conjugateSubgroup element.val target) from
      embedded_order_thompson_center_map_of_injective (MulAut.conj element.val).toMonoidHom
        (MulAut.conj element.val).injective target]

@[expose] def NormalizerControlled (prime rank q : ℕ) (actor : Subgroup G)
    (values : Subgroup G → Subgroup G) (model W : Subgroup G) : Prop :=
  ∃ element : signalizerCommonFixed prime rank actor values,
    signalizerNormalizerCompletion prime rank actor values W =
      (primeSetCore (GroupType := signalizerNormalizerCompletion prime rank actor values W)
          ({q}ᶜ)).map (signalizerNormalizerCompletion prime rank actor values W).subtype ⊔
        (signalizerNormalizerCompletion prime rank actor values W ⊓
          conjugateSubgroup element.val model)

theorem signalizerNormalizerFactorization_iff_controlled (prime rank q : ℕ) (actor : Subgroup G)
    (values : Subgroup G → Subgroup G) (model : Subgroup G) :
    signalizerNormalizerFactorization prime rank q actor values model ↔
      ∀ target : Subgroup G, target ≠ ⊥ →
        solvableSignalizerCompatible prime rank actor values target → IsPGroup q target →
        NormalizerControlled prime rank q actor values model target :=
  Iff.rfl

variable [Finite G]

theorem normalizer_controlled_transfer
    (prime rank q : ℕ) (prime_prime : prime.Prime) (q_prime : q.Prime)
    (actor : Subgroup G) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup G → Subgroup G)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (controller V W : Subgroup G)
    (hcontroller : solvableSignalizerCompatible prime rank actor values controller)
    (hmiddle : solvableSignalizerCompatible prime rank actor values
      (signalizerNormalizerCompletion prime rank actor values V))
    (hW : W ≠ ⊥) (hWcomp : solvableSignalizerCompatible prime rank actor values W)
    (hWq : IsPGroup q W) (hWle : W ≤ signalizerNormalizerCompletion prime rank actor values V)
    (hVcontrolled : NormalizerControlled prime rank q actor values controller V)
    (hWfactor : signalizerNormalizerCompletion prime rank actor values W =
      (primeSetCore (GroupType := signalizerNormalizerCompletion prime rank actor values W)
          ({q}ᶜ)).map (signalizerNormalizerCompletion prime rank actor values W).subtype ⊔
        (signalizerNormalizerCompletion prime rank actor values W ⊓
          signalizerNormalizerCompletion prime rank actor values V)) :
    NormalizerControlled prime rank q actor values controller W := by
  obtain ⟨first, hfirst⟩ := hVcontrolled
  obtain ⟨second, -, hsecond⟩ := signalizer_normalizer_factorization_transfer prime rank q
    prime_prime q_prime actor (conjugateSubgroup first.val controller)
    (signalizerNormalizerCompletion prime rank actor values V) W elementary large values conditions
    locally_complete
    (solvable_signalizer_compatible_conjugate prime rank actor controller values hcontroller first)
    hmiddle hWcomp hW hWq hWle (by rwa [inf_comm] at hfirst) hWfactor
  refine ⟨second * first, ?_⟩
  rw [show conjugateSubgroup (second * first).val controller =
    conjugateSubgroup second.val (conjugateSubgroup first.val controller) from
      (conjugate_subgroup_mul _ _ _).symm]
  exact hsecond

end CFSG.SignalizerFunctorTheorem.Solvable
