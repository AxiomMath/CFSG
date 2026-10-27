module

public import CFSG.LocalAnalysis.SignalizerFunctor.SignalizerFactorization
public import CFSG.LocalAnalysis.SignalizerFunctor.ThompsonSubgroupTransport

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers

namespace CFSG.SignalizerFunctorTheorem.Solvable

variable {G : Type*} [Group G] [Finite G]

theorem zj_larger_normalizer
    (prime rank q : ℕ) (prime_prime : prime.Prime) (q_prime : q.Prime)
    (actor : Subgroup G) (elementary : IsElemAbelian prime actor)
    (large : prime ^ (rank + 1) ≤ Nat.card actor)
    (values : Subgroup G → Subgroup G)
    (conditions : SolvableSignalizerConditions prime rank actor values)
    (locally_complete : solvableSignalizerLocallyComplete prime rank actor values)
    (T larger : Subgroup G) (hTne : T ≠ ⊥)
    (hTcomp : solvableSignalizerCompatible prime rank actor values T)
    (hlargerComp : solvableSignalizerCompatible prime rank actor values larger)
    (hlargerq : IsPGroup q larger) (hlt : T < larger) :
    ∃ R : Subgroup G, solvableSignalizerCompatible prime rank actor values R ∧ IsPGroup q R ∧
      R ≤ signalizerNormalizerCompletion prime rank actor values (embeddedOrderThompsonCenter T) ∧
      Nat.card T < Nat.card R := by
  have hstrict : T < larger ⊓ Subgroup.normalizer (T : Set G) :=
    pgroup_normalizer_strict_growth q q_prime larger T hlargerq hlt
  have hTq : IsPGroup q T := hlargerq.to_le hlt.le
  have hnormalized : actor ≤ Subgroup.normalizer
      ((larger ⊓ Subgroup.normalizer (T : Set G) : Subgroup G) : Set G) :=
    normalizer_inf_of_le actor larger _ hlargerComp.1.1 (normalizer_normalized actor T hTcomp.1.1)
  have hRcomp := solvable_signalizer_compatible_of_le prime rank actor values larger _
    hlargerComp inf_le_left hnormalized
  obtain ⟨hZne, -⟩ := embedded_order_thompson_center_pgroup q q_prime T hTq hTne
  obtain ⟨hZle, -, hZnorm⟩ := embedded_order_thompson_center_properties T actor hTcomp.1.1
  have hZcomp := solvable_signalizer_compatible_of_le prime rank actor values T _ hTcomp hZle hZnorm
  have hcomplete := locally_complete.1 _ hZne hZcomp
  have control := signalizer_normalizer_completion_control prime rank prime_prime actor _ elementary
    large values conditions.coprime hZcomp.1 hcomplete.1
  have hnormalizerLe : Subgroup.normalizer (T : Set G) ≤
      Subgroup.normalizer (embeddedOrderThompsonCenter T : Set G) :=
    (embedded_order_thompson_center_properties T _ (le_refl _)).2.2
  exact ⟨_, hRcomp, hlargerq.to_le inf_le_left,
    control.2.2.2 _ hRcomp.1 (inf_le_right.trans hnormalizerLe),
    subgroup_card_strict_mono hstrict⟩

end CFSG.SignalizerFunctorTheorem.Solvable
