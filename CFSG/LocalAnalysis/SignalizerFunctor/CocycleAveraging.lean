module

public import CFSG.LocalAnalysis.SignalizerFunctor.IrreducibleAction

public section

universe actorUniverse moduleUniverse

namespace CFSG.SignalizerFunctor.Helpers

theorem coprime_additive_cocycle_principal
    (ActorType : Type actorUniverse) [Group ActorType] [Finite ActorType]
    (ModuleType : Type moduleUniverse) [AddCommGroup ModuleType]
    [DistribMulAction ActorType ModuleType]
    (coprime : Nat.Coprime (Nat.card ModuleType) (Nat.card ActorType))
    (cocycle : ActorType → ModuleType)
    (cocycle_law : ∀ first second : ActorType,
      cocycle (first * second) = cocycle first + first • cocycle second) :
    ∃ average : ModuleType, ∀ actorElement : ActorType,
      cocycle actorElement = average - actorElement • average := by
  classical
  let : Fintype ActorType := Fintype.ofFinite ActorType
  let total : ModuleType := ∑ actorElement : ActorType, cocycle actorElement
  have sum_law : ∀ actorElement : ActorType,
      total = Fintype.card ActorType • cocycle actorElement + actorElement • total := by
    intro actorElement
    calc
      total = ∑ other : ActorType, cocycle (actorElement * other) :=
        (Fintype.sum_bijective (Equiv.mulLeft actorElement)
          (Equiv.mulLeft actorElement).bijective _ cocycle (fun _ => rfl)).symm
      _ = ∑ other : ActorType, (cocycle actorElement + actorElement • cocycle other) := by
        apply Finset.sum_congr rfl
        intro other _
        exact cocycle_law actorElement other
      _ = Fintype.card ActorType • cocycle actorElement + actorElement • total := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ← Finset.smul_sum]
  have bijective : Function.Bijective (fun element : ModuleType =>
      Fintype.card ActorType • element) := by
    rw [← Nat.card_eq_fintype_card]
    exact coprime.nsmul_right_bijective
  obtain ⟨average, average_total⟩ := bijective.surjective total
  refine ⟨average, ?_⟩
  intro actorElement
  apply bijective.injective
  change Fintype.card ActorType • cocycle actorElement =
    Fintype.card ActorType • (average - actorElement • average)
  change Fintype.card ActorType • average = total at average_total
  rw [nsmul_sub, average_total]
  have action_nsmul : Fintype.card ActorType • (actorElement • average) =
      actorElement • (Fintype.card ActorType • average) :=
    (map_nsmul (DistribSMul.toAddMonoidHom ModuleType actorElement) _ average).symm
  rw [action_nsmul, average_total]
  exact eq_sub_iff_add_eq.mpr (sum_law actorElement).symm

theorem coprime_multiplicative_cocycle_principal
    (ActorType : Type actorUniverse) [Group ActorType] [Finite ActorType]
    (GroupType : Type moduleUniverse) [CommGroup GroupType]
    [MulDistribMulAction ActorType GroupType]
    (coprime : Nat.Coprime (Nat.card GroupType) (Nat.card ActorType))
    (cocycle : ActorType → GroupType)
    (cocycle_law : ∀ first second : ActorType,
      cocycle (first * second) = cocycle first * (first • cocycle second)) :
    ∃ average : GroupType, ∀ actorElement : ActorType,
      cocycle actorElement = average * (actorElement • average)⁻¹ := by
  let _action := additiveActionOfMultiplicative ActorType GroupType
  let additiveCocycle : ActorType → Additive GroupType := fun element =>
    Additive.ofMul (cocycle element)
  have additive_law : ∀ first second : ActorType,
      additiveCocycle (first * second) = additiveCocycle first + first • additiveCocycle second :=
    cocycle_law
  obtain ⟨average, principal⟩ := coprime_additive_cocycle_principal ActorType
    (Additive GroupType) coprime additiveCocycle additive_law
  refine ⟨average.toMul, ?_⟩
  intro actorElement
  have equality := congrArg Additive.toMul (principal actorElement)
  rw [sub_eq_add_neg] at equality
  exact equality

end CFSG.SignalizerFunctor.Helpers
