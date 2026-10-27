module

public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Basic
public import CFSG.SignalizerFunctorTheorem.Basic
public import CFSG.LocalAnalysis.SignalizerFunctor.CompatibleSubgroups

public section

open CFSG.Open CFSG.SignalizerFunctor.Helpers

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type*} [Group G] {p : ℕ} {A : Subgroup G} {θ : G → Subgroup G}

theorem mem_signalizerFunctorEk_one_iff (hp : p.Prime) (hA : IsElemAbelian p A) {S : Subgroup G} :
    S ∈ signalizerFunctorEk p 1 A ↔ ∃ a ∈ A, a ≠ 1 ∧ Subgroup.zpowers a = S := by
  constructor
  · exact exists_zpowers_eq_of_mem_signalizerFunctorEk_one hp
  · rintro ⟨a, ha, ha1, rfl⟩
    exact zpowers_mem_signalizerFunctorEk_one hp hA ha ha1

theorem IsFunctor.isSignalizerFunctor_thetaOf [Finite G] (hp : p.Prime) (hA : IsElemAbelian p A)
    (hθ : IsFunctor p A θ) : IsSignalizerFunctor p 1 A (thetaOf θ) := by
  have hne : ∀ S ∈ signalizerFunctorEk p 1 A, S ≠ ⊥ := by
    intro S hS h
    have hc : Nat.card S = p := by rw [hS.2, pow_one]
    rw [h, Subgroup.card_bot] at hc
    exact hp.one_lt.ne hc
  refine ⟨fun S hS => hθ.thetaOf_le_centralizer hS.1,
    fun S hS => hθ.coprime_thetaOf hS.1 (hne S hS), fun S hS => hθ.normalizes_thetaOf hS.1,
    fun S hS S' hS' => ?_⟩
  obtain ⟨a, ha, ha1, rfl⟩ := (mem_signalizerFunctorEk_one_iff hp hA).mp hS
  obtain ⟨b, hb, hb1, rfl⟩ := (mem_signalizerFunctorEk_one_iff hp hA).mp hS'
  rw [hθ.thetaOf_zpowers ha ha1, hθ.thetaOf_zpowers hb hb1, centralizer_zpowers_eq_singleton]
  exact hθ.balance a ha ha1 b hb hb1

theorem signalizerCompatible_thetaOf_iff (hp : p.Prime) (hA : IsElemAbelian p A)
    (hθ : IsFunctor p A θ) {X : Subgroup G} :
    signalizerCompatible p 1 A (thetaOf θ) X ↔
      A ≤ Subgroup.normalizer (X : Set G) ∧
        ∀ a ∈ A, a ≠ 1 → X ⊓ Subgroup.centralizer {a} ≤ θ a := by
  unfold signalizerCompatible
  refine and_congr_right fun _ => ⟨fun h a ha ha1 => ?_, fun h S hS => ?_⟩
  · have := h _ (zpowers_mem_signalizerFunctorEk_one hp hA ha ha1)
    rwa [centralizer_zpowers_eq_singleton, hθ.thetaOf_zpowers ha ha1] at this
  · obtain ⟨a, ha, ha1, rfl⟩ := (mem_signalizerFunctorEk_one_iff hp hA).mp hS
    rw [hθ.thetaOf_zpowers ha ha1, centralizer_zpowers_eq_singleton]
    exact h a ha ha1

theorem mem_signalizers_iff_signalizerCompatible (hp : p.Prime) (hA : IsElemAbelian p A)
    (hθ : IsFunctor p A θ) {P : Subgroup G → Prop} {X : Subgroup G} :
    X ∈ signalizers p A θ P ↔
      signalizerCompatible p 1 A (thetaOf θ) X ∧ Nat.Coprime p (Nat.card X) ∧ P X := by
  rw [signalizerCompatible_thetaOf_iff hp hA hθ, mem_signalizers_iff]
  tauto

end CFSG.SignalizerFunctorTheorem.McBride
