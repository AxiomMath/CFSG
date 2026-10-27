module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.S143UA

public section

namespace CFSG.Quasithin

open Equiv

namespace S143

namespace InspW2

@[expose] def sg0 : Perm (Fin 8) := (swap 0 1 * swap 2 3) * (swap 4 5 * swap 6 7)

theorem cycleType_swap8 {x y : Fin 8} (h : x ≠ y) : (swap x y).cycleType = {2} := by
  rw [(Equiv.Perm.isCycle_swap h).cycleType, Equiv.Perm.card_support_swap h]

theorem cycleType_sg0 : sg0.cycleType = Multiset.replicate 4 2 := by
  have d1 : (swap (0 : Fin 8) 1).Disjoint (swap 2 3) := by
    unfold Equiv.Perm.Disjoint
    decide
  have d2 : (swap (4 : Fin 8) 5).Disjoint (swap 6 7) := by
    unfold Equiv.Perm.Disjoint
    decide
  have d3 : (swap (0 : Fin 8) 1 * swap 2 3).Disjoint (swap 4 5 * swap 6 7) := by
    unfold Equiv.Perm.Disjoint
    decide
  unfold sg0
  rw [d3.cycleType_mul, d1.cycleType_mul, d2.cycleType_mul, cycleType_swap8 (by decide),
    cycleType_swap8 (by decide), cycleType_swap8 (by decide), cycleType_swap8 (by decide)]
  rfl

@[expose] def tau8 : Fin 9 → Perm (Fin 8) :=
  ![[0, 2, 4].formPerm * [1, 3, 5].formPerm, [0, 4, 2].formPerm * [1, 5, 3].formPerm,
    [0, 2, 6].formPerm * [1, 3, 7].formPerm, [0, 6, 2].formPerm * [1, 7, 3].formPerm,
    [0, 4, 6].formPerm * [1, 5, 7].formPerm, [0, 6, 4].formPerm * [1, 7, 5].formPerm,
    [2, 4, 6].formPerm * [3, 5, 7].formPerm, [2, 6, 4].formPerm * [3, 7, 5].formPerm,
    [1, 2, 4].formPerm * [0, 3, 5].formPerm]

theorem tau8_props : (∀ i, tau8 i ^ 3 = 1 ∧ tau8 i ≠ 1 ∧ tau8 i * sg0 = sg0 * tau8 i) ∧
    Function.Injective tau8 := by
  unfold tau8 sg0
  decide +kernel

theorem exists_nine_order_three (σ : Perm (Fin 8)) (h : σ.cycleType = Multiset.replicate 4 2) :
    ∃ f : Fin 9 → Perm (Fin 8), Function.Injective f ∧
      ∀ i, f i ^ 3 = 1 ∧ f i ≠ 1 ∧ f i * σ = σ * f i := by
  obtain ⟨c, hc⟩ :=
    isConj_iff.mp (Equiv.Perm.isConj_iff_cycleType_eq.mpr (h.trans cycleType_sg0.symm))
  obtain ⟨hp, hinj⟩ := tau8_props
  have hσ : σ = c⁻¹ * sg0 * c := by rw [← hc]; group
  refine ⟨fun i => c⁻¹ * tau8 i * c, ?_, fun i => ?_⟩
  · intro i j hij
    apply hinj
    exact mul_left_cancel (mul_right_cancel hij : c⁻¹ * tau8 i = c⁻¹ * tau8 j)
  · dsimp only
    refine ⟨?_, ?_, ?_⟩
    · have h1 : c⁻¹ * tau8 i * c = (MulAut.conj c⁻¹) (tau8 i) := by simp
      rw [h1, ← map_pow, (hp i).1, map_one]
    · intro h1
      apply (hp i).2.1
      have : tau8 i = c * (c⁻¹ * tau8 i * c) * c⁻¹ := by group
      rw [this, h1]
      group
    · calc c⁻¹ * tau8 i * c * σ = c⁻¹ * (tau8 i * sg0) * c := by rw [hσ]; group
        _ = c⁻¹ * (sg0 * tau8 i) * c := by rw [(hp i).2.2]
        _ = σ * (c⁻¹ * tau8 i * c) := by rw [hσ]; group

end InspW2

end S143

end CFSG.Quasithin
