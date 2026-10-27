module

public import CFSG.RankThree.PartOne.SPOR.I613Plane
public import CFSG.RankThree.PartOne.S11c.PlaneLift
public import CFSG.RankThree.PartOne.N143.Statements

public section

namespace CFSG.RankThree.PartOne.N143X

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.N143
open scoped commutatorElement

theorem item613_false_of_inner_planes {X : Type} [Group X] [Finite X]
    (hZ : Subgroup.center X = ⊥) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpl : ∀ (E' : Subgroup (MulAut X)) (U : Subgroup X), PlaneOn p E' U →
      E' ≤ (MulAut.conj : X →* MulAut X).range → PlaneCentralizes E' U)
    {E : Subgroup X} [IsElementaryAbelian p E] (hcard : p ^ 2 ≤ Nat.card E) {S : Subgroup X}
    (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 S) (hEN : E ≤ Subgroup.normalizer (S : Set X))
    (hSE : ⁅S, E⁆ = S) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hinj : Function.Injective (MulAut.conj : X →* MulAut X) := conj_injective_of_center_bot hZ
  have hcent : ∀ x ∈ E, ∀ u ∈ S, x * u * x⁻¹ = u := by
    intro x hx u hu
    by_cases hx1 : x = 1
    · simp [hx1]
    obtain ⟨E0, hE0E, hxE0, hE0card, hE0el⟩ :=
      SPOR.exists_plane_containing hp hcard hx hx1
    have hplane : PlaneOn p (E0.map (MulAut.conj : X →* MulAut X)) S :=
      { prime := hp
        three_lt := by omega
        elementary := IsElementaryAbelian.map _
        card := by rw [Subgroup.card_map_of_injective hinj, hE0card]
        two_group := hS2
        normalized := by
          intro e he v hv
          obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 he
          have h := (Subgroup.mem_normalizer_iff.1 (hEN (hE0E ht)) v).1 hv
          simpa [MulAut.conj_apply] using h }
    have h := hpl _ S hplane (Subgroup.map_le_range _ _) (MulAut.conj x)
      (Subgroup.mem_map_of_mem _ hxE0) u hu
    simpa [MulAut.conj_apply] using h
  have hEc : E ≤ Subgroup.centralizer (S : Set X) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h := hcent x hx u hu
    calc u * x = (x * u * x⁻¹) * x := by rw [h]
      _ = x * u := by group
  have hcomm : ⁅E, S⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hEc
  apply hS1
  rw [← hSE, Subgroup.commutator_comm]
  exact hcomm

end CFSG.RankThree.PartOne.N143X
