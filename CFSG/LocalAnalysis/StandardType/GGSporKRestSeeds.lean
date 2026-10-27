module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClosure

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly

theorem sporKRest_generating_of_seeds {K : Type} [Group K] [Finite K] {p : ℕ} (hp : p.Prime)
    (a b : K) (hab : Subgroup.closure ({a, b} : Set K) = ⊤) (S₀ : Subgroup K) (hS₀ : IsPGroup p S₀)
    (x₀ : K) (U : Set K)
    (hU : ∀ z ∈ U, z ∈ S₀ ∨ ∃ g y, y ∈ S₀ ∧ x₀ * g = g * y ∧ z * y = y * z)
    (ha : a ∈ Subgroup.closure U) (hb : b ∈ Subgroup.closure U) {x : K} (hx : IsConj x₀ x) :
    SporKRestGenerating p x := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hSS⟩ := hS₀.exists_le_sylow
  refine ggSporKRest_generating_of_closure hp S hx
    {z | ∃ g y, y ∈ S₀ ∧ x₀ * g = g * y ∧ z * y = y * z} ?_ ?_
  · rintro z ⟨g, y, hy, hxg, hzy⟩
    exact ⟨g, y, hSS hy, by rw [mul_assoc, hxg, inv_mul_cancel_left],
      Subgroup.mem_centralizer_singleton_iff.mpr hzy⟩
  · have hU' : Subgroup.closure U ≤ Subgroup.closure ((S : Set K) ∪
        {z | ∃ g y, y ∈ S₀ ∧ x₀ * g = g * y ∧ z * y = y * z}) := by
      rw [Subgroup.closure_le]
      intro z hz
      refine Subgroup.subset_closure ?_
      rcases hU z hz with h | h
      · exact Or.inl (hSS h)
      · exact Or.inr h
    rw [eq_top_iff, ← hab, Subgroup.closure_le]
    intro z hz
    rcases hz with rfl | rfl
    · exact hU' ha
    · exact hU' hb

theorem isPGroup_closure_of_commute {K : Type} [Group K] {p : ℕ} (S : Set K)
    (hc : ∀ x ∈ S, ∀ y ∈ S, Commute x y) (ho : ∀ x ∈ S, x ^ p = 1) :
    IsPGroup p (Subgroup.closure S) := by
  letI : CommGroup (Subgroup.closure S) :=
    Subgroup.closureCommGroupOfComm fun x hx y hy _ => hc x hx y hy
  have hcomm : ∀ x (hx : x ∈ Subgroup.closure S) y (hy : y ∈ Subgroup.closure S), Commute x y :=
    fun x hx y hy => congrArg Subtype.val (mul_comm (⟨x, hx⟩ : Subgroup.closure S) ⟨y, hy⟩)
  have key : ∀ g (hg : g ∈ Subgroup.closure S), g ^ p = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx => exact ho x hx
    | one => exact one_pow p
    | mul x y hx hy ihx ihy => rw [(hcomm x hx y hy).mul_pow, ihx, ihy, one_mul]
    | inv x hx ih => rw [inv_pow, ih, inv_one]
  intro g
  exact ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, key g g.2, Subgroup.coe_one])⟩

end CFSG.StandardType.SporadicShape

end
