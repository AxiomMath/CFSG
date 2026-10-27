module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowTools

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

theorem listRow_of_single_class {S : Type} [Group S] [Finite S]
    (hcl : ∀ a b : S, orderOf a = 3 → orderOf b = 3 → ∃ k : S, k * a * k⁻¹ = b)
    {x y : S} (hx : orderOf x = 3) (hy : y ^ 3 = 1) (hc : x * y = y * x)
    (hn : y ∉ Subgroup.zpowers x) : ListRow S := by
  refine listRow_of_forall_not_weaklyClosed fun z hz => ?_
  obtain ⟨k, hk⟩ := hcl x z hx hz
  have hy1 : y ≠ 1 := fun h => hn (h ▸ one_mem _)
  have hyo : orderOf y = 3 := orderOf_eq_prime hy hy1
  set y' := k * y * k⁻¹ with hy'
  have hy'o : orderOf y' = 3 := by
    have := orderOf_injective (MulAut.conj k).toMonoidHom (MulAut.conj k).injective y
    rw [hyo] at this
    simpa [hy'] using this
  obtain ⟨h, hh⟩ := hcl z y' hz hy'o
  refine not_weaklyClosed_of_commute_conj (g := h) ?_ ?_
  · rw [hh, ← hk, hy']
    calc k * y * k⁻¹ * (k * x * k⁻¹) = k * (y * x) * k⁻¹ := by group
      _ = k * (x * y) * k⁻¹ := by rw [hc]
      _ = k * x * k⁻¹ * (k * y * k⁻¹) := by group
  · rw [hh, ← hk, hy']
    intro hmem
    apply hn
    have := Subgroup.mem_zpowers_iff.mp hmem
    obtain ⟨i, hi⟩ := this
    refine Subgroup.mem_zpowers_iff.mpr ⟨i, ?_⟩
    have h1 : (k * x * k⁻¹) ^ i = k * x ^ i * k⁻¹ := by simp [conj_zpow]
    rw [h1] at hi
    have := congrArg (fun t => k⁻¹ * t * k) hi
    simpa [mul_assoc] using this

end CFSG.RankThree.PartTwo.Sec4.RonanK432
