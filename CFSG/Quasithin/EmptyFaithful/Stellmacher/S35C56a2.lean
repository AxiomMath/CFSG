module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S42GtGrp

public section

namespace CFSG.Quasithin

namespace F53.Stellmacher

namespace S35.C56.Six

variable {G : Type} [Group G]

theorem eq_of_card_two {Z : Subgroup G} (hZ : Nat.card Z = 2) {a b : G} (ha : a ∈ Z) (hb : b ∈ Z)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZ
  have h1 : (⟨a, ha⟩ : Z) = y := hy _ (fun h => ha1 (congrArg Subtype.val h))
  have h2 : (⟨b, hb⟩ : Z) = y := hy _ (fun h => hb1 (congrArg Subtype.val h))
  exact congrArg Subtype.val (h1.trans h2.symm)

theorem relIndex_le_two {C V : Subgroup G}
    (h : ∀ u ∈ V, ∀ v ∈ V, u ∉ C → v ∉ C → u⁻¹ * v ∈ C) : C.relIndex V ≤ 2 := by
  by_cases hV : V ≤ C
  · rw [Subgroup.relIndex_eq_one.mpr hV]
    omega
  · obtain ⟨a, haV, haC⟩ := Set.not_subset.mp hV
    have h2 : (C.subgroupOf V).index = 2 := by
      refine Subgroup.index_eq_two_iff.mpr ⟨⟨a, haV⟩, fun b => ?_⟩
      by_cases hbC : (b : G) ∈ C
      · refine Or.inr ⟨hbC, fun hba => haC ?_⟩
        have := C.mul_mem (C.inv_mem hbC) (show (b : G) * a ∈ C from hba)
        simpa using this
      · refine Or.inl ⟨?_, hbC⟩
        show (b : G) * a ∈ C
        have := h _ (V.inv_mem b.2) a haV (fun hc => hbC (by simpa using C.inv_mem hc)) haC
        simpa using this
    exact h2.le

end S35.C56.Six

end F53.Stellmacher

end CFSG.Quasithin
