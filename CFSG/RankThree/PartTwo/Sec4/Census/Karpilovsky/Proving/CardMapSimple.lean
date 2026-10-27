module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Algebra.Group.Subgroup.Finite

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving

variable {G H : Type*} [Group G] [Group H]

theorem card_map_of_isSimpleGroup (φ : G →* H)
    {T : Subgroup G} [IsSimpleGroup T] (hT : ¬ T ≤ φ.ker) :
    Nat.card (T.map φ) = Nat.card T := by
  set ψ : T →* H := φ.comp T.subtype with hψ
  rcases Subgroup.Normal.eq_bot_or_eq_top ψ.ker with h | h
  · have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp h
    have hrange : T.map φ = ψ.range := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩
      · intro hy
        obtain ⟨⟨x, hx⟩, rfl⟩ := MonoidHom.mem_range.mp hy
        exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    rw [hrange, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top]
  · exfalso
    apply hT
    intro t ht
    have hmem : (⟨t, ht⟩ : T) ∈ ψ.ker := by
      rw [h]
      exact Subgroup.mem_top _
    exact MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hmem)

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving
