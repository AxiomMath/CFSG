module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Group

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem s16h_exists_noncyclic_pgroup_of_perfect_quotient {H : Type*} [Group H] [Finite H]
    {C : Subgroup H} [C.Normal] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hperf : Group.IsPerfect (H ⧸ C)) (h1 : p ∣ Nat.card (H ⧸ C)) (h2 : p ∣ Nat.card C) :
    ∃ P : Subgroup H, IsPGroup p P ∧ ¬ IsCyclic ↥P := by
  letI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsPerfect (H ⧸ C) := hperf
  obtain ⟨P⟩ := Sylow.nonempty (p := p) (G := H)
  exact ⟨(P : Subgroup H), P.isPGroup',
    not_isCyclic_sylow_of_perfect_quotient (φ := QuotientGroup.mk' C)
      (QuotientGroup.mk'_surjective C) h1 (by rw [QuotientGroup.ker_mk']; exact h2) P⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
