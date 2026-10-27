module

public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneMarking

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggMarking_of_rawDatum {Y : Type} [Group Y] {lab : LargeEvenLabel}
    {P : LargeEvenLabel → Prop} (hlab : LargeEvenInLambda2 lab) (hP : P lab)
    (h : LargeEvenRawDatum lab fun R₀ _ _ _ =>
      IsSimpleGroup R₀ ∧ (∃ a b : R₀, a * b ≠ b * a) ∧ Nonempty (Y ≃* R₀)) :
    Subgroup.center Y = ⊥ ∧ LargeEvenMarking Y fun lab' _ _ _ _ _ => P lab' := by
  obtain ⟨R₀, _, I, F, hR₀simp, hna, ⟨e⟩⟩ := largeEvenRawDatum_exists h
  haveI : IsSimpleGroup R₀ := hR₀simp
  have hZR : Subgroup.center R₀ = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R₀) with hbot | htop
    · exact hbot
    · exfalso
      obtain ⟨a, b, hab⟩ := hna
      have ha : a ∈ Subgroup.center R₀ := htop ▸ Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.mp ha b).symm
  have hZ : Subgroup.center Y = ⊥ := center_eq_bot_of_mulEquiv e hZR
  have hcommR : commutator R₀ = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator R₀) with hbot | htop
    · haveI : IsMulCommutative R₀ := (commutator_eq_bot_iff R₀).mp hbot
      obtain ⟨a, b, hab⟩ := hna
      exact absurd (mul_comm' a b) hab
    · exact htop
  have hcomm : commutator Y = ⊤ := by
    haveI : Group.IsPerfect R₀ := ⟨hcommR⟩
    exact (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom)
      e.symm.surjective).commutator_eq_top
  refine ⟨hZ, ?_⟩
  refine ⟨hcomm, lab, hlab, largeEvenRawDatum_mono ?_ h⟩
  rintro R _ I F ⟨hs, hna, ⟨e'⟩⟩
  exact ⟨hs, hna, (QuotientGroup.quotientMulEquivOfEq hZ).trans
    (QuotientGroup.quotientBot.trans e'), hP⟩

end CFSG.StandardType
