module

public import CFSG.Milestones.ASVolI.C31.KW

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

@[expose] def burnsideJ4KW_IsMaxTwoLocal (X : Subgroup J) : Prop :=
  IsPGroup 2 ↥X ∧ X ≠ ⊥ ∧ ∀ Y : Subgroup J, IsPGroup 2 ↥Y → Y ≠ ⊥ →
    Subgroup.normalizer (X : Set J) ≤ Subgroup.normalizer (Y : Set J) →
    Subgroup.normalizer (Y : Set J) = Subgroup.normalizer (X : Set J)

@[expose] def burnsideJ4KW_MaxNonParabolic : Prop :=
  ∀ X : Subgroup J, burnsideJ4KW_IsMaxTwoLocal X →
    (∀ g : J, ¬ P0.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (X : Set J)) →
    ∃ g : J, Subgroup.normalizer (X : Set J) ≤ CFSG.Quasithin.KGJ4.M4.map (MulAut.conj g).toMonoidHom

theorem burnsideJ4KW_finite_subgroup : Finite (Subgroup J) :=
  Finite.of_injective (fun H : Subgroup J => (H : Set J)) SetLike.coe_injective

theorem burnsideJ4KW_exists_maxTwoLocal {P : Subgroup J} (hP : IsPGroup 2 ↥P) (hne : P ≠ ⊥) :
    ∃ X : Subgroup J, burnsideJ4KW_IsMaxTwoLocal X ∧
      Subgroup.normalizer (P : Set J) ≤ Subgroup.normalizer (X : Set J) := by
  haveI := burnsideJ4KW_finite_subgroup
  let S : Set (Subgroup J) := {Y | IsPGroup 2 ↥Y ∧ Y ≠ ⊥ ∧
    Subgroup.normalizer (P : Set J) ≤ Subgroup.normalizer (Y : Set J)}
  have hS : S.Nonempty := ⟨P, hP, hne, le_rfl⟩
  obtain ⟨X, hX, hmax⟩ := (Set.toFinite S).exists_maximalFor
    (fun Y : Subgroup J => Nat.card ↥(Subgroup.normalizer (Y : Set J))) S hS
  obtain ⟨hX2, hXne, hPX⟩ := hX
  refine ⟨X, ⟨hX2, hXne, fun Y hY hYne hXY => ?_⟩, hPX⟩
  have hYS : Y ∈ S := ⟨hY, hYne, hPX.trans hXY⟩
  have hcard := hmax hYS (Subgroup.card_le_of_le hXY)
  exact (Subgroup.eq_of_le_of_card_ge hXY hcard).symm

theorem burnsideJ4KW_twoLocals_of_maxNonParabolic
    (h : burnsideJ4KW_MaxNonParabolic) : CFSG.Quasithin.KGJ4.J4TwoLocalsKW := by
  intro P hP hne
  obtain ⟨X, hXmax, hPX⟩ := burnsideJ4KW_exists_maxTwoLocal hP hne
  by_cases hs : ∃ g : J, P0.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (X : Set J)
  · obtain ⟨g, hg⟩ := hs
    rcases burnsideC31_kw_parabolic hXmax.1 hXmax.2.1 g hg with h1 | h1 | h1
    · exact ⟨g, Or.inl (hPX.trans h1)⟩
    · exact ⟨g, Or.inr (Or.inl (hPX.trans h1))⟩
    · exact ⟨g, Or.inr (Or.inr (Or.inl (hPX.trans h1)))⟩
  · obtain ⟨g, hg⟩ := h X hXmax fun g hg => hs ⟨g, hg⟩
    exact ⟨g, Or.inr (Or.inr (Or.inr (hPX.trans hg)))⟩

theorem burnsideJ4KW_isPGroup_of_sq {A : Subgroup J} (hsq : ∀ x ∈ A, x * x = 1) :
    IsPGroup 2 ↥A := fun x => ⟨1, Subtype.ext (by
  have := hsq x x.2
  simpa [pow_one, pow_two] using this)⟩

theorem burnsideJ4KW_core_of_maxNonParabolic
    (h : burnsideJ4KW_MaxNonParabolic) : burnsideC31_J4KWCore := by
  intro A hA _ hsq _ _
  exact burnsideJ4KW_twoLocals_of_maxNonParabolic h A (burnsideJ4KW_isPGroup_of_sq hsq) hA

end CFSG.ASVolI
