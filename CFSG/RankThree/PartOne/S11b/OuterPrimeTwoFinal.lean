module

public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoLinear
public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSymplectic
public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadic

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def OrthogonalOuterPrimeTwoTrivial : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    ∀ (t : StatedLieTag) (n p f : ℕ), (t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus) →
      StatedClassicalModel S t n p f → OuterPrimeTwoTrivial S

theorem classicalOuterPrimeTwoTrivial_of_orthogonal (horth : OrthogonalOuterPrimeTwoTrivial) :
    ClassicalOuterPrimeTwoTrivial := by
  intro S _ _ hsimple hnonab hclass
  have := hsimple
  obtain ⟨t, n, p, f, h⟩ := hclass
  cases t with
  | PSL => exact outerPrimeTwoTrivial_linear hnonab h
  | PSU => exact outerPrimeTwoTrivial_unitary hnonab h
  | PSp => exact outerPrimeTwoTrivial_symplectic h
  | POmegaOdd => exact horth S hsimple hnonab _ n p f (Or.inl rfl) h
  | POmegaPlus => exact horth S hsimple hnonab _ n p f (Or.inr (Or.inl rfl)) h
  | POmegaMinus => exact horth S hsimple hnonab _ n p f (Or.inr (Or.inr rfl)) h
  | G2 | F4 | E6 | E7 | E8 | twistedE6 | trialityD4
  | twistedB2 | twistedG2 | twistedF4 | Tits => exact h.2.elim

theorem catalogPrimeTwoAutomorphismsInner_of_open_inspections_simple
    (horth : OrthogonalOuterPrimeTwoTrivial) (hex : ExceptionalOuterPrimeTwoTrivial)
    (hsp : ∀ s, SporadicOuterSmallSimple s) : CatalogPrimeTwoAutomorphismsInner :=
  catalogPrimeTwoAutomorphismsInner_of_outer fun S _ _ hsimple hnonab hcat => by
    rcases hcat with ⟨q, hq, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | hclass | hexc | hspor
    · exfalso
      obtain ⟨a, b, hab⟩ := hnonab
      apply hab
      have h1 : e (a * b) = e (b * a) := by
        rw [map_mul, map_mul]
        exact mul_comm _ _
      exact e.injective h1
    · exact outerPrimeTwoTrivial_alternating hn e
    · exact classicalOuterPrimeTwoTrivial_of_orthogonal horth S hsimple hnonab hclass
    · exact hex S hsimple hnonab hexc
    · exact outerPrimeTwoTrivial_sporadic_of_small_simple hsp hnonab hspor

end CFSG.RankThree.PartOne
