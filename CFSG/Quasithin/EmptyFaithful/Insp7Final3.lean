module

public import CFSG.Quasithin.EmptyFaithful.Insp7Final2
public import CFSG.Quasithin.EmptyFaithful.Insp7NumO

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint

namespace Insp7

@[expose] def ResidualSimple3 (L : Type) [Group L] : Prop :=
  StatedClassicalModel L .PSL 3 2 2 ∨ StatedClassicalModel L .PSp 2 2 2

@[expose] def SporSimple3 (L : Type) [Group L] : Prop :=
  ∃ s : TauCeti.SporadicName, (s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .J2) ∧
    Nonempty (L ≃* NativeSporadic.Carrier s)

theorem numFactAt_residualSimple (h : NumFactAt ResidualSimple3) : NumFactAt ResidualSimple :=
  numFactAt_of_cover (G := ResidualSimple3) (H := fun L _ => StatedClassicalModel L .PSL 4 2 1)
    (fun L _ hL => by
      unfold ResidualSimple at hL
      unfold ResidualSimple3
      tauto) h numFactAt_a8

theorem numFactAt_sporSimple (hM11 : NumFactAt M11Fam) (h : NumFactAt SporSimple3) :
    NumFactAt SporSimple :=
  numFactAt_of_cover (G := M11Fam) (H := SporSimple3)
    (fun L _ ⟨s, hs, he⟩ => by
      rcases hs with rfl | hs
      · exact Or.inl he
      · exact Or.inr ⟨s, hs, he⟩) hM11 h

theorem lemma14320Inspect_of_residual3
    (hbig : ∀ s : TauCeti.SporadicName, (s = .M24 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) →
      2 ^ 9 ∣ Nat.card (NativeSporadic.Carrier s))
    (hsimple : ∀ s : TauCeti.SporadicName,
      (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .J2) →
      IsSimpleGroup (NativeSporadic.Carrier s))
    (hM11 : NumFactAt M11Fam) (hres : NumFactAt ResidualSimple3 ∧ NumFactAt LargeReeTits ∧ NumFactAt
        SporSimple3) : S143.Lemma14320Inspect :=
  lemma14320Inspect_of_residual2 hbig hsimple
    ⟨numFactAt_residualSimple hres.1, hres.2.1, numFactAt_sporSimple hM11 hres.2.2⟩

end Insp7

end CFSG.Quasithin
