module

public import CFSG.Quasithin.EmptyFaithful.Insp7NumN

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint

namespace Insp7

@[expose] def ResidualSimple (L : Type) [Group L] : Prop :=
  StatedClassicalModel L .PSL 3 2 2 ∨ StatedClassicalModel L .PSp 2 2 2 ∨
    StatedClassicalModel L .PSL 4 2 1

theorem numFactAt_smallSimple' (h : NumFactAt ResidualSimple) : NumFactAt SmallSimple' :=
  numFactAt_of_cover (G := ResidualSimple)
    (H := fun L _ => Nonempty (L ≃* alternatingGroup (Fin 6)) ∨ StatedClassicalModel L .PSU 3 3 1 ∨
      StatedClassicalModel L .PSU 3 2 2)
    (fun L _ hL => by
      unfold SmallSimple' at hL
      unfold ResidualSimple
      tauto) h
    (numFactAt_of_cover (G := fun L _ => Nonempty (L ≃* alternatingGroup (Fin 6)))
      (H := fun L _ => StatedClassicalModel L .PSU 3 3 1 ∨ StatedClassicalModel L .PSU 3 2 2)
      (fun _ _ hL => hL) numFactAt_a6
      (numFactAt_of_cover (G := fun L _ => StatedClassicalModel L .PSU 3 3 1)
        (H := fun L _ => StatedClassicalModel L .PSU 3 2 2) (fun _ _ hL => hL) numFactAt_u33
        numFactAt_u34))

theorem lemma14320Inspect_of_residual2
    (hbig : ∀ s : TauCeti.SporadicName, (s = .M24 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) →
      2 ^ 9 ∣ Nat.card (NativeSporadic.Carrier s))
    (hsimple : ∀ s : TauCeti.SporadicName,
      (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .J2) →
      IsSimpleGroup (NativeSporadic.Carrier s))
    (hres : NumFactAt ResidualSimple ∧ NumFactAt LargeReeTits ∧ NumFactAt
        SporSimple) : S143.Lemma14320Inspect :=
  lemma14320Inspect_final hbig hsimple (numFactAt_smallSimple' hres.1) hres.2.1 numFactAt_l33
    hres.2.2

end Insp7

end CFSG.Quasithin
