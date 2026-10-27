module

public import CFSG.Quasithin.EmptyFaithful.Insp7NumY
public import CFSG.Quasithin.EmptyFaithful.Insp7NumZ

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint

namespace Insp7

@[expose] def M12Fam (L : Type) [Group L] : Prop := Nonempty (L ≃* NativeSporadic.Carrier .M12)

@[expose] def M22Fam (L : Type) [Group L] : Prop := Nonempty (L ≃* NativeSporadic.Carrier .M22)

@[expose] def M23Fam (L : Type) [Group L] : Prop := Nonempty (L ≃* NativeSporadic.Carrier .M23)

@[expose] def J2Fam (L : Type) [Group L] : Prop := Nonempty (L ≃* NativeSporadic.Carrier .J2)

theorem numFactAt_sporSimple3 (hM12 : NumFactAt M12Fam) (hM22 : NumFactAt M22Fam)
    (hM23 : NumFactAt M23Fam) (hJ2 : NumFactAt J2Fam) : NumFactAt SporSimple3 := by
  intro L _ _ hq ⟨s, hs, he⟩ z hz2 hzc Gc _ _ ρ hρ hinn ž hž Ŝ hŜ2 hŜodd hŜC hcard
  rcases hs with rfl | rfl | rfl | rfl
  · exact hM12 L hq he z hz2 hzc Gc ρ hρ hinn ž hž Ŝ hŜ2 hŜodd hŜC hcard
  · exact hM22 L hq he z hz2 hzc Gc ρ hρ hinn ž hž Ŝ hŜ2 hŜodd hŜC hcard
  · exact hM23 L hq he z hz2 hzc Gc ρ hρ hinn ž hž Ŝ hŜ2 hŜodd hŜC hcard
  · exact hJ2 L hq he z hz2 hzc Gc ρ hρ hinn ž hž Ŝ hŜ2 hŜodd hŜC hcard

theorem numFactAt_residualSimple3
    (hL34 : NumFactAt (fun L _ => StatedClassicalModel L .PSL 3 2 2))
    (hSp44 : NumFactAt (fun L _ => StatedClassicalModel L .PSp 2 2 2)) :
    NumFactAt ResidualSimple3 :=
  numFactAt_of_cover (G := fun L _ => StatedClassicalModel L .PSL 3 2 2)
    (H := fun L _ => StatedClassicalModel L .PSp 2 2 2)
    (fun L _ h => by
      unfold ResidualSimple3 at h
      exact h) hL34 hSp44

theorem numFactAt_largeReeTits_of
    (hTits : NumFactAt (fun L _ => ReeTitsModel L .Tits 2 1)) : NumFactAt LargeReeTits :=
  numFactAt_of_cover (G := fun L _ => ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ReeTitsModel L .twistedF4 2 f)
    (H := fun L _ => ReeTitsModel L .Tits 2 1)
    (fun L _ h => by
      unfold LargeReeTits at h
      exact h) numFactAt_f4 hTits

theorem lemma14320Inspect_of_natives
    (hbig : ∀ s : TauCeti.SporadicName, (s = .M24 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) →
      2 ^ 9 ∣ Nat.card (NativeSporadic.Carrier s))
    (hsimple : ∀ s : TauCeti.SporadicName,
      (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .J2) →
      IsSimpleGroup (NativeSporadic.Carrier s))
    (hM11 : NumFactAt M11Fam) (hM12 : NumFactAt M12Fam) (hM22 : NumFactAt M22Fam)
    (hM23 : NumFactAt M23Fam) (hJ2 : NumFactAt J2Fam)
    (hL34 : NumFactAt (fun L _ => StatedClassicalModel L .PSL 3 2 2))
    (hTits : NumFactAt (fun L _ => ReeTitsModel L .Tits 2 1)) : S143.Lemma14320Inspect :=
  lemma14320Inspect_of_residual3 hbig hsimple hM11
    ⟨numFactAt_residualSimple3 hL34 numFactAt_sp44, numFactAt_largeReeTits_of hTits,
      numFactAt_sporSimple3 hM12 hM22 hM23 hJ2⟩

end Insp7

end CFSG.Quasithin
