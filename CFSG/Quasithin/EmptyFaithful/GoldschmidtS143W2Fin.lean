module

public import CFSG.Quasithin.EmptyFaithful.Insp7NumD
public import CFSG.Quasithin.EmptyFaithful.Insp7NumS
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Alt
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2L2
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2L2e
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Ree
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Spor
public import CFSG.Quasithin.EmptyFaithful.Insp7NumJ
public import CFSG.Quasithin.EmptyFaithful.Insp7NumR
public import CFSG.Quasithin.EmptyFaithful.Insp7NumTits
public import CFSG.Quasithin.EmptyFaithful.Insp7NumW
public import Certificates.Certificate2199
public import Certificates.Certificate2267

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank CFSG.Blueprint

namespace S143

namespace InspW2

@[expose] def SmallLieNoU33 (L : Type) [Group L] : Prop :=
  Insp7.SmallLie L ∧ ¬ StatedClassicalModel L .PSU 3 3 1

theorem resW_coverL34 (hL34 : ResW fun L _ => StatedClassicalModel L .PSL 3 2 2) :
    ResW fun L _ => Subgroup.center L ≠ ⊥ ∧ Subgroup.center L = CFSG.pCore 2 L ∧
      StatedClassicalModel (L ⧸ CFSG.pCore 2 L) .PSL 3 2 2 :=
  resW_cover (G' := fun L _ => StatedClassicalModel L .PSL 3 2 2)
    (fun _ _ _ _ ⟨_, hc, hadm, K, hKf, hKfin, hK, ⟨e'⟩⟩ =>
      ⟨hadm, K, hKf, hKfin, hK, ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans e'⟩⟩) hL34

theorem resW_smallLie (hL34 : ResW fun L _ => StatedClassicalModel L .PSL 3 2 2)
    (hU34 : ResW fun L _ => StatedClassicalModel L .PSU 3 2 2)
    (hA8 : ResW fun L _ => StatedClassicalModel L .PSL 4 2 1)
    (hSz8 : ResW fun L _ => SuzukiModel L 2 3) : ResW SmallLieNoU33 := by
  intro L _ _ hq ⟨hS, hnot⟩ Gc _ _ ρ ž Ŝ Kh hin hz
  rcases hS with h | h | h | h | h | h | h | h | h | h
  · exact resW_of_numFactW numFactW_evenL2 L hq h Gc ρ ž Ŝ Kh hin hz
  · exact resW_of_numFactW numFactW_psl32 L hq h Gc ρ ž Ŝ Kh hin hz
  · exact hL34 L hq h Gc ρ ž Ŝ Kh hin hz
  · exact hU34 L hq h Gc ρ ž Ŝ Kh hin hz
  · exact resW_of_numFactW numFactW_sp44 L hq h Gc ρ ž Ŝ Kh hin hz
  · exact hA8 L hq h Gc ρ ž Ŝ Kh hin hz
  · exact resW_of_resWAny resWAny_a6 L hq h Gc ρ ž Ŝ Kh hin hz
  · exact absurd h hnot
  · exact hSz8 L hq h Gc ρ ž Ŝ Kh hin hz
  · exact resW_coverL34 hL34 L hq h Gc ρ ž Ŝ Kh hin hz

theorem resW_oddFam (hL33 : ResW Insp7.L33Fam) : ResW Insp7.OddFam :=
  resW_of_union (G' := Insp7.L33Fam) (H := Insp7.OddL2Fam) (fun _ _ h => h) hL33
    (resW_of_numFactW numFactW_oddL2)

theorem inspWi_of_residuals
    (hbig : ∀ s : TauCeti.SporadicName, (s = .M24 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) →
      2 ^ 9 ∣ Nat.card (NativeSporadic.Carrier s))
    (hsimple : ∀ s : TauCeti.SporadicName,
      (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .J2) →
        IsSimpleGroup (NativeSporadic.Carrier s))
    (hL34 : ResW fun L _ => StatedClassicalModel L .PSL 3 2 2)
    (hU34 : ResW fun L _ => StatedClassicalModel L .PSU 3 2 2)
    (hA8 : ResW fun L _ => StatedClassicalModel L .PSL 4 2 1)
    (hSz8 : ResW fun L _ => SuzukiModel L 2 3) (hL33 : ResW Insp7.L33Fam)
    (hM12 : ResW Insp7.M12Fam) : InspWi := by
  intro L _ _ hq hlist Gc _ _ ρ ž Ŝ Kh hin hz
  by_cases hU33 : StatedClassicalModel L .PSU 3 3 1
  · exact hU33
  exfalso
  rcases Insp7.listCases_cases hq hbig hlist with hb | hs | ht | ho | hp
  · exact resW_of_numFactW (numFactW_of_big fun _ _ _ _ h => two_pow_seven_of_bigDvd h)
      L hq hb Gc ρ ž Ŝ Kh hin hz
  · exact resW_smallLie hL34 hU34 hA8 hSz8 L hq ⟨hs, hU33⟩ Gc ρ ž Ŝ Kh hin hz
  · exact resW_of_numFactW numFactW_largeReeTits L hq ht Gc ρ ž Ŝ Kh hin hz
  · exact resW_oddFam hL33 L hq ho Gc ρ ž Ŝ Kh hin hz
  · exact resW_sporSmall hsimple hM12 numFactW_sporNoM12 L hq hp Gc ρ ž Ŝ Kh hin hz

theorem inspW_of_residuals
    (hbig : ∀ s : TauCeti.SporadicName, (s = .M24 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) →
      2 ^ 9 ∣ Nat.card (NativeSporadic.Carrier s))
    (hsimple : ∀ s : TauCeti.SporadicName,
      (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .J2) →
        IsSimpleGroup (NativeSporadic.Carrier s))
    (hL34 : ResW fun L _ => StatedClassicalModel L .PSL 3 2 2)
    (hU34 : ResW fun L _ => StatedClassicalModel L .PSU 3 2 2)
    (hA8 : ResW fun L _ => StatedClassicalModel L .PSL 4 2 1)
    (hSz8 : ResW fun L _ => SuzukiModel L 2 3) (hL33 : ResW Insp7.L33Fam)
    (hM12 : ResW Insp7.M12Fam) : InspW :=
  ⟨inspWi_of_residuals hbig hsimple hL34 hU34 hA8 hSz8 hL33 hM12, inspWo⟩

theorem inspW_cards
    (hL34 : ResW fun L _ => StatedClassicalModel L .PSL 3 2 2)
    (hU34 : ResW fun L _ => StatedClassicalModel L .PSU 3 2 2)
    (hA8 : ResW fun L _ => StatedClassicalModel L .PSL 4 2 1)
    (hSz8 : ResW fun L _ => SuzukiModel L 2 3) (hL33 : ResW Insp7.L33Fam)
    (hM12 : ResW Insp7.M12Fam) : InspW :=
  inspW_of_residuals (fun _ hs => Insp7.card_carrier_big hs)
    (fun _ hs => Insp7.isSimpleGroup_carrier_small hs) hL34 hU34 hA8 hSz8 hL33 hM12

end InspW2

end S143

end CFSG.Quasithin
