module

public import CFSG.Quasithin.EmptyFaithful.T1521SBlkBasic
public import CFSG.Quasithin.EmptyFaithful.T1521SBlkDefs
public import CFSG.Quasithin.EmptyFaithful.T1521SAux
public import CFSG.Quasithin.EmptyFaithful.T1521SDefs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

theorem nrm1521_l2_of {G : Type} [Group G] [Finite G] {S L : Subgroup G} {n : ℕ}
    (hAut : AutFactL2Block1521) (hshort : IsShort2 L) (hn : 1 < n) (hLn : IsLin2Type L n)
    (hS2 : IsPGroup 2 ↥S) (hsyl : IsSylowTwoOf (S ⊓ L) L) (hth : ⁅L, thompsonJ S⁆ = L) :
    Nrm1521 S L :=
  ⟨oTwoUpper (L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G)),
    (oTwoUpper_le _).trans le_conjJoin,
    (oTwoUpper_le _).trans (borel_le_normalizer_thompsonJ_l2 (by omega) hLn hshort hS2 hsyl hth),
    oTwoUpper_oTwoUpper1521 _, fun v hvS hvN hc l hl =>
    hAut G L (S ⊓ L) hshort ⟨n, hn, hLn⟩ hsyl v hvN
      (hS2.to_le (Subgroup.zpowers_le.mpr hvS)) hc l hl⟩

theorem dich1521BlockL2_of (hAut : AutFactL2Block1521) : Dich1521BlockL2 := by
  intro G _ _ X S L hstd hth _ hblk hL
  obtain ⟨n, hn, hLn⟩ := hL
  exact Or.inl (nrm1521_l2_of hAut hblk.1 hn hLn hstd.sylow.isPGroup hstd.sylowL hth)

end CFSG.Quasithin
