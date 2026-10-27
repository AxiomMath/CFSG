module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamMain
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamRows
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamU3Four
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamBlk
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamSz
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamSp4
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamL3
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamU3

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin

theorem dichE9BlockA5_holds (horb : ∀ (G : Type) [Group G] [Finite G], A3Orbits G) :
    DichE9BlockA5 := by
  intro G _ _ X S L hStd hth _ hbl h5
  exact exc5_of_isAltType_five (horb G) hStd hth hbl h5

theorem dichE9BlockL2_holds (horb : ∀ (G : Type) [Group G] [Finite G], A3Orbits G) :
    DichE9BlockL2 := by
  intro G _ _ X S L hStd hth hchar hbl ⟨n, hn, hLn⟩
  by_cases hn2 : n = 2
  · subst hn2
    exact Or.inr (exc5_of_isLin2Type_two (horb G) hStd hbl.1 hLn)
  · exact Or.inl (nrmE9_BlockL2_big hStd hth hchar hbl ⟨n, by omega, hLn⟩)

theorem dichE9L2_holds (horb : ∀ (G : Type) [Group G] [Finite G], A3Orbits G) : DichE9L2 := by
  intro G _ _ X S L hStd hco _ ⟨n, hn, h⟩
  by_cases hn2 : n = 2
  · subst hn2
    exact Or.inr (exc5_of_isPSL_two_two_two (horb G) hStd hco h)
  · exact Or.inl (nrmE9_L2_big (horb G) (by omega) h hco hStd)

theorem dichE9Sz_holds
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) : DichE9Sz := by
  intro G _ _ X S L hStd hco hZ hty
  exact nrmE9_Sz h37 h38 hStd hco hZ hty

theorem dichE9U3_holds (h37 : A37ForSQTK) (h38 : A38ForSQTK) :
    DichE9U3 := by
  intro G _ _ X S L hStd hco hZ ⟨n, hn, h⟩
  by_cases hn2 : n = 2
  · subst hn2
    exact Or.inr (noE16_U3_four hStd h)
  · exact Or.inl (nrmE9_U3_big h37 h38 hStd hco hZ (by omega) h)

theorem dichE9Sp4_holds (horb : ∀ (G : Type) [Group G] [Finite G], A3Orbits G)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) : DichE9Sp4 := by
  intro G _ _ X S L hStd hco hZ ⟨n, hn, h⟩
  by_cases hn2 : n = 2
  · subst hn2
    exact Or.inr (exc5_of_isPSp4_two_two (horb G) hStd hco h)
  · exact Or.inl (nrmE9_Sp4_big h37 h38 hStd hco hZ (by omega) h)

theorem dichE9L3_holds (horb : ∀ (G : Type) [Group G] [Finite G], A3Orbits G)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) : DichE9L3 := by
  intro G _ _ X S L hStd _ hco hZ hty
  rcases hty with ⟨n, hn, h⟩ | hq
  · by_cases hn2 : n = 2
    · subst hn2
      exact Or.inr (exc5_of_isPSL_three_two_two (horb G) hStd hco h)
    · exact Or.inl (nrmE9_L3_big h37 h38 hStd hco hZ (by omega) h)
  · exact Or.inr (exc5_of_isPSL_three_two_two_quot (horb G) hStd hco hq)

theorem famE9_of
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) : FamE9 := by
  have horb : ∀ (G : Type) [Group G] [Finite G], A3Orbits G := fun _ _ _ =>
    a3Orbits_of_a37_a38 h37 h38
  exact famE9_of_dich (dichE9BlockL2_holds horb) (dichE9BlockA5_holds horb) (dichE9L2_holds horb)
    (dichE9Sz_holds h37 h38) (dichE9U3_holds h37 h38) (dichE9L3_holds horb h37 h38)
    (dichE9Sp4_holds horb h37 h38)

end CFSG.Quasithin.E9
