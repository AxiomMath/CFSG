module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432SylowCountMain
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Refine
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.ThetaSpor.HeThree

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.Blueprint CFSG.Sporadic.HeldB CFSG.AGLEmbeddingD2.Wilson.ThetaSpor.He

@[expose] noncomputable def heClassA : ↥heP := ⟨bOf heThreeWordsA, bOf_mem⟩

@[expose] noncomputable def heClassB : ↥heP := ⟨bOf heThreeWordsB, bOf_mem⟩

theorem card_centralizer_heClassA :
    Nat.card (Subgroup.centralizer ({heClassA} : Set ↥heP)) = 7560 :=
  (Nat.card_congr (heCentralizerEquiv heClassA).toEquiv).trans card_cent_A

theorem card_centralizer_heClassB :
    Nat.card (Subgroup.centralizer ({heClassB} : Set ↥heP)) = 504 :=
  (Nat.card_congr (heCentralizerEquiv heClassB).toEquiv).trans card_cent_B

theorem sylowThreeData_heP :
    SylowThreeData ↥heP heClassA heClassB 149273600 56 where
  card := by
    rw [card_heP]
  card_mod := by norm_num
  orderA := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_bOf bigDataA
  orderB := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_bOf bigDataB
  centB := by
    rw [card_centralizer_heClassB]
  centB_mod := by norm_num
  cover := by
    intro z hz
    have hz' : orderOf (z : Equiv.Perm (Fin 8330)) = 3 := by
      rw [Subgroup.orderOf_coe]
      exact hz
    rcases three_conj_cases z.2 hz' with ⟨c, hc, hzc⟩ | ⟨c, hc, hzc⟩
    · exact Or.inl (isConj_iff.2 ⟨⟨c, hc⟩, Subtype.ext hzc.symm⟩)
    · exact Or.inr (isConj_iff.2 ⟨⟨c, hc⟩, Subtype.ext hzc.symm⟩)
  disj := by
    intro h
    have := card_centralizer_eq_of_isConj h
    rw [card_centralizer_heClassA, card_centralizer_heClassB] at this
    omega

theorem listRow_heP :
    ListRow ↥heP :=
  listRow_of_sylowThreeData sylowThreeData_heP

theorem listRowOf_he :
    ListRowOf (NativeSporadic.Carrier .He) := by
  intro S _ _ _ _ ⟨e⟩
  have e' : S ≃* heP := e.trans heEquivP
  exact ListRow.of_mulEquiv e'.symm listRow_heP

end CFSG.RankThree.PartTwo.Sec4.RonanK432
