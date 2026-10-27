module

public import CFSG.Quasithin.H13.GoldschmidtC137SQSimp
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13

public section

namespace CFSG.Quasithin.H13.U3.GC137.SQ

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.SectionRank

theorem statedClassicalModel_of_lieModel_psl {Y : Type} [Group Y] {n p f : ℕ} (hn : n ≠ 0)
    (h : LieModel Y .PSL n p f) : StatedClassicalModel Y .PSL n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero hn h

theorem simple_card_of_lieModel_psl_three_two {Y : Type} [Group Y] (h : LieModel Y .PSL 3 2 1) :
    IsSimpleGroup Y ∧ Nat.card Y = 168 := by
  have hm := statedClassicalModel_of_lieModel_psl (by norm_num) h
  refine ⟨?_, ?_⟩
  · obtain ⟨⟨-, -, hn, -, -⟩, F, _, _, hF, ⟨e⟩⟩ := hm
    have e' : Y ≃* StatedProj (StatedSL 3 F) := e
    have hs := CFSG.BenderSuzuki.External.huppert_II_6_13 (K := F) 3 hn
      (Or.inl (by norm_num)) (Or.inl (by norm_num))
    exact (e'.trans (projectiveSpecialLinearGroupEquivStatedProj 3 F).symm).isSimpleGroup
  · rw [(CFSG.Timmesfeld.card_statedClassicalModel_two (t := .PSL) (n := 3) (f := 1) hm).1 rfl]
    decide

theorem isKGroupCat_of_lieModel_psl_three_two {Y : Type} [Group Y] [Finite Y]
    (h : LieModel Y .PSL 3 2 1) : IsKGroupCat Y := by
  obtain ⟨hs, hcard⟩ := simple_card_of_lieModel_psl_three_two h
  exact isKGroupCat_of_card_168 hcard (lieModel_catalog Y .PSL 3 2 1 h)

end CFSG.Quasithin.H13.U3.GC137.SQ
