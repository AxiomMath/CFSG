module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Open.LocalVocabulary
import CFSG.Quasithin.Background.C41PfI
import CFSG.RankThree.Asc83Table.M22
import CFSG.RankThree.PartTwo.Sec15.Sylow155T51Lift

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

theorem res1Cent_exists_e9_alternatingGroup_seven :
    ∃ E : Subgroup (alternatingGroup (Fin 7)), CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨E, hE, hcard⟩ := CFSG.Quasithin.C41Pf.exists_elemAbelian_alt7
  exact ⟨E, hE, hcard.trans (by norm_num)⟩

theorem res1Cent_exists_e9_m22 :
    ∃ E : Subgroup CFSG.Blueprint.NativeSporadic.M22, CFSG.Open.IsElemAbelian 3 E ∧
      Nat.card E = 9 := by
  obtain ⟨hc, hp⟩ := CFSG.RankThree.Asc83Table.isElementaryAbelian_iff.mp
    CFSG.RankThree.Asc83Table.M22.E.isElementaryAbelian
  exact ⟨_, ⟨⟨⟨fun a b => Subtype.ext (hc _ a.2 _ b.2)⟩⟩, hp⟩,
    CFSG.RankThree.Asc83Table.M22.E.card⟩

theorem res1Cent_exists_e9_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∃ E : Subgroup Y, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9) :
    ∃ E : Subgroup X, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨E, hE, hcard⟩ := h
  obtain ⟨F, hF, hFcard⟩ := CFSG.Quasithin.C41Pf.exists_elemAbelian_of_mulEquiv e
    (p := 3) (k := 2) ⟨E, hE, hcard.trans (by norm_num)⟩
  exact ⟨F, hF, hFcard.trans (by norm_num)⟩

theorem res1Cent_exists_e9_lift {L : Type*} [Group L] [Finite L] (N : Subgroup L) [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N)
    (h : ∃ E : Subgroup (L ⧸ N), CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9) :
    ∃ E : Subgroup L, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨E, hE, hcard⟩ := h
  obtain ⟨S, -, -, hS, hScard⟩ :=
    CFSG.RankThree.PartTwo.Sec15.Sylow155T51.exists_elemAbelian_lift_le N hN
      (A := ⊥) IsPGroup.of_bot hE (by rw [Subgroup.map_bot]; exact bot_le)
  exact ⟨S, hS, hScard.trans hcard⟩

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
