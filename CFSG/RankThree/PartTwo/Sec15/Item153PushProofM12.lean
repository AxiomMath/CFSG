module

public import CFSG.RankThree.PartTwo.Sec15.Item153PushProof
public import CFSG.RankThree.PartTwo.Sec15.Item157Proof
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.KFacts.KS14PGL
public import CFSG.Sporadic.Mathieu.M12

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

theorem isEmpty_m12_alternating :
    IsEmpty (CFSG.Blueprint.NativeSporadic.M12 ≃* alternatingGroup (Fin 5)) ∧
      IsEmpty (CFSG.Blueprint.NativeSporadic.M12 ≃* alternatingGroup (Fin 7)) ∧
      IsEmpty (CFSG.Blueprint.NativeSporadic.M12 ≃* alternatingGroup (Fin 10)) := by
  have key : ∀ n : ℕ, 2 ≤ n → n.factorial / 2 ≠ 95040 →
      IsEmpty (CFSG.Blueprint.NativeSporadic.M12 ≃* alternatingGroup (Fin n)) := by
    intro n hn hne
    refine ⟨fun e => hne ?_⟩
    have h := Nat.card_congr e.toEquiv
    rw [KFacts.KS14.card_nativeM12, KFacts.KS14.card_alternatingGroup_fin hn] at h
    exact h.symm
  exact ⟨key 5 (by norm_num) (by decide), key 7 (by norm_num) (by decide),
    key 10 (by norm_num) (by decide)⟩

theorem step153PushM12R_of_item157
    (h137 : Item137) (h142 : Item142AllS14) (h134 : Item134) (h135 : Item135)
    (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) (h148 : Item148R) : Step153PushM12R := by
  intro G _ _ A c L hR Y hY S _ _ _ _ hM
  obtain ⟨e⟩ := hM
  have h157 := rank3II_15_7_of_item142 h137 h142 h134 h135 h48 h415
    (KFacts.KS14.center_nativeJ2_eq_bot h415) KFacts.KS14.ks15Z3PGLNonabelian
    CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
    (fun p f _ => KFacts.KS14.not_isLThreeEpsAt_M12 p f) isEmpty_m12_alternating hR
    (h148 G A c L hR)
  exact ((h157 Y hY).false e).elim

end CFSG.RankThree.PartTwo.Sec15
