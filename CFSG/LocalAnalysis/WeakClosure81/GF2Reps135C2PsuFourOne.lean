module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuFourLabel

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.RankThreeUC (IsU4Group NaturalU4Mod)
open CFSG.HardMathSupport.U4FF (Lbl disp locM locF1)

theorem w135c2_psu_four_label_one_numerics (l : Lbl 1) (hl0 : ¬ l.IsZero) (hN : ¬ l.SingleN)
    (hO : ¬ l.SingleO) {d : ℕ} (hd : 1 ≤ d) : 7 ≤ d * l.rk1 ∨ (d = 1 ∧ l.dim = 14) := by
  have hdim : l.dim = locM (l.a 0) (l.b 0) (l.c 0) := by simp [Lbl.dim]
  have hfix : l.fix1 = locF1 (l.a 0) (l.b 0) (l.c 0) := by simp [Lbl.fix1]
  have hrk : l.rk1 = (locM (l.a 0) (l.b 0) (l.c 0) - locF1 (l.a 0) (l.b 0) (l.c 0)) / 2 := by
    rw [Lbl.rk1, hdim, hfix]
  have hzero : ∀ i : Fin 1, i ≠ 0 → l.ZeroAt i := fun i hi =>
    absurd (Subsingleton.elim i 0) hi
  rcases ha : l.a 0 with _ | _ <;> rcases hb : l.b 0 with _ | _ <;>
    rcases hc : l.c 0 with _ | _ <;> simp only [ha, hb, hc, locM, locF1] at hdim hrk
  · exact absurd (show l.IsZero from fun i => by fin_cases i; exact ⟨ha, hb, hc⟩) hl0
  · exfalso
    apply hN
    unfold Lbl.SingleN
    exact ⟨0, hzero, hb, Or.inr ⟨ha, hc⟩⟩
  · exfalso
    apply hO
    unfold Lbl.SingleO
    exact ⟨0, hzero, ha, hb, hc⟩
  · norm_num at hrk
    left
    rw [hrk]
    omega
  · exfalso
    apply hN
    unfold Lbl.SingleN
    exact ⟨0, hzero, hb, Or.inl ⟨ha, hc⟩⟩
  · norm_num at hrk
    rcases Nat.lt_or_ge d 2 with h | h
    · right
      exact ⟨by omega, hdim⟩
    · left
      rw [hrk]
      omega
  · norm_num at hrk
    left
    rw [hrk]
    omega
  · norm_num at hrk
    left
    rw [hrk]
    omega

theorem w135c2_psu_four_one_refined
    {S : Type} [CommGroup S]
    [Finite S] [Fact (∀ s : S, s * s = 1)] {L : Subgroup (MulAut S)} (hL : IsU4Group 1 L)
    (hirr : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn L) :
    NaturalU4Mod 1 L ∨ Nat.card S = 2 ^ 14 ∨ ∀ t ∈ L, t ≠ 1 → t * t = 1 → 7 ≤ disp t := by
  rcases w135c2_psu_four_label le_rfl hL hirr with hnat | ⟨d, l, hd, hl0, hsN, hsO, hcard, hrk⟩
  · exact Or.inl hnat
  · rcases w135c2_psu_four_label_one_numerics l hl0 hsN hsO hd with h7 | ⟨rfl, h14⟩
    · exact Or.inr (Or.inr fun t ht ht1 htt => h7.trans (hrk t ht ht1 htt))
    · refine Or.inr (Or.inl ?_)
      rw [hcard, h14]

end CFSG.LocalAnalysis.WeakClosure81
