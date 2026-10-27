module

public import CFSG.RankThree.GF2n.Smith81.Bridge
public import CFSG.RankThree.GF2n.Stroth80.Stroth1980Below

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG.RankThree.GF2n.Stroth80

@[expose] def Stroth1980Rel : Prop :=
  ∀ N : ℕ, Smith1981TheoremBelow N → Stroth1980Below N

theorem stroth1980Rel_of_step
    (hstep : ∀ N : ℕ, Stroth1980Below N → Smith1981TheoremBelow N → Stroth1980Below (N + 1)) :
    Stroth1980Rel := by
  intro N
  induction N with
  | zero => exact fun _ => Stroth1980Below.zero
  | succ N ih => exact fun hS => hstep N (ih (hS.mono (Nat.le_succ N))) (hS.mono (Nat.le_succ N))

theorem _root_.CFSG.RankThree.GF2n.Smith81.Smith1981Statement.theoremBelow
    (h : Smith1981Statement) (N : ℕ) : Smith1981TheoremBelow N :=
  fun G _ _ _ M Q Z H B hB hBQ hBZ hC => h G M Q Z H B hB hBQ hBZ hC

theorem stroth1980_of_rel (hR : Stroth1980Rel) (hS : Smith1981Statement) :
    Stroth1980Statement :=
  stroth1980_of_below fun N => hR N (hS.theoremBelow N)

end CFSG.RankThree.GF2n.Smith81
