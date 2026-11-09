module

public import Certificates.Data.Kernel.RouteP.TextSplit

public section

namespace CFSG.KC.RouteP

@[expose] def splitSp : List Char → List Char → List (List Char)
  | [], w => [w]
  | c :: cs, w => if c = ' ' then w :: splitSp cs [] else splitSp cs (w ++ [c])

theorem splitSL_space (cs : List Char) :
    ∀ (f b i : Nat) (r : List (List Char)), b ≤ i → i ≤ cs.length → cs.length + 1 ≤ i + f →
      splitSL cs [' '] cs.length f b i 0 r =
        r.reverse ++ splitSp (cs.drop i) ((cs.drop b).take (i - b)) := by
  intro f
  induction f with
  | zero => intro b i r _ hi hf; omega
  | succ f ih =>
    intro b i r hb hi hf
    unfold splitSL
    by_cases hn : cs.length ≤ i
    · have e : i = cs.length := by omega
      subst e
      rw [if_pos hn, List.drop_length]
      simp [splitSp]
    · rw [if_neg hn]
      have hlt : i < cs.length := by omega
      have hd : cs.drop i = cs[i] :: cs.drop (i + 1) := List.drop_eq_getElem_cons hlt
      have hg : cs.getD i 'a' = cs[i] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; rfl
      rw [hg, hd]
      by_cases hc : cs[i] = ' '
      · have hb' : (cs[i] == [' '].getD 0 'a') = true := by rw [hc]; rfl
        rw [if_pos hb', if_pos (by simp), ih (i + 1) (i + 1) _ (Nat.le_refl _) (by omega) (by omega)]
        simp [splitSp, hc, Nat.sub_zero]
      · have hb' : (cs[i] == [' '].getD 0 'a') = false := by
          simp only [List.getD_cons_zero]
          exact beq_false_of_ne hc
        rw [if_neg (by rw [hb']; exact Bool.false_ne_true), Nat.sub_zero,
          ih b (i + 1) r (by omega) (by omega) (by omega)]
        simp only [splitSp, if_neg hc]
        congr 2
        rw [show i + 1 - b = (i - b) + 1 by omega, List.take_succ, List.getElem?_drop,
          show b + (i - b) = i by omega, List.getElem?_eq_getElem hlt]
        rfl

theorem splitSepL_space (cs : List Char) : splitSepL cs [' '] = splitSp cs [] := by
  unfold splitSepL
  rw [splitSL_space cs _ 0 0 [] (Nat.le_refl _) (Nat.zero_le _) (by simp; omega)]
  simp

end CFSG.KC.RouteP

end
