module

public import CFSG.LargeExtraspecial.O62Check

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LargeExtraspecial.O62 CFSG.LargeExtraspecial.O62.Code CFSG.LargeExtraspecial.O62.Check

@[expose] def s16c1b_gens : List (List ℕ) :=
  [[49, 18], [50, 17], [53, 22], [57, 26], [49, 22], [50, 21]]

@[expose] def s16c1b_invC (w : List ℕ) : ℕ := wordC w.reverse

@[expose] def s16c1b_step (gens l : List ℕ) : List ℕ :=
  gens.foldl (fun acc g => l.foldl (fun acc' x =>
    if acc'.contains (mul g x) then acc' else acc' ++ [mul g x]) acc) l

@[expose] def s16c1b_iter (gens : List ℕ) : ℕ → List ℕ → List ℕ
  | 0, l => l
  | n + 1, l => s16c1b_iter gens n (s16c1b_step gens l)

@[expose] def s16c1b_S0 : List ℕ := s16c1b_iter (s16c1b_gens.map wordC) 6 [one]

@[expose] def s16c1b_okWord (w : List ℕ) : Bool := (w.all fun n => qB true n) && w.length % 2 == 0

@[expose] def s16c1b_A : List (List ℕ) :=
  [[3776990419, 3853274583, 8077724887, 8152960467, 34630287489, 34706571653, 38931021957,
    39006257537],
   [3793765619, 3870049783, 8094238195, 8169997559, 34630287489, 34706571653, 38930760065,
    39006519429],
   [34630287489, 34632122757, 34706571653, 34706833537, 35167158338, 35168993606, 35243442502,
    35243704386]]

@[expose] def s16c1b_checkA : Bool :=
  s16c1b_A.length == 3 &&
    s16c1b_A.all fun a => a.length == 8 && a.contains one &&
      (a.all fun x => s16c1b_S0.contains x && mul x x == one) &&
        a.all fun x => a.all fun y => a.contains (mul x y)

theorem s16c1b_checkA_ok : s16c1b_checkA = true := by decide +kernel

@[expose] def s16c1b_fixMask (c : ℕ) : ℕ :=
  (List.range 64).foldl (fun acc w => if act c w == w then acc ||| (1 <<< w) else acc) 0

@[expose] def s16c1b_tab : List (ℕ × ℕ) :=
  (s16c1b_S0.filter isInv).map fun c => (c, s16c1b_fixMask c)

@[expose] def s16c1b_fixM (c : ℕ) : ℕ :=
  if c == one then 2 ^ 64 - 1 else ((s16c1b_tab.find? fun p => p.1 == c).map Prod.snd).getD 0

@[expose] def s16c1b_prodSub (xs : List ℕ) (I : ℕ) : ℕ :=
  (List.range xs.length).foldl (fun acc i => if I.testBit i then mul acc (xs.getD i 0) else acc) one

@[expose] def s16c1b_par (m I k : ℕ) : Bool :=
  ((List.range k).filter fun i => (I &&& m).testBit i).length % 2 == 1

@[expose] def s16c1b_maskOver (xs : List ℕ) (p : ℕ → Bool) : ℕ :=
  (List.range (2 ^ xs.length)).foldl
    (fun acc I => if p I then acc &&& s16c1b_fixM (s16c1b_prodSub xs I) else acc) (2 ^ 64 - 1)

@[expose] def s16c1b_a2Prop (xs : List ℕ) : Bool :=
  (List.range (2 ^ xs.length)).all fun m => m == 0 ||
    s16c1b_maskOver xs (fun I => !s16c1b_par m I xs.length) ==
      s16c1b_maskOver xs (fun _ => true)

@[expose] def s16c1b_inA (sp : List ℕ) : Bool :=
  s16c1b_A.any fun a => sp.all (a.contains ·) && a.all (sp.contains ·)

@[expose] def s16c1b_extOK (xs : List ℕ) (x : ℕ) : Bool :=
  (xs.all fun y => y < x) && (xs.all fun y => comm x y) && !(spanC xs).contains x

@[expose] def s16c1b_dfs (invs : List ℕ) : ℕ → List ℕ → Bool
  | 0, xs => (xs.isEmpty || !s16c1b_a2Prop xs || s16c1b_inA (spanC xs)) &&
      invs.all fun x => !s16c1b_extOK xs x
  | n + 1, xs => (xs.isEmpty || !s16c1b_a2Prop xs || s16c1b_inA (spanC xs)) &&
      invs.all fun x => !s16c1b_extOK xs x || s16c1b_dfs invs n (x :: xs)

@[expose] def s16c1b_checkClassify : Bool := s16c1b_dfs (s16c1b_S0.filter isInv) 4 []

theorem s16c1b_checkClassify_ok : s16c1b_checkClassify = true := by decide +kernel

@[expose] def s16c1b_orbSize (w : ℕ) : ℕ := ((s16c1b_S0.map fun s => act s w).eraseDups).length

@[expose] def s16c1b_checkOrb : Bool :=
  (List.range 64).all fun w => w == 0 || qB true w || 4 < s16c1b_orbSize w ||
    s16c1b_A.all fun a => a.all fun c => act c w == w

theorem s16c1b_checkOrb_ok : s16c1b_checkOrb = true := by decide +kernel

@[expose] def s16c1b_conjC (n : List ℕ) (c : ℕ) : ℕ := mul (wordC n) (mul c (wordC n.reverse))

@[expose] def s16c1b_sameSet (l l' : List ℕ) : Bool :=
  l.all (l'.contains ·) && l'.all (l.contains ·)

@[expose] def s16c1b_Q : List ℕ := s16c1b_iter (s16c1b_A.flatten.eraseDups) 6 [one]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
