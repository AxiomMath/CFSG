module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check45Inputs
public meta import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Check45Inputs

public section

namespace CFSG.RankThree.PartTwo.Sec14.Wales1411W.ModelJ2

open CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover
  CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.RankThree.Native

@[expose] def et2Word (gs : Array (Array ℕ)) (w : List ℕ) : Array ℕ :=
  w.foldr (fun l t => compA 315 gs[l]! t) (idA 315)

@[expose] def et2GensWV (i : ℕ) : Array (Array ℕ) :=
  #[wg i 0, wg i 1, vkArr ((i + 2) % 3) 1, vkArr ((i + 2) % 3) 2]

@[expose] def et2GensVV : Array (Array ℕ) :=
  #[vkArr 0 1, vkArr 0 2, vkArr 1 1, vkArr 1 2, vkArr 2 1, vkArr 2 2]

@[expose] def et2GensWW (i j : ℕ) : Array (Array ℕ) := #[wg i 0, wg i 1, wg j 0, wg j 1]

@[expose] def et2YWords : List (List ℕ) :=
  [[2, 0, 1, 3, 1, 2, 0, 2, 0, 3, 0, 1, 3, 0, 1, 2, 3],
    [2, 1, 3, 0, 2, 0, 2, 1, 2, 1, 2, 0, 3, 1, 2],
    [2, 0, 3, 1, 2, 1, 2, 0, 2, 0, 2, 1, 3, 0, 2]]

@[expose] def et2YVWord : List ℕ := [1, 5, 2, 1, 5, 2, 1, 5]

@[expose] def et2NPairs : List (ℕ × ℕ) := [(0, 1), (0, 2), (1, 0), (1, 2), (2, 0), (2, 1)]

@[expose] def et2NWord (i j : ℕ) : List ℕ :=
  if i = 0 ∧ j = 1 then [1, 2, 1] else if i = 0 ∧ j = 2 then [2, 0, 1, 2]
  else if i = 1 ∧ j = 0 then [0, 3, 0] else if i = 1 ∧ j = 2 then [1, 2, 1]
  else if i = 2 ∧ j = 0 then [0, 2, 3, 0] else [0, 3, 0]

@[expose] def et2YWV : Bool :=
  [0, 1, 2].all fun i => (et2YWords.getD i []).all (· < 4) &&
    eqA 315 yArr (et2Word (et2GensWV i) (et2YWords.getD i []))

@[expose] def et2YVV : Bool :=
  et2YVWord.all (· < 6) && eqA 315 yArr (et2Word et2GensVV et2YVWord)

@[expose] def et2NFacts (i j c : ℕ) (n : Array ℕ) : Bool :=
  validA 315 n && inE 0 (conjA 315 n zArr) && inE 0 (conjA 315 n xArr) &&
    inW j (conjA 315 n (wg i 0)) && inW j (conjA 315 n (wg i 1)) &&
    inW i (conjInvA 315 n (wg j 0)) && inW i (conjInvA 315 n (wg j 1)) &&
    inVk c (conjA 315 n (vkArr c 1)) && inVk c (conjA 315 n (vkArr c 2)) &&
    inVk c (conjInvA 315 n (vkArr c 1)) && inVk c (conjInvA 315 n (vkArr c 2))

@[expose] def et2NOK (i j c : ℕ) (w : List ℕ) : Bool :=
  w.all (· < 4) && et2NFacts i j c (et2Word (et2GensWW i j) w)

@[expose] def et2ChkN : Bool :=
  et2NPairs.all fun p => et2NOK p.1 p.2 ((8 - p.1 - p.2) % 3) (et2NWord p.1 p.2)

end CFSG.RankThree.PartTwo.Sec14.Wales1411W.ModelJ2
