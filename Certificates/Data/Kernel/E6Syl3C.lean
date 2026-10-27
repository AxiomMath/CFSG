module

public import Certificates.Data.Kernel.E6Syl3P
public import Certificates.Data.E6CaseI

public section

namespace CFSG.KC.E6Syl3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.LieType.SeitzGeneration.ExcWideThree.E6Order3

@[expose] def n3 (k : ℕ) : ℤ := node3 k

@[expose] def fixN3 (t : List ℕ) : Bool :=
  (List.range 72).all fun k => ((actV t (rvL k)).getD 3 0 - n3 k) % 3 == 0

@[expose] def genN3 (gw : List (List ℕ)) : Bool :=
  gw.all fun w => fixN3 (wordT w (List.range 6))

@[expose] def divB (a b d : ℕ) : Bool := n3 a % 3 == 0 && n3 b % 3 == 0 && n3 d % 3 == 0

@[expose] def noneB (a b d : ℕ) : Bool := n3 a % 3 != 0 && n3 b % 3 != 0 && n3 d % 3 != 0

@[expose] def idxV (v : List ℤ) : ℕ := ((List.range 72).filter fun k => rvL k == v).headD 72

@[expose] def orthC (b x y : ℕ) : Bool :=
  reflIdx 72 b x == x && reflIdx 72 b y == y && reflIdx 72 x y == y

@[expose] def tauB (t : List ℕ) (a : ℕ) : Bool :=
  (List.range 729).all fun n => n == 0 ||
    !(chiTestL .E6 (RootTables.ofCert e6Certificate) (digits3 .E6 n) t) ||
    !(killBit (RootTables.ofCert e6Certificate) a n) ||
    killCount (RootTables.ofCert e6Certificate) n == 18 ||
    (List.range 72).any fun b => n3 b % 3 == 0 && killBit (RootTables.ofCert e6Certificate) b n &&
      (let x := idxV (actV t (rvL b))
       let y := idxV (actV t (rvL x))
       decide (x < 72) && decide (y < 72) && orthC b x y)

@[expose] def caseIEl (t : List ℕ) (c : List ℕ) : Bool :=
  match c with
  | [3, a, b, d, _] => divB a b d || (noneB a b d && tauB t a)
  | _ => true

@[expose] def caseIElems (Q W : List (List ℕ)) : Bool :=
  Q.length == W.length && (Q.zip W).all fun p => caseIEl p.1 p.2

@[expose] def is2Div (kw : List (List ℕ)) (x : ℕ) : Bool :=
  match kw.getD x [] with
  | [3, a, b, d, _] => divB a b d
  | _ => false

@[expose] def badC (Q kw lt wd : List (List ℕ)) (i j : ℕ) (e : List ℕ) : Bool :=
  match e with
  | [i', j', r, a, b, c, d] =>
    i' == i && j' == j && decide (r < 72) && n3 r % 3 == 0 &&
      actV (Q.getD i []) (rvL r) == rvL r && actV (Q.getD j []) (rvL r) == rvL r &&
      (a * d + 2 * (b * c)) % 3 != 0 && is2Div kw (gEl lt wd i j a b) &&
      is2Div kw (gEl lt wd i j c d)
  | _ => false

@[expose] def caseIPairs (Q kw lt wd : List (List ℕ)) (o3 : List ℕ) (cw : List (List ℕ)) : Bool :=
  o3.all fun i => o3.all fun j =>
    !(commI lt wd i j && j != i && j != powI lt wd i 2) || has3 kw lt wd i j ||
      cw.any (badC Q kw lt wd i j)

end CFSG.KC.E6Syl3
