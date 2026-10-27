module

public import Certificates.Data.E6Order3

public section

namespace CFSG.KC.E6Syl3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration.ExcWideThree.E6Order3

@[expose] def tImg (i : ℕ) (t : List ℕ) : List ℕ :=
  t.map fun k => e6Certificate.table.getD k 0 / 256 ^ i % 256

@[expose] def wordT (w t : List ℕ) : List ℕ := w.foldr tImg t

@[expose] def powT (w : List ℕ) : ℕ → List ℕ → List ℕ
  | 0, t => t
  | n + 1, t => wordT w (powT w n t)

@[expose] def qTups (gw : List (List ℕ)) : List (List ℕ) :=
  (List.range 3).flatMap fun a => (List.range 3).flatMap fun b =>
    (List.range 3).flatMap fun c => (List.range 3).map fun d =>
      powT (gw.getD 0 []) a (powT (gw.getD 1 []) b (powT (gw.getD 2 []) c
        (powT (gw.getD 3 []) d (List.range 6))))

@[expose] def nodupB : List (List ℕ) → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && nodupB xs

@[expose] def qCheckWith (gw : List (List ℕ)) (Q : List (List ℕ)) : Bool :=
  gw.all (fun w => w.all fun i => decide (i < 6)) && Q.length == 81 && nodupB Q &&
    Q.contains (List.range 6) && Q.all fun t => gw.all fun w => Q.contains (wordT w t)

@[expose] def rvL (k : ℕ) : List ℤ :=
  (List.range 6).map fun j => (((e6Certificate.roots.getD k 0) / 16 ^ j % 16 : ℕ) : ℤ) - 8

@[expose] def addV (u v : List ℤ) : List ℤ := List.zipWith (· + ·) u v

@[expose] def smulV (c : ℤ) (v : List ℤ) : List ℤ := v.map (c * ·)

@[expose] def negV (v : List ℤ) : List ℤ := v.map (- ·)

@[expose] def zeroV : List ℤ := [0, 0, 0, 0, 0, 0]

@[expose] def eV (j : ℕ) : List ℤ := (List.range 6).map fun i => if i = j then 1 else 0

@[expose] def actV (t : List ℕ) (v : List ℤ) : List ℤ :=
  (List.range 6).foldr (fun j acc => addV (smulV (v.getD j 0) (rvL (t.getD j 0))) acc) zeroV

@[expose] def normV (t : List ℕ) (v : List ℤ) : List ℤ := addV (addV v (actV t v)) (actV t (actV t v))

@[expose] def notOrd3 (t : List ℕ) : Bool :=
  t == List.range 6 || (List.range 6).any fun j => actV t (actV t (actV t (eV j))) != eV j

@[expose] def k3B (t : List ℕ) : Bool := (List.range 6).all fun j => normV t (eV j) == zeroV

@[expose] def sumB (a b c : ℕ) : Bool :=
  decide (a < 72) && decide (b < 72) && decide (c < 72) && rvL c == addV (rvL a) (rvL b)

@[expose] def kA2B (t : List ℕ) (a b c : ℕ) : Bool :=
  sumB a b c && (List.range 6).all fun j => t.getD j 0 == reflIdx 72 a (reflIdx 72 b j)

@[expose] def cpL (a j : ℕ) : ℤ := (rvL a).getD j 0 - (rvL (imgN a j)).getD j 0

@[expose] def k2B (t : List ℕ) (a b c m : ℕ) : Bool :=
  sumB a b c && decide (m < 72) && actV t (rvL a) == rvL a && actV t (rvL b) == rvL b &&
    (List.range 72).all (fun k => actV t (rvL k) != rvL k || rvL k == rvL a ||
      rvL k == negV (rvL a) || rvL k == rvL b || rvL k == negV (rvL b) || rvL k == rvL c ||
      rvL k == negV (rvL c)) &&
    normV t (rvL m) == addV (smulV 2 (rvL a)) (rvL b) &&
    (List.range 6).all fun j => normV t (eV j) ==
      addV (smulV (2 * cpL a j + cpL b j) (rvL a)) (smulV (cpL a j + 2 * cpL b j) (rvL b))

@[expose] def kindOK (t : List ℕ) (c : List ℕ) : Bool :=
  match c with
  | [0] => notOrd3 t
  | [1] => k3B t
  | [2, a, b, d] => kA2B t a b d
  | [3, a, b, d, m] => k2B t a b d m
  | _ => false

@[expose] def kindsCheck (Q : List (List ℕ)) (W : List (List ℕ)) : Bool :=
  Q.length == W.length && (Q.zip W).all fun p => kindOK p.1 p.2

end CFSG.KC.E6Syl3
