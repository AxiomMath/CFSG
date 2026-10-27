module

public import CFSG.Quasithin.H13.L32NKGCertInputs
public import CFSG.Quasithin.Recognition.RuTypeDefs

public section

namespace CFSG.Quasithin.H13.Sp4Cert

open KGCert

@[expose] def bJ (u w : ℕ) : Bool := bfN 12 u w

@[expose] def isSympC (x : List ℕ) : Bool :=
  (List.range 4).all fun i => (List.range 4).all fun j =>
    bJ (x.getD i 0) (x.getD j 0) == bJ (2 ^ i) (2 ^ j)

@[expose] def spElsC : List (List ℕ) :=
  (List.range 16).flatMap fun a => (List.range 16).flatMap fun b =>
    (List.range 16).flatMap fun c => (List.range 16).filterMap fun d =>
      if isSympC [a, b, c, d] then some [a, b, c, d] else none

@[expose] def codeC (x : List ℕ) : ℕ :=
  x.getD 0 0 + 16 * x.getD 1 0 + 256 * x.getD 2 0 + 4096 * x.getD 3 0

@[expose] def oneC4 : List ℕ := [1, 2, 4, 8]

@[expose] def memM (m : ℕ) (x : List ℕ) : Bool := m.testBit (codeC x)

@[expose] def addM (m : ℕ) (x : List ℕ) : ℕ := m ||| (1 <<< codeC x)

@[expose] def maskOf (s : List (List ℕ)) : ℕ := s.foldl addM 0

@[expose] def subM (m m' : ℕ) : Bool := m &&& m' == m

@[expose] def bfs (gens : List (List ℕ)) : ℕ → List (List ℕ) → ℕ → List (List ℕ) →
    List (List ℕ) × ℕ
  | 0, _, m, acc => (acc, m)
  | _ + 1, [], m, acc => (acc, m)
  | n + 1, a :: fr, m, acc =>
    let step := gens.foldl (fun (p : List (List ℕ) × ℕ) g =>
      let b := mulC a g
      if memM p.2 b then p else (b :: p.1, addM p.2 b)) ([], m)
    bfs gens n (fr ++ step.1) step.2 (step.1 ++ acc)

@[expose] def closeC (gens : List (List ℕ)) : List (List ℕ) × ℕ :=
  bfs gens 2000 [oneC4] (addM 0 oneC4) [oneC4]

structure Node where
  els : List (List ℕ)
  gens : List (List ℕ)
  mask : ℕ
  reps : List (List ℕ)

@[expose] def validB (x : List ℕ) : Bool := x.length == 4 && x.all (· < 16)

@[expose] def x5C : List ℕ := [2, 8, 3, 14]

@[expose] def a9C : List ℕ := [1, 4, 6, 8]

@[expose] def b9C : List ℕ := [8, 2, 4, 9]

@[expose] def tiLinesC : List (List ℕ) :=
  (List.range 16).flatMap fun u => (List.range 16).filterMap fun v =>
    if 0 < u && 0 < v && u != v && !bJ u v then some [u, v, u ^^^ v] else none

@[expose] def isNT (x l : List ℕ) : Bool := l.any fun y => mulVecC x y != y

@[expose] def ord3 (x : List ℕ) : Bool := x != oneC4 && mulC x (mulC x x) == oneC4

@[expose] def invl (x : List ℕ) : Bool := x != oneC4 && mulC x x == oneC4

@[expose] def nrmL (els : List (List ℕ)) (l : List ℕ) : List (List ℕ) :=
  els.filter fun x => l.all fun y => l.contains (mulVecC x y)

@[expose] def fixL (els : List (List ℕ)) (l : List ℕ) : List (List ℕ) :=
  els.filter fun x => l.all fun y => mulVecC x y == y

@[expose] def feasible (els : List (List ℕ)) (l : List ℕ) : Bool :=
  let N := nrmL els l
  N.length % Nat.gcd els.length 16 == 0 && N.any (fun x => ord3 x && isNT x l) &&
    N.length < els.length && N.any (fun x => invl x && isNT x l)

@[expose] def psiC (v : ℕ) : ℕ × ℕ :=
  let p := fun (i : ℕ) (a : ℕ × ℕ) (acc : ℕ × ℕ) =>
    if v.testBit i then (acc.1 ^^^ a.1, acc.2 ^^^ a.2) else acc
  p 0 (1, 0) (p 1 (0, 1) (p 2 (2, 1) (p 3 (1, 3) (0, 0))))

@[expose] def f4m (x y : ℕ) : ℕ :=
  let a0 := x % 2
  let a1 := x / 2
  let b0 := y % 2
  let b1 := y / 2
  (a0 * b0 + a1 * b1) % 2 + 2 * ((a0 * b1 + a1 * b0 + a1 * b1) % 2)

@[expose] def frobC (x : ℕ) : ℕ := f4m x x

@[expose] def psiInv (w : ℕ × ℕ) : ℕ := ((List.range 16).find? fun v => psiC v == w).getD 0

@[expose] def semC (d : List ℕ) : (ℕ × ℕ) × (ℕ × ℕ) × ℕ :=
  let c1 := psiC (mulVecC d (psiInv (1, 0)))
  let c2 := psiC (mulVecC d (psiInv (0, 1)))
  let ok0 := (List.range 16).all fun v => let w := psiC v
    psiC (mulVecC d v) == (f4m c1.1 w.1 ^^^ f4m c2.1 w.2, f4m c1.2 w.1 ^^^ f4m c2.2 w.2)
  (c1, c2, if ok0 then 0 else 1)

@[expose] def semOk (d : List ℕ) : Bool :=
  let c := semC d
  (List.range 16).all (fun v => let w := psiC v
    let w' := if c.2.2 == 0 then w else (frobC w.1, frobC w.2)
    psiC (mulVecC d v) ==
      (f4m c.1.1 w'.1 ^^^ f4m c.2.1.1 w'.2, f4m c.1.2 w'.1 ^^^ f4m c.2.1.2 w'.2)) &&
  (f4m c.1.1 c.2.1.2 ^^^ f4m c.2.1.1 c.1.2) == 1

@[expose] def pts : List (ℕ × ℕ) := [(1, 0), (0, 1), (1, 1), (1, 2), (1, 3)]

@[expose] def ptIdx (w : ℕ × ℕ) : ℕ :=
  (pts.findIdx? fun p => (List.range 4).any fun c => c != 0 && (f4m c p.1, f4m c p.2) == w).getD 0

@[expose] def permC (d : List ℕ) : List ℕ := pts.map fun p => ptIdx (psiC (mulVecC d (psiInv p)))

@[expose] def compP (p q : List ℕ) : List ℕ := q.map fun i => p.getD i 0

@[expose] def qJ (a v : ℕ) : Bool := qfN 12 a v

structure Spec where
  a36 : List (List ℕ) × ℕ
  b36 : List (List ℕ) × ℕ
  s36 : List (List ℕ) × ℕ
  s120 : List (List ℕ) × ℕ
  m60 : ℕ

@[expose] def closedB (l : List (List ℕ)) : Bool :=
  l.all fun x => l.all fun y => l.contains (mulC x y)

@[expose] def permOk (l : List (List ℕ)) : Bool :=
  let P := l.map fun d => (d, permC d)
  P.all (fun d => P.all fun e => permC (mulC d.1 e.1) == compP d.2 e.2) &&
  P.all (fun d => d.2 != [0, 1, 2, 3, 4] || d.1 == oneC4) &&
  P.all (fun d => d.2.all (· < 5) && d.2.Nodup)

@[expose] def f4c (c : ℕ) : RuType.F4 := ⟨⟨c % 4, Nat.mod_lt _ (by norm_num)⟩⟩

@[expose] def psi4 (v : ℕ) : Fin 2 → RuType.F4 := ![f4c (psiC v).1, f4c (psiC v).2]

@[expose] def matC (d : List ℕ) : Matrix (Fin 2) (Fin 2) RuType.F4 :=
  let c := semC d
  !![f4c c.1.1, f4c c.2.1.1; f4c c.1.2, f4c c.2.1.2]

@[expose] def phiC (d : List ℕ) : RuType.SigmaL2F4 :=
  if h : (matC d).det = 1 then ⟨⟨matC d, h⟩, Multiplicative.ofAdd ((semC d).2.2 : ZMod 2)⟩ else 1

@[expose] def permFunL (p : List ℕ) (i : Fin 5) : Fin 5 :=
  ⟨p.getD i 0 % 5, Nat.mod_lt _ (by norm_num)⟩

@[expose] def permInvL (p : List ℕ) (j : Fin 5) : Fin 5 :=
  ((List.finRange 5).find? fun i => permFunL p i = j).getD 0

@[expose] def PermCond (p : List ℕ) : Prop :=
  (∀ i, permInvL p (permFunL p i) = i) ∧ ∀ j, permFunL p (permInvL p j) = j

instance (p : List ℕ) : Decidable (PermCond p) := inferInstanceAs (Decidable (_ ∧ _))

@[expose] def permOfList (p : List ℕ) : Equiv.Perm (Fin 5) :=
  if h : PermCond p then ⟨permFunL p, permInvL p, h.1, h.2⟩ else 1

@[expose] def permF (d : List ℕ) : Equiv.Perm (Fin 5) := permOfList (permC d)

@[expose] def powC (x : List ℕ) : ℕ → List ℕ
  | 0 => oneC4
  | n + 1 => mulC (powC x n) x

@[expose] def p9C : List (List ℕ) × ℕ := closeC [a9C, b9C]

@[expose] def specialChecks (sp : Spec) : List Bool :=
  [sp.a36.1.length == 6, sp.b36.1.length == 6, sp.s36.1.length == 36,
    decide sp.a36.1.Nodup, decide sp.b36.1.Nodup, decide sp.s36.1.Nodup,
    decide sp.s120.1.Nodup,
    sp.a36.2 == maskOf sp.a36.1, sp.b36.2 == maskOf sp.b36.1,
    sp.s36.2 == maskOf sp.s36.1, sp.s120.2 == maskOf sp.s120.1,
    sp.a36.1.any (fun x => sp.a36.1.any fun y => mulC x y != mulC y x),
    sp.b36.1.any (fun x => sp.b36.1.any fun y => mulC x y != mulC y x),
    sp.a36.1.all (fun x => sp.b36.1.all fun y => mulC x y == mulC y x),
    sp.a36.1.all (fun x => !memM sp.b36.2 x || x == oneC4),
    sp.a36.1.all validB, sp.b36.1.all validB, sp.s36.1.all validB, sp.s120.1.all validB,
    closedB sp.a36.1, closedB sp.b36.1, sp.a36.1.contains oneC4, sp.b36.1.contains oneC4,
    sp.a36.1.all (memM sp.s36.2), sp.b36.1.all (memM sp.s36.2),
    closedB (sp.s120.1.filter fun d => memM sp.m60 d),
    (List.range 16).all (fun v => (psiC v).1 < 4 && (psiC v).2 < 4),
    sp.s120.1.length == 120, sp.s120.1.all semOk,
    sp.m60 == maskOf (sp.s120.1.filter fun d => (semC d).2.2 == 0),
    (sp.s120.1.filter fun d => memM sp.m60 d).length == 60,
    (List.range 16).all (fun v => (List.range 16).all fun w => psiC v != psiC w || v == w),
    permOk sp.s120.1,
    decide (∀ d ∈ sp.s120.1, ∀ v ∈ List.range 16,
      psi4 (mulVecC d v) = RuType.sigmaAct (phiC d) (psi4 v)),
    decide (∀ x ∈ List.range 16, ∀ y ∈ List.range 16, psi4 (x ^^^ y) = psi4 x + psi4 y),
    decide (∀ x ∈ List.range 16, ∀ y ∈ List.range 16, psi4 x = psi4 y → x = y),
    decide (∀ d ∈ sp.s120.1, PermCond (permC d)),
    sp.s120.1.all (fun x => sp.s120.1.all fun y => memM sp.s120.2 (mulC x y)),
    decide (∀ d ∈ sp.s120.1, permF d = 1 → d = oneC4),
    decide (∀ d ∈ sp.s120.1, (phiC d).right = 1 → Equiv.Perm.sign (permF d) = 1),
    decide (∀ d ∈ sp.s120.1, memM sp.m60 d = decide ((phiC d).right = 1)),
    p9C.1.length == 9, decide p9C.1.Nodup, p9C.1.all validB, closedB p9C.1,
    p9C.1.contains oneC4, p9C.2 == maskOf p9C.1, p9C.1.all (fun x => sp.s36.1.contains x),
    sp.s36.1.all (fun g => p9C.1.all fun x => p9C.1.any fun y => mulC g x == mulC y g),
    sp.s36.1.all (fun x => !(ord3 x) || p9C.1.contains x),
    p9C.1.all (fun x => p9C.1.all fun y => mulC x y == mulC y x),
    p9C.1.all (fun x => mulC x (mulC x x) == oneC4),
    spElsC.all (fun x => powC x 9 != oneC4 || mulC x (mulC x x) == oneC4)]

@[expose] def specialOk (sp : Spec) : Bool := (specialChecks sp).all id

@[expose] def concl (sp : Spec) (s : Node) (l : List ℕ) : Bool :=
  let n := s.els.length
  let N := nrmL s.els l
  let F := fixL s.els l
  n == 18 ||
  (n == 36 && s.mask == sp.s36.2 && F.length == 2 &&
    ((F.all (memM sp.a36.2) && N.all fun x => !(memM sp.a36.2 x && ord3 x && isNT x l)) ||
     (F.all (memM sp.b36.2) && N.all fun x => !(memM sp.b36.2 x && ord3 x && isNT x l)))) ||
  (n == 120 && s.mask == sp.s120.2 && F.all (memM sp.m60) &&
    N.all fun x => !(invl x && isNT x l) ||
      (F.filter fun f => mulC f x == mulC x f).length == 2) ||
  (n == 360 && F.length == 4) ||
  (n == 720 && F.length == 8 && s.els.all fun y => !(F.all fun f => mulC f y == mulC y f) ||
    F.contains y)

@[expose] def lineOk (sp : Spec) (L : List Node) : Bool :=
  L.all fun s => tiLinesC.all fun l => !feasible s.els l || concl sp s l

@[expose] def quadOk (sp : Spec) (L : List Node) : Bool :=
  L.all fun s => !(s.mask == sp.s120.2 || 360 ≤ s.els.length) ||
    (List.range 16).all fun a => tiLinesC.all fun l => !(l.all fun y => !qJ a y) ||
      s.els.any fun d => (List.range 16).any fun v => qJ a (mulVecC d v) != qJ a v

end CFSG.Quasithin.H13.Sp4Cert
