module

public import CFSG.Quasithin.H13.L32NS8Inputs
public import CFSG.Quasithin.H13.L32NS7Inputs

public section

namespace CFSG.Quasithin.H13.S7Conj

open Mat8Cert

@[expose] def powB : ℕ → List ℕ → ℕ → List ℕ → List ℕ
  | 0, _, _, acc => acc
  | fuel + 1, base, n, acc =>
    powB fuel (mul8 base base) (n / 2) (if n % 2 = 1 then mul8 acc base else acc)

@[expose] def inv8 (x : List ℕ) : List ℕ := powB 10 x 839 one8

@[expose] def c7 : List ℕ := S7Cert.s7G.getD 0 one8

@[expose] def c7P : List (List ℕ) := (List.range 6).map fun k => (mul8 c7)^[k + 1] one8

@[expose] def nE : List (List ℕ × List ℕ) :=
  (S8Cert.s8E.filter fun n => c7P.any fun c => mul8 n c7 == mul8 c n).map fun n => (n, inv8 n)

@[expose] def invs8 : List (List ℕ) :=
  S8Cert.s8E.filter fun x => mul8 x x == one8 && x != one8

@[expose] def orbOf (h : List ℕ) : List (List ℕ) := nE.map fun p => mul8 (mul8 p.1 h) p.2

@[expose] def reps : List (List ℕ) :=
  (invs8.foldl (fun (st : Std.HashSet (List ℕ) × List (List ℕ)) h =>
    if st.1.contains h then st else ((orbOf h).foldl (fun s x => s.insert x) st.1, h :: st.2))
    ((∅ : Std.HashSet (List ℕ)), [])).2

@[expose] def repsH : Std.HashSet (List ℕ) := Std.HashSet.ofList reps

@[expose] def orbB : Bool :=
  invs8.all fun h => nE.any fun p => repsH.contains (mul8 (mul8 p.1 h) p.2)

@[expose] def nB : Bool :=
  nE.all fun p => validB p.2 && mul8 p.1 p.2 == one8 && c7P.any fun c => mul8 p.1 c7 == mul8 c p.1

@[expose] def s8H : Std.HashSet (List ℕ) := Std.HashSet.ofList S8Cert.s8E

@[expose] def s7s8B : Bool := S7Cert.s7G.all fun g => s8H.contains g

@[expose] def s7H : Std.HashSet (List ℕ) := Std.HashSet.ofList S7Cert.s7E

@[expose] def s8EI : List (List ℕ × List ℕ) := S8Cert.s8E.map fun m => (m, inv8 m)

@[expose] def conjB (p : List ℕ × List ℕ) (h : List ℕ) : Bool :=
  validB p.2 && mul8 p.1 p.2 == one8 && s7H.contains (mul8 (mul8 p.1 c7) p.2) &&
    s7H.contains (mul8 (mul8 p.1 h) p.2)

@[expose] def hB (h : List ℕ) : Bool :=
  let L := elemsOf [c7, h] 5041
  L.all validB && nodupB L && L.contains one8 && [c7, h].all validB &&
    (if L.length ≤ 5040 then
      closedB [c7, h] L && (L.length != 5040 || s8EI.any fun p => conjB p h)
    else true)

@[expose] def s7ConjCheck : Bool := s7s8B && nB && orbB && reps.all hB

end CFSG.Quasithin.H13.S7Conj
