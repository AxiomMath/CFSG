module

public import CFSG.Monster.B.Mathieu.ChainCheck

public section

namespace CFSG.Monster.B.Mathieu

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

@[expose] def powArr (n : ℕ) (t : Array ℕ) : ℕ → Array ℕ
  | 0 => idA n
  | k + 1 => compA n t (powArr n t k)

@[expose] def permArrOK (n : ℕ) (t : Array ℕ) : Bool := t.size == n && isInvA n t (invCand n t)

@[expose] def pvalAux (p : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, m => if 1 < p ∧ m ≠ 0 ∧ m % p = 0 then pvalAux p fuel (m / p) + 1 else 0

@[expose] def pval (p m : ℕ) : ℕ := pvalAux p m m

@[expose] def bfsStep (n : ℕ) (gens : Array (Array ℕ)) (limit : ℕ) (i : ℕ)
    (st : Array (Array ℕ) × Array ℕ × Array ℕ × Std.HashMap (List ℕ) ℕ) :
    Array (Array ℕ) × Array ℕ × Array ℕ × Std.HashMap (List ℕ) ℕ :=
  (List.range gens.size).foldl (fun acc k =>
    let (pts, par, lab, idx) := acc
    let y := compA n gens[k]! pts[i]!
    if idx.contains y.toList || limit ≤ pts.size then acc
    else (pts.push y, par.push i, lab.push k, idx.insert y.toList pts.size)) st

@[expose] def bfsLoop (n : ℕ) (gens : Array (Array ℕ)) (limit : ℕ) :
    ℕ → ℕ → Array (Array ℕ) × Array ℕ × Array ℕ × Std.HashMap (List ℕ) ℕ →
      Array (Array ℕ) × Array ℕ × Array ℕ × Std.HashMap (List ℕ) ℕ
  | 0, _, st => st
  | fuel + 1, i, st =>
    if i < st.1.size then bfsLoop n gens limit fuel (i + 1) (bfsStep n gens limit i st) else st

@[expose] def bfsGroup (n : ℕ) (gens : Array (Array ℕ)) (limit : ℕ) :
    Array (Array ℕ) × Array ℕ × Array ℕ :=
  let st := bfsLoop n gens limit limit 0
    (#[idA n], #[0], #[0], (∅ : Std.HashMap (List ℕ) ℕ).insert (idA n).toList 0)
  (st.1, st.2.1, st.2.2.1)

@[expose] def sylowWords (m : ℕ) (par lab : Array ℕ) : Array (List ℤ) :=
  Array.replicate m [] ++ Array.ofFn (n := par.size) fun i =>
    if i.val = 0 then [] else [(lab[i.val]! : ℤ) + 1, ((m + par[i.val]! : ℕ) : ℤ) + 1]

@[expose] def fullBase (n : ℕ) : Array ℕ := (List.range n).toArray

@[expose] def conjArr (n : ℕ) (O : Array (Array ℕ)) (x : Array ℕ) (w : List ℤ) : Array ℕ :=
  let g := wordA n O (rawInvs n O) w
  compA n (invCand n g) (compA n x g)

@[expose] def normalGenCheck (n N : ℕ) (O : Array (Array ℕ)) (ng : NormalGenRecord) : Bool :=
  ng.conjugators.all (fun w => lettersOK O.size w) && ng.chain.check n &&
    (ng.chain.orbitSizes n).prod == N && ng.chain.generators.length == ng.conjugators.length &&
    (List.zip ng.chain.generators ng.conjugators).all fun aw =>
      let g := wordA n O (rawInvs n O) aw.2
      isInvA n g (invCand n g) && eqA n aw.1.toArray (conjArr n O ng.representative.toArray aw.2)

@[expose] def repCheck (n p : ℕ) (pts : Array (Array ℕ)) (x : Array ℕ) : Bool :=
  permArrOK n x && pts.any (fun y => eqA n y x) && !eqA n x (idA n) &&
    eqA n (powArr n x p) (idA n) &&
    (List.range p).all fun j => j == 0 || decide (x.toList ≤ (powArr n x j).toList)

@[expose] def coverCheck (n p : ℕ) (reps : Array (Array ℕ)) (y : Array ℕ) : Bool :=
  eqA n y (idA n) || !eqA n (powArr n y p) (idA n) ||
    (List.range p).any fun j => j != 0 && reps.any fun x => eqA n (powArr n y j) x

@[expose] def SylowRecord.genArrs (s : SylowRecord) : Array (Array ℕ) :=
  (s.generators.map List.toArray).toArray

@[expose] def SylowRecord.repArrs (s : SylowRecord) : Array (Array ℕ) :=
  (s.normalGeneration.map fun ng => ng.representative.toArray).toArray

@[expose] def SylowRecord.exponent (s : SylowRecord) (N : ℕ) : ℕ := pval s.prime N

@[expose] def SylowRecord.enum (s : SylowRecord) (n N : ℕ) :
    Array (Array ℕ) × Array ℕ × Array ℕ :=
  bfsGroup n s.genArrs (s.prime ^ s.exponent N + 1)

@[expose] def SylowRecord.elems (s : SylowRecord) (n N : ℕ) : Array (Array ℕ) := (s.enum n N).1

@[expose] def SylowRecord.strongArrs (s : SylowRecord) (n N : ℕ) : Array (Array ℕ) :=
  s.genArrs ++ s.elems n N

@[expose] def SylowRecord.wordArrs (s : SylowRecord) (n N : ℕ) : Array (List ℤ) :=
  sylowWords s.genArrs.size (s.enum n N).2.1 (s.enum n N).2.2

@[expose] def sylowCheck (n N : ℕ) (c : ChainRecord) (s : SylowRecord) : Bool :=
  let p := s.prime
  let k := s.exponent N
  s.genArrs.all (fun a => permArrOK n a &&
      siftA n (rawLevels n c.strongArrs c.baseArr) c.baseArr 0 a) &&
    arraysOK n s.genArrs (s.strongArrs n N) (fullBase n) (s.wordArrs n N) &&
    (rawOrbitSizes n (s.strongArrs n N) (fullBase n)).prod == p ^ k &&
    (s.elems n N).size == p ^ k && (s.elems n N).all (permArrOK n) &&
    decide ((s.elems n N).toList.map Array.toList : List (List ℕ)).Nodup &&
    N % p ^ k == 0 && N % p ^ (k + 1) != 0 &&
    decide (s.repArrs.toList.map Array.toList : List (List ℕ)).Nodup &&
    s.repArrs.all (repCheck n p (s.elems n N)) &&
    (s.elems n N).all (coverCheck n p s.repArrs) &&
    s.normalGeneration.all (normalGenCheck n N c.origArrs)

@[expose] def groupSylowCheck (n N : ℕ) (r : GroupRecord) : Bool :=
  r.sylows.all (sylowCheck n N r.chain)

end CFSG.Monster.B.Mathieu
