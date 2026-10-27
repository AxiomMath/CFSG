module

public import Std.Data.HashMap

public section

namespace CFSG.LieType.Chevalley.WE8.Native

@[expose] def cart (i j : Nat) : Int :=
  if i = j then 2
  else if (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ (i = 1 ∧ j = 3) ∨ (i = 3 ∧ j = 1) ∨
      (2 ≤ i ∧ j = i + 1) ∨ (2 ≤ j ∧ i = j + 1) then -1
  else 0

abbrev Vec := List Int

@[expose] def pair (i : Nat) (v : Vec) : Int :=
  (List.ofFn fun k : Fin 8 => cart i k * v.getD k 0).sum

@[expose] def ip (u v : Vec) : Int :=
  (List.ofFn fun i : Fin 8 => u.getD i 0 * pair i v).sum

@[expose] def sRefl (j : Nat) (v : Vec) : Vec :=
  List.ofFn fun k : Fin 8 => if (k : Nat) = j then v.getD k 0 - pair j v else v.getD k 0

@[expose] def vadd (u v : Vec) : Vec := List.ofFn fun k : Fin 8 => u.getD k 0 + v.getD k 0

@[expose] def vsub (u v : Vec) : Vec := List.ofFn fun k : Fin 8 => u.getD k 0 - v.getD k 0

@[expose] def vsmul (c : Int) (u : Vec) : Vec := List.ofFn fun k : Fin 8 => c * u.getD k 0

@[expose] def vneg (u : Vec) : Vec := List.ofFn fun k : Fin 8 => -u.getD k 0

@[expose] def basisV (i : Nat) : Vec := List.ofFn fun k : Fin 8 => if (k : Nat) = i then 1 else 0

@[expose] def rootCodes (_ : Unit := ()) : List Nat := [
    2290649225, 2290649240, 2290649480, 2290653320, 2290714760, 2291697800, 2307426440,
    2559084680, 2290649223, 2290649481, 2290649208, 2290653336, 2290648968, 2290653576,
    2290645128, 2290718856, 2290583688, 2291763336, 2289600648, 2308475016, 2273872008,
    2575861896, 2022213768, 2290648967, 2290653577, 2290645112, 2290653592, 2290718872,
    2290644872, 2290719112, 2290579592, 2291767432, 2289535112, 2308540552, 2272823432,
    2576910472, 2005436552, 2290644871, 2290653593, 2290719113, 2290644856, 2290579576,
    2290719128, 2291767448, 2290579336, 2291767688, 2289531016, 2308544648, 2272757896,
    2576976008, 2004387976, 2290644855, 2290579335, 2290719129, 2291767689, 2290579320,
    2289531000, 2290723224, 2291767704, 2308544664, 2289530760, 2308544904, 2272753800,
    2576980104, 2004322440, 2290579319, 2289530759, 2290723225, 2291767705, 2308544905,
    2290575224, 2289530744, 2272753784, 2291771800, 2308544920, 2576980120, 2272753544,
    2576980360, 2004318344, 2290575223, 2289530743, 2272753543, 2290723481, 2291771801,
    2308544921, 2576980361, 2289526648, 2272753528, 2004318328, 2291837336, 2308549016,
    2576980376, 2004318088, 2290574967, 2289526647, 2272753527, 2004318087, 2291772057,
    2291837337, 2308549017, 2576980377, 2289461112, 2272749432, 2004318072, 2308614552,
    2576984472, 2289526391, 2289461111, 2272749431, 2004318071, 2291837593, 2308549273,
    2308614553, 2576984473, 2272683896, 2004313976, 2309663128, 2577050008, 2289460855,
    2272749175, 2272683895, 2004313975, 2291841689, 2308614809, 2576984729, 2309663129,
    2577050009, 2271635320, 2004248440, 2578098584, 2289456759, 2272683639, 2004313719,
    2271635319, 2004248439, 2291841705, 2308618905, 2309663385, 2577050265, 2578098585,
    2003199864, 2594875800, 2289456743, 2272679543, 2271635063, 2004248183, 2003199863,
    2308618921, 2309667481, 2577054361, 2578098841, 2594875801, 1986422648, 2272679527,
    2271630967, 2004244087, 2003199607, 1986422647, 2309667497, 2577054377, 2309733017,
    2578102937, 2594876057, 2271630951, 2004244071, 2271565431, 2003195511, 1986422391,
    2309733033, 2578102953, 2578168473, 2594880153, 2271565415, 2003195495, 2003129975,
    1986418295, 2309737129, 2578168489, 2594880169, 2594945689, 2271561319, 2003129959,
    1986418279, 1986352759, 2309737385, 2578172585, 2594945705, 2595994265, 2271561063,
    2003125863, 1986352743, 1985304183, 2309737386, 2578172841, 2594949801, 2595994281,
    2271561062, 2003125607, 1986348647, 1985304167, 2578172842, 2594950057, 2595998377,
    2003125606, 1986348391, 1985300071, 2594950058, 2595998633, 2596063913, 1986348390,
    1985299815, 1985234535, 2595998634, 2596064169, 1985299814, 1985234279, 2596064170,
    2596068265, 1985234278, 1985230183, 2596068266, 2596068281, 1985230182, 1985230167,
    2596068282, 2596068522, 1985230166, 1985229926, 2596068538, 1985229910, 2596072634,
    1985225814, 2596138170, 1985160278, 2597186746, 1984111702, 2613963962, 1967334486,
    2882399418, 1698899030]

@[expose] def decodeVec (c : Nat) : Vec :=
  List.ofFn fun k : Fin 8 => ((c / 16 ^ (k : Nat) % 16 : Nat) : Int) - 8

@[expose] def rootsL (_ : Unit := ()) : List Vec := rootCodes.map decodeVec

@[expose] def roots (_ : Unit := ()) : Array Vec := rootsL.toArray

@[expose] def rootIdx (v : Vec) : Nat := rootsL.idxOf v

abbrev ICode := List Nat

@[expose] def permT (_ : Unit := ()) : Array (Array Nat) :=
  Array.ofFn fun j : Fin 8 => roots.map fun v => rootIdx (sRefl j v)

@[expose] def negT (_ : Unit := ()) : Array Nat := roots.map fun v => rootIdx (vneg v)

@[expose] def addT (_ : Unit := ()) : Array (Array Nat) :=
  roots.map fun u => roots.map fun v => if ip u v == -1 then rootIdx (vadd u v) else 0

@[expose] def conjI (j : Nat) (cs : ICode) : ICode :=
  List.ofFn fun i : Fin 8 =>
    if (i : Nat) = j then negT.getD ((permT.getD j #[]).getD (cs.getD j 0) 0) 0
    else if cart j i = -1 then
      (permT.getD j #[]).getD ((addT.getD (cs.getD i 0) #[]).getD (cs.getD j 0) 0) 0
    else (permT.getD j #[]).getD (cs.getD i 0) 0

@[expose] def keyI (cs : ICode) : Nat := cs.foldr (fun c acc => acc * 256 + c) 0

@[expose] def applyI (cs : ICode) (v : Vec) : Vec :=
  List.ofFn fun i : Fin 8 =>
    (List.ofFn fun k : Fin 8 => v.getD k 0 * (rootsL.getD (cs.getD k 0) []).getD i 0).sum

@[expose] def mulI (M N : ICode) : ICode := N.map fun c => rootIdx (applyI M (rootsL.getD c []))

@[expose] def negI (cs : ICode) : ICode := cs.map fun c => negT.getD c 0

@[expose] def rRefl (b v : Vec) : Vec := vsub v (vsmul (ip b v) b)

@[expose] def frameCode (frame : List Vec) : ICode :=
  List.ofFn fun i : Fin 8 => rootIdx (frame.foldr rRefl (basisV i))

@[expose] def wordCode (ω : List Nat) : ICode :=
  List.ofFn fun i : Fin 8 => rootIdx (ω.foldr sRefl (basisV i))

@[expose] def negCount (cs : ICode) : Nat :=
  (rootsL.filter fun v => applyI cs v == vneg v).length

structure OrbitData where
  elts : Array ICode
  par : Array (Nat × Nat)
  tab : Array (Array Nat)

@[expose] def bfsStep (d : OrbitData) (seen : Std.HashMap Nat Nat) (qi : Nat) :
    OrbitData × Std.HashMap Nat Nat :=
  match d with
  | ⟨elts, par, tab⟩ =>
    let M := elts.getD qi []
    let r := (List.range 8).foldl
      (fun (acc : Array ICode × Array (Nat × Nat) × Std.HashMap Nat Nat × Array Nat) j =>
        match acc with
        | (elts, par, seen, row) =>
          let N := conjI j M
          let k := keyI N
          match seen.get? k with
          | some m => (elts, par, seen, row.push m)
          | none =>
            let sz := elts.size
            (elts.push N, par.push (qi, j), seen.insert k sz, row.push sz))
      (elts, par, seen, #[])
    match r with
    | (elts, par, seen, row) => (⟨elts, par, tab.push row⟩, seen)

@[expose] def bfsLoop : Nat → Nat → OrbitData → Std.HashMap Nat Nat → OrbitData
  | 0, _, d, _ => d
  | fuel + 1, qi, d, seen =>
    if qi < d.elts.size then
      let r := bfsStep d seen qi
      bfsLoop fuel (qi + 1) r.1 r.2
    else d

@[expose] def bfs (start : ICode) : OrbitData :=
  bfsLoop 200000 0 ⟨#[start], #[(0, 0)], #[]⟩ ((∅ : Std.HashMap Nat Nat).insert (keyI start) 0)

@[expose] def checkPar (d : OrbitData) (k : Nat) : Bool :=
  k == 0 || match d.par[k]? with
    | some (p, j) => p < k && j < 8 && d.elts[k]? == (d.elts[p]?).map (conjI j)
    | none => false

@[expose] def checkTab (d : OrbitData) (k : Nat) : Bool :=
  match d.tab[k]? with
  | some row => (List.range 8).all fun j => match row[j]? with
      | some m => d.elts[m]? == (d.elts[k]?).map (conjI j)
      | none => false
  | none => false

@[expose] def strictSorted : List Nat → Bool
  | a :: b :: l => a < b && strictSorted (b :: l)
  | _ => true

@[expose] def checkOrbit (start : ICode) (d : OrbitData) : Bool :=
  d.elts[0]? == some start &&
  (List.range d.elts.size).all (checkPar d) &&
  (List.range d.elts.size).all (checkTab d) &&
  strictSorted ((d.elts.toList.map keyI).mergeSort)

@[expose] def pairT (_ : Unit := ()) : Array (Array Int) :=
  roots.map fun v => Array.ofFn fun i : Fin 8 => pair i v

@[expose] def ipT (_ : Unit := ()) : Array (Array Int) := roots.map fun u => roots.map fun v => ip u v

@[expose] def okFrom (sgn : Int) (a n : Nat) (pa : Array Int) : Nat → List Nat → Bool
  | _, [] => true
  | j, b :: bs =>
    ((ipT.getD b #[]).getD a 0 == cart j n && pa.getD j 0 == sgn * (pairT.getD b #[]).getD n 0) &&
      okFrom sgn a n pa (j + 1) bs

@[expose] def okNew (sgn : Int) (n : Nat) (pre : List Nat) (a : Nat) : Bool :=
  let pa := pairT.getD a #[]
  pa.getD n 0 == sgn * pa.getD n 0 && okFrom sgn a n pa 0 pre

@[expose] def extend (sgn : Int) (pre : List Nat) : List (List Nat) :=
  let n := pre.length
  ((List.range 240).filter (okNew sgn n pre)).map fun a => pre ++ [a]

@[expose] def enum (sgn : Int) : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => (enum sgn n).flatMap (extend sgn)

@[expose] def frameData (_ : Unit := ()) : List (List Vec) := [
  [[1, 0, 0, 0, 0, 0, 0, 0]],
  [[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0]],
  [[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0]],
  [[1, 0, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 1, 0]],
  [[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0],
    [0, 1, 1, 2, 1, 0, 0, 0]],
  [[0, 1, 0, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0, 0],
    [0, 1, 1, 2, 1, 0, 0, 0], [0, 0, 0, 0, 0, 0, 1, 0]],
  [[1, 1, 2, 2, 1, 1, 0, 0], [1, 2, 3, 4, 3, 2, 2, 1], [1, 1, 2, 3, 3, 2, 1, 1],
    [1, 1, 1, 2, 1, 1, 1, 1], [1, 2, 2, 4, 3, 2, 1, 0], [1, 1, 1, 1, 1, 0, 0, 0]],
  [[0, 0, 0, 0, 0, 0, 1, 1], [0, 1, 1, 1, 1, 1, 1, 0], [1, 2, 2, 3, 2, 2, 1, 1],
    [1, 1, 1, 1, 1, 0, 0, 0], [1, 1, 1, 2, 1, 1, 1, 0], [2, 2, 4, 5, 4, 3, 2, 1],
    [1, 2, 2, 4, 4, 3, 2, 1]],
  [[0, 0, 1, 1, 1, 1, 1, 1], [1, 2, 2, 3, 3, 2, 2, 1], [1, 1, 2, 3, 2, 1, 1, 0],
    [1, 1, 1, 2, 1, 1, 1, 1], [0, 0, 0, 0, 0, 1, 1, 0], [2, 3, 4, 6, 5, 4, 2, 1],
    [1, 0, 1, 0, 0, 0, 0, 0], [0, 1, 1, 1, 0, 0, 0, 0]]
]

@[expose] def classSizes : List Nat := [120, 3780, 37800, 113400, 3150, 37800, 3780, 120, 1]

@[expose] def zClass : List Nat := [7, 6, 5, 3, 4, 2, 1, 0]

@[expose] def y0Word : List Nat := [
  6, 7, 3, 2, 1, 3, 4, 5, 6, 0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 6, 7, 6, 5, 4, 2,
  3, 0, 2, 1, 3, 4, 5, 6, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5, 2, 3, 0, 2, 1, 3, 4, 1]

@[noinline, expose] def orbitOK (start : ICode) (n : Nat) : Bool :=
  let d := bfs start
  checkOrbit start d && d.elts.size == n

@[noinline, expose] def inOrbit (start c : ICode) : Bool := (bfs start).elts.contains c

@[expose] def classOK (i : Nat) : Bool :=
  orbitOK (frameCode (frameData.getD i [])) (classSizes.getD i 0)

@[expose] def zOK (i : Nat) : Bool :=
  inOrbit (frameCode (frameData.getD (zClass.getD i 0) [])) (negI (frameCode (frameData.getD i [])))

@[expose] def simpleOK (j : Nat) : Bool := inOrbit (frameCode (frameData.getD 0 [])) (wordCode [j])

@[expose] def yOK (_ : Unit) : Bool := orbitOK (wordCode y0Word) 15120

@[noinline, expose] def enumCount (sgn : Int) (k : Nat) : Nat := (enum sgn k).length

@[expose] def enumOK (_ : Unit) : Bool := enumCount 1 8 == 199952 && enumCount (-1) 8 == 15120

@[expose] def allOK (_ : Unit) : Bool :=
  (List.range 9).all classOK && (List.range 8).all zOK && (List.range 8).all simpleOK && yOK () &&
    enumOK ()

end CFSG.LieType.Chevalley.WE8.Native
