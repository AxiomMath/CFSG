module

public import CFSG.Milestones.ASVolI.F48.Rest.G23Data
public import CFSG.Milestones.ASVolI.F48.Rest.PermCheck
public import CFSG.RankThree.PartTwo.Census.Carrier.G2ThreeData
public import Batteries.Data.ByteArray
public import Certificates.Data.CFSGNative.CosetTable.Enum

public section

namespace CFSG.ASVolI

open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.CosetTable
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

set_option compiler.extract_closed false

@[expose] def burnsideF48t_g23Mats (_ : Unit := ()) : Array (Array ℕ) :=
  #[CFSG.RankThree.PartTwo.Census.Carrier.G2Three.x0c.toArray,
    CFSG.RankThree.PartTwo.Census.Carrier.G2Three.x1c.toArray,
    CFSG.RankThree.PartTwo.Census.Carrier.G2Three.y0c.toArray,
    CFSG.RankThree.PartTwo.Census.Carrier.G2Three.y1c.toArray]

@[expose] def burnsideF48t_g23Dot (A v : Array ℕ) (i : ℕ) : ℕ :=
  ((List.range 14).map fun k => A[14 * i + k]! * v[k]!).sum

@[expose] def burnsideF48t_g23MulVec (A v : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 14) fun i => burnsideF48t_g23Dot A v i.val % 3

@[expose] def burnsideF48t_g23Norm (v : Array ℕ) : Array ℕ :=
  if v.find? (· != 0) == some 2 then v.map fun x => 2 * x % 3 else v

@[expose] def burnsideF48t_g23Unit (j : ℕ) : Array ℕ :=
  Array.ofFn (n := 14) fun i => if i.val = j then 1 else 0

@[expose] def burnsideF48t_g23Pts (_ : Unit := ()) : Array (Array ℕ) :=
  let b := burnsideF48t_g23PtsStr.toUTF8
  (Array.range 728).map fun k => (Array.range 14).map fun j => b[14 * k + j]!.toNat - 48

@[expose] def burnsideF48t_g23Index (P : Array (Array ℕ)) : Std.HashMap (Array ℕ) ℕ := Id.run do
  let mut I : Std.HashMap (Array ℕ) ℕ := ∅
  for k in [0:P.size] do
    I := I.insert P[k]! k
  return I

@[expose] def burnsideF48t_g23Gens (_ : Unit := ()) : Array (Array ℕ) := burnsideF48t_g23GensArr

@[expose] def burnsideF48t_g23GensInv (_ : Unit := ()) : Array (Array ℕ) :=
  (burnsideF48t_g23Gens ()).map (pinvCand 728)

@[expose] def burnsideF48t_g23LInv (_ : Unit := ()) : Array (Array ℕ) :=
  burnsideF48t_g23LArr.map (pinvCand 728)

@[expose] def burnsideF48t_g23P1Arr : Array (Array ℕ) :=
  #[burnsideF48t_g23LArr[0]!, burnsideF48t_g23LArr[1]!, burnsideF48t_g23LArr[2]!]

@[expose] def burnsideF48t_g23P2Arr : Array (Array ℕ) :=
  #[burnsideF48t_g23LArr[0]!, burnsideF48t_g23LArr[1]!, burnsideF48t_g23LArr[3]!]

@[expose] def burnsideF48t_g23BArr : Array (Array ℕ) :=
  #[burnsideF48t_g23LArr[0]!, burnsideF48t_g23LArr[1]!]

@[expose] def burnsideF48t_g23S0Arr (_ : Unit := ()) : Array (Array ℕ) :=
  let Li := burnsideF48t_g23LInv ()
  (burnsideF48t_g23SW.map fun w => burnsideF48t_evA 728 burnsideF48t_g23LArr Li w).toArray

@[expose] def burnsideF48t_g23KArr (_ : Unit := ()) : Array (Array ℕ) :=
  let Li := burnsideF48t_g23LInv ()
  (burnsideF48t_g23KW.map fun w => burnsideF48t_evA 728 burnsideF48t_g23LArr Li w).toArray

@[expose] def burnsideF48t_g23LevX (_ : Unit := ()) : Array Level :=
  burnsideF48t_levels 728 (burnsideF48t_g23Gens ()) burnsideF48t_g23WX burnsideF48t_g23BaseX

@[expose] def burnsideF48t_g23LevP2 (_ : Unit := ()) : Array Level :=
  burnsideF48t_levels 728 burnsideF48t_g23P2Arr burnsideF48t_g23WP2 burnsideF48t_g23BaseP2

@[expose] def burnsideF48t_g23LevP1 (_ : Unit := ()) : Array Level :=
  burnsideF48t_levels 728 burnsideF48t_g23P1Arr burnsideF48t_g23WP1 burnsideF48t_g23BaseP1

@[expose] def burnsideF48t_g23LevB (_ : Unit := ()) : Array Level :=
  burnsideF48t_levels 728 burnsideF48t_g23BArr burnsideF48t_g23WB burnsideF48t_g23BaseB

@[expose] def burnsideF48t_g23LevS0 (_ : Unit := ()) : Array Level :=
  burnsideF48t_levels 728 (burnsideF48t_g23S0Arr ()) burnsideF48t_g23WS0 burnsideF48t_g23BaseS0

@[expose] def burnsideF48t_g23LevK (_ : Unit := ()) : Array Level :=
  burnsideF48t_levels 728 (burnsideF48t_g23KArr ()) burnsideF48t_g23WK burnsideF48t_g23BaseK

@[expose] def burnsideF48t_g23ChainXOK (_ : Unit := ()) : Bool :=
  chainCheck 728 (burnsideF48t_g23Gens ()) burnsideF48t_g23WX burnsideF48t_g23BaseX
    burnsideF48t_g23SizesX

@[expose] def burnsideF48t_g23ChainP1OK (_ : Unit := ()) : Bool :=
  chainCheck 728 burnsideF48t_g23P1Arr burnsideF48t_g23WP1 burnsideF48t_g23BaseP1
    burnsideF48t_g23SizesP1

@[expose] def burnsideF48t_g23ChainP2OK (_ : Unit := ()) : Bool :=
  chainCheck 728 burnsideF48t_g23P2Arr burnsideF48t_g23WP2 burnsideF48t_g23BaseP2
    burnsideF48t_g23SizesP2

@[expose] def burnsideF48t_g23ChainBOK (_ : Unit := ()) : Bool :=
  chainCheck 728 burnsideF48t_g23BArr burnsideF48t_g23WB burnsideF48t_g23BaseB
    burnsideF48t_g23SizesB

@[expose] def burnsideF48t_g23ChainS0OK (_ : Unit := ()) : Bool :=
  chainCheck 728 (burnsideF48t_g23S0Arr ()) burnsideF48t_g23WS0 burnsideF48t_g23BaseS0
    burnsideF48t_g23SizesS0

@[expose] def burnsideF48t_g23ChainKOK (_ : Unit := ()) : Bool :=
  chainCheck 728 (burnsideF48t_g23KArr ()) burnsideF48t_g23WK burnsideF48t_g23BaseK
    burnsideF48t_g23SizesK

@[expose] def burnsideF48t_g23InvOK (_ : Unit := ()) : Bool :=
  let Li := burnsideF48t_g23LInv ()
  let G := burnsideF48t_g23Gens ()
  let Gi := burnsideF48t_g23GensInv ()
  burnsideF48t_g23LArr.size == 4 && Li.size == 4 && G.size == 4 && Gi.size == 4 &&
    (allBelowN 4 fun i => pisInv 728 burnsideF48t_g23LArr[i]! Li[i]!) &&
    (allBelowN 4 fun i => pisInv 728 G[i]! Gi[i]!) &&
    pisInv 728 burnsideF48t_g23Tau (pinvCand 728 burnsideF48t_g23Tau)

@[expose] def burnsideF48t_g23LMemOK (_ : Unit := ()) : Bool :=
  let lv := burnsideF48t_g23LevX ()
  allBelowN 4 fun i => burnsideF48t_sift 728 lv burnsideF48t_g23BaseX burnsideF48t_g23LArr[i]!

@[expose] def burnsideF48t_g23RelOK (_ : Unit := ()) : Bool :=
  let Li := burnsideF48t_g23LInv ()
  (burnsideF48t_g23R1 ++ burnsideF48t_g23R2 ++
      [(List.replicate 6 [((2 : Fin 4), true), ((3 : Fin 4), true)]).flatten]).all
    fun r => peq 728 (burnsideF48t_evA 728 burnsideF48t_g23LArr Li r) (pid 728)

@[expose] def burnsideF48t_g23CommOK (_ : Unit := ()) : Bool :=
  let K := burnsideF48t_g23KArr ()
  let xy := pcomp 728 burnsideF48t_g23LArr[2]! burnsideF48t_g23LArr[3]!
  K.size == 2 &&
    !peq 728 (pcomp 728 xy K[0]!) (pcomp 728 K[0]! xy) &&
    !peq 728 (pcomp 728 xy K[1]!) (pcomp 728 K[1]! xy) &&
    !peq 728 (pcomp 728 xy (pcomp 728 K[0]! K[1]!)) (pcomp 728 (pcomp 728 K[0]! K[1]!) xy)

@[expose] def burnsideF48t_g23TauOK (_ : Unit := ()) : Bool :=
  let lv := burnsideF48t_g23LevX ()
  let G := burnsideF48t_g23Gens ()
  let τ := burnsideF48t_g23Tau
  let τi := pinvCand 728 τ
  (allBelowN 4 fun i =>
      burnsideF48t_sift 728 lv burnsideF48t_g23BaseX (pcomp 728 (pcomp 728 τ G[i]!) τi)) &&
    decide (364 ≤ τ[0]!) && decide (τ[0]! < 728)

@[expose] def burnsideF48t_g23FixOK (_ : Unit := ()) : Bool :=
  let L := burnsideF48t_g23LArr
  let S0 := burnsideF48t_g23S0Arr ()
  let P1 := burnsideF48t_g23P1Arr
  let P2 := burnsideF48t_g23P2Arr
  (L[0]!)[0]! == 0 && (L[0]!)[364]! == 364 && (L[1]!)[0]! == 0 && (L[1]!)[364]! == 364 &&
    (L[2]!)[0]! == 0 && (L[3]!)[364]! == 364 && (L[3]!)[0]! != 0 && (L[2]!)[364]! != 364 &&
    (S0.all fun s => s[0]! == 0 && s[364]! == 364) &&
    (allBelowN 728 fun p => p == 0 || p == 364 || S0.any fun s => s[p]! != p) &&
    (allBelowN 364 fun p => P1.any fun g => g[p + 364]! != p + 364) &&
    (allBelowN 364 fun p => P2.any fun g => g[p]! != p)

@[expose] def burnsideF48t_g23HArr (H : List (List (Fin 4 × Bool))) : Array (Array ℕ) :=
  let G := burnsideF48t_g23Gens ()
  let Gi := G.map (pinvCand 728)
  (H.map fun w => burnsideF48t_evA 728 G Gi w).toArray

@[expose] def burnsideF48t_g23OrbXOK (_ : Unit := ()) : Bool :=
  let G := burnsideF48t_g23Gens ()
  burnsideF48t_orbOK 728 G 0 364 && burnsideF48t_orbOK 728 G 364 364 &&
    (allBelowN 4 fun i => allBelowN 364 fun p => decide ((G[i]!)[p]! < 364))

@[expose] def burnsideF48t_g23OrbP1OK (_ : Unit := ()) : Bool :=
  let P1 := burnsideF48t_g23P1Arr
  let HA := burnsideF48t_g23HArr burnsideF48t_g23HA
  burnsideF48t_orbOK 728 P1 364 4 &&
    burnsideF48t_orbOK 728 P1 1 12 && burnsideF48t_orbOK 728 P1 7 108 &&
    burnsideF48t_orbOK 728 P1 34 243 &&
    burnsideF48t_coverOK 728 P1 [1, 7, 34] 1 363 &&
    HA.size == 3 && (HA[0]!)[0]! == 1 && (HA[1]!)[0]! == 7 && (HA[2]!)[0]! == 34 &&
    (allBelowN 3 fun j => burnsideF48t_orbOK 728 (P1.push HA[j]!) 0 364)

@[expose] def burnsideF48t_g23OrbP2OK (_ : Unit := ()) : Bool :=
  let P2 := burnsideF48t_g23P2Arr
  let HB := burnsideF48t_g23HArr burnsideF48t_g23HB
  burnsideF48t_orbOK 728 P2 365 12 && burnsideF48t_orbOK 728 P2 372 108 &&
    burnsideF48t_orbOK 728 P2 400 243 &&
    burnsideF48t_coverOK 728 P2 [365, 372, 400] 365 363 &&
    HB.size == 3 && (HB[0]!)[364]! == 365 && (HB[1]!)[364]! == 372 && (HB[2]!)[364]! == 400 &&
    (allBelowN 3 fun j => burnsideF48t_orbOK 728 (P2.push HB[j]!) 364 364)

@[expose] def burnsideF48t_g23S0NormOK (_ : Unit := ()) : Bool :=
  let L := burnsideF48t_g23LArr
  let Li := burnsideF48t_g23LInv ()
  let S0 := burnsideF48t_g23S0Arr ()
  let lvS := burnsideF48t_g23LevS0 ()
  allBelowN 2 fun i => S0.all fun s =>
    burnsideF48t_sift 728 lvS burnsideF48t_g23BaseS0 (pcomp 728 (pcomp 728 L[i]! s) Li[i]!)

@[expose] def burnsideF48t_g23KL (_ : Unit := ()) : List (Array ℕ) :=
  let K := burnsideF48t_g23KArr ()
  [pid 728, K[0]!, K[1]!, pcomp 728 K[0]! K[1]!]

@[expose] def burnsideF48t_g23CosetTest (KL : List (Array ℕ)) (Kg : Array (Array ℕ))
    (fix : ℕ) (ri e : Array ℕ) : Bool :=
  let ei := pinvCand 728 e
  pisInv 728 e ei &&
    (e[fix]! == fix || !(Kg.all fun k => KL.contains (pcomp 728 (pcomp 728 e k) ei)) ||
      !KL.contains (pcomp 728 e e) || KL.contains (pcomp 728 ri e))

@[expose] def burnsideF48t_g23KClosedOK (_ : Unit := ()) : Bool :=
  burnsideF48t_closedL 728 (burnsideF48t_g23KArr ()) (burnsideF48t_g23KL ())

@[expose] def burnsideF48t_g23E1OK (_ : Unit := ()) : Bool :=
  let KL := burnsideF48t_g23KL ()
  let Kg := burnsideF48t_g23KArr ()
  let Li := burnsideF48t_g23LInv ()
  let E1 := burnsideF48t_closeSet 728 burnsideF48t_g23P1Arr 20000
  burnsideF48t_closedOK 728 burnsideF48t_g23P1Arr E1 &&
    E1.toList.all (burnsideF48t_g23CosetTest KL Kg 364 Li[2]!)

@[expose] def burnsideF48t_g23E2OK (_ : Unit := ()) : Bool :=
  let KL := burnsideF48t_g23KL ()
  let Kg := burnsideF48t_g23KArr ()
  let Li := burnsideF48t_g23LInv ()
  let E2 := burnsideF48t_closeSet 728 burnsideF48t_g23P2Arr 20000
  burnsideF48t_closedOK 728 burnsideF48t_g23P2Arr E2 &&
    E2.toList.all (burnsideF48t_g23CosetTest KL Kg 0 Li[3]!)

@[expose] def burnsideF48t_g23PtsBasicOK (_ : Unit := ()) : Bool :=
  let P := burnsideF48t_g23Pts ()
  let I := burnsideF48t_g23Index P
  let M := burnsideF48t_g23Mats ()
  P.size == 728 && M.size == 4 && (M.all fun A => A.size == 196) &&
    (allBelowN 728 fun i => P[i]!.size == 14 && P[i]!.all (· < 3) &&
      P[i]!.find? (· != 0) == some 1 && I.get? P[i]! == some i &&
      I.get? (P[i]!.map fun x => 2 * x % 3) == none)

@[expose] def burnsideF48t_g23PtsGenOK (_ : Unit := ()) : Bool :=
  let P := burnsideF48t_g23Pts ()
  let M := burnsideF48t_g23Mats ()
  let G := burnsideF48t_g23Gens ()
  G.size == 4 &&
    (allBelowN 4 fun k => allBelowN 728 fun i => decide ((G[k]!)[i]! < 728) &&
      P[(G[k]!)[i]!]! == burnsideF48t_g23Norm (burnsideF48t_g23MulVec M[k]! P[i]!))

end CFSG.ASVolI
