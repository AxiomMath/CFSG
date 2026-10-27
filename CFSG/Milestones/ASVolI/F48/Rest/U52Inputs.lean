module

public import CFSG.Milestones.ASVolI.F48.Rest.U52Data
public import CFSG.Milestones.ASVolI.F48.Rest.PermCheck
public import CFSG.Milestones.ASVolI.F48.Small.EngCheck
public import CFSG.Milestones.ASVolI.F48.Rest.GF4
public import CFSG.Certificates.CosetTablePresented

public section

namespace CFSG.ASVolI

open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.CosetTable
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

set_option compiler.extract_closed false

@[expose] def burnsideF48t_u52Dot (a b : Array ℕ) : ℕ :=
  burnsideF48t_gf4Mul a[0]! b[0]! ^^^ burnsideF48t_gf4Mul a[1]! b[1]! ^^^
    burnsideF48t_gf4Mul a[2]! b[2]! ^^^ burnsideF48t_gf4Mul a[3]! b[3]! ^^^
    burnsideF48t_gf4Mul a[4]! b[4]!

@[expose] def burnsideF48t_u52Bar (a : Array ℕ) : Array ℕ :=
  Array.ofFn (n := 5) fun i => burnsideF48t_gf4Sq a[i.val]!

@[expose] def burnsideF48t_u52TV (u v : Array ℕ) : Array ℕ :=
  let s := burnsideF48t_u52Dot (burnsideF48t_u52Bar u) v
  Array.ofFn (n := 5) fun i => v[i.val]! ^^^ burnsideF48t_gf4Mul u[i.val]! s

@[expose] def burnsideF48t_u52Gens (_ : Unit := ()) : Array (Array ℕ) := burnsideF48t_u52GensArr

@[expose] def burnsideF48t_u52GensInv (_ : Unit := ()) : Array (Array ℕ) :=
  (burnsideF48t_u52Gens ()).map (pinvCand 462)

@[expose] def burnsideF48t_u52LInv (_ : Unit := ()) : Array (Array ℕ) :=
  burnsideF48t_u52LArr.map (pinvCand 462)

@[expose] def burnsideF48t_u52IsoOK (_ : Unit := ()) : Bool :=
  burnsideF48t_u52U.size == 6 &&
    burnsideF48t_u52U.all fun u => u.size == 5 && (u.all fun x => decide (x < 4)) &&
      burnsideF48t_u52Dot (burnsideF48t_u52Bar u) u == 0

@[expose] def burnsideF48t_u52P1Arr : Array (Array ℕ) :=
  #[burnsideF48t_u52LArr[0]!, burnsideF48t_u52LArr[1]!, burnsideF48t_u52LArr[2]!]

@[expose] def burnsideF48t_u52P2Arr : Array (Array ℕ) :=
  #[burnsideF48t_u52LArr[0]!, burnsideF48t_u52LArr[1]!, burnsideF48t_u52LArr[3]!]

@[expose] def burnsideF48t_u52BArr : Array (Array ℕ) :=
  #[burnsideF48t_u52LArr[0]!, burnsideF48t_u52LArr[1]!]

@[expose] def burnsideF48t_u52S0Arr (_ : Unit := ()) : Array (Array ℕ) :=
  let Li := burnsideF48t_u52LInv ()
  (burnsideF48t_u52SW.map fun w => burnsideF48t_evA 462 burnsideF48t_u52LArr Li w).toArray

@[expose] def burnsideF48t_u52KArr (_ : Unit := ()) : Array (Array ℕ) :=
  let Li := burnsideF48t_u52LInv ()
  (burnsideF48t_u52KGenIdx.map fun i =>
    burnsideF48t_evA 462 burnsideF48t_u52LArr Li (burnsideF48t_u52KW.getD i [])).toArray

@[expose] def burnsideF48t_u52KL (_ : Unit := ()) : List (Array ℕ) :=
  let Li := burnsideF48t_u52LInv ()
  burnsideF48t_u52KW.map fun w => burnsideF48t_evA 462 burnsideF48t_u52LArr Li w

@[expose] def burnsideF48t_u52LevX (_ : Unit := ()) : Array Level :=
  burnsideF48t_levels 462 (burnsideF48t_u52Gens ()) burnsideF48t_u52WX burnsideF48t_u52BaseX

@[expose] def burnsideF48t_u52LevS0 (_ : Unit := ()) : Array Level :=
  burnsideF48t_levels 462 (burnsideF48t_u52S0Arr ()) burnsideF48t_u52WS0 burnsideF48t_u52BaseS0

@[expose] def burnsideF48t_u52ChainXOK (_ : Unit := ()) : Bool :=
  chainCheck 462 (burnsideF48t_u52Gens ()) burnsideF48t_u52WX burnsideF48t_u52BaseX
    burnsideF48t_u52SizesX

@[expose] def burnsideF48t_u52ChainP1OK (_ : Unit := ()) : Bool :=
  chainCheck 462 burnsideF48t_u52P1Arr burnsideF48t_u52WP1 burnsideF48t_u52BaseP1
    burnsideF48t_u52SizesP1

@[expose] def burnsideF48t_u52ChainP2OK (_ : Unit := ()) : Bool :=
  chainCheck 462 burnsideF48t_u52P2Arr burnsideF48t_u52WP2 burnsideF48t_u52BaseP2
    burnsideF48t_u52SizesP2

@[expose] def burnsideF48t_u52ChainBOK (_ : Unit := ()) : Bool :=
  chainCheck 462 burnsideF48t_u52BArr burnsideF48t_u52WB burnsideF48t_u52BaseB
    burnsideF48t_u52SizesB

@[expose] def burnsideF48t_u52ChainS0OK (_ : Unit := ()) : Bool :=
  chainCheck 462 (burnsideF48t_u52S0Arr ()) burnsideF48t_u52WS0 burnsideF48t_u52BaseS0
    burnsideF48t_u52SizesS0

@[expose] def burnsideF48t_u52ChainKOK (_ : Unit := ()) : Bool :=
  chainCheck 462 (burnsideF48t_u52KArr ()) burnsideF48t_u52WK burnsideF48t_u52BaseK
    burnsideF48t_u52SizesK

@[expose] def burnsideF48t_u52InvOK (_ : Unit := ()) : Bool :=
  let Li := burnsideF48t_u52LInv ()
  let G := burnsideF48t_u52Gens ()
  let Gi := burnsideF48t_u52GensInv ()
  burnsideF48t_u52LArr.size == 4 && Li.size == 4 && G.size == 6 && Gi.size == 6 &&
    (allBelowN 4 fun i => pisInv 462 burnsideF48t_u52LArr[i]! Li[i]!) &&
    (allBelowN 6 fun i => pisInv 462 G[i]! Gi[i]!)

@[expose] def burnsideF48t_u52LMemOK (_ : Unit := ()) : Bool :=
  let lv := burnsideF48t_u52LevX ()
  allBelowN 4 fun i => burnsideF48t_sift 462 lv burnsideF48t_u52BaseX burnsideF48t_u52LArr[i]!

@[expose] def burnsideF48t_u52RelOK (_ : Unit := ()) : Bool :=
  let Li := burnsideF48t_u52LInv ()
  (burnsideF48t_u52R1 ++ burnsideF48t_u52R2).all
    fun r => peq 462 (burnsideF48t_evA 462 burnsideF48t_u52LArr Li r) (pid 462)

@[expose] def burnsideF48t_u52CandOK (_ : Unit := ()) : Bool :=
  let Li := burnsideF48t_u52LInv ()
  let ev := fun w => burnsideF48t_evA 462 burnsideF48t_u52LArr Li w
  allBelowN 4 fun i => allBelowN 2 fun j => allBelowN 9 fun k =>
    let u := burnsideF48t_u52XW.getD i []
    let v := burnsideF48t_u52YW.getD j []
    let c := burnsideF48t_u52KW.getD k []
    match burnsideF48t_u52Cands.find? fun t => t.1 == i && t.2.1 == j && t.2.2.1 == k with
    | some t => t.2.2.2 != 165 ||
        peq 462 (ev (burnsideF48s_eCandRel 4 u v c)) (pid 462)
    | none => !peq 462 (pcomp 462 (pcomp 462 (ev u) (ev v)) (ev c))
        (pcomp 462 (ev c) (pcomp 462 (ev u) (ev v)))

@[expose] def burnsideF48t_u52FixOK (_ : Unit := ()) : Bool :=
  let L := burnsideF48t_u52LArr
  let S0 := burnsideF48t_u52S0Arr ()
  (L[0]!)[0]! == 0 && (L[0]!)[165]! == 165 && (L[1]!)[0]! == 0 && (L[1]!)[165]! == 165 &&
    (L[2]!)[0]! == 0 && (L[3]!)[165]! == 165 && (L[3]!)[0]! != 0 && (L[2]!)[165]! != 165 &&
    (S0.all fun s => s[0]! == 0 && s[165]! == 165) &&
    (allBelowN 462 fun p => p == 0 || p == 165 || S0.any fun s => s[p]! != p)

@[expose] def burnsideF48t_u52HArr (H : List (List (Fin 6 × Bool))) : Array (Array ℕ) :=
  let G := burnsideF48t_u52Gens ()
  let Gi := G.map (pinvCand 462)
  (H.map fun w => burnsideF48t_evA 462 G Gi w).toArray

@[expose] def burnsideF48t_u52OrbXOK (_ : Unit := ()) : Bool :=
  let G := burnsideF48t_u52Gens ()
  burnsideF48t_orbOK 462 G 0 165 && burnsideF48t_orbOK 462 G 165 297 &&
    (allBelowN 6 fun i => allBelowN 165 fun p => decide ((G[i]!)[p]! < 165))

@[expose] def burnsideF48t_u52OrbP1OK (_ : Unit := ()) : Bool :=
  let P1 := burnsideF48t_u52P1Arr
  let HA := burnsideF48t_u52HArr burnsideF48t_u52HA
  burnsideF48t_orbOK 462 P1 165 9 && burnsideF48t_orbOK 462 P1 1 128 &&
    burnsideF48t_orbOK 462 P1 15 36 && burnsideF48t_coverOK 462 P1 [1, 15] 1 164 &&
    HA.size == 2 && (HA[0]!)[0]! == 1 && (HA[1]!)[0]! == 15 &&
    (allBelowN 2 fun j => burnsideF48t_orbOK 462 (P1.push HA[j]!) 0 165)

@[expose] def burnsideF48t_u52OrbP2OK (_ : Unit := ()) : Bool :=
  let P2 := burnsideF48t_u52P2Arr
  let HB := burnsideF48t_u52HArr burnsideF48t_u52HB
  burnsideF48t_orbOK 462 P2 166 40 && burnsideF48t_orbOK 462 P2 175 256 &&
    burnsideF48t_coverOK 462 P2 [166, 175] 166 296 &&
    HB.size == 2 && (HB[0]!)[165]! == 166 && (HB[1]!)[165]! == 175 &&
    (allBelowN 2 fun j => burnsideF48t_orbOK 462 (P2.push HB[j]!) 165 297)

@[expose] def burnsideF48t_u52S0NormOK (_ : Unit := ()) : Bool :=
  let L := burnsideF48t_u52LArr
  let Li := burnsideF48t_u52LInv ()
  let S0 := burnsideF48t_u52S0Arr ()
  let lvS := burnsideF48t_u52LevS0 ()
  allBelowN 2 fun i => S0.all fun s =>
    burnsideF48t_sift 462 lvS burnsideF48t_u52BaseS0 (pcomp 462 (pcomp 462 L[i]! s) Li[i]!)

@[expose] def burnsideF48t_u52CosetTest (KL : List (Array ℕ)) (Kg : Array (Array ℕ))
    (fix : ℕ) (ris : List (Array ℕ)) (e : Array ℕ) : Bool :=
  let ei := pinvCand 462 e
  pisInv 462 e ei &&
    (e[fix]! == fix || !(Kg.all fun k => KL.contains (pcomp 462 (pcomp 462 e k) ei)) ||
      !KL.contains (pcomp 462 e e) || ris.any fun ri => KL.contains (pcomp 462 ri e))

@[expose] def burnsideF48t_u52KClosedOK (_ : Unit := ()) : Bool :=
  burnsideF48t_closedL 462 (burnsideF48t_u52KArr ()) (burnsideF48t_u52KL ())

@[expose] def burnsideF48t_u52E1OK (_ : Unit := ()) : Bool :=
  let KL := burnsideF48t_u52KL ()
  let Kg := burnsideF48t_u52KArr ()
  let Li := burnsideF48t_u52LInv ()
  let ris := burnsideF48t_u52XW.map fun w =>
    burnsideF48t_evA 462 burnsideF48t_u52LArr Li (burnsideF48s_eInvW w)
  let E1 := burnsideF48t_closeSet 462 burnsideF48t_u52P1Arr 100000
  burnsideF48t_closedOK 462 burnsideF48t_u52P1Arr E1 &&
    E1.toList.all (burnsideF48t_u52CosetTest KL Kg 165 ris)

@[expose] def burnsideF48t_u52E2OK (_ : Unit := ()) : Bool :=
  let KL := burnsideF48t_u52KL ()
  let Kg := burnsideF48t_u52KArr ()
  let Li := burnsideF48t_u52LInv ()
  let ris := burnsideF48t_u52YW.map fun w =>
    burnsideF48t_evA 462 burnsideF48t_u52LArr Li (burnsideF48s_eInvW w)
  let E2 := burnsideF48t_closeSet 462 burnsideF48t_u52P2Arr 100000
  burnsideF48t_closedOK 462 burnsideF48t_u52P2Arr E2 &&
    E2.toList.all (burnsideF48t_u52CosetTest KL Kg 0 ris)

abbrev burnsideF48t_u52Ws (i j k : ℕ) : List (List (Fin 4 × Bool)) :=
  burnsideF48s_eWs burnsideF48t_u52R1 burnsideF48t_u52R2 4 (burnsideF48t_u52XW.getD i [])
    (burnsideF48t_u52YW.getD j []) (burnsideF48t_u52KW.getD k [])

abbrev burnsideF48t_u52WsB : List (List (Fin (subsetOf 4 [0, 1, 2]).length × Bool)) :=
  restrictWords (subsetOf 4 [0, 1, 2]) (burnsideF48t_u52R1 ++ burnsideF48t_u52R2)

@[expose] def burnsideF48t_u52TCOK (_ : Unit := ()) : Bool :=
  burnsideF48t_u52Cands.all fun t =>
    subsetCheck (burnsideF48t_u52Ws t.1 t.2.1 t.2.2.1) [0, 1, 2] 100000 t.2.2.2

end CFSG.ASVolI
