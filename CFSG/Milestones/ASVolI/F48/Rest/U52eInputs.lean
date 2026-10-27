module

public import CFSG.Milestones.ASVolI.F48.Rest.U52eData
public import CFSG.Milestones.ASVolI.F48.Rest.U52Inputs

public section

namespace CFSG.ASVolI

open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.CosetTable
open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

set_option compiler.extract_closed false

@[expose] def burnsideF48t_u52eLArr (_ : Unit := ()) : Array (Array ℕ) :=
  burnsideF48t_u52LArr.push burnsideF48t_u52eF

@[expose] def burnsideF48t_u52eLInv (_ : Unit := ()) : Array (Array ℕ) :=
  (burnsideF48t_u52eLArr ()).map (pinvCand 462)

@[expose] def burnsideF48t_u52eInvOK (_ : Unit := ()) : Bool :=
  let L := burnsideF48t_u52eLArr ()
  let Li := burnsideF48t_u52eLInv ()
  L.size == 5 && Li.size == 5 && allBelowN 5 fun i => pisInv 462 L[i]! Li[i]!

@[expose] def burnsideF48t_u52eFOK (_ : Unit := ()) : Bool :=
  let F := burnsideF48t_u52eF
  let lv := burnsideF48t_u52LevX ()
  let G := burnsideF48t_u52Gens ()
  pisInv 462 F F && F[0]! == 0 && F[165]! == 165 &&
    (G.all fun g => burnsideF48t_sift 462 lv burnsideF48t_u52BaseX (pcomp 462 (pcomp 462 F g) F)) &&
    !burnsideF48t_sift 462 lv burnsideF48t_u52BaseX F

@[expose] def burnsideF48t_u52eRelOK (_ : Unit := ()) : Bool :=
  let L := burnsideF48t_u52eLArr ()
  let Li := burnsideF48t_u52eLInv ()
  (burnsideF48t_u52eR1 ++ burnsideF48t_u52eR2).all
    fun r => peq 462 (burnsideF48t_evA 462 L Li r) (pid 462)

@[expose] def burnsideF48t_u52eKL (j : ℕ) (_ : Unit := ()) : List (Array ℕ) :=
  let L := burnsideF48t_u52eLArr ()
  let Li := burnsideF48t_u52eLInv ()
  (burnsideF48t_u52eKhW.getD j []).map fun w => burnsideF48t_evA 462 L Li w

@[expose] def burnsideF48t_u52eKG (j : ℕ) (_ : Unit := ()) : Array (Array ℕ) :=
  let KL := burnsideF48t_u52eKL j ()
  #[KL.getD 1 (pid 462), KL.getD 3 (pid 462), KL.getD 9 (pid 462)]

@[expose] def burnsideF48t_u52eKhOK (_ : Unit := ()) : Bool :=
  let KL := burnsideF48t_u52KL ()
  burnsideF48t_u52eKhW.length == 4 &&
    allBelowN 4 fun j =>
      let C := burnsideF48t_u52eKL j ()
      C.length == 18 && burnsideF48t_closedL 462 (burnsideF48t_u52eKG j ()) C &&
        peq 462 (C.getD 1 (pid 462)) (KL.getD 1 (pid 462)) &&
        peq 462 (C.getD 3 (pid 462)) (KL.getD 3 (pid 462)) && !KL.contains (C.getD 9 (pid 462))

@[expose] def burnsideF48t_u52eTest (KL : List (Array ℕ)) (Kg : Array (Array ℕ)) (fix : ℕ)
    (ris : List (Array ℕ)) (e ei : Array ℕ) : Bool :=
  e[fix]! == fix || !(Kg.all fun k => KL.contains (pcomp 462 (pcomp 462 e k) ei)) ||
    !KL.contains (pcomp 462 e e) || ris.any fun ri => KL.contains (pcomp 462 ri e)

@[expose] def burnsideF48t_u52eRisX (_ : Unit := ()) : List (Array ℕ) :=
  let L := burnsideF48t_u52eLArr ()
  let Li := burnsideF48t_u52eLInv ()
  burnsideF48t_u52eXW.map fun w => burnsideF48t_evA 462 L Li (burnsideF48s_eInvW w)

@[expose] def burnsideF48t_u52eRisY (_ : Unit := ()) : List (Array ℕ) :=
  let L := burnsideF48t_u52eLArr ()
  let Li := burnsideF48t_u52eLInv ()
  burnsideF48t_u52eYW.map fun w => burnsideF48t_evA 462 L Li (burnsideF48s_eInvW w)

@[expose] def burnsideF48t_u52eE1OK (_ : Unit := ()) : Bool :=
  let F := burnsideF48t_u52eF
  let KL0 := burnsideF48t_u52eKL 0 ()
  let KG0 := burnsideF48t_u52eKG 0 ()
  let KL1 := burnsideF48t_u52eKL 1 ()
  let KG1 := burnsideF48t_u52eKG 1 ()
  let KL2 := burnsideF48t_u52eKL 2 ()
  let KG2 := burnsideF48t_u52eKG 2 ()
  let ris := burnsideF48t_u52eRisX ()
  let E1 := burnsideF48t_closeSet 462 burnsideF48t_u52P1Arr 100000
  burnsideF48t_closedOK 462 burnsideF48t_u52P1Arr E1 &&
    E1.toList.all fun p =>
      let pinv := pinvCand 462 p
      let q := pcomp 462 F p
      let qinv := pcomp 462 pinv F
      pisInv 462 p pinv && pisInv 462 q qinv &&
        burnsideF48t_u52eTest KL0 KG0 165 [] p pinv && burnsideF48t_u52eTest KL0 KG0 165 [] q qinv &&
        burnsideF48t_u52eTest KL1 KG1 165 [] p pinv && burnsideF48t_u52eTest KL1 KG1 165 [] q qinv &&
        burnsideF48t_u52eTest KL2 KG2 165 ris p pinv && burnsideF48t_u52eTest KL2 KG2 165 ris q qinv

@[expose] def burnsideF48t_u52eE2OK (_ : Unit := ()) : Bool :=
  let F := burnsideF48t_u52eF
  let KL2 := burnsideF48t_u52eKL 2 ()
  let KG2 := burnsideF48t_u52eKG 2 ()
  let KL3 := burnsideF48t_u52eKL 3 ()
  let KG3 := burnsideF48t_u52eKG 3 ()
  let ris := burnsideF48t_u52eRisY ()
  let E2 := burnsideF48t_closeSet 462 burnsideF48t_u52P2Arr 100000
  burnsideF48t_closedOK 462 burnsideF48t_u52P2Arr E2 &&
    E2.toList.all fun p =>
      let pinv := pinvCand 462 p
      let q := pcomp 462 F p
      let qinv := pcomp 462 pinv F
      pisInv 462 p pinv && pisInv 462 q qinv &&
        burnsideF48t_u52eTest KL2 KG2 0 ris p pinv && burnsideF48t_u52eTest KL2 KG2 0 ris q qinv &&
        burnsideF48t_u52eTest KL3 KG3 0 [] p pinv && burnsideF48t_u52eTest KL3 KG3 0 [] q qinv

@[expose] def burnsideF48t_u52eTestB (KL : List (Array ℕ)) (Kg : Array (Array ℕ)) (LS : Array Level)
    (e ei : Array ℕ) : Bool :=
  !(Kg.all fun k => KL.contains (pcomp 462 (pcomp 462 e k) ei)) || !KL.contains (pcomp 462 e e) ||
    KL.contains e || KL.any fun k =>
      burnsideF48t_sift 462 LS burnsideF48t_u52BaseS0 (pcomp 462 e k) &&
        !peq 462 (pcomp 462 e k) (pid 462)

@[expose] def burnsideF48t_u52eTestF (KL : List (Array ℕ)) (Kg : Array (Array ℕ))
    (C : List (List (Array ℕ))) (e ei : Array ℕ) : Bool :=
  !(Kg.all fun k => KL.contains (pcomp 462 (pcomp 462 e k) ei)) || !KL.contains (pcomp 462 e e) ||
    C.any fun c => c.contains e

@[expose] def burnsideF48t_u52eClassOK (_ : Unit := ()) : Bool :=
  let F := burnsideF48t_u52eF
  let KL := burnsideF48t_u52KL ()
  let Kg := burnsideF48t_u52KArr ()
  let C := [burnsideF48t_u52eKL 0 (), burnsideF48t_u52eKL 1 (), burnsideF48t_u52eKL 2 (),
    burnsideF48t_u52eKL 3 ()]
  let LS := burnsideF48t_u52LevS0 ()
  let EB := burnsideF48t_closeSet 462 burnsideF48t_u52BArr 100000
  burnsideF48t_closedOK 462 burnsideF48t_u52BArr EB &&
    EB.toList.all fun b =>
      let bi := pinvCand 462 b
      let t := pcomp 462 F b
      let ti := pcomp 462 bi F
      pisInv 462 b bi && pisInv 462 t ti && burnsideF48t_u52eTestB KL Kg LS b bi &&
        burnsideF48t_u52eTestF KL Kg C t ti

@[expose] def burnsideF48t_u52eCandOK (_ : Unit := ()) : Bool :=
  let L := burnsideF48t_u52eLArr ()
  let Li := burnsideF48t_u52eLInv ()
  let KW := burnsideF48t_u52eKhW.getD 2 []
  allBelowN 4 fun i => allBelowN 2 fun j => allBelowN 18 fun k =>
    match burnsideF48t_u52eCands.find? (fun t => t.1 == i && t.2.1 == j && t.2.2.1 == k) with
    | some t => t.2.2.2 != 165 || peq 462 (burnsideF48t_evA 462 L Li
        (burnsideF48s_eCandRel 4 (burnsideF48t_u52eXW.getD i []) (burnsideF48t_u52eYW.getD j [])
          (KW.getD k []))) (pid 462)
    | none =>
      let u := burnsideF48t_evA 462 L Li (burnsideF48t_u52eXW.getD i [])
      let v := burnsideF48t_evA 462 L Li (burnsideF48t_u52eYW.getD j [])
      let c := burnsideF48t_evA 462 L Li (KW.getD k [])
      !peq 462 (pcomp 462 (pcomp 462 u v) c) (pcomp 462 c (pcomp 462 u v))

abbrev burnsideF48t_u52eWs (i j k : ℕ) : List (List (Fin 5 × Bool)) :=
  burnsideF48s_eWs burnsideF48t_u52eR1 burnsideF48t_u52eR2 4 (burnsideF48t_u52eXW.getD i [])
    (burnsideF48t_u52eYW.getD j []) ((burnsideF48t_u52eKhW.getD 2 []).getD k [])

abbrev burnsideF48t_u52eWsB : List (List (Fin (subsetOf 5 [0, 1, 2, 4]).length × Bool)) :=
  restrictWords (subsetOf 5 [0, 1, 2, 4]) (burnsideF48t_u52eR1 ++ burnsideF48t_u52eR2)

abbrev burnsideF48t_u52eWsBB : List (List (Fin (subsetOf (subsetOf 5 [0, 1, 2, 4]).length
    [0, 1, 2]).length × Bool)) :=
  restrictWords (subsetOf (subsetOf 5 [0, 1, 2, 4]).length [0, 1, 2]) burnsideF48t_u52eWsB

@[expose] def burnsideF48t_u52eTCOK (_ : Unit := ()) : Bool :=
  (burnsideF48t_u52eCands.all fun t =>
    subsetCheck (burnsideF48t_u52eWs t.1 t.2.1 t.2.2.1) [0, 1, 2, 4] 100000 t.2.2.2) &&
    subsetCheck burnsideF48t_u52eWsB [0, 1, 2] 100000 2 &&
    subsetCheck burnsideF48t_u52eWsBB [] 1000000 82944

end CFSG.ASVolI
