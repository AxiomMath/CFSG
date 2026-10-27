
module

public import CFSG.Sporadic.HNSchreier.SylowCheckBase
public import CFSG.Sporadic.HNSchreier.IntrinsicData
public meta import CFSG.Sporadic.HNSchreier.SylowCheckBase
public meta import CFSG.Sporadic.HNSchreier.IntrinsicData

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.F5.Native CFSG.Perm.Native CFSG.Sporadic.Th.Native

@[noinline, expose] def intrinsicChecks (O : VOrbit) : Bool :=
  let n := hnsData.n
  let a0 := natTab O.alpha
  let a1 := natTab O.beta
  let ai := pinvs n #[a0, a1]
  let regs := progRegs n (initRegs n a0 a1) Data.subgroupProgram
  let hS := extendStrong n #[regs[1]!, regs[2]!] LocalData.strongWords
  let hSi := pinvs n hS
  let s1 := pword n hS hSi FAData.sWords[0]!
  let nS := extendStrong 12 #[natArr LocalData.natGen1, natArr LocalData.natGen2]
    LocalData.strongWords
  let nSi := pinvs 12 nS
  let B := Data.baseList
  ai.size == 2 && pisInv n a0 ai[0]! && pisInv n a1 ai[1]! &&
    IntrinsicData.wRoot.size == 2 && IntrinsicData.wHWord.size == 2 &&
    IntrinsicData.wNat.size == 2 && IntrinsicData.rho.size == 2 &&
    IntrinsicData.wCycles == #[2, 4] &&
    allBelowN 2 (fun c =>
      let w := IntrinsicData.wRoot[c]!
      let hw := IntrinsicData.wHWord[c]!
      let harr := pword n hS hSi hw
      let k := IntrinsicData.wCycles[c]!
      let ρ := natArr IntrinsicData.rho[c]!
      w.all (fun l => l == 1 || l == 2) && plettersOK 17 hw &&
        B.all (fun b => seedWordInvIdx ai[0]! ai[1]! w (s1[seedWordIdx a0 a1 w b]!) ==
          harr[b]!) &&
        peq 12 (pword 12 nS nSi hw) (natArr IntrinsicData.wNat[c]!) &&
        pisInv 12 ρ (pinvCand 12 ρ) &&
        peq 12 (pcomp 12 (pcomp 12 ρ (tripleArr k)) (pinvCand 12 ρ))
          (natArr IntrinsicData.wNat[c]!))

end CFSG.Sporadic.HNSchreier.Native
