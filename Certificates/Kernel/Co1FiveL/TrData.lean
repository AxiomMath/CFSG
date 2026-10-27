module

public import Certificates.Kernel.Co1FiveK.Data
public import Certificates.Data.Kernel.Co1F2
public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.CFSGNative.Timmesfeld.Co1Five
public meta import Certificates.Kernel.SporSch.Co1.GenBfs
public meta import Certificates.Kernel.Co1FiveK.Data
public meta import Certificates.Kernel.Sporadic.OrbRecGen
public meta import Certificates.Data.CFSGNative.Timmesfeld.Co1Five
public meta import Certificates.Data.CFSGNative.Timmesfeld.Co1Seven
public meta import Std.Data.HashMap
public import Certificates.Kernel.Sporadic.OrbRecGen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1FiveL

open CFSG.Sporadic.Co1Schreier.Native

@[expose] noncomputable def HG (τ l : Nat) : Nat :=
  nIf(Nat.beq l (nat_lit 0),
    CFSG.KC.Co1F2.getL (nat_lit 0) CertificateChecks.KernelCo1FiveK.FW.AT
      (Timmesfeld.Co1Five.repA.getD τ 0),
    nIf(Nat.beq l (nat_lit 1),
      CFSG.KC.Co1F2.getL (nat_lit 0) CertificateChecks.KernelCo1FiveK.FW.AT
        (Timmesfeld.Co1Five.repB.getD τ 0),
      CertificateChecks.KernelCo1FiveK.D.M
        (CFSG.KC.Co1F2.getL (nat_lit 0) (Timmesfeld.Co1Five.idxH.getD τ []) (Nat.sub l 2))))

meta def hArr (τ : Nat) : Array Rows :=
  let rs := CertificateChecks.KernelCo1FiveK.dagD.1
  (#[Timmesfeld.Co1Five.a0Row rs (Timmesfeld.Co1Five.repA.getD τ 0),
    Timmesfeld.Co1Five.a0Row rs (Timmesfeld.Co1Five.repB.getD τ 0)] ++
    ((Timmesfeld.Co1Five.idxH.getD τ []).map (Timmesfeld.Co1Five.rowAt rs)).toArray)

meta def hArr0 : Array Rows := hArr 0
meta def hArr1 : Array Rows := hArr 1
meta def hArr2 : Array Rows := hArr 2

meta def closP (G : Array Rows) (e m : Nat) : Array Nat × Array Nat × Array Nat := Id.run do
  let pts := (CFSG.Sporadic.Co1.TwoBNative.gtBFS G 100000).pts
  let good := fun w => w != one () && pow w e == one ()
  let F := Timmesfeld.Co1Seven.fusData pts G.toList good
  let N := pts.size
  let mut pos : Std.HashMap Rows Nat := ∅
  for k in [0:N] do
    pos := pos.insert pts[k]! k
  let M := min N 64
  let invs := (Array.range M).map fun a => inv pts[a]!
  let mut wit : Array Nat := Array.replicate N 0
  for r in [0:N] do
    if good pts[r]! && (F[r]!).1 == r then
      let x := pts[r]!
      let mut found := false
      for a in [0:M] do
        if found then break
        let ca := Timmesfeld.Co1Seven.conjCand pts[a]! invs[a]! x
        for b in [0:(if m == 0 then 1 else M)] do
          if found then break
          let y := mul (mul x ca) (pow (Timmesfeld.Co1Seven.conjCand pts[b]! invs[b]! x) m)
          if y != one () && pow y 5 == one () then
            let ai := pos.getD invs[a]! N
            let bi := pos.getD invs[b]! N
            wit := wit.set! r (a + 65536 * (ai + 65536 * (b + 65536 * bi)))
            found := true
  return (F.map (·.1), F.map (·.2), wit)

meta def clos1 : Array Nat × Array Nat × Array Nat := closP hArr1 12 1
meta def clos2 : Array Nat × Array Nat × Array Nat := closP hArr2 2 0

meta def clos1R : Array Nat := clos1.1
meta def clos1C : Array Nat := clos1.2.1
meta def clos1W : Array Nat := clos1.2.2
meta def clos2R : Array Nat := clos2.1
meta def clos2C : Array Nat := clos2.2.1
meta def clos2W : Array Nat := clos2.2.2

end CertificateChecks.KernelCo1FiveL

#kss_co1gt CertificateChecks.KernelCo1FiveL.HT0 CertificateChecks.KernelCo1FiveL.hArr0 100000

#kss_co1gt CertificateChecks.KernelCo1FiveL.HT1 CertificateChecks.KernelCo1FiveL.hArr1 100000

#kss_co1gt CertificateChecks.KernelCo1FiveL.HT2 CertificateChecks.KernelCo1FiveL.hArr2 100000

#kc_nattree CertificateChecks.KernelCo1FiveL.F1.R CertificateChecks.KernelCo1FiveL.clos1R
#kc_nattree CertificateChecks.KernelCo1FiveL.F1.C CertificateChecks.KernelCo1FiveL.clos1C
#kc_nattree CertificateChecks.KernelCo1FiveL.F1.W CertificateChecks.KernelCo1FiveL.clos1W
#kc_nattree CertificateChecks.KernelCo1FiveL.F2.R CertificateChecks.KernelCo1FiveL.clos2R
#kc_nattree CertificateChecks.KernelCo1FiveL.F2.C CertificateChecks.KernelCo1FiveL.clos2C
#kc_nattree CertificateChecks.KernelCo1FiveL.F2.W CertificateChecks.KernelCo1FiveL.clos2W

end
