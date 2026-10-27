module

public import Certificates.Kernel.B433Alt.ChOK
public import Certificates.Kernel.B433Alt.OmOK
public import Certificates.Kernel.B433Alt.MdOK

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelB433.NegB

open CFSG.KC.B4A

@[expose] noncomputable def upd (F : Nat → Nat) (k v : Nat) (r : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (F r) v (Nat.beq r k)

open CFSG.KD.B4A CFSG.KD.B4AC in
theorem neg_el : sB (EL 2140) (fun d => elOK LP RD RW EL (upd EW 2140 (EW 0))
    (baseOf (elJ d) (elL d)) 2140) = false := by
  decide +kernel

open CFSG.KD.B4A CFSG.KD.B4AC in
theorem neg_orb : sB (CL 600) (fun kk => Nat.beq (orbRun LP RD RW EL EW (Nat.shiftRight kk 4)
    (Nat.land kk 15) (LG kk) (LN kk) (CN 600) (CR 600) (CS 600)) (CT 600 + 1)) = false := by
  decide +kernel

open CFSG.KD.B4A in
theorem neg_letter : sB (upd LP 3 (LP 4) 3) (fun P => sB (CFSG.KD.YM432P.F 3) fun F =>
    ptsOK (fun x => Nat.beq (CFSG.KC.Y333.pget P x) (CFSG.KC.YModel.fieldAt 32 F x)) 0 1000) = false := by
  decide +kernel

open CFSG.KD.B4A in
theorem neg_pair : sB (upd LP 23 (LP 32) 23) (fun R => sB (LP 1) fun P => sB (LP 3) fun Q =>
    ptsOK (fun x => Nat.beq (CFSG.KC.Y333.pget R x) (CFSG.KC.Y333.pget P (CFSG.KC.Y333.pget Q x))) 0 4000) =
    false := by
  decide +kernel

open CFSG.KD.B4AN in
theorem neg_netcol : netColOK (upd MS 40 (MS 41)) CB 1 3 = false := by
  decide +kernel

open CFSG.KD.B4AN in
theorem neg_rel : relOK (upd MS 75 0) (omRels.getD 2 []) = false := by
  decide +kernel

open CFSG.KD.B4AN in
theorem neg_segment : segChk MS CFSG.KD.B4A.RD CFSG.KD.B4A.RW CFSG.KD.B4A.PW CB LIVE RN RL GS
    (upd XO 500 (XO 500 / 2)) SJ ST SA SN STL NSEG 500 = false := by
  decide +kernel

open CFSG.KD.B4AN in
theorem neg_seg_count : segChk MS CFSG.KD.B4A.RD CFSG.KD.B4A.RW CFSG.KD.B4A.PW CB LIVE RN RL GS
    XO SJ ST SA (upd SN 501 (SN 501 + 1)) STL NSEG 501 = false := by
  decide +kernel

open CFSG.KD.B4AN in
theorem neg_seg_gen : segChk MS CFSG.KD.B4A.RD CFSG.KD.B4A.RW CFSG.KD.B4A.PW CB LIVE RN RL
    (upd GS 9 (GS 9 + 1)) XO SJ ST SA SN STL NSEG 443 = false := by
  decide +kernel

open CFSG.KD.B4AN in
theorem neg_fin : finChk CFSG.KD.B4A.RD CFSG.KD.B4A.RW CFSG.KD.B4A.PW CB LIVE RN RL GS
    (upd GN 9 (GN 9 - 1)) XO SJ ST SA SN STL NSEG 9 = false := by
  decide +kernel

end CertificateChecks.KernelB433.NegB

end
