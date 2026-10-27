module

public import Certificates.Kernel.ChengHeld.PropsS4
public import Certificates.Kernel.ChengHeld.PropsEA
public import Certificates.Kernel.ChengHeld.PropsAutF
public import CFSG.Certificates.Kernel.ChengHeldS4Sound
public import CFSG.Certificates.Kernel.ChengHeldPropsEASound

public section

namespace CertificateChecks.KernelChengHeld.P

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.PEnum CFSG.PSL3Four.Native
open CFSG.OddStandard.ChengHeldData CFSG.OddStandard.ChengHeld.Model CFSG.KC.ChengHeldS2
open CFSG.KC.ChengHeldP CertificateChecks.KernelChengHeld
open CertificateChecks.KernelChengHeld.S2 (IX0 IX1 IV0 IV1)

@[expose] def ea4C (k : ℕ) : ℕ := if k = 0 then 55 else if k = 1 then 143 else if k = 2 then 29 else 0

theorem eaCounts0 {H : Type} [Group H] (R : Rep (mkReg 0) H) :
    (mkReg 0).eaCounts = [55, 143, 29, 0, 0, 0] := by
  have hW := rows_of bound0
  have hi := p6138_ea0i
  have hu := p6138_ea0u
  have hw := p6138_ea0w
  have hz := p6138_eaz
  simp only [bAnd_iff] at hi hu hw hz
  have l1 := levelOK_one R hW hi.1 hi.2.2
  have l2 := levelOK_succ R hW hi.1 hi.2.1 l1 hu.1 hw.1
  have l3 := levelOK_succ R hW hi.1 hi.2.1 l2 hu.2 hw.2.1
  have l4 := levelOK_succ R hW hi.1 hi.2.1 l3 hz.1.1 hw.2.2
  have l5 := levelOK_succ R hW hi.1 hi.2.1 l4 hz.1.2.1 hz.1.2.2.2.1
  have l6 := levelOK_succ R hW hi.1 hi.2.1 l5 hz.1.2.2.1 hz.1.2.2.2.2
  have := eaCounts_of (L := EAL0) (c := ea4C) R fun k hk => by
    interval_cases k
    exacts [l1, l2, l3, l4, l5, l6]
  rw [this]
  rfl

theorem eaCounts1 {H : Type} [Group H] (R : Rep (mkReg 1) H) :
    (mkReg 1).eaCounts = [55, 143, 29, 0, 0, 0] := by
  have hW := rows_of bound1
  have hi := p6138_ea1i
  have hu := p6138_ea1u
  have hw := p6138_ea1w
  have hz := p6138_eaz
  simp only [bAnd_iff] at hi hu hw hz
  have l1 := levelOK_one R hW hi.1 hi.2.2
  have l2 := levelOK_succ R hW hi.1 hi.2.1 l1 hu.1 hw.1
  have l3 := levelOK_succ R hW hi.1 hi.2.1 l2 hu.2 hw.2.1
  have l4 := levelOK_succ R hW hi.1 hi.2.1 l3 hz.2.1.1 hw.2.2
  have l5 := levelOK_succ R hW hi.1 hi.2.1 l4 hz.2.1.2.1 hz.2.1.2.2.2.1
  have l6 := levelOK_succ R hW hi.1 hi.2.1 l5 hz.2.1.2.2.1 hz.2.1.2.2.2.2
  have := eaCounts_of (L := EAL1) (c := ea4C) R fun k hk => by
    interval_cases k
    exacts [l1, l2, l3, l4, l5, l6]
  rw [this]
  rfl

theorem s4glt : (∀ j < 7, h0 j < 256) ∧ ∀ j < 7, h1 j < 256 := by
  have h := p6138_s4lt
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Nat.blt_eq] at h
  exact h

theorem struct4_0 : struct4OK 0 = true := by
  have hd := regData (α := 0) (by norm_num) chPres_true
  let R : Rep (mkReg 0) _ := (mkReg_eq 0) ▸ hd.rep
  exact struct4OK_of (n := 256) (m := n0) (inv := j0) (g := h0) (qs := []) R
    (treeSpec_mkReg (by norm_num) chPres_true) bound0.N_eq bound0.m_eq bound0.inv_eq bound0.g_eq
    (by norm_num) (mlt_of (by norm_num) bound0) s4glt.1 (eaCounts0 R) p6138_s4cl0 p6138_s4d0
    p6138_s4w0 (fun h => absurd rfl h) p6138_s4r0

theorem struct4_1 : struct4OK 1 = true := by
  have hd := regData (α := 1) (by norm_num) chPres_true
  let R : Rep (mkReg 1) _ := (mkReg_eq 1) ▸ hd.rep
  exact struct4OK_of (n := 256) (m := n1) (inv := j1) (g := h1) R
    (treeSpec_mkReg (by norm_num) chPres_true) bound1.N_eq bound1.m_eq bound1.inv_eq bound1.g_eq
    (by norm_num) (mlt_of (by norm_num) bound1) s4glt.2 (eaCounts1 R) p6138_s4cl1 p6138_s4d1
    p6138_s4w1 (fun _ => p6138_s4q1) p6138_s4r1

end CertificateChecks.KernelChengHeld.P

end
