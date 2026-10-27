
module

public import CFSG.Sporadic.Co1.Module.TwoBFrameInputs
import Certificates.Kernel.Co1M.Frame10077
import Certificates.Kernel.Co1M.TreeX10077
import Certificates.Kernel.Co1M.TreeY10077
import Certificates.Kernel.Co1M.S10077
import Certificates.Kernel.Co1M.Cent10077
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Sporadic.Co1.Module.InvDataBase
public import CFSG.Sporadic.Co1.Module.OddCentCardBase
public import CFSG.Sporadic.Co1.Module.TwoBTree

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1M CFSG.KD.Co1M CFSG.KD.Co1B CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.TreeK

noncomputable def w77 : CFSG.Sporadic.Co1.Module.TwoB.TwoBW where
  RB := RB77
  AP := AP77
  N1T := N1T77
  N2T := N2T77
  SBT := SBT77
  P1 := P77n1
  P2 := P77n2
  PS := P77sB
  P1i := P77n1i
  P2i := P77n2i
  M01W := M01W77
  M0W := M0W77
  W0 := W77
  H := H77
  Hi := H77i
  G := G77
  WP := WP77
  WPi := WP77i
  TP := TP77
  TX := T77X
  TPt := T77P
  TY := T77Y
  TS := T77S
  TU := T77U
  YT := YT77
  ST := ST77
  EW := EW77
  EM := EM77
  ET := ET77
  SW := SW77
  UM := UM77
  UT := UT77
  GW := GW77
  Q := QP77
  QI := QIP77

theorem sb77 : getL 0 RB77 2 = SBK := rfl

theorem ok77 : CFSG.Sporadic.Co1.Module.TwoB.TwoBOK w77 where
  regs := c77_regs
  rbl := Nat.eq_of_beq_eq_true (by quickRfl)
  sb := by
    rw [CertificateChecks.KernelCo1B.rowsSB_eq]
    exact congrArg (CFSG.KC.Co1F2.unpackR 24) sb77.symm
  tr := by
    have h := b77_tr
    rw [← b77_n12.1, ← b77_n12.2, ← sb77] at h
    exact h
  e := by
    have h := b77_e
    rw [← b77_n12.1, ← b77_n12.2] at h
    exact h
  u := b77_u
  perm := b77_perm
  words := b77_words
  fix := b77_fix
  gw := b77_gw
  q := b77_q
  sym := fr77_sym
  dist := fr77_dist_chk
  ind1 := ind77_n1_chk
  ind2 := ind77_n2_chk
  indS := ind77_sB_chk
  indE := fun k hk => by
    rcases k with _ | _ | _ | _ | _ | k
    · exact ind77_e0_chk
    · exact ind77_e1_chk
    · exact ind77_e2_chk
    · exact ind77_e3_chk
    · exact ind77_e4_chk
    · omega
  econj := by
    have h := e77_conj_chk
    rw [← sb77] at h
    exact h
  einv := e77_invs_chk
  elen := e77_len
  tx := tx77_chk
  txl := Nat.eq_of_beq_eq_true (by quickRfl)
  tp := tp77_chk
  tpl := Nat.eq_of_beq_eq_true (by quickRfl)
  ty := ty77_chk
  tyl := Nat.eq_of_beq_eq_true (by quickRfl)
  ts := ts77_chk
  tsl := Nat.eq_of_beq_eq_true (by quickRfl)
  tu := tu77_chk
  tul := Nat.eq_of_beq_eq_true (by quickRfl)
  uni := uni77_chk
  wd := by decide +kernel
  lens := by decide +kernel

end CertificateChecks.KernelCo1M

@[expose] public section

namespace Certificates

end Certificates
