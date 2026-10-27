module

public import CFSG.Certificates.Kernel.BabyMonster.PktSound
public import CFSG.Certificates.Kernel.BabyMonster.PktBind.All
public import Certificates.Kernel.BabyMonster.ForallLt
public import CFSG.Certificates.Kernel.BabyMonster.Native.Small
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Certificates.Kernel.BabyMonster.PktBind.Check0
public import CFSG.Certificates.Kernel.BabyMonster.PktBind.Check1
public import CFSG.Certificates.Kernel.BabyMonster.PktBind.Check2
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

public section

namespace CertificateChecks.KernelBM.Pkt

open CFSG.KC.YModel CFSG.KC.BM CFSG.KC.BM.B64 CFSG.KC.BM.Pkt CFSG.KC.BM.Dyadic

@[expose] def selK (g : Nat) : Nat := if g = 0 then 1 else g + 22

@[expose] noncomputable def monoTs : List Nat :=
  [nthN G0.b0 0, nthN G1.b0 0, nthN G2.b0 0, nthN G3.b0 0, nthN G4.b0 0, nthN G5.b0 0,
    nthN G6.b0 0, nthN G7.b0 0, nthN G8.b0 0, nthN G9.b0 0, nthN G10.b0 0, nthN G11.b0 0,
    nthN G12.b0 0, nthN G13.b0 0, nthN G14.b0 0, nthN G15.b0 0, nthN G16.b0 0, nthN G17.b0 0,
    nthN G18.b0 0, nthN G19.b0 0, nthN G20.b0 0, nthN G21.b0 0, nthN G22.b0 0, nthN G23.b0 0]

theorem lines_ok : ∀ i < 48, lineOK (lineOf CFSG.KD.PktBind.CH CFSG.KD.PktBind.S i) = true := by
  forall_lt_consts CFSG.KD.PktBind.ln 48

theorem pieces_ok : piecesOK CFSG.KD.PktBind.CH = true := by quickRfl

section Tabs

set_option maxRecDepth 100000

theorem tab0 : tabOK (nthN monoTs 0) = true := by quickRfl
theorem tab1 : tabOK (nthN monoTs 1) = true := by quickRfl
theorem tab2 : tabOK (nthN monoTs 2) = true := by quickRfl
theorem tab3 : tabOK (nthN monoTs 3) = true := by quickRfl
theorem tab4 : tabOK (nthN monoTs 4) = true := by quickRfl
theorem tab5 : tabOK (nthN monoTs 5) = true := by quickRfl
theorem tab6 : tabOK (nthN monoTs 6) = true := by quickRfl
theorem tab7 : tabOK (nthN monoTs 7) = true := by quickRfl
theorem tab8 : tabOK (nthN monoTs 8) = true := by quickRfl
theorem tab9 : tabOK (nthN monoTs 9) = true := by quickRfl
theorem tab10 : tabOK (nthN monoTs 10) = true := by quickRfl
theorem tab11 : tabOK (nthN monoTs 11) = true := by quickRfl
theorem tab12 : tabOK (nthN monoTs 12) = true := by quickRfl
theorem tab13 : tabOK (nthN monoTs 13) = true := by quickRfl
theorem tab14 : tabOK (nthN monoTs 14) = true := by quickRfl
theorem tab15 : tabOK (nthN monoTs 15) = true := by quickRfl
theorem tab16 : tabOK (nthN monoTs 16) = true := by quickRfl
theorem tab17 : tabOK (nthN monoTs 17) = true := by quickRfl
theorem tab18 : tabOK (nthN monoTs 18) = true := by quickRfl
theorem tab19 : tabOK (nthN monoTs 19) = true := by quickRfl
theorem tab20 : tabOK (nthN monoTs 20) = true := by quickRfl
theorem tab21 : tabOK (nthN monoTs 21) = true := by quickRfl
theorem tab22 : tabOK (nthN monoTs 22) = true := by quickRfl
theorem tab23 : tabOK (nthN monoTs 23) = true := by quickRfl

end Tabs

theorem tabs_ok : ∀ g < 24, tabOK (nthN monoTs g) = true := by
  forall_lt_consts CertificateChecks.KernelBM.Pkt.tab 24

theorem numer_mono : ∀ g < 24, ∀ t u : Nat, t < 4371 →
    numerOf CFSG.Monster.B.Native.packetRows (selK g) t u = kNumMono (nthN monoTs g) t u := by
  have h : ∀ g < 24,
      monoOK (lineOf CFSG.KD.PktBind.CH CFSG.KD.PktBind.S (selK g)) (nthN monoTs g) = true := by
    forall_lt_consts CFSG.KD.PktBind.mono 24
  intro g hg
  have hj : selK g < 48 := by
    unfold selK
    split <;> omega
  rw [CFSG.Monster.B.Native.packetRows, CFSG.KD.PktBind.eq]
  exact numerOf_mono CFSG.KD.PktBind.lines CFSG.KD.PktBind.nlines lines_ok hj (h g hg) pieces_ok
    (tabs_ok g hg)

theorem numer_sparse24 : ∀ t u : Nat, t < 4371 → u < 4371 →
    numerOf CFSG.Monster.B.Native.packetRows (selK 24) t u = kNumSparse SG24 t u := by
  rw [CFSG.Monster.B.Native.packetRows, CFSG.KD.PktBind.eq]
  exact numerOf_sparse CFSG.KD.PktBind.lines CFSG.KD.PktBind.nlines lines_ok (by simp [selK])
    CFSG.KD.PktBind.sp24 pieces_ok

theorem numer_sparse25 : ∀ t u : Nat, t < 4371 → u < 4371 →
    numerOf CFSG.Monster.B.Native.packetRows (selK 25) t u = kNumSparse SG25 t u := by
  rw [CFSG.Monster.B.Native.packetRows, CFSG.KD.PktBind.eq]
  exact numerOf_sparse CFSG.KD.PktBind.lines CFSG.KD.PktBind.nlines lines_ok (by simp [selK])
    CFSG.KD.PktBind.sp25 pieces_ok

end CertificateChecks.KernelBM.Pkt

end
