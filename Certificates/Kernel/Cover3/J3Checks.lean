module

public import Certificates.Kernel.Cover3.J3Data
public import Certificates.Kernel.SporSch.PairJ3.Chain
public import Certificates.Data.Kernel.B3S3K
public import Certificates.Data.Kernel.Spor.Prim
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCover3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.Misc.ArrEnum
open CFSG.KC.B3S3K (cm pw)
open CertificateChecks.KernelSporSch

@[expose] noncomputable def ivJ (p : ℕ) : ℕ := pinvS 6156 13 (mask 13) p

@[expose] noncomputable def cjJ (q t : ℕ) : ℕ := cm 6156 13 (cm 6156 13 q t) (ivJ q)

@[expose] noncomputable def cmJ (p q : ℕ) : Bool := Nat.beq (cm 6156 13 p q) (cm 6156 13 q p)

@[expose] noncomputable def prJ (u : ℕ) : ℕ :=
  cm 6156 13 (pw 6156 13 (JC.F 2) (u % 3)) (pw 6156 13 (JC.F 3) (u / 3))

@[expose] noncomputable def inQJ (c : ℕ) : Bool :=
  Nat.beq c (JC.F 0) || Nat.beq c (JC.F 1) || Nat.beq c (cm 6156 13 (JC.F 0) (JC.F 1))

@[expose] noncomputable def wordJ (k : ℕ) : Bool :=
  wordEqK 6156 13 (mask 13) (pidn 6156 13) PJ3.S PJ3.SI 5 (JW.getD k []) (JC.F k)

theorem c589303W : szOK 6156 13 = true := by quickRfl

theorem c589303P : allN 6 (fun k => permB 6156 13 (JC.F k)) = true := by quickRfl

theorem c589303S0 : wordJ 0 = true := by quickRfl
theorem c589303S1 : wordJ 1 = true := by quickRfl
theorem c589303S2 : wordJ 2 = true := by quickRfl
theorem c589303S3 : wordJ 3 = true := by quickRfl
theorem c589303S4 : wordJ 4 = true := by quickRfl
theorem c589303S5 : wordJ 5 = true := by quickRfl

theorem c589303Q : Nat.beq (cm 6156 13 (JC.F 0) (JC.F 0)) (pidn 6156 13) = true ∧
    Nat.beq (cm 6156 13 (JC.F 1) (JC.F 1)) (pidn 6156 13) = true ∧ cmJ (JC.F 0) (JC.F 1) = true ∧
    Nat.beq (JC.F 0) (pidn 6156 13) = false :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by decide +kernel⟩

theorem c589303O : Nat.beq (pw 6156 13 (JC.F 2) 3) (pidn 6156 13) = true ∧
    Nat.beq (pw 6156 13 (JC.F 3) 3) (pidn 6156 13) = true ∧ cmJ (JC.F 2) (JC.F 3) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl⟩

theorem c589303D : allN 9 (fun u => Nat.beq (JD u) (prJ u)) = true := by quickRfl

theorem c589303E : allN 9 (fun u => allN 9 fun v => u == v || !Nat.beq (JD u) (JD v)) = true := by
  quickRfl

theorem c589303I : inQJ (cjJ (JC.F 2) (JC.F 0)) = true ∧ inQJ (cjJ (JC.F 2) (JC.F 1)) = true ∧
    inQJ (cjJ (JC.F 3) (JC.F 0)) = true ∧ inQJ (cjJ (JC.F 3) (JC.F 1)) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem c589303G : Nat.beq (cjJ (JC.F 4) (JC.F 2)) (ivJ (JC.F 2)) = true ∧
    cmJ (JC.F 5) (JC.F 2) = true ∧ Nat.beq (cjJ (JC.F 5) (JC.F 3)) (ivJ (JC.F 3)) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl⟩

end CertificateChecks.KernelCover3

end
