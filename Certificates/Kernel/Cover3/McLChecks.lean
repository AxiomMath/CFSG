module

public import Certificates.Kernel.Cover3.McLData
public import Certificates.Kernel.Census.McLChain
public import Certificates.Data.Kernel.B3S3K
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCover3

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.ArrEnum
open CFSG.KC.B3S3K (cm pw)

@[expose] noncomputable def siftC (G : ℕ) : Bool :=
  Nat.beq (Nat.shiftRight G (275 * 9)) 0 && allN 275 (fun t => Nat.blt (pg 9 (mask 9) G t) 275) &&
    siftK 275 9 (mask 9) (275 * 9) (pidn 275 9) KernelCensus.McLC.LR KernelCensus.McLC.TRI
      KernelCensus.McLC.BP 5 0 G

@[expose] noncomputable def ivC (p : ℕ) : ℕ := pinvS 275 9 (mask 9) p

@[expose] noncomputable def cjC (q t : ℕ) : ℕ := cm 275 9 (cm 275 9 q t) (ivC q)

@[expose] noncomputable def prC (u : ℕ) : ℕ :=
  cm 275 9 (pw 275 9 (MC.F 1) (u % 3)) (pw 275 9 (MC.F 2) (u / 3))

@[expose] noncomputable def cmC (p q : ℕ) : Bool := Nat.beq (cm 275 9 p q) (cm 275 9 q p)

theorem c589302W : szOK 275 9 = true := by quickRfl

theorem c589302P : allN 5 (fun k => permB 275 9 (MC.F k)) = true := by quickRfl

theorem c589302S : allN 5 (fun k => siftC (MC.F k)) = true := by quickRfl

theorem c589302Z : Nat.beq (cm 275 9 (MC.F 0) (MC.F 0)) (pidn 275 9) = true ∧
    Nat.beq (MC.F 0) (pidn 275 9) = false :=
  ⟨by quickRfl, by decide +kernel⟩

theorem c589302O : Nat.beq (pw 275 9 (MC.F 1) 3) (pidn 275 9) = true ∧
    Nat.beq (pw 275 9 (MC.F 2) 3) (pidn 275 9) = true :=
  ⟨by quickRfl, by quickRfl⟩

theorem c589302C : cmC (MC.F 1) (MC.F 2) = true ∧ cmC (MC.F 1) (MC.F 0) = true ∧
    cmC (MC.F 2) (MC.F 0) = true ∧ cmC (MC.F 4) (MC.F 1) = true :=
  ⟨by quickRfl, by quickRfl, by quickRfl, by quickRfl⟩

theorem c589302D : allN 9 (fun u => allN 9 fun v => u == v || !Nat.beq (prC u) (prC v)) = true := by
  quickRfl

theorem c589302G : Nat.beq (cjC (MC.F 3) (MC.F 1)) (ivC (MC.F 1)) = true ∧
    Nat.beq (cjC (MC.F 4) (MC.F 2)) (ivC (MC.F 2)) = true :=
  ⟨by quickRfl, by quickRfl⟩

end CertificateChecks.KernelCover3

end
