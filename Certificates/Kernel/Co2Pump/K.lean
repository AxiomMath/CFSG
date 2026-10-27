module

public import Certificates.Kernel.Co2Pump.Bind
public import Certificates.Kernel.Misc.Perm.C2K
public import Certificates.Data.Kernel.Spor.Text
public import Certificates.Data.Kernel.MonsterB.BfsReplay
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Pump

open CFSG.KC.Enum CFSG.KS CFSG.RankThree.Native.F2 CertificateChecks.KernelMisc.Co2K
open CFSG.HardMathSupport.Solomon.Coordinator.Co2Pump CFSG.RankThree.PartTwo.Sec4.Item434SporE81
open CFSG.KC.Bfs (replayLoop replayOK)
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance

@[expose] noncomputable def NM (L : ℕ) : ℕ := PMt L

@[expose] noncomputable def NMI (L : ℕ) : ℕ := PMt (Nat.add 6 L)

@[expose] noncomputable def OM (k : ℕ) : ℕ := PMt (Nat.add 12 k)

@[expose] noncomputable def OMI (k : ℕ) : ℕ := PMt (Nat.add 14 k)

@[expose] noncomputable def QD (j : ℕ) : ℕ := DMt j

@[expose] noncomputable def DD (i : ℕ) : ℕ := DMt (Nat.add 3 i)

@[expose] noncomputable def ED (k : ℕ) : ℕ := DMt (Nat.add 7 k)

@[expose] noncomputable def wM (G : ℕ → ℕ) (w : List ℕ) : ℕ :=
  w.foldl (fun acc l => mmK (G l) acc) I22

@[expose] noncomputable def DF (k : ℕ) : ℕ :=
  mmK (mmK (mmK (pwK (DD 3) (Co2T.digit3 k 3)) (pwK (DD 2) (Co2T.digit3 k 2)))
    (pwK (DD 1) (Co2T.digit3 k 1))) (pwK (DD 0) (Co2T.digit3 k 0))

theorem tbind : CFSG.KS.Text.hexBind (PT.chars ++ ['\n']) 3 2300 12 6 0 6 PR = true := by
  quickRfl

theorem pbind : allN 6 (fun L => bindK (PR L) (NM L) (NMI L)) = true := by quickRfl

theorem obind : allN 2 (fun k => CFSG.KC.Misc.ArrEnum.arrBind CFSG.Sporadic.Co2Cert.co2OrigArrs[k]!
    2300 12 (OA k) && bindK (OA k) (OM k) (OMI k)) = true := by quickRfl

theorem psift : allN 6 (fun L => siftM vmK mmK I22 2300 VG BS LK mL PO TIM 6 0 (NM L)) = true := by
  quickRfl

theorem qchk : allN 3 (fun j => (co2E81.qW[j]!).all (fun l => Nat.blt l 2) &&
    Nat.beq (wM OM (co2E81.qW[j]!)) (QD j)) = true := by quickRfl

theorem dchk : allN 4 (fun i => ((co2E81.dW[0]!)[i]!).all (fun l => Nat.blt l 3) &&
    Nat.beq (wM QD ((co2E81.dW[0]!)[i]!)) (DD i)) = true := by quickRfl

theorem echk : allN 81 (fun k => Nat.beq (DF k) (ED k)) = true := by quickRfl

@[expose] noncomputable def fuseK (k : ℕ) : Bool :=
  k == 0 || (tPar[k]! == k && (k == kA || k == kB)) ||
    (decide (tPar[k]! < 81) && decide (tPar[k]! ≠ 0) && decide (tGen[k]! < 2) &&
      decide (tDep[tPar[k]!]! < tDep[k]!) &&
      Nat.beq (ED k) (mmK (mmK (NMI tGen[k]!) (ED tPar[k]!)) (NM tGen[k]!)))

theorem fchk : allN 81 fuseK = true := by quickRfl

@[expose] noncomputable def pairG (c L : ℕ) : Bool :=
  comm (NM L) (ED c) && Nat.beq (pwK (NM L) 5) I22 && !Nat.beq (NM L) I22

theorem pgA : allN 2 (fun i => pairG 3 (Nat.add 2 i)) = true := by quickRfl

theorem pgB : allN 2 (fun i => pairG 1 (Nat.add 4 i)) = true := by quickRfl

@[expose] noncomputable def EE (I : ℕ → ℕ) (i k : ℕ) : ℕ := f12 (I 0) (Nat.add (Nat.mul 2 i) k)

@[expose] noncomputable def PAR (I : ℕ → ℕ) (j : ℕ) : ℕ := f12 (I 1) j

@[expose] noncomputable def LAB (I : ℕ → ℕ) (j : ℕ) : ℕ := f12 (I 2) j

@[expose] noncomputable def SOK (I : ℕ → ℕ) (j : ℕ) : ℕ := f12 (I 3) j

@[expose] noncomputable def SOIK (I : ℕ → ℕ) (j : ℕ) : ℕ := f12 (I 4) j

@[expose] noncomputable def edgeK (P I : ℕ → ℕ) (g M i : ℕ) : Bool :=
  allN 2 fun k => Nat.blt (EE I i k) M && Nat.beq (P (EE I i k)) (mmK (P i) (NM (Nat.add g k)))

@[expose] noncomputable def treeK (P I : ℕ → ℕ) (g j : ℕ) : Bool :=
  Nat.beq j 0 || (Nat.blt (PAR I j) j && Nat.blt (LAB I j) 2 &&
    Nat.beq (P j) (mmK (P (PAR I j)) (NM (Nat.add g (LAB I j)))))

@[expose] noncomputable def ordK (P I : ℕ → ℕ) (M j : ℕ) : Bool :=
  Nat.blt (SOK I j) M && Nat.beq (SOIK I (SOK I j)) j &&
    (!(Nat.blt (Nat.add j 1) M) || Nat.blt (keyK P (SOK I j)) (keyK P (SOK I (Nat.add j 1))))

theorem rootA : Nat.beq (PAM 0) I22 = true := by quickRfl

theorem edgeA : allN 1100 (edgeK PAM PAI 2 1193) = true := by quickRfl

theorem treeA : allN 1193 (treeK PAM PAI 2) = true := by quickRfl

theorem ordA : allN 1193 (ordK PAM PAI 1193) = true := by quickRfl

theorem repA : (replayLoop (EE PAI) 2 1100 0 1 == some 1193) = true := by quickRfl

theorem rootB : Nat.beq (PBM 0) I22 = true := by quickRfl

theorem edgeB : allN 1100 (edgeK PBM PBI 4 2062) = true := by quickRfl

theorem treeB : allN 2062 (treeK PBM PBI 4) = true := by quickRfl

theorem ordB : allN 2062 (ordK PBM PBI 2062) = true := by quickRfl

theorem repB : (replayLoop (EE PBI) 2 1100 0 1 == some 2062) = true := by quickRfl

theorem repC0 : replayOK (fun i k => f12 (HC0E.F i) k) 2 3000 = true := by quickRfl

theorem repQ : replayOK (fun i k => f12 (HQE.F i) k) 2 125 = true := by quickRfl

@[expose] noncomputable def cntK (X : ℕ) : ℕ := ((List.range 125).filter fun j => comm (PQ j) X).length

@[expose] noncomputable def fiveK (i : ℕ) : Bool :=
  !(Nat.beq (pwK (PC0 i) 3) I22) || Nat.beq (PC0 i) I22 || decide (cntK (PC0 i) < 25)

theorem fiveA : allN 1500 fiveK = true := by quickRfl

theorem fiveB : allN 1500 (fun i => fiveK (Nat.add 1500 i)) = true := by quickRfl

end CertificateChecks.KernelCo2Pump

end
