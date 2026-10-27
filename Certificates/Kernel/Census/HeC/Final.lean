module

public import Certificates.Kernel.Census.HeC.T
public import Certificates.Kernel.Census.HeC.N
public import Certificates.Kernel.Census.HeC.W
import all Certificates.Kernel.Census.HeC.Data
public import Certificates.Kernel.LocalComp.HeFixBind
public import CFSG.Certificates.Kernel.Common.ForallChunks
public import Certificates.Data.Kernel.Census.HeConj2
public import CFSG.Certificates.Kernel.SporSch.PairJ3CntSound
public import CFSG.Sporadic.HeldB.OuterArithCheck

public section

namespace CertificateChecks.KernelCensus.HeCj

open CFSG.KC.HeConj CFSG.KS CFSG.KC.Enum

set_option maxRecDepth 1000000

#kc_forall_chunks nodes_ok (fun k => nodes32OK 32 6 d (List.range' (26 * k) 26) = true) 5
  CertificateChecks.KernelCensus.HeCj.kN 26

#kc_forall_chunks wits_ok (fun k => witF (List.range' (26 * k) 26) = true) 5
  CertificateChecks.KernelCensus.HeCj.kW 26

theorem all_of_chunks {f : Nat → Bool} (h : ∀ k < 5, (List.range' (26 * k) 26).all f = true) :
    (List.range 130).all f = true := by
  rw [List.all_eq_true]
  intro i hi
  have hi' := List.mem_range.1 hi
  exact List.all_eq_true.1 (h (i / 26) (by omega)) i (List.mem_range'_1.2 ⟨by omega, by omega⟩)

theorem he_conj : ∃ (d : HeD) (U w kS BP NS CH NR NL NT BT NQ BQ : ℕ)
    (PS PSI LR Ts LT PT QT : ℕ → ℕ),
    CFSG.Sporadic.HeldB.heUArr = CFSG.KS.Raw.unpack 8330 14 U ∧
    CFSG.KS.SporSch.TabChain 8330 w kS 5 BP NS CH NR NL NT BT NQ BQ PS PSI LR Ts LT PT QT
      CFSG.Sporadic.HeldB.heStrongArrs CFSG.Sporadic.HeldB.heBase.toArray
      CFSG.Sporadic.HeldB.heBase ∧
    d.xs.length = 11 ∧
    heConjOK 8330 32 6 CFSG.Sporadic.HeldB.heBase (CFSG.KS.SporSch.nfValidK 5 LR)
      (CFSG.KS.SporSch.nfPtT w NR NL LT PT 5) (pg 14 (mask 14) U) d = true := by
  have hN := Nat.eq_of_beq_eq_true kNs
  refine ⟨d, CertificateChecks.KernelLC.HeFix.PU, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, CertificateChecks.KernelLC.HeFix.heU_eq, CertificateChecks.KernelSporSch.HeTc.tc,
    Nat.eq_of_beq_eq_true kLen, ?_⟩
  simp only [heConjOK, Bool.and_eq_true]
  refine ⟨⟨⟨kT, ?_⟩, kB⟩, ?_⟩
  · rw [hN]
    exact all_of_chunks nodes_ok
  · rw [hN]
    exact all_of_chunks wits_ok

end CertificateChecks.KernelCensus.HeCj

end
