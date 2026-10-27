
module

public import Certificates.Kernel.Census.HSC.Bind
public import Certificates.Kernel.Census.HSC.T
public import Certificates.Kernel.Census.HSC.N0
public import Certificates.Kernel.Census.HSC.N1
public import CFSG.Certificates.Kernel.Census.ConjYProof
public import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHSBase
import CFSG.RankThree.Native.HSMcLAuxData
import CFSG.Sporadic.Schreier.PairHSCert
import Certificates.Data.CFSGNative.Schreier.Check
import CFSG.RankThree.Native.HSMcLSmallCheckInputs
public import CFSG.Certificates.Kernel.Census.ConjSound

public section

namespace CertificateChecks.KernelCensus.HSC

open CFSG.KC.Census CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.ComponentClassification.RankTwoSporadic.HS

#kc_forall_chunks nodes_ok (fun k => (List.range' (12 * k) 12).all nodeF = true) 9
  CertificateChecks.KernelCensus.HSC.kN 12

theorem nodes_all : ∀ i < d.nodes.size, nodeF i = true := by
  intro i hi
  rw [Nat.eq_of_beq_eq_true kNs] at hi
  have hk : i / 12 < 9 := by omega
  have h := List.all_eq_true.1 (nodes_ok (i / 12) hk) i
  exact h (List.mem_range'_1.2 ⟨by omega, by omega⟩)

theorem hs_conj : ∃ (inX inW : Array ℕ → Bool) (D : ConjData),
    (∀ a, validA 100 a = true → inX a = true → hsInP a = true) ∧
    (∀ a, validA 100 a = true → inW a = true →
      (hsInP a || hsInP (compA 100 (hs100Arr 15) a)) = true) ∧
    conjCensusOKW 100 hsPS inX (fun _ => true) inW false false false D #[] = true ∧
    D.xs.all inW = true ∧ D.xs.length = 10 := by
  obtain ⟨inX, inW, D, h1, h2, h3, h4, h5⟩ := conjCensusY_of_packed (ps := hsPS)
    (testP := hsInP) (inP := inP) (d := d) (Xs := Xs) (by norm_num) (by norm_num) (by norm_num)
    (fun a b g ha hb => Bool.eq_iff_iff.2 ((hsInP_iff a g ha).trans (hsInP_iff b g hb).symm))
    (fun _ hc hv => inP_eq hc hv) u_eq (Bool.and_eq_true _ _ ▸ kU).1
    (Bool.and_eq_true _ _ ▸ kU).2 kCanon kX kW kPc kInv kTab kRl kR nodes_all
  exact ⟨inX, inW, D, h1, h2, h3, h4, h5.trans (Nat.eq_of_beq_eq_true kLen)⟩

end CertificateChecks.KernelCensus.HSC

end
