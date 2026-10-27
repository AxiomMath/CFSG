
module

public import Certificates.Kernel.Census.Co3C.Bind
public import Certificates.Kernel.Census.Co3C.T
public import Certificates.Kernel.Census.Co3C.N0
public import Certificates.Kernel.Census.Co3C.N1
public import CFSG.Certificates.Kernel.Census.ConjYProof
public import CFSG.Certificates.Kernel.Common.ForallChunks
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicCo3Base
import CFSG.Sporadic.Schreier.Co3Arrays
import CFSG.Sporadic.Schreier.Co3OrderCheckInputs
meta import CFSG.Sporadic.Schreier.Co3Cert
meta import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Certificates.Kernel.Census.ConjSound

public section

namespace CertificateChecks.KernelCensus.Co3C

open CFSG.KC.Census CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.ComponentClassification.RankTwoSporadic.Cert CFSG.ComponentClassification.RankTwoSporadic.Co3

#kc_forall_chunks nodes_ok (fun k => (List.range' (13 * k) 13).all nodeF = true) 6
  CertificateChecks.KernelCensus.Co3C.kN 13

theorem nodes_all : ∀ i < d.nodes.size, nodeF i = true := by
  intro i hi
  rw [Nat.eq_of_beq_eq_true kNs] at hi
  have hk : i / 13 < 6 := by omega
  have h := List.all_eq_true.1 (nodes_ok (i / 13) hk) i
  exact h (List.mem_range'_1.2 ⟨by omega, by omega⟩)

theorem co3_conj : ∃ (inX inW : Array ℕ → Bool) (D : ConjData),
    (∀ a, validA 276 a = true → inX a = true → co3InP a = true) ∧
    (∀ a, validA 276 a = true → inW a = true →
      (co3InP a || co3InP (compA 276 (idA 276) a)) = true) ∧
    conjCensusOKW 276 co3PS inX (fun _ => true) inW false false false D #[] = true ∧
    D.xs.all inW = true ∧ D.xs.length = 10 := by
  obtain ⟨inX, inW, D, h1, h2, h3, h4, h5⟩ := conjCensusY_of_packed (ps := co3PS)
    (testP := co3InP) (inP := inP) (d := d) (Xs := Xs) (by norm_num) (by norm_num) (by norm_num)
    (fun a b g ha hb => Bool.eq_iff_iff.2 ((co3InP_iff a g ha).trans (co3InP_iff b g hb).symm))
    (fun _ hc hv => inP_eq hc hv) u_eq (Bool.and_eq_true _ _ ▸ kU).1
    (Bool.and_eq_true _ _ ▸ kU).2 kCanon kX kW kPc kInv kTab kRl kR nodes_all
  exact ⟨inX, inW, D, h1, h2, h3, h4, h5.trans (Nat.eq_of_beq_eq_true kLen)⟩

end CertificateChecks.KernelCensus.Co3C

end
