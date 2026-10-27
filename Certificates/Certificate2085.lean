module

public import CFSG.Sporadic.HNOddCore.FiveCheckInputs
public import CFSG.Sporadic.HNOddCore.FiveGens
import Certificates.Kernel.SporSch.HN.Pt2085
import Certificates.Kernel.SporSch.HN.Small2085
import Certificates.Certificate2102
import Certificates.Certificate2107

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore CFSG.KS.HNArr
open CertificateChecks.KernelSporSch.HNPt2085

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore CFSG.Sporadic.HNOddCore.Native in
theorem certificate2085 : (∀ x : X, fJ • x = x ↔ x.val ∈ FAData.fFixed) ∧
    (∀ j < 5, fJ * aGenJ j = aGenJ j * fJ) ∧ fJ * g5J = g5J * fJ ∧
    (∀ k < 6, ∀ t < 50, ∀ x : X, x.val = FAData.fFixed.getD t 0 →
      (iGen k • x).val = FAData.fFixed.getD ((FAData.iSmall[k]!).getD t 0) 0) ∧
    (∀ k < 4, ∀ t < 50, ∀ x : X, x.val = FAData.fFixed.getD t 0 →
      (a6Gen k • x).val = FAData.fFixed.getD ((FAData.a6Small[k]!).getD t 0) 0) ∧
    (∀ g ∈ Subgroup.closure (Set.range fun k : Fin 6 => iGen k), g • x0 = x0 →
      g ∈ Subgroup.closure (Set.range fun j : Fin 5 => aGenJ j)) ∧
    fiveSmallChecks = true := by
  refine ⟨fun x => ?_, fun j hj => fJ_comm_aGen hj, fJ_comm_g5, fun k hk t ht x hx => ?_,
    fun k hk t ht x hx => ?_, fun g hg hfix => stab_le hg ?_,
    KernelSporSch.HNSmall2085.small⟩
  · have h := fix_f x.isLt
    rw [gi_of_lt _ x.isLt] at h
    rw [Fin.ext_iff]
    exact h
  · have h := iG_omega hk ht
    rw [← hx, gi_of_lt _ x.isLt] at h
    exact h
  · have h := a6_omega hk ht
    rw [← hx, gi_of_lt _ x.isLt] at h
    exact h
  · have h0 : FAData.fFixed.getD 0 0 = 0 := by decide +kernel
    rw [h0, gi_of_lt _ (by decide)]
    exact congrArg Fin.val hfix

end Certificates
