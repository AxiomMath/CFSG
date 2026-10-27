module

public import Certificates.Kernel.Co1B.Syl2B
public import Certificates.Kernel.Co1B.KC24511A
public import Certificates.Kernel.Co1B.KC24511B
public import Certificates.Kernel.Co1B.KC24511C
public import Certificates.Kernel.Co1B.KC24511D
public import CFSG.Certificates.Kernel.SporSch.Co1HypOneSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.H24511

open CFSG.KS.SporSch.M24 CFSG.KS.Raw CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block
  CFSG.Sporadic.Co1Block.Native CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1.InvNative
  CFSG.EvenSporadicStandard.TwoCo1.HypOne CertificateChecks.KernelCo1B.Syl2B

theorem kF_all {i : Nat} (hi : i < 32768) :
    fourConjK S2.M S2.MI 10 (ST.P i) (CC i) = true := by
  obtain ⟨c, r, hr, rfl⟩ : ∃ c r, r < 4096 ∧ i = 4096 * c + r :=
    ⟨i / 4096, i % 4096, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod i 4096).symm⟩
  have hc : c < 8 := by omega
  interval_cases c
  · exact MatL.allN_iff.1 kF0 r hr
  · exact MatL.allN_iff.1 kF1 r hr
  · exact MatL.allN_iff.1 kF2 r hr
  · exact MatL.allN_iff.1 kF3 r hr
  · exact MatL.allN_iff.1 kF4 r hr
  · exact MatL.allN_iff.1 kF5 r hr
  · exact MatL.allN_iff.1 kF6 r hr
  · exact MatL.allN_iff.1 kF7 r hr

theorem cg_eq : ((List.range twoBBray.length).map fun i => unpack 24 24 (S2.M i)).toArray =
    gensArr 10 S2.M := by
  apply Array.ext (by simp [gensArr]; rfl)
  intro l h₁ h₂
  simp [gensArr]

theorem cgi_eq : (gensArr 10 S2.M).map inv = gensArr 10 S2.MI := by
  apply Array.ext (by simp [gensArr])
  intro l h₁ h₂
  have hl : l < 10 := by simpa [gensArr] using h₁
  simp only [Array.getElem_map, gensArr, Array.getElem_ofFn]
  exact (invOKK_sound (MatL.allN_iff.1 kInvB l hl)).2

theorem conj_ok : (bfsTree ST.N ST.P ST.PAR ST.LAB).pts.all
    (fun p => !fourRows p || conjAtLeast (gensArr 10 S2.M) (gensArr 10 S2.MI) p 5) = true := by
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < 32768 := by simpa [bfsTree, hN.1] using hi
  simp only [bfsTree, Array.getElem_ofFn]
  exact fourConjK_sound (kF_all hi')

open Certificates in
theorem c24511 : CFSG.EvenSporadicStandard.TwoCo1.HypOne.sylowCheckB = true := by
  unfold sylowCheckB sylowCheckOf
  simp only []
  rw [dagS_eq, bray_eq, dag₁_eq, sg_eq, gt_eq.1, gt_eq.2, bray_ok, cg_eq, cgi_eq, conj_ok]
  simp [bfsTree, hN.1]

end CertificateChecks.KernelCo1B.H24511

end
