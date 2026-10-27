module

public import Certificates.Kernel.Co1M.C10071
public import Certificates.Kernel.Co1M.Z10071
public import Certificates.Kernel.Co1M.Z71S0
public import Certificates.Kernel.Co1M.Z71S1
public import Certificates.Kernel.Co1M.Z71S2
public import Certificates.Kernel.Co1M.Z71S3
public import Certificates.Kernel.Co1M.Z71S4
public import Certificates.Kernel.Co1M.Z71S5
public import CFSG.Sporadic.Co1.Module.LeechOddLitInputs
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1F2 CFSG.KD.Co1Odd CFSG.Sporadic.Co1.Module.Odd

theorem c71_all1344 (f : Nat → Bool) (h0 : (List.range' 0 336).all f = true)
    (h1 : (List.range' 336 336).all f = true) (h2 : (List.range' 672 336).all f = true)
    (h3 : (List.range' 1008 112).all f = true) (h4 : (List.range' 1120 112).all f = true)
    (h5 : (List.range' 1232 112).all f = true) : (List.range' 0 1344).all f = true := by
  have e : (1344 : Nat) = 336 + 336 + 336 + 112 + 112 + 112 := rfl
  rw [e, all_range'_add, all_range'_add, all_range'_add, all_range'_add, all_range'_add]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩

theorem c71_zgens : (zIdx[1]!).map rr = Z1G.map (unpackR 24) := by
  have hg := z71_gens
  simp only [Bool.and_eq_true, beq_iff_eq] at hg
  rw [hg.1]
  have e : zIdx[1]! = [81, 82] := rfl
  rw [e, List.map_cons, List.map_cons, List.map_nil, c71_rr (by rw [c71_len]; norm_num),
    c71_rr (by rw [c71_len]; norm_num)]
  rfl

theorem c71_zOne : zOneLitOK := by
  have hlen : Z1P.length = 1344 := by
    have h := z71_head1
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact h.1.1.1
  refine ⟨c71_zgens, ?_, z71_dist1, ?_, ?_⟩
  · unfold treeOK71 ptsOK71
    rw [z71_head1, Bool.true_and]
    exact c71_all1344 _ z71_pts0 z71_pts1 z71_pts2 z71_pts3 z71_pts4 z71_pts5
  · unfold canonL canonsL
    rw [hlen]
    exact c71_all1344 _ z71_can0 z71_can1 z71_can2 z71_can3 z71_can4 z71_can5
  · unfold noConjOK ncsOK71
    rw [hlen]
    exact c71_all1344 _ z71_nc0 z71_nc1 z71_nc2 z71_nc3 z71_nc4 z71_nc5

end CertificateChecks.KernelCo1M

end
