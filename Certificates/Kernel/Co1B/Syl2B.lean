module

public import Certificates.Kernel.Co1B.Cent2045
public import Certificates.Kernel.Co1B.ChkS24513
public import Certificates.Kernel.Co1B.KQ24513
public import CFSG.Certificates.Kernel.SporSch.Co1BfsSound
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Syl2B

open CFSG.KS.SporSch.M24 CFSG.KS.Raw CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block
  CFSG.Sporadic.Co1Block.Native CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1.InvNative
  CFSG.EvenSporadicStandard.TwoCo1.HypOne CertificateChecks.KernelSporSch.Co1Packed

theorem dag₁_eq : brayRows aR twoBD1 = ((List.range 43).map fun i => unpack 24 24 (Cent2045.D1.M i),
    (List.range 43).map fun i => unpack 24 24 (Cent2045.D1.MI i), true) :=
  dagIK_sound Cent2045.base_eq Cent2045.kD1

theorem bray_eq : brayElts (brayRows aR twoBD1) twoBBray =
    (List.range twoBBray.length).map fun i => unpack 24 24 (S2.M i) :=
  brayElts_of_K Cent2045.base_eq Cent2045.kD1 Cent2045.kI kBindS

theorem dagS_eq : dag (brayElts (brayRows aR twoBD1) twoBBray) sylD2B =
    ((List.range S2.N).map fun i => unpack 24 24 (S2.M i),
      (List.range S2.N).map fun i => unpack 24 24 (S2.MI i), true) :=
  dagIK_sound bray_eq kS2

theorem hN : ST.N = 32768 ∧ ∀ j ∈ sylIdxB, j < S2.N := by
  have h := kN
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact ⟨Nat.eq_of_beq_eq_true h.1, h.2⟩

theorem getD_range_map (f : Nat → Array Nat) {N j : Nat} (hj : j < N) (d : Array Nat) :
    ((List.range N).map f).getD j d = f j := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]

theorem sg_eq : (sylIdxB.map fun j => ((List.range S2.N).map fun i => unpack 24 24 (S2.M i)).getD j
    (one ())).toArray = gensArr 4 SM := by
  apply Array.ext (by simp [gensArr, sylIdxB])
  intro l h₁ h₂
  have hl : l < 4 := by simpa [sylIdxB] using h₁
  have hj : sylIdxB[l]'(by simpa [sylIdxB] using hl) < S2.N := hN.2 _ (List.getElem_mem _)
  simp only [List.getElem_toArray, List.getElem_map, gensArr, Array.getElem_ofFn, SM]
  rw [getD_range_map _ hj, List.getD_eq_getElem _ _ (by simpa [sylIdxB] using hl)]

theorem gt_eq : gtBFS (gensArr 4 SM) 32769 = bfsTree ST.N ST.P ST.PAR ST.LAB ∧
    gtOK (gensArr 4 SM) (bfsTree ST.N ST.P ST.PAR ST.LAB) = true :=
  gtBFS_of_K kQ

theorem bray_ok : ((List.range twoBBray.length).map fun i => unpack 24 24 (S2.M i)).all
    (fun g => mul g aR == mul aR g && mul g (inv g) == one) = true := by
  rw [List.all_eq_true]
  intro g hg
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hg
  have hi' : i < twoBBray.length := List.mem_range.1 hi
  have hbi : S2.M i = Cent2045.D1.M (twoBBray[i] - 1) := by
    simpa using bindFromK_sound (k := 0) kBindS i hi'
  have hcm := commK_sound Cent2045.kC _ (List.getElem_mem hi')
  have hinv := invOKK_sound (MatL.allN_iff.1 kInvB i hi')
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq, hinv.2, hinv.1, aR_u, mul_unpackK, mul_unpackK,
    hbi, hcm]
  exact ⟨rfl, rfl⟩

end CertificateChecks.KernelCo1B.Syl2B

end
