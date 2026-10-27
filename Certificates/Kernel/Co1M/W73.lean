
module

public import Certificates.Kernel.Co1M.K73T0
public import Certificates.Kernel.Co1M.K73T1
public import Certificates.Kernel.Co1M.K73T2
public import Certificates.Kernel.Co1M.K73T3
public import Certificates.Kernel.Co1M.K73T4
public import Certificates.Kernel.Co1M.K73T5
public import Certificates.Kernel.Co1M.K73Z
public import Certificates.Kernel.Co1M.Regs10071
public import Certificates.Kernel.Co1M.Z10071
public import Certificates.Kernel.Co1M.Z71S0
public import Certificates.Kernel.Co1M.Z71S1
public import Certificates.Kernel.Co1M.Z71S2
public import Certificates.Kernel.Co1M.Z71S3
public import Certificates.Kernel.Co1M.Z71S4
public import Certificates.Kernel.Co1M.Z71S5
public import Certificates.Kernel.Co1Cover.Bridge
public import CFSG.Sporadic.Co1.Module.OddLitInputs
public import CFSG.Certificates.Kernel.SortTreeSound
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.KLie.CT CFSG.KC.Odd73 CFSG.KC.SortTree CFSG.KC.InvFam
  CFSG.KD.Co1M CFSG.KD.Co1Odd CFSG.Sporadic.Co1.Module.Odd CertificateChecks.KernelCo1Cover

@[expose] noncomputable def w73 : OddW where
  R := R73
  P := PROG71
  T := ⟨S73tab, 4, 18, 64, 2859⟩
  aux := A73tab
  Z0G := Z0G
  Z0P := Z0P
  Z0Par := Z0Par
  Z0Lab := Z0Lab
  V1 := FV1
  V2 := FV2
  t1i := 168617

theorem w73_R : R73 = cmRP71 := eq_of_beq (by quickRfl)

theorem w73_progL : PROG71 =CFSG.Sporadic.Co1.Module.Odd.prog := eq_of_beq (by quickRfl)

theorem w73_len : lenL R73 = 94 := Nat.eq_of_beq_eq_true (by quickRfl)

theorem w73_lt {a b c : ℕ} (h : a < b) (e : b = c) : a < c := e ▸ h

theorem w73_slices : ∀ q < 179, ta73S q = true := by
  intro q hq
  by_cases h0 : q < 30
  · exact TA73x0.all q h0
  have e : ∀ a, a ≤ q → Nat.add a (q - a) = q := fun a ha => by
    change a + (q - a) = q
    omega
  by_cases h1 : q < 60
  · have := TA73x1.all (q - 30) (w73_lt (b := 30) (by omega) rfl)
    unfold ta73F1 at this
    rwa [e 30 (by omega)] at this
  by_cases h2 : q < 90
  · have := TA73x2.all (q - 60) (w73_lt (b := 30) (by omega) rfl)
    unfold ta73F2 at this
    rwa [e 60 (by omega)] at this
  by_cases h3 : q < 120
  · have := TA73x3.all (q - 90) (w73_lt (b := 30) (by omega) rfl)
    unfold ta73F3 at this
    rwa [e 90 (by omega)] at this
  by_cases h4 : q < 150
  · have := TA73x4.all (q - 120) (w73_lt (b := 30) (by omega) rfl)
    unfold ta73F4 at this
    rwa [e 120 (by omega)] at this
  · have := TA73x5.all (q - 150) (w73_lt (b := 29) (by omega) rfl)
    unfold ta73F5 at this
    rwa [e 150 (by omega)] at this

theorem w73_andB {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem w73_chunk : ∀ c < 2859, chunkOK (act73 R73) 14 (fun _ => true) (getL 0 R73 27) S73tab
    182919 576 4 18 64 c = true := by
  intro c hc
  have h := (w73_andB (w73_slices (c / 16) (by omega))).1
  unfold t73K chunksK at h
  have := (allN_iff _ _).1 h (c % 16) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (c / 16) 16) (c % 16) = c := by
    change c / 16 * 16 + c % 16 = c
    omega
  rwa [e] at this

theorem w73_aux : ∀ c < 2859, auxRun73 R73 S73tab A73tab 576 4 18 (c * 64)
    (cntF 182919 64 (c * 64)) = true := by
  intro c hc
  have h := (w73_andB (w73_slices (c / 16) (by omega))).2
  unfold a73K at h
  have := (allN_iff _ _).1 h (c % 16) (Nat.mod_lt _ (by norm_num))
  have e : Nat.add (Nat.mul (c / 16) 16) (c % 16) = c := by
    change c / 16 * 16 + c % 16 = c
    omega
  rwa [e] at this

theorem w73_all1344 (f : Nat → Bool) (h0 : (List.range' 0 336).all f = true)
    (h1 : (List.range' 336 336).all f = true) (h2 : (List.range' 672 336).all f = true)
    (h3 : (List.range' 1008 112).all f = true) (h4 : (List.range' 1120 112).all f = true)
    (h5 : (List.range' 1232 112).all f = true) : (List.range' 0 1344).all f = true := by
  have e : (1344 : Nat) = 336 + 336 + 336 + 112 + 112 + 112 := rfl
  rw [e, all_range'_add, all_range'_add, all_range'_add, all_range'_add, all_range'_add]
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩

theorem w73_z1 : treeOK71 Z1G Z1P Z1Par Z1Lab 1344 = true ∧ canonL Z1P = true := by
  have hlen : Z1P.length = 1344 := by
    have h := z71_head1
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    exact h.1.1.1
  constructor
  · unfold treeOK71 ptsOK71
    rw [z71_head1, Bool.true_and]
    exact w73_all1344 _ z71_pts0 z71_pts1 z71_pts2 z71_pts3 z71_pts4 z71_pts5
  · unfold canonL canonsL
    rw [hlen]
    exact w73_all1344 _ z71_can0 z71_can1 z71_can2 z71_can3 z71_can4 z71_can5

theorem ok73 : OddOK w73 := by
  have hz0 := z73_z0
  simp only [Bool.and_eq_true, beq_iff_eq] at hz0
  have hz2 := z71_tree2
  simp only [Bool.and_eq_true] at hz2
  have hg := z71_gens
  simp only [Bool.and_eq_true, beq_iff_eq] at hg
  have hf := z73_faith
  simp only [Bool.and_eq_true] at hf
  refine
    { rA := ?_, rB := ?_, progEq := w73_progL, prog := ?_, len := w73_len, canon := z73_canon,
      tree := ⟨by decide, w73_chunk⟩, t1 := z73_t1, aux := w73_aux, aux0 := ?_, auxN := ?_,
      z0G := hz0.2, z0 := hz0.1.1.1, z0d := hz0.1.1.2, z0c := hz0.1.2, z1G := ?_,
      z1 := w73_z1.1, z1d := z71_dist1, z1c := w73_z1.2, z2G := ?_, z2 := hz2.1.1,
      z2d := hz2.1.2, z2c := hz2.2, faith1 := hf.1, faith2 := hf.2 }
  · change CFSG.Sporadic.Co1.Module.dat.rowsA = unpackR 24 (getL 0 R73 0)
    rw [w73_R]
    exact rowsA_eq
  · change CFSG.Sporadic.Co1.Module.dat.rowsB = unpackR 24 (getL 0 R73 1)
    rw [w73_R]
    exact rowsB_eq
  · change progK 24 R73 PROG71 2 = true
    rw [w73_R]
    exact cm71_prog_chk
  · exact (Bool.and_eq_true _ _ ▸ z73_aux).1
  · exact (Bool.and_eq_true _ _ ▸ z73_aux).2
  · change Z1G = [getL 0 R73 81, getL 0 R73 82]
    rw [w73_R]
    exact hg.1
  · change Z2G = [getL 0 R73 83, getL 0 R73 84]
    rw [w73_R]
    exact hg.2

end CertificateChecks.KernelCo1M

end
