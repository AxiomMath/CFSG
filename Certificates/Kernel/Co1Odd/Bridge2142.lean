module

public import Certificates.Kernel.Co1Odd.Chk2142
public import Certificates.Kernel.Co1Cover.Bridge
public import Certificates.Kernel.SporSch.Co1.Stab2148
public import CFSG.Certificates.Kernel.FixScanSound
public import CFSG.Certificates.Kernel.Co1BInvSound
public import CFSG.Certificates.Kernel.SporSch.Co1BfsSound
public import CFSG.Sporadic.Schreier.Co1OddACCheckInputs
import CFSG.Certificates.Kernel.Co1FixCount

public section

namespace CertificateChecks.KernelCo1Odd

open CFSG.KLie.CT CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.FixScan CFSG.KS.SporSch.VOrb CFSG.Sporadic.SmallF2.Native
  CFSG.Sporadic.Co1.OddNative CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Schreier.Native
  CertificateChecks.KernelCo1Cover CertificateChecks.KernelSporSch.Co1Orbs
  CertificateChecks.KernelSporSch.Co1Stab2148 CertificateChecks.KernelSporSch.Co1Packed

private theorem andB_true {a b : Bool} (h : andB a b = true) : a = true ∧ b = true := by
  cases a <;> cases b <;> simp_all [andB]

theorem g0 : G0 = CertificateChecks.KernelSporSch.Co1Stab.PH0 := rfl

theorem g1 : G1 = CertificateChecks.KernelSporSch.Co1Stab.PH1 := rfl

theorem regs_eq : oddACRegs = (G.map (unpackR 24)).toArray := by
  have hi : #[hRows0, hRows1] = ((G.take 2).map (unpackR 24)).toArray := by
    rw [h0u, h1u, ← CFSG.KS.SporSch.M24.unpackR_eq_unpack,
      ← CFSG.KS.SporSch.M24.unpackR_eq_unpack, ← g0, ← g1]
    rfl
  rw [oddACRegs, hi]
  exact prog_sound prog_ok

theorem r3 : oddReg oddACRegs 3 = unpackR 24 G3 := by
  rw [oddReg, regs_eq]
  rfl

theorem r8 : oddReg oddACRegs 8 = unpackR 24 G8 := by
  rw [oddReg, regs_eq]
  rfl

theorem r10 : oddReg oddACRegs 10 = unpackR 24 G10 := by
  rw [oddReg, regs_eq]
  rfl

theorem r15 : oddReg oddACRegs 15 = unpackR 24 G15 := by
  rw [oddReg, regs_eq]
  rfl

theorem r20 : oddReg oddACRegs 20 = unpackR 24 G20 := by
  rw [oddReg, regs_eq]
  rfl

theorem valid (M : Nat) : CFSG.Sporadic.Co1.OddNative.validRows (unpackR 24 M) = true :=
  validRows_unpackR M

theorem sq_eq {M : Nat} (h : Nat.beq (mulF 24 M M) (idF 24) = true) :
    mulRows 24 (unpackR 24 M) (unpackR 24 M) = idRows 24 := by
  rw [mul_sound h, CFSG.KC.F2W.unpackR_idF]

theorem ne_id {M : Nat} (h : notB (Nat.beq (M / 2 ^ (24 * 0) % 2 ^ 24) (idF 24 / 2 ^ (24 * 0) % 2 ^ 24)) =
    true) : unpackR 24 M ≠ idRows 24 := by
  intro e
  rw [← CFSG.KC.F2W.unpackR_idF] at e
  have h0 := congrArg (fun a : Array Nat => a[0]?.getD 0) e
  simp only [unpackR, Array.getElem?_ofFn] at h0
  simp only [Nat.ofNat_pos, ↓reduceDIte, Option.getD_some] at h0
  rw [h0] at h
  simp [notB, Nat.beq_refl] at h

theorem comm_eq {A B : Nat} (h : Nat.beq (mulF 24 A B) (mulF 24 B A) = true) :
    mulRows 24 (unpackR 24 A) (unpackR 24 B) = mulRows 24 (unpackR 24 B) (unpackR 24 A) := by
  rw [mul_sound (Nat.beq_refl (mulF 24 A B)), mul_sound (Nat.beq_refl (mulF 24 B A)),
    Nat.eq_of_beq_eq_true h]

theorem pow_eq {M n : Nat} (h : orderIsK 24 M n = true) :
    powRows 24 (unpackR 24 M) n = idRows 24 := by
  have h' := orderIs_sound h
  unfold CFSG.Sporadic.Co1.InvNative.orderIs at h'
  rw [Bool.and_eq_true, beq_iff_eq] at h'
  exact h'.1

theorem check : oddACCheckOf oddACRegs = true := by
  unfold oddACCheckOf
  rw [r3, r8, r10, r15, r20]
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨valid _, valid _⟩, sq_eq sq3⟩, ne_id ne3⟩, comm_eq c83⟩, pow_eq ord8⟩,
    sq_eq sq10⟩, ne_id ne10⟩, comm_eq c1510⟩, comm_eq c2010⟩, pow_eq ord15⟩,
    pow_eq ord20⟩

theorem counts : oddACCountsOf oddACRegs = true := by
  unfold oddACCountsOf
  rw [r3, r10, Bool.and_eq_true]
  constructor
  · obtain ⟨h1, h2⟩ := CFSG.KC.Co1Fix.fixK_sound fix3
    rw [CFSG.Sporadic.Co1.Module.countsOK, tr_sound tr3, qRows_eq, tr_sound trQ_ok, h1, h2]
    rfl
  · obtain ⟨h1, h2⟩ := CFSG.KC.Co1Fix.fixK_sound fix10
    rw [CFSG.Sporadic.Co1.Module.countsOK, tr_sound tr10, qRows_eq, tr_sound trQ_ok, h1, h2]
    rfl

theorem pts_eq : ∀ i < 98280, (BF PA PB 2 98280).pts[i]! = ptK F2.T i :=
  (vorbK_sound F2.hr (by decide) (by decide) (by decide) F2.hc0 F2.hcN F2.hb F2.hp).2.2.1

theorem sl_at {s : Nat} (hs : s < 39) :
    fixScanK F2.T [ATP] (s * 2520) 2520 (cl 0 s) = cl 0 (s + 1) ∧
      fixScanK F2.T [ATP, STP] (s * 2520) 2520 (cl 1 s) = cl 1 (s + 1) ∧
      fixScanK F2.T [CTP] (s * 2520) 2520 (cl 2 s) = cl 2 (s + 1) ∧
      fixScanK F2.T [CTP, S1TP, S2TP] (s * 2520) 2520 (cl 3 s) = cl 3 (s + 1) := by
  have h := SL.all s hs
  unfold sl at h
  obtain ⟨h1, h⟩ := andB_true h
  obtain ⟨h2, h⟩ := andB_true h
  obtain ⟨h3, h4⟩ := andB_true h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4⟩

theorem ends : cl 0 0 = 0 ∧ cl 1 0 = 0 ∧ cl 2 0 = 0 ∧ cl 3 0 = 0 ∧ cl 0 39 = 2280 ∧ cl 1 39 = 1 ∧
    cl 2 39 = 264 ∧ cl 3 39 = 2 := by
  have h := cl_ends
  obtain ⟨h1, h⟩ := andB_true h
  obtain ⟨h2, h⟩ := andB_true h
  obtain ⟨h3, h⟩ := andB_true h
  obtain ⟨h4, h⟩ := andB_true h
  obtain ⟨h5, h⟩ := andB_true h
  obtain ⟨h6, h⟩ := andB_true h
  obtain ⟨h7, h8⟩ := andB_true h
  exact ⟨Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h6,
    Nat.eq_of_beq_eq_true h7, Nat.eq_of_beq_eq_true h8⟩

theorem count_of {Ms : List Nat} {j : Nat} (h0 : cl j 0 = 0)
    (hs : ∀ s < 39, fixScanK F2.T Ms (s * 2520) 2520 (cl j s) = cl j (s + 1)) :
    oddCountFix (BF PA PB 2 98280) 98280 (Ms.map (unpackR 24)) = cl j 39 := by
  unfold oddCountFix
  rw [countBelow_congr (q := fun i => allFixK Ms (ptK F2.T i))
    (fun i hi => by rw [pts_eq i hi, allFixK_eq])]
  exact countBelow_slices (L := 2520) (NS := 39) h0 fun s hs' =>
    (fixScanK_eq F2.T Ms (s * 2520) 2520 (cl j s)).symm.trans (hs s hs')

theorem xcounts : oddACXOf (fullOrb 2) oddACRegs = true := by
  obtain ⟨e0, e1, e2, e3, f0, f1, f2, f3⟩ := ends
  unfold oddACXOf
  rw [r3, r8, r10, r15, r20, full2, tr_sound tr3, tr_sound tr8, tr_sound tr10, tr_sound tr15,
    tr_sound tr20]
  have c0 := count_of (Ms := [ATP]) e0 fun s hs => (sl_at hs).1
  have c1 := count_of (Ms := [ATP, STP]) e1 fun s hs => (sl_at hs).2.1
  have c2 := count_of (Ms := [CTP]) e2 fun s hs => (sl_at hs).2.2.1
  have c3 := count_of (Ms := [CTP, S1TP, S2TP]) e3 fun s hs => (sl_at hs).2.2.2
  simp only [List.map_cons, List.map_nil] at c0 c1 c2 c3
  rw [c0, c1, c2, c3, f0, f1, f2, f3]
  rfl

theorem facts2142 :
    (oddACCheckOf oddACRegs = true) ∧ (oddACCountsOf oddACRegs = true) ∧
      (oddACXOf (fullOrb 2) oddACRegs = true) :=
  ⟨check, counts, xcounts⟩

end CertificateChecks.KernelCo1Odd

end
