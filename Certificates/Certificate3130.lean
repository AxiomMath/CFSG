module

public import Certificates.Data.BT2K1Vocab
public import CFSG.Certificates.Kernel.Common.BvecLoop

public section

open CFSG.Monster.B.GSide CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.Code CFSG.KC.BvecLoop

namespace CertificateChecks.Batch3130

open CFSG.Monster.B.GSide CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.Code CFSG.KC.BvecLoop

@[expose] def qT : ℕ :=
  41009698136747687093990734023869748781331473807686848120313033673730012803072

@[expose] def k1Wit : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
   0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 133, 0, 0, 133, 0, 0, 0, 0, 133, 0, 0, 133, 137, 0, 0, 137,
   161, 0, 0, 161, 0, 0, 0, 0, 133, 0, 0, 133, 137, 0, 0, 137, 145, 0, 0, 145, 145, 0, 0, 145,
   137, 0, 0, 137, 133, 0, 0, 133, 0, 0, 0, 0, 0, 130, 0, 0, 0, 130, 0, 0, 0, 130, 0, 0, 0, 0,
   130, 0, 0, 130, 0, 0, 0, 0, 130, 0, 0, 0, 130, 0, 0, 0, 130, 0, 0, 130, 0, 0, 0, 0, 130, 0,
   0, 0, 130, 0, 0, 0, 130, 0, 0, 0, 130, 0, 0, 0, 130, 0, 0, 0, 130, 0, 0, 130, 0, 0]

@[expose] def badB (x : ℕ) : Bool := !qT.testBit x && qT.testBit (x ^^^ 1)

@[expose] def edgeB (v w : ℕ) : Bool :=
  !(v == w) && !qT.testBit (v ^^^ w) && !qT.testBit (1 ^^^ v ^^^ w)

theorem kQ : ∀ x < 2 ^ 8, decide (qPoly (bvec 8 x) = 1) = qT.testBit x := by decide +kernel

theorem kReach : ∀ x < 2 ^ 8, badB x = true →
    (x == 129 || edgeB 129 x ||
      (decide (k1Wit.getD x 0 < 2 ^ 8) && badB (k1Wit.getD x 0) && edgeB 129 (k1Wit.getD x 0) &&
        edgeB (k1Wit.getD x 0) x)) = true := by decide +kernel

theorem zmod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem bvec_xor (a b : ℕ) : bvec 8 a + bvec 8 b = bvec 8 (a ^^^ b) := by
  funext i
  simp only [Pi.add_apply, bvec, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> decide

theorem single_eq : (Pi.single 0 1 : Fin 8 → ZMod 2) = bvec 8 1 := by
  funext i
  revert i
  decide

theorem root_eq : k1Root = bvec 8 129 := by
  funext i
  revert i
  decide

theorem q_one {y : ℕ} (hy : y < 2 ^ 8) : qPoly (bvec 8 y) = 1 ↔ qT.testBit y = true := by
  rw [← kQ y hy, decide_eq_true_iff]

theorem q_zero {y : ℕ} (hy : y < 2 ^ 8) : qPoly (bvec 8 y) = 0 ↔ qT.testBit y = false := by
  rw [← Bool.not_eq_true, ← q_one hy]
  rcases zmod2_cases (qPoly (bvec 8 y)) with h | h <;> rw [h] <;> decide

theorem bad_iff {x : ℕ} (hx : x < 2 ^ 8) : K1Bad (bvec 8 x) ↔ badB x = true := by
  have h1 : x ^^^ 1 < 2 ^ 8 := Nat.xor_lt_two_pow hx (by norm_num)
  rw [K1Bad, single_eq, bvec_xor, q_zero hx, Nat.xor_comm, q_one h1, badB]
  simp

theorem edge_iff {a b : ℕ} (ha : a < 2 ^ 8) (hb : b < 2 ^ 8) :
    K1Edge (bvec 8 a) (bvec 8 b) ↔ edgeB a b = true := by
  have h1 : a ^^^ b < 2 ^ 8 := Nat.xor_lt_two_pow ha hb
  have h2 : 1 ^^^ a ^^^ b < 2 ^ 8 :=
    Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (by norm_num) ha) hb
  have hne : bvec 8 a ≠ bvec 8 b ↔ a ≠ b :=
    ⟨fun h e => h (e ▸ rfl), fun h e => h (bvec_inj ha hb e)⟩
  rw [K1Edge, single_eq, bvec_xor, bvec_xor, bvec_xor, q_zero h1, q_zero h2, hne, edgeB]
  simp [and_assoc]

end CertificateChecks.Batch3130

namespace Certificates

open CertificateChecks.Batch3130 in
open CFSG.Monster.B.GSide in
theorem certificate3130 : ∀ v : Fin 8 → ZMod 2, K1Bad v →
      v = k1Root ∨ K1Edge k1Root v ∨ ∃ m, K1Bad m ∧ K1Edge k1Root m ∧ K1Edge m v := by
  intro v hv
  obtain ⟨x, hx, rfl⟩ := exists_bvec 8 v
  have h := kReach x hx ((bad_iff hx).1 hv)
  have hr : (129 : ℕ) < 2 ^ 8 := by norm_num
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  rw [root_eq]
  rcases h with (h | h) | ⟨⟨⟨hm, h1⟩, h2⟩, h3⟩
  · exact Or.inl (congrArg (bvec 8) h)
  · exact Or.inr (Or.inl ((edge_iff hr hx).2 h))
  · exact Or.inr (Or.inr ⟨_, (bad_iff hm).2 h1, (edge_iff hr hm).2 h2, (edge_iff hm hx).2 h3⟩)

end Certificates
