
module

public import Certificates.Kernel.MonsterB.Sp8Fold
public import CFSG.Monster.B.TwoA.Census.CosetEnumBits

@[expose] public section

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B CFSG.Monster.B.Rep4371 CFSG.Monster.B.TwoA.Census
  CFSG.Monster.Code CertificateChecks.Sp8Fold

namespace CertificateChecks.Batch3057

theorem foldP_single : ∀ k : Fin 8, foldP (Pi.single k 1) = liftP k := by decide +kernel

theorem foldN_one : ∀ x < 256, foldN x = (false, 0, 0) → x = 0 := by decide +kernel

theorem foldN_r : ∀ x < 256, foldN x = (false, 0, 191) → x = 128 := by decide +kernel

theorem foldN_r_ne : ¬ ∀ x < 256, foldN x = (false, 0, 191) → x = 0 := by decide +kernel

theorem comm_corrupt :
    Model.Pauli.mul (false, 63, 0) (false, 0, 1) ≠ Model.Pauli.mul (false, 0, 1) (false, 63, 0) := by
  decide +kernel

theorem bvec_128 : bvec 8 128 = Pi.single 7 1 := by decide +kernel

theorem mul_lt {x y : Model.Pauli} (hx : x.2.1 < 2 ^ 12 ∧ x.2.2 < 2 ^ 12)
    (hy : y.2.1 < 2 ^ 12 ∧ y.2.2 < 2 ^ 12) :
    (Model.Pauli.mul x y).2.1 < 2 ^ 12 ∧ (Model.Pauli.mul x y).2.2 < 2 ^ 12 :=
  ⟨Nat.xor_lt_two_pow hx.1 hy.1, Nat.xor_lt_two_pow hx.2 hy.2⟩

theorem foldP_add (v w : Fin 8 → ZMod 2) :
    foldP (v + w) = Model.Pauli.mul (foldP v) (foldP w) := by
  have h := mul_lt (foldP_lt v) (foldP_lt w)
  refine pauliQ_inj (foldP_lt (v + w)).1 (foldP_lt (v + w)).2 h.1 h.2 ?_
  rw [pauliQ_mul, pauliQ_foldP_add]

theorem foldP_eq_one (v : Fin 8 → ZMod 2) (h : foldP v = (false, 0, 0)) : v = 0 := by
  obtain ⟨n, hn, rfl⟩ := CFSG.KC.BvecLoop.exists_bvec 8 v
  rw [foldP_bvec] at h
  rw [foldN_one n hn h, bvec_zero]

theorem foldP_eq_r (v : Fin 8 → ZMod 2) (h : foldP v = (false, 0, 191)) : v = Pi.single 7 1 := by
  obtain ⟨n, hn, rfl⟩ := CFSG.KC.BvecLoop.exists_bvec 8 v
  rw [foldP_bvec] at h
  rw [foldN_r n hn h, bvec_128]

theorem conjYN_foldP (v : Fin 8 → ZMod 2) : Model.conjYN 3 (foldP v) = foldP v := by
  have h := conjYN_lt (foldP_lt v).1 (foldP_lt v).2
  exact pauliQ_inj h.1 h.2 (foldP_lt v).1 (foldP_lt v).2 (pauliQ_conjYN_foldP v)

end CertificateChecks.Batch3057

namespace Certificates

end Certificates
