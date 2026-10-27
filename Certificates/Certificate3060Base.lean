
module

public import Certificates.Kernel.MonsterB.Sp8Fold
public import CFSG.Monster.B.TwoA.Census.CosetEnumBits

@[expose] public section

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B CFSG.Monster.B.Rep4371 CFSG.Monster.B.TwoA.Census
  CFSG.Monster.Code CertificateChecks.Sp8Fold

namespace CertificateChecks.Batch3060

theorem c_comm : ∀ k : Fin 8,
    Model.Pauli.mul (false, 0, 127) (liftP k) = Model.Pauli.mul (liftP k) (false, 0, 127) := by
  decide +kernel

theorem foldN_ne : ∀ x < 256, Model.Pauli.mul (false, 0, 127) (foldN x) ≠ (false, 0, 0) ∧
    Model.Pauli.mul (false, 0, 127) (foldN x) ≠ (false, 0, 191) := by decide +kernel

theorem foldN_ne_corrupt :
    ¬ ∀ x < 256, Model.Pauli.mul (false, 0, 191) (foldN x) ≠ (false, 0, 0) := by decide +kernel

theorem closed : Model.Pauli.mul (false, 0, 127) (false, 0, 127) = (false, 0, 0) ∧
    Model.conjYN 3 (false, 0, 127) = (false, 0, 127) := by decide +kernel

theorem c_lt (y : Model.Pauli) (hy : y.2.1 < 2 ^ 12 ∧ y.2.2 < 2 ^ 12) :
    (Model.Pauli.mul (false, 0, 127) y).2.1 < 2 ^ 12 ∧
      (Model.Pauli.mul (false, 0, 127) y).2.2 < 2 ^ 12 :=
  ⟨Nat.xor_lt_two_pow (by norm_num) hy.1, Nat.xor_lt_two_pow (by norm_num) hy.2⟩

theorem lt_c (y : Model.Pauli) (hy : y.2.1 < 2 ^ 12 ∧ y.2.2 < 2 ^ 12) :
    (Model.Pauli.mul y (false, 0, 127)).2.1 < 2 ^ 12 ∧
      (Model.Pauli.mul y (false, 0, 127)).2.2 < 2 ^ 12 :=
  ⟨Nat.xor_lt_two_pow hy.1 (by norm_num), Nat.xor_lt_two_pow hy.2 (by norm_num)⟩

theorem comm_foldP (v : Fin 8 → ZMod 2) :
    Model.Pauli.mul (false, 0, 127) (foldP v) = Model.Pauli.mul (foldP v) (false, 0, 127) := by
  have h1 := c_lt _ (foldP_lt v)
  have h2 := lt_c _ (foldP_lt v)
  refine pauliQ_inj h1.1 h1.2 h2.1 h2.2 ?_
  have hc : ∀ k, Commute (pauliQ (false, 0, 127)) (pauliQ (liftP k)) := fun k => by
    change pauliQ (false, 0, 127) * pauliQ (liftP k) = pauliQ (liftP k) * pauliQ (false, 0, 127)
    rw [← pauliQ_mul, ← pauliQ_mul, c_comm]
  rw [pauliQ_mul, pauliQ_mul]
  exact (commute_foldP hc v).eq

theorem ne_foldP (v : Fin 8 → ZMod 2) :
    Model.Pauli.mul (false, 0, 127) (foldP v) ≠ (false, 0, 0) ∧
      Model.Pauli.mul (false, 0, 127) (foldP v) ≠ (false, 0, 191) := by
  obtain ⟨n, hn, rfl⟩ := CFSG.KC.BvecLoop.exists_bvec 8 v
  rw [foldP_bvec]
  exact foldN_ne n hn

end CertificateChecks.Batch3060

namespace Certificates

end Certificates
