module

public import Certificates.Data.Y2L.ClaimA

public section

namespace CertificateChecks.Batch442314

open CFSG.OddStandard.HigherRank.G2Three.Sec2

private def mul3F (m n : List Nat) : List Nat :=
  match m, n with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8], [b0, b1, b2, b3, b4, b5, b6, b7, b8] =>
    [(a0 * b0 + (a1 * b3 + (a2 * b6 + 0))) % 4,
      (a0 * b1 + (a1 * b4 + (a2 * b7 + 0))) % 4,
      (a0 * b2 + (a1 * b5 + (a2 * b8 + 0))) % 4,
      (a3 * b0 + (a4 * b3 + (a5 * b6 + 0))) % 4,
      (a3 * b1 + (a4 * b4 + (a5 * b7 + 0))) % 4,
      (a3 * b2 + (a4 * b5 + (a5 * b8 + 0))) % 4,
      (a6 * b0 + (a7 * b3 + (a8 * b6 + 0))) % 4,
      (a6 * b1 + (a7 * b4 + (a8 * b7 + 0))) % 4,
      (a6 * b2 + (a7 * b5 + (a8 * b8 + 0))) % 4]
  | _, _ => y2l_mul3 m n

private theorem mul3_eq_F (m n : List Nat) : y2l_mul3 m n = mul3F m n := by
  unfold mul3F
  split
  · rfl
  · rfl

private def pow3F (m : List Nat) : Nat → List Nat
  | 0 => y2l_one3
  | k + 1 => mul3F (pow3F m k) m

private theorem pow3_eq_F (m : List Nat) : ∀ k, y2l_pow3 m k = pow3F m k
  | 0 => rfl
  | k + 1 => by rw [y2l_pow3, pow3F, pow3_eq_F m k, mul3_eq_F]

private theorem all_split {α : Type} (L : List α) (f : α → Bool) (n : Nat) :
    L.all f = ((L.take n).all f && (L.drop n).all f) := by
  rw [← List.all_append, List.take_append_drop]

set_option maxHeartbeats 0 in
private theorem claimA_check : y2l_claimACheck () = true := by
  unfold y2l_claimACheck y2l_relOK
  simp only [mul3_eq_F, pow3_eq_F]
  rw [all_split (y2l_bits 9) _ 256, all_split (List.take 256 (y2l_bits 9)) _ 128,
    all_split (List.drop 256 (y2l_bits 9)) _ 128]
  simp only [Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> decide +kernel

end CertificateChecks.Batch442314

namespace Certificates

open CertificateChecks

open CFSG.OddStandard.HigherRank.G2Three.Sec2 in
theorem certificate442314 : y2l_claimACheck () = true :=
  CertificateChecks.Batch442314.claimA_check

end Certificates
