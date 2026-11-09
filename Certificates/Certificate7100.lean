module

public import CFSG.Quasithin.H13.L32NKGCertInputs
import all CFSG.Quasithin.H13.L32NKGCertInputs

public section

namespace CertificateChecks.Batch7100

open CFSG.Quasithin.H13.KGCert in
@[expose] def qPresM (t q₀ : ℕ) (δ : List ℕ) : Bool :=
  match δ with
  | [a, b, c, d] =>
    qfN t q₀ a == bt q₀ 0 && qfN t q₀ b == bt q₀ 1 && qfN t q₀ c == bt q₀ 2 &&
      qfN t q₀ d == bt q₀ 3
  | δ => qPresN t q₀ δ

open CFSG.Quasithin.H13.KGCert in
theorem qPresN_eq : qPresN = qPresM := by
  funext t q₀ δ
  rcases δ with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩ <;> rfl

open CFSG.Quasithin.H13.KGCert in
@[expose] def tOK (t : ℕ) : Bool :=
  !(nondegN t) || (let F := spFramesN t
    (List.range 16).all fun q₀ => decide ((F.filter (qPresM t q₀)).length ≤ 120))

theorem all_range_of_chunks (f : ℕ → Bool) {c m n : ℕ} (hc : 0 < c) (hn : n ≤ m * c)
    (h : ∀ j < m, (List.range' (j * c) c).all f = true) : (List.range n).all f = true := by
  rw [List.all_eq_true]
  intro x hx
  rw [List.mem_range] at hx
  have hj : x / c < m := (Nat.div_lt_iff_lt_mul hc).2 (by omega)
  refine List.all_eq_true.1 (h (x / c) hj) x ?_
  rw [List.mem_range'_1]
  have h1 := Nat.div_mul_le_self x c
  have h2 := Nat.lt_div_mul_add (a := x) hc
  omega

set_option maxHeartbeats 0 in
private theorem t_chunk_0 : (List.range' (0 * 16) 16).all tOK = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem t_chunk_1 : (List.range' (1 * 16) 16).all tOK = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem t_chunk_2 : (List.range' (2 * 16) 16).all tOK = true := by
  decide +kernel

set_option maxHeartbeats 0 in
private theorem t_chunk_3 : (List.range' (3 * 16) 16).all tOK = true := by
  decide +kernel

private theorem check_0M : (List.range 64).all tOK = true := by
  refine all_range_of_chunks tOK (c := 16) (m := 4) (by decide) (by decide) fun j hj => ?_
  match j, hj with
  | 0, _ => exact t_chunk_0
  | 1, _ => exact t_chunk_1
  | 2, _ => exact t_chunk_2
  | 3, _ => exact t_chunk_3
  | j + 4, h => exact absurd h (by omega)

private theorem check_0 : CFSG.Quasithin.H13.KGCert.sp4QuadCheck = true := by
  unfold CFSG.Quasithin.H13.KGCert.sp4QuadCheck
  rw [qPresN_eq]
  exact check_0M

end CertificateChecks.Batch7100

namespace Certificates

open CertificateChecks

theorem certificate7100 : CFSG.Quasithin.H13.KGCert.sp4QuadCheck = true := CertificateChecks.Batch7100.check_0

end Certificates

