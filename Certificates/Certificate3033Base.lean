
module

public import CFSG.Monster.B.Fischer.InducedOrbitChecksInputs

@[expose] public section

open CFSG.Monster.B.Fischer

namespace CertificateChecks.Batch3033

@[expose] noncomputable def hm (i : ℕ) : ℕ := hexMask ((hexCat (hCat i)).map jEmb)

theorem hm_succ : ∀ i < 76, hm i < hm (i + 1) := by decide +kernel

theorem hm_corrupt : ¬ hm 76 < hm 0 := by decide +kernel

theorem hm_lt {i j : ℕ} (hij : i < j) (hj : j < 77) : hm i < hm j := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | rfl
    · exact (ih h (by omega)).trans (hm_succ j (by omega))
    · exact hm_succ i (by omega)

theorem hexCat_inj : ∀ i < 77, ∀ j < 77, hexCat (hCat i) = hexCat (hCat j) → i = j := by
  intro i hi j hj e
  have he : hm i = hm j := by rw [hm, hm, e]
  rcases Nat.lt_trichotomy i j with h | h | h
  · exact absurd he (hm_lt h hj).ne
  · exact h
  · exact absurd he (hm_lt h hi).ne'

end CertificateChecks.Batch3033

namespace Certificates

end Certificates
