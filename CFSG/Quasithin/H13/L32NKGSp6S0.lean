module

public import CFSG.Quasithin.H13.L32NKGSp6Group

public section

namespace CFSG.Quasithin.H13.KGSp6

open CFSG.KGroups.Sp6

theorem validC_s0 : KGCert.ValidC s0 := by
  unfold KGCert.ValidC s0
  decide

theorem cols_s0 : Cols s0 := by
  unfold Cols
  decide +kernel

theorem s0_ne_oneC : s0 ≠ oneC := by decide

theorem powC_s0_seven : powC s0 7 = oneC := by decide +kernel

theorem validC_powC {s : List ℕ} (hs : KGCert.ValidC s) (k : ℕ) : KGCert.ValidC (powC s k) := by
  induction k with
  | zero =>
    have h0 : powC s 0 = oneC := rfl
    rw [h0, oneC_eq]
    exact KGCert.validC_oneC
  | succ k ih =>
    rw [powC, mulC_eq]
    exact KGCert.validC_mulC hs ih

theorem decodeC_powC {s : List ℕ} (hs : KGCert.ValidC s) (k : ℕ) :
    KGCert.decodeC (powC s k) = (KGCert.decodeC s) ^ k := by
  induction k with
  | zero => simp [powC, oneC_eq, KGCert.decodeC_oneC]
  | succ k ih =>
    rw [powC, mulC_eq, KGCert.decodeC_mulC _ _ (validC_powC hs k).1, ih, pow_succ']

theorem isIso_s0 : IsIso (KGCert.decodeC s0) := cols_iff.1 cols_s0

@[expose] noncomputable def s0u : Mat6ˣ := (isUnit_of_isIso isIso_s0).unit

theorem coe_s0u : (s0u : Mat6) = KGCert.decodeC s0 := IsUnit.unit_spec _

theorem s0u_mem : s0u ∈ SpU := by
  rw [mem_SpU, coe_s0u]
  exact isIso_s0

theorem orderOf_s0u : orderOf s0u = 7 := by
  have h7 : s0u ^ 7 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, coe_s0u, ← decodeC_powC validC_s0, powC_s0_seven, oneC_eq,
      KGCert.decodeC_oneC]
    rfl
  have h1 : s0u ≠ 1 := by
    intro h
    have h' : KGCert.decodeC s0 = KGCert.decodeC oneC := by
      rw [← coe_s0u, h, oneC_eq, KGCert.decodeC_oneC]
      rfl
    exact s0_ne_oneC (KGCert.decodeC_injOn validC_s0 (by rw [oneC_eq]; exact KGCert.validC_oneC) h')
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact orderOf_eq_prime h7 h1

end CFSG.Quasithin.H13.KGSp6
