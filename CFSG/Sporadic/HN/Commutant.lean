module

public import CFSG.Sporadic.HN.F5Group

public section

namespace CFSG.Sporadic.F5

open Matrix Native

variable {D : F5Data}

theorem det_ne_zero_of_pow_eq_one' {d n : ℕ} {M : Matrix (Fin d) (Fin d) (ZMod 5)} (hn : 0 < n)
    (h : M ^ n = 1) : M.det ≠ 0 := by
  intro h0
  have := congrArg Matrix.det h
  rw [Matrix.det_pow, h0, zero_pow hn.ne', Matrix.det_one] at this
  exact zero_ne_one this

theorem gA_eq' (h : (mA D).det ≠ 0) : gA D = GeneralLinearGroup.mkOfDetNeZero (mA D) h := by
  unfold gA
  rw [dite_eq_left h]

theorem gB_eq' (h : (mB D).det ≠ 0) : gB D = GeneralLinearGroup.mkOfDetNeZero (mB D) h := by
  unfold gB
  rw [dite_eq_left h]

theorem mat_a' (h : (mA D).det ≠ 0) : mat D (a D) = mA D := by
  change ((gA D : GL (Fin D.d) (ZMod 5)) : Matrix (Fin D.d) (Fin D.d) (ZMod 5)) = mA D
  rw [gA_eq' h]
  rfl

theorem mat_b' (h : (mB D).det ≠ 0) : mat D (b D) = mB D := by
  change ((gB D : GL (Fin D.d) (ZMod 5)) : Matrix (Fin D.d) (Fin D.d) (ZMod 5)) = mB D
  rw [gB_eq' h]
  rfl

noncomputable def seedEquiv' (hd : 0 < D.d) (hA : mA D ^ 2 = 1) (hB : mB D ^ 3 = 1) :
    (CFSG.Blueprint.NativeSporadic.seedMonoid 5 D.d 1 D.seedA D.seedB)ˣ ≃* J D :=
  (Blueprint.NativeSporadic.matrixSeedEquiv 5 D.d hd (mA D) (mB D)
    (det_ne_zero_of_pow_eq_one' (by norm_num) hA)
    (det_ne_zero_of_pow_eq_one' (by norm_num) hB)).trans (MulEquiv.subgroupCongr (by
      change _ = Subgroup.closure {gA D, gB D}
      rw [gA_eq' (det_ne_zero_of_pow_eq_one' (by norm_num) hA),
        gB_eq' (det_ne_zero_of_pow_eq_one' (by norm_num) hB)]))

theorem units_five_eq_one {u : (ZMod 5)ˣ} {n : ℕ} (hn : Nat.Coprime n 4) (h : u ^ n = 1) :
    u = 1 := by
  have h1 : orderOf u ∣ n := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf u ∣ 4 := by
    have := orderOf_dvd_natCard u
    rwa [Nat.card_eq_fintype_card, ZMod.card_units] at this
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hn h1 h2)

noncomputable abbrev detJ : J D →* (ZMod 5)ˣ :=
  (GeneralLinearGroup.det).comp (J D).subtype

theorem detJ_eq_one (hB : mB D ^ 3 = 1) {g : J D} {n : ℕ} (hn : Nat.Coprime n 4)
    (hx : (a D * (g⁻¹ * b D * g)) ^ n = 1) (z : J D) : detJ z = 1 := by
  have hb : detJ (b D) = 1 := by
    refine units_five_eq_one (n := 3) (by norm_num) ?_
    rw [← map_pow]
    have : b D ^ 3 = 1 := by
      apply mat_injective D
      have e : mat D (b D ^ 3) = mat D (b D) ^ 3 := rfl
      rw [e, mat_b' (det_ne_zero_of_pow_eq_one' (by norm_num) hB), hB]
      rfl
    rw [this, map_one]
  have hxd : detJ (a D * (g⁻¹ * b D * g)) = 1 :=
    units_five_eq_one hn (by rw [← map_pow, hx, map_one])
  have ha : detJ (a D) = 1 := by
    rw [map_mul, map_mul, map_mul, hb, map_inv, mul_one, inv_mul_cancel, mul_one] at hxd
    exact hxd
  have hker : (⊤ : Subgroup (J D)) ≤ detJ.ker := by
    rw [← closure_ab D, Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact ha
    · exact hb
  exact hker (Subgroup.mem_top z)

theorem center_J_eq_bot (hd : D.d % 4 = 1) (hA : mA D ^ 2 = 1) (hB : mB D ^ 3 = 1) {g : J D}
    {n : ℕ} (hn : Nat.Coprime n 4) (hx : (a D * (g⁻¹ * b D * g)) ^ n = 1)
    (hcomm : ∀ M : Matrix (Fin D.d) (Fin D.d) (ZMod 5), M * mA D = mA D * M →
      M * mB D = mB D * M → ∃ c : ZMod 5, M = c • 1) :
    Subgroup.center (J D) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_center_iff] at hz
  have hcA : mat D z * mA D = mA D * mat D z := by
    rw [← mat_a' (det_ne_zero_of_pow_eq_one' (by norm_num) hA)]
    exact congrArg (mat D) (hz (a D)).symm
  have hcB : mat D z * mB D = mB D * mat D z := by
    rw [← mat_b' (det_ne_zero_of_pow_eq_one' (by norm_num) hB)]
    exact congrArg (mat D) (hz (b D)).symm
  obtain ⟨c, hc⟩ := hcomm _ hcA hcB
  have hdet : (mat D z).det = 1 := by
    have := congrArg (fun u : (ZMod 5)ˣ => (u : ZMod 5)) (detJ_eq_one hB hn hx z)
    exact this
  rw [hc, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin] at hdet
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hdet
    exact zero_ne_one hdet
  have hc4 : c ^ 4 = 1 := ZMod.pow_card_sub_one_eq_one hc0
  have hc1 : c = 1 := by
    have e : D.d = 4 * (D.d / 4) + 1 := by omega
    rw [e, pow_succ, pow_mul, hc4, one_pow, one_mul] at hdet
    exact hdet
  rw [hc1, one_smul] at hc
  apply mat_injective D
  exact hc

end CFSG.Sporadic.F5
