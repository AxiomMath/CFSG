module

public import CFSG.Quasithin.EmptyFaithful.S152N2Fix

public section

namespace CFSG.Quasithin

namespace S152N2

variable {V : Type*} [CommGroup V]

theorem sq_eq_one_mod_fifteen {k : ℤ} (h : (15 : ℤ) ∣ k * k - 1) :
    k % 15 = 1 ∨ k % 15 = 4 ∨ k % 15 = 11 ∨ k % 15 = 14 := by
  have hz : ((k * k - 1 : ℤ) : ZMod 15) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h
  have hz' : (k : ZMod 15) * (k : ZMod 15) = 1 := by
    have : ((k * k - 1 : ℤ) : ZMod 15) = (k : ZMod 15) * (k : ZMod 15) - 1 := by push_cast; ring
    rw [this] at hz
    exact sub_eq_zero.mp hz
  have hcases : ∀ x : ZMod 15, x * x = 1 → x = 1 ∨ x = 4 ∨ x = 11 ∨ x = 14 := by decide
  rcases hcases _ hz' with h1 | h4 | h11 | h14
  · left
    have := (ZMod.intCast_eq_intCast_iff' (a := k) (b := 1) (c := 15)).mp (by simpa using h1)
    simpa using this
  · right; left
    have := (ZMod.intCast_eq_intCast_iff' (a := k) (b := 4) (c := 15)).mp (by simpa using h4)
    simpa using this
  · right; right; left
    have := (ZMod.intCast_eq_intCast_iff' (a := k) (b := 11) (c := 15)).mp (by simpa using h11)
    simpa using this
  · right; right; right
    have := (ZMod.intCast_eq_intCast_iff' (a := k) (b := 14) (c := 15)).mp (by simpa using h14)
    simpa using this

theorem conj_zpow_exponent {Γ : Type*} [Group Γ] {b z : Γ} (hb : b * b = 1) (hz : orderOf z = 15)
    (hbz : b * z * b⁻¹ ∈ Subgroup.zpowers z) :
    ∃ k : ℤ, (∀ j : ℤ, b * z ^ j * b⁻¹ = z ^ (k * j)) ∧
      (k % 15 = 1 ∨ k % 15 = 4 ∨ k % 15 = 11 ∨ k % 15 = 14) := by
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbz
  have hbpow : ∀ j : ℤ, b * z ^ j * b⁻¹ = z ^ (k * j) := by
    intro j
    rw [← conj_zpow, ← hk, ← zpow_mul]
  refine ⟨k, hbpow, ?_⟩
  have h1 : z ^ (k * k) = z := by
    calc z ^ (k * k) = b * z ^ k * b⁻¹ := (hbpow k).symm
      _ = b * (b * z * b⁻¹) * b⁻¹ := by rw [hk]
      _ = z := by
        calc b * (b * z * b⁻¹) * b⁻¹ = (b * b) * z * (b⁻¹ * b⁻¹) := by group
          _ = z := by rw [hb, hbinv, hb]; simp
  have h2 : z ^ (k * k - 1) = 1 := by
    rw [zpow_sub_one, h1, mul_inv_cancel]
  have h3 : (orderOf z : ℤ) ∣ k * k - 1 := orderOf_dvd_iff_zpow_eq_one.mpr h2
  rw [hz] at h3
  exact sq_eq_one_mod_fifteen (by exact_mod_cast h3)

theorem zpowers_fixes_one [Finite V] (hcard : Nat.card V = 16) {z : MulAut V}
    (hz : orderOf z = 15) :
    ∀ q ∈ Subgroup.zpowers z, ∀ v : V, v ≠ 1 → q v = v → q = 1 := by
  intro q hq v hv1 hqv
  by_contra hq1
  have hz15 : z ^ 15 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hw5 : (z ^ 3) ^ 5 = 1 := by rw [← pow_mul]; exact hz15
  have hw1 : z ^ 3 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hz] at this
    omega
  have hq15 : q ^ 15 = 1 := by
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz15, one_zpow]
  have hd15 : orderOf q ∣ 15 := orderOf_dvd_of_pow_eq_one hq15
  have hd1 : orderOf q ≠ 1 := fun h => hq1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
  have hp15 : p ∣ 15 := hpd.trans hd15
  have hd0 : orderOf q ≠ 0 := fun h => by rw [h] at hd15; omega
  have hordu : orderOf (q ^ (orderOf q / p)) = p := orderOf_pow_orderOf_div hd0 hpd
  set u := q ^ (orderOf q / p) with hu
  have huv : u v = v := by
    have := zpow_apply_eq_of_apply_eq hqv ((orderOf q / p : ℕ) : ℤ)
    rwa [zpow_natCast] at this
  have huz : u ∈ Subgroup.zpowers z := Subgroup.pow_mem _ hq _
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hordu
    exact hp.one_lt.ne hordu
  have hp35 : p = 3 ∨ p = 5 := by
    have h : p ∣ 3 * 5 := hp15
    rcases (Nat.Prime.dvd_mul hp).mp h with h3 | h5
    · left; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
    · right; exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h5
  have hvbot : ∀ hbot : fixV (Subgroup.zpowers u) = ⊥, False := by
    intro hbot
    have : v ∈ fixV (Subgroup.zpowers u) := mem_fixV_zpowers_iff.mpr huv
    rw [hbot, Subgroup.mem_bot] at this
    exact hv1 this
  rcases hp35 with rfl | rfl
  · have hu3 : u ^ 3 = 1 := by rw [← hordu]; exact pow_orderOf_eq_one u
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp huz
    have hcomm : (z ^ 3) * u = u * (z ^ 3) := by
      rw [← hi]
      exact ((Commute.refl z).pow_left 3).zpow_right i |>.eq
    exact hvbot (fixV_zpowers_eq_bot_of_commute hcard hw5 hw1 hu1 hcomm)
  · have hu5 : u ^ 5 = 1 := by rw [← hordu]; exact pow_orderOf_eq_one u
    exact hvbot (fixV_zpowers_eq_bot_of_pow_five hcard hu5 hu1)

theorem fixed_unique_of_inverts [Finite V] (hcard : Nat.card V = 16) {b z : MulAut V}
    (hz : orderOf z = 15) (hinv : ∀ j : ℤ, b * z ^ j * b⁻¹ = (z ^ j)⁻¹) {v v' : V}
    (hv1 : v ≠ 1) (hv'1 : v' ≠ 1) (hbv : b v = v) (hbv' : b v' = v') : v = v' := by
  have hfix := zpowers_fixes_one hcard hz
  have hsurj : ∀ w : V, w ≠ 1 → ∃ q ∈ Subgroup.zpowers z, q v = w := by
    let f : Subgroup.zpowers z → {w : V // w ≠ 1} := fun q => ⟨(q : MulAut V) v, fun h => by
      have : (q : MulAut V) v = 1 := h
      rw [← map_one (q : MulAut V)] at this
      exact hv1 ((q : MulAut V).injective this)⟩
    have hf : Function.Injective f := by
      intro q q' h
      have h1 : (q : MulAut V) v = (q' : MulAut V) v := congrArg Subtype.val h
      have h2 : ((q' : MulAut V)⁻¹ * q) v = v := by
        rw [MulAut.mul_apply, h1]
        simp
      have hmem : (q' : MulAut V)⁻¹ * q ∈ Subgroup.zpowers z :=
        Subgroup.mul_mem _ (Subgroup.inv_mem _ q'.2) q.2
      have := hfix _ hmem v hv1 h2
      apply Subtype.ext
      exact (inv_mul_eq_one.mp this).symm
    have hcardS : Nat.card {w : V // w ≠ 1} ≤ 15 := by
      have : Fintype V := Fintype.ofFinite V
      classical
      have h1 : Fintype.card {w : V // w ≠ 1} < Fintype.card V :=
        Fintype.card_subtype_lt (p := fun w => w ≠ 1) (x := 1) (by simp)
      have h2 : Nat.card V = Fintype.card V := Nat.card_eq_fintype_card
      have h3 : Nat.card {w : V // w ≠ 1} = Fintype.card {w : V // w ≠ 1} :=
        Nat.card_eq_fintype_card
      omega
    have hQ : Nat.card (Subgroup.zpowers z) = 15 := by rw [Nat.card_zpowers, hz]
    have hbij : Function.Bijective f := hf.bijective_of_nat_card_le (by rw [hQ]; exact hcardS)
    intro w hw
    obtain ⟨q, hq⟩ := hbij.2 ⟨w, hw⟩
    exact ⟨q, q.2, congrArg Subtype.val hq⟩
  obtain ⟨q, hqQ, hqv⟩ := hsurj v' hv'1
  have hbq : b * q * b⁻¹ = q⁻¹ := by
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hqQ
    exact hinv j
  have h1 : b (q v) = q⁻¹ v := by
    calc b (q v) = (b * q * b⁻¹) (b v) := by simp [MulAut.mul_apply]
      _ = (b * q * b⁻¹) v := by rw [hbv]
      _ = q⁻¹ v := by rw [hbq]
  have hh : q⁻¹ v = q v := by
    rw [← h1, hqv, hbv']
  have h2 : (q * q) v = v := by
    rw [MulAut.mul_apply, ← hh]
    simp
  have hqq : q * q = 1 :=
    hfix (q * q) (Subgroup.mul_mem _ hqQ hqQ) v hv1 h2
  have hord2 : orderOf q ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hqq)
  have hord15 : orderOf q ∣ 15 := by
    have := orderOf_dvd_of_mem_zpowers hqQ
    rwa [hz] at this
  have hq1 : q = 1 := by
    have h := Nat.dvd_gcd hord2 hord15
    have : orderOf q ∣ 1 := by simpa using h
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)
  rw [← hqv, hq1]
  simp

theorem exists_two_ne_one {W : Subgroup V} [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1)
    (hW : Nat.card W = 4) : ∃ v ∈ W, ∃ v' ∈ W, v ≠ 1 ∧ v' ≠ 1 ∧ v ≠ v' := by
  have hne : W ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hW
    omega
  obtain ⟨⟨v, hv⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hordv : orderOf v = 2 := orderOf_eq_prime (by simpa [sq] using hV2 v) hv1'
  have hK : Nat.card (Subgroup.zpowers v) = 2 := by rw [Nat.card_zpowers, hordv]
  have hKW : Subgroup.zpowers v ≤ W := (Subgroup.zpowers_le).mpr hv
  have hne' : Subgroup.zpowers v ≠ W := by
    intro h
    rw [h] at hK
    omega
  obtain ⟨v', hv'W, hv'K⟩ : ∃ v' ∈ W, v' ∉ Subgroup.zpowers v := by
    by_contra hcon
    push Not at hcon
    exact hne' (le_antisymm hKW hcon)
  refine ⟨v, hv, v', hv'W, hv1', ?_, ?_⟩
  · intro h
    apply hv'K
    rw [h]; exact Subgroup.one_mem _
  · intro h
    apply hv'K
    rw [← h]; exact Subgroup.mem_zpowers v

theorem no_order_fifteen [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 16)
    {b z : MulAut V} (hb : b * b = 1) (hfixb : Nat.card (fixV (Subgroup.zpowers b)) = 4)
    (hz : orderOf z = 15) (hbz : b * z * b⁻¹ ∈ Subgroup.zpowers z)
    (hstar : ∀ y ∈ Subgroup.zpowers z, y ^ 3 = 1 → b * y = y * b → y = 1) : False := by
  obtain ⟨k, hbpow, hk⟩ := conj_zpow_exponent hb hz hbz
  have hz15 : z ^ 15 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hzmod : ∀ m n : ℤ, m ≡ n [ZMOD 15] → z ^ m = z ^ n := by
    intro m n h
    rw [zpow_eq_zpow_iff_modEq, hz]
    exact_mod_cast h
  rcases hk with hk | hk | hk | hk
  · have hy3 : (z ^ (5 : ℤ)) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul]
      have : z ^ ((5 : ℤ) * (3 : ℕ)) = z ^ (15 : ℕ) := by norm_num
      rw [this, hz15]
    have hcomm : b * z ^ (5 : ℤ) = z ^ (5 : ℤ) * b := by
      have h1 := hbpow 5
      have h2 : z ^ (k * 5) = z ^ (5 : ℤ) := hzmod _ _ (by unfold Int.ModEq; omega)
      rw [h2] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1)
    have := hstar _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) _) hy3 hcomm
    have hd := orderOf_dvd_of_pow_eq_one (by simpa using this : z ^ 5 = 1)
    rw [hz] at hd
    omega
  · have hy3 : (z ^ (5 : ℤ)) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul]
      have : z ^ ((5 : ℤ) * (3 : ℕ)) = z ^ (15 : ℕ) := by norm_num
      rw [this, hz15]
    have hcomm : b * z ^ (5 : ℤ) = z ^ (5 : ℤ) * b := by
      have h1 := hbpow 5
      have h2 : z ^ (k * 5) = z ^ (5 : ℤ) := hzmod _ _ (by unfold Int.ModEq; omega)
      rw [h2] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1)
    have := hstar _ (Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) _) hy3 hcomm
    have hd := orderOf_dvd_of_pow_eq_one (by simpa using this : z ^ 5 = 1)
    rw [hz] at hd
    omega
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hw5 : (z ^ (3 : ℤ)) ^ 5 = 1 := by
      rw [← zpow_natCast, ← zpow_mul]
      have : z ^ ((3 : ℤ) * (5 : ℕ)) = z ^ (15 : ℕ) := by norm_num
      rw [this, hz15]
    have hw1 : z ^ (3 : ℤ) ≠ 1 := by
      intro h
      have hd := orderOf_dvd_of_pow_eq_one (by simpa using h : z ^ 3 = 1)
      rw [hz] at hd
      omega
    have hcomm : b * z ^ (3 : ℤ) = z ^ (3 : ℤ) * b := by
      have h1 := hbpow 3
      have h2 : z ^ (k * 3) = z ^ (3 : ℤ) := hzmod _ _ (by unfold Int.ModEq; omega)
      rw [h2] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1)
    have hP := isPGroup_zpowers_of_pow_prime (p := 5) hw5
    have hfw := fixV_zpowers_eq_bot_of_pow_five hcard hw5 hw1
    have hW : ∀ g ∈ Subgroup.zpowers (z ^ (3 : ℤ)), ∀ v ∈ fixV (Subgroup.zpowers b),
        g v ∈ fixV (Subgroup.zpowers b) := by
      intro g hg v hv
      rw [mem_fixV_zpowers_iff] at hv ⊢
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      have hck : b * (z ^ (3 : ℤ)) ^ m = (z ^ (3 : ℤ)) ^ m * b :=
        (Commute.zpow_right (show Commute b (z ^ (3 : ℤ)) from hcomm) m)
      have := congrArg (fun φ : MulAut V => φ v) hck
      simp only [MulAut.mul_apply] at this
      rw [this, hv]
    have h := card_modEq_card_inf_fixV hP hW
    rw [hfw, inf_bot_eq, Subgroup.card_bot, hfixb] at h
    exact absurd h (by decide)
  · have hinv : ∀ j : ℤ, b * z ^ j * b⁻¹ = (z ^ j)⁻¹ := by
      intro j
      rw [hbpow j, ← zpow_neg]
      apply hzmod
      have : k ≡ 14 [ZMOD 15] := by unfold Int.ModEq; omega
      have h2 := this.mul_right j
      refine h2.trans ?_
      unfold Int.ModEq
      omega
    obtain ⟨v, hv, v', hv', hv1, hv'1, hne⟩ := exists_two_ne_one hV2 hfixb
    have hbv : b v = v := mem_fixV_zpowers_iff.mp hv
    have hbv' : b v' = v' := mem_fixV_zpowers_iff.mp hv'
    exact hne (fixed_unique_of_inverts hcard hz hinv hv1 hv'1 hbv hbv')

end S152N2

end CFSG.Quasithin
