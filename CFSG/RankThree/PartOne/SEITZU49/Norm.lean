module

public import CFSG.ClassicalGroups.Unitary.Finite

public section

namespace CFSG.RankThree.PartOne.SEITZU49.Norm

open CFSG.LieType.BorelTits CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

theorem exists_generator (hK : Nat.card K = (2 ^ f) ^ 2) :
    ∃ γ : K, unitaryInvolution K 2 f γ * γ = 1 ∧ orderOf γ = 2 ^ f + 1 ∧
      ∀ w : K, unitaryInvolution K 2 f w * w = 1 → ∃ i : ℕ, w = γ ^ i := by
  have hq := one_lt_pow_of_card hK
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = (2 ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, card_units_of_card hK]
  have hgK : orderOf (g : K) = (2 ^ f) ^ 2 - 1 := by rw [orderOf_units, hord]
  set q := 2 ^ f with hqdef
  have hq1 : q - 1 ≠ 0 := by omega
  have hγord : orderOf ((g : K) ^ (q - 1)) = q + 1 := by
    rw [orderOf_pow' _ hq1, hgK, sq_sub_one_eq q hq.le]
    have : Nat.gcd ((q + 1) * (q - 1)) (q - 1) = q - 1 := Nat.gcd_eq_right (dvd_mul_left _ _)
    rw [this]
    exact Nat.mul_div_cancel _ (by omega)
  refine ⟨(g : K) ^ (q - 1), ?_, hγord, ?_⟩
  · rw [unitaryInvolution_apply, ← pow_succ]
    have := pow_orderOf_eq_one ((g : K) ^ (q - 1))
    rwa [hγord] at this
  · intro w hw
    have hw0 : w ≠ 0 := by
      rintro rfl
      simp at hw
    set W : Kˣ := Units.mk0 w hw0 with hW
    obtain ⟨k, hk⟩ : ∃ k : ℕ, g ^ k = W := mem_powers_iff_mem_zpowers.mpr (hg W)
    have hWq : W ^ (q + 1) = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hW, Units.val_mk0, Units.val_one]
      rw [unitaryInvolution_apply, ← pow_succ] at hw
      exact hw
    have hdvd : (q ^ 2 - 1) ∣ k * (q + 1) := by
      rw [← hord]
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul, hk, hWq]
    rw [sq_sub_one_eq _ hq.le, mul_comm (q + 1) (q - 1)] at hdvd
    obtain ⟨i, rfl⟩ : q - 1 ∣ k := Nat.dvd_of_mul_dvd_mul_right (by omega : 0 < q + 1) hdvd
    refine ⟨i, ?_⟩
    have := congrArg (fun x : Kˣ => (x : K)) hk
    simp only [Units.val_pow_eq_pow_val, hW, Units.val_mk0] at this
    rw [← this, ← pow_mul]

variable {γ : K}

theorem fifth_power_iff (hγ : unitaryInvolution K 2 f γ * γ = 1) (hord : orderOf γ = 2 ^ f + 1)
    (hgen : ∀ w : K, unitaryInvolution K 2 f w * w = 1 → ∃ i : ℕ, w = γ ^ i)
    (h5 : 5 ∣ 2 ^ f + 1) (i : ℕ) :
    (∃ u : K, unitaryInvolution K 2 f u * u = 1 ∧ u ^ 5 = γ ^ i) ↔ 5 ∣ i := by
  constructor
  · rintro ⟨u, hu, hu5⟩
    obtain ⟨a, rfl⟩ := hgen u hu
    rw [← pow_mul] at hu5
    have hγ0 : γ ≠ 0 := by
      rintro rfl
      simp at hγ
    set Γ : Kˣ := Units.mk0 γ hγ0 with hΓ
    have hΓord : orderOf Γ = 2 ^ f + 1 := by
      rw [← hord, ← orderOf_units]
      rfl
    have hΓ5 : Γ ^ (a * 5) = Γ ^ i := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hΓ, Units.val_mk0]
      exact hu5
    have hmod := (pow_eq_pow_iff_modEq (x := Γ) (n := a * 5) (m := i)).mp hΓ5
    rw [hΓord] at hmod
    have h5' : i ≡ a * 5 [MOD 5] := (Nat.ModEq.of_dvd h5 hmod).symm
    have : i % 5 = 0 := by
      have := h5'
      unfold Nat.ModEq at this
      omega
    omega
  · rintro ⟨j, rfl⟩
    refine ⟨γ ^ j, ?_, by rw [← pow_mul, mul_comm]⟩
    rw [map_pow, ← mul_pow, hγ, one_pow]

theorem exists_mod_five (i j : ℕ) (hj : ¬ 5 ∣ j) : ∃ k : ℕ, 5 ∣ i + j * k := by
  have key : ∀ a b : Fin 5, b ≠ 0 → ∃ k : Fin 5, (a.val + b.val * k.val) % 5 = 0 := by decide
  have hb : (⟨j % 5, Nat.mod_lt _ (by norm_num)⟩ : Fin 5) ≠ 0 := by
    intro h
    apply hj
    have := congrArg Fin.val h
    simp at this
    omega
  obtain ⟨k, hk⟩ := key ⟨i % 5, Nat.mod_lt _ (by norm_num)⟩ _ hb
  refine ⟨k.val, ?_⟩
  have h1 : i + j * k.val ≡ i % 5 + j % 5 * k.val [MOD 5] :=
    Nat.ModEq.add (Nat.mod_modEq i 5).symm (Nat.ModEq.mul_right _ (Nat.mod_modEq j 5).symm)
  have h2 : i % 5 + j % 5 * k.val ≡ 0 [MOD 5] := hk
  exact (Nat.modEq_zero_iff_dvd).mp (h1.trans h2)

theorem exists_good_mul (hγ : unitaryInvolution K 2 f γ * γ = 1) (hord : orderOf γ = 2 ^ f + 1)
    (hgen : ∀ w : K, unitaryInvolution K 2 f w * w = 1 → ∃ i : ℕ, w = γ ^ i)
    (h5 : 5 ∣ 2 ^ f + 1) {a b : K} (ha : unitaryInvolution K 2 f a * a = 1)
    (hb : unitaryInvolution K 2 f b * b = 1)
    (hna : ¬ ∃ u : K, unitaryInvolution K 2 f u * u = 1 ∧ u ^ 5 = a)
    (hnb : ¬ ∃ u : K, unitaryInvolution K 2 f u * u = 1 ∧ u ^ 5 = b) :
    ∃ k : ℕ, ∃ u : K, unitaryInvolution K 2 f u * u = 1 ∧ u ^ 5 = a * b ^ k := by
  obtain ⟨i, rfl⟩ := hgen a ha
  obtain ⟨j, rfl⟩ := hgen b hb
  have hi : ¬ 5 ∣ i := fun h => hna ((fifth_power_iff hγ hord hgen h5 i).mpr h)
  have hj : ¬ 5 ∣ j := fun h => hnb ((fifth_power_iff hγ hord hgen h5 j).mpr h)
  obtain ⟨k, hk⟩ := exists_mod_five i j hj
  refine ⟨k, ?_⟩
  rw [← pow_mul, ← pow_add]
  exact (fifth_power_iff hγ hord hgen h5 _).mpr hk

theorem exists_decomp (hγ : unitaryInvolution K 2 f γ * γ = 1) (hord : orderOf γ = 2 ^ f + 1)
    (hgen : ∀ w : K, unitaryInvolution K 2 f w * w = 1 → ∃ i : ℕ, w = γ ^ i)
    (h5 : 5 ∣ 2 ^ f + 1) {z : K} (hz : unitaryInvolution K 2 f z * z = 1)
    (hnz : ¬ ∃ u : K, unitaryInvolution K 2 f u * u = 1 ∧ u ^ 5 = z) {d : K}
    (hd : unitaryInvolution K 2 f d * d = 1) :
    ∃ k : ℕ, ∃ u : K, unitaryInvolution K 2 f u * u = 1 ∧ d = z ^ k * u ^ 5 := by
  obtain ⟨i, rfl⟩ := hgen z hz
  obtain ⟨e, rfl⟩ := hgen d hd
  have hi : ¬ 5 ∣ i := fun h => hnz ((fifth_power_iff hγ hord hgen h5 i).mpr h)
  obtain ⟨k, j, hj⟩ := exists_mod_five e i hi
  refine ⟨2 ^ f * k, γ ^ j, ?_, ?_⟩
  · rw [map_pow, ← mul_pow, hγ, one_pow]
  · have h1 : γ ^ (2 ^ f + 1) = 1 := by
      have := pow_orderOf_eq_one γ
      rwa [hord] at this
    calc γ ^ e = γ ^ e * (γ ^ (2 ^ f + 1)) ^ (i * k) := by rw [h1, one_pow, mul_one]
      _ = (γ ^ i) ^ (2 ^ f * k) * (γ ^ j) ^ 5 := by
        rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
        congr 1
        have : 5 * j = e + i * k := hj.symm
        nlinarith

end CFSG.RankThree.PartOne.SEITZU49.Norm
