module

public import CFSG.Quasithin.H13.KGFactSzEnd
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiLayerKernel

public section

namespace CFSG.Quasithin.H13.KGSz

open CFSG.Blueprint CFSG.LieType.Ree CFSG.Quasithin

variable {a : ℕ} {K : Type} [Field K] [Finite K]

@[expose] def fstU (g : suzukiGroup a K) : K :=
  ((g : Matrix.GeneralLinearGroup (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 0

omit [Finite K] in
theorem fstU_suzukiSElt (u v : K) :
    fstU (suzukiSElt a K u v) = u := by
  simp [fstU, coe_suzukiSElt, suzukiS]

theorem exists_eq_suzukiSElt (hK : Nat.card K = 2 ^ (2 * a + 1))
    {x : suzukiGroup a K} (hx : x ∈ suzukiU a K) : ∃ v, x = suzukiSElt a K (fstU x) v := by
  obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hx
  exact ⟨v, by rw [fstU_suzukiSElt]⟩

theorem fstU_mul (hK : Nat.card K = 2 ^ (2 * a + 1))
    {x y : suzukiGroup a K} (hx : x ∈ suzukiU a K) (hy : y ∈ suzukiU a K) :
    fstU (x * y) = fstU x + fstU y := by
  obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hx
  obtain ⟨c, d, rfl⟩ := (mem_suzukiU_iff hK).1 hy
  rw [suzukiSElt_mul hK, fstU_suzukiSElt, fstU_suzukiSElt, fstU_suzukiSElt]

theorem suzukiSElt_sq (hK : Nat.card K = 2 ^ (2 * a + 1))
    (u v : K) : suzukiSElt a K u v * suzukiSElt a K u v =
      suzukiSElt a K 0 (u ^ (2 ^ (a + 1) + 1)) := by
  have : CharP K 2 := (suzuki_frobenius_exponents a K hK).1
  rw [suzukiSElt_mul hK, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, zero_add, ← pow_succ]

omit [Finite K] in
theorem eq_one_of_pow_three_pow (hK : Nat.card K = 2 ^ (2 * a + 1)) {μ : K} {e : ℕ}
    (h : μ ^ 3 ^ e = 1) : μ = 1 := by
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero _ (by norm_num))] at h
    exact zero_ne_one h
  have hν : (Units.mk0 μ hμ0) ^ 3 ^ e = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, h, Units.val_one])
  have hcard : Nat.card Kˣ = 2 ^ (2 * a + 1) - 1 := by rw [Nat.card_units, hK]
  have h1 := orderOf_dvd_of_pow_eq_one hν
  have h2 : orderOf (Units.mk0 μ hμ0) ∣ 2 ^ (2 * a + 1) - 1 := hcard ▸ orderOf_dvd_natCard _
  have h3 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 (coprime_three_pow a e)) h2
  exact congrArg Units.val (orderOf_eq_one_iff.mp h3)

theorem eq_one_of_fix_torus (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {l₀ : Kˣ} (hl₀ : ∀ c : Kˣ, ∃ n : ℕ, l₀ ^ n = c)
    {β : MulAut (suzukiGroup a K)} {e : ℕ} (he : β ^ 3 ^ e = 1)
    (hβU : ∀ x ∈ suzukiU a K, β x ∈ suzukiU a K)
    (hβt : β (suzukiDElt a K l₀) = suzukiDElt a K l₀) : β = 1 := by
  have : CharP K 2 := (suzuki_frobenius_exponents a K hK).1
  set t₀ := suzukiDElt a K l₀ with ht₀
  have hS : ∀ u v, suzukiSElt a K u v ∈ suzukiU a K := suzukiSElt_mem_suzukiU a K
  have hβc : ∀ x, β (t₀⁻¹ * x * t₀) = t₀⁻¹ * β x * t₀ := fun x => by
    rw [map_mul, map_mul, map_inv, hβt]
  set φ : K → K := fun u => fstU (β (suzukiSElt a K u 0)) with hφ
  have hfst : ∀ u v, fstU (β (suzukiSElt a K u v)) = φ u := by
    intro u v
    have h1 : suzukiSElt a K u v = suzukiSElt a K u 0 * suzukiSElt a K 0 v := by
      rw [suzukiSElt_mul hK, add_zero, zero_add, mul_zero, add_zero]
    have hz : fstU (β (suzukiSElt a K 0 v)) = 0 := by
      obtain ⟨w, hw⟩ := exists_eq_suzukiSElt hK (hβU _ (hS 0 v))
      have h2 : β (suzukiSElt a K 0 v) * β (suzukiSElt a K 0 v) = 1 := by
        rw [← map_mul, suzukiSElt_sq hK, zero_pow (Nat.succ_ne_zero _), suzukiSElt_zero_zero hK,
          map_one]
      rw [hw, suzukiSElt_sq hK, ← suzukiSElt_zero_zero hK (a := a), suzukiSElt_inj] at h2
      exact pow_eq_zero_iff (Nat.succ_ne_zero _) |>.mp h2.2
    rw [h1, map_mul, fstU_mul hK (hβU _ (hS _ _)) (hβU _ (hS _ _)), hz, add_zero]
  have hφadd : ∀ u c, φ (u + c) = φ u + φ c := by
    intro u c
    have h1 := congrArg (fun x => fstU (β x)) (suzukiSElt_mul hK u 0 c 0)
    rw [map_mul, fstU_mul hK (hβU _ (hS _ _)) (hβU _ (hS _ _)), hfst u 0, hfst c 0, hfst] at h1
    exact h1.symm
  have hφ0 : φ 0 = 0 := by
    have := hφadd 0 0
    rw [add_zero] at this
    exact left_eq_add.mp this
  have hφl : ∀ u, φ ((l₀ : K) * u) = (l₀ : K) * φ u := by
    intro u
    obtain ⟨w, hw⟩ := exists_eq_suzukiSElt hK (hβU _ (hS u 0))
    have h1 : suzukiSElt a K ((l₀ : K) * u) 0 = t₀⁻¹ * suzukiSElt a K u 0 * t₀ := by
      rw [ht₀, suzukiDElt_conj hK, mul_zero]
    rw [← hfst _ 0, h1, hβc, hw, ht₀, suzukiDElt_conj hK, fstU_suzukiSElt]
  have hφpow : ∀ n : ℕ, ∀ u, φ ((l₀ : K) ^ n * u) = (l₀ : K) ^ n * φ u := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ n ih => intro u; rw [pow_succ', mul_assoc, hφl, ih, mul_assoc]
  have hφmul : ∀ c u : K, φ (c * u) = c * φ u := by
    intro c u
    by_cases hc : c = 0
    · rw [hc, zero_mul, zero_mul, hφ0]
    · obtain ⟨n, hn⟩ := hl₀ (Units.mk0 c hc)
      have hc' : c = (l₀ : K) ^ n := by rw [← Units.val_pow_eq_pow_val, hn, Units.val_mk0]
      rw [hc', hφpow]
  set μ := φ 1 with hμ
  have hφμ : ∀ u, φ u = μ * u := fun u => by
    rw [show φ u = φ (u * 1) by rw [mul_one], hφmul, mul_comm]
  have hiter : ∀ k : ℕ, ∀ u : K, ∃ w,
      (β ^ k) (suzukiSElt a K u 0) = suzukiSElt a K (μ ^ k * u) w := by
    intro k
    induction k with
    | zero => intro u; exact ⟨0, by simp⟩
    | succ k ih =>
      intro u
      obtain ⟨w, hw⟩ := ih u
      obtain ⟨w', hw'⟩ := exists_eq_suzukiSElt hK (hβU _ (hS (μ ^ k * u) w))
      refine ⟨w', ?_⟩
      rw [pow_succ', MulAut.mul_apply, hw, hw', hfst, hφμ, pow_succ', mul_assoc]
  have hμ1 : μ = 1 := by
    obtain ⟨w, hw⟩ := hiter (3 ^ e) 1
    rw [he, MulAut.one_apply] at hw
    have h1 := (suzukiSElt_inj.mp hw).1
    rw [mul_one] at h1
    exact eq_one_of_pow_three_pow hK h1.symm
  have hfix1 : ∀ u v, ∃ w, β (suzukiSElt a K u v) = suzukiSElt a K u w := by
    intro u v
    obtain ⟨w, hw⟩ := exists_eq_suzukiSElt hK (hβU _ (hS u v))
    exact ⟨w, by rw [hw, hfst, hφμ, hμ1, one_mul]⟩
  have hUZ : ∀ x ∈ suzukiU a K, x⁻¹ * β x ∈ suzukiZ0 a K := by
    intro x hx
    obtain ⟨u, v, rfl⟩ := (mem_suzukiU_iff hK).1 hx
    obtain ⟨w, hw⟩ := hfix1 u v
    rw [hw, suzukiSElt_inv hK, suzukiSElt_mul hK, CharTwo.add_self_eq_zero, mem_suzukiZ0_iff hK]
    exact ⟨_, rfl⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hbij, -, -⟩ := suzuki_frobenius_exponents a K hK
  have hZ : ∀ z ∈ suzukiZ0 a K, β z = z := by
    intro z hz
    obtain ⟨v, rfl⟩ := (mem_suzukiZ0_iff hK).1 hz
    by_cases hv : v = 0
    · rw [hv, suzukiSElt_zero_zero hK, map_one]
    · obtain ⟨s, hs⟩ := hbij.2 (Units.mk0 v hv)
      have hv' : v = (s : K) ^ (2 ^ (a + 1) + 1) := by
        have h1 : s ^ ((2 ^ (a + 1) + 1 : ℕ) : ℤ) = Units.mk0 v hv := by
          rw [show ((2 ^ (a + 1) + 1 : ℕ) : ℤ) = (2 ^ (a + 1) + 1 : ℤ) by push_cast; ring]
          exact hs
        rw [zpow_natCast] at h1
        have h2 := congrArg Units.val h1
        rw [Units.val_pow_eq_pow_val, Units.val_mk0] at h2
        exact h2.symm
      obtain ⟨w, hw⟩ := hfix1 s 0
      rw [hv', ← suzukiSElt_sq hK (s : K) 0, map_mul, hw, suzukiSElt_sq hK, suzukiSElt_sq hK]
  have hmap : (suzukiU a K).map β.toMonoidHom = suzukiU a K := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact hβU x hx
    · rw [Subgroup.card_map_of_injective β.injective]
  obtain ⟨b, hbU, hb⟩ := CFSG.ShultStronglyClosedTI.suzukiU_layer_kernel ha hK β hmap hZ hUZ
  have h1 : orderOf (MulAut.conj b) ∣ 3 ^ e := orderOf_dvd_of_pow_eq_one (hb ▸ he)
  have h2 : orderOf (MulAut.conj b) ∣ (2 ^ (2 * a + 1)) ^ 2 :=
    (orderOf_map_dvd MulAut.conj b).trans ((Subgroup.orderOf_dvd_natCard _ hbU).trans
      (by rw [(suzuki_unipotent_structure hK).2.1]))
  have h3 : Nat.Coprime (3 ^ e) ((2 ^ (2 * a + 1)) ^ 2) :=
    Nat.Coprime.pow_left e (Nat.Coprime.pow_right 2 (Nat.Coprime.pow_right _ (by norm_num)))
  rw [hb]
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 h3) h2)

theorem eq_one_of_commute_torus (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    {l₀ : Kˣ} (hl₀ : ∀ c : Kˣ, ∃ n : ℕ, l₀ ^ n = c) {z : suzukiGroup a K}
    (hz : z ∈ suzukiU a K) (hzt : z * suzukiDElt a K l₀ = suzukiDElt a K l₀ * z) : z = 1 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hbij, -, -⟩ := suzuki_frobenius_exponents a K hK
  have hl1 : l₀ ≠ 1 := by
    intro h1
    have hcard : 1 < Nat.card Kˣ := by
      rw [Nat.card_units, hK]
      have h8 : 2 ^ 3 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      generalize 2 ^ (2 * a + 1) = n at h8 ⊢
      norm_num at h8
      omega
    have := Finite.one_lt_card_iff_nontrivial.mp hcard
    obtain ⟨c, hc⟩ := exists_ne (1 : Kˣ)
    obtain ⟨n, hn⟩ := hl₀ c
    rw [h1, one_pow] at hn
    exact hc hn.symm
  have hlθ : (l₀ : K) ^ (2 ^ (a + 1) + 1) ≠ 1 := by
    intro h
    apply hl1
    apply hbij.1
    simp only
    rw [one_zpow, show ((2 ^ (a + 1) + 1 : ℤ)) = ((2 ^ (a + 1) + 1 : ℕ) : ℤ) by push_cast; ring,
      zpow_natCast]
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, h, Units.val_one])
  obtain ⟨p, q, rfl⟩ := (mem_suzukiU_iff hK).1 hz
  have h1 : (suzukiDElt a K l₀)⁻¹ * suzukiSElt a K p q * suzukiDElt a K l₀ =
      suzukiSElt a K p q := by
    rw [mul_assoc, hzt, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [suzukiDElt_conj hK, suzukiSElt_inj] at h1
  have hp : p = 0 := by
    have h2 : ((l₀ : K) - 1) * p = 0 := by rw [sub_mul, h1.1, one_mul, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (Units.ext (sub_eq_zero.mp h)) hl1
    · exact h
  have hq : q = 0 := by
    have h2 : ((l₀ : K) ^ (2 ^ (a + 1) + 1) - 1) * q = 0 := by
      rw [sub_mul, h1.2, one_mul, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (sub_eq_zero.mp h) hlθ
    · exact h
  rw [hp, hq, suzukiSElt_zero_zero hK]

theorem eq_one_of_borel (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {β : MulAut (suzukiGroup a K)} {e : ℕ}
    (he : β ^ 3 ^ e = 1) (hβU : ∀ x ∈ suzukiU a K, β x ∈ suzukiU a K)
    (hβT : ∀ t ∈ suzukiT a K, β t * t⁻¹ ∈ suzukiU a K) : β = 1 := by
  classical
  obtain ⟨l₀, hl₀⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hl₀' : ∀ c : Kˣ, ∃ n : ℕ, l₀ ^ n = c := fun c =>
    (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr (hl₀ c))
  set t₀ := suzukiDElt a K l₀ with ht₀
  have ht₀T : t₀ ∈ suzukiT a K := suzukiDElt_mem_suzukiT a K l₀
  have ht₀N := suzukiT_le_normalizer hK ht₀T
  have hβM : ∀ x, x * t₀⁻¹ ∈ suzukiU a K → β x * t₀⁻¹ ∈ suzukiU a K := by
    intro x hx
    have h1 := hβT t₀ ht₀T
    have h2 := hβU _ hx
    have : β x * t₀⁻¹ = β (x * t₀⁻¹) * (β t₀ * t₀⁻¹) := by rw [map_mul, map_inv]; group
    rw [this]
    exact (suzukiU a K).mul_mem h2 h1
  have hβnM : ∀ n : ℕ, ∀ x, x * t₀⁻¹ ∈ suzukiU a K → (β ^ n) x * t₀⁻¹ ∈ suzukiU a K := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih => intro x hx; rw [pow_succ', MulAut.mul_apply]; exact hβM _ (ih x hx)
  have hfin : IsOfFinOrder β := isOfFinOrder_iff_pow_eq_one.mpr ⟨3 ^ e, by positivity, he⟩
  have hpM : ∀ p ∈ Subgroup.zpowers β, ∀ x, x * t₀⁻¹ ∈ suzukiU a K →
      p x * t₀⁻¹ ∈ suzukiU a K := by
    intro p hp x hx
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (hfin.mem_powers_iff_mem_zpowers.mpr hp)
    exact hβnM n x hx
  let M := {x : suzukiGroup a K // x * t₀⁻¹ ∈ suzukiU a K}
  let _ : MulAction (Subgroup.zpowers β) M :=
    { smul := fun p x => ⟨(p : MulAut (suzukiGroup a K)) x.1, hpM p p.2 x.1 x.2⟩
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl }
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 (Subgroup.zpowers β) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one he)
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  have hcong := hP.card_modEq_card_fixedPoints M
  have hMU : M ≃ ↥(suzukiU a K) :=
    { toFun := fun x => ⟨x.1 * t₀⁻¹, x.2⟩
      invFun := fun u => ⟨u.1 * t₀, by simp⟩
      left_inv := fun x => Subtype.ext (by simp)
      right_inv := fun u => Subtype.ext (by simp) }
  have hcardM : Nat.card M = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [Nat.card_congr hMU, (suzuki_unipotent_structure hK).2.1]
  have hmod : (2 ^ (2 * a + 1)) ^ 2 % 3 = 1 := by
    rw [← pow_mul, show (2 : ℕ) ^ ((2 * a + 1) * 2) = 4 ^ (2 * a + 1) by
      rw [mul_comm, pow_mul]; norm_num, Nat.pow_mod]
    norm_num
  have hfixne : (MulAction.fixedPoints (Subgroup.zpowers β) M).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h, hcardM] at hcong
    have h0 : Nat.card (∅ : Set M) = 0 := by simp
    rw [h0, Nat.ModEq, hmod] at hcong
    exact absurd hcong (by norm_num)
  obtain ⟨x, hx⟩ := hfixne
  have hβx : β x.1 = x.1 := congrArg Subtype.val (hx ⟨β, Subgroup.mem_zpowers β⟩)
  let F : ↥(suzukiU a K) → M := fun u => ⟨u.1 * t₀ * u.1⁻¹, by
    have h1 := (Subgroup.mem_normalizer_iff.mp ht₀N (u.1⁻¹)).mp ((suzukiU a K).inv_mem u.2)
    have : u.1 * t₀ * u.1⁻¹ * t₀⁻¹ = u.1 * (t₀ * u.1⁻¹ * t₀⁻¹) := by group
    rw [this]
    exact (suzukiU a K).mul_mem u.2 h1⟩
  have hFinj : Function.Injective F := by
    intro u u' h
    have h1 : u.1 * t₀ * u.1⁻¹ = u'.1 * t₀ * u'.1⁻¹ := congrArg Subtype.val h
    have hz : u'.1⁻¹ * u.1 ∈ suzukiU a K := (suzukiU a K).mul_mem ((suzukiU a K).inv_mem u'.2) u.2
    have h2 := eq_one_of_commute_torus ha hK hl₀' hz (by
      calc u'.1⁻¹ * u.1 * t₀ = u'.1⁻¹ * (u.1 * t₀ * u.1⁻¹) * u.1 := by group
        _ = u'.1⁻¹ * (u'.1 * t₀ * u'.1⁻¹) * u.1 := by rw [h1]
        _ = t₀ * (u'.1⁻¹ * u.1) := by group)
    exact Subtype.ext (inv_mul_eq_one.mp h2).symm
  obtain ⟨u, hu⟩ := (hFinj.bijective_of_nat_card_le (by
    rw [hcardM, (suzuki_unipotent_structure hK).2.1])).2 x
  have hxu : x.1 = u.1 * t₀ * u.1⁻¹ := (congrArg Subtype.val hu).symm
  set γ := (MulAut.conj u.1)⁻¹ * β * MulAut.conj u.1 with hγ
  have hγapp : ∀ y, γ y = u.1⁻¹ * β (u.1 * y * u.1⁻¹) * u.1 := by
    intro y
    rw [hγ, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, ← map_inv, MulAut.conj_apply,
      inv_inv]
  have hγ1 : γ = 1 := by
    refine eq_one_of_fix_torus ha hK hl₀' (e := e) ?_ ?_ ?_
    · have h := conj_pow (a := (MulAut.conj u.1)⁻¹) (b := β) (i := 3 ^ e)
      rw [inv_inv] at h
      rw [hγ, h, he, mul_one, inv_mul_cancel]
    · intro y hy
      rw [hγapp]
      have h1 := hβU _ ((suzukiU a K).mul_mem ((suzukiU a K).mul_mem u.2 hy)
        ((suzukiU a K).inv_mem u.2))
      exact (suzukiU a K).mul_mem ((suzukiU a K).mul_mem ((suzukiU a K).inv_mem u.2) h1) u.2
    · rw [hγapp, ← ht₀, ← hxu, hβx, hxu]
      group
  have : β = MulAut.conj u.1 * γ * (MulAut.conj u.1)⁻¹ := by rw [hγ]; group
  rw [this, hγ1, mul_one, mul_inv_cancel]

theorem szCent_holds : A6.SzCent := by
  intro X _ _ n hX α hα S hαS hαN
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := hX
  obtain ⟨k, hk⟩ := hα
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set UX : Subgroup X := (suzukiU a K).comap e.toMonoidHom with hUX
  have hmemUX : ∀ y, y ∈ UX ↔ e y ∈ suzukiU a K := fun y => Iff.rfl
  have hUXcard : Nat.card UX = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [Nat.card_congr (e.toEquiv.subtypeEquiv hmemUX), (suzuki_unipotent_structure hK).2.1]
  have hXcard : Nat.card X = (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) *
      ((2 ^ (2 * a + 1)) ^ 2 + 1) := by
    rw [Nat.card_congr e.toEquiv, suzuki_order hK]
  have hUXp : IsPGroup 2 UX := IsPGroup.of_card (n := (2 * a + 1) * 2) (by rw [hUXcard, pow_mul])
  have hUXidx : ¬ 2 ∣ UX.index := by
    have h1 := Subgroup.card_mul_index UX
    rw [hUXcard, hXcard, mul_assoc] at h1
    have h2 := Nat.eq_of_mul_eq_mul_left (by positivity) h1
    rw [h2]
    have hq : 2 ∣ 2 ^ (2 * a + 1) := dvd_pow_self 2 (by omega)
    have hq1 : 1 ≤ 2 ^ (2 * a + 1) := Nat.one_le_two_pow
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h with h3 | h3
    · omega
    · have : 2 ∣ (2 ^ (2 * a + 1)) ^ 2 := dvd_pow hq (by norm_num)
      omega
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S (hUXp.toSylow hUXidx)
  have hcrit : ∀ y, y ∈ UX ↔ g⁻¹ * y * g ∈ (S : Subgroup X) := by
    intro y
    have h1 : ((g • S : Sylow 2 X) : Subgroup X) = UX := by
      rw [hg, IsPGroup.toSylow_coe]
    rw [← h1, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, ← map_inv, MulAut.conj_apply, inv_inv]
  set α' := MulAut.conj g * α * (MulAut.conj g)⁻¹ with hα'
  have hα'app : ∀ y, α' y = g * α (g⁻¹ * y * g) * g⁻¹ := by
    intro y
    rw [hα', MulAut.mul_apply, MulAut.mul_apply, ← map_inv, MulAut.conj_apply, MulAut.conj_apply,
      inv_inv]
  have hα'UX : ∀ y ∈ UX, α' y ∈ UX := by
    intro y hy
    rw [hcrit, hα'app]
    have : g⁻¹ * (g * α (g⁻¹ * y * g) * g⁻¹) * g = α (g⁻¹ * y * g) := by group
    rw [this]
    exact hαS _ ((hcrit y).mp hy)
  set β := MulAut.congr e α' with hβ
  have hβapp : ∀ x, β x = e (α' (e.symm x)) := fun x => rfl
  have hβ1 : β = 1 := by
    refine eq_one_of_borel ha hK (e := k) ?_ ?_ ?_
    · have h := conj_pow (a := MulAut.conj g) (b := α) (i := 3 ^ k)
      rw [hβ, ← map_pow, hα', h, hk, mul_one, mul_inv_cancel, map_one]
    · intro x hx
      rw [hβapp, ← hmemUX]
      exact hα'UX _ ((hmemUX _).mpr (by rw [MulEquiv.apply_symm_apply]; exact hx))
    · intro t ht
      have htN := suzukiT_le_normalizer hK ht
      set y := e.symm t with hy
      have hyN : ∀ h, h ∈ UX ↔ y * h * y⁻¹ ∈ UX := by
        intro h
        rw [hmemUX, hmemUX, map_mul, map_mul, map_inv, hy, MulEquiv.apply_symm_apply]
        exact Subgroup.mem_normalizer_iff.mp htN (e h)
      set b := g⁻¹ * y * g with hb
      have hbN : b ∈ Subgroup.normalizer ((S : Subgroup X) : Set X) := by
        rw [Subgroup.mem_normalizer_iff]
        intro h
        have e1 : g⁻¹ * (g * h * g⁻¹) * g = h := by group
        have e2 : g⁻¹ * (y * (g * h * g⁻¹) * y⁻¹) * g = b * h * b⁻¹ := by rw [hb]; group
        rw [← e1, ← hcrit, hyN, hcrit, e2, e1]
      have h1 := hαN b hbN
      have h2 : α' y * y⁻¹ ∈ UX := by
        rw [hcrit]
        have : g⁻¹ * (α' y * y⁻¹) * g = α b * b⁻¹ := by
          rw [hα'app, hb]
          group
        rw [this]
        exact h1
      have h3 : β t * t⁻¹ = e (α' y * y⁻¹) := by
        rw [hβapp, ← hy, map_mul, map_inv, hy, MulEquiv.apply_symm_apply]
      rw [h3]
      exact h2
  have hα'1 : α' = 1 := by
    have := congrArg (MulAut.congr e).symm hβ1
    rwa [hβ, MulEquiv.symm_apply_apply, map_one] at this
  have : α = (MulAut.conj g)⁻¹ * α' * MulAut.conj g := by rw [hα']; group
  rw [this, hα'1, mul_one, inv_mul_cancel]

end CFSG.Quasithin.H13.KGSz
