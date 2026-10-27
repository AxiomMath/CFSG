module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.GCD

public section

namespace CFSG.StandardType.KGUniv

private lemma list_prod_range_inv_mul {G : Type*} [CommGroup G] (p : ℕ) (t : G) (f : ℕ → G) :
    ((List.range p).map (fun _ => t)).prod⁻¹ * ((List.range p).map f).prod
      = ((List.range p).map (fun i => t⁻¹ * f i)).prod := by
  rw [List.prod_inv, List.map_map, ← List.prod_map_mul]
  rfl

private lemma prod_range_const_eq_pow {G : Type*} [Monoid G] (p : ℕ) (t : G) :
    ((List.range p).map (fun _ => t)).prod = t ^ p := by
  have h := List.prod_eq_pow_length ((List.range p).map (fun _ => t)) t (by
    intro x hx
    rcases List.mem_map.mp hx with ⟨i, -, rfl⟩
    rfl)
  simpa [List.length_map, List.length_range] using h

private lemma pow_inv_prod_range_mem {G : Type*} [CommGroup G] (Φ : MulAut G) (Y : Subgroup G)
    (hYΦ : ∀ y : G, Φ y ∈ Y ↔ y ∈ Y) (p : ℕ) (t : G) (ht : t⁻¹ * Φ t ∈ Y) :
    (t ^ p)⁻¹ * ((List.range p).map (fun i => (Φ ^ i) t)).prod ∈ Y := by
  have step : ∀ i : ℕ, t⁻¹ * (Φ ^ i) t ∈ Y := by
    intro i
    induction i with
    | zero => simpa using Y.one_mem
    | succ i ih =>
      have h : t⁻¹ * (Φ ^ (i + 1)) t = (t⁻¹ * Φ t) * Φ (t⁻¹ * (Φ ^ i) t) := by
        rw [pow_succ', MulAut.mul_apply]
        simp only [map_mul, map_inv]
        group
      rw [h]
      exact Y.mul_mem ht ((hYΦ _).mpr ih)
  rw [← prod_range_const_eq_pow, list_prod_range_inv_mul]
  exact Subgroup.list_prod_mem Y (by
    intro x hx
    rcases List.mem_map.mp hx with ⟨i, -, rfl⟩
    exact step i)

theorem exists_norm_mod_of_fixed_mod {p : ℕ} (hp : p.Prime) {C : Type} [Group C] [Finite C]
    (M Y : Subgroup C) (hM : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a) (β : MulAut C)
    (hMβ : ∀ t : C, β t ∈ M ↔ t ∈ M) (hYM : Y ≤ M) (hYβ : ∀ t : C, β t ∈ Y ↔ t ∈ Y)
    (hYp : Nat.Coprime (Nat.card Y) p)
    (hnorm : ∀ t ∈ M, β t = t →
      ∃ s ∈ M, t = ((List.range p).map fun i => (β ^ i) s).prod)
    (x : C) (hx : x ∈ M) (hxY : x⁻¹ * β x ∈ Y) :
    ∃ s ∈ M, x * (((List.range p).map fun i => (β ^ i) s).prod)⁻¹ ∈ Y := by
  letI : CommGroup M :=
    CommGroup.mk (fun a b => Subtype.ext (hM a a.2 b b.2))
  let Φ : MulAut M :=
    { toFun := fun s => ⟨β (s : C), (hMβ (s : C)).mpr s.2⟩
      invFun := fun s => ⟨β⁻¹ (s : C), (hMβ (β⁻¹ (s : C))).mp (by simpa using s.2)⟩
      left_inv := fun s => Subtype.ext (by simp)
      right_inv := fun s => Subtype.ext (by simp)
      map_mul' := fun s t => Subtype.ext (by simp [Subgroup.coe_mul]) }
  let YM : Subgroup M := Y.subgroupOf M
  have hYM' : ∀ y : M, y ∈ YM ↔ (y : C) ∈ Y := fun y => Subgroup.mem_subgroupOf
  have hYΦ : ∀ y : M, Φ y ∈ YM ↔ y ∈ YM := by
    intro y
    rw [hYM', hYM']
    exact hYβ (y : C)
  let norm : M → M := fun s => ((List.range p).map fun i => (Φ ^ i) s).prod
  have hcoe : ∀ (i : ℕ) (s : M), (((Φ ^ i) s : M) : C) = (β ^ i) (s : C) := by
    intro i s
    induction i with
    | zero => simp
    | succ i ih =>
      have h1 : (((Φ ^ (i + 1)) s : M) : C) = β (((Φ ^ i) s : C)) := by
        rw [pow_succ', MulAut.mul_apply]
        rfl
      have h2 : (β ^ (i + 1)) (s : C) = β ((β ^ i) (s : C)) := by
        rw [pow_succ', MulAut.mul_apply]
      rw [h1, h2, ih]
  have norm_coe : ∀ s : M, (norm s : C) = ((List.range p).map fun i => (β ^ i) (s : C)).prod := by
    intro s
    dsimp only [norm]
    rw [Subgroup.val_list_prod, List.map_map]
    apply congrArg List.prod
    apply List.map_congr_left
    intro i _
    exact hcoe i s
  have norm_mul : ∀ s t : M, norm (s * t) = norm s * norm t := by
    intro s t
    dsimp only [norm]
    simp_rw [map_mul]
    rw [List.prod_map_mul]
  have fixed_pow : ∀ (z : M), z⁻¹ * Φ z ∈ YM → ∀ k : ℤ, (z ^ k)⁻¹ * Φ (z ^ k) ∈ YM := by
    intro z hz k
    have h : (z ^ k)⁻¹ * Φ (z ^ k) = (z⁻¹ * Φ z) ^ k := by
      rw [map_zpow, ← inv_zpow, ← mul_zpow]
    rw [h]
    exact YM.zpow_mem hz k
  set n : ℕ := orderOf (⟨x, hx⟩ : M) with hn_def
  have hn_ne : n ≠ 0 := by
    rw [hn_def]
    exact (isOfFinOrder_of_finite (⟨x, hx⟩ : M)).orderOf_pos.ne'
  obtain ⟨a, m, hm_ndvd, hn_eq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn_ne p hp.ne_one
  have hcop_pow : Nat.Coprime m (p ^ a) := hp.coprime_pow_of_not_dvd hm_ndvd
  have hcop' : Nat.Coprime (p ^ a) m := hcop_pow.symm
  have hm_ne : m ≠ 0 := by
    rintro rfl
    simp only [mul_zero] at hn_eq
    exact hn_ne hn_eq
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * ((p ^ a : ℕ) : ℤ) + v * (m : ℤ) = 1 := by
    refine ⟨Nat.gcdA (p ^ a) m, Nat.gcdB (p ^ a) m, ?_⟩
    have h := Nat.gcd_eq_gcd_ab (p ^ a) m
    rw [Nat.Coprime.gcd_eq_one hcop'] at h
    norm_num at h
    rw [mul_comm (Nat.gcdA (p ^ a) m) (((p ^ a : ℕ) : ℤ)),
      mul_comm (Nat.gcdB (p ^ a) m) ((m : ℕ) : ℤ)]
    exact h.symm
  let xp : M := (⟨x, hx⟩ : M) ^ (v * (m : ℤ))
  let xq : M := (⟨x, hx⟩ : M) ^ (u * ((p ^ a : ℕ) : ℤ))
  have hx_split : (⟨x, hx⟩ : M) = xp * xq := by
    have h1 : (⟨x, hx⟩ : M) = (⟨x, hx⟩ : M) ^ (u * ((p ^ a : ℕ) : ℤ) + v * (m : ℤ)) := by
      rw [huv, zpow_one]
    rw [h1, zpow_add]
    show (⟨x, hx⟩ : M) ^ (u * ((p ^ a : ℕ) : ℤ)) * (⟨x, hx⟩ : M) ^ (v * (m : ℤ)) = xp * xq
    rw [show xp = (⟨x, hx⟩ : M) ^ (v * (m : ℤ)) from rfl,
      show xq = (⟨x, hx⟩ : M) ^ (u * ((p ^ a : ℕ) : ℤ)) from rfl, mul_comm]
  have hn_pow : (⟨x, hx⟩ : M) ^ n = 1 := by
    rw [hn_def]
    exact pow_orderOf_eq_one _
  have hxp_pow : xp ^ (p ^ a) = 1 := by
    show ((⟨x, hx⟩ : M) ^ (v * (m : ℤ))) ^ (p ^ a) = 1
    rw [← zpow_natCast, ← zpow_mul]
    have hexp : v * (m : ℤ) * ((p ^ a : ℕ) : ℤ) = v * (n : ℤ) := by
      rw [hn_eq]
      push_cast
      ring
    rw [hexp]
    rw [show v * (n : ℤ) = (n : ℤ) * v by ring, zpow_mul]
    have hnz : (⟨x, hx⟩ : M) ^ (n : ℤ) = 1 := by
      rw [zpow_natCast]
      exact hn_pow
    rw [hnz, one_zpow]
  have hxq_pow : xq ^ m = 1 := by
    show ((⟨x, hx⟩ : M) ^ (u * ((p ^ a : ℕ) : ℤ))) ^ m = 1
    rw [← zpow_natCast, ← zpow_mul]
    have hexp : u * ((p ^ a : ℕ) : ℤ) * (m : ℤ) = u * (n : ℤ) := by
      rw [hn_eq]
      push_cast
      ring
    rw [hexp]
    rw [show u * (n : ℤ) = (n : ℤ) * u by ring, zpow_mul]
    have hnz : (⟨x, hx⟩ : M) ^ (n : ℤ) = 1 := by
      rw [zpow_natCast]
      exact hn_pow
    rw [hnz, one_zpow]
  have hxY' : (⟨x, hx⟩ : M)⁻¹ * Φ (⟨x, hx⟩ : M) ∈ YM := by
    refine (hYM' _).mpr ?_
    simpa [Φ, Subgroup.coe_mul, Subgroup.coe_inv] using hxY
  have hu0Y : xp⁻¹ * Φ xp ∈ YM := by
    have := fixed_pow (⟨x, hx⟩ : M) hxY' (v * (m : ℤ))
    simpa [xp] using this
  have hu0_pow : (xp⁻¹ * Φ xp) ^ (p ^ a) = 1 := by
    rw [mul_pow, inv_pow, ← map_pow, hxp_pow]
    simp
  have hu0C_pow : (((xp⁻¹ * Φ xp : M)) : C) ^ (p ^ a) = 1 := by
    rw [← Subgroup.coe_pow, hu0_pow]
    simp
  have hu0Y_C : (((xp⁻¹ * Φ xp : M)) : C) ∈ Y := (hYM' (xp⁻¹ * Φ xp)).mp hu0Y
  have horder_one : orderOf (((xp⁻¹ * Φ xp : M)) : C) = 1 := by
    refine Nat.eq_one_of_dvd_coprimes (hYp.pow_right a) ?_ ?_
    · exact Subgroup.orderOf_dvd_natCard Y hu0Y_C
    · exact orderOf_dvd_of_pow_eq_one hu0C_pow
  have hu0C_eq : (((xp⁻¹ * Φ xp : M)) : C) = (xp : C)⁻¹ * β (xp : C) := by
    simp [Φ, Subgroup.coe_mul]
  have hfix_xp : β (xp : C) = (xp : C) := by
    have h : (xp : C)⁻¹ * β (xp : C) = 1 := by rw [← hu0C_eq, orderOf_eq_one_iff.mp horder_one]
    calc β (xp : C) = 1 * β (xp : C) := by rw [one_mul]
      _ = ((xp : C) * (xp : C)⁻¹) * β (xp : C) := by rw [mul_inv_cancel]
      _ = (xp : C) * ((xp : C)⁻¹ * β (xp : C)) := by rw [mul_assoc]
      _ = (xp : C) * 1 := by rw [h]
      _ = (xp : C) := by rw [mul_one]
  obtain ⟨sp, hspM, hsp⟩ := hnorm (xp : C) xp.2 hfix_xp
  have hcop_pm : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hm_ndvd
  obtain ⟨r, hr_lt, hr_mod⟩ :=
    Nat.exists_mul_mod_eq_of_coprime (n := p) (k := m) 1 hcop_pm hm_ne
  have hmod : r * p ≡ 1 [MOD m] := by
    show (r * p) % m = 1 % m
    rw [mul_comm]
    exact hr_mod
  have hxqY : xq⁻¹ * Φ xq ∈ YM := by
    have := fixed_pow (⟨x, hx⟩ : M) hxY' (u * ((p ^ a : ℕ) : ℤ))
    simpa [xq] using this
  let t : M := xq ^ r
  have htY : t⁻¹ * Φ t ∈ YM := by
    have := fixed_pow xq hxqY (r : ℤ)
    simpa [t, zpow_natCast] using this
  have ht_pow : t ^ p = xq := by
    show (xq ^ r) ^ p = xq
    rw [← pow_mul]
    have hmod' : r * p ≡ 1 [MOD orderOf xq] :=
      Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one hxq_pow) hmod
    simpa using (pow_eq_pow_iff_modEq (x := xq) (n := r * p) (m := 1)).mpr hmod'
  have hxq_norm : xq⁻¹ * norm t ∈ YM := by
    have := pow_inv_prod_range_mem Φ YM hYΦ p t htY
    rwa [ht_pow] at this
  let sM : M := ⟨sp, hspM⟩ * t
  have hnsp : norm ⟨sp, hspM⟩ = xp := by
    apply Subtype.ext
    rw [norm_coe]
    simpa using hsp.symm
  have hnorm_sM : norm sM = xp * norm t := by
    show norm (⟨sp, hspM⟩ * t) = xp * norm t
    rw [norm_mul, hnsp]
  have hmem : (⟨x, hx⟩ : M) * (norm sM)⁻¹ ∈ YM := by
    rw [hnorm_sM]
    have heq : (⟨x, hx⟩ : M) * (xp * norm t)⁻¹ = (xq⁻¹ * norm t)⁻¹ := by
      rw [hx_split]
      calc xp * xq * (xp * norm t)⁻¹
          = xp * xq * ((norm t)⁻¹ * xp⁻¹) := by rw [mul_inv_rev]
        _ = (xp * xp⁻¹) * (xq * (norm t)⁻¹) := by ac_rfl
        _ = 1 * (xq * (norm t)⁻¹) := by rw [mul_inv_cancel]
        _ = (norm t)⁻¹ * xq := by rw [one_mul, mul_comm]
        _ = (xq⁻¹ * norm t)⁻¹ := by rw [mul_inv_rev, inv_inv]
    rw [heq]
    exact YM.inv_mem hxq_norm
  refine ⟨(sM : C), sM.2, ?_⟩
  have := (hYM' ((⟨x, hx⟩ : M) * (norm sM)⁻¹)).mp hmem
  simpa [sM, norm_coe, Subgroup.coe_mul, Subgroup.coe_inv] using this

end CFSG.StandardType.KGUniv
