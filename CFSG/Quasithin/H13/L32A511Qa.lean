module

public import CFSG.Quasithin.Background.D2Involutions

public section

namespace CFSG.Quasithin.H13.Q511

open CFSG.Quasithin

variable {V : Type*} [CommGroup V] [Finite V]

omit [Finite V] in
theorem mem_inf_fix {U : Subgroup V} {g : MulAut V} {v : V} :
    v ∈ U ⊓ fixV (Subgroup.zpowers g) ↔ v ∈ U ∧ g v = v := by
  rw [Subgroup.mem_inf, mem_fixV_zpowers_iff]

theorem rk_map_add_rk_inf (U : Subgroup V) (g : MulAut V) :
    rk (U.map (commHom g)) + rk (U ⊓ fixV (Subgroup.zpowers g) : Subgroup V) = rk U := by
  have := rk_map_add_rk_inf_ker (commHom g) U
  rwa [ker_commHom] at this

omit [Finite V] in
theorem map_commHom_le {U : Subgroup V} {g : MulAut V} (hU : ∀ u ∈ U, g u ∈ U) :
    U.map (commHom g) ≤ U := by
  rintro _ ⟨u, hu, rfl⟩
  exact U.mul_mem (hU u hu) (U.inv_mem hu)

theorem inv_mem_of_invariant {U : Subgroup V} {g : MulAut V} (hU : ∀ u ∈ U, g u ∈ U) :
    ∀ u ∈ U, g⁻¹ u ∈ U := by
  intro u hu
  let f : U → U := fun v => ⟨g v, hU v v.2⟩
  have hf : Function.Injective f := fun a b h =>
    Subtype.ext (g.injective (congrArg Subtype.val h))
  obtain ⟨v, hv⟩ := (Finite.injective_iff_surjective.mp hf) ⟨u, hu⟩
  have h1 : g v = u := congrArg Subtype.val hv
  rw [← h1]
  simp

omit [Finite V] in
theorem pow_mem_of_invariant {U : Subgroup V} {g : MulAut V} (hU : ∀ u ∈ U, g u ∈ U) (n : ℕ) :
    ∀ u ∈ U, (g ^ n) u ∈ U := by
  induction n with
  | zero => intro u hu; simpa using hu
  | succ n ih =>
    intro u hu
    rw [pow_succ', MulAut.mul_apply]
    exact hU _ (ih u hu)

theorem zpowers_invariant {U : Subgroup V} {g : MulAut V} (hU : ∀ u ∈ U, g u ∈ U) :
    ∀ x ∈ Subgroup.zpowers g, ∀ w ∈ U, x w ∈ U := by
  intro x hx w hw
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [zpow_natCast]
    exact pow_mem_of_invariant hU m w hw
  · rw [zpow_neg, zpow_natCast, ← inv_pow]
    exact pow_mem_of_invariant (inv_mem_of_invariant hU) m w hw

omit [Finite V] in
theorem pow_apply_of_comm {g : MulAut V} {u y : V} (hy : g y = y) (hu : g u = y * u) (k : ℕ) :
    (g ^ k) u = y ^ k * u := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hy, hu, pow_succ]
    ac_rfl

omit [Finite V] in
theorem map_commHom_inf_fix_eq_bot (hV : ∀ v : V, v ^ 2 = 1) {g : MulAut V} {n : ℕ}
    (hn : Odd n) (hg : g ^ n = 1) (U : Subgroup V) :
    U.map (commHom g) ⊓ fixV (Subgroup.zpowers g) = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨⟨u, -, rfl⟩, hy⟩
  rw [Subgroup.mem_bot]
  have hy' : g (commHom g u) = commHom g u := mem_fixV_zpowers_iff.mp hy
  set y := commHom g u with hydef
  have hu : g u = y * u := by rw [hydef, commHom_apply]; group
  have h1 := pow_apply_of_comm hy' hu n
  rw [hg] at h1
  have h2 : y ^ n = 1 := by
    have : u = y ^ n * u := h1
    exact (mul_eq_right.mp this.symm)
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, hV y, one_pow, one_mul] at h2
  exact h2

theorem map_commHom_eq_of_fix_eq_bot (hV : ∀ v : V, v ^ 2 = 1) {U : Subgroup V} {g : MulAut V}
    (hU : ∀ u ∈ U, g u ∈ U) (hfix : U ⊓ fixV (Subgroup.zpowers g) = ⊥) :
    U.map (commHom g) = U := by
  refine eq_of_le_of_rk_le hV (map_commHom_le hU) ?_
  have := rk_map_add_rk_inf U g
  rw [hfix, rk_bot] at this
  omega

omit [Finite V] in
theorem map_commHom_le_inf_fix (hV : ∀ v : V, v ^ 2 = 1) {U : Subgroup V} {t : MulAut V}
    (hU : ∀ u ∈ U, t u ∈ U) (ht2 : t ^ 2 = 1) :
    U.map (commHom t) ≤ U ⊓ fixV (Subgroup.zpowers t) := by
  rintro _ ⟨u, hu, rfl⟩
  refine mem_inf_fix.mpr ⟨map_commHom_le hU ⟨u, hu, rfl⟩, ?_⟩
  have htt : t (t u) = u := by
    have : (t ^ 2) u = u := by rw [ht2]; rfl
    simpa [pow_two] using this
  rw [commHom_apply, map_mul, map_inv, htt, inv_eq_self_of_sq_eq_one hV u,
    inv_eq_self_of_sq_eq_one hV (t u), mul_comm]

theorem rk_eq_two_mul_of_inverts (hV : ∀ v : V, v ^ 2 = 1) {U : Subgroup V} {g t : MulAut V}
    (hUg : ∀ u ∈ U, g u ∈ U) (hUt : ∀ u ∈ U, t u ∈ U)
    (hfix : U ⊓ fixV (Subgroup.zpowers g) = ⊥) (ht2 : t ^ 2 = 1) (hinv : t * g * t⁻¹ = g⁻¹) :
    rk U = 2 * rk (U ⊓ fixV (Subgroup.zpowers t) : Subgroup V) := by
  have hle := map_commHom_le_inf_fix hV hUt ht2
  have hge : U ⊓ fixV (Subgroup.zpowers t) ≤ U.map (commHom t) := by
    intro w hw
    obtain ⟨hwU, hwt⟩ := mem_inf_fix.mp hw
    rw [← map_commHom_eq_of_fix_eq_bot hV hUg hfix] at hwU
    obtain ⟨u, hu, rfl⟩ := hwU
    have hxt' : t * g = g⁻¹ * t := by
      have := congrArg (· * t) hinv
      simpa [mul_assoc] using this
    have key : t (g u) = g⁻¹ (t u) := by
      have := congrArg (fun h : MulAut V => h u) hxt'
      simpa using this
    have h1 : commHom g (g⁻¹ (t u))⁻¹ = commHom g u := by
      have e1 : g⁻¹ (t u) * (t u)⁻¹ = commHom g u := by
        calc g⁻¹ (t u) * (t u)⁻¹ = t (g u) * (t u)⁻¹ := by rw [key]
          _ = t (g u * u⁻¹) := by rw [map_mul, map_inv]
          _ = commHom g u := hwt
      rw [commHom_apply, map_inv, show g (g⁻¹ (t u)) = t u by simp, inv_inv, ← e1, mul_comm]
    have hinj : ∀ a ∈ U, ∀ b ∈ U, commHom g a = commHom g b → a = b := by
      intro a ha b hb hab
      have : a * b⁻¹ ∈ U ⊓ fixV (Subgroup.zpowers g) := by
        refine mem_inf_fix.mpr ⟨U.mul_mem ha (U.inv_mem hb), ?_⟩
        have h := congrArg (fun z => z * b * (g b)⁻¹) hab
        simp only [commHom_apply] at h
        rw [map_mul, map_inv]
        calc g a * (g b)⁻¹ = g a * a⁻¹ * a * (g b)⁻¹ := by group
          _ = g b * b⁻¹ * a * (g b)⁻¹ := by rw [show g a * a⁻¹ = g b * b⁻¹ from by
              simpa [commHom_apply] using hab]
          _ = a * b⁻¹ := by
              rw [mul_comm (g b * b⁻¹) a, mul_assoc a, mul_comm (g b * b⁻¹) (g b)⁻¹]
              group
      rw [hfix, Subgroup.mem_bot] at this
      exact mul_inv_eq_one.mp this
    have hmemU : (g⁻¹ (t u))⁻¹ ∈ U :=
      U.inv_mem (inv_mem_of_invariant hUg _ (hUt u hu))
    have h3 : u = (g⁻¹ (t u))⁻¹ := hinj u hu _ hmemU h1.symm
    have h4 : u = g⁻¹ (t u) := by rwa [inv_eq_self_of_sq_eq_one hV] at h3
    have h5 : t u = g u := by
      calc t u = g (g⁻¹ (t u)) := by simp
        _ = g u := by rw [← h4]
    exact ⟨u, hu, by rw [commHom_apply, commHom_apply, h5]⟩
  have heq : U.map (commHom t) = U ⊓ fixV (Subgroup.zpowers t) := le_antisymm hle hge
  have := rk_map_add_rk_inf U t
  rw [heq] at this
  omega

theorem dvd_two_pow_rk_sub_one (hV : ∀ v : V, v ^ 2 = 1) {U : Subgroup V} {g : MulAut V}
    {p : ℕ} [Fact p.Prime] (hU : ∀ u ∈ U, g u ∈ U) (hgp : g ^ p = 1)
    (hfix : U ⊓ fixV (Subgroup.zpowers g) = ⊥) : p ∣ 2 ^ rk U - 1 := by
  have hst : g ∈ stabSub U := fun u => ⟨fun h => by
      have := inv_mem_of_invariant hU _ h
      simpa using this, fun h => hU u h⟩
  set gU := resHom U ⟨g, hst⟩ with hgU
  have h1 : gU ^ p = 1 := by
    rw [hgU, ← map_pow]
    have : (⟨g, hst⟩ : stabSub U) ^ p = 1 := Subtype.ext (by simpa using hgp)
    rw [this, map_one]
  have hpg : IsPGroup p (Subgroup.zpowers gU) := by
    rintro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one]
    show (gU ^ n) ^ p = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h1, one_zpow]
  have hmod := card_modEq_card_fixV hpg
  have hbot : fixV (Subgroup.zpowers gU) = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    have hgu : gU u = u := mem_fixV_zpowers_iff.mp hu
    have hmem : (u : V) ∈ U ⊓ fixV (Subgroup.zpowers g) := by
      refine mem_inf_fix.mpr ⟨u.2, ?_⟩
      have := congrArg Subtype.val hgu
      rwa [hgU, resHom_apply] at this
    rw [hfix, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
  rw [hbot, Subgroup.card_bot, Nat.card_congr (Equiv.refl _)] at hmod
  have hcard : Nat.card U = 2 ^ rk U := card_eq_two_pow hV U
  rw [hcard] at hmod
  exact (Nat.modEq_iff_dvd' (Nat.one_le_two_pow)).mp hmod.symm

omit [Finite V] in
theorem prod_pow_apply_fixed {e : MulAut V} {n : ℕ} (he : e ^ n = 1) (u : V) :
    e (∏ k ∈ Finset.range n, (e ^ k) u) = ∏ k ∈ Finset.range n, (e ^ k) u := by
  rw [map_prod]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have h1 : ∀ k, e ((e ^ k) u) = (e ^ (k + 1)) u := fun k => by
      rw [pow_succ', MulAut.mul_apply]
    simp_rw [h1]
    rw [Finset.prod_range_succ, Finset.prod_range_succ' (fun k => (e ^ k) u), he, pow_zero]

omit [Finite V] in
theorem prod_pow_apply_mem {U : Subgroup V} {e : MulAut V} (hU : ∀ u ∈ U, e u ∈ U) (n : ℕ)
    {u : V} (hu : u ∈ U) : ∏ k ∈ Finset.range n, (e ^ k) u ∈ U :=
  Subgroup.prod_mem _ fun k _ => pow_mem_of_invariant hU k u hu

theorem apply_eq_of_pow_apply_eq {r : MulAut V} {p k : ℕ} (hp : p.Prime) (hr : r ^ p = 1)
    (hk0 : 0 < k) (hkp : k < p) {u : V} (hu : (r ^ k) u = u) : r u = u := by
  rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hr) with h1 | h1
  · rw [orderOf_eq_one_iff.mp h1]
    rfl
  · have h2 := pow_gcd_apply_eq hu
    have hg : Nat.gcd k (orderOf r) = 1 := by
      rw [h1]
      exact Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).mpr
        (Nat.not_dvd_of_pos_of_lt hk0 hkp))
    rw [hg, pow_one] at h2
    exact h2

theorem mem_iSup_inf_fix (hV : ∀ v : V, v ^ 2 = 1) {r r₁ : MulAut V} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hr : r ^ p = 1) (hr₁ : r₁ ^ p = 1) (hc : r * r₁ = r₁ * r) {U : Subgroup V}
    (hUr : ∀ u ∈ U, r u ∈ U) (hUr₁ : ∀ u ∈ U, r₁ u ∈ U)
    (hfix : U ⊓ fixV (Subgroup.zpowers r) = ⊥) {u : V} (hu : u ∈ U) :
    u ∈ ⨆ i ∈ Finset.range p, (U ⊓ fixV (Subgroup.zpowers (r₁ * r ^ i))) := by
  have hcomm : ∀ i : ℕ, Commute r₁ (r ^ i) := fun i => (Commute.pow_right (Commute.symm hc) i)
  have hUe : ∀ i : ℕ, ∀ v ∈ U, (r₁ * r ^ i) v ∈ U := fun i v hv => by
    rw [MulAut.mul_apply]
    exact hUr₁ _ (pow_mem_of_invariant hUr i v hv)
  have hep : ∀ i : ℕ, (r₁ * r ^ i) ^ p = 1 := fun i => by
    rw [(hcomm i).mul_pow, ← pow_mul, mul_comm i p, pow_mul, hr, one_pow, hr₁, one_mul]
  have hmem : ∀ i ∈ Finset.range p, ∏ k ∈ Finset.range p, ((r₁ * r ^ i) ^ k) u ∈
      ⨆ i ∈ Finset.range p, (U ⊓ fixV (Subgroup.zpowers (r₁ * r ^ i))) := by
    intro i hi
    refine (le_biSup (fun i => U ⊓ fixV (Subgroup.zpowers (r₁ * r ^ i))) hi) ?_
    exact mem_inf_fix.mpr ⟨prod_pow_apply_mem (hUe i) p hu, prod_pow_apply_fixed (hep i) u⟩
  have hzero : ∀ k ∈ Finset.range p, k ≠ 0 →
      ∏ i ∈ Finset.range p, ((r ^ k) ^ i) u = 1 := by
    intro k hk hk0
    have hfx : ∏ i ∈ Finset.range p, ((r ^ k) ^ i) u ∈ U ⊓ fixV (Subgroup.zpowers r) := by
      refine mem_inf_fix.mpr ⟨prod_pow_apply_mem (fun v hv => pow_mem_of_invariant hUr k v hv) p
        hu, ?_⟩
      have hrk : (r ^ k) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hr, one_pow]
      exact apply_eq_of_pow_apply_eq hp hr (Nat.pos_of_ne_zero hk0) (Finset.mem_range.mp hk)
        (prod_pow_apply_fixed hrk u)
    rw [hfix, Subgroup.mem_bot] at hfx
    exact hfx
  have hid : ∏ i ∈ Finset.range p, ∏ k ∈ Finset.range p, ((r₁ * r ^ i) ^ k) u = u := by
    have e1 : ∀ i k : ℕ, ((r₁ * r ^ i) ^ k) u = (r₁ ^ k) (((r ^ k) ^ i) u) := by
      intro i k
      rw [(hcomm i).mul_pow, ← pow_mul, ← pow_mul, mul_comm i k, MulAut.mul_apply]
    simp_rw [e1]
    rw [Finset.prod_comm]
    simp_rw [← map_prod]
    obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
    rw [Finset.prod_range_succ']
    have hrest : ∏ k ∈ Finset.range m, (r₁ ^ (k + 1)) (∏ i ∈ Finset.range (m + 1),
        ((r ^ (k + 1)) ^ i) u) = 1 := by
      refine Finset.prod_eq_one fun k hk => ?_
      rw [hzero (k + 1) (Finset.mem_range.mpr (by simpa using hk)) (by omega), map_one]
    rw [hrest, one_mul, pow_zero, pow_zero]
    simp only [one_pow, MulAut.one_apply, Finset.prod_const, Finset.card_range]
    obtain ⟨j, hj⟩ : Odd (m + 1) := hp.odd_of_ne_two hp2
    rw [hj, pow_succ, pow_mul, hV u, one_pow, one_mul]
  rw [← hid]
  exact Subgroup.prod_mem _ hmem

theorem inf_inf_fix_eq_bot {r r₁ : MulAut V} {p : ℕ} (hp : p.Prime) (hr : r ^ p = 1)
    (hc : r * r₁ = r₁ * r) {U : Subgroup V} (hfix : U ⊓ fixV (Subgroup.zpowers r) = ⊥)
    {i j : ℕ} (hij : i < j) (hjp : j < p) :
    (U ⊓ fixV (Subgroup.zpowers (r₁ * r ^ i))) ⊓ (U ⊓ fixV (Subgroup.zpowers (r₁ * r ^ j))) =
      ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  obtain ⟨hvU, hvi⟩ := mem_inf_fix.mp hv.1
  obtain ⟨-, hvj⟩ := mem_inf_fix.mp hv.2
  have hji : r ^ (j - i) * (r₁ * r ^ i) = r₁ * r ^ j := by
    have hcomm : Commute r₁ (r ^ (j - i)) := (Commute.pow_right (Commute.symm hc) _)
    rw [← mul_assoc, ← hcomm.eq, mul_assoc, ← pow_add, Nat.sub_add_cancel hij.le]
  have h1 : (r ^ (j - i)) v = v := by
    have : (r ^ (j - i) * (r₁ * r ^ i)) v = v := by rw [hji]; exact hvj
    rwa [MulAut.mul_apply, hvi] at this
  have h2 := apply_eq_of_pow_apply_eq hp hr (by omega) (by omega) h1
  have : v ∈ U ⊓ fixV (Subgroup.zpowers r) := mem_inf_fix.mpr ⟨hvU, h2⟩
  rwa [hfix] at this

end CFSG.Quasithin.H13.Q511
