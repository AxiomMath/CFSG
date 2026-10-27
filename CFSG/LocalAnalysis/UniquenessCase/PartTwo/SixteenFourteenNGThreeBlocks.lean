module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFourteenNGThreeWeights
public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin

theorem s1614_bl_map_fixV {W : Type} [CommGroup W] (h y : MulAut W) :
    (fixV (Subgroup.zpowers h)).map y.toMonoidHom =
      fixV (Subgroup.zpowers (y * h * y⁻¹)) := by
  ext w
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [mem_fixV_zpowers_iff_apply] at hv ⊢
    change (y * h * y⁻¹) (y v) = y v
    simp only [MulAut.mul_apply, MulAut.inv_apply_self, hv]
  · intro hw
    rw [mem_fixV_zpowers_iff_apply] at hw
    refine ⟨y⁻¹ w, ?_, ?_⟩
    · rw [mem_fixV_zpowers_iff_apply]
      have h := congrArg (fun u => y⁻¹ u) hw
      simpa only [MulAut.mul_apply, MulAut.inv_apply_self] using h
    · change y (y⁻¹ w) = w
      simp

private theorem s1614_bl_rk_map_fixV {W : Type} [CommGroup W] (h y : MulAut W) :
    rk ↥((fixV (Subgroup.zpowers h)).map y.toMonoidHom) = rk ↥(fixV (Subgroup.zpowers h)) := by
  unfold rk
  rw [Subgroup.card_map_of_injective y.injective]

private theorem s1614_bl_fixV_pow {W : Type} [CommGroup W] {h : MulAut W} (h3 : h ^ 3 = 1)
    {n : ℕ} (hn : ¬ 3 ∣ n) :
    fixV (Subgroup.zpowers (h ^ n)) = fixV (Subgroup.zpowers h) := by
  have hmod : n % 3 = 1 ∨ n % 3 = 2 := by
    have hne : n % 3 ≠ 0 := fun h0 => hn (Nat.dvd_iff_mod_eq_zero.mpr h0)
    have hlt : n % 3 < 3 := Nat.mod_lt n (by norm_num)
    omega
  rw [pow_eq_pow_mod n h3]
  rcases hmod with h1 | h2
  · rw [h1, pow_one]
  · rw [h2]
    ext w
    rw [mem_fixV_zpowers_iff_apply, mem_fixV_zpowers_iff_apply]
    constructor
    · intro hw
      calc h w = h ((h ^ 2) w) := by rw [hw]
        _ = (h * h ^ 2) w := by rw [MulAut.mul_apply]
        _ = (h ^ 3) w := by rw [pow_succ' h 2]
        _ = w := by rw [h3, MulAut.one_apply]
    · intro hw
      calc (h ^ 2) w = h (h w) := by rw [pow_two, MulAut.mul_apply]
        _ = w := by rw [hw, hw]

private theorem s1614_bl_conj_mul {W : Type} [CommGroup W] {g z y : MulAut W} {s : ℕ}
    (hyz : y * z = z * y) (hyg : y * g * y⁻¹ = g * z ^ s) (n : ℕ) :
    y * (g * z ^ n) * y⁻¹ = g * z ^ (s + n) := by
  have hyzy : y * z * y⁻¹ = z := by rw [hyz, mul_assoc, mul_inv_cancel, mul_one]
  calc y * (g * z ^ n) * y⁻¹
      = (y * g * y⁻¹) * (y * z ^ n * y⁻¹) := by group
    _ = (g * z ^ s) * (y * z * y⁻¹) ^ n := by rw [hyg, ← conj_pow]
    _ = (g * z ^ s) * z ^ n := by rw [hyzy]
    _ = g * z ^ (s + n) := by rw [mul_assoc, ← pow_add]

private theorem s1614_bl_map_pow {W : Type} [CommGroup W] {g z y : MulAut W} {s : ℕ}
    (hyz : y * z = z * y) (hyg : y * g * y⁻¹ = g * z ^ s) (hz3 : z ^ 3 = 1) (n : ℕ) :
    (fixV (Subgroup.zpowers (g * z ^ n))).map y.toMonoidHom =
      fixV (Subgroup.zpowers (g * z ^ ((s + n) % 3))) := by
  rw [s1614_bl_map_fixV (g * z ^ n) y, s1614_bl_conj_mul hyz hyg n,
    pow_eq_pow_mod (s + n) hz3]

theorem s1614_blocks_rank {W : Type} [CommGroup W] [Finite W] (hW : ∀ x : W, x * x = 1)
    (hcard : Nat.card W = 2 ^ 6) {z g y : MulAut W} (hz3 : z * z * z = 1)
    (hg3 : g * g * g = 1) (hgz : g * z = z * g) (hzfix : ∀ x : W, z x = x → x = 1)
    (hyz : y * z = z * y) {s : ℕ} (hs : ¬ 3 ∣ s) (hyg : y * g * y⁻¹ = g * z ^ s) (j : Fin 3) :
    rk ↥(fixV (Subgroup.zpowers (g * z ^ (j : ℕ)))) = 2 := by
  have hz3' : z ^ 3 = 1 := by
    have h : z ^ 3 = z * z * z := by rw [pow_succ, pow_succ, pow_one]
    rw [h, hz3]
  let Wj : Fin 3 → Subgroup W := fun j => fixV (Subgroup.zpowers (g * z ^ (j:ℕ)))
  have hweights := s1614_weights hW hz3 hg3 hgz hzfix
  have hind : iSupIndep Wj := hweights.1
  have hsup : ⨆ j, Wj j = ⊤ := hweights.2
  let f : Fin 3 → Fin 3 := fun j => ⟨(s + (j:ℕ)) % 3, Nat.mod_lt _ (by norm_num)⟩
  have hrank (j : Fin 3) : rk ↥(Wj j) = rk ↥(Wj (f j)) := by
    rw [← s1614_bl_rk_map_fixV (g * z ^ (j:ℕ)) y]
    exact congrArg (fun H : Subgroup W => rk ↥H) (s1614_bl_map_pow hyz hyg hz3' (j:ℕ))
  have hsmod : s % 3 = 1 ∨ s % 3 = 2 := by
    have hne : s % 3 ≠ 0 := fun h0 => hs (Nat.dvd_iff_mod_eq_zero.mpr h0)
    have hlt : s % 3 < 3 := Nat.mod_lt s (by norm_num)
    omega
  have he01 : rk ↥(Wj 0) = rk ↥(Wj 1) ∧ rk ↥(Wj 1) = rk ↥(Wj 2) := by
    rcases hsmod with hs1 | hs2
    · have h0 : f 0 = 1 := by ext; simp [f, hs1]
      have h1 : f 1 = 2 := by
        ext
        show (s + 1) % 3 = 2
        rw [Nat.add_mod, hs1]
      exact ⟨by have := hrank 0; rwa [h0] at this, by have := hrank 1; rwa [h1] at this⟩
    · have h0 : f 0 = 2 := by ext; simp [f, hs2]
      have h1 : f 1 = 0 := by
        ext
        show (s + 1) % 3 = 0
        rw [Nat.add_mod, hs2]
      have e02 : rk ↥(Wj 0) = rk ↥(Wj 2) := by have := hrank 0; rwa [h0] at this
      have e10 : rk ↥(Wj 1) = rk ↥(Wj 0) := by have := hrank 1; rwa [h1] at this
      exact ⟨e10.symm, e10.trans e02⟩
  obtain ⟨e01, e12⟩ := he01
  have hd := iSupIndep_fin_three.mp hind
  have hAB : Wj 0 ⊓ Wj 1 = ⊥ := by
    have hle : Wj 0 ⊓ Wj 1 ≤ Wj 0 ⊓ (Wj 1 ⊔ Wj 2) := inf_le_inf_left _ le_sup_left
    rw [disjoint_iff.mp hd.1] at hle
    exact le_bot_iff.mp hle
  have hABC : (Wj 0 ⊔ Wj 1) ⊓ Wj 2 = ⊥ := by
    rw [inf_comm]
    exact disjoint_iff.mp hd.2.2
  have e1 : rk ↥(Wj 0 ⊔ Wj 1) = rk ↥(Wj 0) + rk ↥(Wj 1) := by
    have h := rk_sup_add_rk_inf (Wj 0) (Wj 1)
    rw [hAB, rk_bot, add_zero] at h
    exact h
  have e2 : rk ↥(Wj 0 ⊔ Wj 1 ⊔ Wj 2) = rk ↥(Wj 0 ⊔ Wj 1) + rk ↥(Wj 2) := by
    have h := rk_sup_add_rk_inf (Wj 0 ⊔ Wj 1) (Wj 2)
    rw [hABC, rk_bot, add_zero] at h
    exact h
  have htop : rk ↥(Wj 0 ⊔ Wj 1 ⊔ Wj 2) = rk W := by
    rw [← iSup_fin_three, hsup, rk_top]
  have hsum : rk ↥(Wj 0) + rk ↥(Wj 1) + rk ↥(Wj 2) = rk W := by
    rw [← e1, ← e2, htop]
  have hrkW : rk W = 6 := by
    have h := card_eq_two_pow (V := W) (fun x => by rw [pow_two]; exact hW x) ⊤
    rw [Subgroup.card_top, rk_top, hcard] at h
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 2) h).symm
  have hsum6 : rk ↥(Wj 0) + rk ↥(Wj 1) + rk ↥(Wj 2) = 6 := by rw [hsum, hrkW]
  have h3r : 3 * rk ↥(Wj 0) = 6 := by
    rw [← hsum6, ← e12, ← e01]
    ring
  have hr0 : rk ↥(Wj 0) = 2 := by omega
  fin_cases j
  · change rk ↥(Wj 0) = 2; exact hr0
  · change rk ↥(Wj 1) = 2; rw [← e01]; exact hr0
  · change rk ↥(Wj 2) = 2; rw [← e12, ← e01]; exact hr0

theorem s1614_blocks_perm {W : Type} [CommGroup W] {z g t : MulAut W} (hz3 : z * z * z = 1)
    (hg3 : g * g * g = 1) (hgz : g * z = z * g) {a b e : ℕ} (ha : ¬ 3 ∣ a)
    (htg : t * g * t⁻¹ = g ^ a * z ^ b) (htz : t * z * t⁻¹ = z ^ e) (j : Fin 3) :
    ∃ j' : Fin 3, (fixV (Subgroup.zpowers (g * z ^ (j : ℕ)))).map t.toMonoidHom =
      fixV (Subgroup.zpowers (g * z ^ (j' : ℕ))) := by
  have hz3' : z ^ 3 = 1 := by
    have h : z ^ 3 = z * z * z := by rw [pow_succ, pow_succ, pow_one]
    rw [h, hz3]
  have hg3' : g ^ 3 = 1 := by
    have h : g ^ 3 = g * g * g := by rw [pow_succ, pow_succ, pow_one]
    rw [h, hg3]
  set c : ℕ := b + e * (j : ℕ) with hc
  have hgc : Commute g z := (commute_iff_eq g z).mpr hgz
  have hconj : t * (g * z ^ (j:ℕ)) * t⁻¹ = g ^ a * z ^ c := by
    rw [hc]
    calc t * (g * z ^ (j:ℕ)) * t⁻¹
        = (t * g * t⁻¹) * (t * z ^ (j:ℕ) * t⁻¹) := by group
      _ = (g ^ a * z ^ b) * (t * z * t⁻¹) ^ (j:ℕ) := by rw [htg, ← conj_pow]
      _ = (g ^ a * z ^ b) * (z ^ e) ^ (j:ℕ) := by rw [htz]
      _ = g ^ a * z ^ (b + e * (j:ℕ)) := by rw [← pow_mul, mul_assoc, ← pow_add]
  rw [s1614_bl_map_fixV (g * z ^ (j:ℕ)) t, hconj]
  have hmod : a % 3 = 1 ∨ a % 3 = 2 := by
    have hne : a % 3 ≠ 0 := fun h0 => ha (Nat.dvd_iff_mod_eq_zero.mpr h0)
    have hlt : a % 3 < 3 := Nat.mod_lt a (by norm_num)
    omega
  rcases hmod with ha1 | ha2
  · have hga : g ^ a = g := by rw [pow_eq_pow_mod a hg3', ha1, pow_one]
    refine ⟨⟨c % 3, Nat.mod_lt c (by norm_num)⟩, ?_⟩
    rw [hga, pow_eq_pow_mod c hz3']
  · have hga : g ^ a = g ^ 2 := by rw [pow_eq_pow_mod a hg3', ha2]
    have hc2 : (a * 2) % 3 = 1 := by omega
    have hh2 : (g ^ a * z ^ c) ^ 2 = g * z ^ ((c * 2) % 3) := by
      rw [hgc.pow_pow a c |>.mul_pow 2, ← pow_mul g a 2, ← pow_mul z c 2,
        pow_eq_pow_mod (a * 2) hg3', hc2, pow_one, pow_eq_pow_mod (c * 2) hz3']
    have hga3 : (g ^ a) ^ 3 = 1 := by
      rw [← pow_mul, Nat.mul_comm a 3, pow_mul, hg3', one_pow]
    have hzc3 : (z ^ c) ^ 3 = 1 := by
      rw [← pow_mul, Nat.mul_comm c 3, pow_mul, hz3', one_pow]
    have hh3 : (g ^ a * z ^ c) ^ 3 = 1 := by
      rw [hgc.pow_pow a c |>.mul_pow 3, hga3, hzc3, mul_one]
    refine ⟨⟨(c * 2) % 3, Nat.mod_lt _ (by norm_num)⟩, ?_⟩
    rw [← hh2, s1614_bl_fixV_pow hh3 (by norm_num : ¬ 3 ∣ 2)]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
