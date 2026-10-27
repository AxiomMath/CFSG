module

public import CFSG.Quasithin.Background.CommVBasics
public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.Quasithin.Background.D2Params

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem inv_eq_self_of_sq_eq_one (hV : ∀ v : V, v ^ 2 = 1) (v : V) : v⁻¹ = v := by
  have := hV v
  rw [pow_two, mul_eq_one_iff_eq_inv] at this
  exact this.symm

theorem commSub_zpowers_le_inf_fixV [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {t : MulAut V}
    (ht : t ^ 2 = 1) {W : Subgroup V} (hW : ∀ x ∈ Subgroup.zpowers t, ∀ w ∈ W, x w ∈ W) :
    commSub W (Subgroup.zpowers t) ≤ W ⊓ fixV (Subgroup.zpowers t) := by
  rw [commSub_zpowers_eq_map hW]
  rintro _ ⟨w, hw, rfl⟩
  refine ⟨W.mul_mem (hW t (Subgroup.mem_zpowers t) w hw) (W.inv_mem hw), ?_⟩
  show commHom t w ∈ fixV (Subgroup.zpowers t)
  rw [mem_fixV_zpowers_iff, commHom_apply, map_mul, map_inv]
  have h2 : t (t w) = w := by
    have : (t ^ 2) w = w := by rw [ht]; rfl
    simpa [pow_two] using this
  rw [h2, inv_eq_self_of_sq_eq_one hV w, inv_eq_self_of_sq_eq_one hV (t w), mul_comm]

theorem commV_zpowers_le_fixV [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {t : MulAut V}
    (ht : t ^ 2 = 1) : commV (Subgroup.zpowers t) ≤ fixV (Subgroup.zpowers t) := by
  have := commSub_zpowers_le_inf_fixV hV ht (W := ⊤) (fun _ _ w _ => Subgroup.mem_top _)
  rw [← commV_eq_commSub, top_inf_eq] at this
  exact this

theorem isQuadratic_zpowers [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {t : MulAut V}
    (ht : t ^ 2 = 1) : IsQuadratic (Subgroup.zpowers t) := by
  intro c hc x hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hfix : c ∈ fixV (Subgroup.zpowers t) := commV_zpowers_le_fixV hV ht hc
  exact hfix _ hx

theorem fixV_eq_commV_of_inverts [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {x t : MulAut V}
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (ht2 : t ^ 2 = 1) (hxt : t * x * t⁻¹ = x⁻¹) :
    fixV (Subgroup.zpowers t) = commV (Subgroup.zpowers t) := by
  refine le_antisymm ?_ (commV_zpowers_le_fixV hV ht2)
  intro w hw
  have hwt : t w = w := mem_fixV_zpowers_iff.mp hw
  have hinj : Function.Injective (commHom x) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_commHom, hfix]
  obtain ⟨u, hu⟩ := (Finite.injective_iff_surjective.mp hinj) w
  have hxt' : t * x = x⁻¹ * t := by
    have := congrArg (· * t) hxt
    simpa [mul_assoc] using this
  have key : t (x u) = x⁻¹ (t u) := by
    have := congrArg (fun g : MulAut V => g u) hxt'
    simpa using this
  have h1 : x⁻¹ (t u) * (t u)⁻¹ = w := by
    calc x⁻¹ (t u) * (t u)⁻¹ = t (x u) * (t u)⁻¹ := by rw [key]
      _ = t (x u * u⁻¹) := by rw [map_mul, map_inv]
      _ = t w := by rw [← hu]; rfl
      _ = w := hwt
  have hxz : x (x⁻¹ (t u)) = t u := by simp
  have h2 : commHom x (x⁻¹ (t u))⁻¹ = w := by
    rw [commHom_apply, map_inv, hxz, inv_inv, ← h1, mul_comm]
  have h3 : u = (x⁻¹ (t u))⁻¹ := hinj (hu.trans h2.symm)
  have h4 : u = x⁻¹ (t u) := by
    rw [inv_eq_self_of_sq_eq_one hV] at h3
    exact h3
  have h5 : t u = x u := by
    calc t u = x (x⁻¹ (t u)) := hxz.symm
      _ = x u := by rw [← h4]
  rw [commV_zpowers_eq_map]
  refine ⟨u, Subgroup.mem_top _, ?_⟩
  rw [commHom_apply, h5, ← commHom_apply, hu]

theorem rk_eq_two_mul_of_inverts [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {x t : MulAut V}
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (ht2 : t ^ 2 = 1) (hxt : t * x * t⁻¹ = x⁻¹) :
    rk V = 2 * rk (commV (Subgroup.zpowers t)) := by
  have h := rk_commV_add_rk_fixV t
  rw [fixV_eq_commV_of_inverts hV hfix ht2 hxt] at h
  omega

theorem pow_gcd_apply_eq [Finite V] {y : MulAut V} {j : ℕ} {v : V} (h : (y ^ j) v = v) :
    (y ^ Nat.gcd j (orderOf y)) v = v := by
  by_cases hd : orderOf y ∣ j
  · rw [Nat.gcd_eq_right hd, pow_orderOf_eq_one]
    rfl
  · have hlt : Nat.gcd j (orderOf y) < orderOf y := by
      refine lt_of_le_of_ne (Nat.le_of_dvd (orderOf_pos y) (Nat.gcd_dvd_right _ _)) fun h' => hd ?_
      rw [← h']
      exact Nat.gcd_dvd_left _ _
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_gcd hlt
    have : y ^ Nat.gcd j (orderOf y) = (y ^ j) ^ m := by
      rw [← pow_mul, ← hm, pow_mod_orderOf]
    rw [this]
    have hs : y ^ j ∈ MulAction.stabilizer (MulAut V) v := h
    exact Subgroup.pow_mem _ hs m

theorem card_ne_one_add_one (H : Subgroup V) [Finite V] :
    Nat.card {c : V // c ∈ H ∧ c ≠ 1} + 1 = Nat.card H := by
  classical
  have : Fintype H := Fintype.ofFinite H
  have e : {c : V // c ∈ H ∧ c ≠ 1} ≃ {c : H // c ≠ 1} :=
    { toFun := fun c => ⟨⟨c.1, c.2.1⟩, fun h => c.2.2 (congrArg Subtype.val h)⟩
      invFun := fun c => ⟨c.1.1, c.1.2, fun h => c.2 (Subtype.ext h)⟩
      left_inv := fun c => rfl
      right_inv := fun c => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  have := Fintype.card_subtype_compl (fun c : H => c = 1)
  simp only [Fintype.card_subtype_eq] at this
  simp only [ne_eq] at *
  have hpos : 0 < Fintype.card H := Fintype.card_pos
  omega

theorem two_le_rk_of_invariant [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {x : MulAut V}
    (hfix : fixV (Subgroup.zpowers x) = ⊥) {F : Subgroup V} (hF : ∀ w ∈ F, x w ∈ F)
    (hF0 : F ≠ ⊥) : 2 ≤ rk F := by
  by_contra h
  have h0 : rk F ≠ 0 := fun h0 => hF0 ((rk_eq_zero_iff hV).mp h0)
  have h1 : rk F = 1 := by omega
  have hcard : Nat.card F = 2 := by rw [card_eq_two_pow hV F, h1]; norm_num
  obtain ⟨c, hcF, hc1⟩ : ∃ c ∈ F, c ≠ 1 := by
    obtain ⟨c, hne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hF0
    exact ⟨c, c.2, fun h => hne (Subtype.ext h)⟩
  have hxc : x c ∈ F := hF c hcF
  have hxc1 : x c ≠ 1 := by
    intro h
    exact hc1 (x.injective (by rw [h, map_one]))
  have hxcc : x c = c := by
    by_contra hne
    have h3 : 2 < Nat.card F := by
      classical
      have : Fintype F := Fintype.ofFinite F
      rw [Nat.card_eq_fintype_card, ← Finset.card_univ, Finset.two_lt_card_iff]
      refine ⟨1, ⟨c, hcF⟩, ⟨x c, hxc⟩, Finset.mem_univ _, Finset.mem_univ _, Finset.mem_univ _,
        ?_, ?_, ?_⟩
      · intro h; exact hc1 (congrArg Subtype.val h).symm
      · intro h; exact hxc1 (congrArg Subtype.val h).symm
      · intro h; exact hne (congrArg Subtype.val h).symm
    omega
  have : c ∈ fixV (Subgroup.zpowers x) := mem_fixV_zpowers_iff.mpr hxcc
  rw [hfix, Subgroup.mem_bot] at this
  exact hc1 this

theorem not_seven_dvd_orderOf [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {x : MulAut V}
    (hrk : rk V = 4) (hfix : fixV (Subgroup.zpowers x) = ⊥) : ¬ 7 ∣ orderOf x := by
  intro h7
  obtain ⟨m, hm⟩ := h7
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact (orderOf_pos x).ne' hm
  have hy : orderOf (x ^ m) = 7 := by
    rw [orderOf_pow_of_dvd hm0 ⟨7, by rw [hm]; ring⟩, hm]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hgrp : IsPGroup 7 (Subgroup.zpowers (x ^ m)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy]; simp)
  have hmod := card_modEq_card_fixV hgrp
  rw [card_eq_two_pow_rk hV, hrk, card_eq_two_pow hV] at hmod
  have hFle : rk (fixV (Subgroup.zpowers (x ^ m))) ≤ 4 := by
    have := rk_mono (le_top : fixV (Subgroup.zpowers (x ^ m)) ≤ ⊤)
    rwa [rk_top, hrk] at this
  have hF4 : rk (fixV (Subgroup.zpowers (x ^ m))) ≠ 4 := by
    intro h4
    have h1 : fixV (Subgroup.zpowers (x ^ m)) = ⊤ :=
      eq_of_le_of_rk_le hV le_top (by rw [rk_top, hrk, h4])
    have h2 : x ^ m = 1 := eq_one_of_fixV_eq_top h1
    rw [h2, orderOf_one] at hy
    omega
  have hF1 : rk (fixV (Subgroup.zpowers (x ^ m))) = 1 := by
    have key : ∀ e ≤ 4, e ≠ 4 → 2 ^ 4 ≡ 2 ^ e [MOD 7] → e = 1 := by decide
    exact key _ hFle hF4 hmod
  have hF0 : fixV (Subgroup.zpowers (x ^ m)) ≠ ⊥ := by
    intro h
    rw [h, rk_bot] at hF1
    omega
  have hinv : ∀ w ∈ fixV (Subgroup.zpowers (x ^ m)), x w ∈ fixV (Subgroup.zpowers (x ^ m)) := by
    intro w hw
    rw [mem_fixV_zpowers_iff] at hw ⊢
    have hcomm : x ^ m * x = x * x ^ m := (Commute.pow_left (Commute.refl x) m).eq
    calc (x ^ m) (x w) = (x ^ m * x) w := rfl
      _ = (x * x ^ m) w := by rw [hcomm]
      _ = x ((x ^ m) w) := rfl
      _ = x w := by rw [hw]
  have := two_le_rk_of_invariant hV hfix hinv hF0
  omega

theorem fixV_pow_eq_bot_of_orderOf_fifteen [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {x : MulAut V}
    (hrk : rk V = 4) (hfix : fixV (Subgroup.zpowers x) = ⊥) (hx : orderOf x = 15) :
    fixV (Subgroup.zpowers (x ^ 3)) = ⊥ ∧ fixV (Subgroup.zpowers (x ^ 5)) = ⊥ := by
  have h3 : fixV (Subgroup.zpowers (x ^ 3)) = ⊥ := by
    have hy : orderOf (x ^ 3) = 5 := by
      rw [orderOf_pow_of_dvd (by norm_num) (by rw [hx]; norm_num), hx]
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have hgrp : IsPGroup 5 (Subgroup.zpowers (x ^ 3)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy]; simp)
    have hmod := card_modEq_card_fixV hgrp
    rw [card_eq_two_pow_rk hV, hrk, card_eq_two_pow hV] at hmod
    have hFle : rk (fixV (Subgroup.zpowers (x ^ 3))) ≤ 4 := by
      have := rk_mono (le_top : fixV (Subgroup.zpowers (x ^ 3)) ≤ ⊤)
      rwa [rk_top, hrk] at this
    have hF4 : rk (fixV (Subgroup.zpowers (x ^ 3))) ≠ 4 := by
      intro h4
      have h1 : fixV (Subgroup.zpowers (x ^ 3)) = ⊤ :=
        eq_of_le_of_rk_le hV le_top (by rw [rk_top, hrk, h4])
      have h2 : x ^ 3 = 1 := eq_one_of_fixV_eq_top h1
      rw [h2, orderOf_one] at hy
      omega
    have hF0 : rk (fixV (Subgroup.zpowers (x ^ 3))) = 0 := by
      have key : ∀ e ≤ 4, e ≠ 4 → 2 ^ 4 ≡ 2 ^ e [MOD 5] → e = 0 := by decide
      exact key _ hFle hF4 hmod
    exact (rk_eq_zero_iff hV).mp hF0
  refine ⟨h3, ?_⟩
  set F := fixV (Subgroup.zpowers (x ^ 5)) with hF
  have hcomm : ∀ g ∈ Subgroup.zpowers x, g * x ^ 5 = x ^ 5 * g := by
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    exact (Commute.zpow_left (Commute.pow_right (Commute.refl x) 5) k).eq
  have hΩ : ∀ g ∈ Subgroup.zpowers x, ∀ v ∈ ((F : Set V)ᶜ : Set V),
      g v ∈ ((F : Set V)ᶜ : Set V) := by
    intro g hg v hv hgv
    apply hv
    have h1 : (x ^ 5) (g v) = g v := mem_fixV_zpowers_iff.mp hgv
    have h2 : g ((x ^ 5) v) = g v := by
      have hc := hcomm g hg
      calc g ((x ^ 5) v) = (g * x ^ 5) v := rfl
        _ = (x ^ 5 * g) v := by rw [hc]
        _ = (x ^ 5) (g v) := rfl
        _ = g v := h1
    exact mem_fixV_zpowers_iff.mpr (g.injective h2)
  have hfree : ∀ g ∈ Subgroup.zpowers x, ∀ v ∈ ((F : Set V)ᶜ : Set V), g v = v → g = 1 := by
    intro g hg v hv hgv
    by_contra hg1
    apply hv
    obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff g x).mp
      ((mem_powers_iff_mem_zpowers (x := x) (y := g)).mpr hg)
    have hfix' := pow_gcd_apply_eq hgv
    rw [hx] at hfix'
    have hdvd : Nat.gcd j 15 ∣ 15 := Nat.gcd_dvd_right _ _
    have hcases : Nat.gcd j 15 = 1 ∨ Nat.gcd j 15 = 3 ∨ Nat.gcd j 15 = 5 ∨ Nat.gcd j 15 = 15 := by
      have : Nat.gcd j 15 ∈ Nat.divisors 15 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have hd : Nat.divisors 15 = {1, 3, 5, 15} := by decide
      rw [hd] at this
      simpa using this
    rcases hcases with h | h | h | h
    · rw [h, pow_one] at hfix'
      have : v ∈ fixV (Subgroup.zpowers x) := mem_fixV_zpowers_iff.mpr hfix'
      rw [hfix, Subgroup.mem_bot] at this
      subst this
      exact one_mem _
    · rw [h] at hfix'
      have : v ∈ fixV (Subgroup.zpowers (x ^ 3)) := mem_fixV_zpowers_iff.mpr hfix'
      rw [h3, Subgroup.mem_bot] at this
      subst this
      exact one_mem _
    · rw [h] at hfix'
      exact mem_fixV_zpowers_iff.mpr hfix'
    · exfalso
      apply hg1
      have h15 : 15 ∣ j := by
        have := Nat.gcd_dvd_left j 15
        rwa [h] at this
      exact (orderOf_dvd_iff_pow_eq_one).mp (hx ▸ h15)
  have hdvd := card_dvd_card_of_free hΩ hfree
  rw [Nat.card_zpowers, hx, card_compl_fixV F] at hdvd
  have hFlt : rk F < 4 := by
    by_contra hge
    rw [not_lt] at hge
    have h1 : F = ⊤ := eq_of_le_of_rk_le hV le_top (by rw [rk_top, hrk]; exact hge)
    have h2 : x ^ 5 = 1 := eq_one_of_fixV_eq_top h1
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [hx] at h3
    omega
  rw [card_eq_two_pow_rk hV, hrk, card_eq_two_pow hV F] at hdvd
  have hF0 : rk F = 0 := by
    have key : ∀ e < 4, 15 ∣ 2 ^ 4 - 2 ^ e → e = 0 := by decide
    exact key _ hFlt hdvd
  exact (rk_eq_zero_iff hV).mp hF0

theorem no_order_fifteen [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {x t : MulAut V} (hrk : rk V = 4)
    (hfix : fixV (Subgroup.zpowers x) = ⊥) (hx : orderOf x = 15) (ht2 : t ^ 2 = 1)
    (hxt : t * x * t⁻¹ = x⁻¹) : False := by
  obtain ⟨h3, h5⟩ := fixV_pow_eq_bot_of_orderOf_fifteen hV hrk hfix hx
  have hff : ∀ (m : ℕ) (v : V), v ≠ 1 → (x ^ m) v = v → 15 ∣ m := by
    intro m v hv hmv
    have hfx := pow_gcd_apply_eq hmv
    rw [hx] at hfx
    have hdvd : Nat.gcd m 15 ∣ 15 := Nat.gcd_dvd_right _ _
    have hcases : Nat.gcd m 15 = 1 ∨ Nat.gcd m 15 = 3 ∨ Nat.gcd m 15 = 5 ∨ Nat.gcd m 15 = 15 := by
      have : Nat.gcd m 15 ∈ Nat.divisors 15 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have hd : Nat.divisors 15 = {1, 3, 5, 15} := by decide
      rw [hd] at this
      simpa using this
    rcases hcases with h | h | h | h
    · exfalso
      rw [h, pow_one] at hfx
      have : v ∈ fixV (Subgroup.zpowers x) := mem_fixV_zpowers_iff.mpr hfx
      rw [hfix, Subgroup.mem_bot] at this
      exact hv this
    · exfalso
      rw [h] at hfx
      have : v ∈ fixV (Subgroup.zpowers (x ^ 3)) := mem_fixV_zpowers_iff.mpr hfx
      rw [h3, Subgroup.mem_bot] at this
      exact hv this
    · exfalso
      rw [h] at hfx
      have : v ∈ fixV (Subgroup.zpowers (x ^ 5)) := mem_fixV_zpowers_iff.mpr hfx
      rw [h5, Subgroup.mem_bot] at this
      exact hv this
    · have := Nat.gcd_dvd_left m 15
      rwa [h] at this
  have hrkt := rk_eq_two_mul_of_inverts hV hfix ht2 hxt
  have hfreet := fixV_eq_commV_of_inverts hV hfix ht2 hxt
  have hC : rk (fixV (Subgroup.zpowers t)) = 2 := by rw [hfreet]; omega
  have hx15 : x ^ 15 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hxinv : x⁻¹ = x ^ 14 := by
    refine (eq_inv_of_mul_eq_one_right ?_).symm
    rw [← pow_succ']
    exact hx15
  have hconj : ∀ a : ℕ, t * x ^ a * t⁻¹ = x ^ (14 * a) := by
    intro a
    rw [← conj_pow, hxt, hxinv, ← pow_mul]
  have ht' : ∀ (a : ℕ) (v : V), t ((x ^ a) v) = (x ^ (14 * a)) (t v) := by
    intro a v
    have h1 : t * x ^ a = x ^ (14 * a) * t := by
      have := hconj a
      calc t * x ^ a = (t * x ^ a * t⁻¹) * t := by group
        _ = x ^ (14 * a) * t := by rw [this]
    calc t ((x ^ a) v) = (t * x ^ a) v := rfl
      _ = (x ^ (14 * a) * t) v := by rw [h1]
      _ = (x ^ (14 * a)) (t v) := rfl
  have hxpow : ∀ (a b : ℕ) (v : V), (x ^ a) ((x ^ b) v) = (x ^ (a + b)) v := by
    intro a b v
    rw [pow_add]
    rfl
  have hx15' : ∀ (n : ℕ) (v : V), (x ^ (15 * n)) v = v := by
    intro n v
    rw [pow_mul, hx15, one_pow]
    rfl
  let S := {c : V // c ∈ fixV (Subgroup.zpowers t) ∧ c ≠ 1}
  let T := {c : V // c ∈ (⊤ : Subgroup V) ∧ c ≠ 1}
  let f : Fin 15 × S → T := fun p =>
    ⟨(x ^ (p.1 : ℕ)) p.2.1, Subgroup.mem_top _, fun h => p.2.2.2 ((x ^ (p.1 : ℕ)).injective
      (by rw [h, map_one]))⟩
  have hinj : Function.Injective f := by
    rintro ⟨i, c, hc, hc1⟩ ⟨i', c', hc', hc1'⟩ hf
    have hA : (x ^ (i : ℕ)) c = (x ^ (i' : ℕ)) c' := congrArg Subtype.val hf
    have hct : t c = c := mem_fixV_zpowers_iff.mp hc
    have hct' : t c' = c' := mem_fixV_zpowers_iff.mp hc'
    have hB : (x ^ (14 * (i : ℕ))) c = (x ^ (14 * (i' : ℕ))) c' := by
      have := congrArg t hA
      rwa [ht', ht', hct, hct'] at this
    have hC : (x ^ (14 * (i' : ℕ) + (i : ℕ))) c = c' := by
      calc (x ^ (14 * (i' : ℕ) + (i : ℕ))) c
          = (x ^ (14 * (i' : ℕ))) ((x ^ (i : ℕ)) c) := (hxpow _ _ _).symm
        _ = (x ^ (14 * (i' : ℕ))) ((x ^ (i' : ℕ)) c') := by rw [hA]
        _ = (x ^ (14 * (i' : ℕ) + (i' : ℕ))) c' := hxpow _ _ _
        _ = c' := by
          have := hx15' (i' : ℕ) c'
          rwa [show 14 * (i' : ℕ) + (i' : ℕ) = 15 * (i' : ℕ) by ring]
    have hD : (x ^ ((i' : ℕ) + 14 * (i : ℕ))) c = c' := by
      calc (x ^ ((i' : ℕ) + 14 * (i : ℕ))) c
          = (x ^ (i' : ℕ)) ((x ^ (14 * (i : ℕ))) c) := (hxpow _ _ _).symm
        _ = (x ^ (i' : ℕ)) ((x ^ (14 * (i' : ℕ))) c') := by rw [hB]
        _ = (x ^ ((i' : ℕ) + 14 * (i' : ℕ))) c' := hxpow _ _ _
        _ = c' := by
          have := hx15' (i' : ℕ) c'
          rwa [show (i' : ℕ) + 14 * (i' : ℕ) = 15 * (i' : ℕ) by ring]
    have hE : (x ^ (2 * (i : ℕ) + 28 * (i' : ℕ))) c = c := by
      have h1 : (x ^ (14 * (i' : ℕ) + (i : ℕ))) c = (x ^ ((i' : ℕ) + 14 * (i : ℕ))) c :=
        hC.trans hD.symm
      have h2 := congrArg (fun w => (x ^ ((i : ℕ) + 14 * (i' : ℕ))) w) h1
      simp only [hxpow] at h2
      have h3 : (i : ℕ) + 14 * (i' : ℕ) + (14 * (i' : ℕ) + (i : ℕ)) =
          2 * (i : ℕ) + 28 * (i' : ℕ) := by ring
      have h4 : (i : ℕ) + 14 * (i' : ℕ) + ((i' : ℕ) + 14 * (i : ℕ)) =
          15 * ((i : ℕ) + (i' : ℕ)) := by ring
      rw [h3, h4, hx15'] at h2
      exact h2
    have hdvd := hff _ c hc1 hE
    have hii : (i : ℕ) = (i' : ℕ) := by
      have := i.2
      have := i'.2
      omega
    have hii' : i = i' := Fin.ext hii
    subst hii'
    have hcc : c = c' := (x ^ (i : ℕ)).injective hA
    subst hcc
    rfl
  have hle := Nat.card_le_card_of_injective f hinj
  have hS : Nat.card S = 3 := by
    have h1 := card_ne_one_add_one (fixV (Subgroup.zpowers t))
    rw [card_eq_two_pow hV, hC] at h1
    have : Nat.card S = Nat.card {c : V // c ∈ fixV (Subgroup.zpowers t) ∧ c ≠ 1} := rfl
    omega
  have hT : Nat.card T = 15 := by
    have h1 := card_ne_one_add_one (⊤ : Subgroup V)
    rw [Subgroup.card_top, card_eq_two_pow_rk hV, hrk] at h1
    have : Nat.card T = Nat.card {c : V // c ∈ (⊤ : Subgroup V) ∧ c ≠ 1} := rfl
    omega
  rw [Nat.card_prod, hS, hT, Nat.card_eq_fintype_card, Fintype.card_fin] at hle
  omega

theorem small_dihedral [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {x t : MulAut V}
    (hxodd : Odd (orderOf x)) (hx1 : x ≠ 1) (hfix : fixV (Subgroup.zpowers x) = ⊥)
    (ht2 : t ^ 2 = 1) (hxt : t * x * t⁻¹ = x⁻¹) (hrk : rk V ≤ 4) :
    (rk V = 2 ∧ orderOf x = 3) ∨ (rk V = 4 ∧ (orderOf x = 3 ∨ orderOf x = 5)) := by
  have hrk2 := rk_eq_two_mul_of_inverts hV hfix ht2 hxt
  have hn1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
  have hV0 : rk V ≠ 0 := by
    intro h0
    apply hx1
    have hcard : Nat.card V = 1 := by rw [card_eq_two_pow_rk hV, h0]; rfl
    have : Subsingleton V := (Nat.card_eq_one_iff_unique.mp hcard).1
    ext v
    exact Subsingleton.elim _ _
  have hd : rk V = 2 ∨ rk V = 4 := by omega
  have hdvd : orderOf x ∣ Nat.card (MulAut V) := orderOf_dvd_natCard x
  have hcardAut := card_mulAut_eq hV
  rcases hd with hd | hd
  · left
    refine ⟨hd, ?_⟩
    rw [hd] at hcardAut
    have h6 : Nat.card (MulAut V) = 6 := by
      rw [hcardAut]
      simp [Fin.prod_univ_two]
    rw [h6] at hdvd
    generalize orderOf x = n at hdvd hxodd hn1 ⊢
    have hle : n ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases n <;> simp_all <;> contradiction
  · right
    refine ⟨hd, ?_⟩
    have hcard4 : Nat.card (MulAut V) = 20160 := by
      rw [hd] at hcardAut
      rw [hcardAut]
      simp [Fin.prod_univ_four]
    rw [hcard4] at hdvd
    have h315 : orderOf x ∣ 315 := by
      have hcop : Nat.Coprime (orderOf x) 64 := by
        have : Nat.Coprime (orderOf x) 2 := Nat.coprime_two_right.mpr hxodd
        simpa using this.pow_right 6
      have h20160 : (20160 : ℕ) = 315 * 64 := by norm_num
      rw [h20160] at hdvd
      exact hcop.dvd_of_dvd_mul_right hdvd
    have h9 : ¬ 9 ∣ orderOf x := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have := not_sq_dvd_orderOf hV (q := 3) (Or.inl rfl) (by omega) x
      simpa using this
    have h7 : ¬ 7 ∣ orderOf x := not_seven_dvd_orderOf hV hd hfix
    have h15 : orderOf x ∣ 15 := by
      have h105 : orderOf x ∣ 105 := by
        have key : ∀ n ∈ Nat.divisors 315, ¬ 9 ∣ n → n ∣ 105 := by decide
        exact key _ (Nat.mem_divisors.mpr ⟨h315, by norm_num⟩) h9
      have key : ∀ n ∈ Nat.divisors 105, ¬ 7 ∣ n → n ∣ 15 := by decide
      exact key _ (Nat.mem_divisors.mpr ⟨h105, by norm_num⟩) h7
    have hcases : orderOf x = 1 ∨ orderOf x = 3 ∨ orderOf x = 5 ∨ orderOf x = 15 := by
      have : orderOf x ∈ Nat.divisors 15 := Nat.mem_divisors.mpr ⟨h15, by norm_num⟩
      have hdv : Nat.divisors 15 = {1, 3, 5, 15} := by decide
      rw [hdv] at this
      simpa using this
    rcases hcases with h | h | h | h
    · exact absurd h hn1
    · exact Or.inl h
    · exact Or.inr h
    · exact (no_order_fifteen hV hd hfix h ht2 hxt).elim

section Normalize

theorem commV_smul_mem {P : Subgroup (MulAut V)} {g : MulAut V}
    (hg : ∀ p ∈ P, g * p * g⁻¹ ∈ P) {c : V} (hc : c ∈ commV P) : g c ∈ commV P :=
  CFSG.Quasithin.commV_apply_mem_of_normalizes hg hc

theorem fixV_smul_mem {P : Subgroup (MulAut V)} {g : MulAut V}
    (hg : ∀ p ∈ P, g⁻¹ * p * g ∈ P) {c : V} (hc : c ∈ fixV P) : g c ∈ fixV P := by
  intro p hp
  have h1 : (g⁻¹ * p * g) c = c := hc _ (hg p hp)
  have : p (g c) = g c := by
    calc p (g c) = g (g⁻¹ (p (g c))) := by simp
      _ = g ((g⁻¹ * p * g) c) := rfl
      _ = g c := by rw [h1]
  exact this

theorem mem_stabSub_commV {P : Subgroup (MulAut V)} {g : MulAut V}
    (hg : ∀ p ∈ P, g * p * g⁻¹ ∈ P) (hg' : ∀ p ∈ P, g⁻¹ * p * g ∈ P) :
    g ∈ stabSub (commV P) := by
  intro u
  constructor
  · intro h
    have := commV_smul_mem (g := g⁻¹) (by simpa using hg') h
    simpa using this
  · exact commV_smul_mem hg

theorem mem_stabSub_fixV {P : Subgroup (MulAut V)} {g : MulAut V}
    (hg : ∀ p ∈ P, g * p * g⁻¹ ∈ P) (hg' : ∀ p ∈ P, g⁻¹ * p * g ∈ P) :
    g ∈ stabSub (fixV P) := by
  intro u
  constructor
  · intro h
    have := fixV_smul_mem (g := g⁻¹) (by simpa using hg) h
    simpa using this
  · exact fixV_smul_mem hg'


theorem rk_fixV_resHom [Finite V] {W : Subgroup V} {g : MulAut V} (hg : g ∈ stabSub W) :
    rk (fixV (Subgroup.zpowers (resHom W ⟨g, hg⟩))) = rk ↥(W ⊓ fixV (Subgroup.zpowers g)) := by
  have hmap : (fixV (Subgroup.zpowers (resHom W ⟨g, hg⟩))).map W.subtype =
      W ⊓ fixV (Subgroup.zpowers g) := by
    ext v
    simp only [Subgroup.mem_map, Subgroup.subtype_apply, Subgroup.mem_inf]
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨w.2, mem_fixV_zpowers_iff.mpr (congrArg Subtype.val (mem_fixV_zpowers_iff.mp hw))⟩
    · rintro ⟨hvW, hv⟩
      exact ⟨⟨v, hvW⟩, mem_fixV_zpowers_iff.mpr (Subtype.ext (mem_fixV_zpowers_iff.mp hv)), rfl⟩
  unfold rk
  rw [← hmap, Subgroup.card_map_of_injective W.subtype_injective]

theorem rk_commV_resHom [Finite V] {W : Subgroup V} {g : MulAut V} (hg : g ∈ stabSub W)
    (hW : ∀ x ∈ Subgroup.zpowers g, ∀ w ∈ W, x w ∈ W) :
    rk (commV (Subgroup.zpowers (resHom W ⟨g, hg⟩))) = rk (commSub W (Subgroup.zpowers g)) := by
  have h1 := rk_commV_add_rk_fixV (resHom W ⟨g, hg⟩)
  have h2 := rk_commSub_add_rk_inf_fixV hW
  have h3 := rk_fixV_resHom hg
  omega

theorem orderOf_resHom_eq [Finite V] {W : Subgroup V} {x : MulAut V} (hx : x ∈ stabSub W)
    (hW : W ⊔ fixV (Subgroup.zpowers x) = ⊤) : orderOf (resHom W ⟨x, hx⟩) = orderOf x := by
  have hcoe : ∀ (n : ℕ) (w : W), (((resHom W ⟨x, hx⟩) ^ n) w : V) = (x ^ n) w := by
    intro n w
    rw [← map_pow]
    rfl
  apply Nat.dvd_antisymm
  · apply orderOf_dvd_of_pow_eq_one
    ext w
    rw [hcoe, pow_orderOf_eq_one]
    rfl
  · apply orderOf_dvd_of_pow_eq_one
    ext v
    have hv : v ∈ W ⊔ fixV (Subgroup.zpowers x) := by rw [hW]; exact Subgroup.mem_top v
    obtain ⟨w, hw, c, hc, rfl⟩ := Subgroup.mem_sup.mp hv
    have h1 : (x ^ orderOf (resHom W ⟨x, hx⟩)) w = w := by
      have := hcoe (orderOf (resHom W ⟨x, hx⟩)) ⟨w, hw⟩
      rw [pow_orderOf_eq_one] at this
      exact this.symm
    have h2 : (x ^ orderOf (resHom W ⟨x, hx⟩)) c = c := by
      have hs : x ∈ MulAction.stabilizer (MulAut V) c := mem_fixV_zpowers_iff.mp hc
      exact Subgroup.pow_mem _ hs _
    rw [map_mul, h1, h2]
    rfl

end Normalize

theorem d2_11_core [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {t x : MulAut V} (ht2 : t ^ 2 = 1)
    (hm : rk (commV (Subgroup.zpowers t)) ≤ 2) (hx1 : x ≠ 1) (hodd : Odd (orderOf x))
    (hinv : t * x * t⁻¹ = x⁻¹) :
    rk (commV (Subgroup.zpowers x)) =
        2 * rk (commSub (commV (Subgroup.zpowers x)) (Subgroup.zpowers t)) ∧
      rk (commSub (commV (Subgroup.zpowers x)) (Subgroup.zpowers t)) ≤
        rk (commV (Subgroup.zpowers t)) ∧
      ((rk (commV (Subgroup.zpowers x)) = 2 ∧ orderOf x = 3) ∨
        (rk (commV (Subgroup.zpowers x)) = 4 ∧ (orderOf x = 3 ∨ orderOf x = 5))) := by
  have hP : Odd (Nat.card (Subgroup.zpowers x)) := by rw [Nat.card_zpowers]; exact hodd
  obtain ⟨hsup, hinf⟩ := coprime_decomp hP hV (W := ⊤) (fun _ _ w _ => Subgroup.mem_top _)
  rw [← commV_eq_commSub, top_inf_eq] at hsup hinf
  have htinv : t⁻¹ = t := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, ht2]
  have hn : ∀ p ∈ Subgroup.zpowers x, x * p * x⁻¹ ∈ Subgroup.zpowers x := by
    intro p hp
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    rw [(Commute.zpow_right (Commute.refl x) k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k
  have hn' : ∀ p ∈ Subgroup.zpowers x, x⁻¹ * p * x ∈ Subgroup.zpowers x := by
    intro p hp
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    rw [mul_assoc, ← (Commute.zpow_right (Commute.refl x) k).eq, ← mul_assoc, inv_mul_cancel,
      one_mul]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) k
  have htn : ∀ p ∈ Subgroup.zpowers x, t * p * t⁻¹ ∈ Subgroup.zpowers x := by
    intro p hp
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    rw [← conj_zpow, hinv, inv_zpow']
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) _
  have htn' : ∀ p ∈ Subgroup.zpowers x, t⁻¹ * p * t ∈ Subgroup.zpowers x := by
    intro p hp
    have := htn p hp
    rw [htinv] at this ⊢
    exact this
  have hxs : x ∈ stabSub (commV (Subgroup.zpowers x)) := mem_stabSub_commV hn hn'
  have hts : t ∈ stabSub (commV (Subgroup.zpowers x)) := mem_stabSub_commV htn htn'
  have hWt : ∀ y ∈ Subgroup.zpowers t, ∀ w ∈ commV (Subgroup.zpowers x),
      y w ∈ commV (Subgroup.zpowers x) := by
    intro y hy w hw
    have : Subgroup.zpowers t ≤ stabSub (commV (Subgroup.zpowers x)) := by
      rw [Subgroup.zpowers_le]; exact hts
    exact ((this hy) w).mpr hw
  set W := commV (Subgroup.zpowers x) with hWdef
  have hVW : ∀ w : W, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV w)
  have hfix' : fixV (Subgroup.zpowers (resHom W ⟨x, hxs⟩)) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun w hw => ?_
    have hxw : x (w : V) = w := congrArg Subtype.val (mem_fixV_zpowers_iff.mp hw)
    have hmem : (w : V) ∈ W ⊓ fixV (Subgroup.zpowers x) :=
      ⟨w.2, mem_fixV_zpowers_iff.mpr hxw⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have ht2' : resHom W ⟨t, hts⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨t, hts⟩ : stabSub W) ^ 2 = 1 := Subtype.ext (by simpa using ht2)
    rw [this, map_one]
  have hxt' : resHom W ⟨t, hts⟩ * resHom W ⟨x, hxs⟩ * (resHom W ⟨t, hts⟩)⁻¹ =
      (resHom W ⟨x, hxs⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    exact Subtype.ext (by simpa using hinv)
  have hCW : W ⊔ fixV (Subgroup.zpowers x) = ⊤ := hsup
  have hord := orderOf_resHom_eq hxs hCW
  have hxodd' : Odd (orderOf (resHom W ⟨x, hxs⟩)) := by rw [hord]; exact hodd
  have hx1' : resHom W ⟨x, hxs⟩ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    exact hx1 (orderOf_eq_one_iff.mp hord.symm)
  have hrk2 := rk_eq_two_mul_of_inverts hVW hfix' ht2' hxt'
  have hrkt := rk_commV_resHom hts hWt
  have hle : rk (commSub W (Subgroup.zpowers t)) ≤ rk (commV (Subgroup.zpowers t)) := by
    rw [commV_eq_commSub]
    exact rk_mono (commSub_mono le_top le_rfl)
  refine ⟨by rw [← hrkt]; exact hrk2, hle, ?_⟩
  have hrkW : rk W ≤ 4 := by omega
  have := small_dihedral hVW hxodd' hx1' hfix' ht2' hxt' hrkW
  rwa [hord] at this

@[expose] def TInv (X : Subgroup (MulAut V)) : Set (MulAut V) :=
  {t | t ∈ X ∧ t ≠ 1 ∧ t ^ 2 = 1 ∧ rk (commV (Subgroup.zpowers t)) ≤ 2}

theorem D2_11_1 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} {t x : MulAut V}
    (ht : t ∈ TInv X) (hm : rk (commV (Subgroup.zpowers t)) = 1) (_hx : x ∈ X) (hx1 : x ≠ 1)
    (hodd : Odd (orderOf x)) (hinv : t * x * t⁻¹ = x⁻¹) :
    orderOf x = 3 ∧ rk (commV (Subgroup.zpowers x)) = 2 := by
  obtain ⟨h1, h2, h3⟩ := d2_11_core hV ht.2.2.1 ht.2.2.2 hx1 hodd hinv
  rw [hm] at h2
  rcases h3 with ⟨h5, h6⟩ | ⟨h5, h6⟩
  · exact ⟨h6, h5⟩
  · omega

theorem D2_11_2 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} {t x : MulAut V}
    (ht : t ∈ TInv X) (_hm : rk (commV (Subgroup.zpowers t)) = 2) (_hx : x ∈ X) (hx1 : x ≠ 1)
    (hodd : Odd (orderOf x)) (hinv : t * x * t⁻¹ = x⁻¹) :
    (orderOf x = 3 ∨ orderOf x = 5) ∧
      (orderOf x = 5 → rk (commV (Subgroup.zpowers x)) = 4) := by
  obtain ⟨h1, h2, h3⟩ := d2_11_core hV ht.2.2.1 ht.2.2.2 hx1 hodd hinv
  rcases h3 with ⟨h5, h6⟩ | ⟨h5, h6⟩
  · exact ⟨Or.inl h6, fun h => by omega⟩
  · exact ⟨h6, fun _ => h5⟩

theorem D2_11_3 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} {t x : MulAut V}
    (ht : t ∈ TInv X) (_hx : x ∈ X) (hx1 : x ≠ 1) (hodd : Odd (orderOf x))
    (hinv : t * x * t⁻¹ = x⁻¹)
    (hm : rk (commV (Subgroup.zpowers x)) = 2 * rk (commV (Subgroup.zpowers t))) :
    commSub (commV (Subgroup.zpowers x)) (Subgroup.zpowers t) = commV (Subgroup.zpowers t) ∧
      commSub (fixV (Subgroup.zpowers x)) (Subgroup.zpowers t) = ⊥ ∧
      ∀ y ∈ X, y ∈ Subgroup.centralizer ({x} : Set (MulAut V)) →
        y ∈ centSub (commV (Subgroup.zpowers x)) → y * t = t * y := by
  obtain ⟨h1, h2, -⟩ := d2_11_core hV ht.2.2.1 ht.2.2.2 hx1 hodd hinv
  have hP : Odd (Nat.card (Subgroup.zpowers x)) := by rw [Nat.card_zpowers]; exact hodd
  obtain ⟨hsup, hinf⟩ := coprime_decomp hP hV (W := ⊤) (fun _ _ w _ => Subgroup.mem_top _)
  rw [← commV_eq_commSub, top_inf_eq] at hsup hinf
  set W := commV (Subgroup.zpowers x) with hWdef
  set C := fixV (Subgroup.zpowers x) with hCdef
  have ht2 : t ^ 2 = 1 := ht.2.2.1
  have htinv : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, ← pow_two, ht2]
  have hn : ∀ p ∈ Subgroup.zpowers x, t * p * t⁻¹ ∈ Subgroup.zpowers x := by
    intro p hp
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
    rw [← conj_zpow, hinv, inv_zpow']
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers x) _
  have hn' : ∀ p ∈ Subgroup.zpowers x, t⁻¹ * p * t ∈ Subgroup.zpowers x := by
    intro p hp
    have := hn p hp
    rw [htinv] at this ⊢
    exact this
  have hts : t ∈ stabSub W := mem_stabSub_commV hn hn'
  have htC : t ∈ stabSub C := mem_stabSub_fixV hn hn'
  have hWt : ∀ y ∈ Subgroup.zpowers t, ∀ w ∈ W, y w ∈ W := by
    intro y hy w hw
    have : Subgroup.zpowers t ≤ stabSub W := by rw [Subgroup.zpowers_le]; exact hts
    exact ((this hy) w).mpr hw
  have hCt : ∀ y ∈ Subgroup.zpowers t, ∀ w ∈ C, y w ∈ C := by
    intro y hy w hw
    have : Subgroup.zpowers t ≤ stabSub C := by rw [Subgroup.zpowers_le]; exact htC
    exact ((this hy) w).mpr hw
  have hsubW : commSub W (Subgroup.zpowers t) ≤ commV (Subgroup.zpowers t) := by
    rw [commV_eq_commSub]
    exact commSub_mono le_top le_rfl
  have hsubC : commSub C (Subgroup.zpowers t) ≤ commV (Subgroup.zpowers t) := by
    rw [commV_eq_commSub]
    exact commSub_mono le_top le_rfl
  have hVt : commV (Subgroup.zpowers t) ≤
      commSub W (Subgroup.zpowers t) ⊔ commSub C (Subgroup.zpowers t) := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨y, hy, v, rfl⟩
    have hv : v ∈ W ⊔ C := by rw [hsup]; exact Subgroup.mem_top v
    obtain ⟨w, hw, c, hc, rfl⟩ := Subgroup.mem_sup.mp hv
    have : y (w * c) * (w * c)⁻¹ = (y w * w⁻¹) * (y c * c⁻¹) := by
      rw [map_mul, mul_inv]
      ac_rfl
    rw [this]
    exact Subgroup.mul_mem_sup (Subgroup.subset_closure ⟨y, hy, w, hw, rfl⟩)
      (Subgroup.subset_closure ⟨y, hy, c, hc, rfl⟩)
  have hdisj : commSub W (Subgroup.zpowers t) ⊓ commSub C (Subgroup.zpowers t) = ⊥ := by
    refine le_bot_iff.mp ?_
    calc commSub W (Subgroup.zpowers t) ⊓ commSub C (Subgroup.zpowers t) ≤ W ⊓ C :=
          inf_le_inf (commSub_le_of_invariant hWt) (commSub_le_of_invariant hCt)
      _ = ⊥ := hinf
      _ ≤ ⊥ := le_rfl
  have hrkVt : rk (commV (Subgroup.zpowers t)) ≤
      rk ↥(commSub W (Subgroup.zpowers t) ⊔ commSub C (Subgroup.zpowers t)) := rk_mono hVt
  have hrkVt' : rk ↥(commSub W (Subgroup.zpowers t) ⊔ commSub C (Subgroup.zpowers t)) ≤
      rk (commV (Subgroup.zpowers t)) := rk_mono (sup_le hsubW hsubC)
  have hsum := rk_sup_add_rk_inf (commSub W (Subgroup.zpowers t)) (commSub C (Subgroup.zpowers t))
  rw [hdisj, rk_bot] at hsum
  have hrkC : rk (commSub C (Subgroup.zpowers t)) = 0 := by omega
  have hCbot : commSub C (Subgroup.zpowers t) = ⊥ := (rk_eq_zero_iff hV).mp hrkC
  have hWeq : commSub W (Subgroup.zpowers t) = commV (Subgroup.zpowers t) := by
    refine eq_of_le_of_rk_le hV hsubW ?_
    omega
  refine ⟨hWeq, hCbot, ?_⟩
  intro y _ hyx hyW
  have hyxc : y * x = x * y := by
    have := Subgroup.mem_centralizer_iff.mp hyx x (Set.mem_singleton x)
    exact this.symm
  have htCfix : ∀ c ∈ C, t c = c := by
    intro c hc
    have : c ∈ fixV (Subgroup.zpowers t) := (commSub_eq_bot_iff.mp hCbot) hc
    exact mem_fixV_zpowers_iff.mp this
  ext v
  have hv : v ∈ W ⊔ C := by rw [hsup]; exact Subgroup.mem_top v
  obtain ⟨w, hw, c, hc, rfl⟩ := Subgroup.mem_sup.mp hv
  have hyc : y c ∈ C := by
    intro g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hc' : (x ^ k) c = c := hc _ hg
    have hcomm : (x ^ k) * y = y * x ^ k := by
      have : Commute y x := hyxc
      exact (this.zpow_right k).symm.eq
    calc (x ^ k) (y c) = ((x ^ k) * y) c := rfl
      _ = (y * x ^ k) c := by rw [hcomm]
      _ = y ((x ^ k) c) := rfl
      _ = y c := by rw [hc']
  have htw : t w ∈ W := hWt t (Subgroup.mem_zpowers t) w hw
  have hyfix : ∀ u ∈ W, y u = u := fun u hu => hyW u hu
  have hL : (y * t) (w * c) = t w * y c := by
    simp only [MulAut.mul_apply, map_mul]
    rw [hyfix _ htw, htCfix c hc]
  have hR : (t * y) (w * c) = t w * y c := by
    simp only [MulAut.mul_apply, map_mul]
    rw [hyfix _ hw, htCfix _ hyc]
  rw [hL, hR]

theorem D2_11_4 [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X : Subgroup (MulAut V)} {t : MulAut V}
    (ht : t ∈ TInv X) : Subgroup.zpowers t ∈ Qset X := by
  obtain ⟨htX, ht1, ht2, htm⟩ := ht
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hA2 : IsA2 X (Subgroup.zpowers t) := by
    refine ⟨(Subgroup.zpowers_le).mpr htX, ?_, ?_, ?_⟩
    · intro h
      rw [Subgroup.zpowers_eq_bot] at h
      exact ht1 h
    · intro a ha b hb
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact ((Commute.refl t).zpow_zpow i j).eq
    · intro a ha
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
      simp [ht2]
  have hrk : rk (Subgroup.zpowers t) = 1 := by
    unfold rk
    rw [Nat.card_zpowers, hord]
    simp
  refine ⟨⟨hA2, ?_⟩, (isQuadratic_iff_commSeries_two _).mp (isQuadratic_zpowers hV ht2)⟩
  unfold rAV
  rw [hrk, rkIdx_fixV_zpowers]
  simpa using (by exact_mod_cast htm : ((rk (commV (Subgroup.zpowers t)) : ℚ)) ≤ 2)

end CFSG.Quasithin
