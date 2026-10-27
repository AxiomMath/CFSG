module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCaseZeroOrth

public section

namespace CFSG.StandardType

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V] {m : ℕ}

private lemma ggCZForm_root_u {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {i j : Fin m} (hij : i ≠ j) (ε : ZMod p) (u : V) :
    ggCZForm φ (e i - ε • e j) u = φ i u - ε * φ j u := by
  rw [ggCZForm]
  simp only [map_sub, map_smul, smul_eq_mul]
  have h : ∀ x, (φ x (e i) - ε * φ x (e j)) * φ x u =
      (if x = i then φ x u else 0) - ε * (if x = j then φ x u else 0) := by
    intro x
    rw [hd x i, hd x j]
    by_cases hxi : x = i
    · subst hxi
      by_cases hxj : x = j
      · subst hxj
        exact absurd rfl hij
      · simp [hxj]
    · by_cases hxj : x = j
      · subst hxj
        simp [hxi]
      · simp [hxi, hxj]
  simp only [h, Finset.sum_sub_distrib]
  rw [← Finset.mul_sum]
  rw [Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

private lemma ggCZ_t_involutive {φ : Fin m → Module.Dual (ZMod p) V} {u : V}
    {t : V ≃ₗ[ZMod p] V}
    (hB : ggCZForm φ u u ≠ 0)
    (htu : ∀ v, t v = v - (2 * ggCZForm φ v u / ggCZForm φ u u) • u) :
    ∀ v, t (t v) = v := by
  intro v
  have hQ : ggCZForm φ u u ≠ 0 := hB
  have hBt : ggCZForm φ (t v) u = - ggCZForm φ v u := by
    rw [htu v]
    calc
      ggCZForm φ (v - (2 * ggCZForm φ v u / ggCZForm φ u u) • u) u
          = ggCZForm φ v u - (2 * ggCZForm φ v u / ggCZForm φ u u) * ggCZForm φ u u := by
            rw [ggCZForm_sub_left, ggCZForm_smul_left]
      _ = ggCZForm φ v u - 2 * ggCZForm φ v u := by
            rw [div_mul_cancel₀ _ hQ]
      _ = - ggCZForm φ v u := by ring
  calc
    t (t v) = t v - (2 * ggCZForm φ (t v) u / ggCZForm φ u u) • u := by rw [htu]
    _ = (v - (2 * ggCZForm φ v u / ggCZForm φ u u) • u)
          - (2 * (- ggCZForm φ v u) / ggCZForm φ u u) • u := by rw [hBt, htu v]
    _ = v := by
          simp only [mul_neg, neg_div, neg_smul]
          abel

private lemma ggCZ_t_isom {φ : Fin m → Module.Dual (ZMod p) V} {u : V}
    {t : V ≃ₗ[ZMod p] V}
    (hB : ggCZForm φ u u ≠ 0)
    (htu : ∀ v, t v = v - (2 * ggCZForm φ v u / ggCZForm φ u u) • u) :
    ∀ v w, ggCZForm φ (t v) (t w) = ggCZForm φ v w := by
  intro v w
  have hQ : ggCZForm φ u u ≠ 0 := hB
  calc
    ggCZForm φ (t v) (t w)
        = ggCZForm φ (v - (2 * ggCZForm φ v u / ggCZForm φ u u) • u)
            (w - (2 * ggCZForm φ w u / ggCZForm φ u u) • u) := by rw [htu, htu]
    _ = ggCZForm φ v w := by
          rw [ggCZForm_sub_left]
          rw [ggCZForm_smul_left]
          rw [ggCZForm_sub_right]
          rw [ggCZForm_smul_right]
          rw [ggCZForm_sub_right]
          rw [ggCZForm_smul_right]
          rw [ggCZForm_comm u w]
          field_simp [hQ]
          ring

private lemma ggCZ_t_alpha_coord {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {i j : Fin m} (hij : i ≠ j) (ε : ZMod p) (u : V)
    {t : V ≃ₗ[ZMod p] V}
    (htu : ∀ v, t v = v - (2 * ggCZForm φ v u / ggCZForm φ u u) • u)
    (k : Fin m) :
    φ k (t (e i - ε • e j)) =
      (if k = i then 1 else 0) - ε * (if k = j then 1 else 0)
        - (2 * (φ i u - ε * φ j u) / ggCZForm φ u u) * φ k u := by
  rw [htu, ggCZForm_root_u hd hij ε u]
  simp only [map_sub, map_smul, smul_eq_mul, hd k i, hd k j]

private lemma ggCZ_image_root {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hd : GGCZDual e φ) {u : V}
    (hB : ggCZForm φ u u ≠ 0) {t : V ≃ₗ[ZMod p] V}
    (htu : ∀ v, t v = v - (2 * ggCZForm φ v u / ggCZForm φ u u) • u)
    (hN : ∀ r ∈ ggCZRD e φ, t * r * t⁻¹ ∈ ggCZRD e φ)
    {i j : Fin m} (hij : i ≠ j) {ε : ZMod p} (hε : ε = 1 ∨ ε = -1) :
    ∃ p q : Fin m, p ≠ q ∧ ∀ k : Fin m, k ≠ p → k ≠ q → φ k (t (e i - ε • e j)) = 0 := by
  let α := e i - ε • e j
  let f : V →ₗ[ZMod p] ZMod p := φ i - ε • φ j
  have hα : f α = 2 := by
    simp only [f, α, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, map_sub, map_smul,
      hd i i, hd i j, hd j i, hd j j, hij, Ne.symm hij, if_false, if_true]
    rcases hε with rfl | rfl <;> norm_num
  let rα : V ≃ₗ[ZMod p] V := Module.reflection hα
  have hrα : rα ∈ ggCZRD e φ := by
    refine ⟨i, j, hij, ε, hε, fun v => ?_⟩
    rw [Module.reflection_apply v hα]
    rfl
  obtain ⟨p, q, hpq, δ, hδ, hβ⟩ := hN rα hrα
  have ht_inv : t⁻¹ = t := by
    ext v
    show t.symm v = t v
    rw [LinearEquiv.symm_apply_eq]
    exact (ggCZ_t_involutive hB htu v).symm
  have hconj : ∀ v, (t * rα * t⁻¹) v = v - ggCZForm φ v (t α) • t α := by
    intro v
    rw [ht_inv]
    simp only [LinearEquiv.mul_apply]
    rw [Module.reflection_apply (t v) hα]
    rw [map_sub, map_smul]
    rw [ggCZ_t_involutive hB htu v]
    have hft : f (t v) = ggCZForm φ v (t α) := by
      have h1 : f (t v) = ggCZForm φ (t v) α := by
        simp only [f, α, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
        rw [ggCZForm_comm (t v) α]
        rw [ggCZForm_root_u hd hij ε (t v)]
      have h2 : ggCZForm φ (t v) α = ggCZForm φ v (t α) := by
        have hisom := ggCZ_t_isom hB htu v (t⁻¹ α)
        have hsymm : t (t⁻¹ α) = α := by
          change t (t.symm α) = α
          exact t.apply_symm_apply α
        rw [hsymm] at hisom
        rw [ht_inv] at hisom
        exact hisom
      rw [h1, h2]
    rw [hft]
  have heq : ∀ v, ggCZForm φ v (t α) • t α =
      (φ p v - δ * φ q v) • (e p - δ • e q) := by
    intro v
    have h1 := hconj v
    have h2 := hβ v
    rw [h2] at h1
    exact sub_right_inj.mp h1.symm
  have hα_ne : α ≠ 0 := by
    intro h
    have h1 : φ i α = φ i 0 := by rw [h]
    rw [map_zero] at h1
    simp only [α, map_sub, map_smul, smul_eq_mul, hd i i, hd i j, hij, if_false, if_true,
      mul_zero, sub_zero] at h1
    exact one_ne_zero h1
  have htα_ne : t α ≠ 0 := by
    intro h
    have := congrArg t.symm h
    rw [LinearEquiv.symm_apply_apply, map_zero] at this
    exact hα_ne this
  refine ⟨p, q, hpq, fun k hkp hkq => ?_⟩
  have h := heq (e k)
  rw [ggCZForm_e_apply hd k (t α), hd p k, hd q k, if_neg (Ne.symm hkp),
    if_neg (Ne.symm hkq)] at h
  simp only [mul_zero, sub_zero, zero_smul] at h
  exact (smul_eq_zero.mp h).resolve_right htα_ne

private lemma ggCZ_three_coords_contra {φ : Fin m → Module.Dual (ZMod p) V}
    {t : V ≃ₗ[ZMod p] V} {α : V}
    {p q : Fin m} (hpq : p ≠ q)
    (hzero : ∀ k : Fin m, k ≠ p → k ≠ q → φ k (t α) = 0)
    {a b c : Fin m} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : φ a (t α) ≠ 0)
    (hb : φ b (t α) ≠ 0)
    (hc : φ c (t α) ≠ 0) : False := by
  have h_nonzero : ∀ x ∈ ({a, b, c} : Finset (Fin m)), φ x (t α) ≠ 0 := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have h_subset : ({a, b, c} : Finset (Fin m)) ⊆ {p, q} := by
    intro x hx
    by_contra hx'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx'
    push Not at hx'
    exact h_nonzero x hx (hzero x hx'.1 hx'.2)
  have h_card : ({a, b, c} : Finset (Fin m)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · intro h
      exact hbc (Finset.mem_singleton.mp h)
    · intro h
      rcases Finset.mem_insert.mp h with h | h
      · exact hab h
      · exact hac (Finset.mem_singleton.mp h)
  have hpq_card : ({p, q} : Finset (Fin m)).card = 2 := by
    rw [Finset.card_insert_of_notMem, Finset.card_singleton]
    simp [hpq]
  have := Finset.card_le_card h_subset
  omega

private lemma ggCZ_coord_ne_zero {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hp2 : p ≠ 2) (hd : GGCZDual e φ) {u : V} (hB : ggCZForm φ u u ≠ 0)
    {t : V ≃ₗ[ZMod p] V}
    (htu : ∀ v, t v = v - (2 * ggCZForm φ v u / ggCZForm φ u u) • u)
    {i j k : Fin m} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) {ε : ZMod p}
    (hne : φ i u ≠ ε * φ j u) (hk : φ k u ≠ 0) :
    φ k (t (e i - ε • e j)) ≠ 0 := by
  rw [ggCZ_t_alpha_coord hd hij ε u htu k]
  rw [if_neg hki, if_neg hkj]
  simp only [mul_zero, zero_sub, sub_zero]
  have hc : 2 * (φ i u - ε * φ j u) / ggCZForm φ u u ≠ 0 := by
    rw [div_eq_mul_inv]
    exact mul_ne_zero (mul_ne_zero (zmod_two_ne_zero hp2) (sub_ne_zero.mpr hne)) (inv_ne_zero hB)
  exact neg_ne_zero.mpr (mul_ne_zero hc hk)

private lemma ggCZ_t_of_scale {φ : Fin m → Module.Dual (ZMod p) V} {u w : V} {a N : ZMod p}
    (ha : a ≠ 0) (hN : N ≠ 0) {t : V ≃ₗ[ZMod p] V}
    (htu : ∀ v, t v = v - (2 * ggCZForm φ v u / ggCZForm φ u u) • u)
    (huw : u = a • w) (hQ : ggCZForm φ u u = a ^ 2 * N) {L : V → ZMod p}
    (hL : ∀ v, ggCZForm φ v u = a * L v) (v : V) :
    t v = v - (2 * L v / N) • w := by
  rw [htu v, hL v, hQ, huw, smul_smul]
  congr 2
  field_simp

private lemma ggCZ_poly_or {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hp2 : p ≠ 2) (hd : GGCZDual e φ) {u : V}
    (hB : ggCZForm φ u u ≠ 0) {t : V ≃ₗ[ZMod p] V}
    (htu : ∀ v, t v = v - (2 * ggCZForm φ v u / ggCZForm φ u u) • u)
    (hN : ∀ r ∈ ggCZRD e φ, t * r * t⁻¹ ∈ ggCZRD e φ)
    {i j k : Fin m} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) {ε : ZMod p}
    (hε : ε = 1 ∨ ε = -1) (hne : φ i u ≠ ε * φ j u) (hk : φ k u ≠ 0) :
    ggCZForm φ u u = 2 * (φ i u - ε * φ j u) * φ i u ∨
      -ε * ggCZForm φ u u = 2 * (φ i u - ε * φ j u) * φ j u := by
  have hQ : ggCZForm φ u u * (ggCZForm φ u u)⁻¹ = 1 := mul_inv_cancel₀ hB
  obtain ⟨p', q', hpq, hz⟩ := ggCZ_image_root hd hB htu hN hij hε
  have hck := ggCZ_coord_ne_zero hp2 hd hB htu hij hki hkj hne hk
  by_cases hi : φ i (t (e i - ε • e j)) = 0
  · left
    rw [ggCZ_t_alpha_coord hd hij ε u htu i, if_pos rfl, if_neg hij] at hi
    linear_combination ggCZForm φ u u * hi + 2 * (φ i u - ε * φ j u) * φ i u * hQ
  · right
    have hj : φ j (t (e i - ε • e j)) = 0 := by
      by_contra hj
      exact ggCZ_three_coords_contra hpq hz hij hki.symm hkj.symm hi hj hck
    rw [ggCZ_t_alpha_coord hd hij ε u htu j, if_neg hij.symm, if_pos rfl] at hj
    linear_combination ggCZForm φ u u * hj + 2 * (φ i u - ε * φ j u) * φ j u * hQ

private lemma ggCZ_pm_of_two_out {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hp2 : p ≠ 2) (hd : GGCZDual e φ) {u : V}
    (hB : ggCZForm φ u u ≠ 0) {t : V ≃ₗ[ZMod p] V}
    (htu : ∀ v, t v = v - (2 * ggCZForm φ v u / ggCZForm φ u u) • u)
    (hN : ∀ r ∈ ggCZRD e φ, t * r * t⁻¹ ∈ ggCZRD e φ)
    {i l a b : Fin m} (hil : i ≠ l) (hab : a ≠ b) (hai : a ≠ i) (hal : a ≠ l) (hbi : b ≠ i)
    (hbl : b ≠ l) (ha : φ a u ≠ 0) (hb : φ b u ≠ 0) :
    φ l u = φ i u ∨ φ l u = -φ i u := by
  by_cases hne : φ i u = 1 * φ l u
  · left
    linear_combination -hne
  right
  obtain ⟨p', q', hpq, hz⟩ := ggCZ_image_root hd hB htu hN hil (ε := 1) (Or.inl rfl)
  have hca := ggCZ_coord_ne_zero hp2 hd hB htu hil hai hal hne ha
  have hcb := ggCZ_coord_ne_zero hp2 hd hB htu hil hbi hbl hne hb
  have hci : φ i (t (e i - (1 : ZMod p) • e l)) = 0 := by
    by_contra h
    exact ggCZ_three_coords_contra hpq hz hai.symm hbi.symm hab h hca hcb
  have hcl : φ l (t (e i - (1 : ZMod p) • e l)) = 0 := by
    by_contra h
    exact ggCZ_three_coords_contra hpq hz hal.symm hbl.symm hab h hca hcb
  rw [ggCZ_t_alpha_coord hd hil 1 u htu i, if_pos rfl, if_neg hil] at hci
  rw [ggCZ_t_alpha_coord hd hil 1 u htu l, if_neg hil.symm, if_pos rfl] at hcl
  have hc0 : 2 * (φ i u - 1 * φ l u) / ggCZForm φ u u ≠ 0 :=
    div_ne_zero (mul_ne_zero (zmod_two_ne_zero hp2) (sub_ne_zero.mpr hne)) hB
  have hsum : 2 * (φ i u - 1 * φ l u) / ggCZForm φ u u * (φ i u + φ l u) = 0 := by
    linear_combination -hci - hcl
  linear_combination (mul_eq_zero.mp hsum).resolve_left hc0

private lemma ggCZ_pm_of_three {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hp2 : p ≠ 2) (hd : GGCZDual e φ) {u : V}
    (hB : ggCZForm φ u u ≠ 0) {t : V ≃ₗ[ZMod p] V}
    (htu : ∀ v, t v = v - (2 * ggCZForm φ v u / ggCZForm φ u u) • u)
    (hN : ∀ r ∈ ggCZRD e φ, t * r * t⁻¹ ∈ ggCZRD e φ)
    {i j k : Fin m} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) (hi : φ i u ≠ 0)
    (hj : φ j u ≠ 0) (hk : φ k u ≠ 0)
    (hQ : ggCZForm φ u u = φ i u * φ i u + φ j u * φ j u + φ k u * φ k u) :
    φ j u = φ i u ∨ φ j u = -φ i u := by
  have h2 := zmod_two_ne_zero hp2
  by_contra hcon
  push Not at hcon
  have hne1 : φ i u ≠ 1 * φ j u := fun h => hcon.1 (by linear_combination -h)
  have hne2 : φ i u ≠ -1 * φ j u := fun h => hcon.2 (by linear_combination h)
  have hab : φ i u * φ j u ≠ 0 := mul_ne_zero hi hj
  have hcc : φ k u * φ k u ≠ 0 := mul_ne_zero hk hk
  rcases ggCZ_poly_or hp2 hd hB htu hN hij hki hkj (Or.inl rfl) hne1 hk with A1 | B1 <;>
    rcases ggCZ_poly_or hp2 hd hB htu hN hij hki hkj (Or.inr rfl) hne2 hk with A2 | B2
  · exact mul_ne_zero (mul_ne_zero h2 h2) hab (by linear_combination A1 - A2)
  · exact mul_ne_zero h2 hcc (by linear_combination A1 + B2 - 2 * hQ)
  · exact mul_ne_zero h2 hcc (by linear_combination -B1 + A2 - 2 * hQ)
  · exact mul_ne_zero (mul_ne_zero h2 h2) hab (by linear_combination -B1 - B2)

private lemma ggCZ_Q_four {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hp2 : p ≠ 2) (hd : GGCZDual e φ) {u : V}
    (hB : ggCZForm φ u u ≠ 0) {t : V ≃ₗ[ZMod p] V}
    (htu : ∀ v, t v = v - (2 * ggCZForm φ v u / ggCZForm φ u u) • u)
    (hN : ∀ r ∈ ggCZRD e φ, t * r * t⁻¹ ∈ ggCZRD e φ)
    {i j k : Fin m} (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) {ε : ZMod p}
    (hε : ε = 1 ∨ ε = -1) (hi : φ i u ≠ 0) (hεj : ε * φ j u = -φ i u) (hk : φ k u ≠ 0) :
    ggCZForm φ u u = 4 * (φ i u * φ i u) := by
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hne : φ i u ≠ ε * φ j u := by
    rw [hεj]
    intro h
    exact mul_ne_zero (zmod_two_ne_zero hp2) hi (by linear_combination h)
  rcases ggCZ_poly_or hp2 hd hB htu hN hij hki hkj hε hne hk with A | B
  · linear_combination A - 2 * φ i u * hεj
  · linear_combination -ε * B - ggCZForm φ u u * hε2 + 2 * (ε * φ j u - 2 * φ i u) * hεj

private lemma ggCZ_mem_RD_of_two {e : Fin m → V} {φ : Fin m → Module.Dual (ZMod p) V}
    (hp2 : p ≠ 2) {u : V} (hu : u = ∑ k, φ k u • e k) {t : V ≃ₗ[ZMod p] V}
    (htu : ∀ v, t v = v - (2 * ggCZForm φ v u / ggCZForm φ u u) • u)
    {i j : Fin m} (hij : i ≠ j) (hzero : ∀ l, l ≠ i → l ≠ j → φ l u = 0) (hi : φ i u ≠ 0)
    {ε : ZMod p} (hε : ε = 1 ∨ ε = -1) (huj : φ j u = -ε * φ i u) :
    t ∈ ggCZRD e φ := by
  have h2 := zmod_two_ne_zero hp2
  have hε2 : ε * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have hL : ∀ v, ggCZForm φ v u = φ i u * (φ i v - ε * φ j v) := by
    intro v
    have h : ∑ k, φ k v * φ k u = φ i v * φ i u + φ j v * φ j u :=
      Fintype.sum_eq_add i j hij fun l hl => by rw [hzero l hl.1 hl.2, mul_zero]
    rw [ggCZForm, h, huj]
    ring
  have hQ : ggCZForm φ u u = φ i u ^ 2 * 2 := by
    rw [hL u, huj]
    linear_combination φ i u ^ 2 * hε2
  have hw : u = φ i u • (e i - ε • e j) := by
    have h : ∑ k, φ k u • e k = φ i u • e i + φ j u • e j :=
      Fintype.sum_eq_add i j hij fun l hl => by rw [hzero l hl.1 hl.2, zero_smul]
    calc u = ∑ k, φ k u • e k := hu
      _ = φ i u • e i + φ j u • e j := h
      _ = φ i u • (e i - ε • e j) := by
        rw [huj]
        module
  refine ⟨i, j, hij, ε, hε, fun v => ?_⟩
  rw [ggCZ_t_of_scale hi h2 htu hw hQ hL v, mul_div_cancel_left₀ _ h2]

theorem ggCZ_core_classify (hp2 : p ≠ 2) (hm : 3 ≤ m) {e : Fin m → V}
    {φ : Fin m → Module.Dual (ZMod p) V} (hd : GGCZDual e φ) {u : V}
    (hu : u = ∑ k, φ k u • e k) (hB : ggCZForm φ u u ≠ 0) {t : V ≃ₗ[ZMod p] V}
    (htu : ∀ v, t v = v - (2 * ggCZForm φ v u / ggCZForm φ u u) • u)
    (hN : ∀ r ∈ ggCZRD e φ, t * r * t⁻¹ ∈ ggCZRD e φ) :
    t ∈ ggCZRD e φ ∨ t ∈ ggCZS e φ ∨ (m = 4 ∧ t ∈ ggCZH e φ) := by
  by_cases hsupp : ∃ k : Fin m, φ k u = 0
  ·
    obtain ⟨k, hk⟩ := hsupp
    have hs_le_two : ∀ i j l : Fin m, i ≠ j → i ≠ l → j ≠ l →
        φ i u = 0 ∨ φ j u = 0 ∨ φ l u = 0 := by
      intro i j l hij hil hjl
      by_contra h
      push Not at h
      obtain ⟨hi, hj, hl⟩ := h
      have hik : i ≠ k := by rintro rfl; exact hi hk
      have hjk : j ≠ k := by rintro rfl; exact hj hk
      have hlk : l ≠ k := by rintro rfl; exact hl hk
      obtain ⟨p, q, hpq, hzero⟩ := ggCZ_image_root hd hB htu hN hik (ε := 1) (Or.inl rfl)
      have hj_coord : φ j (t (e i - e k)) ≠ 0 := by
        have h := ggCZ_coord_ne_zero hp2 hd hB htu hik hij.symm hjk (ε := 1)
          (by simpa [hk] using hi) hj
        simpa using h
      have hl_coord : φ l (t (e i - e k)) ≠ 0 := by
        have h := ggCZ_coord_ne_zero hp2 hd hB htu hik hil.symm hlk (ε := 1)
          (by simpa [hk] using hi) hl
        simpa using h
      have hk_coord : φ k (t (e i - e k)) ≠ 0 := by
        have h := ggCZ_t_alpha_coord hd hik 1 u htu k
        rw [if_neg hik.symm, if_pos rfl, hk, one_smul] at h
        rw [h]
        simp
      have hzero' : ∀ l : Fin m, l ≠ p → l ≠ q → φ l (t (e i - e k)) = 0 := by
        intro l hlp hlq
        simpa using hzero l hlp hlq
      exact ggCZ_three_coords_contra hpq hzero' hjl hjk hlk hj_coord hl_coord hk_coord
    have hex : ∃ i : Fin m, φ i u ≠ 0 := by
      by_contra h
      push Not at h
      have : u = 0 := by
        rw [hu]
        simp [h]
      rw [this] at hB
      simp [ggCZForm] at hB
    obtain ⟨i, hi⟩ := hex
    by_cases h2 : ∃ j : Fin m, j ≠ i ∧ φ j u ≠ 0
    ·
      obtain ⟨j, hji, hj⟩ := h2
      have hk_zero : ∀ l : Fin m, l ≠ i → l ≠ j → φ l u = 0 := by
        intro l hli hlj
        by_contra hl
        have hil : i ≠ l := fun h => hli h.symm
        have hjl : j ≠ l := fun h => hlj h.symm
        have hij : i ≠ j := fun h => hji h.symm
        have := hs_le_two i j l hij hil hjl
        tauto
      have hij : i ≠ j := fun h => hji h.symm
      have hki : k ≠ i := fun h => hi (h ▸ hk)
      have hkj : k ≠ j := fun h => hj (h ▸ hk)
      have hQ2 : ggCZForm φ u u = φ i u * φ i u + φ j u * φ j u :=
        Fintype.sum_eq_add i j hij fun l hl => by rw [hk_zero l hl.1 hl.2, mul_zero]
      have hQi : ggCZForm φ u u = 2 * (φ i u * φ i u) := by
        rcases ggCZ_poly_or hp2 hd hB htu hN hki.symm hji hkj.symm (ε := 1) (Or.inl rfl)
          (by rw [hk, mul_zero]; exact hi) hj with A | A
        · linear_combination A - 2 * φ i u * hk
        · exact (hB (by linear_combination -A - 2 * (φ i u - 1 * φ k u) * hk)).elim
      have hsq : (φ j u - φ i u) * (φ j u + φ i u) = 0 := by linear_combination hQi - hQ2
      left
      rcases mul_eq_zero.mp hsq with h | h
      · exact ggCZ_mem_RD_of_two hp2 hu htu hij hk_zero hi (Or.inr rfl) (by linear_combination h)
      · exact ggCZ_mem_RD_of_two hp2 hu htu hij hk_zero hi (Or.inl rfl) (by linear_combination h)
    ·
      push Not at h2
      right; left
      refine ⟨i, fun v => ?_⟩
      rw [htu v]
      have hu_i : u = φ i u • e i := by
        rw [hu]
        rw [Finset.sum_eq_single i]
        · simp [hd i i]
        · intro b _ hbi
          rw [h2 b hbi, zero_smul]
        · intro hi_not_mem
          simp at hi_not_mem
      have hBv : ggCZForm φ v ((φ i u) • e i) = (φ i u) * φ i v := by
        rw [ggCZForm_smul_right, ggCZForm_comm v (e i), ggCZForm_e_apply hd i v]
      have hBu : ggCZForm φ ((φ i u) • e i) ((φ i u) • e i) = (φ i u)^2 := by
        rw [ggCZForm_smul_left, ggCZForm_smul_right, ggCZForm_e_apply hd i (e i), hd i i,
          if_pos rfl]
        ring
      rw [hu_i, hBv, hBu, smul_smul]
      congr 2
      rw [div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 hi)]
      ring
  ·
    push Not at hsupp
    have hm5 : ∀ (h : 5 ≤ m), False := by
      intro h5
      let i : Fin m := ⟨0, by omega⟩
      let j : Fin m := ⟨1, by omega⟩
      let a : Fin m := ⟨2, by omega⟩
      let b : Fin m := ⟨3, by omega⟩
      let c : Fin m := ⟨4, by omega⟩
      have hij : i ≠ j := by simp [i, j]
      have hia : i ≠ a := by simp [i, a]
      have hib : i ≠ b := by simp [i, b]
      have hic : i ≠ c := by simp [i, c]
      have hja : j ≠ a := by simp [j, a]
      have hjb : j ≠ b := by simp [j, b]
      have hjc : j ≠ c := by simp [j, c]
      have hab : a ≠ b := by simp [a, b]
      have hac : a ≠ c := by simp [a, c]
      have hbc : b ≠ c := by simp [b, c]
      have h_eq : φ i u = φ j u := by
        by_contra hne
        have hne' : φ i u ≠ 1 * φ j u := by rwa [one_mul]
        obtain ⟨p', q', hpq, hzero⟩ := ggCZ_image_root hd hB htu hN hij (ε := 1) (Or.inl rfl)
        exact ggCZ_three_coords_contra hpq hzero hab hac hbc
          (ggCZ_coord_ne_zero hp2 hd hB htu hij hia.symm hja.symm hne' (hsupp a))
          (ggCZ_coord_ne_zero hp2 hd hB htu hij hib.symm hjb.symm hne' (hsupp b))
          (ggCZ_coord_ne_zero hp2 hd hB htu hij hic.symm hjc.symm hne' (hsupp c))
      have h_neg : φ i u = -φ j u := by
        by_contra hne
        have hne' : φ i u ≠ -1 * φ j u := by rwa [neg_one_mul]
        obtain ⟨p', q', hpq, hzero⟩ :=
          ggCZ_image_root hd hB htu hN hij (ε := -1) (Or.inr rfl)
        exact ggCZ_three_coords_contra hpq hzero hab hac hbc
          (ggCZ_coord_ne_zero hp2 hd hB htu hij hia.symm hja.symm hne' (hsupp a))
          (ggCZ_coord_ne_zero hp2 hd hB htu hij hib.symm hjb.symm hne' (hsupp b))
          (ggCZ_coord_ne_zero hp2 hd hB htu hij hic.symm hjc.symm hne' (hsupp c))
      exact mul_ne_zero (zmod_two_ne_zero hp2) (hsupp j) (by linear_combination h_neg - h_eq)
    by_cases h5 : 5 ≤ m
    · exact absurd h5 hm5
    ·
      have hm4 : m ≤ 4 := by omega
      interval_cases m
      ·
        exfalso
        have hQ3 : ggCZForm φ u u = φ 0 u * φ 0 u + φ 1 u * φ 1 u + φ 2 u * φ 2 u := by
          rw [ggCZForm, Fin.sum_univ_three]
        have hb := ggCZ_pm_of_three hp2 hd hB htu hN (i := 0) (j := 1) (k := 2) (by decide)
          (by decide) (by decide) (hsupp 0) (hsupp 1) (hsupp 2) hQ3
        have hc := ggCZ_pm_of_three hp2 hd hB htu hN (i := 0) (j := 2) (k := 1) (by decide)
          (by decide) (by decide) (hsupp 0) (hsupp 2) (hsupp 1) (by rw [hQ3]; ring)
        obtain ⟨ε, hε, hεj⟩ : ∃ ε : ZMod p, (ε = 1 ∨ ε = -1) ∧ ε * φ 1 u = -φ 0 u := by
          rcases hb with hb | hb
          · exact ⟨-1, Or.inr rfl, by linear_combination -hb⟩
          · exact ⟨1, Or.inl rfl, by linear_combination hb⟩
        have hQ4 := ggCZ_Q_four hp2 hd hB htu hN (i := 0) (j := 1) (k := 2) (by decide)
          (by decide) (by decide) hε (hsupp 0) hεj (hsupp 2)
        have hb2 : φ 1 u * φ 1 u = φ 0 u * φ 0 u := by
          rcases hb with h | h
          · linear_combination (φ 1 u + φ 0 u) * h
          · linear_combination (φ 1 u - φ 0 u) * h
        have hc2 : φ 2 u * φ 2 u = φ 0 u * φ 0 u := by
          rcases hc with h | h
          · linear_combination (φ 2 u + φ 0 u) * h
          · linear_combination (φ 2 u - φ 0 u) * h
        exact mul_ne_zero (hsupp 0) (hsupp 0) (by linear_combination hQ3 - hQ4 + hb2 + hc2)
      ·
        right; right
        have h2 := zmod_two_ne_zero hp2
        have h4 : (4 : ZMod p) ≠ 0 := by
          have h22 : (4 : ZMod p) = 2 * 2 := by norm_num
          rw [h22]
          exact mul_ne_zero h2 h2
        have hex : ∀ l : Fin 4, l ≠ 0 →
            ∃ a b : Fin 4, a ≠ b ∧ a ≠ 0 ∧ a ≠ l ∧ b ≠ 0 ∧ b ≠ l := by decide
        have hsign : ∀ l : Fin 4, ∃ s : ZMod p, (s = 1 ∨ s = -1) ∧ φ l u = s * φ 0 u := by
          intro l
          have hpm : φ l u = φ 0 u ∨ φ l u = -φ 0 u := by
            by_cases hl : l = 0
            · exact Or.inl (by rw [hl])
            · obtain ⟨a, b, hab, ha0, hal, hb0, hbl⟩ := hex l hl
              exact ggCZ_pm_of_two_out hp2 hd hB htu hN (Ne.symm hl) hab ha0 hal hb0 hbl
                (hsupp a) (hsupp b)
          rcases hpm with h | h
          · exact ⟨1, Or.inl rfl, by linear_combination h⟩
          · exact ⟨-1, Or.inr rfl, by linear_combination h⟩
        choose w hw hwu using hsign
        have hsq : ∀ k, w k * w k = 1 := fun k => by rcases hw k with h | h <;> simp [h]
        have hu' : u = φ 0 u • ∑ k, w k • e k := by
          calc u = ∑ k, φ k u • e k := hu
            _ = φ 0 u • ∑ k, w k • e k := by
              rw [Finset.smul_sum]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [smul_smul, hwu k, mul_comm (w k)]
        have hL : ∀ v, ggCZForm φ v u = φ 0 u * ∑ k, w k * φ k v := by
          intro v
          rw [ggCZForm, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hwu k]
          ring
        have hQ : ggCZForm φ u u = φ 0 u ^ 2 * 4 := by
          rw [hL u, Fin.sum_univ_four, hwu 1, hwu 2, hwu 3]
          linear_combination (-φ 0 u) * hwu 0 + φ 0 u ^ 2 * (hsq 1 + hsq 2 + hsq 3)
        refine ⟨rfl, w, hw, fun v => ?_⟩
        rw [ggCZ_t_of_scale (hsupp 0) h4 htu hu' hQ hL v]
        congr 2
        field_simp
        ring

theorem ggCZ_core [Finite V] (hp2 : p ≠ 2) (hm : 3 ≤ m) {e : Fin m → V}
    {φ : Fin m → Module.Dual (ZMod p) V} (hd : GGCZDual e φ) {t : V ≃ₗ[ZMod p] V}
    (ht : GGLinRefl t) (hC : ∀ v, (∀ k, φ k v = 0) → t v = v)
    (hN : ∀ r ∈ ggCZRD e φ, t * r * t⁻¹ ∈ ggCZRD e φ) :
    t ∈ ggCZRD e φ ∨ t ∈ ggCZS e φ ∨ (m = 4 ∧ t ∈ ggCZH e φ) := by
  obtain ⟨u, hu, hB, htu⟩ := ggCZ_core_orth hp2 hm hd ht hC hN
  exact ggCZ_core_classify hp2 hm hd hu hB htu hN

end

end CFSG.StandardType

end
