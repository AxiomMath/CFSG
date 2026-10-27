module

public import CFSG.Quasithin.Background.S1567W2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

section Abstract

variable {G : Type*} [Group G]


theorem irr_exclusion (V₀ X F : Subgroup G) (q e : G)
    (hVab : ∀ a ∈ V₀, ∀ b ∈ V₀, a * b = b * a)
    (hV2 : ∀ v ∈ V₀, v * v = 1)
    (hqV : ∀ v ∈ V₀, q * v * q⁻¹ ∈ V₀)
    (hXV : ∀ x ∈ X, ∀ v ∈ V₀, x * v * x⁻¹ ∈ V₀)
    (hq2 : ∀ v ∈ V₀, q * (q * v * q⁻¹) * q⁻¹ = v)
    (hXq : ∀ x ∈ X, ∀ v ∈ V₀, (x * q * x⁻¹) * v * (x * q * x⁻¹)⁻¹ = q * v * q⁻¹)
    (hFC : ∀ f ∈ F, (∀ x ∈ X, x * f = f * x) → f = 1)
    (heV : e ∈ V₀) (hf₀F : q * e * q⁻¹ * e⁻¹ ∈ F) (hf₀ : q * e * q⁻¹ * e⁻¹ ≠ 1)
    (hirr : ∀ U : Subgroup G, U ≤ V₀ → (∀ x ∈ X, ∀ u ∈ U, x * u * x⁻¹ ∈ U) →
      U ≤ Subgroup.centralizer (X : Set G) ∨
        ∀ v ∈ V₀, ∃ u ∈ U, u⁻¹ * v ∈ Subgroup.centralizer (X : Set G)) :
    False := by
  set n : G → G := fun v => q * v * q⁻¹ * v⁻¹ with hn
  have hn_mem : ∀ v ∈ V₀, n v ∈ V₀ := fun v hv =>
    V₀.mul_mem (hqV v hv) (V₀.inv_mem hv)
  have hn_mul : ∀ v ∈ V₀, ∀ w ∈ V₀, n (v * w) = n v * n w := by
    intro v hv w hw
    have h1 : (q * w * q⁻¹ * w⁻¹) * v⁻¹ = v⁻¹ * (q * w * q⁻¹ * w⁻¹) :=
      hVab _ (hn_mem w hw) _ (V₀.inv_mem hv)
    simp only [hn]
    calc q * (v * w) * q⁻¹ * (v * w)⁻¹
        = (q * v * q⁻¹) * ((q * w * q⁻¹ * w⁻¹) * v⁻¹) := by group
      _ = (q * v * q⁻¹) * (v⁻¹ * (q * w * q⁻¹ * w⁻¹)) := by rw [h1]
      _ = (q * v * q⁻¹ * v⁻¹) * (q * w * q⁻¹ * w⁻¹) := by group
  have hn_n : ∀ v ∈ V₀, n (n v) = 1 := by
    intro v hv
    have h1 : q * (n v) * q⁻¹ = (n v)⁻¹ := by
      have := hq2 v hv
      simp only [hn]
      calc q * (q * v * q⁻¹ * v⁻¹) * q⁻¹
          = (q * (q * v * q⁻¹) * q⁻¹) * (q * v⁻¹ * q⁻¹) := by group
        _ = v * (q * v * q⁻¹)⁻¹ := by rw [this]; group
        _ = (q * v * q⁻¹ * v⁻¹)⁻¹ := by group
    have h2 : n v * n v = 1 := hV2 _ (hn_mem v hv)
    have h3 : n (n v) = (n v)⁻¹ * (n v)⁻¹ := by
      show q * n v * q⁻¹ * (n v)⁻¹ = _
      rw [h1]
    rw [h3, ← mul_inv_rev, h2, inv_one]
  have hn_X : ∀ x ∈ X, ∀ v ∈ V₀, x * n v * x⁻¹ = n (x * v * x⁻¹) := by
    intro x hx v hv
    have h1 := hXq x hx (x * v * x⁻¹) (hXV x hx v hv)
    simp only [hn]
    calc x * (q * v * q⁻¹ * v⁻¹) * x⁻¹
        = ((x * q * x⁻¹) * (x * v * x⁻¹) * (x * q * x⁻¹)⁻¹) * (x * v * x⁻¹)⁻¹ := by group
      _ = (q * (x * v * x⁻¹) * q⁻¹) * (x * v * x⁻¹)⁻¹ := by rw [h1]
  set K : Subgroup G := V₀ ⊓ Subgroup.centralizer ({q} : Set G) with hK
  have hKn : ∀ v ∈ V₀, v ∈ K ↔ n v = 1 := by
    intro v hv
    simp only [hK, Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_singleton_iff,
      forall_eq, hn]
    constructor
    · rintro ⟨-, h⟩
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact h
    · intro h
      refine ⟨hv, ?_⟩
      have h' : q * v * q⁻¹ = v := by rwa [mul_inv_eq_one] at h
      calc q * v = (q * v * q⁻¹) * q := by group
        _ = v * q := by rw [h']
  have hKV : K ≤ V₀ := inf_le_left
  have hKX : ∀ x ∈ X, ∀ u ∈ K, x * u * x⁻¹ ∈ K := by
    intro x hx u hu
    have huV : u ∈ V₀ := hKV hu
    have hu1 : n u = 1 := (hKn u huV).1 hu
    have hxuV : x * u * x⁻¹ ∈ V₀ := hXV x hx u huV
    rw [hKn _ hxuV, ← hn_X x hx u huV, hu1]
    group
  have hf₀K : n e ∈ K := (hKn _ (hn_mem e heV)).2 (hn_n e heV)
  have hf₀C : n e ∉ Subgroup.centralizer (X : Set G) := fun h =>
    hf₀ (hFC _ hf₀F (fun x hx => Subgroup.mem_centralizer_iff.mp h x hx))
  rcases hirr K hKV hKX with h | h
  · exact hf₀C (h hf₀K)
  · obtain ⟨u, huK, hu⟩ := h e heV
    have huV : u ∈ V₀ := hKV huK
    have hc : u⁻¹ * e ∈ V₀ := V₀.mul_mem (V₀.inv_mem huV) heV
    have hnc : n (u⁻¹ * e) ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hcx : x * (u⁻¹ * e) = (u⁻¹ * e) * x := Subgroup.mem_centralizer_iff.mp hu x hx
      have h1 := hn_X x hx _ hc
      have h2 : x * (u⁻¹ * e) * x⁻¹ = u⁻¹ * e := by
        rw [hcx]; group
      rw [h2] at h1
      calc x * n (u⁻¹ * e) = (x * n (u⁻¹ * e) * x⁻¹) * x := by group
        _ = n (u⁻¹ * e) * x := by rw [h1]
    have hnu : n u = 1 := (hKn u huV).1 huK
    have : n e = n u * n (u⁻¹ * e) := by
      rw [← hn_mul u huV _ hc]
      congr 1
      group
    rw [hnu, one_mul] at this
    exact hf₀C (this ▸ hnc)



theorem mem_four_of_card_four {E : Subgroup G} (hE4 : Nat.card E = 4)
    (hE2 : ∀ x ∈ E, x * x = 1) (a b : G) (ha : a ∈ E) (hb : b ∈ E) (h1 : a ≠ 1) (h2 : b ≠ 1)
    (h3 : a ≠ b) : ∀ x ∈ E, x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  classical
  have hfin : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype E := Fintype.ofFinite E
  have hab1 : a * b ≠ 1 := by
    intro h
    have hb' : b = a := (eq_inv_of_mul_eq_one_right h).trans (inv_eq_of_mul_eq_one_right (hE2 a ha))
    exact h3 hb'.symm
  let A : E := ⟨a, ha⟩
  let B : E := ⟨b, hb⟩
  let AB : E := ⟨a * b, E.mul_mem ha hb⟩
  have hA1 : A ≠ 1 := fun h => h1 (congrArg Subtype.val h)
  have hB1 : B ≠ 1 := fun h => h2 (congrArg Subtype.val h)
  have hAB1 : AB ≠ 1 := fun h => hab1 (congrArg Subtype.val h)
  have hAB : A ≠ B := fun h => h3 (congrArg Subtype.val h)
  have hAAB : A ≠ AB := fun h => h2 (by
    have h' : a = a * b := congrArg Subtype.val h
    exact (mul_left_cancel (a := a) (by simpa using h' : a * 1 = a * b)).symm)
  have hBAB : B ≠ AB := fun h => h1 (by
    have h' : b = a * b := congrArg Subtype.val h
    exact (mul_right_cancel (b := b) (by simpa using h' : 1 * b = a * b)).symm)
  have hS4 : ({1, A, B, AB} : Finset E).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm hA1, Ne.symm hB1, Ne.symm hAB1]),
      Finset.card_insert_of_notMem (by simp [hAB, hAAB]),
      Finset.card_insert_of_notMem (by simp [hBAB]), Finset.card_singleton]
  have huniv : ({1, A, B, AB} : Finset E) = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [hS4, Fintype.card_eq_nat_card, hE4])
  intro x hx
  have hmem : (⟨x, hx⟩ : E) ∈ ({1, A, B, AB} : Finset E) := by rw [huniv]; exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))



theorem comm_of_sq_eq_one {E : Subgroup G} (hE2 : ∀ x ∈ E, x * x = 1) {x y : G} (hx : x ∈ E)
    (hy : y ∈ E) : x * y = y * x := by
  have h1 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_right (hE2 _ (E.mul_mem hx hy))
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hE2 x hx)
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hE2 y hy)
  rw [mul_inv_rev, hx', hy'] at h1
  exact h1.symm

theorem eq_one_of_fixed_of_order_three {E : Subgroup G} (hE4 : Nat.card E = 4)
    (hE2 : ∀ x ∈ E, x * x = 1) (y : G) (hyN : ∀ x ∈ E, y * x * y⁻¹ ∈ E)
    (hy3 : ∀ x ∈ E, y ^ 3 * x * (y ^ 3)⁻¹ = x) (hmove : ∃ e₀ ∈ E, y * e₀ * y⁻¹ ≠ e₀) :
    ∀ e ∈ E, y * e * y⁻¹ = e → e = 1 := by
  intro e he hfix
  by_contra hne
  obtain ⟨e₀, he₀, hmv⟩ := hmove
  have he₀1 : e₀ ≠ 1 := by
    rintro rfl
    exact hmv (by group)
  have hee₀ : e ≠ e₀ := by
    rintro rfl
    exact hmv hfix
  have hcases := mem_four_of_card_four hE4 hE2 e e₀ he he₀ hne he₀1 hee₀ (y * e₀ * y⁻¹) (hyN _ he₀)
  have hcomm := comm_of_sq_eq_one hE2 he he₀
  rcases hcases with h | h | h | h
  · apply he₀1
    have : e₀ = y⁻¹ * (y * e₀ * y⁻¹) * y := by group
    rw [this, h]; group
  · apply hee₀
    symm
    calc e₀ = y⁻¹ * (y * e₀ * y⁻¹) * y := by group
      _ = y⁻¹ * (y * e * y⁻¹) * y := by rw [h, hfix]
      _ = e := by group
  · exact hmv h
  ·
    have h3 := hy3 e₀ he₀
    rw [pow_three'] at h3
    have hee : e * e = 1 := hE2 e he
    have : y * y * y * e₀ * (y * y * y)⁻¹ = e * e₀ := by
      calc y * y * y * e₀ * (y * y * y)⁻¹ = y * (y * (y * e₀ * y⁻¹) * y⁻¹) * y⁻¹ := by group
        _ = y * (y * (e * e₀) * y⁻¹) * y⁻¹ := by rw [h]
        _ = y * ((y * e * y⁻¹) * (y * e₀ * y⁻¹)) * y⁻¹ := by group
        _ = y * (e * (e * e₀)) * y⁻¹ := by rw [hfix, h]
        _ = y * ((e * e) * e₀) * y⁻¹ := by group
        _ = y * e₀ * y⁻¹ := by rw [hee, one_mul]
        _ = e * e₀ := h
    rw [this] at h3
    apply hne
    have : e = e * e₀ * e₀⁻¹ := by group
    rw [this, h3]; group

theorem commutator_mem_of_card_two {E Z : Subgroup G} (hE4 : Nat.card E = 4)
    (hE2 : ∀ x ∈ E, x * x = 1) (hZE : Z ≤ E) (hZ2 : Nat.card Z = 2) (q : G)
    (hqN : ∀ x ∈ E, q * x * q⁻¹ ∈ E) (hqZ : ∀ z ∈ Z, q * z * q⁻¹ = z) (e : G) (he : e ∈ E)
    (hne : q * e * q⁻¹ * e⁻¹ ≠ 1) : q * e * q⁻¹ * e⁻¹ ∈ Z := by
  obtain ⟨z, hz1, huniq⟩ := (Nat.card_eq_two_iff' (1 : Z)).1 hZ2
  have hzE : (z : G) ∈ E := hZE z.2
  have hz1' : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  set g := q * e * q⁻¹ * e⁻¹ with hg
  have hgE : g ∈ E := E.mul_mem (hqN e he) (E.inv_mem he)
  by_contra hgZ
  have hgz : (z : G) ≠ g := fun h => hgZ (h ▸ z.2)
  have hg1 : g ≠ 1 := hne
  have hcases := mem_four_of_card_four hE4 hE2 (z : G) g hzE hgE hz1' hg1 hgz e he
  have hgg : g * g = 1 := hE2 g hgE
  have hqe : q * e * q⁻¹ = g * e := by rw [hg]; group
  have hconj : ∀ w : G, q * w * q⁻¹ = 1 → w = 1 := by
    intro w hw
    have : w = q⁻¹ * (q * w * q⁻¹) * q := by group
    rw [this, hw]; group
  rcases hcases with h | h | h | h
  · apply hg1
    rw [hg, h]; group
  · apply hne
    rw [hg, h, hqZ _ z.2]; group
  · apply hg1
    apply hconj
    rw [h] at hqe
    rw [hqe]
    exact hgg
  · apply hg1
    apply hconj
    have hz' : q * (z : G) * q⁻¹ = z := hqZ _ z.2
    have hcz : g * (z : G) = (z : G) * g := comm_of_sq_eq_one hE2 hgE hzE
    have h5 : q * (z * g) * q⁻¹ = z * (q * g * q⁻¹) := by
      calc q * (z * g) * q⁻¹ = (q * z * q⁻¹) * (q * g * q⁻¹) := by group
        _ = z * (q * g * q⁻¹) := by rw [hz']
    rw [h] at hqe
    have hh : z * (q * g * q⁻¹) = z := by
      rw [← h5, hqe]
      calc g * (z * g) = (g * z) * g := by group
        _ = (z * g) * g := by rw [hcz]
        _ = z * (g * g) := by group
        _ = z := by rw [hgg]; group
    exact (mul_eq_left.mp hh : q * g * q⁻¹ = 1)


end Abstract

section Setting

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

@[expose] def IrrShape153 (T Mc M E : Subgroup G) (s : G) : Prop :=
  ∀ U : Subgroup G, U ≤ V0_153 T Mc M E s →
    (∀ x ∈ thompsonJ (G0_153 T Mc M E s), ∀ u ∈ U, x * u * x⁻¹ ∈ U) →
    U ≤ Subgroup.centralizer (thompsonJ (G0_153 T Mc M E s) : Set G) ∨
      ∀ v ∈ V0_153 T Mc M E s, ∃ u ∈ U,
        u⁻¹ * v ∈ Subgroup.centralizer (thompsonJ (G0_153 T Mc M E s) : Set G)

theorem alpha153_eq_one_of_odd (h113 : StageLemma14113) (c : Ctx153 G T Mc M V₁ V₂ t)
    (L : LineData153 T M V₁ V₂ E) (r66 : Res15366B T Mc M V₁ V₂ E)
    (r68 : Res15368NoTwo T Mc M E s) {x : G} (hx : x ∈ G0_153 T Mc M E s)
    (hodd : Odd (orderOf x)) : S1567.alpha153 T Mc M E s r68.le_normalizer ⟨x, hx⟩ = 1 :=
  S1567.eq_one_of_odd_of_card_two (S1567.card_mulAut_quot_YE h113 c L r66) _
    (by rw [Subgroup.orderOf_mk]; exact hodd)

theorem alpha153_eq_one_of_mem_thompsonJ (c : Ctx153 G T Mc M V₁ V₂ t) (L : LineData153 T M V₁ V₂ E)
    (r66 : Res15366B T Mc M V₁ V₂ E) (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s)
    (r68 : Res15368NoTwo T Mc M E s) {x : G} (hx : x ∈ thompsonJ (G0_153 T Mc M E s)) :
    ∃ hxG : x ∈ G0_153 T Mc M E s, S1567.alpha153 T Mc M E s r68.le_normalizer ⟨x, hxG⟩ = 1 := by
  obtain ⟨y, hy, hyx⟩ := thompsonJ_G0_le_ker_alpha c L r66 r67 gl r68 hx
  subst hyx
  exact ⟨y.2, hy⟩

theorem exists_odd_y_eps (h113 : StageLemma14113) (c : Ctx153 G T Mc M V₁ V₂ t)
    (L : LineData153 T M V₁ V₂ E) :
    ∃ y ∈ YE153 Mc M E, ∃ m : ℕ, Odd m ∧ y ^ m = 1 ∧ (∀ x ∈ E, y * x * y⁻¹ ∈ E) ∧
      (∀ x ∈ E, y ^ 3 * x * (y ^ 3)⁻¹ = x) ∧ ∃ e₀ ∈ E, y * e₀ * y⁻¹ ≠ e₀ := by
  obtain ⟨y, hyY, hyN, hε1, hε3⟩ := S1567.exists_y_eps h113 c L
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hy3N : y ^ 3 ∈ Subgroup.normalizer (E : Set G) := (Subgroup.normalizer _).pow_mem hyN 3
  have hy3C : y ^ 3 ∈ Subgroup.centralizer (E : Set G) := by
    have e1 : conjAct E ⟨y, hyN⟩ ^ 3 = conjAct E ⟨y ^ 3, hy3N⟩ := by
      rw [← map_pow]
      rfl
    rw [e1, conjAct_eq_one_iff'''] at hε3
    exact hε3
  have hy₁N : y ^ 2 ^ k ∈ Subgroup.normalizer (E : Set G) := (Subgroup.normalizer _).pow_mem hyN _
  refine ⟨y ^ 2 ^ k, (YE153 Mc M E).pow_mem hyY _, m, hm, ?_, ?_, ?_, ?_⟩
  · rw [← pow_mul, ← hkm]
    exact pow_orderOf_eq_one y
  · intro x hx
    exact (Subgroup.mem_normalizer_iff.mp hy₁N x).mp hx
  · intro x hx
    have h3 : (y ^ 2 ^ k) ^ 3 ∈ Subgroup.centralizer (E : Set G) := by
      rw [← pow_mul, mul_comm, pow_mul]
      exact (Subgroup.centralizer _).pow_mem hy3C _
    have h := Subgroup.mem_centralizer_iff.mp h3 x hx
    calc (y ^ 2 ^ k) ^ 3 * x * ((y ^ 2 ^ k) ^ 3)⁻¹
        = x * (y ^ 2 ^ k) ^ 3 * ((y ^ 2 ^ k) ^ 3)⁻¹ := by rw [← h]
      _ = x := mul_inv_cancel_right _ _
  · by_contra hcon
    push Not at hcon
    have hC : y ^ 2 ^ k ∈ Subgroup.centralizer (E : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have h := hcon e he
      calc e * y ^ 2 ^ k = (y ^ 2 ^ k * e * (y ^ 2 ^ k)⁻¹) * y ^ 2 ^ k := by rw [h]
        _ = y ^ 2 ^ k * e := inv_mul_cancel_right _ _
    have h1 : conjAct E ⟨y ^ 2 ^ k, hy₁N⟩ = 1 := (conjAct_eq_one_iff''' E _).2 hC
    have e2 : conjAct E ⟨y ^ 2 ^ k, hy₁N⟩ = conjAct E ⟨y, hyN⟩ ^ 2 ^ k := by
      rw [← map_pow]
      rfl
    rw [e2] at h1
    have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    have h4 := pow_gcd_eq_one.2 ⟨h1, hε3⟩
    rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at h4
    exact hε1 h4

theorem exists_odd_y_F (h113 : StageLemma14113) (c : Ctx153 G T Mc M V₁ V₂ t)
    (L : LineData153 T M V₁ V₂ E) :
    ∃ y ∈ G0_153 T Mc M E s, ∃ m : ℕ, Odd m ∧ y ^ m = 1 ∧
      ∀ f ∈ FE153 E s, y * f * y⁻¹ = f → f = 1 := by
  obtain ⟨y₁, hy₁Y, m, hm, hym, hyN, hy3, e₀, he₀, hmv⟩ := exists_odd_y_eps h113 c L
  have hE2 : ∀ x ∈ E, x * x = 1 := fun x hx => by
    have := c.hyp.elemAbelian.2 x (L.le_V hx)
    rwa [pow_two] at this
  refine ⟨s⁻¹ * y₁ * s, ?_, m, hm, ?_, ?_⟩
  · have hyYF : s⁻¹ * y₁ * s ∈ YF153 Mc M E s := by
      rw [mem_conjSubgroup_iff]
      have : s * (s⁻¹ * y₁ * s) * s⁻¹ = y₁ := by group
      rw [this]
      exact hy₁Y
    exact Subgroup.mem_sup_left (Subgroup.mem_sup_left hyYF)
  · have := conj_pow (a := s⁻¹) (b := y₁) (i := m)
    simpa [hym] using this
  · intro f hf hfix
    have hef : s * f * s⁻¹ ∈ E := mem_conjSubgroup_iff.mp hf
    have hfix' : y₁ * (s * f * s⁻¹) * y₁⁻¹ = s * f * s⁻¹ := by
      calc y₁ * (s * f * s⁻¹) * y₁⁻¹
          = s * ((s⁻¹ * y₁ * s) * f * (s⁻¹ * y₁ * s)⁻¹) * s⁻¹ := by group
        _ = s * f * s⁻¹ := by rw [hfix]
    have h1 := eq_one_of_fixed_of_order_three L.card_eq hE2 y₁ hyN hy3 ⟨e₀, he₀, hmv⟩ _ hef hfix'
    have : f = s⁻¹ * (s * f * s⁻¹) * s := by group
    rw [this, h1]
    group

end Setting

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ E : Subgroup G} {t s : G}

theorem F_trivial_of_centralizes_J (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t)
    (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s) (r68 : Res15368NoTwo T Mc M E s)
    (hO2 : oTwoUpper (⊤ : Subgroup (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)))
      ≤ Xdot153 T Mc M E s) :
    ∀ f ∈ FE153 E s, (∀ x ∈ thompsonJ (G0_153 T Mc M E s), x * f = f * x) → f = 1 := by
  obtain ⟨y, hyG, m, hm, hym, hy⟩ := exists_odd_y_F (s := s) h113 k.c k.L
  intro f hf hcomm
  refine hy f hf ?_
  have hodd : Odd (orderOf y) := Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hym)
  have hodd' : Odd (orderOf (QuotientGroup.mk (⟨y, hyG⟩ : ↥(G0_153 T Mc M E s)) :
      ↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s))) := by
    refine Odd.of_dvd_nat (n := orderOf y) hodd ?_
    have := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)))
      (⟨y, hyG⟩ : ↥(G0_153 T Mc M E s))
    rwa [Subgroup.orderOf_mk] at this
  have hmem := hO2 (mem_oTwoUpper_of_odd (Subgroup.mem_top _) hodd')
  obtain ⟨x, hxX, hxy⟩ := mem_barQ.mp hmem
  have h1 : x⁻¹ * ⟨y, hyG⟩ ∈ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s) := QuotientGroup.eq.mp hxy
  have h2 : (x : G)⁻¹ * y ∈ pCoreOf 2 (G0_153 T Mc M E s) := by
    rw [r68.pCore_eq]
    exact ⟨x⁻¹ * ⟨y, hyG⟩, h1, by simp⟩
  have hcG : (x : G)⁻¹ * y ∈ G0_153 T Mc M E s :=
    (G0_153 T Mc M E s).mul_mem ((G0_153 T Mc M E s).inv_mem x.2) hyG
  obtain ⟨hxG', hαx⟩ := alpha153_eq_one_of_mem_thompsonJ k.c k.L k.r66 r67 gl r68 hxX
  have hαx' : S1567.alpha153 T Mc M E s r68.le_normalizer x = 1 := hαx
  have hαy := alpha153_eq_one_of_odd h113 k.c k.L k.r66 r68 hyG hodd
  have hαc : S1567.alpha153 T Mc M E s r68.le_normalizer ⟨(x : G)⁻¹ * y, hcG⟩ = 1 := by
    have e : (⟨(x : G)⁻¹ * y, hcG⟩ : ↥(G0_153 T Mc M E s)) = x⁻¹ * ⟨y, hyG⟩ := rfl
    rw [e, map_mul, map_inv, hαx', inv_one, one_mul, hαy]
  have hc := pCore_inf_ker_alpha_le_centralizer_V0 h113 k r67 gl r68 h2 hcG hαc
  have hfV0 : f ∈ V0_153 T Mc M E s := V_le_V0 (FE153_le_V k.c k.L gl hf)
  have hfc : f * ((x : G)⁻¹ * y) = ((x : G)⁻¹ * y) * f := Subgroup.mem_centralizer_iff.mp hc f hfV0
  have hcf : ((x : G)⁻¹ * y) * f * ((x : G)⁻¹ * y)⁻¹ = f := by
    rw [← hfc]
    group
  calc y * f * y⁻¹ = (x : G) * (((x : G)⁻¹ * y) * f * ((x : G)⁻¹ * y)⁻¹) * (x : G)⁻¹ := by group
    _ = (x : G) * f * (x : G)⁻¹ := by rw [hcf]
    _ = f := by rw [hcomm x hxX]; group

theorem commutator_mem_F (k : Ctx67 G T Mc M V₁ V₂ E t) (r67 : Res15367 T Mc M V₁ V₂ E)
    (gl : GoldLine153 T V₁ E s) (r68 : Res15368NoTwo T Mc M E s) {q e : G}
    (hq : q ∈ pCoreOf 2 (G0_153 T Mc M E s)) (he : e ∈ E) (hne : q * e * q⁻¹ * e⁻¹ ≠ 1) :
    q * e * q⁻¹ * e⁻¹ ∈ FE153 E s := by
  have hqT : q ∈ TE153 T E := S1567.pCore_G0_le_TE k.c k.L k.r66 r67 gl r68.triple hq
  have hqF : q ∈ Subgroup.centralizer (FE153 E s : Set G) :=
    S1567.pCore_G0_le_centralizer_F k.c k.L k.r66 r67 gl r68.triple hq
  have hqN : ∀ x ∈ E, q * x * q⁻¹ ∈ E := fun x hx => (Subgroup.mem_normalizer_iff.mp hqT.2 x).mp hx
  have hZ2 : Nat.card (quasithinOmegaOneCenter T) = 2 := k.c.hyp.lemma_15_3_2_two.2
  have hZF := Z_le_FE153B k.c k.r66 gl
  have hE2 : ∀ x ∈ E, x * x = 1 := fun x hx => by
    have := k.c.hyp.elemAbelian.2 x (k.L.le_V hx)
    rwa [pow_two] at this
  have hqZ : ∀ z ∈ quasithinOmegaOneCenter T, q * z * q⁻¹ = z := fun z hz => by
    have := Subgroup.mem_centralizer_iff.mp hqF z (hZF hz)
    calc q * z * q⁻¹ = (z * q) * q⁻¹ := by rw [this]
      _ = z := by group
  exact hZF (commutator_mem_of_card_two (E := E) (Z := quasithinOmegaOneCenter T) k.L.card_eq hE2
    k.r66.Z_le_E hZ2 q hqN hqZ e he hne)

theorem caseB_false_of_irr (h113 : StageLemma14113) (k : Ctx67 G T Mc M V₁ V₂ E t)
    (r67 : Res15367 T Mc M V₁ V₂ E) (gl : GoldLine153 T V₁ E s) (r68 : Res15368NoTwo T Mc M E s)
    (hO2 : oTwoUpper (⊤ : Subgroup (↥(G0_153 T Mc M E s) ⧸ CFSG.pPrimeCore 3 ↥(G0_153 T Mc M E s)))
      ≤ Xdot153 T Mc M E s)
    (hB : ¬ pCoreOf 2 (G0_153 T Mc M E s) ≤ Subgroup.centralizer (E : Set G))
    (hirr : IrrShape153 T Mc M E s) : False := by
  obtain ⟨q, hqQ, hqE⟩ : ∃ q ∈ pCoreOf 2 (G0_153 T Mc M E s),
      q ∉ Subgroup.centralizer (E : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hB hcon
  have hqG : q ∈ G0_153 T Mc M E s := pCoreOf_le 2 _ hqQ
  obtain ⟨e, heE, hne⟩ : ∃ e ∈ E, ¬ (e * q = q * e) := by
    by_contra hcon
    push Not at hcon
    exact hqE (Subgroup.mem_centralizer_iff.mpr hcon)
  have hf₀ : q * e * q⁻¹ * e⁻¹ ≠ 1 := fun h => by
    have h1 : q * e * q⁻¹ = e := mul_inv_eq_one.mp h
    apply hne
    calc e * q = (q * e * q⁻¹) * q := by rw [h1]
      _ = q * e := by group
  have hV0 : IsElemAbelian 2 (V0_153 T Mc M E s) :=
    isElemAbelian_V0_NoTwo k.c k.r46 k.L k.r66 r67 gl r68
  have hJG : thompsonJ (G0_153 T Mc M E s) ≤ G0_153 T Mc M E s := B6.thompsonJ_le _
  have hcard := S1567.card_mulAut_quot_YE h113 k.c k.L k.r66
  refine irr_exclusion (V0_153 T Mc M E s) (thompsonJ (G0_153 T Mc M E s)) (FE153 E s) q e
    (fun a ha b hb => by have := hV0.1; exact setLike_mul_comm ha hb)
    (fun v hv => by rw [← pow_two]; exact hV0.2 v hv)
    (fun v hv => (Subgroup.mem_normalizer_iff.mp (V0_normal hqG) v).mp hv)
    (fun x hx v hv => (Subgroup.mem_normalizer_iff.mp (V0_normal (hJG hx)) v).mp hv)
    ?_ ?_ (F_trivial_of_centralizes_J h113 k r67 gl r68 hO2)
    (V_le_V0 (k.L.le_V heE)) (commutator_mem_F k r67 gl r68 hqQ heE hf₀) hf₀ hirr
  ·
    intro v hv
    have hα2 : S1567.alpha153 T Mc M E s r68.le_normalizer
        ⟨q * q, (G0_153 T Mc M E s).mul_mem hqG hqG⟩ = 1 := by
      have e1 : (⟨q * q, (G0_153 T Mc M E s).mul_mem hqG hqG⟩ : ↥(G0_153 T Mc M E s)) =
          ⟨q, hqG⟩ * ⟨q, hqG⟩ := rfl
      have h2 := pow_card_eq_one' (x := S1567.alpha153 T Mc M E s r68.le_normalizer ⟨q, hqG⟩)
      rw [hcard, pow_two] at h2
      rw [e1, map_mul]
      exact h2
    have hc := pCore_inf_ker_alpha_le_centralizer_V0 h113 k r67 gl r68
      ((pCoreOf 2 (G0_153 T Mc M E s)).mul_mem hqQ hqQ) ((G0_153 T Mc M E s).mul_mem hqG hqG) hα2
    have hcv : v * (q * q) = (q * q) * v := Subgroup.mem_centralizer_iff.mp hc v hv
    calc q * (q * v * q⁻¹) * q⁻¹ = (q * q) * v * (q * q)⁻¹ := by group
      _ = v := by rw [← hcv]; group
  ·
    intro x hx v hv
    have hxG : x ∈ G0_153 T Mc M E s := hJG hx
    obtain ⟨hxG₂, hαx⟩ := alpha153_eq_one_of_mem_thompsonJ k.c k.L k.r66 r67 gl r68 hx
    have hαx' : S1567.alpha153 T Mc M E s r68.le_normalizer ⟨x, hxG⟩ = 1 := hαx
    have hq' : x * q * x⁻¹ ∈ pCoreOf 2 (G0_153 T Mc M E s) :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hxG) q).mp hqQ
    have hcQ : x * q * x⁻¹ * q⁻¹ ∈ pCoreOf 2 (G0_153 T Mc M E s) :=
      (pCoreOf 2 (G0_153 T Mc M E s)).mul_mem hq' ((pCoreOf 2 (G0_153 T Mc M E s)).inv_mem hqQ)
    have hcG : x * q * x⁻¹ * q⁻¹ ∈ G0_153 T Mc M E s := pCoreOf_le 2 _ hcQ
    have hαc : S1567.alpha153 T Mc M E s r68.le_normalizer ⟨x * q * x⁻¹ * q⁻¹, hcG⟩ = 1 := by
      have e1 : (⟨x * q * x⁻¹ * q⁻¹, hcG⟩ : ↥(G0_153 T Mc M E s)) =
          ⟨x, hxG⟩ * ⟨q, hqG⟩ * ⟨x, hxG⟩⁻¹ * ⟨q, hqG⟩⁻¹ := rfl
      rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, hαx', one_mul, inv_one, mul_one,
        mul_inv_cancel]
    have hc := pCore_inf_ker_alpha_le_centralizer_V0 h113 k r67 gl r68 hcQ hcG hαc
    have hw : q * v * q⁻¹ ∈ V0_153 T Mc M E s :=
      (Subgroup.mem_normalizer_iff.mp (V0_normal hqG) v).mp hv
    have hwc : (q * v * q⁻¹) * (x * q * x⁻¹ * q⁻¹) = (x * q * x⁻¹ * q⁻¹) * (q * v * q⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hc _ hw
    calc (x * q * x⁻¹) * v * (x * q * x⁻¹)⁻¹
        = (x * q * x⁻¹ * q⁻¹) * (q * v * q⁻¹) * (x * q * x⁻¹ * q⁻¹)⁻¹ := by group
      _ = q * v * q⁻¹ := by rw [← hwc]; group

end Main

end CFSG.Quasithin
