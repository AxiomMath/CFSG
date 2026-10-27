module

public import CFSG.Quasithin.Background.JonesParshallG2Module

public section

namespace CFSG.Quasithin.G11.SzG11S.Two

open CFSG.Quasithin.JonesParshall CFSG.Quasithin.Explicit CFSG.Open

@[expose] def stabU0 (K : Type) [Field K] [CharP K 2] : Subgroup ↥(cayleyGroup K) where
  carrier := {g | cgE g (zU0 K) = zU0 K}
  mul_mem' := fun {a b} ha hb => by
    show cgE (a * b) (zU0 K) = zU0 K
    rw [cg_mul_apply]
    have hb' : cgE b (zU0 K) = zU0 K := hb
    have ha' : cgE a (zU0 K) = zU0 K := ha
    rw [hb', ha']
  one_mem' := rfl
  inv_mem' := fun {a} ha => by
    have ha' : cgE a (zU0 K) = zU0 K := ha
    show cgE a⁻¹ (zU0 K) = zU0 K
    conv_lhs => rw [← ha']
    exact cg_inv_apply a (zU0 K)

@[expose] def YQ (K : Type) [Field K] : AddSubgroup (Ix3 → K) where
  carrier := {w | w (Sum.inr 0) = 0}
  add_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq, Pi.add_apply] at *
    rw [ha, hb, add_zero]
  zero_mem' := rfl
  neg_mem' := fun {a} ha => by
    simp only [Set.mem_ofPred_eq, Pi.neg_apply] at *
    rw [ha, neg_zero]

namespace G2Low

section GroupTheory

variable {G : Type*} [Group G]

theorem two_mul_card_dvd_of_mem_normalizer {S : Subgroup G} {t : G}
    (htN : t ∈ Subgroup.normalizer (S : Set G)) (htS : t ∉ S) (ht2 : t * t ∈ S) :
    2 * Nat.card S ∣ Nat.card G := by
  let q : Subgroup.normalizer (S : Set G) ⧸ S.subgroupOf (Subgroup.normalizer (S : Set G)) :=
    QuotientGroup.mk ⟨t, htN⟩
  have hq1 : q ≠ 1 := fun h =>
    htS ((QuotientGroup.eq_one_iff (⟨t, htN⟩ : Subgroup.normalizer (S : Set G))).mp h)
  have hq2 : q ^ 2 = 1 := by
    rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact ht2
  have h1 : 2 ∣ Nat.card (Subgroup.normalizer (S : Set G) ⧸
      S.subgroupOf (Subgroup.normalizer (S : Set G))) := by
    rw [← orderOf_eq_prime hq2 hq1]
    exact orderOf_dvd_natCard q
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (S.subgroupOf (Subgroup.normalizer (S : Set G)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv] at h2
  exact (mul_dvd_mul_right h1 _).trans
    (h2 ▸ Subgroup.card_subgroup_dvd_card (Subgroup.normalizer (S : Set G)))

theorem two_mul_card_dvd_of_involution {R S : Subgroup G} (hSR : S ≤ R) {t : G} (htR : t ∈ R)
    (htS : t ∉ S) (ht2 : t * t = 1) (hn : ∀ s ∈ S, t * s * t ∈ S) :
    2 * Nat.card S ∣ Nat.card R := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hnorm : (⟨t, htR⟩ : R) ∈ Subgroup.normalizer ((S.subgroupOf R : Subgroup R) : Set R) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    change (h : G) ∈ S ↔ t * (h : G) * t⁻¹ ∈ S
    rw [htinv]
    refine ⟨hn _, fun h' => ?_⟩
    have := hn _ h'
    rwa [← mul_assoc, ← mul_assoc, ht2, one_mul, mul_assoc, ht2, mul_one] at this
  have key := two_mul_card_dvd_of_mem_normalizer hnorm
    (fun h => htS h) (S := S.subgroupOf R) (t := ⟨t, htR⟩) (by
      change t * t ∈ S
      rw [ht2]
      exact S.one_mem)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSR).toEquiv] at key

end GroupTheory

section Formulas

variable {K : Type} [Field K] [CharP K 2]

theorem g2Act_g2X_q6 (a : Fin 3 → K) (u₀ u₁ u₂ v₀ v₁ v₂ : K) :
    g2Act (g2X a) (q6 u₀ u₁ u₂ v₀ v₁ v₂) =
      q6 (u₀ + (0 + 0 + (a 0 * v₀ + a 1 * v₁ + a 2 * v₂)) * a 0)
        (u₁ + (0 + 0 + (a 0 * v₀ + a 1 * v₁ + a 2 * v₂)) * a 1)
        (u₂ + (0 + 0 + (a 0 * v₀ + a 1 * v₁ + a 2 * v₂)) * a 2)
        (v₀ + (a 1 * u₂ - a 2 * u₁)) (v₁ + (a 2 * u₀ - a 0 * u₂)) (v₂ + (a 0 * u₁ - a 1 * u₀)) := by
  rw [g2Act_apply, zI_q6, g2X_apply, xaFun_zmk, zP_zmk]

theorem g2Act_g2Y_q6 (b : Fin 3 → K) (u₀ u₁ u₂ v₀ v₁ v₂ : K) :
    g2Act (g2Y b) (q6 u₀ u₁ u₂ v₀ v₁ v₂) =
      q6 (u₀ + (b 1 * v₂ - b 2 * v₁)) (u₁ + (b 2 * v₀ - b 0 * v₂)) (u₂ + (b 0 * v₁ - b 1 * v₀))
        (v₀ + (0 + 0 + (b 0 * u₀ + b 1 * u₁ + b 2 * u₂)) * b 0)
        (v₁ + (0 + 0 + (b 0 * u₀ + b 1 * u₁ + b 2 * u₂)) * b 1)
        (v₂ + (0 + 0 + (b 0 * u₀ + b 1 * u₁ + b 2 * u₂)) * b 2) := by
  rw [g2Act_apply, zI_q6, g2Y_apply, ybFun_zmk, zP_zmk]

theorem g2Act_Xa (α u₀ u₁ u₂ v₁ v₂ : K) :
    g2Act (g2X ![α, 0, 0]) (q6 u₀ u₁ u₂ 0 v₁ v₂) = q6 u₀ u₁ u₂ 0 (v₁ - α * u₂) (v₂ + α * u₁) := by
  rw [g2Act_g2X_q6]
  apply q6_congr <;> simp [sub_eq_add_neg]

theorem g2Act_Yb1 (β u₀ u₁ u₂ v₁ v₂ : K) :
    g2Act (g2Y ![0, β, 0]) (q6 u₀ u₁ u₂ 0 v₁ v₂) =
      q6 (u₀ + β * v₂) u₁ u₂ 0 (v₁ + β * β * u₁) v₂ := by
  rw [g2Act_g2Y_q6]
  apply q6_congr <;> simp
  ring

theorem g2Act_Yb2 (γ u₀ u₁ u₂ v₁ v₂ : K) :
    g2Act (g2Y ![0, 0, γ]) (q6 u₀ u₁ u₂ 0 v₁ v₂) =
      q6 (u₀ - γ * v₁) u₁ u₂ 0 v₁ (v₂ + γ * γ * u₂) := by
  rw [g2Act_g2Y_q6]
  apply q6_congr <;> simp <;> ring

@[expose] def gA1 (K : Type) [Field K] : SL3 K :=
  ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem g2Act_GA (u₀ u₁ u₂ v₁ v₂ : K) :
    g2Act (g2A (gA1 K)) (q6 u₀ u₁ u₂ 0 v₁ v₂) = q6 u₀ (u₁ + u₂) u₂ 0 v₁ (v₂ - v₁) := by
  rw [g2Act_apply, zI_q6, g2A_apply, gAFun_zmk, zP_zmk]
  apply q6_congr <;> simp [gA1, Matrix.adjugate_fin_three]
  ring

theorem Xa_mem (α : K) : g2X ![α, 0, 0] ∈ stabU0 K := by
  show cgE (g2X ![α, 0, 0]) (zU0 K) = zU0 K
  rw [zU0]
  change xaFun ![α, 0, 0] (zmk 0 1 0 0 0 0 0 0) = _
  rw [xaFun_zmk]
  apply zmk_congr <;> simp

theorem Yb1_mem (β : K) : g2Y ![0, β, 0] ∈ stabU0 K := by
  show cgE (g2Y ![0, β, 0]) (zU0 K) = zU0 K
  rw [zU0]
  change ybFun ![0, β, 0] (zmk 0 1 0 0 0 0 0 0) = _
  rw [ybFun_zmk]
  apply zmk_congr <;> simp

theorem Yb2_mem (γ : K) : g2Y ![0, 0, γ] ∈ stabU0 K := by
  show cgE (g2Y ![0, 0, γ]) (zU0 K) = zU0 K
  rw [zU0]
  change ybFun ![0, 0, γ] (zmk 0 1 0 0 0 0 0 0) = _
  rw [ybFun_zmk]
  apply zmk_congr <;> simp

theorem GA_mem : g2A (gA1 K) ∈ stabU0 K := by
  show cgE (g2A (gA1 K)) (zU0 K) = zU0 K
  rw [zU0]
  change gAFun ((gA1 K : SL3 K) : Matrix (Fin 3) (Fin 3) K) (zmk 0 1 0 0 0 0 0 0) = _
  rw [gAFun_zmk]
  apply zmk_congr <;> simp [gA1]

end Formulas

section Coord

variable {K : Type} [Field K] {M : Type} [AddCommGroup M]

@[expose] def yq (K : Type) [Field K] (u₀ u₁ u₂ v₁ v₂ : K) : ↥(YQ K) :=
  ⟨q6 u₀ u₁ u₂ 0 v₁ v₂, rfl⟩

theorem yq_coe (u₀ u₁ u₂ v₁ v₂ : K) :
    ((yq K u₀ u₁ u₂ v₁ v₂ : ↥(YQ K)) : Ix3 → K) = q6 u₀ u₁ u₂ 0 v₁ v₂ := rfl

theorem yq_add (u₀ u₁ u₂ v₁ v₂ u₀' u₁' u₂' v₁' v₂' : K) :
    yq K u₀ u₁ u₂ v₁ v₂ + yq K u₀' u₁' u₂' v₁' v₂' =
      yq K (u₀ + u₀') (u₁ + u₁') (u₂ + u₂') (v₁ + v₁') (v₂ + v₂') := by
  apply Subtype.ext
  simp only [AddSubgroup.coe_add, yq_coe, q6_add, add_zero]

@[expose] def mm (m : ↥(YQ K) →+ M) (u₁ u₂ v₁ v₂ : K) : M := m (yq K 0 u₁ u₂ v₁ v₂)

theorem mm_add (m : ↥(YQ K) →+ M) (a b c d a' b' c' d' : K) :
    mm m (a + a') (b + b') (c + c') (d + d') = mm m a b c d + mm m a' b' c' d' := by
  rw [mm, mm, mm, ← map_add, yq_add, add_zero]

theorem mm_zero (m : ↥(YQ K) →+ M) : mm m 0 0 0 0 = 0 := by
  have : yq K 0 0 0 0 0 = 0 := Subtype.ext q6_zero
  rw [mm, this, map_zero]

theorem mm_sub (m : ↥(YQ K) →+ M) (a b c d a' b' c' d' : K) :
    mm m (a - a') (b - b') (c - c') (d - d') = mm m a b c d - mm m a' b' c' d' := by
  rw [eq_sub_iff_add_eq, ← mm_add]
  simp only [sub_add_cancel]

theorem mm_add_right (m : ↥(YQ K) →+ M) (a b c d x y : K) :
    mm m a b (c + x) (d + y) = mm m a b c d + mm m 0 0 x y := by
  have := mm_add m a b c d 0 0 x y
  rwa [add_zero, add_zero] at this

variable {m : ↥(YQ K) →+ M}
  (hker : ∀ w w' : ↥(YQ K), m w = m w' ↔
    ∃ c : K, (w : Ix3 → K) - (w' : Ix3 → K) = q6 c 0 0 0 0 0)

include hker in
theorem m_yq (u₀ u₁ u₂ v₁ v₂ : K) : m (yq K u₀ u₁ u₂ v₁ v₂) = mm m u₁ u₂ v₁ v₂ := by
  refine (hker _ _).2 ⟨u₀, ?_⟩
  rw [yq_coe, yq_coe, q6_sub]
  apply q6_congr <;> simp

include hker in
theorem mm_eq_iff (a b c d a' b' c' d' : K) :
    mm m a b c d = mm m a' b' c' d' ↔ a = a' ∧ b = b' ∧ c = c' ∧ d = d' := by
  rw [mm, mm, hker]
  constructor
  · rintro ⟨c₀, h⟩
    rw [yq_coe, yq_coe, q6_sub] at h
    obtain ⟨-, h1, h2, -, h4, h5⟩ := q6_inj h
    exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2, sub_eq_zero.mp h4, sub_eq_zero.mp h5⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    exact ⟨0, by simp only [yq_coe, q6_sub]; apply q6_congr <;> simp⟩

include hker in
theorem m_eq_mm (w : ↥(YQ K)) :
    m w = mm m ((w : Ix3 → K) (.inl 1)) ((w : Ix3 → K) (.inl 2)) ((w : Ix3 → K) (.inr 1))
      ((w : Ix3 → K) (.inr 2)) := by
  have h0 : (w : Ix3 → K) (Sum.inr 0) = 0 := w.2
  have e : w = yq K ((w : Ix3 → K) (.inl 0)) ((w : Ix3 → K) (.inl 1)) ((w : Ix3 → K) (.inl 2))
      ((w : Ix3 → K) (.inr 1)) ((w : Ix3 → K) (.inr 2)) := by
    apply Subtype.ext
    have := q6_eta (w : Ix3 → K)
    rw [h0] at this
    exact this
  rw [e, m_yq hker]
  rfl

include hker in
theorem exists_mm (hsurj : Function.Surjective m) (n : M) : ∃ a b c d : K, mm m a b c d = n := by
  obtain ⟨w, rfl⟩ := hsurj n
  exact ⟨_, _, _, _, (m_eq_mm hker w).symm⟩

end Coord

section SBig

variable {K : Type} [Field K] {M : Type} [AddCommGroup M]

@[expose] def vHom (m : ↥(YQ K) →+ M) : K × K →+ M where
  toFun p := mm m 0 0 p.1 p.2
  map_zero' := mm_zero m
  map_add' p q := by
    have := mm_add m 0 0 p.1 p.2 0 0 q.1 q.2
    rw [add_zero] at this
    exact this

@[expose] def vSub (m : ↥(YQ K) →+ M) : AddSubgroup M := (vHom m).range

theorem mm_mem_vSub (m : ↥(YQ K) →+ M) (c d : K) : mm m 0 0 c d ∈ vSub m := ⟨(c, d), rfl⟩

theorem mem_vSub_iff (m : ↥(YQ K) →+ M) {n : M} : n ∈ vSub m ↔ ∃ c d : K, mm m 0 0 c d = n := by
  constructor
  · rintro ⟨⟨c, d⟩, h⟩
    exact ⟨c, d, h⟩
  · rintro ⟨c, d, h⟩
    exact ⟨(c, d), h⟩

variable {m : ↥(YQ K) →+ M}
  (hker : ∀ w w' : ↥(YQ K), m w = m w' ↔
    ∃ c : K, (w : Ix3 → K) - (w' : Ix3 → K) = q6 c 0 0 0 0 0)

include hker in
theorem mm_mem_vSub_iff (a b c d : K) : mm m a b c d ∈ vSub m ↔ a = 0 ∧ b = 0 := by
  rw [mem_vSub_iff]
  constructor
  · rintro ⟨c', d', h⟩
    obtain ⟨h1, h2, -, -⟩ := (mm_eq_iff hker _ _ _ _ _ _ _ _).mp h
    exact ⟨h1.symm, h2.symm⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨c, d, rfl⟩

@[expose] def sBig (m : ↥(YQ K) →+ M) (E : Type) [Semiring E] [Module E M] :
    Subgroup (M ≃ₗ[E] M) where
  carrier := {σ | (∀ n, σ n - n ∈ vSub m) ∧ ∀ n ∈ vSub m, σ n = n}
  mul_mem' := by
    rintro σ ρ ⟨hσ, hσ'⟩ ⟨hρ, hρ'⟩
    refine ⟨fun n => ?_, fun n hn => ?_⟩
    · have := (vSub m).add_mem (hσ (ρ n)) (hρ n)
      rwa [sub_add_sub_cancel] at this
    · rw [LinearEquiv.mul_apply, hρ' n hn, hσ' n hn]
  one_mem' := ⟨fun n => by simp, fun n hn => rfl⟩
  inv_mem' := by
    rintro σ ⟨hσ, hσ'⟩
    refine ⟨fun n => ?_, fun n hn => ?_⟩
    · have h := (vSub m).neg_mem (hσ (σ⁻¹ n))
      rw [show σ (σ⁻¹ n) = n from σ.apply_symm_apply n, neg_sub] at h
      exact h
    · calc σ⁻¹ n = σ⁻¹ (σ n) := by rw [hσ' n hn]
        _ = n := σ.symm_apply_apply n

variable {E : Type} [Semiring E] [Module E M]

theorem sBig_mul_self (h2 : ∀ n : M, n + n = 0) {σ : M ≃ₗ[E] M} (hσ : σ ∈ sBig m E) :
    σ * σ = 1 := by
  obtain ⟨h1, h1'⟩ := hσ
  ext n
  have hfix := h1' _ (h1 n)
  have e1 : σ (σ n) = σ n + (σ n - n) := by
    calc σ (σ n) = σ (n + (σ n - n)) := by rw [add_sub_cancel]
      _ = σ n + σ (σ n - n) := map_add _ _ _
      _ = σ n + (σ n - n) := by rw [hfix]
  rw [LinearEquiv.mul_apply, e1]
  change _ = n
  calc σ n + (σ n - n) = ((σ n - n) + (σ n - n)) + n := by abel
    _ = n := by rw [h2, zero_add]

theorem isPGroup_of_le_sBig (h2 : ∀ n : M, n + n = 0) {S : Subgroup (M ≃ₗ[E] M)}
    (hS : S ≤ sBig m E) : IsPGroup 2 S := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, pow_two, Subgroup.coe_mul, sBig_mul_self h2 (hS g.2)]
  rfl

theorem conj_mem_sBig {τ : M ≃ₗ[E] M} (hτ2 : τ * τ = 1) (hτV : ∀ n ∈ vSub m, τ n ∈ vSub m)
    {s : M ≃ₗ[E] M} (hs : s ∈ sBig m E) : τ * s * τ ∈ sBig m E := by
  obtain ⟨hs1, hs2⟩ := hs
  have hττ : ∀ n, τ (τ n) = n := fun n => by
    have := congrArg (fun f : M ≃ₗ[E] M => f n) hτ2
    simpa using this
  refine ⟨fun n => ?_, fun n hn => ?_⟩
  · have hd := hτV _ (hs1 (τ n))
    rw [map_sub, hττ] at hd
    exact hd
  · have h1 := hτV n hn
    change τ (s (τ n)) = n
    rw [hs2 _ h1, hττ]

end SBig

section Action

variable {K : Type} [Field K] [CharP K 2] {E : Type} [Semiring E] {M : Type} [AddCommGroup M]
  [Module E M] {m : ↥(YQ K) →+ M}
  (hker : ∀ w w' : ↥(YQ K), m w = m w' ↔
    ∃ c : K, (w : Ix3 → K) - (w' : Ix3 → K) = q6 c 0 0 0 0 0)
  {Ξ : ↥(stabU0 K) →* (M ≃ₗ[E] M)}
  (hΞ : ∀ (g : ↥(stabU0 K)) (w : ↥(YQ K)), ∃ w' : ↥(YQ K),
    (w' : Ix3 → K) = g2Act (g : ↥(cayleyGroup K)) (w : Ix3 → K) ∧ Ξ g (m w) = m w')

include hker hΞ in
theorem Xi_mm (g : ↥(stabU0 K)) {a b c d a' b' c' d' u₀' : K}
    (hg : g2Act (g : ↥(cayleyGroup K)) (q6 0 a b 0 c d) = q6 u₀' a' b' 0 c' d') :
    Ξ g (mm m a b c d) = mm m a' b' c' d' := by
  obtain ⟨w', hw', hΞw'⟩ := hΞ g (yq K 0 a b c d)
  rw [yq_coe, hg] at hw'
  have e : w' = yq K u₀' a' b' c' d' := Subtype.ext hw'
  show Ξ g (m (yq K 0 a b c d)) = _
  rw [hΞw', e, m_yq hker]

include hker hΞ in
theorem Xi_Xa (α a b c d : K) :
    Ξ ⟨g2X ![α, 0, 0], Xa_mem α⟩ (mm m a b c d) = mm m a b (c - α * b) (d + α * a) :=
  Xi_mm hker hΞ _ (g2Act_Xa α 0 a b c d)

include hker hΞ in
theorem Xi_Yb1 (β a b c d : K) :
    Ξ ⟨g2Y ![0, β, 0], Yb1_mem β⟩ (mm m a b c d) = mm m a b (c + β * β * a) d :=
  Xi_mm hker hΞ _ (g2Act_Yb1 β 0 a b c d)

include hker hΞ in
theorem Xi_Yb2 (γ a b c d : K) :
    Ξ ⟨g2Y ![0, 0, γ], Yb2_mem γ⟩ (mm m a b c d) = mm m a b c (d + γ * γ * b) :=
  Xi_mm hker hΞ _ (g2Act_Yb2 γ 0 a b c d)

@[expose] def fam (β γ α : K) : ↥(stabU0 K) :=
  ⟨g2Y ![0, β, 0], Yb1_mem β⟩ * ⟨g2Y ![0, 0, γ], Yb2_mem γ⟩ * ⟨g2X ![α, 0, 0], Xa_mem α⟩

include hker hΞ in
theorem Xi_fam (β γ α a b c d : K) :
    Ξ (fam β γ α) (mm m a b c d) =
      mm m a b (c + (β * β * a - α * b)) (d + (α * a + γ * γ * b)) := by
  rw [fam, map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, Xi_Xa hker hΞ,
    Xi_Yb2 hker hΞ, Xi_Yb1 hker hΞ]
  congr 1 <;> ring

include hker hΞ in
theorem Xi_fam_mem_sBig (hsurj : Function.Surjective m) (β γ α : K) :
    Ξ (fam β γ α) ∈ sBig m E := by
  refine ⟨fun n => ?_, fun n hn => ?_⟩
  · obtain ⟨a, b, c, d, rfl⟩ := exists_mm hker hsurj n
    rw [Xi_fam hker hΞ, mm_add_right, add_sub_cancel_left]
    exact mm_mem_vSub m _ _
  · obtain ⟨c, d, rfl⟩ := (mem_vSub_iff m).mp hn
    rw [Xi_fam hker hΞ]
    simp

theorem gA1_mul_self : gA1 K * gA1 K = 1 := by
  apply Subtype.ext
  change !![(1 : K), 0, 0; 0, 1, 1; 0, 0, 1] * !![1, 0, 0; 0, 1, 1; 0, 0, 1] = 1
  rw [Matrix.mul_fin_three, Matrix.one_fin_three]
  have h : (1 : K) + 1 = 0 := CharTwo.add_self_eq_zero 1
  simp [h]

@[expose] def gaStab : ↥(stabU0 K) := ⟨g2A (gA1 K), GA_mem⟩

theorem gaStab_mul_self : (gaStab : ↥(stabU0 K)) * gaStab = 1 := by
  apply Subtype.ext
  change g2A (gA1 K) * g2A (gA1 K) = 1
  rw [← map_mul, gA1_mul_self, map_one]

include hker hΞ in
theorem Xi_gaStab (a b c d : K) :
    Ξ gaStab (mm m a b c d) = mm m (a + b) b c (d - c) :=
  Xi_mm hker hΞ _ (g2Act_GA 0 a b c d)

end Action

end G2Low

open G2Low

theorem two_pow_seven_dvd {K : Type} [Field K] [CharP K 2] (hK : Nat.card K = 4)
    {E : Type} [Semiring E] {M : Type} [AddCommGroup M] [Module E M] [Finite M]
    (h2 : ∀ n : M, n + n = 0)
    (m : ↥(YQ K) →+ M) (hsurj : Function.Surjective m)
    (hker : ∀ w w' : ↥(YQ K), m w = m w' ↔
      ∃ c : K, (w : Ix3 → K) - (w' : Ix3 → K) = q6 c 0 0 0 0 0)
    (Ξ : ↥(stabU0 K) →* (M ≃ₗ[E] M))
    (hΞ : ∀ (g : ↥(stabU0 K)) (w : ↥(YQ K)), ∃ w' : ↥(YQ K),
      (w' : Ix3 → K) = g2Act (g : ↥(cayleyGroup K)) (w : Ix3 → K) ∧ Ξ g (m w) = m w') :
    2 ^ 7 ∣ Nat.card Ξ.range := by
  have hKfin : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  have hGfin : Finite (M ≃ₗ[E] M) :=
    Finite.of_injective (fun e : M ≃ₗ[E] M => (e : M → M)) DFunLike.coe_injective
  set S : Subgroup (M ≃ₗ[E] M) := Ξ.range ⊓ sBig m E
  have hSR : S ≤ Ξ.range := inf_le_left
  obtain ⟨a, ha⟩ := (isPGroup_of_le_sBig h2 (inf_le_right : S ≤ sBig m E)).exists_card_eq
  have hsq : ∀ x y : K, x * x = y * y → x = y := fun x y h => by
    have : x ^ 2 = y ^ 2 := by simpa [sq] using h
    exact frobenius_inj K 2 this
  have hmem : ∀ x : K × K × K, Ξ (fam x.1 x.2.1 x.2.2) ∈ S := fun x =>
    ⟨⟨_, rfl⟩, Xi_fam_mem_sBig hker hΞ hsurj _ _ _⟩
  have hinj : Function.Injective
      (fun x : K × K × K => (⟨Ξ (fam x.1 x.2.1 x.2.2), hmem x⟩ : ↥S)) := by
    rintro ⟨β, γ, α⟩ ⟨β', γ', α'⟩ h
    have h' : Ξ (fam β γ α) = Ξ (fam β' γ' α') := congrArg Subtype.val h
    have e1 := congrArg (fun σ => σ (mm m 1 0 0 0)) h'
    have e2 := congrArg (fun σ => σ (mm m 0 1 0 0)) h'
    simp only [Xi_fam hker hΞ, mm_eq_iff hker] at e1 e2
    obtain ⟨-, -, e11, e12⟩ := e1
    obtain ⟨-, -, -, e22⟩ := e2
    simp at e11 e12 e22
    exact Prod.ext (hsq _ _ e11) (Prod.ext (hsq _ _ e22) e12)
  have h64 : 64 ≤ Nat.card S := by
    have := Nat.card_le_card_of_injective _ hinj
    rwa [Nat.card_prod, Nat.card_prod, hK] at this
  have h6a : 6 ≤ a := by
    have h64' : 2 ^ 6 ≤ 2 ^ a := by
      rw [← show Nat.card S = 2 ^ a from ha]
      exact h64
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h64'
  have h6 : 2 ^ 6 ∣ Nat.card S := by
    rw [show Nat.card S = 2 ^ a from ha]
    exact pow_dvd_pow 2 h6a
  set τ : M ≃ₗ[E] M := Ξ gaStab with hτdef
  have hττ : τ * τ = 1 := by rw [hτdef, ← map_mul, gaStab_mul_self, map_one]
  have hτR : τ ∈ Ξ.range := ⟨gaStab, rfl⟩
  have hτV : ∀ n ∈ vSub m, τ n ∈ vSub m := by
    intro n hn
    obtain ⟨c, d, rfl⟩ := (mem_vSub_iff m).mp hn
    rw [hτdef, Xi_gaStab hker hΞ, add_zero]
    exact mm_mem_vSub m _ _
  have hτS : τ ∉ S := by
    intro hτ
    have h1 := hτ.2.1 (mm m 0 1 0 0)
    rw [hτdef, Xi_gaStab hker hΞ, ← mm_sub, mm_mem_vSub_iff hker] at h1
    exact absurd h1.1 (by simp)
  have hτn : ∀ s ∈ S, τ * s * τ ∈ S := fun s hs =>
    ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hτR hs.1) hτR, conj_mem_sBig hττ hτV hs.2⟩
  have key := two_mul_card_dvd_of_involution hSR hτR hτS hττ hτn
  calc 2 ^ 7 = 2 * 2 ^ 6 := by norm_num
    _ ∣ 2 * Nat.card S := mul_dvd_mul_left 2 h6
    _ ∣ Nat.card Ξ.range := key

end CFSG.Quasithin.G11.SzG11S.Two
