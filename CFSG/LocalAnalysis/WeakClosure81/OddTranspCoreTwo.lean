module

public import CFSG.Fischer.Classification.PartII.Herm.Graph
public import CFSG.CGT.PushingUpLit.BHSSym.Coxeter

public section

namespace CFSG.LocalAnalysis.WeakClosure81.CoreStar

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification Subgroup
open CFSG.Permutation.SymmetricCoxeter

variable {Y : Type} [Group Y]

@[expose] def HasCoreStar (Y : Type) [Group Y] (t : Y) : Prop :=
  ∃ e₁ e₂ e₃ : Y, IsConj t e₁ ∧ IsConj t e₂ ∧ IsConj t e₃ ∧
    orderOf (t * e₁) = 3 ∧ orderOf (t * e₂) = 3 ∧ orderOf (t * e₃) = 3 ∧
    e₁ * e₂ = e₂ * e₁ ∧ e₁ * e₃ = e₃ * e₁ ∧ e₂ * e₃ = e₃ * e₂ ∧
    e₁ ≠ e₂ ∧ e₁ ≠ e₃ ∧ e₂ ≠ e₃

private theorem orderOf_conj_inv (g x : Y) : orderOf (g⁻¹ * x * g) = orderOf x :=
  (SemiconjBy.orderOf_eq g⁻¹ (by unfold SemiconjBy; group)).symm

theorem hasCoreStar_of_center {t c x y z : Y} (hc : IsConj t c) (hx : IsConj t x)
    (hy : IsConj t y) (hz : IsConj t z) (ox : orderOf (c * x) = 3) (oy : orderOf (c * y) = 3)
    (oz : orderOf (c * z) = 3) (cxy : x * y = y * x) (cxz : x * z = z * x)
    (cyz : y * z = z * y) (nxy : x ≠ y) (nxz : x ≠ z) (nyz : y ≠ z) : HasCoreStar Y t := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hc
  have hconj : ∀ w : Y, IsConj t w → IsConj t (g⁻¹ * w * g) := fun w hw =>
    hw.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩)
  have hord : ∀ w : Y, orderOf (t * (g⁻¹ * w * g)) = orderOf (c * w) := fun w => by
    rw [show t * (g⁻¹ * w * g) = g⁻¹ * (c * w) * g by rw [← hg]; group, orderOf_conj_inv]
  have hcomm : ∀ u v : Y, u * v = v * u → (g⁻¹ * u * g) * (g⁻¹ * v * g) =
      (g⁻¹ * v * g) * (g⁻¹ * u * g) := fun u v h => by
    rw [show (g⁻¹ * u * g) * (g⁻¹ * v * g) = g⁻¹ * (u * v) * g by group, h]; group
  have hne : ∀ u v : Y, u ≠ v → g⁻¹ * u * g ≠ g⁻¹ * v * g := fun u v h h' =>
    h (by simpa using h')
  exact ⟨_, _, _, hconj x hx, hconj y hy, hconj z hz, (hord x).trans ox, (hord y).trans oy,
    (hord z).trans oz, hcomm x y cxy, hcomm x z cxz, hcomm y z cyz, hne x y nxy, hne x z nxz,
    hne y z nyz⟩

theorem hasCoreStar_map {G H : Type} [Group G] [Group H] {t : G} (f : G →* H)
    (hf : Function.Injective f) (h : HasCoreStar G t) : HasCoreStar H (f t) := by
  obtain ⟨e₁, e₂, e₃, k₁, k₂, k₃, o₁, o₂, o₃, c₁₂, c₁₃, c₂₃, n₁₂, n₁₃, n₂₃⟩ := h
  have hord : ∀ e : G, orderOf (f t * f e) = orderOf (t * e) := fun e => by
    rw [← map_mul, orderOf_injective f hf]
  have hc : ∀ a b : G, a * b = b * a → f a * f b = f b * f a := fun a b h => by
    rw [← map_mul, h, map_mul]
  exact ⟨f e₁, f e₂, f e₃, f.map_isConj k₁, f.map_isConj k₂, f.map_isConj k₃,
    (hord e₁).trans o₁, (hord e₂).trans o₂, (hord e₃).trans o₃, hc _ _ c₁₂, hc _ _ c₁₃,
    hc _ _ c₂₃, hf.ne n₁₂, hf.ne n₁₃, hf.ne n₂₃⟩

private def seq3 (a b c : Y) : ℕ → Y
  | 0 => a
  | 1 => b
  | _ => c

private theorem exists_hom_perm_four {a b c : Y} (ha : a * a = 1) (hb : b * b = 1)
    (hc : c * c = 1) (hab : (a * b) ^ 3 = 1) (hbc : (b * c) ^ 3 = 1) (hac : a * c = c * a)
    (nab : a ≠ b) (nac : a ≠ c) (nbc : b ≠ c) :
    ∃ φ : Equiv.Perm (Fin 4) →* Y, Function.Injective φ ∧ φ (adjSwap 3 0) = a ∧
      φ (adjSwap 3 1) = b ∧ φ (adjSwap 3 2) = c := by
  obtain ⟨e, he⟩ := CFSG.CGT.PushingUpLit.BHSSym.exists_mulEquiv_of_pow_three (n := 3)
    (x := seq3 a b c) (by norm_num)
    (fun i hi => by
      interval_cases i
      exacts [ha, hb, hc])
    (fun i hi => by
      obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
      exacts [hab, hbc])
    (fun i j hij hj => by
      obtain rfl : i = 0 := by omega
      obtain rfl : j = 2 := by omega
      exact hac)
    (fun i j hi hj hij => by
      interval_cases i <;> interval_cases j
      exacts [absurd rfl hij, nab, nac, nab.symm, absurd rfl hij, nbc, nac.symm, nbc.symm,
        absurd rfl hij])
  exact ⟨(Subgroup.closure (seq3 a b c '' Set.Iio 3)).subtype.comp e.toMonoidHom,
    Subtype.val_injective.comp e.injective, he 0 (by norm_num), he 1 (by norm_num),
    he 2 (by norm_num)⟩

private theorem eq_one_of_conj_relations {p z A B R : Y} (hpp : p * p = 1)
    (h1 : p * R * p = z * R) (hR : R = A * B) (h3 : p * A * p = z * A)
    (h4 : p * B * p = z * B) : z = 1 := by
  subst hR
  have e : z * (A * B) = z * A * z * B := by
    rw [← h1, show p * (A * B) * p = (p * A * p) * (p * B * p) by
      rw [show p * A * p * (p * B * p) = p * A * (p * p) * B * p by group, hpp]; group, h3, h4]
    group
  have e' := mul_right_cancel ((mul_assoc z A B).trans e)
  exact (mul_left_cancel ((mul_one (z * A)).trans e')).symm

theorem mul_ne_mul_of_orderOf {x y : Y} (hx : x * x = 1) (hy : y * y = 1)
    (h : orderOf (x * y) = 3) : x * y ≠ y * x := by
  intro hxy
  have h2 : (x * y) ^ 2 = 1 := by
    rw [sq, show x * y * (x * y) = x * (y * x) * y by group, ← hxy,
      show x * (x * y) * y = (x * x) * (y * y) by group, hx, hy, one_mul]
  have := orderOf_dvd_of_pow_eq_one h2
  rw [h] at this
  exact absurd this (by norm_num)

section TwoCore

variable {t : Y} {Q : Subgroup Y} [Q.Normal]

omit [Q.Normal] in
theorem commute_of_mul_mem (hP : Pair Y {x | IsConj t x}) (hQ2 : IsPGroup 2 Q)
    {x y : Y} (hx : IsConj t x) (hy : IsConj t y) (hxy : x * y ∈ Q) : x * y = y * x := by
  obtain ⟨k, hk⟩ := hQ2 ⟨x * y, hxy⟩
  have hk' : (x * y) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd : orderOf (x * y) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  by_contra hne
  rw [Pair.orderOf_mul_eq_three hP hx hy hne] at hdvd
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)

theorem commute_of_mk_commute (hP : Pair Y {x | IsConj t x}) (hQ2 : IsPGroup 2 Q)
    {x y : Y} (hx : IsConj t x) (hy : IsConj t y) (h : (x : Y ⧸ Q) * y = y * x) :
    x * y = y * x := by
  by_contra hne
  have h3 : (x * y) ^ 3 = 1 := by
    rw [← Pair.orderOf_mul_eq_three hP hx hy hne, pow_orderOf_eq_one]
  have ha : (x : Y ⧸ Q) * x = 1 := by
    rw [← QuotientGroup.mk_mul, Pair.mul_self hP hx, QuotientGroup.mk_one]
  have hb : (y : Y ⧸ Q) * y = 1 := by
    rw [← QuotientGroup.mk_mul, Pair.mul_self hP hy, QuotientGroup.mk_one]
  have h2 : ((x : Y ⧸ Q) * y) ^ 2 = 1 := by
    rw [sq, show (x : Y ⧸ Q) * y * (x * y) = x * (y * x) * y by group, ← h,
      show (x : Y ⧸ Q) * (x * y) * y = (x * x) * (y * y) by group, ha, hb, one_mul]
  have h1 : (x : Y ⧸ Q) * y = 1 := by
    have : ((x : Y ⧸ Q) * y) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, h3, QuotientGroup.mk_one]
    rwa [pow_succ, h2, one_mul] at this
  exact hne (commute_of_mul_mem hP hQ2 hx hy
    ((QuotientGroup.eq_one_iff _).mp (by rw [QuotientGroup.mk_mul]; exact h1)))

theorem orderOf_eq_three_of_mk_eq (hP : Pair Y {x | IsConj t x}) (hQ2 : IsPGroup 2 Q)
    {c x y : Y} (hc : IsConj t c) (hx : IsConj t x) (hy : IsConj t y)
    (hxy : (x : Y ⧸ Q) = y) (h : orderOf (c * x) = 3) : orderOf (c * y) = 3 := by
  refine Pair.orderOf_mul_eq_three hP hc hy fun hcy => ?_
  exact mul_ne_mul_of_orderOf (Pair.mul_self hP hc) (Pair.mul_self hP hx) h
    (commute_of_mk_commute hP hQ2 hc hx (by
      rw [hxy, ← QuotientGroup.mk_mul, hcy, QuotientGroup.mk_mul]))

omit [Q.Normal] in
private theorem exists_orderOf_mul_eq_three (hP : Pair Y {x | IsConj t x})
    (hQ : ¬ Q ≤ center Y) {x : Y} (hx : IsConj t x) :
    ∃ c, IsConj t c ∧ orderOf (c * x) = 3 := by
  by_contra h
  push Not at h
  have hxZ : x ∈ center Y := (Pair.mem_center_iff hP).2 fun e he => by
    by_contra hne
    exact h e he (Pair.orderOf_mul_eq_three hP he hx hne)
  refine hQ (le_top.trans ?_)
  rw [← Pair.closure_eq hP, closure_le]
  intro e he
  obtain ⟨g, rfl⟩ := isConj_iff.mp (Pair.isConj hP hx he)
  rw [Subgroup.mem_center_iff.mp hxZ g, mul_inv_cancel_right]
  exact hxZ

private theorem exists_conj_ne (hP : Pair Y {x | IsConj t x}) (hQ : ¬ Q ≤ center Y) {x : Y}
    (hx : IsConj t x) : ∃ q ∈ Q, q * x * q⁻¹ ≠ x := by
  by_contra h
  push Not at h
  refine hQ fun q hq => (Pair.mem_center_iff hP).2 fun e he => ?_
  obtain ⟨g, rfl⟩ := isConj_iff.mp (Pair.isConj hP hx he)
  have hq' := h (g⁻¹ * q * g) (by simpa using ‹Q.Normal›.conj_mem q hq g⁻¹)
  calc g * x * g⁻¹ * q = g * (g⁻¹ * q * g * x * (g⁻¹ * q * g)⁻¹) * g⁻¹ * q := by rw [hq']
    _ = q * (g * x * g⁻¹) := by group

private theorem exists_partner (hP : Pair Y {x | IsConj t x}) (hQ : ¬ Q ≤ center Y) {x : Y}
    (hx : IsConj t x) : ∃ x₂, IsConj t x₂ ∧ x₂ ≠ x ∧ (x₂ : Y ⧸ Q) = x := by
  obtain ⟨q, hq, hne⟩ := exists_conj_ne hP hQ hx
  refine ⟨q * x * q⁻¹, hx.trans (isConj_iff.mpr ⟨q, rfl⟩), hne, ?_⟩
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    (QuotientGroup.eq_one_iff q).mpr hq, one_mul, inv_one, mul_one]

variable (hP : Pair Y {x | IsConj t x}) (hQ2 : IsPGroup 2 Q) (hQ : ¬ Q ≤ center Y)
  (hS : ¬ HasCoreStar Y t)
include hP hQ2 hQ hS

private theorem eq_of_mk_eq {x y z : Y} (hx : IsConj t x) (hy : IsConj t y) (hz : IsConj t z)
    (hyx : (y : Y ⧸ Q) = x) (hzx : (z : Y ⧸ Q) = x) (nyx : y ≠ x) (nzx : z ≠ x) : y = z := by
  by_contra nyz
  obtain ⟨c, hc, hcx⟩ := exists_orderOf_mul_eq_three hP hQ hx
  have cm : ∀ {u v : Y}, IsConj t u → IsConj t v → (u : Y ⧸ Q) = v → u * v = v * u :=
    fun hu hv h => commute_of_mk_commute hP hQ2 hu hv (by rw [h])
  exact hS (hasCoreStar_of_center hc hx hy hz hcx
    (orderOf_eq_three_of_mk_eq hP hQ2 hc hx hy hyx.symm hcx)
    (orderOf_eq_three_of_mk_eq hP hQ2 hc hx hz hzx.symm hcx)
    (cm hx hy hyx.symm) (cm hx hz hzx.symm) (cm hy hz (hyx.trans hzx.symm))
    (Ne.symm nyx) (Ne.symm nzx) nyz)

private theorem eq_or_eq_of_mk_eq {x x₂ y : Y} (hx : IsConj t x) (hx₂ : IsConj t x₂)
    (hy : IsConj t y) (nx₂ : x₂ ≠ x) (hx₂x : (x₂ : Y ⧸ Q) = x) (hyx : (y : Y ⧸ Q) = x) :
    y = x ∨ y = x₂ := by
  by_cases h : y = x
  · exact Or.inl h
  · exact Or.inr (eq_of_mk_eq hP hQ2 hQ hS hx hy hx₂ hyx hx₂x h nx₂)

private theorem mk_eq_of_commute {x y : Y} (hx : IsConj t x) (hy : IsConj t y)
    (hxy : x * y = y * x) : (x : Y ⧸ Q) = y := by
  by_contra hne
  obtain ⟨x₂, hx₂, nx₂, hx₂x⟩ := exists_partner hP hQ hx
  have nxy : x ≠ y := fun h => hne (by rw [h])
  obtain ⟨⟨z, hz⟩, hrz, hzv⟩ := Herm.exists_adj_adj_of_connected (Pair.isTranspositionSet hP)
    (Pair.connected_nonCommGraph hP) (r := ⟨x, hx⟩) (v := ⟨y, hy⟩)
    (fun h => nxy (congrArg Subtype.val h).symm) (fun h => h hxy)
  have ozx : orderOf (z * x) = 3 := Pair.orderOf_mul_eq_three hP hz hx fun h => hrz h.symm
  have ozy : orderOf (z * y) = 3 := Pair.orderOf_mul_eq_three hP hz hy hzv
  have cxx₂ : x * x₂ = x₂ * x := commute_of_mk_commute hP hQ2 hx hx₂ (by rw [hx₂x])
  have cx₂y : x₂ * y = y * x₂ := commute_of_mk_commute hP hQ2 hx₂ hy (by
    rw [hx₂x, ← QuotientGroup.mk_mul, hxy, QuotientGroup.mk_mul])
  exact hS (hasCoreStar_of_center hz hx hx₂ hy ozx
    (orderOf_eq_three_of_mk_eq hP hQ2 hz hx hx₂ hx₂x.symm ozx) ozy cxx₂ hxy cx₂y
    nx₂.symm nxy fun h => hne (by rw [← hx₂x, h]))

private theorem partner_eq {a a₂ b b₂ : Y} (ha : IsConj t a) (ha₂ : IsConj t a₂)
    (hb : IsConj t b) (hb₂ : IsConj t b₂) (na₂ : a₂ ≠ a) (ha₂a : (a₂ : Y ⧸ Q) = a)
    (nb₂ : b₂ ≠ b) (hb₂b : (b₂ : Y ⧸ Q) = b) (hab : (a : Y ⧸ Q) ≠ b) :
    a * b * a₂ * b * a = b₂ := by
  have nab : a * b ≠ b * a := fun h => hab (mk_eq_of_commute hP hQ2 hQ hS ha hb h)
  have nba₂ : b * a₂ ≠ a₂ * b := fun h =>
    hab (by rw [mk_eq_of_commute hP hQ2 hQ hS hb ha₂ h, ha₂a])
  obtain ⟨φ, hφ, h0, h1, h2⟩ := exists_hom_perm_four (Pair.mul_self hP ha)
    (Pair.mul_self hP hb) (Pair.mul_self hP ha₂)
    (by rw [← Pair.orderOf_mul_eq_three hP ha hb nab, pow_orderOf_eq_one])
    (by rw [← Pair.orderOf_mul_eq_three hP hb ha₂ nba₂, pow_orderOf_eq_one])
    (commute_of_mk_commute hP hQ2 ha ha₂ (by rw [ha₂a])) (fun h => hab (by rw [h]))
    na₂.symm (fun h => hab (by rw [h, ha₂a]))
  have hw : IsConj t (a * b * a₂ * b * a) := by
    have := Pair.mul_mul_mem hP ha (Pair.mul_mul_mem hP hb ha₂)
    rwa [show a * (b * a₂ * b) * a = a * b * a₂ * b * a by group] at this
  have hwb : a * b * a₂ * b * a * b = b * (a * b * a₂ * b * a) := by
    have := congrArg φ (show adjSwap 3 0 * adjSwap 3 1 * adjSwap 3 2 * adjSwap 3 1 *
        adjSwap 3 0 * adjSwap 3 1 = adjSwap 3 1 * (adjSwap 3 0 * adjSwap 3 1 * adjSwap 3 2 *
        adjSwap 3 1 * adjSwap 3 0) by decide)
    simpa only [map_mul, h0, h1, h2] using this
  have nwb : a * b * a₂ * b * a ≠ b := by
    have := hφ.ne (show adjSwap 3 0 * adjSwap 3 1 * adjSwap 3 2 * adjSwap 3 1 * adjSwap 3 0 ≠
        adjSwap 3 1 by decide)
    simpa only [map_mul, h0, h1, h2] using this
  exact (eq_or_eq_of_mk_eq hP hQ2 hQ hS hb hb₂ hw nb₂ hb₂b
    (mk_eq_of_commute hP hQ2 hQ hS hw hb hwb)).resolve_left nwb

private theorem conj_partnerProd {a a₂ b b₂ : Y} (ha : IsConj t a) (ha₂ : IsConj t a₂)
    (hb : IsConj t b) (hb₂ : IsConj t b₂) (na₂ : a₂ ≠ a) (ha₂a : (a₂ : Y ⧸ Q) = a)
    (nb₂ : b₂ ≠ b) (hb₂b : (b₂ : Y ⧸ Q) = b) (hab : (a : Y ⧸ Q) ≠ b) :
    a * (b * b₂) * a = a * a₂ * (b * b₂) := by
  have nab : a * b ≠ b * a := fun h => hab (mk_eq_of_commute hP hQ2 hQ hS ha hb h)
  have nba₂ : b * a₂ ≠ a₂ * b := fun h =>
    hab (by rw [mk_eq_of_commute hP hQ2 hQ hS hb ha₂ h, ha₂a])
  obtain ⟨φ, -, h0, h1, h2⟩ := exists_hom_perm_four (Pair.mul_self hP ha)
    (Pair.mul_self hP hb) (Pair.mul_self hP ha₂)
    (by rw [← Pair.orderOf_mul_eq_three hP ha hb nab, pow_orderOf_eq_one])
    (by rw [← Pair.orderOf_mul_eq_three hP hb ha₂ nba₂, pow_orderOf_eq_one])
    (commute_of_mk_commute hP hQ2 ha ha₂ (by rw [ha₂a])) (fun h => hab (by rw [h]))
    na₂.symm (fun h => hab (by rw [h, ha₂a]))
  rw [← partner_eq hP hQ2 hQ hS ha ha₂ hb hb₂ na₂ ha₂a nb₂ hb₂b hab]
  have := congrArg φ (show adjSwap 3 0 * (adjSwap 3 1 * (adjSwap 3 0 * adjSwap 3 1 *
      adjSwap 3 2 * adjSwap 3 1 * adjSwap 3 0)) * adjSwap 3 0 = adjSwap 3 0 * adjSwap 3 2 *
      (adjSwap 3 1 * (adjSwap 3 0 * adjSwap 3 1 * adjSwap 3 2 * adjSwap 3 1 * adjSwap 3 0)) by
    decide)
  simpa only [map_mul, h0, h1, h2] using this

private theorem false_of_fourth_point {p p₂ q q₂ d d₂ : Y} (hp : IsConj t p)
    (hp₂ : IsConj t p₂) (hq : IsConj t q) (hq₂ : IsConj t q₂) (hd : IsConj t d)
    (hd₂ : IsConj t d₂) (np₂ : p₂ ≠ p) (hp₂p : (p₂ : Y ⧸ Q) = p) (nq₂ : q₂ ≠ q)
    (hq₂q : (q₂ : Y ⧸ Q) = q) (nd₂ : d₂ ≠ d) (hd₂d : (d₂ : Y ⧸ Q) = d)
    (hpq : (p : Y ⧸ Q) ≠ q) (hdp : (d : Y ⧸ Q) ≠ p) (hdq : (d : Y ⧸ Q) ≠ q)
    (hdpqp : (d : Y ⧸ Q) ≠ ((p * q * p : Y) : Y ⧸ Q)) : False := by
  have hr : IsConj t (q * d * q) := Pair.mul_mul_mem hP hq hd
  have hr₂ : IsConj t (q * d₂ * q) := Pair.mul_mul_mem hP hq hd₂
  have nr₂ : q * d₂ * q ≠ q * d * q := fun h => nd₂ (by simpa using h)
  have hr₂r : ((q * d₂ * q : Y) : Y ⧸ Q) = ((q * d * q : Y) : Y ⧸ Q) := by
    simp only [QuotientGroup.mk_mul, hd₂d]
  have hbraid : p * q * p = q * p * q :=
    Pair.mul_mul_eq hP hp hq fun h => hpq (mk_eq_of_commute hP hQ2 hQ hS hp hq h)
  have hpr : (p : Y ⧸ Q) ≠ ((q * d * q : Y) : Y ⧸ Q) := by
    intro h
    apply hdpqp
    have hqq : (q : Y ⧸ Q) * q = 1 := by
      rw [← QuotientGroup.mk_mul, Pair.mul_self hP hq, QuotientGroup.mk_one]
    rw [hbraid]
    simp only [QuotientGroup.mk_mul] at h ⊢
    rw [h]
    calc (d : Y ⧸ Q) = (q * q) * d * (q * q) := by rw [hqq, one_mul, mul_one]
      _ = _ := by group
  have hR : q * d * q * (q * d₂ * q) = q * q₂ * (d * d₂) := by
    rw [← conj_partnerProd hP hQ2 hQ hS hq hq₂ hd hd₂ nq₂ hq₂q nd₂ hd₂d (Ne.symm hdq),
      show q * d * q * (q * d₂ * q) = q * d * (q * q) * d₂ * q by group, Pair.mul_self hP hq]
    group
  have hZ := eq_one_of_conj_relations (Pair.mul_self hP hp)
    (conj_partnerProd hP hQ2 hQ hS hp hp₂ hr hr₂ np₂ hp₂p nr₂ hr₂r hpr) hR
    (conj_partnerProd hP hQ2 hQ hS hp hp₂ hq hq₂ np₂ hp₂p nq₂ hq₂q hpq)
    (conj_partnerProd hP hQ2 hQ hS hp hp₂ hd hd₂ np₂ hp₂p nd₂ hd₂d (Ne.symm hdp))
  exact np₂ (by rw [← Pair.inv_eq hP hp]; exact eq_inv_of_mul_eq_one_right hZ)

end TwoCore

theorem perm_four_or_hasCoreStar {t : Y} (hP : Pair Y {x | IsConj t x}) {Q : Subgroup Y}
    [Q.Normal] (hQ2 : IsPGroup 2 Q) (hQ : ¬ Q ≤ center Y) :
    (∃ e : Y ≃* Equiv.Perm (Fin 4), (e t).IsSwap) ∨ HasCoreStar Y t := by
  by_cases hS : HasCoreStar Y t
  · exact Or.inr hS
  left
  have ht : IsConj t t := IsConj.refl t
  obtain ⟨t₂, ht₂, nt₂, ht₂t⟩ := exists_partner hP hQ ht
  obtain ⟨s, hs, hst⟩ := exists_orderOf_mul_eq_three hP hQ ht
  obtain ⟨s₂, hs₂, ns₂, hs₂s⟩ := exists_partner hP hQ hs
  have nts : t * s ≠ s * t := fun h =>
    mul_ne_mul_of_orderOf (Pair.mul_self hP hs) (Pair.mul_self hP ht) hst h.symm
  have hts : (t : Y ⧸ Q) ≠ s := fun h => nts (commute_of_mk_commute hP hQ2 ht hs (by rw [h]))
  have nst₂ : s * t₂ ≠ t₂ * s := fun h =>
    hts (by rw [← ht₂t, mk_eq_of_commute hP hQ2 hQ hS hs ht₂ h])
  obtain ⟨φ, hφ, h0, h1, h2⟩ := exists_hom_perm_four (Pair.mul_self hP ht)
    (Pair.mul_self hP hs) (Pair.mul_self hP ht₂)
    (by rw [← Pair.orderOf_mul_eq_three hP ht hs nts, pow_orderOf_eq_one])
    (by rw [← Pair.orderOf_mul_eq_three hP hs ht₂ nst₂, pow_orderOf_eq_one])
    (commute_of_mk_commute hP hQ2 ht ht₂ (by rw [ht₂t])) (fun h => hts (by rw [h]))
    nt₂.symm (fun h => hts (by rw [h, ht₂t]))
  have mt : t ∈ φ.range := MonoidHom.mem_range.mpr ⟨_, h0⟩
  have ms : s ∈ φ.range := MonoidHom.mem_range.mpr ⟨_, h1⟩
  have mt₂ : t₂ ∈ φ.range := MonoidHom.mem_range.mpr ⟨_, h2⟩
  have ms₂ : s₂ ∈ φ.range := by
    rw [← partner_eq hP hQ2 hQ hS ht ht₂ hs hs₂ nt₂ ht₂t ns₂ hs₂s hts]
    exact mul_mem (mul_mem (mul_mem (mul_mem mt ms) mt₂) ms) mt
  have hu : IsConj t (t * s * t) := Pair.mul_mul_mem hP ht hs
  have mu : t * s * t ∈ φ.range := mul_mem (mul_mem mt ms) mt
  obtain ⟨u₂, hu₂, nu₂, hu₂u⟩ := exists_partner hP hQ hu
  have hsu : (s : Y ⧸ Q) ≠ ((t * s * t : Y) : Y ⧸ Q) := fun h =>
    nts (commute_of_mk_commute hP hQ2 ht hs (by
      have htt : (t : Y ⧸ Q) * t = 1 := by
        rw [← QuotientGroup.mk_mul, Pair.mul_self hP ht, QuotientGroup.mk_one]
      simp only [QuotientGroup.mk_mul] at h
      calc (t : Y ⧸ Q) * s = t * (t * s * t) := by rw [← h]
        _ = (t * t) * s * t := by group
        _ = s * t := by rw [htt, one_mul]))
  have mu₂ : u₂ ∈ φ.range := by
    rw [← partner_eq hP hQ2 hQ hS hs hs₂ hu hu₂ ns₂ hs₂s nu₂ hu₂u hsu]
    exact mul_mem (mul_mem (mul_mem (mul_mem ms mu) ms₂) mu) ms
  have hsurj : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← Pair.closure_eq hP, closure_le]
    intro d hd
    obtain ⟨d₂, hd₂, nd₂, hd₂d⟩ := exists_partner hP hQ hd
    by_cases e1 : (d : Y ⧸ Q) = t
    · rcases eq_or_eq_of_mk_eq hP hQ2 hQ hS ht ht₂ hd nt₂ ht₂t e1 with h | h <;> rw [h]
      exacts [mt, mt₂]
    by_cases e2 : (d : Y ⧸ Q) = s
    · rcases eq_or_eq_of_mk_eq hP hQ2 hQ hS hs hs₂ hd ns₂ hs₂s e2 with h | h <;> rw [h]
      exacts [ms, ms₂]
    by_cases e3 : (d : Y ⧸ Q) = ((t * s * t : Y) : Y ⧸ Q)
    · rcases eq_or_eq_of_mk_eq hP hQ2 hQ hS hu hu₂ hd nu₂ hu₂u e3 with h | h <;> rw [h]
      exacts [mu, mu₂]
    exact (false_of_fourth_point hP hQ2 hQ hS ht ht₂ hs hs₂ hd hd₂ nt₂ ht₂t ns₂ hs₂s nd₂ hd₂d
      hts e1 e2 e3).elim
  have hbij : Function.Bijective φ := ⟨hφ, hsurj⟩
  refine ⟨(MulEquiv.ofBijective φ hbij).symm, ?_⟩
  have key : (MulEquiv.ofBijective φ hbij).symm t = adjSwap 3 0 := by
    rw [MulEquiv.symm_apply_eq, MulEquiv.ofBijective_apply, h0]
  rw [key]
  exact ⟨0, 1, by decide, by decide⟩

end CFSG.LocalAnalysis.WeakClosure81.CoreStar
