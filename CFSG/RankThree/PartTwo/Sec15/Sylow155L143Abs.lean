module

public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Group
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155L143

theorem mul_pow_three_of_central {G : Type*} [Group G] {u v : G}
    (hc : u * v * u⁻¹ * v⁻¹ ∈ Subgroup.center G) (hv : v ^ 3 ∈ Subgroup.center G) :
    (u * v) ^ 3 = u ^ 3 * v ^ 3 := by
  set c := u * v * u⁻¹ * v⁻¹ with hcdef
  have hcz : ∀ (k : ℕ) (g : G), g * c ^ k = c ^ k * g := fun k g =>
    Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hc k) g
  have h1 : u * v * u⁻¹ = c * v := by rw [hcdef]; group
  have hk : ∀ k : ℕ, u ^ k * v * (u ^ k)⁻¹ = c ^ k * v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc u ^ (k + 1) * v * (u ^ (k + 1))⁻¹ = u * (u ^ k * v * (u ^ k)⁻¹) * u⁻¹ := by group
        _ = u * (c ^ k * v) * u⁻¹ := by rw [ih]
        _ = c ^ k * (u * v * u⁻¹) := by
          rw [← mul_assoc u, hcz k u]
          simp only [mul_assoc]
        _ = c ^ (k + 1) * v := by rw [h1, ← mul_assoc, ← pow_succ]
  have hcv : Commute c v := by
    have := hcz 1 v
    rw [pow_one] at this
    exact this.symm
  have hc3 : c ^ 3 = 1 := by
    have h2 : u * v ^ 3 * u⁻¹ = c ^ 3 * v ^ 3 := by
      rw [← conj_pow, h1, hcv.mul_pow]
    have h3 : u * v ^ 3 * u⁻¹ = v ^ 3 := by
      rw [Subgroup.mem_center_iff.mp hv u]
      group
    rw [h3] at h2
    calc c ^ 3 = c ^ 3 * v ^ 3 * (v ^ 3)⁻¹ := by group
      _ = 1 := by rw [← h2, mul_inv_cancel]
  calc (u * v) ^ 3
      = (u ^ 1 * v * (u ^ 1)⁻¹) * (u ^ 2 * v * (u ^ 2)⁻¹) * (u ^ 3 * v * (u ^ 3)⁻¹) * u ^ 3 := by
        rw [pow_three']
        group
    _ = (c ^ 1 * v) * (c ^ 2 * v) * (c ^ 3 * v) * u ^ 3 := by rw [hk 1, hk 2, hk 3]
    _ = (c ^ 1 * c ^ 2) * (v * v) * v * u ^ 3 := by
        rw [hc3, one_mul, mul_assoc (c ^ 1) v, ← mul_assoc v, hcz 2 v]
        simp only [mul_assoc]
    _ = u ^ 3 * v ^ 3 := by
        rw [← pow_add, show 1 + 2 = 3 from rfl, hc3, one_mul, ← pow_three']
        exact (Subgroup.mem_center_iff.mp hv (u ^ 3)).symm

structure L143Config {Y : Type*} [Group Y] (a w : Y) : Prop where
  w_mem : w ∈ Subgroup.center Y
  w_ne : w ≠ 1
  w_pow : w ^ 3 = 1
  a_pow : a ^ 3 = 1
  a_not_mem : a ∉ Subgroup.center Y
  threes : ∀ u : Y, u * a = a * u → u ^ 3 = 1 → ∃ i j : ℕ, u = a ^ i * w ^ j
  not_conj : ∀ y : Y, y * a * y⁻¹ ≠ a * w

namespace L143Config

variable {Y : Type*} [Group Y] {a w : Y}

theorem orderOf_a (h : L143Config a w) : orderOf a = 3 :=
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  orderOf_eq_prime h.a_pow fun h1 => h.a_not_mem (h1 ▸ Subgroup.one_mem _)

theorem orderOf_w (h : L143Config a w) : orderOf w = 3 :=
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  orderOf_eq_prime h.w_pow h.w_ne

theorem map {Y' : Type*} [Group Y'] (e : Y ≃* Y') (h : L143Config a w) :
    L143Config (e a) (e w) where
  w_mem := Subgroup.mem_center_iff.mpr fun g => by
    rw [← e.apply_symm_apply g, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp h.w_mem]
  w_ne := fun h1 => h.w_ne (e.injective (by rw [h1, map_one]))
  w_pow := by rw [← map_pow, h.w_pow, map_one]
  a_pow := by rw [← map_pow, h.a_pow, map_one]
  a_not_mem := fun ha => h.a_not_mem (Subgroup.mem_center_iff.mpr fun g => e.injective (by
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp ha (e g)))
  threes := by
    intro u hua hu3
    obtain ⟨i, j, hij⟩ := h.threes (e.symm u)
      (e.injective (by simpa using hua)) (by rw [← map_pow, hu3, map_one])
    exact ⟨i, j, by rw [← e.apply_symm_apply u, hij, map_mul, map_pow, map_pow]⟩
  not_conj := by
    intro y hy
    apply h.not_conj (e.symm y)
    apply e.injective
    simpa using hy

theorem pow_eq_one_of_mem_center (h : L143Config a w) {i : ℕ}
    (hi : a ^ i ∈ Subgroup.center Y) : a ^ i = 1 := by
  have hmod : a ^ i = a ^ (i % 3) := by rw [← h.orderOf_a, pow_mod_orderOf]
  rw [hmod] at hi ⊢
  rcases (by omega : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2) with h0 | h1 | h2
  · rw [h0, pow_zero]
  · rw [h1, pow_one] at hi
    exact absurd hi h.a_not_mem
  · rw [h2] at hi
    refine absurd ?_ h.a_not_mem
    have ha : a = (a ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, h.a_pow, one_mul]
    rw [ha]
    exact Subgroup.pow_mem _ hi 2

theorem exists_eq_pow_of_mem_center (h : L143Config a w) {u : Y}
    (hu : u ∈ Subgroup.center Y) (hu3 : u ^ 3 = 1) : ∃ j : ℕ, u = w ^ j := by
  obtain ⟨i, j, rfl⟩ := h.threes _ (Subgroup.mem_center_iff.mp hu a).symm hu3
  refine ⟨j, ?_⟩
  have hai : a ^ i ∈ Subgroup.center Y := by
    rw [← mul_inv_cancel_right (a ^ i) (w ^ j)]
    exact Subgroup.mul_mem _ hu (Subgroup.inv_mem _ (Subgroup.pow_mem _ h.w_mem _))
  rw [h.pow_eq_one_of_mem_center hai, one_mul]

theorem commute_of_comm_mem_center (h : L143Config a w) {x : Y}
    (hx : x * a * x⁻¹ * a⁻¹ ∈ Subgroup.center Y) : x * a = a * x := by
  set c := x * a * x⁻¹ * a⁻¹ with hc
  have hxa : x * a * x⁻¹ = c * a := by rw [hc]; group
  have hca : Commute c a := (Subgroup.mem_center_iff.mp hx a).symm
  have hc3 : c ^ 3 = 1 := by
    have h1 : (x * a * x⁻¹) ^ 3 = x * a ^ 3 * x⁻¹ := conj_pow
    rw [hxa, hca.mul_pow, h.a_pow, mul_one, mul_one, mul_inv_cancel] at h1
    exact h1
  obtain ⟨j, hj⟩ := h.exists_eq_pow_of_mem_center hx hc3
  have hwj : w ^ j = w ^ (j % 3) := by rw [← h.orderOf_w, pow_mod_orderOf]
  have hwc : ∀ g : Y, w * g = g * w := fun g => (Subgroup.mem_center_iff.mp h.w_mem g).symm
  have hw2 : ∀ g : Y, w ^ 2 * g = g * w ^ 2 := fun g =>
    (Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ h.w_mem 2) g).symm
  rcases (by omega : j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2) with h0 | h1 | h2
  · rw [hwj, h0, pow_zero] at hj
    rw [hj, one_mul] at hxa
    calc x * a = x * a * x⁻¹ * x := by group
      _ = a * x := by rw [hxa]
  · exfalso
    rw [hwj, h1, pow_one] at hj
    rw [hj, hwc] at hxa
    exact h.not_conj x hxa
  · exfalso
    rw [hwj, h2] at hj
    apply h.not_conj (x ^ 2)
    calc x ^ 2 * a * (x ^ 2)⁻¹ = x * (x * a * x⁻¹) * x⁻¹ := by rw [sq]; group
      _ = x * (w ^ 2 * a) * x⁻¹ := by rw [hxa, hj]
      _ = w ^ 2 * (x * a * x⁻¹) := by
        rw [← mul_assoc x, ← hw2 x]
        simp only [mul_assoc]
      _ = w ^ 2 * (w ^ 2 * a) := by rw [hxa, hj]
      _ = a * w := by
        rw [← mul_assoc, ← pow_add, show 2 + 2 = 3 + 1 from rfl, pow_succ, h.w_pow, one_mul,
          hwc]

theorem exists_pow_mul_inv_mem_center_of_real [Finite Y] (h : L143Config a w)
    (hZ : Odd (Nat.card (Subgroup.center Y))) {x s : Y}
    (hx : x * a * x⁻¹ * a⁻¹ ∈ Subgroup.center Y) (hx3 : x ^ 3 ∈ Subgroup.center Y)
    (hs : s * x * s⁻¹ * x ∈ Subgroup.center Y) :
    ∃ i : ℕ, a ^ i * x⁻¹ ∈ Subgroup.center Y := by
  have h2 : ¬ 2 ∣ Nat.card (Subgroup.center Y) := by
    rintro ⟨k, hk⟩
    obtain ⟨m, hm⟩ := hZ
    omega
  have hcop : (Nat.card (Subgroup.center Y)).Coprime 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2).symm
  set z₁ : (Subgroup.center Y) := ⟨s * x * s⁻¹ * x, hs⟩ with hz₁
  set t : (Subgroup.center Y) := ⟨x ^ 3, hx3⟩ with ht
  obtain ⟨z₂, hz₂⟩ := (powCoprime hcop).surjective z₁⁻¹
  rw [powCoprime_apply] at hz₂
  have hsx : s * x * s⁻¹ = (z₁ : Y) * x⁻¹ := by
    show s * x * s⁻¹ = s * x * s⁻¹ * x * x⁻¹
    group
  have htt : t * t = z₁ ^ 3 := by
    apply Subtype.ext
    have e1 : s * x ^ 3 * s⁻¹ = (z₁ : Y) ^ 3 * (x ^ 3)⁻¹ := by
      rw [← conj_pow, hsx, Commute.mul_pow (show Commute (z₁ : Y) x⁻¹ from
        (Subgroup.mem_center_iff.mp z₁.2 x⁻¹).symm), inv_pow]
    have e2 : s * x ^ 3 * s⁻¹ = x ^ 3 := by
      rw [Subgroup.mem_center_iff.mp hx3 s]
      group
    rw [e2] at e1
    change x ^ 3 * x ^ 3 = (z₁ : Y) ^ 3
    calc x ^ 3 * x ^ 3 = (z₁ : Y) ^ 3 * (x ^ 3)⁻¹ * x ^ 3 := by rw [← e1]
      _ = (z₁ : Y) ^ 3 := by group
  have htz : Commute t (z₂ ^ 3) :=
    Subtype.ext (Subgroup.mem_center_iff.mp t.2 ((z₂ ^ 3 : (Subgroup.center Y)) : Y)).symm
  have hu2 : (t * z₂ ^ 3) ^ 2 = 1 := by
    rw [htz.mul_pow, ← pow_mul, show 3 * 2 = 2 * 3 from rfl, pow_mul, hz₂, sq, htt, inv_pow,
      mul_inv_cancel]
  have hu1 : t * z₂ ^ 3 = 1 := by
    have hdvd2 : orderOf (t * z₂ ^ 3) ∣ 2 := orderOf_dvd_of_pow_eq_one hu2
    have hdvdZ : orderOf (t * z₂ ^ 3) ∣ Nat.card (Subgroup.center Y) := orderOf_dvd_natCard _
    have hc : Nat.Coprime (orderOf (t * z₂ ^ 3)) 2 := Nat.Coprime.coprime_dvd_left hdvdZ hcop
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hc hdvd2)
  have hz₂c : ∀ g : Y, (z₂ : Y) * g = g * z₂ := fun g =>
    (Subgroup.mem_center_iff.mp z₂.2 g).symm
  have hx'3 : (x * z₂) ^ 3 = 1 := by
    rw [(show Commute x (z₂ : Y) from (hz₂c x).symm).mul_pow]
    have := congrArg Subtype.val hu1
    simpa [ht] using this
  have hx'a : x * z₂ * a * (x * z₂)⁻¹ * a⁻¹ ∈ (Subgroup.center Y) := by
    have e : x * z₂ * a * (x * z₂)⁻¹ * a⁻¹ = x * a * x⁻¹ * a⁻¹ := by
      calc x * z₂ * a * (x * z₂)⁻¹ * a⁻¹ = x * ((z₂ : Y) * a) * (z₂ : Y)⁻¹ * x⁻¹ * a⁻¹ := by
            group
        _ = x * (a * z₂) * (z₂ : Y)⁻¹ * x⁻¹ * a⁻¹ := by rw [hz₂c a]
        _ = x * a * x⁻¹ * a⁻¹ := by group
    rw [e]
    exact hx
  obtain ⟨i, j, hij⟩ := h.threes _ (h.commute_of_comm_mem_center hx'a) hx'3
  refine ⟨i, ?_⟩
  have e : a ^ i * x⁻¹ = x * ((z₂ : Y) * (w ^ j)⁻¹) * x⁻¹ := by
    have hai : a ^ i = x * z₂ * (w ^ j)⁻¹ := by rw [hij]; group
    rw [hai]
    group
  rw [e]
  exact (inferInstance : (Subgroup.center Y).Normal).conj_mem _
    (Subgroup.mul_mem _ z₂.2 (Subgroup.inv_mem _ (Subgroup.pow_mem _ h.w_mem _))) x

theorem false_of_real [Finite Y] (h : L143Config a w) (hZ : Odd (Nat.card (Subgroup.center Y)))
    {y s : Y ⧸ Subgroup.center Y}
    (hya : y * (a : Y ⧸ Subgroup.center Y) = (a : Y ⧸ Subgroup.center Y) * y) (hy3 : y ^ 3 = 1)
    (hy : y ∉ Subgroup.zpowers (a : Y ⧸ Subgroup.center Y)) (hs : s * y * s⁻¹ = y⁻¹) : False := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective s
  have hx : x * a * x⁻¹ * a⁻¹ ∈ Subgroup.center Y := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hya]
    group
  have hx3 : x ^ 3 ∈ Subgroup.center Y := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hy3
  have hs' : s * x * s⁻¹ * x ∈ Subgroup.center Y := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hs, inv_mul_cancel]
  obtain ⟨i, hi⟩ := h.exists_pow_mul_inv_mem_center_of_real hZ hx hx3 hs'
  apply hy
  have hxi : (x : Y ⧸ Subgroup.center Y) = (a : Y ⧸ Subgroup.center Y) ^ i := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_pow, mul_inv_eq_one] at hi
    exact hi.symm
  rw [hxi]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) i

theorem card_le_nine [Finite Y] (h : L143Config a w) (E : Subgroup (Y ⧸ Subgroup.center Y))
    (hEa : ∀ e ∈ E, e * (a : Y ⧸ Subgroup.center Y) = (a : Y ⧸ Subgroup.center Y) * e)
    (hEc : ∀ e ∈ E, ∀ f ∈ E, e * f = f * e) (hE3 : ∀ e ∈ E, e ^ 3 = 1) : Nat.card E ≤ 9 := by
  set F := E.comap (QuotientGroup.mk' (Subgroup.center Y)) with hFdef
  have hmemF : ∀ u : Y, u ∈ F ↔ (u : Y ⧸ (Subgroup.center Y)) ∈ E := fun u => Iff.rfl
  have hF3 : ∀ u ∈ F, u ^ 3 ∈ (Subgroup.center Y) := fun u hu => by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hE3 _ ((hmemF u).mp hu)
  have hFc : ∀ u ∈ F, ∀ v ∈ F, u * v * u⁻¹ * v⁻¹ ∈ (Subgroup.center Y) := fun u hu v hv => by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hEc _ ((hmemF u).mp hu) _ ((hmemF v).mp hv)]
    group
  have hFa : ∀ u ∈ F, u * a = a * u := fun u hu => by
    refine h.commute_of_comm_mem_center ?_
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hEa _ ((hmemF u).mp hu)]
    group
  let φ : F →* Y :=
    { toFun := fun u => (u : Y) ^ 3
      map_one' := by simp
      map_mul' := fun u v => by
        change ((u : Y) * v) ^ 3 = (u : Y) ^ 3 * (v : Y) ^ 3
        exact mul_pow_three_of_central (hFc _ u.2 _ v.2) (hF3 _ v.2) }
  have hrange : Nat.card φ.range ≤ Nat.card (Subgroup.center Y) := by
    apply Subgroup.card_le_of_le
    rintro _ ⟨u, rfl⟩
    show (u : Y) ^ 3 ∈ (Subgroup.center Y)
    exact hF3 _ u.2
  have hker : Nat.card φ.ker ≤ 9 := by
    let g : Fin 3 × Fin 3 → Y := fun p => a ^ (p.1 : ℕ) * w ^ (p.2 : ℕ)
    have hmem : ∀ u : Y, u * a = a * u → u ^ 3 = 1 → u ∈ Set.range g := by
      intro u hua hu3
      obtain ⟨i, j, hij⟩ := h.threes u hua hu3
      refine ⟨(⟨i % 3, Nat.mod_lt _ (by norm_num)⟩, ⟨j % 3, Nat.mod_lt _ (by norm_num)⟩), ?_⟩
      have e1 : a ^ (i % 3) = a ^ i := by rw [← h.orderOf_a, pow_mod_orderOf]
      have e2 : w ^ (j % 3) = w ^ j := by rw [← h.orderOf_w, pow_mod_orderOf]
      change a ^ (i % 3) * w ^ (j % 3) = u
      rw [e1, e2, hij]
    have hinj : Function.Injective (fun u : φ.ker => (⟨((u : F) : Y),
        hmem _ (hFa _ (u : F).2) (MonoidHom.mem_ker.mp u.2)⟩ : Set.range g)) := by
      intro u v huv
      simp only [Subtype.mk.injEq] at huv
      exact Subtype.ext (Subtype.ext huv)
    calc Nat.card φ.ker ≤ Nat.card (Set.range g) := Nat.card_le_card_of_injective _ hinj
      _ ≤ Nat.card (Fin 3 × Fin 3) := Finite.card_range_le g
      _ = 9 := by simp
  have hFcard : Nat.card F = Nat.card E * Nat.card (Subgroup.center Y) := by
    have hidx : F.index = E.index :=
      Subgroup.index_comap_of_surjective (H := E) (QuotientGroup.mk'_surjective (Subgroup.center Y))
    have e1 : Nat.card F * F.index = Nat.card Y := Subgroup.card_mul_index (H := F)
    have e2 : Nat.card E * E.index = Nat.card (Y ⧸ (Subgroup.center Y)) :=
      Subgroup.card_mul_index (H := E)
    have e3 : Nat.card Y = Nat.card (Y ⧸ (Subgroup.center Y)) * Nat.card (Subgroup.center Y) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Y)
    have hpos : 0 < E.index := Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
    rw [hidx] at e1
    have : Nat.card F * E.index = Nat.card E * Nat.card (Subgroup.center Y) * E.index := by
      rw [e1, e3, ← e2]
      ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hZpos : 0 < Nat.card (Subgroup.center Y) := Nat.card_pos
  have hF : Nat.card F = Nat.card φ.ker * Nat.card φ.range :=
    (Subgroup.card_ker_mul_card_range φ).symm
  have : Nat.card E * Nat.card (Subgroup.center Y) ≤ 9 * Nat.card (Subgroup.center Y) := by
    rw [← hFcard, hF]
    exact Nat.mul_le_mul hker hrange
  exact Nat.le_of_mul_le_mul_right this hZpos

end L143Config

@[expose] def L143Row {S : Type*} [Group S] (x : S) : Prop :=
  (∃ y s : S, y * x = x * y ∧ y ^ 3 = 1 ∧ y ∉ Subgroup.zpowers x ∧ s * y * s⁻¹ = y⁻¹) ∨
    ∃ E : Subgroup S, (∀ e ∈ E, e * x = x * e) ∧ (∀ e ∈ E, ∀ f ∈ E, e * f = f * e) ∧
      (∀ e ∈ E, e ^ 3 = 1) ∧ 27 ≤ Nat.card E

@[expose] def L143Rows (S : Type*) [Group S] : Prop :=
  ∀ x : S, x ^ 3 = 1 → x ≠ 1 → L143Row x

theorem L143Row.of_mulEquiv {S S' : Type*} [Group S] [Group S'] (e : S ≃* S') {x : S}
    (h : L143Row (e x)) : L143Row x := by
  rcases h with ⟨y, s, hyx, hy3, hy, hs⟩ | ⟨E, hEx, hEc, hE3, hE⟩
  · refine Or.inl ⟨e.symm y, e.symm s, ?_, ?_, ?_, ?_⟩
    · apply e.injective
      simp [hyx]
    · rw [← map_pow, hy3, map_one]
    · intro hmem
      apply hy
      have := Subgroup.mem_map_of_mem e.toMonoidHom hmem
      rw [MonoidHom.map_zpowers] at this
      simpa using this
    · apply e.injective
      simp [hs]
  · refine Or.inr ⟨E.map e.symm.toMonoidHom, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨u, hu, rfl⟩
      apply e.injective
      simp [hEx u hu]
    · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      apply e.injective
      simp [hEc u hu v hv]
    · rintro _ ⟨u, hu, rfl⟩
      apply e.injective
      simp [hE3 u hu]
    · rwa [Subgroup.card_map_of_injective e.symm.injective]

theorem L143Rows.of_mulEquiv {S S' : Type*} [Group S] [Group S'] (e : S ≃* S')
    (h : L143Rows S') : L143Rows S := fun x hx3 hx1 =>
  L143Row.of_mulEquiv e (h (e x) (by rw [← map_pow, hx3, map_one])
    (fun h1 => hx1 (e.injective (by rw [h1, map_one]))))

theorem L143Config.false_of_rows {Y : Type*} [Group Y] [Finite Y] {a w : Y} (h : L143Config a w)
    (hZ : Odd (Nat.card (Subgroup.center Y))) (hR : L143Rows (Y ⧸ Subgroup.center Y)) : False := by
  have ha3 : (a : Y ⧸ Subgroup.center Y) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, h.a_pow, QuotientGroup.mk_one]
  have ha1 : (a : Y ⧸ Subgroup.center Y) ≠ 1 := fun h1 =>
    h.a_not_mem ((QuotientGroup.eq_one_iff a).mp h1)
  rcases hR _ ha3 ha1 with ⟨y, s, hya, hy3, hy, hs⟩ | ⟨E, hEa, hEc, hE3, hE⟩
  · exact h.false_of_real hZ hya hy3 hy hs
  · have := h.card_le_nine E hEa hEc hE3
    omega

end CFSG.RankThree.PartTwo.Sec15.Sylow155L143
