module

public import CFSG.Sporadic.SuzRecog.LocalRTau
public import CFSG.LocalAnalysis.OddStandard.Seitz77L34Certified

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.SuzRecog.LocalR

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AS81
  CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification

variable {G : Type} [Group G] {z : G} {A R : Subgroup G} {H : Type*} [Group H]

theorem conj_mul (x r s : G) : x * (r * s) * x⁻¹ = (x * r * x⁻¹) * (x * s * x⁻¹) := by group

theorem conj_inj {x a b : G} (h : x * a * x⁻¹ = x * b * x⁻¹) : a = b := by
  have := congrArg (fun y => x⁻¹ * y * x) h
  simpa [mul_assoc] using this

theorem three_dvd_of_pow_conj {b r s₁ s₂ : G} (h1 : b * r * b⁻¹ = s₁) (h2 : b * s₁ * b⁻¹ = s₂)
    (h3 : b * s₂ * b⁻¹ = r) (hs₁ : s₁ ≠ r) (hs₂ : s₂ ≠ r) :
    ∀ k : ℕ, b ^ k * r * (b ^ k)⁻¹ = r → 3 ∣ k := by
  have hb3 : b ^ 3 * r * (b ^ 3)⁻¹ = r := by
    rw [pow_three]
    calc b * (b * b) * r * (b * (b * b))⁻¹ = b * (b * (b * r * b⁻¹) * b⁻¹) * b⁻¹ := by group
      _ = r := by rw [h1, h2, h3]
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    match k, ih, hk with
    | 0, _, _ => exact dvd_zero 3
    | 1, _, hk => exact absurd (by simpa [h1] using hk) hs₁
    | 2, _, hk =>
      have e : b ^ 2 * r * (b ^ 2)⁻¹ = s₂ := by
        rw [sq]
        calc b * b * r * (b * b)⁻¹ = b * (b * r * b⁻¹) * b⁻¹ := by group
          _ = s₂ := by rw [h1, h2]
      exact absurd (e.symm.trans hk) hs₂
    | k + 3, ih, hk =>
      have e : b ^ (k + 3) * r * (b ^ (k + 3))⁻¹ = b ^ k * r * (b ^ k)⁻¹ := by
        calc b ^ (k + 3) * r * (b ^ (k + 3))⁻¹ = b ^ k * (b ^ 3 * r * (b ^ 3)⁻¹) * (b ^ k)⁻¹ := by
              rw [pow_add, mul_inv_rev]; simp only [mul_assoc]
          _ = b ^ k * r * (b ^ k)⁻¹ := by rw [hb3]
      exact (ih k (by omega) (e ▸ hk)).add (dvd_refl 3)

theorem mem_normalizer_of_forall [Finite G] {K : Subgroup G} {g : G}
    (h : ∀ x ∈ K, g * x * g⁻¹ ∈ K) : g ∈ normalizer (K : Set G) := by
  have hmap : K.map (MulAut.conj g).toMonoidHom ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : K.map (MulAut.conj g).toMonoidHom = K :=
    Subgroup.eq_of_le_of_card_ge hmap
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [mem_normalizer_iff]
  intro y
  constructor
  · exact h y
  · intro hy
    rw [← heq] at hy
    obtain ⟨a, ha, hag⟩ := hy
    have : a = y := conj_inj (x := g) hag
    rwa [← this]

theorem exists_mem_ne_of_card_four [Finite G] {R : Subgroup G} (hR : Nat.card R = 4) (r : G) :
    ∃ s ∈ R, s ≠ 1 ∧ s ≠ r := by
  classical
  by_contra h
  push Not at h
  have hsub : (R : Set G) ⊆ ({1, r} : Finset G) := fun x hx => by
    by_cases hx1 : x = 1
    · simp [hx1]
    · simp [h x hx hx1]
  have hle := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset, ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hR] at hle
  have := Finset.card_le_two (a := (1 : G)) (b := r)
  omega

section Norm

variable [Finite G]
  (hc : Comp z A R) (hz : orderOf z = 2)
  (hM : Nat.card (centralizer ({z} : Set G)) = 3317760) (hH : NonCentralSylow z)

include hM hH in
theorem Comp.mem_normalizer_of_conj (hc : Comp z A R) (hz : orderOf z = 2) {r r' g : G}
    (hr : r ∈ R) (hr1 : r ≠ 1) (hr' : r' ∈ R) (hr1' : r' ≠ 1) (hg : g * r * g⁻¹ = r') :
    g ∈ normalizer (A : Set G) := by
  have hmap : A.map (MulAut.conj g).toMonoidHom ≤ A := by
    have e1 := hc.closure_odd_eq hM hH hz hr hr1
    have e2 := hc.closure_odd_eq hM hH hz hr' hr1'
    calc A.map (MulAut.conj g).toMonoidHom
        = (closure {x : G | x ∈ centralizer ({r} : Set G) ∧ Odd (orderOf x)}).map
            (MulAut.conj g).toMonoidHom := by rw [e1]
      _ ≤ closure {x : G | x ∈ centralizer ({r'} : Set G) ∧ Odd (orderOf x)} := ?_
      _ = A := e2
    rw [MonoidHom.map_closure]
    refine closure_mono ?_
    rintro _ ⟨x, ⟨hxr, hxo⟩, rfl⟩
    refine ⟨mem_centralizer_singleton_iff.2 ?_, ?_⟩
    · have h := mem_centralizer_singleton_iff.1 hxr
      show g * x * g⁻¹ * r' = r' * (g * x * g⁻¹)
      rw [← hg]
      calc g * x * g⁻¹ * (g * r * g⁻¹) = g * (x * r) * g⁻¹ := by group
        _ = g * (r * x) * g⁻¹ := by rw [h]
        _ = g * r * g⁻¹ * (g * x * g⁻¹) := by group
    · show Odd (orderOf (MulAut.conj g x))
      rw [MulEquiv.orderOf_eq]
      exact hxo
  have heq : A.map (MulAut.conj g).toMonoidHom = A :=
    Subgroup.eq_of_le_of_card_ge hmap
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [← heq]
    exact ⟨h, hh, rfl⟩
  · intro hh
    rw [← heq] at hh
    obtain ⟨a, ha, hag⟩ := hh
    have : a = h := conj_inj (x := g) hag
    rwa [← this]

include hM hH in
theorem Comp.conj_mem_R_of_conj (hc : Comp z A R) (hz : orderOf z = 2) {r r' g : G}
    (hr : r ∈ R) (hr1 : r ≠ 1) (hr' : r' ∈ R) (hr1' : r' ≠ 1) (hg : g * r * g⁻¹ = r')
    {s : G} (hs : s ∈ R) : g * s * g⁻¹ ∈ R := by
  have hgN := hc.mem_normalizer_of_conj hM hH hz hr hr1 hr' hr1' hg
  rw [← hc.centralizer_inf_eq hM hH hr' hr1']
  refine mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_, ?_⟩
  · rw [← hg, ← conj_mul, ← conj_mul, hc.comm hr hs]
  · rw [mem_centralizer_iff]
    intro a ha
    have ha' : g⁻¹ * a * g⁻¹⁻¹ ∈ A := (mem_normalizer_iff.1 (inv_mem hgN) a).1 ha
    have hca := mem_centralizer_iff.1 (hc.R_le_centralizer hs) _ ha'
    calc a * (g * s * g⁻¹) = g * ((g⁻¹ * a * g⁻¹⁻¹) * s) * g⁻¹ := by group
      _ = g * (s * (g⁻¹ * a * g⁻¹⁻¹)) * g⁻¹ := by rw [hca]
      _ = g * s * g⁻¹ * a := by group

end Norm

section Rho

variable [Finite G]
  (hc : Comp z A R) (hz : orderOf z = 2)
  (hM : Nat.card (centralizer ({z} : Set G)) = 3317760) (hH : NonCentralSylow z)
  {σ : ↥(centralizer ({z} : Set G)) ≃* H} {l : H} {T : Subgroup H}
  (hiff : ∀ t : ↥(centralizer ({z} : Set G)), orderOf t = 2 →
    (¬ IsConj (t : G) z ↔ IsConj (σ t) l))

omit [Finite G] in
include hc hM hiff in
theorem Comp.exists_conj_M {r r' : G} (hr : r ∈ R) (hr1 : r ≠ 1) (hr' : r' ∈ R)
    (hr1' : r' ≠ 1) : ∃ g ∈ centralizer ({z} : Set G), g * r * g⁻¹ = r' := by
  have h1 := (hiff ⟨r, hc.R_le_M hr⟩
    (by rw [Subgroup.orderOf_mk]; exact hc.orderOf_eq_two hr hr1)).1 (hc.not_isConj hM hr)
  have h2 := (hiff ⟨r', hc.R_le_M hr'⟩
    (by rw [Subgroup.orderOf_mk]; exact hc.orderOf_eq_two hr' hr1')).1 (hc.not_isConj hM hr')
  obtain ⟨k, hk⟩ := isConj_iff.1 (h1.trans h2.symm)
  refine ⟨(σ.symm k : G), (σ.symm k).2, ?_⟩
  have e : σ.symm k * ⟨r, hc.R_le_M hr⟩ * (σ.symm k)⁻¹ = ⟨r', hc.R_le_M hr'⟩ :=
    σ.injective (by rw [map_mul, map_mul, map_inv, σ.apply_symm_apply]; exact hk)
  exact congrArg Subtype.val e

include hc hz hM hH hiff in
theorem Comp.exists_cycle {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) :
    ∃ b ∈ centralizer ({z} : Set G), (∀ s ∈ R, b * s * b⁻¹ ∈ R) ∧
      ∃ s₁ s₂ : G, b * r * b⁻¹ = s₁ ∧ b * s₁ * b⁻¹ = s₂ ∧ b * s₂ * b⁻¹ = r ∧ s₁ ≠ r ∧
        s₂ ≠ r := by
  obtain ⟨s, hs, hs1, hsr⟩ := exists_mem_ne_of_card_four hc.card r
  have hrr : r * r = 1 := by rw [← sq]; exact hc.elem.2 r hr
  have hss : s * s = 1 := by rw [← sq]; exact hc.elem.2 s hs
  have hrs : r * s ∈ R := mul_mem hr hs
  have hrs1 : r * s ≠ 1 := fun e => hsr (by
    calc s = r * r * s := by rw [hrr, one_mul]
      _ = r * (r * s) := by group
      _ = r := by rw [e, mul_one])
  have hrsr : r * s ≠ r := fun e => hs1 (by simpa using e)
  have hrss : r * s ≠ s := fun e => hr1 (by simpa using e)
  have hcomm := hc.comm hr hs
  obtain ⟨g₁, hg₁M, hg₁⟩ := hc.exists_conj_M hM hiff hr hr1 hs hs1
  obtain ⟨g₂, hg₂M, hg₂⟩ := hc.exists_conj_M hM hiff hr hr1 hrs hrs1
  have hN₁ : ∀ x ∈ R, g₁ * x * g₁⁻¹ ∈ R := fun x hx =>
    hc.conj_mem_R_of_conj hM hH hz hr hr1 hs hs1 hg₁ hx
  have hN₂ : ∀ x ∈ R, g₂ * x * g₂⁻¹ ∈ R := fun x hx =>
    hc.conj_mem_R_of_conj hM hH hz hr hr1 hrs hrs1 hg₂ hx
  have hcases := fun {u : G} (hu : u ∈ R) => mem_four hc.card hr hs hr1 hs1 hsr hrr hu
  have hne1 : ∀ g x : G, x ≠ 1 → g * x * g⁻¹ ≠ 1 := fun g x hx e => hx (by
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [e]; group)
  by_cases hA : g₁ * s * g₁⁻¹ = r
  · by_cases hB : g₂ * (r * s) * g₂⁻¹ = r
    ·
      have hg₂s : g₂ * s * g₂⁻¹ = s := by
        have e : s = r⁻¹ * (r * s) := by group
        calc g₂ * s * g₂⁻¹ = (g₂ * r * g₂⁻¹)⁻¹ * (g₂ * (r * s) * g₂⁻¹) := by
              conv_lhs => rw [e]
              group
          _ = (r * s)⁻¹ * r := by rw [hg₂, hB]
          _ = s := by
            rw [mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one, ← mul_one s⁻¹, ← hss]
            group
      refine ⟨g₁ * g₂, mul_mem hg₁M hg₂M, fun x hx => ?_, r * s, s, ?_, ?_, ?_, hrsr, hsr⟩
      · have e : g₁ * g₂ * x * (g₁ * g₂)⁻¹ = g₁ * (g₂ * x * g₂⁻¹) * g₁⁻¹ := by group
        rw [e]
        exact hN₁ _ (hN₂ x hx)
      · calc g₁ * g₂ * r * (g₁ * g₂)⁻¹ = g₁ * (g₂ * r * g₂⁻¹) * g₁⁻¹ := by group
          _ = (g₁ * r * g₁⁻¹) * (g₁ * s * g₁⁻¹) := by rw [hg₂, conj_mul]
          _ = r * s := by rw [hg₁, hA, hc.comm hs hr]
      · calc g₁ * g₂ * (r * s) * (g₁ * g₂)⁻¹ = g₁ * (g₂ * (r * s) * g₂⁻¹) * g₁⁻¹ := by group
          _ = s := by rw [hB, hg₁]
      · calc g₁ * g₂ * s * (g₁ * g₂)⁻¹ = g₁ * (g₂ * s * g₂⁻¹) * g₁⁻¹ := by group
          _ = r := by rw [hg₂s, hA]
    ·
      have hrs' : g₂ * (r * s) * g₂⁻¹ = s := by
        rcases hcases (hN₂ _ hrs) with h | h | h | h
        · exact absurd h (hne1 _ _ hrs1)
        · exact absurd h hB
        · exact h
        · exfalso
          exact hrsr (conj_inj (x := g₂) (h.trans hg₂.symm))
      have hs' : g₂ * s * g₂⁻¹ = r := by
        have e : s = r * (r * s) := by rw [← mul_assoc, hrr, one_mul]
        calc g₂ * s * g₂⁻¹ = (g₂ * r * g₂⁻¹) * (g₂ * (r * s) * g₂⁻¹) := by
              conv_lhs => rw [e]
              rw [conj_mul]
          _ = r * s * s := by rw [hg₂, hrs']
          _ = r := by rw [mul_assoc, hss, mul_one]
      exact ⟨g₂, hg₂M, hN₂, r * s, s, hg₂, hrs', hs', hrsr, hsr⟩
  ·
    have hs' : g₁ * s * g₁⁻¹ = r * s := by
      rcases hcases (hN₁ s hs) with h | h | h | h
      · exact absurd h (hne1 _ _ hs1)
      · exact absurd h hA
      · exfalso
        exact hsr (conj_inj (x := g₁) (h.trans hg₁.symm))
      · exact h
    have hrs' : g₁ * (r * s) * g₁⁻¹ = r := by
      rw [conj_mul, hg₁, hs', ← mul_assoc, hc.comm hs hr, mul_assoc, hss, mul_one]
    exact ⟨g₁, hg₁M, hN₁, s, r * s, hg₁, hs', hrs', hsr, hrsr⟩

include hc hz hM hH hiff in
theorem Comp.exists_order_three {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) :
    ∃ y ∈ centralizer ({z} : Set G), orderOf y = 3 ∧ y ∈ normalizer (R : Set G) ∧
      y * r * y⁻¹ ≠ r ∧ y ∈ normalizer (A : Set G) := by
  obtain ⟨b, hbM, hbR, s₁, s₂, h1, h2, h3, hs₁, hs₂⟩ := hc.exists_cycle hz hM hH hiff hr hr1
  have hb0 : orderOf b ≠ 0 := (orderOf_pos b).ne'
  have h3dvd : 3 ∣ orderOf b :=
    three_dvd_of_pow_conj h1 h2 h3 hs₁ hs₂ _ (by rw [pow_orderOf_eq_one]; group)
  have hy3 : orderOf (b ^ (orderOf b / 3)) = 3 := orderOf_pow_orderOf_div hb0 h3dvd
  have hbN : b ∈ normalizer (R : Set G) := mem_normalizer_of_forall hbR
  have hs₁R : s₁ ∈ R := h1 ▸ hbR r hr
  have hs₁1 : s₁ ≠ 1 := fun e => hr1 (by
    rw [e] at h1
    calc r = b⁻¹ * (b * r * b⁻¹) * b := by group
      _ = 1 := by rw [h1]; group)
  have hbA : b ∈ normalizer (A : Set G) :=
    hc.mem_normalizer_of_conj hM hH hz hr hr1 hs₁R hs₁1 h1
  refine ⟨b ^ (orderOf b / 3), pow_mem hbM _, hy3, pow_mem hbN _, fun hfix => ?_,
    pow_mem hbA _⟩
  have hmem : b ^ (orderOf b / 3) ∈ centralizer ({r} : Set G) ⊓ centralizer ({z} : Set G) :=
    ⟨mem_centralizer_singleton_iff.2 (by
      calc b ^ (orderOf b / 3) * r = b ^ (orderOf b / 3) * r * (b ^ (orderOf b / 3))⁻¹ *
            b ^ (orderOf b / 3) := by group
        _ = r * b ^ (orderOf b / 3) := by rw [hfix]), pow_mem hbM _⟩
  obtain ⟨k, hk⟩ := hc.isPGroup_inf hM hH hr hr1 ⟨_, hmem⟩
  have hdvd : orderOf (b ^ (orderOf b / 3)) ∣ 2 ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    have := congrArg Subtype.val hk
    simpa using this
  rw [hy3] at hdvd
  have := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) hdvd)
  omega

include hc hz hM hH hiff in
theorem Comp.mem_centralizer_A (hMF : LocModel l T) {r : G}
    (hr : r ∈ R) (hr1 : r ≠ 1) (hσr : σ ⟨r, hc.R_le_M hr⟩ = l) {y : G}
    (hyM : y ∈ centralizer ({z} : Set G)) (hy3 : orderOf y = 3)
    (hyR : y ∈ normalizer (R : Set G)) (hyr : y * r * y⁻¹ ≠ r)
    (hyA : y ∈ normalizer (A : Set G)) : y ∈ centralizer (A : Set G) := by
  have hZ := hc.center_eq_bot hM hH
  obtain ⟨s, hs, hs1, hsr⟩ := exists_mem_ne_of_card_four hc.card r
  have hrr : r * r = 1 := by rw [← sq]; exact hc.elem.2 r hr
  have hss : s * s = 1 := by rw [← sq]; exact hc.elem.2 s hs
  have hrs1 : r * s ≠ 1 := fun e => hsr (by
    calc s = r * r * s := by rw [hrr, one_mul]
      _ = r * (r * s) := by group
      _ = r := by rw [e, mul_one])
  have hcases := fun {v : G} (hv : v ∈ R) => mem_four hc.card hr hs hr1 hs1 hsr hrr hv
  let rM : ↥(centralizer ({z} : Set G)) := ⟨r, hc.R_le_M hr⟩
  let sM : ↥(centralizer ({z} : Set G)) := ⟨s, hc.R_le_M hs⟩
  let yM : ↥(centralizer ({z} : Set G)) := ⟨y, hyM⟩
  have hne1 : ∀ x : G, x ≠ 1 → y * x * y⁻¹ ≠ 1 := fun x hx e => hx (by
    calc x = y⁻¹ * (y * x * y⁻¹) * y := by group
      _ = 1 := by rw [e]; group)
  have hCV : R ≤ (centralizer ({r} : Set G) ⊓ centralizer ({z} : Set G)) ⊓
      centralizer ((A ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G) := by
    rw [CV_eq hc hz hM hH hiff hr hσr hMF]
    exact le_sup_right
  have huC : σ sM ∈ locC l T := by
    rw [← trS_CV hc hz hM hH hiff hr hσr hMF]
    exact (mem_trS sM.2).2 (hCV hs)
  have huu : σ sM * σ sM = 1 := by
    rw [← map_mul, show sM * sM = 1 from Subtype.ext hss, map_one]
  have hu1 : σ sM ≠ 1 := fun h =>
    hs1 (congrArg Subtype.val (σ.injective (h.trans (map_one σ).symm)))
  have hul : σ sM ≠ l := fun h => hsr (congrArg Subtype.val (σ.injective (h.trans hσr.symm)))
  have hnotT : ∀ x : ↥(centralizer ({z} : Set G)), (x : G) ∈ R → (x : G) ≠ 1 → σ x ∉ T := by
    intro x hx hx1 h
    rw [← trS_T hc hz hM hH hiff hr hσr hMF, mem_trS_iff, MulEquiv.symm_apply_apply] at h
    have h' : (x : G) ∈ A ⊓ R := ⟨h.1, hx⟩
    rw [hc.inf_R_eq_bot hZ, mem_bot] at h'
    exact hx1 h'
  have huT : σ sM ∉ T := hnotT sM hs hs1
  have hluT : l * σ sM ∉ T := by
    rw [← hσr, ← map_mul]
    exact hnotT (rM * sM) (mul_mem hr hs) hrs1
  have hco : Odd (orderOf (σ yM)) := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy3]
    decide
  have hconjM : ∀ x : ↥(centralizer ({z} : Set G)),
      σ (yM * x * yM⁻¹) = σ yM * σ x * (σ yM)⁻¹ := fun x => by
    rw [map_mul, map_mul, map_inv]
  have h1 : σ yM * l * (σ yM)⁻¹ = σ sM ∨ σ yM * l * (σ yM)⁻¹ = l * σ sM := by
    rw [← hσr, ← hconjM]
    rcases hcases ((mem_normalizer_iff.1 hyR r).1 hr) with h | h | h | h
    · exact absurd h (hne1 r hr1)
    · exact absurd h hyr
    · exact Or.inl (congrArg σ (Subtype.ext h))
    · refine Or.inr ?_
      rw [← map_mul]
      exact congrArg σ (Subtype.ext h)
  have h2 : σ yM * σ sM * (σ yM)⁻¹ = l ∨ σ yM * σ sM * (σ yM)⁻¹ = σ sM ∨
      σ yM * σ sM * (σ yM)⁻¹ = l * σ sM := by
    rw [← hσr, ← hconjM]
    rcases hcases ((mem_normalizer_iff.1 hyR s).1 hs) with h | h | h | h
    · exact absurd h (hne1 s hs1)
    · exact Or.inl (congrArg σ (Subtype.ext h))
    · exact Or.inr (Or.inl (congrArg σ (Subtype.ext h)))
    · refine Or.inr (Or.inr ?_)
      rw [← map_mul]
      exact congrArg σ (Subtype.ext h)
  have hcT := hMF.rho (σ sM) huC huu hu1 hul huT hluT (σ yM) hco h1 h2
  have hyT : y ∈ centralizer ((A ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G) := by
    rw [← trS_T hc hz hM hH hiff hr hσr hMF, ← trS_centralizer inf_le_right] at hcT
    exact (mem_trS hyM).1 hcT
  have hF5 := CFSG.OddStandard.Seitz77.centralizer_V_le_of_certificate hc.standard.1.1
    (Classical.choice (PSL3Four.nonempty_equiv_of_stated _ hc.type)) (hc.isSylowOf_T hZ hz)
    ⟨hyA, hyT⟩
  obtain ⟨V₁, V₂, -, -, -, -, he₁, -, -, -, h12inf, -, -, -, -, -⟩ :=
    CFSG.OddStandard.Seitz77.exists_parabolic_radicals_of_isSylowOf hc.odd
      (Classical.choice (PSL3Four.nonempty_equiv_of_stated _ hc.type)) (hc.isSylowOf_T hZ hz)
  have hcommZC : ∀ t ∈ (A ⊓ centralizer ({z} : Set G)) ⊓
      centralizer ((A ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G),
      ∀ c ∈ centralizer (A : Set G), t * c = c * t := fun t ht c hcA =>
    mem_centralizer_iff.1 hcA t ht.1.1
  have hset := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcommZC).2
  have hy' : y ∈ ((((A ⊓ centralizer ({z} : Set G)) ⊓
      centralizer ((A ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G)) ⊔
      centralizer (A : Set G) : Subgroup G) : Set G) := hF5
  rw [hset] at hy'
  obtain ⟨t, ht, c, hcA, htc⟩ := hy'
  have ht2 : t * t = 1 := by
    have htV : t ∈ V₁ := by
      rw [← h12inf] at ht
      exact ht.1
    rw [← sq]
    exact he₁.2 t htV
  have hty : Commute t⁻¹ y :=
    (Commute.inv_left ((mem_centralizer_iff.1 hyT t ht.1)))
  have hc' : t⁻¹ * y = c := by rw [← htc]; group
  have hy4 : y = (t⁻¹ * y) ^ 4 := by
    rw [hty.mul_pow]
    have ht2' : t ^ 2 = 1 := by rw [sq]; exact ht2
    have h4 : t⁻¹ ^ 4 = 1 := by
      rw [inv_pow, show t ^ 4 = (t ^ 2) ^ 2 by rw [← pow_mul], ht2', one_pow, inv_one]
    have hy4' : y ^ 4 = y := by
      rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, ← hy3, pow_orderOf_eq_one, one_mul]
    rw [h4, hy4', one_mul]
  rw [hy4, hc']
  exact pow_mem hcA 4

include hc hz hM hH hiff in
theorem Comp.exists_rho (hMF : LocModel l T) {r : G} (hr : r ∈ R)
    (hr1 : r ≠ 1) (hσr : σ ⟨r, hc.R_le_M hr⟩ = l) :
    ∃ ρ ∈ centralizer (A : Set G) ⊓ centralizer ({z} : Set G), orderOf ρ = 3 ∧
      ρ ∈ normalizer (R : Set G) ∧ ρ * r * ρ⁻¹ ≠ r ∧
      centralizer (A : Set G) = R ⊔ zpowers ρ ∧ Nat.card (centralizer (A : Set G)) = 12 := by
  have hZ := hc.center_eq_bot hM hH
  obtain ⟨y, hyM, hy3, hyR, hyr, hyA⟩ := hc.exists_order_three hz hM hH hiff hr hr1
  have hyC := hc.mem_centralizer_A hz hM hH hiff hMF hr hr1 hσr hyM hy3 hyR hyr hyA
  have h3 : 3 ∣ Nat.card (centralizer (A : Set G)) := by
    have := orderOf_dvd_natCard (⟨y, hyC⟩ : centralizer (A : Set G))
    rwa [Subgroup.orderOf_mk, hy3] at this
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hZ4, -, -, -⟩ :=
    CFSG.OddStandard.Seitz77.exists_parabolic_radicals_of_isSylowOf hc.odd
      (Classical.choice (PSL3Four.nonempty_equiv_of_stated _ hc.type)) (hc.isSylowOf_T hZ hz)
  have hTA : A ⊓ centralizer ({z} : Set G) ≤ A := inf_le_left
  have hle : centralizer (A : Set G) ⊔ ((A ⊓ centralizer ({z} : Set G)) ⊓
      centralizer ((A ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G)) ≤
      centralizer ({z} : Set G) ⊓
        centralizer ((A ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G) :=
    sup_le (le_inf hc.centralizer_le_M (centralizer_le hTA))
      (le_inf (inf_le_left.trans inf_le_right) inf_le_right)
  have hX : Nat.card (centralizer ({z} : Set G) ⊓
      centralizer ((A ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G) : Subgroup G) = 192 := by
    rw [← card_trS (σ := σ) inf_le_left, trS_inf, trS_M, top_inf_eq,
      trS_centralizer inf_le_right, trS_T hc hz hM hH hiff hr hσr hMF, hMF.card_cent_T]
  have hcomm : ∀ c ∈ centralizer (A : Set G), ∀ t ∈ (A ⊓ centralizer ({z} : Set G)) ⊓
      centralizer ((A ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G), c * t = t * c :=
    fun c hcA t ht => (mem_centralizer_iff.1 hcA t ht.1.1).symm
  have hprod := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm).1
  have hbot : centralizer (A : Set G) ⊓ ((A ⊓ centralizer ({z} : Set G)) ⊓
      centralizer ((A ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G)) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxc : (⟨x, hx.2.1.1⟩ : A) ∈ center A := mem_center_iff.2 fun g =>
      Subtype.ext (mem_centralizer_iff.1 hx.1 g g.2)
    rw [hZ, mem_bot] at hxc
    exact mem_bot.2 (congrArg Subtype.val hxc)
  rw [hbot, Subgroup.card_bot, mul_one, hZ4] at hprod
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hprod, hX] at hdvd
  have hsyl := (isSylowOf_iff.1 hc.sylow)
  have hrel := Subgroup.relIndex_mul_card (H := R) (K := centralizer (A : Set G))
  rw [inf_of_le_left hsyl.1, hc.card] at hrel
  have h12 : Nat.card (centralizer (A : Set G)) = 12 := by
    obtain ⟨q, hq⟩ := hdvd
    set m := R.relIndex (centralizer (A : Set G))
    have hm : ¬ 2 ∣ m := hsyl.2.2
    have hmq : m * q = 12 := by
      have : m * 4 * 4 * q = 192 := by rw [hrel]; linarith
      nlinarith
    have hm12 : m ≤ 12 := by
      rcases Nat.eq_zero_or_pos q with hq0 | hq0
      · rw [hq0, mul_zero] at hmq
        omega
      · nlinarith
    have h3m : 3 ∣ m * 4 := hrel ▸ h3
    interval_cases m <;> omega
  have hRy : R ⊔ zpowers y ≤ centralizer (A : Set G) :=
    sup_le hsyl.1 ((zpowers_le).2 hyC)
  have hRy_bot : R ⊓ zpowers y = ⊥ :=
    disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard
      (by rw [hc.card, Nat.card_zpowers, hy3]; norm_num))
  have hprod2 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    ((zpowers_le).2 hyR)
  rw [hRy_bot, Subgroup.card_bot, mul_one, hc.card, Nat.card_zpowers, hy3] at hprod2
  have hCA : centralizer (A : Set G) = R ⊔ zpowers y :=
    (Subgroup.eq_of_le_of_card_ge hRy (by rw [h12, hprod2])).symm
  exact ⟨y, ⟨hyC, hyM⟩, hy3, hyR, hyr, hCA, h12⟩

theorem mem_R_of_sq {R C : Subgroup G} (hRC : R ≤ C) (hCN : C ≤ normalizer (R : Set G))
    (hR : Nat.card R = 4) (hC : Nat.card C = 12) {x : G} (hx : x ∈ C) (hx2 : x * x = 1) :
    x ∈ R := by
  by_contra hxR
  have hxN : zpowers x ≤ normalizer (R : Set G) := (zpowers_le).2 (hCN hx)
  have hx1 : x ≠ 1 := fun h => hxR (h ▸ R.one_mem)
  have hcx : Nat.card (zpowers x) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_two_of_mul_self hx2 hx1
  have hinf : R ⊓ zpowers x = ⊥ := by
    have hle : R ⊓ zpowers x ≤ zpowers x := inf_le_right
    have hne : R ⊓ zpowers x ≠ zpowers x := fun h => hxR (by
      have : x ∈ R ⊓ zpowers x := by rw [h]; exact mem_zpowers x
      exact this.1)
    have hd := Subgroup.card_dvd_of_le hle
    rw [hcx] at hd
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h2
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exact absurd (Subgroup.eq_of_le_of_card_ge hle (by rw [h2, hcx])) hne
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hxN
  rw [hinf, Subgroup.card_bot, mul_one, hR, hcx] at hprod
  have hdvd := Subgroup.card_dvd_of_le (sup_le hRC ((zpowers_le).2 hx))
  rw [hprod, hC] at hdvd
  norm_num at hdvd

include hc hz hM hH in
theorem Comp.normalizer_eq {r : G} (hr : r ∈ R) (hr1 : r ≠ 1) {ρ : G}
    (hρ : ρ ∈ centralizer (A : Set G) ⊓ centralizer ({z} : Set G)) (hρ3 : orderOf ρ = 3)
    (hρR : ρ ∈ normalizer (R : Set G)) (hρr : ρ * r * ρ⁻¹ ≠ r)
    (hCA : centralizer (A : Set G) = R ⊔ zpowers ρ)
    (h12 : Nat.card (centralizer (A : Set G)) = 12) {τ : G}
    (hτr : τ ∈ centralizer ({r} : Set G)) (hτ2 : τ * τ = 1) (hτAR : τ ∉ A ⊔ R)
    (hCr : centralizer ({r} : Set G) = (A ⊔ R) ⊔ zpowers τ) :
    normalizer (R : Set G) = normalizer (A : Set G) ∧
      normalizer (A : Set G) = (A ⊔ centralizer (A : Set G)) ⊔ zpowers τ ∧
      Nat.card (normalizer (A : Set G)) = 483840 := by
  have hZ := hc.center_eq_bot hM hH
  have hCN : centralizer (A : Set G) ≤ normalizer (R : Set G) := by
    rw [hCA]
    exact sup_le Subgroup.le_normalizer ((zpowers_le).2 hρR)
  have h1 : normalizer (R : Set G) ≤ normalizer (A : Set G) := fun g hg => by
    have hgr : g * r * g⁻¹ ∈ R := (mem_normalizer_iff.1 hg r).1 hr
    have hgr1 : g * r * g⁻¹ ≠ 1 := fun e => hr1 (by
      calc r = g⁻¹ * (g * r * g⁻¹) * g := by group
        _ = 1 := by rw [e]; group)
    exact hc.mem_normalizer_of_conj hM hH hz hr hr1 hgr hgr1 rfl
  have h2 : normalizer (A : Set G) ≤ normalizer (R : Set G) := fun g hg => by
    apply mem_normalizer_of_forall
    intro x hx
    have hxC : g * x * g⁻¹ ∈ centralizer (A : Set G) := by
      rw [mem_centralizer_iff]
      intro a ha
      have ha' : g⁻¹ * a * g⁻¹⁻¹ ∈ A := (mem_normalizer_iff.1 (inv_mem hg) a).1 ha
      have hca := mem_centralizer_iff.1 (hc.R_le_centralizer hx) _ ha'
      calc a * (g * x * g⁻¹) = g * ((g⁻¹ * a * g⁻¹⁻¹) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * a * g⁻¹⁻¹)) * g⁻¹ := by rw [hca]
        _ = g * x * g⁻¹ * a := by group
    have hx2 : x * x = 1 := by rw [← sq]; exact hc.elem.2 x hx
    have hgx2 : g * x * g⁻¹ * (g * x * g⁻¹) = 1 := by
      calc g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
        _ = 1 := by rw [hx2]; group
    exact mem_R_of_sq hc.R_le_centralizer hCN hc.card h12 hxC hgx2
  refine ⟨le_antisymm h1 h2, ?_⟩
  have hτN : τ ∈ normalizer (A : Set G) := hc.le_normalizer r hr hr1 hτr
  have hrr : r * r = 1 := by rw [← sq]; exact hc.elem.2 r hr
  have hs₁R : ρ * r * ρ⁻¹ ∈ R := (mem_normalizer_iff.1 hρR r).1 hr
  have hne1 : ∀ g x : G, x ≠ 1 → g * x * g⁻¹ ≠ 1 := fun g x hx e => hx (by
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [e]; group)
  have hs₁1 := hne1 ρ r hr1
  have hs₂ : ρ * (ρ * r * ρ⁻¹) * ρ⁻¹ = r * (ρ * r * ρ⁻¹) := by
    have hmem : ρ * (ρ * r * ρ⁻¹) * ρ⁻¹ ∈ R := (mem_normalizer_iff.1 hρR _).1 hs₁R
    rcases mem_four hc.card hr hs₁R hr1 hs₁1 hρr hrr hmem with h | h | h | h
    · exact absurd h (hne1 _ _ hs₁1)
    · exfalso
      have hρ2 : ρ * ρ ∈ centralizer ({r} : Set G) ⊓ centralizer ({z} : Set G) :=
        ⟨mem_centralizer_singleton_iff.2 (by
          calc ρ * ρ * r = ρ * (ρ * r * ρ⁻¹) * ρ⁻¹ * (ρ * ρ) := by group
            _ = r * (ρ * ρ) := by rw [h]), mul_mem hρ.2 hρ.2⟩
      have hρV : ρ ∈ centralizer ({r} : Set G) ⊓ centralizer ({z} : Set G) := by
        have e : ρ = (ρ * ρ) * (ρ * ρ) := by
          calc ρ = ρ ^ 3 * ρ := by rw [← hρ3, pow_orderOf_eq_one, one_mul]
            _ = (ρ * ρ) * (ρ * ρ) := by rw [pow_three]; group
        rw [e]
        exact mul_mem hρ2 hρ2
      obtain ⟨k, hk⟩ := hc.isPGroup_inf hM hH hr hr1 ⟨_, hρV⟩
      have hdvd : orderOf ρ ∣ 2 ^ k := by
        apply orderOf_dvd_of_pow_eq_one
        have := congrArg Subtype.val hk
        simpa using this
      rw [hρ3] at hdvd
      have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) hdvd
      omega
    · exact absurd (conj_inj (x := ρ) h) hρr
    · exact h
  have horbit : ∀ r' ∈ R, r' ≠ 1 → ∃ c ∈ centralizer (A : Set G), c * r' * c⁻¹ = r := by
    intro r' hr' hr1'
    rcases mem_four hc.card hr hs₁R hr1 hs₁1 hρr hrr hr' with h | h | h | h
    · exact absurd h hr1'
    · exact ⟨1, one_mem _, by rw [h]; group⟩
    · exact ⟨ρ⁻¹, inv_mem hρ.1, by rw [h]; group⟩
    · exact ⟨ρ⁻¹ * ρ⁻¹, mul_mem (inv_mem hρ.1) (inv_mem hρ.1), by rw [h, ← hs₂]; group⟩
  have hNA : normalizer (A : Set G) = (A ⊔ centralizer (A : Set G)) ⊔ zpowers τ := by
    apply le_antisymm
    · intro g hg
      have hgr : g * r * g⁻¹ ∈ R := (mem_normalizer_iff.1 (h2 hg) r).1 hr
      obtain ⟨c, hcA, hc'⟩ := horbit _ hgr (hne1 g r hr1)
      have hcg : c * g ∈ centralizer ({r} : Set G) := mem_centralizer_singleton_iff.2 (by
        calc c * g * r = c * (g * r * g⁻¹) * c⁻¹ * (c * g) := by group
          _ = r * (c * g) := by rw [hc'])
      rw [hCr] at hcg
      have hmono : (A ⊔ R) ⊔ zpowers τ ≤ (A ⊔ centralizer (A : Set G)) ⊔ zpowers τ :=
        sup_le_sup_right (sup_le_sup_left hc.R_le_centralizer A) _
      have e : g = c⁻¹ * (c * g) := by group
      rw [e]
      exact mul_mem (mem_sup_left (mem_sup_right (inv_mem hcA))) (hmono hcg)
    · exact sup_le (sup_le Subgroup.le_normalizer (centralizer_le_normalizer _))
        ((zpowers_le).2 hτN)
  refine ⟨hNA, ?_⟩
  have hcommAC : ∀ x ∈ A, ∀ y ∈ centralizer (A : Set G), x * y = y * x := fun x hx y hy =>
    mem_centralizer_iff.1 hy x hx
  have hAC := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcommAC).1
  have hbot : A ⊓ centralizer (A : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxc : (⟨x, hx.1⟩ : A) ∈ center A := mem_center_iff.2 fun g =>
      Subtype.ext (mem_centralizer_iff.1 hx.2 g g.2)
    rw [hZ, mem_bot] at hxc
    exact mem_bot.2 (congrArg Subtype.val hxc)
  rw [hbot, Subgroup.card_bot, mul_one, hc.card_A hZ, h12] at hAC
  have hτAC : τ ∉ A ⊔ centralizer (A : Set G) := fun h => hτAR (by
    rw [← hc.centralizer_inf_sup_centralizer hM hH hr hr1]
    exact ⟨hτr, h⟩)
  have hτ1 : τ ≠ 1 := fun h => hτAR (h ▸ one_mem _)
  have hτnorm : zpowers τ ≤ normalizer ((A ⊔ centralizer (A : Set G) : Subgroup G) : Set G) := by
    refine (zpowers_le).2 (mem_normalizer_of_forall fun x hx => ?_)
    obtain ⟨a, ha, c, hcA, rfl⟩ := (CFSG.RankThree.PartOne.K1214.mem_sup_centralizer_iff A).1 hx
    rw [conj_mul]
    refine mul_mem (mem_sup_left ((mem_normalizer_iff.1 hτN a).1 ha)) (mem_sup_right ?_)
    rw [mem_centralizer_iff]
    intro b hb
    have hb' : τ⁻¹ * b * τ⁻¹⁻¹ ∈ A := (mem_normalizer_iff.1 (inv_mem hτN) b).1 hb
    have hcb := mem_centralizer_iff.1 hcA _ hb'
    calc b * (τ * c * τ⁻¹) = τ * ((τ⁻¹ * b * τ⁻¹⁻¹) * c) * τ⁻¹ := by group
      _ = τ * (c * (τ⁻¹ * b * τ⁻¹⁻¹)) * τ⁻¹ := by rw [hcb]
      _ = τ * c * τ⁻¹ * b := by group
  have hcτ : Nat.card (zpowers τ) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_two_of_mul_self hτ2 hτ1
  have hinf : (A ⊔ centralizer (A : Set G)) ⊓ zpowers τ = ⊥ := by
    have hle : (A ⊔ centralizer (A : Set G)) ⊓ zpowers τ ≤ zpowers τ := inf_le_right
    have hne : (A ⊔ centralizer (A : Set G)) ⊓ zpowers τ ≠ zpowers τ := fun h => hτAC (by
      have : τ ∈ (A ⊔ centralizer (A : Set G)) ⊓ zpowers τ := by rw [h]; exact mem_zpowers τ
      exact this.1)
    have hd := Subgroup.card_dvd_of_le hle
    rw [hcτ] at hd
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h1 | h2
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exact absurd (Subgroup.eq_of_le_of_card_ge hle (by rw [h2, hcτ])) hne
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hτnorm
  rw [hinf, Subgroup.card_bot, mul_one, hcτ] at hprod
  rw [hNA, hprod]
  omega

end Rho

end CFSG.Sporadic.SuzRecog.LocalR
