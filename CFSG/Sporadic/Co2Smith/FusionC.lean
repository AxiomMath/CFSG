module

public import CFSG.Sporadic.Co2Smith.G21

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup

universe u

variable {G : Type u} [Group G] {z : G}

theorem exists_swap_norm {g γ : G} (h1 h2 : G) (hh1 : h1 * z = z * h1) (hh2 : h2 * z = z * h2)
    (e1 : h1 * (g⁻¹ * z * g) * h1⁻¹ = γ) (e2 : h2 * (g * z * g⁻¹) * h2⁻¹ = γ) :
    ∃ g' : G, g'⁻¹ * z * g' = γ ∧ g' * z * g'⁻¹ = γ := by
  refine ⟨h2 * g * h1⁻¹, ?_, ?_⟩
  · have hz2 : h2⁻¹ * z * h2 = z := by
      rw [mul_assoc, ← hh2, ← mul_assoc, inv_mul_cancel, one_mul]
    calc (h2 * g * h1⁻¹)⁻¹ * z * (h2 * g * h1⁻¹)
        = h1 * (g⁻¹ * (h2⁻¹ * z * h2) * g) * h1⁻¹ := by group
      _ = γ := by rw [hz2, ← e1]
  · have hz1 : h1⁻¹ * z * h1 = z := by
      rw [mul_assoc, ← hh1, ← mul_assoc, inv_mul_cancel, one_mul]
    calc (h2 * g * h1⁻¹) * z * (h2 * g * h1⁻¹)⁻¹
        = h2 * (g * (h1⁻¹ * z * h1) * g⁻¹) * h2⁻¹ := by group
      _ = γ := by rw [hz1, ← e2]

abbrev cent2 (z γ : G) : Subgroup G := centralizer ({z, γ} : Set G)

theorem mem_cent2 {γ x : G} : x ∈ cent2 z γ ↔ x * z = z * x ∧ x * γ = γ * x := by
  rw [cent2, mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨(h z (Set.mem_insert _ _)).symm, (h γ (Set.mem_insert_of_mem _ rfl)).symm⟩
  · rintro ⟨h1, h2⟩ y hy
    rcases hy with rfl | rfl
    · exact h1.symm
    · exact h2.symm

theorem conj_mem_cent2 {g γ : G} (hg1 : g⁻¹ * z * g = γ) (hg2 : g * z * g⁻¹ = γ) {x : G}
    (hx : x ∈ cent2 z γ) : g⁻¹ * x * g ∈ cent2 z γ := by
  rw [mem_cent2] at hx ⊢
  have hγ : g⁻¹ * γ * g = z := by rw [← hg2]; group
  constructor
  · calc g⁻¹ * x * g * z = g⁻¹ * (x * γ) * g := by rw [← hg2]; group
      _ = g⁻¹ * (γ * x) * g := by rw [hx.2]
      _ = z * (g⁻¹ * x * g) := by rw [← hg2]; group
  · calc g⁻¹ * x * g * γ = g⁻¹ * (x * z) * g := by rw [← hg1]; group
      _ = g⁻¹ * (z * x) * g := by rw [hx.1]
      _ = γ * (g⁻¹ * x * g) := by rw [← hg1]; group

@[expose] def swapAut {g γ : G} (hg1 : g⁻¹ * z * g = γ) (hg2 : g * z * g⁻¹ = γ) :
    cent2 z γ ≃* cent2 z γ where
  toFun x := ⟨g⁻¹ * x * g, conj_mem_cent2 hg1 hg2 x.2⟩
  invFun x := ⟨g * x * g⁻¹, by
    have h1 : (g⁻¹)⁻¹ * z * g⁻¹ = γ := by rw [inv_inv]; exact hg2
    have h2 : g⁻¹ * z * g⁻¹⁻¹ = γ := by rw [inv_inv]; exact hg1
    simpa using conj_mem_cent2 h1 h2 x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem not_swap_of_fixed {γ w : G} (hz2 : orderOf z = 2)
    (h22 : ∀ k : G, ∀ hk : k⁻¹ * z * k ∈ centralizer ({z} : Set G),
      (⟨_, hk⟩ : centralizer ({z} : Set G)) ∈ CFSG.pCore 2 (centralizer ({z} : Set G)) →
        k⁻¹ * z * k = z)
    (hwH : w ∈ centralizer ({z} : Set G))
    (hwE : (⟨w, hwH⟩ : centralizer ({z} : Set G)) ∈ CFSG.pCore 2 (centralizer ({z} : Set G)))
    (hw1 : w ≠ 1) (hwX : w ∈ cent2 z γ) {h : G}
    (hγw : h * (γ * w) * h⁻¹ = γ) (hfix : ∀ α : cent2 z γ ≃* cent2 z γ, α ⟨w, hwX⟩ = ⟨w, hwX⟩)
    {g : G} (hg1 : g⁻¹ * z * g = γ) (hg2 : g * z * g⁻¹ = γ) : False := by
  have hw : g⁻¹ * w * g = w := congrArg Subtype.val (hfix (swapAut hg1 hg2))
  have hγ : g⁻¹ * γ * g = z := by rw [← hg2]; group
  have hw' : g * w * g⁻¹ = w := by
    calc g * w * g⁻¹ = g * (g⁻¹ * w * g) * g⁻¹ := by rw [hw]
      _ = w := by group
  set k := g⁻¹ * h * g
  have hk : k * (z * w) * k⁻¹ = z := by
    calc k * (z * w) * k⁻¹ = g⁻¹ * (h * ((g * z * g⁻¹) * (g * w * g⁻¹)) * h⁻¹) * g := by
          simp only [k]; group
      _ = z := by rw [hw', hg2, hγw, hγ]
  have hzw : k⁻¹ * z * k = z * w :=
    calc k⁻¹ * z * k = k⁻¹ * (k * (z * w) * k⁻¹) * k := by rw [hk]
      _ = z * w := by group
  have hmem : k⁻¹ * z * k ∈ centralizer ({z} : Set G) := by
    rw [hzw]
    exact (centralizer ({z} : Set G)).mul_mem (mem_centralizer_singleton_iff.mpr rfl) hwH
  have hE : (⟨_, hmem⟩ : centralizer ({z} : Set G)) ∈
      CFSG.pCore 2 (centralizer ({z} : Set G)) := by
    have e : (⟨_, hmem⟩ : centralizer ({z} : Set G)) = zC z * ⟨w, hwH⟩ := Subtype.ext hzw
    rw [e]
    exact Subgroup.mul_mem _ (zC_mem_pCore hz2) hwE
  have := h22 k hmem hE
  rw [hzw] at this
  exact hw1 (by simpa using this)

@[expose] noncomputable def sqrtIn {X : Type*} [Group X] (y : X) : ℕ :=
  Nat.card {u : X // u * u = y}

theorem sqrtIn_mulEquiv {X : Type*} [Group X] (α : X ≃* X) (y : X) : sqrtIn (α y) = sqrtIn y := by
  unfold sqrtIn
  refine (Nat.card_congr (α.toEquiv.subtypeEquiv fun u => ?_)).symm
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, ← map_mul, α.injective.eq_iff]

theorem mem_map_conj_inv {D : Subgroup G} {g y : G} :
    y ∈ D.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * y * g⁻¹ ∈ D := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨d, hd, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hd
  · intro hy
    exact ⟨g * y * g⁻¹, hy, by simp [mul_assoc]⟩

theorem mem_map_conj {D : Subgroup G} {g y : G} :
    y ∈ D.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ D := by
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨d, hd, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hd
  · intro hy
    exact ⟨g⁻¹ * y * g, hy, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem false_of_D0_disj [Finite G] {X : Subgroup G} {g : G}
    (hκX : ∀ x ∈ X, g⁻¹ * x * g ∈ X) (hκX' : ∀ x ∈ X, g * x * g⁻¹ ∈ X)
    (D : Subgroup G) (hDX : D ≤ X) (hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a)
    (hXD : ∀ x ∈ X, ∀ d ∈ D, x * d * x⁻¹ ∈ D)
    (D₀ : Subgroup G) (hmemD₀ : ∀ y, y ∈ D₀ ↔ g * y * g⁻¹ ∈ D) (hD₀X : ∀ y ∈ D₀, y ∈ X)
    (hXD₀ : ∀ x ∈ X, ∀ y ∈ D₀, x * y * x⁻¹ ∈ D₀) (hcase : D ⊓ D₀ = ⊥)
    (hA : Nat.card (centralizer (D : Set G) ⊓ X : Subgroup G) ≤ Nat.card D ^ 2)
    (hZD : Nat.card {d : G // d ∈ D ∧ ∀ x ∈ X, x * d = d * x} ≤ 2)
    (hZA : 8 ≤ Nat.card {a : G // a ∈ centralizer (D : Set G) ⊓ X ∧
      ∀ x ∈ X, x * a = a * x}) : False := by
  have hc1 : ∀ y : G, g * (g⁻¹ * y * g) * g⁻¹ = y := fun y => by group
  have hc2 : ∀ y : G, g⁻¹ * (g * y * g⁻¹) * g = y := fun y => by group
  have hcomm : ∀ d ∈ D, ∀ e ∈ D₀, d * e = e * d := by
    intro d hd e he
    have h1 : d * e * d⁻¹ * e⁻¹ ∈ D := by
      have := hXD e (hD₀X e he) d⁻¹ (D.inv_mem hd)
      rw [show d * e * d⁻¹ * e⁻¹ = d * (e * d⁻¹ * e⁻¹) by group]
      exact D.mul_mem hd this
    have h2 : d * e * d⁻¹ * e⁻¹ ∈ D₀ := D₀.mul_mem (hXD₀ d (hDX hd) e he) (D₀.inv_mem he)
    have h3 : d * e * d⁻¹ * e⁻¹ ∈ D ⊓ D₀ := Subgroup.mem_inf.mpr ⟨h1, h2⟩
    rw [hcase, Subgroup.mem_bot] at h3
    calc d * e = (d * e * d⁻¹ * e⁻¹) * (e * d) := by group
      _ = e * d := by rw [h3, one_mul]
  have hinj : ∀ d ∈ D, ∀ d' ∈ D, ∀ e ∈ D₀, ∀ e' ∈ D₀, d * e = d' * e' → d = d' ∧ e = e' := by
    intro d hd d' hd' e he e' he' h
    have h1 : d'⁻¹ * d = e' * e⁻¹ := by
      calc d'⁻¹ * d = d'⁻¹ * (d * e) * e⁻¹ := by group
        _ = d'⁻¹ * (d' * e') * e⁻¹ := by rw [h]
        _ = e' * e⁻¹ := by group
    have h2 : d'⁻¹ * d ∈ D ⊓ D₀ := Subgroup.mem_inf.mpr ⟨D.mul_mem (D.inv_mem hd') hd,
      by rw [h1]; exact D₀.mul_mem he' (D₀.inv_mem he)⟩
    rw [hcase, Subgroup.mem_bot, inv_mul_eq_one] at h2
    subst h2
    exact ⟨rfl, mul_left_cancel h⟩
  have hcardD₀ : Nat.card D₀ = Nat.card D := Nat.card_congr
    { toFun := fun y => ⟨g * y * g⁻¹, (hmemD₀ y).mp y.2⟩
      invFun := fun d => ⟨g⁻¹ * d * g, (hmemD₀ _).mpr (by rw [hc1]; exact d.2)⟩
      left_inv := fun y => Subtype.ext (hc2 y)
      right_inv := fun d => Subtype.ext (hc1 d) }
  let μ : D × D₀ → (centralizer (D : Set G) ⊓ X : Subgroup G) := fun p =>
    ⟨p.1 * p.2, Subgroup.mem_inf.mpr ⟨mem_centralizer_iff.mpr fun b hb => by
      rw [← mul_assoc, hDab b hb _ p.1.2, mul_assoc, hcomm b hb _ p.2.2, ← mul_assoc],
      X.mul_mem (hDX p.1.2) (hD₀X _ p.2.2)⟩⟩
  have hμinj : Function.Injective μ := by
    rintro ⟨⟨d, hd⟩, ⟨e, he⟩⟩ ⟨⟨d', hd'⟩, ⟨e', he'⟩⟩ h
    obtain ⟨h1, h2⟩ := hinj d hd d' hd' e he e' he' (congrArg Subtype.val h)
    subst h1
    subst h2
    rfl
  have hμbij : Function.Bijective μ := hμinj.bijective_of_nat_card_le (by
    rw [Nat.card_prod, hcardD₀, ← sq]
    exact hA)
  have hcent : ∀ d ∈ D, ∀ e ∈ D₀, (∀ x ∈ X, x * (d * e) = d * e * x) →
      (∀ x ∈ X, x * d = d * x) ∧ (∀ x ∈ X, x * e = e * x) := by
    intro d hd e he ha
    have key : ∀ x ∈ X, x * d * x⁻¹ = d ∧ x * e * x⁻¹ = e := by
      intro x hx
      refine hinj _ (hXD x hx d hd) _ hd _ (hXD₀ x hx e he) _ he ?_
      calc x * d * x⁻¹ * (x * e * x⁻¹) = x * (d * e) * x⁻¹ := by group
        _ = d * e := by rw [ha x hx, mul_inv_cancel_right]
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · calc x * d = (x * d * x⁻¹) * x := by group
        _ = d * x := by rw [(key x hx).1]
    · calc x * e = (x * e * x⁻¹) * x := by group
        _ = e * x := by rw [(key x hx).2]
  have hZ : Nat.card {a : G // a ∈ centralizer (D : Set G) ⊓ X ∧ ∀ x ∈ X, x * a = a * x} ≤
      Nat.card ({d : G // d ∈ D ∧ ∀ x ∈ X, x * d = d * x} ×
        {e : G // e ∈ D₀ ∧ ∀ x ∈ X, x * e = e * x}) := by
    refine Nat.card_le_card_of_surjective
      (fun q => ⟨q.1.1 * q.2.1, (μ (⟨q.1.1, q.1.2.1⟩, ⟨q.2.1, q.2.2.1⟩)).2, fun x hx => ?_⟩) ?_
    · rw [← mul_assoc, q.1.2.2 x hx, mul_assoc, q.2.2.2 x hx, mul_assoc]
    · rintro ⟨a, ha, hc⟩
      obtain ⟨⟨d, e⟩, hp⟩ := hμbij.2 ⟨a, ha⟩
      have hde : (d : G) * e = a := congrArg Subtype.val hp
      obtain ⟨hd, he⟩ := hcent d d.2 e e.2 (by rw [hde]; exact hc)
      exact ⟨(⟨(d : G), d.2, hd⟩, ⟨(e : G), e.2, he⟩), Subtype.ext hde⟩
  have hZD₀ : Nat.card {e : G // e ∈ D₀ ∧ ∀ x ∈ X, x * e = e * x} =
      Nat.card {d : G // d ∈ D ∧ ∀ x ∈ X, x * d = d * x} := by
    refine Nat.card_congr
      { toFun := fun e => ⟨g * e.1 * g⁻¹, (hmemD₀ e.1).mp e.2.1, fun x hx => ?_⟩
        invFun := fun d => ⟨g⁻¹ * d.1 * g, (hmemD₀ _).mpr (by rw [hc1]; exact d.2.1),
          fun x hx => ?_⟩
        left_inv := fun e => Subtype.ext (hc2 e.1)
        right_inv := fun d => Subtype.ext (hc1 d.1) }
    · have := e.2.2 _ (hκX x hx)
      calc x * (g * e.1 * g⁻¹) = g * ((g⁻¹ * x * g) * e.1) * g⁻¹ := by group
        _ = g * (e.1 * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
        _ = g * e.1 * g⁻¹ * x := by group
    · have := d.2.2 _ (hκX' x hx)
      calc x * (g⁻¹ * d.1 * g) = g⁻¹ * ((g * x * g⁻¹) * d.1) * g := by group
        _ = g⁻¹ * (d.1 * (g * x * g⁻¹)) * g := by rw [this]
        _ = g⁻¹ * d.1 * g * x := by group
  rw [Nat.card_prod, hZD₀] at hZ
  exact absurd (hZA.trans (hZ.trans (Nat.mul_le_mul hZD hZD))) (by norm_num)

theorem false_of_D0_meet {γ g : G} (hg1 : g⁻¹ * z * g = γ) (hg2 : g * z * g⁻¹ = γ)
    {X : Subgroup G} (hκX : ∀ x ∈ X, g⁻¹ * x * g ∈ X)
    (D : Subgroup G) (hXD : ∀ x ∈ X, ∀ d ∈ D, x * d * x⁻¹ ∈ D) (hγD : γ ∉ D)
    (hE : ∀ k : G, ∀ d ∈ D, k⁻¹ * z * k = z * d → d = 1)
    (hmin : ∀ N : Subgroup G, N ≤ D → (∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) → N ≠ ⊥ →
      z ∉ N → ∃ d ∈ N, d ≠ 1 ∧ ∃ h : G, h * (γ * d) * h⁻¹ = γ)
    (D₀ : Subgroup G) (hmemD₀ : ∀ y, y ∈ D₀ ↔ g * y * g⁻¹ ∈ D)
    (hXD₀ : ∀ x ∈ X, ∀ y ∈ D₀, x * y * x⁻¹ ∈ D₀) (hcase : D ⊓ D₀ ≠ ⊥) : False := by
  have hc1 : ∀ y : G, g * (g⁻¹ * y * g) * g⁻¹ = y := fun y => by group
  have hc2 : ∀ y : G, g⁻¹ * (g * y * g⁻¹) * g = y := fun y => by group
  obtain ⟨N, hmemN⟩ : ∃ N : Subgroup G, ∀ y, y ∈ N ↔ g⁻¹ * y * g ∈ D ⊓ D₀ :=
    ⟨(D ⊓ D₀).map (MulAut.conj g).toMonoidHom, fun y => mem_map_conj⟩
  have hND : N ≤ D := by
    intro y hy
    have := (hmemD₀ _).mp (Subgroup.mem_inf.mp ((hmemN y).mp hy)).2
    rwa [hc1] at this
  have hNX : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N := by
    intro x hx n hn
    rw [hmemN] at hn ⊢
    have hx' := hκX x hx
    have e : g⁻¹ * (x * n * x⁻¹) * g = (g⁻¹ * x * g) * (g⁻¹ * n * g) * (g⁻¹ * x * g)⁻¹ := by
      group
    rw [e]
    exact Subgroup.mem_inf.mpr ⟨hXD _ hx' _ (Subgroup.mem_inf.mp hn).1,
      hXD₀ _ hx' _ (Subgroup.mem_inf.mp hn).2⟩
  have hN : N ≠ ⊥ := by
    intro h
    apply hcase
    rw [eq_bot_iff]
    intro m hm
    have : g * m * g⁻¹ ∈ N := (hmemN _).mpr (by rw [hc2]; exact hm)
    rw [h, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot, ← hc2 m, this]
    group
  have hzN : z ∉ N := by
    intro h
    apply hγD
    have := (Subgroup.mem_inf.mp ((hmemN z).mp h)).1
    rwa [hg1] at this
  obtain ⟨d, hdN, hd1, h, hh⟩ := hmin N hND hNX hN hzN
  have hκd : g⁻¹ * d * g ∈ D := (Subgroup.mem_inf.mp ((hmemN d).mp hdN)).1
  have hγ : g⁻¹ * γ * g = z := by rw [← hg2]; group
  have e : (g⁻¹ * h * g)⁻¹ * z * (g⁻¹ * h * g) = z * (g⁻¹ * d * g) := by
    calc (g⁻¹ * h * g)⁻¹ * z * (g⁻¹ * h * g)
        = (g⁻¹ * h * g)⁻¹ * (g⁻¹ * (h * ((g * z * g⁻¹) * d) * h⁻¹) * g) * (g⁻¹ * h * g) := by
          rw [hg2, hh, hγ]
      _ = z * (g⁻¹ * d * g) := by group
  apply hd1
  rw [← hc1 d, hE _ _ hκd e]
  group

theorem false_of_D0 [Finite G] {γ g : G} (hg1 : g⁻¹ * z * g = γ) (hg2 : g * z * g⁻¹ = γ)
    (D : Subgroup G) (hDX : D ≤ cent2 z γ) (hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a)
    (hXD : ∀ x ∈ cent2 z γ, ∀ d ∈ D, x * d * x⁻¹ ∈ D) (hγD : γ ∉ D)
    (hE : ∀ k : G, ∀ d ∈ D, k⁻¹ * z * k = z * d → d = 1)
    (hmin : ∀ N : Subgroup G, N ≤ D → (∀ x ∈ cent2 z γ, ∀ n ∈ N, x * n * x⁻¹ ∈ N) → N ≠ ⊥ →
      z ∉ N → ∃ d ∈ N, d ≠ 1 ∧ ∃ h : G, h * (γ * d) * h⁻¹ = γ)
    (hA : Nat.card (centralizer (D : Set G) ⊓ cent2 z γ : Subgroup G) ≤ Nat.card D ^ 2)
    (hZD : Nat.card {d : G // d ∈ D ∧ ∀ x ∈ cent2 z γ, x * d = d * x} ≤ 2)
    (hZA : 8 ≤ Nat.card {a : G // a ∈ centralizer (D : Set G) ⊓ cent2 z γ ∧
      ∀ x ∈ cent2 z γ, x * a = a * x}) : False := by
  have hκX : ∀ x ∈ cent2 z γ, g⁻¹ * x * g ∈ cent2 z γ := fun x hx => conj_mem_cent2 hg1 hg2 hx
  have hκX' : ∀ x ∈ cent2 z γ, g * x * g⁻¹ ∈ cent2 z γ := by
    intro x hx
    have h1 : (g⁻¹)⁻¹ * z * g⁻¹ = γ := by rw [inv_inv]; exact hg2
    have h2 : g⁻¹ * z * g⁻¹⁻¹ = γ := by rw [inv_inv]; exact hg1
    simpa using conj_mem_cent2 h1 h2 hx
  have hc2 : ∀ y : G, g⁻¹ * (g * y * g⁻¹) * g = y := fun y => by group
  obtain ⟨D₀, hmemD₀⟩ : ∃ D₀ : Subgroup G, ∀ y, y ∈ D₀ ↔ g * y * g⁻¹ ∈ D :=
    ⟨D.map (MulAut.conj g⁻¹).toMonoidHom, fun y => mem_map_conj_inv⟩
  have hD₀X : ∀ y ∈ D₀, y ∈ cent2 z γ := by
    intro y hy
    have := hκX _ (hDX ((hmemD₀ y).mp hy))
    rwa [hc2] at this
  have hXD₀ : ∀ x ∈ cent2 z γ, ∀ y ∈ D₀, x * y * x⁻¹ ∈ D₀ := by
    intro x hx y hy
    rw [hmemD₀] at hy ⊢
    have e : g * (x * y * x⁻¹) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ := by
      group
    rw [e]
    exact hXD _ (hκX' x hx) _ hy
  by_cases hcase : D ⊓ D₀ = ⊥
  · exact false_of_D0_disj hκX hκX' D hDX hDab hXD D₀ hmemD₀ hD₀X hXD₀ hcase hA hZD hZA
  · exact false_of_D0_meet hg1 hg2 hκX D hXD hγD hE hmin D₀ hmemD₀ hXD₀ hcase

end CFSG.Sporadic.Co2Smith
