module

public import CFSG.Quasithin.SteinbergBSConjugateOrbits

public section

namespace CFSG.Quasithin.SteinbergBS

open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

@[expose] def normalizerConjOn (V A : Subgroup G) (hA : A ≤ normalizer (V : Set G)) :
    A →* MulAut V where
  toFun a :=
    { toFun := fun v => ⟨a * v * (a : G)⁻¹, (mem_normalizer_iff.1 (hA a.2) v).1 v.2⟩
      invFun := fun v => ⟨(a : G)⁻¹ * v * a, by
        have h1 := (mem_normalizer_iff.1 (inv_mem (hA a.2)) v).1 v.2
        rwa [inv_inv] at h1⟩
      left_inv := fun v => Subtype.ext (by simp [mul_assoc])
      right_inv := fun v => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun v w => Subtype.ext (by
        change (a : G) * (v * w) * (a : G)⁻¹ = (a * v * (a : G)⁻¹) * (a * w * (a : G)⁻¹)
        group) }
  map_one' := MulEquiv.ext fun v => Subtype.ext (by
    change ((1 : A) : G) * v * ((1 : A) : G)⁻¹ = v
    simp)
  map_mul' := fun a b => MulEquiv.ext fun v => Subtype.ext (by
    change ((a * b : A) : G) * v * ((a * b : A) : G)⁻¹ = a * (b * v * (b : G)⁻¹) * (a : G)⁻¹
    simp only [Subgroup.coe_mul]
    group)

theorem normalizerConjOn_apply {V A : Subgroup G} (hA : A ≤ normalizer (V : Set G)) (a : A)
    (v : V) : ((normalizerConjOn V A hA a v : V) : G) = a * v * (a : G)⁻¹ := rfl

@[expose] def autFixed (V : Subgroup G) (S : Subgroup (MulAut V)) : Subgroup G where
  carrier := {x | ∃ hx : x ∈ V, ∀ σ ∈ S, σ ⟨x, hx⟩ = ⟨x, hx⟩}
  mul_mem' := fun {x y} ⟨hx, hxS⟩ ⟨hy, hyS⟩ => ⟨V.mul_mem hx hy, fun σ hσ => by
    have h1 : σ (⟨x, hx⟩ * ⟨y, hy⟩) = ⟨x, hx⟩ * ⟨y, hy⟩ := by
      rw [map_mul, hxS σ hσ, hyS σ hσ]
    exact h1⟩
  one_mem' := ⟨V.one_mem, fun σ _ => map_one σ⟩
  inv_mem' := fun {x} ⟨hx, hxS⟩ => ⟨V.inv_mem hx, fun σ hσ => by
    have h1 : σ (⟨x, hx⟩⁻¹) = (⟨x, hx⟩ : V)⁻¹ := by
      rw [map_inv, hxS σ hσ]
    exact h1⟩

theorem conjugate_normalizer_fixed_space_stability [Finite G] {p : ℕ} [hp : Fact p.Prime]
    {V : Subgroup G} [IsElementaryAbelian p V] {r : ℕ}
    (hcent : ∀ E : Subgroup G, E ≤ V → E.relIndex V < p ^ r →
      centralizer (E : Set G) ≤ normalizer (V : Set G))
    (hint : ∀ x : G, V ⊓ conjugate V x ≠ ⊥ → ⁅V, conjugate V x⁆ = ⊥) (g : G) {A : Subgroup G}
    (hAW : A ≤ conjugate V g) (hAN : A ≤ normalizer (V : Set G)) {k : ℕ}
    (hk : A.relIndex (conjugate V g) = p ^ k) (hkr : k < r) (hVA : ⁅V, A⁆ ≠ ⊥) :
    V ⊓ conjugate V g = ⊥ ∧
      V ⊓ normalizer ((conjugate V g : Subgroup G) : Set G) = V ⊓ centralizer (A : Set G) ∧
      V ⊓ normalizer ((conjugate V g : Subgroup G) : Set G) < V ∧
      (∀ B : Subgroup G, B ≤ A → B.relIndex A < p ^ (r - k) →
        V ⊓ centralizer (B : Set G) = V ⊓ normalizer ((conjugate V g : Subgroup G) : Set G)) ∧
      IsElementaryAbelian p (normalizerConjOn V A hAN).range ∧
      (normalizerConjOn V A hAN).range ≠ ⊥ ∧
      p ^ (r - k) ≤ Nat.card (normalizerConjOn V A hAN).range ∧
      autFixed V (normalizerConjOn V A hAN).range =
        V ⊓ normalizer ((conjugate V g : Subgroup G) : Set G) ∧
      ∀ Bb : Subgroup (MulAut V), Bb ≤ (normalizerConjOn V A hAN).range →
        Bb.relIndex (normalizerConjOn V A hAN).range < p ^ (r - k) →
        autFixed V Bb = V ⊓ normalizer ((conjugate V g : Subgroup G) : Set G) := by
  set W := conjugate V g with hW
  set U := V ⊓ normalizer ((W : Subgroup G) : Set G) with hU
  set ρ := normalizerConjOn V A hAN with hρ
  have hp1 := hp.out.one_lt
  have hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : V) ⟨y, hy⟩)
  have hVp : ∀ x ∈ V, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  have hWab : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
    intro x hx y hy
    have h1 := hVab _ (mem_conjugate_iff.1 hx) _ (mem_conjugate_iff.1 hy)
    calc x * y = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by rw [h1]
      _ = y * x := by group
  have hWp : ∀ x ∈ W, x ^ p = 1 := by
    intro x hx
    have h1 := hVp _ (mem_conjugate_iff.1 hx)
    rw [show g * x * g⁻¹ = (MulAut.conj g) x from rfl, ← map_pow] at h1
    exact (MulAut.conj g).injective (h1.trans (map_one _).symm)
  have hVW : V ⊓ W = ⊥ := by
    by_contra h
    exact hVA (commutator_eq_bot_iff_le_centralizer.2
      ((commutator_eq_bot_iff_le_centralizer.1 (hint g h)).trans (centralizer_le hAW)))
  have hUA : U ≤ V ⊓ centralizer (A : Set G) := by
    rintro u ⟨huV, huW⟩
    refine ⟨huV, mem_centralizer_iff.2 fun a ha => ?_⟩
    have hc1 : u * a * u⁻¹ * a⁻¹ ∈ V := by
      have h1 : a * u⁻¹ * a⁻¹ ∈ V := (mem_normalizer_iff.1 (hAN ha) _).1 (V.inv_mem huV)
      have h2 := V.mul_mem huV h1
      rwa [show u * (a * u⁻¹ * a⁻¹) = u * a * u⁻¹ * a⁻¹ by group] at h2
    have hc2 : u * a * u⁻¹ * a⁻¹ ∈ W :=
      W.mul_mem ((mem_normalizer_iff.1 huW a).1 (hAW ha)) (W.inv_mem (hAW ha))
    have hc : u * a * u⁻¹ * a⁻¹ ∈ V ⊓ W := ⟨hc1, hc2⟩
    rw [hVW, mem_bot] at hc
    calc a * u = (u * a * u⁻¹ * a⁻¹)⁻¹ * (u * a) := by group
      _ = u * a := by rw [hc, inv_one, one_mul]
  have hcentW : ∀ E : Subgroup G, E ≤ W → E.relIndex W < p ^ r →
      centralizer (E : Set G) ≤ normalizer ((W : Subgroup G) : Set G) := by
    intro E hEW hEr y hy
    have hE'V : conjugate E g⁻¹ ≤ V := by
      intro x hx
      rw [mem_conjugate_iff, inv_inv] at hx
      have h1 := mem_conjugate_iff.1 (hEW hx)
      rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h1
    have hidx : (conjugate E g⁻¹).relIndex V = E.relIndex W := by
      have hVW' : V = conjugate W g⁻¹ := by
        rw [hW, ← conjugate_mul, mul_inv_cancel, conjugate_one]
      rw [hVW', conjugate, conjugate, relIndex_map_map_of_injective _ _
        (MulAut.conj g⁻¹⁻¹).injective]
    have hgy : g * y * g⁻¹ ∈ centralizer ((conjugate E g⁻¹ : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      intro x hx
      rw [SetLike.mem_coe, mem_conjugate_iff, inv_inv] at hx
      have h1 := mem_centralizer_iff.1 hy _ hx
      calc x * (g * y * g⁻¹) = g * ((g⁻¹ * x * g) * y) * g⁻¹ := by group
        _ = g * (y * (g⁻¹ * x * g)) * g⁻¹ := by rw [h1]
        _ = g * y * g⁻¹ * x := by group
    have h1 := hcent _ hE'V (hidx ▸ hEr) hgy
    rw [mem_normalizer_iff] at h1 ⊢
    intro x
    rw [mem_conjugate_iff, mem_conjugate_iff]
    have h2 := h1 (g * x * g⁻¹)
    rwa [show g * y * g⁻¹ * (g * x * g⁻¹) * (g * y * g⁻¹)⁻¹ = g * (y * x * y⁻¹) * g⁻¹ by group]
      at h2
  have hB : ∀ B : Subgroup G, B ≤ A → B.relIndex A < p ^ (r - k) →
      V ⊓ centralizer (B : Set G) = U := by
    intro B hBA hBidx
    have hBW : B.relIndex W < p ^ r := by
      rw [← relIndex_mul_relIndex B A W hBA hAW, hk]
      calc B.relIndex A * p ^ k < p ^ (r - k) * p ^ k :=
            Nat.mul_lt_mul_of_pos_right hBidx (pow_pos hp.out.pos k)
        _ = p ^ r := by rw [← pow_add, Nat.sub_add_cancel hkr.le]
    refine le_antisymm (fun v hv => ⟨hv.1, hcentW B (hBA.trans hAW) hBW hv.2⟩) ?_
    exact hUA.trans (inf_le_inf_left _ (centralizer_le hBA))
  have hpos : 1 < p ^ (r - k) := Nat.one_lt_pow (by omega) hp1
  have hUA' : U = V ⊓ centralizer (A : Set G) :=
    (hB A le_rfl (by rw [relIndex_self]; exact hpos)).symm
  have hUV : U < V := by
    refine lt_of_le_of_ne inf_le_left fun h => hVA ?_
    rw [commutator_eq_bot_iff_le_centralizer]
    intro v hv
    have hv' : v ∈ U := h ▸ hv
    rw [hUA'] at hv'
    exact hv'.2
  have hρker : ∀ a : A, ρ a = 1 ↔ (a : G) ∈ centralizer (V : Set G) := by
    intro a
    constructor
    · intro h
      rw [mem_centralizer_iff]
      intro v hv
      have h1 := congrArg (fun σ : MulAut V => ((σ ⟨v, hv⟩ : V) : G)) h
      change (a : G) * v * (a : G)⁻¹ = v at h1
      calc v * a = (a : G) * v * (a : G)⁻¹ * a := by rw [h1]
        _ = a * v := by group
    · intro h
      refine MulEquiv.ext fun v => Subtype.ext ?_
      change (a : G) * v * (a : G)⁻¹ = v
      rw [← mem_centralizer_iff.1 h v v.2, mul_inv_cancel_right]
  have hfix : ∀ (S : Subgroup A) (x : G), x ∈ autFixed V (S.map ρ) ↔
      x ∈ V ⊓ centralizer ((S.map A.subtype : Subgroup G) : Set G) := by
    intro S x
    constructor
    · rintro ⟨hx, hxS⟩
      refine ⟨hx, mem_centralizer_iff.2 ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      have h1 := congrArg Subtype.val (hxS (ρ a) ⟨a, ha, rfl⟩)
      change (a : G) * x * (a : G)⁻¹ = x at h1
      calc (a : G) * x = (a : G) * x * (a : G)⁻¹ * a := by group
        _ = x * a := by rw [h1]
    · rintro ⟨hx, hxc⟩
      refine ⟨hx, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      apply Subtype.ext
      change (a : G) * x * (a : G)⁻¹ = x
      rw [mem_centralizer_iff.1 hxc (a : G) ⟨a, ha, rfl⟩, mul_inv_cancel_right]
  have hfixB : ∀ S : Subgroup A, S.index < p ^ (r - k) → autFixed V (S.map ρ) = U := by
    intro S hS
    ext x
    rw [hfix, hB (S.map A.subtype) (map_subtype_le S) (by
      rw [relIndex, ← comap_subtype, comap_map_eq_self_of_injective (subtype_injective A)]
      exact hS)]
  have hAbar_ab : IsElementaryAbelian p ρ.range :=
    { toIsMulCommutative := ⟨⟨fun x y => by
        obtain ⟨a, ha⟩ := x.2
        obtain ⟨b, hb⟩ := y.2
        apply Subtype.ext
        change (x : MulAut V) * y = y * x
        rw [← ha, ← hb, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hWab _ (hAW a.2) _ (hAW b.2))⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
        obtain ⟨a, ha⟩ := x.2
        apply Subtype.ext
        change (x : MulAut V) ^ p = 1
        rw [← ha, ← map_pow]
        have h1 : a ^ p = 1 := Subtype.ext (by
          rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
          exact hWp _ (hAW a.2))
        rw [h1, map_one] }
  have hAbar1 : ρ.range ≠ ⊥ := by
    intro h
    apply hVA
    rw [commutator_eq_bot_iff_le_centralizer, le_centralizer_iff]
    intro a ha
    have h1 : ρ ⟨a, ha⟩ ∈ ρ.range := ⟨⟨a, ha⟩, rfl⟩
    rw [h, mem_bot] at h1
    exact (hρker ⟨a, ha⟩).1 h1
  have hfix_bot : autFixed V ⊥ = V := by
    ext x
    exact ⟨fun ⟨hx, _⟩ => hx, fun hx => ⟨hx, fun σ hσ => by rw [(mem_bot).1 hσ]; rfl⟩⟩
  have hAbar_card : p ^ (r - k) ≤ Nat.card ρ.range := by
    by_contra hlt
    push Not at hlt
    have h1 := hfixB ρ.ker (by rw [index_ker]; exact hlt)
    rw [(Subgroup.map_eq_bot_iff _).2 le_rfl, hfix_bot] at h1
    exact hUV.ne h1.symm
  have hfixAbar : autFixed V ρ.range = U := by
    rw [MonoidHom.range_eq_map]
    exact hfixB ⊤ (by rw [index_top]; exact hpos)
  refine ⟨hVW, hUA', hUV, hB, hAbar_ab, hAbar1, hAbar_card, hfixAbar, fun Bb hBb hBbidx => ?_⟩
  have h1 : (Bb.comap ρ).map ρ = Bb := by
    rw [map_comap_eq, inf_of_le_right hBb]
  rw [← h1]
  exact hfixB _ (by rw [index_comap]; exact hBbidx)

end CFSG.Quasithin.SteinbergBS
