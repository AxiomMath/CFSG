module

public import Mathlib.GroupTheory.GroupAction.Jordan
public import Mathlib.GroupTheory.Perm.Cycle.Concrete
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.A10Gen

open Equiv Equiv.Perm Subgroup

@[expose] def O1 : Finset (Fin 10) := {0, 1, 2, 3, 4}

@[expose] def O2 : Finset (Fin 10) := {5, 6, 7, 8, 9}

theorem card_O1 : O1.card = 5 := by decide

theorem card_O2 : O2.card = 5 := by decide

theorem O1O2 : ∀ x, x ∈ O1 ∨ x ∈ O2 := by decide

theorem O1_disj : ∀ x, x ∈ O1 → x ∉ O2 := by decide

theorem O2_disj : ∀ x, x ∈ O2 → x ∉ O1 := by decide

theorem alt_two_trans (S : Finset (Fin 10)) (hS : S.card = 5) {x y x' y' : Fin 10}
    (hx : x ∈ S) (hy : y ∈ S) (hx' : x' ∈ S) (hy' : y' ∈ S) (hxy : x ≠ y) (hxy' : x' ≠ y') :
    ∃ t : Perm (Fin 10), t ∈ alternatingGroup (Fin 10) ∧ (∀ i, i ∉ S → t i = i) ∧
      t x = x' ∧ t y = y' := by
  have hcard : Nat.card ↥S = 5 := by simp [hS]
  haveI h3 : MulAction.IsMultiplyPretransitive (alternatingGroup ↥S) ↥S (Nat.card ↥S - 2) :=
    alternatingGroup.isMultiplyPretransitive ↥S
  haveI h2 : MulAction.IsMultiplyPretransitive (alternatingGroup ↥S) ↥S 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := Nat.card ↥S - 2) (by omega) (by omega)
  have h2' : ∀ {a b c d : ↥S}, a ≠ b → c ≠ d →
      ∃ g : alternatingGroup ↥S, g • a = c ∧ g • b = d :=
    fun {_ _ _ _} hab hcd => (MulAction.is_two_pretransitive_iff).1 h2 hab hcd
  obtain ⟨g, hg1, hg2⟩ := @h2' ⟨x, hx⟩ ⟨y, hy⟩ ⟨x', hx'⟩ ⟨y', hy'⟩
    (fun h => hxy (congrArg Subtype.val h)) (fun h => hxy' (congrArg Subtype.val h))
  refine ⟨Equiv.Perm.ofSubtype (g : Perm ↥S), ?_, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_ofSubtype]
    exact Equiv.Perm.mem_alternatingGroup.1 g.2
  · intro i hi
    exact Equiv.Perm.ofSubtype_apply_of_not_mem _ hi
  · have := congrArg Subtype.val hg1
    rw [Equiv.Perm.ofSubtype_apply_of_mem _ hx]
    exact this
  · have := congrArg Subtype.val hg2
    rw [Equiv.Perm.ofSubtype_apply_of_mem _ hy]
    exact this

theorem gen_of_bridge (T : Subgroup (Perm (Fin 10)))
    (h1 : ∀ x ∈ alternatingGroup (Fin 10), (∀ i, i ∉ O1 → x i = i) → x ∈ T)
    (h2 : ∀ x ∈ alternatingGroup (Fin 10), (∀ i, i ∉ O2 → x i = i) → x ∈ T)
    {g : Perm (Fin 10)} (hg : g ∈ T) {a b : Fin 10} (ha : a ∈ O1) (hb : b ∈ O1)
    (hga : g a ∈ O1) (hgb : g b ∈ O2) :
    alternatingGroup (Fin 10) ≤ T := by
  have mv1 : ∀ {x y x' y' : Fin 10}, x ∈ O1 → y ∈ O1 → x' ∈ O1 → y' ∈ O1 → x ≠ y → x' ≠ y' →
      ∃ t ∈ T, (∀ i, i ∉ O1 → t i = i) ∧ t x = x' ∧ t y = y' := by
    intro x y x' y' hx hy hx' hy' hxy hxy'
    obtain ⟨t, ht, hfix, e1, e2⟩ := alt_two_trans O1 card_O1 hx hy hx' hy' hxy hxy'
    exact ⟨t, h1 t ht hfix, hfix, e1, e2⟩
  have mv2 : ∀ {x y x' y' : Fin 10}, x ∈ O2 → y ∈ O2 → x' ∈ O2 → y' ∈ O2 → x ≠ y → x' ≠ y' →
      ∃ t ∈ T, (∀ i, i ∉ O2 → t i = i) ∧ t x = x' ∧ t y = y' := by
    intro x y x' y' hx hy hx' hy' hxy hxy'
    obtain ⟨t, ht, hfix, e1, e2⟩ := alt_two_trans O2 card_O2 hx hy hx' hy' hxy hxy'
    exact ⟨t, h2 t ht hfix, hfix, e1, e2⟩
  have other1 : ∀ x ∈ O1, ∃ y ∈ O1, y ≠ x := by decide
  have other2 : ∀ x ∈ O2, ∃ y ∈ O2, y ≠ x := by decide
  have tr1 : ∀ {x x' : Fin 10}, x ∈ O1 → x' ∈ O1 →
      ∃ t ∈ T, (∀ i, i ∉ O1 → t i = i) ∧ t x = x' := by
    intro x x' hx hx'
    obtain ⟨y, hy, hyx⟩ := other1 x hx
    obtain ⟨y', hy', hyx'⟩ := other1 x' hx'
    obtain ⟨t, ht, hf, e1, -⟩ := mv1 hx hy hx' hy' hyx.symm hyx'.symm
    exact ⟨t, ht, hf, e1⟩
  have tr2 : ∀ {x x' : Fin 10}, x ∈ O2 → x' ∈ O2 →
      ∃ t ∈ T, (∀ i, i ∉ O2 → t i = i) ∧ t x = x' := by
    intro x x' hx hx'
    obtain ⟨y, hy, hyx⟩ := other2 x hx
    obtain ⟨y', hy', hyx'⟩ := other2 x' hx'
    obtain ⟨t, ht, hf, e1, -⟩ := mv2 hx hy hx' hy' hyx.symm hyx'.symm
    exact ⟨t, ht, hf, e1⟩
  have hab : a ≠ b := fun h => by
    subst h
    exact O1_disj _ hga (by simpa using hgb)
  have h0 : (0 : Fin 10) ∈ O1 := by decide
  have h1' : (1 : Fin 10) ∈ O1 := by decide
  have trans : ∀ u v : Fin 10, ∃ t ∈ T, t u = v := by
    have to2 : ∀ {u v : Fin 10}, u ∈ O1 → v ∈ O2 → ∃ t ∈ T, t u = v := by
      intro u v hu hv
      obtain ⟨t₁, ht₁, -, e₁⟩ := tr1 hu hb
      obtain ⟨t₂, ht₂, -, e₂⟩ := tr2 hgb hv
      refine ⟨t₂ * (g * t₁), T.mul_mem ht₂ (T.mul_mem hg ht₁), ?_⟩
      simp [Perm.mul_apply, e₁, e₂]
    intro u v
    rcases O1O2 u with hu | hu <;> rcases O1O2 v with hv | hv
    · obtain ⟨t, ht, -, e⟩ := tr1 hu hv; exact ⟨t, ht, e⟩
    · exact to2 hu hv
    · obtain ⟨t, ht, e⟩ := to2 hv hu
      exact ⟨t⁻¹, T.inv_mem ht, by rw [← e]; simp⟩
    · obtain ⟨t, ht, -, e⟩ := tr2 hu hv; exact ⟨t, ht, e⟩
  have K : ∀ u : Fin 10, u ≠ 0 → ∃ s ∈ T, s 0 = 0 ∧ s u = 1 := by
    intro u hu0
    rcases O1O2 u with hu | hu
    · obtain ⟨t, ht, -, e0, e1⟩ := mv1 h0 hu h0 h1' (fun h => hu0 h.symm) (by decide)
      exact ⟨t, ht, e0, e1⟩
    · obtain ⟨k, hk, hkf, ek0, ek1⟩ := mv1 h0 h1' ha hb (by decide) hab
      obtain ⟨h, hh, hhf, eh⟩ := tr1 hga h0
      obtain ⟨s₁, hs₁, hs₁f, es₁⟩ := tr2 hu hgb
      have hs₂0 : (h * g * k) 0 = 0 := by simp [Perm.mul_apply, ek0, eh]
      have hs₂1 : (h * g * k) 1 = g b := by
        simp only [Perm.mul_apply, ek1]
        exact hhf _ (O2_disj _ hgb)
      refine ⟨(h * g * k)⁻¹ * s₁, T.mul_mem (T.inv_mem (T.mul_mem (T.mul_mem hh hg) hk)) hs₁, ?_, ?_⟩
      · rw [Perm.mul_apply, hs₁f 0 (O1_disj _ h0), Perm.inv_eq_iff_eq, hs₂0]
      · rw [Perm.mul_apply, es₁, Perm.inv_eq_iff_eq, hs₂1]
  have norm : ∀ {x y : Fin 10}, x ≠ y → ∃ t ∈ T, t x = 0 ∧ t y = 1 := by
    intro x y hxy
    obtain ⟨t₁, ht₁, e₁⟩ := trans x 0
    have hne : t₁ y ≠ 0 := fun h => hxy (t₁.injective (by rw [h, e₁])).symm
    obtain ⟨s, hs, e0, e1⟩ := K (t₁ y) hne
    refine ⟨s * t₁, T.mul_mem hs ht₁, ?_, ?_⟩
    · simp [Perm.mul_apply, e₁, e0]
    · simp [Perm.mul_apply, e1]
  haveI h2t : MulAction.IsMultiplyPretransitive T (Fin 10) 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro x y z w hxy hzw
    obtain ⟨t, ht, e1, e2⟩ := norm hxy
    obtain ⟨t', ht', e1', e2'⟩ := norm hzw
    refine ⟨⟨t'⁻¹ * t, T.mul_mem (T.inv_mem ht') ht⟩, ?_, ?_⟩
    · show t'⁻¹ (t x) = z
      rw [e1, Perm.inv_eq_iff_eq]; exact e1'.symm
    · show t'⁻¹ (t y) = w
      rw [e2, Perm.inv_eq_iff_eq]; exact e2'.symm
  have hprim : MulAction.IsPreprimitive T (Fin 10) :=
    MulAction.isPreprimitive_of_is_two_pretransitive h2t
  have c3 : (c[0, 1, 2] : Perm (Fin 10)).IsThreeCycle :=
    _root_.card_support_eq_three_iff.1 (by decide +kernel)
  have c3T : (c[0, 1, 2] : Perm (Fin 10)) ∈ T := by
    refine h1 _ c3.mem_alternatingGroup (fun i hi => ?_)
    revert i; decide +kernel
  exact Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hprim c3 c3T

theorem eq_three_or_seven {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp5 : p ≠ 5)
    (h : p ∣ Nat.card (Perm (Fin 10))) : p = 3 ∨ p = 7 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin] at h
  have hp10 : p ≤ 10 := (Nat.Prime.dvd_factorial hp).1 h
  have h2 := hp.two_le
  interval_cases p
  · exact (hp2 rfl).elim
  · exact Or.inl rfl
  · exact absurd hp (by decide)
  · exact (hp5 rfl).elim
  · exact absurd hp (by decide)
  · exact Or.inr rfl
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)
  · exact absurd hp (by decide)

theorem sign_eq_one_of_pow (σ : Perm (Fin 10)) (h : σ ^ 3 = 1 ∨ σ ^ 7 = 1) : sign σ = 1 := by
  rcases Int.units_eq_one_or (sign σ) with h1 | h1
  · exact h1
  · exfalso
    rcases h with h | h
    · have := congrArg sign h
      rw [map_pow, h1, map_one] at this
      revert this; decide
    · have := congrArg sign h
      rw [map_pow, h1, map_one] at this
      revert this; decide

theorem two_fixed_of_stable (σ : Perm (Fin 10)) (h : σ ^ 3 = 1 ∨ σ ^ 7 = 1) (S : Finset (Fin 10))
    (hS : S.card = 5) (hσS : ∀ x, σ x ∈ S ↔ x ∈ S) :
    ∃ u v, u ∈ S ∧ v ∈ S ∧ u ≠ v ∧ σ u = u ∧ σ v = v := by
  classical
  let f : Perm {x // x ∈ S} := σ.subtypePerm hσS
  have hcardS : Fintype.card {x // x ∈ S} = 5 := by simp [hS]
  have key : 1 < f.supportᶜ.card := by
    have hle : f.supportᶜ.card ≤ 5 := by
      calc f.supportᶜ.card ≤ Fintype.card {x // x ∈ S} := Finset.card_le_univ _
        _ = 5 := hcardS
    rcases h with h | h
    · haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hf : f ^ 3 ^ 1 = 1 := by
        simp only [f, pow_one, Equiv.Perm.subtypePerm_pow, h]; rfl
      have := Equiv.Perm.card_compl_support_modEq hf
      rw [hcardS] at this
      unfold Nat.ModEq at this
      omega
    · haveI : Fact (Nat.Prime 7) := ⟨by decide⟩
      have hf : f ^ 7 ^ 1 = 1 := by
        simp only [f, pow_one, Equiv.Perm.subtypePerm_pow, h]; rfl
      have := Equiv.Perm.card_compl_support_modEq hf
      rw [hcardS] at this
      unfold Nat.ModEq at this
      omega
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 key
  rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at hu hv
  refine ⟨u, v, u.2, v.2, fun h => huv (Subtype.ext h), ?_, ?_⟩
  · exact congrArg Subtype.val hu
  · exact congrArg Subtype.val hv

theorem stable_or_bridge (σ : Perm (Fin 10)) (h : σ ^ 3 = 1 ∨ σ ^ 7 = 1) :
    (∃ a b, a ∈ O1 ∧ b ∈ O1 ∧ σ a ∈ O1 ∧ σ b ∈ O2) ∨ (∀ x, σ x ∈ O1 ↔ x ∈ O1) := by
  by_cases hex : ∃ a ∈ O1, σ a ∈ O1
  · by_cases hbr : ∃ b ∈ O1, σ b ∈ O2
    · obtain ⟨a, ha, hσa⟩ := hex
      obtain ⟨b, hb, hσb⟩ := hbr
      exact Or.inl ⟨a, b, ha, hb, hσa, hσb⟩
    · right
      have hsub : ∀ b ∈ O1, σ b ∈ O1 := fun b hb => by
        by_contra hn
        exact hbr ⟨b, hb, (O1O2 (σ b)).resolve_left hn⟩
      have himg : O1.image σ = O1 := by
        apply Finset.eq_of_subset_of_card_le
        · intro y hy
          obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
          exact hsub b hb
        · rw [Finset.card_image_of_injective _ σ.injective]
      intro x
      refine ⟨fun hx => ?_, hsub x⟩
      rw [← himg] at hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.1 hx
      exact (σ.injective hyx) ▸ hy
  · exfalso
    push Not at hex
    have himg : O1.image σ = O2 := by
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hy
        exact (O1O2 _).resolve_left (hex b hb)
      · rw [Finset.card_image_of_injective _ σ.injective, card_O1, card_O2]
    have hflip2 : ∀ x ∈ O2, σ x ∈ O1 := fun x hx => by
      by_contra hn
      have h2 : σ x ∈ O2 := (O1O2 _).resolve_left hn
      rw [← himg] at h2
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.1 h2
      exact O1_disj y hy ((σ.injective hyx) ▸ hx)
    have flip : ∀ x, σ x ∈ O1 ↔ x ∉ O1 := fun x => by
      rcases O1O2 x with hx | hx
      · exact ⟨fun h => absurd h (hex x hx), fun h => absurd hx h⟩
      · exact ⟨fun _ => O2_disj x hx, fun _ => hflip2 x hx⟩
    have par : ∀ k : ℕ, ∀ x, (σ ^ k) x ∈ O1 ↔ (x ∈ O1 ↔ Even k) := by
      intro k
      induction k with
      | zero => intro x; simp
      | succ k ih =>
        intro x
        rw [pow_succ', Perm.mul_apply, flip, ih x, Nat.even_add_one]
        tauto
    have h0 : (0 : Fin 10) ∈ O1 := by decide
    rcases h with h | h
    · have := par 3 0
      rw [h, Perm.one_apply] at this
      have h1 := this.1 h0
      exact absurd (h1.1 h0) (by decide)
    · have := par 7 0
      rw [h, Perm.one_apply] at this
      have h1 := this.1 h0
      exact absurd (h1.1 h0) (by decide)

theorem exists_bridge (σ : Perm (Fin 10)) (h : σ ^ 3 = 1 ∨ σ ^ 7 = 1) :
    ∃ g : Perm (Fin 10), g ∈ alternatingGroup (Fin 10) ∧ g * σ = σ * g ∧
      ∃ a b, a ∈ O1 ∧ b ∈ O1 ∧ g a ∈ O1 ∧ g b ∈ O2 := by
  rcases stable_or_bridge σ h with ⟨a, b, ha, hb, hσa, hσb⟩ | hst
  · exact ⟨σ, Equiv.Perm.mem_alternatingGroup.2 (sign_eq_one_of_pow σ h), rfl, a, b, ha, hb, hσa,
      hσb⟩
  · have hst2 : ∀ x, σ x ∈ O2 ↔ x ∈ O2 := by
      intro x
      rcases O1O2 x with hx | hx
      · exact ⟨fun h2 => absurd ((hst x).2 hx) (O2_disj _ h2), fun h2 => absurd hx (O2_disj _ h2)⟩
      · refine ⟨fun _ => hx, fun _ => ?_⟩
        rcases O1O2 (σ x) with h1 | h1
        · exact absurd ((hst x).1 h1) (O2_disj _ hx)
        · exact h1
    obtain ⟨u, v, hu, hv, huv, hσu, hσv⟩ := two_fixed_of_stable σ h O1 card_O1 hst
    obtain ⟨w, w', hw, hw', hww', hσw, -⟩ := two_fixed_of_stable σ h O2 card_O2 hst2
    have huw : u ≠ w := fun e => O1_disj u hu (e ▸ hw)
    have hvw : v ≠ w := fun e => O1_disj v hv (e ▸ hw)
    refine ⟨swap u v * swap u w,
      (Equiv.Perm.isThreeCycle_swap_mul_swap_same huv huw hvw).mem_alternatingGroup, ?_, v, u, hv, hu,
      ?_, ?_⟩
    · have e1 : σ * swap u v = swap u v * σ := by rw [mul_swap_eq_swap_mul, hσu, hσv]
      have e2 : σ * swap u w = swap u w * σ := by rw [mul_swap_eq_swap_mul, hσu, hσw]
      exact (calc σ * (swap u v * swap u w) = (σ * swap u v) * swap u w := by rw [mul_assoc]
        _ = swap u v * (σ * swap u w) := by rw [e1, mul_assoc]
        _ = swap u v * (swap u w * σ) := by rw [e2]
        _ = (swap u v * swap u w) * σ := by rw [mul_assoc]).symm
    · have : (swap u v * swap u w) v = u := by
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne huv.symm hvw, swap_apply_right]
      rw [this]; exact hu
    · have : (swap u v * swap u w) u = w := by
        rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne huw.symm hvw.symm]
      rw [this]; exact hw

theorem core_A10 (T : Subgroup ↥(alternatingGroup (Fin 10)))
    (h1 : ∀ x : ↥(alternatingGroup (Fin 10)), (∀ i, i ∉ O1 → (x : Perm (Fin 10)) i = i) → x ∈ T)
    (h2 : ∀ x : ↥(alternatingGroup (Fin 10)), (∀ i, i ∉ O2 → (x : Perm (Fin 10)) i = i) → x ∈ T)
    {σ : ↥(alternatingGroup (Fin 10))} (hσ : σ ^ 3 = 1 ∨ σ ^ 7 = 1)
    (hC : ∀ x : ↥(alternatingGroup (Fin 10)), x * σ = σ * x → x ∈ T) : T = ⊤ := by
  have hσ' : (σ : Perm (Fin 10)) ^ 3 = 1 ∨ (σ : Perm (Fin 10)) ^ 7 = 1 := by
    rcases hσ with h | h
    · exact Or.inl (by simpa using congrArg Subtype.val h)
    · exact Or.inr (by simpa using congrArg Subtype.val h)
  obtain ⟨g, hgA, hgσ, a, b, ha, hb, hga, hgb⟩ := exists_bridge (σ : Perm (Fin 10)) hσ'
  have hgT : (⟨g, hgA⟩ : ↥(alternatingGroup (Fin 10))) ∈ T := hC _ (Subtype.ext hgσ)
  have hbridge := gen_of_bridge (T.map (alternatingGroup (Fin 10)).subtype)
    (fun x hx hfix => ⟨⟨x, hx⟩, h1 ⟨x, hx⟩ hfix, rfl⟩)
    (fun x hx hfix => ⟨⟨x, hx⟩, h2 ⟨x, hx⟩ hfix, rfl⟩)
    (g := g) ⟨⟨g, hgA⟩, hgT, rfl⟩ ha hb hga hgb
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := hbridge x.2
  exact (Subtype.ext hyx : y = x) ▸ hy

theorem exists_orderOf_map_eq_prime {H K : Type*} [Group H] [Group K] {p : ℕ} (hp : p.Prime)
    (hH : IsPGroup p H) (f : H →* K) {q : H} (hq : f q ≠ 1) : ∃ q' : H, orderOf (f q') = p := by
  obtain ⟨k, hk⟩ := hH q
  have hdvd : orderOf (f q) ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hk, map_one])
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hi0 : i ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hi
    exact hq hi
  refine ⟨q ^ p ^ (i - 1), ?_⟩
  rw [map_pow, orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero)
    (by rw [hi]; exact pow_dvd_pow p (Nat.sub_le i 1)), hi, Nat.pow_div (Nat.sub_le i 1) hp.pos]
  have : i - (i - 1) = 1 := by omega
  rw [this, pow_one]

end CFSG.LocalAnalysis.UniquenessCase.UC6.A10Gen
