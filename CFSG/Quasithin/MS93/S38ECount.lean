module

public import CFSG.Quasithin.Background.G6Basic

public section

namespace CFSG.Quasithin.MS93.S38E

open CFSG.Quasithin
open scoped commutatorElement

variable {Y : Type*} [CommGroup Y]

@[expose] def Stab (E : Subgroup (MulAut Y)) (W : Subgroup Y) : Prop := ∀ e ∈ E, ∀ w ∈ W, e w ∈ W

@[expose] def fixRel (E : Subgroup (MulAut Y)) (W N : Subgroup Y) : Subgroup Y where
  carrier := {w | w ∈ W ∧ ∀ e ∈ E, e w * w⁻¹ ∈ N}
  one_mem' := ⟨W.one_mem, fun e _ => by simp [N.one_mem]⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨W.mul_mem ha hb, fun e he => ?_⟩
    have h : e (a * b) * (a * b)⁻¹ = (e a * a⁻¹) * (e b * b⁻¹) := by
      rw [map_mul, mul_inv]
      ac_rfl
    rw [h]
    exact N.mul_mem (ha' e he) (hb' e he)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨W.inv_mem ha, fun e he => ?_⟩
    have h : e a⁻¹ * a⁻¹⁻¹ = (e a * a⁻¹)⁻¹ := by
      rw [map_inv, inv_inv, mul_inv, inv_inv]
    rw [h]
    exact N.inv_mem (ha' e he)

theorem mem_fixRel {E : Subgroup (MulAut Y)} {W N : Subgroup Y} {w : Y} :
    w ∈ fixRel E W N ↔ w ∈ W ∧ ∀ e ∈ E, e w * w⁻¹ ∈ N := Iff.rfl

theorem fixRel_le (E : Subgroup (MulAut Y)) (W N : Subgroup Y) : fixRel E W N ≤ W :=
  fun _ hw => hw.1

theorem fixRel_mono {E : Subgroup (MulAut Y)} {W N N' : Subgroup Y} (h : N ≤ N') :
    fixRel E W N ≤ fixRel E W N' := fun _ hw => ⟨hw.1, fun e he => h (hw.2 e he)⟩

theorem commOn_le {E : Subgroup (MulAut Y)} {W : Subgroup Y} (hW : Stab E W) :
    G6.commOn E W ≤ W := by
  rw [G6.commOn, Subgroup.closure_le]
  rintro _ ⟨e, he, w, hw, rfl⟩
  exact W.mul_mem (hW e he w hw) (W.inv_mem hw)

theorem commOn_mono {E : Subgroup (MulAut Y)} {W W' : Subgroup Y} (h : W ≤ W') :
    G6.commOn E W ≤ G6.commOn E W' := by
  rw [G6.commOn, G6.commOn]
  refine Subgroup.closure_mono ?_
  rintro _ ⟨e, he, w, hw, rfl⟩
  exact ⟨e, he, w, h hw, rfl⟩

theorem mem_commOn_of {E : Subgroup (MulAut Y)} {W : Subgroup Y} {e : MulAut Y} (he : e ∈ E)
    {w : Y} (hw : w ∈ W) : e w * w⁻¹ ∈ G6.commOn E W :=
  Subgroup.subset_closure ⟨e, he, w, hw, rfl⟩

theorem le_fixRel {E : Subgroup (MulAut Y)} {W W' : Subgroup Y} (hW' : Stab E W') (h : W' ≤ W) :
    W' ≤ fixRel E W W' :=
  fun w hw => ⟨h hw, fun e he => W'.mul_mem (hW' e he w hw) (W'.inv_mem hw)⟩

theorem fixRel_inf {E : Subgroup (MulAut Y)} {W W' N : Subgroup Y} (h : W' ≤ W) :
    fixRel E W N ⊓ W' = fixRel E W' N := by
  ext w
  simp only [Subgroup.mem_inf, mem_fixRel]
  constructor
  · rintro ⟨⟨-, h1⟩, h2⟩
    exact ⟨h2, h1⟩
  · rintro ⟨h2, h1⟩
    exact ⟨⟨h h2, h1⟩, h2⟩

@[expose] noncomputable def aI (E : Subgroup (MulAut Y)) (W N : Subgroup Y) : ℕ :=
  (fixRel E W N).relIndex W

@[expose] noncomputable def cI (E : Subgroup (MulAut Y)) (W N : Subgroup Y) : ℕ :=
  N.relIndex (G6.commOn E W ⊔ N)

theorem aI_top_bot (E : Subgroup (MulAut Y)) : aI E ⊤ ⊥ = (fixV E).index := by
  have h : fixRel E ⊤ ⊥ = fixV E := by
    ext w
    simp only [mem_fixRel, Subgroup.mem_top, true_and, Subgroup.mem_bot, mul_inv_eq_one]
    rfl
  rw [aI, h, Subgroup.relIndex_top_right]

theorem cI_top_bot (E : Subgroup (MulAut Y)) : cI E ⊤ ⊥ = Nat.card (commV E) := by
  rw [cI, sup_bot_eq, Subgroup.relIndex_bot_left, G6.commV_eq_commOn_top]

@[expose] def kerRel (E : Subgroup (MulAut Y)) (W N : Subgroup Y) (hN : Stab E N) :
    Subgroup (MulAut Y) where
  carrier := {e | e ∈ E ∧ ∀ w ∈ W, e w * w⁻¹ ∈ N}
  one_mem' := ⟨E.one_mem, fun w _ => by simp [N.one_mem]⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨E.mul_mem ha hb, fun w hw => ?_⟩
    have h : (a * b) w * w⁻¹ = a (b w * w⁻¹) * (a w * w⁻¹) := by
      rw [MulAut.mul_apply, map_mul, map_inv]
      group
    rw [h]
    exact N.mul_mem (hN a ha _ (hb' w hw)) (ha' w hw)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨E.inv_mem ha, fun w hw => ?_⟩
    have h : a⁻¹ w * w⁻¹ = (a⁻¹ (a w * w⁻¹))⁻¹ := by
      rw [map_mul, map_inv, MulAut.inv_apply_self]
      group
    rw [h]
    exact N.inv_mem (hN a⁻¹ (E.inv_mem ha) _ (ha' w hw))

theorem kerRel_le (E : Subgroup (MulAut Y)) (W N : Subgroup Y) (hN : Stab E N) :
    kerRel E W N hN ≤ E := fun _ he => he.1

theorem mem_kerRel {E : Subgroup (MulAut Y)} {W N : Subgroup Y} {hN : Stab E N} {e : MulAut Y} :
    e ∈ kerRel E W N hN ↔ e ∈ E ∧ ∀ w ∈ W, e w * w⁻¹ ∈ N := Iff.rfl

theorem relIndex_le_two_of {G : Type*} [Group G] {H E : Subgroup G} (hHE : H ≤ E)
    {a : G} (h : ∀ b ∈ E, b ∈ H ∨ a * b ∈ H) : H.relIndex E ≤ 2 := by
  by_cases hEH : E ≤ H
  · rw [Subgroup.relIndex_eq_one.mpr hEH]
    omega
  obtain ⟨b₀, hb₀E, hb₀H⟩ := Set.not_subset.mp hEH
  have haE : a ∈ E := by
    rcases h b₀ hb₀E with h1 | h1
    · exact absurd h1 hb₀H
    · have := E.mul_mem (hHE h1) (E.inv_mem hb₀E)
      simpa using this
  let f : Bool → ↥E ⧸ H.subgroupOf E := fun t =>
    if t then QuotientGroup.mk 1 else QuotientGroup.mk ⟨a⁻¹, E.inv_mem haE⟩
  have hf : Function.Surjective f := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H b =>
      rcases h b b.2 with h1 | h1
      · refine ⟨true, ?_⟩
        show (QuotientGroup.mk 1 : ↥E ⧸ H.subgroupOf E) = QuotientGroup.mk b
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa using h1
      · refine ⟨false, ?_⟩
        show (QuotientGroup.mk ⟨a⁻¹, E.inv_mem haE⟩ : ↥E ⧸ H.subgroupOf E) = QuotientGroup.mk b
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa using h1
  have hle := Nat.card_le_card_of_surjective f hf
  have h2 : Nat.card Bool = 2 := by simp
  rw [h2] at hle
  exact hle

variable [Finite Y]

theorem relIndex_ne_zero' (H K : Subgroup Y) : H.relIndex K ≠ 0 := by
  unfold Subgroup.relIndex
  exact Subgroup.index_ne_zero_of_finite

theorem aI_mul_le {E : Subgroup (MulAut Y)} {W W' N : Subgroup Y} (hW' : Stab E W')
    (hNW' : N ≤ W') (hW'W : W' ≤ W) : aI E W W' * aI E W' N ≤ aI E W N := by
  unfold aI
  have h1 := Subgroup.relIndex_mul_relIndex (fixRel E W N) (fixRel E W W') W
    (fixRel_mono hNW') (fixRel_le _ _ _)
  have h2 : (fixRel E W' N).relIndex W' = (fixRel E W N).relIndex W' := by
    rw [← fixRel_inf hW'W, Subgroup.inf_relIndex_right]
  have h3 : (fixRel E W N).relIndex W' ≤ (fixRel E W N).relIndex (fixRel E W W') :=
    Subgroup.relIndex_le_of_le_right (le_fixRel hW' hW'W) (relIndex_ne_zero' _ _)
  rw [h2, ← h1, mul_comm]
  exact Nat.mul_le_mul_right _ h3

theorem cI_mul_le {E : Subgroup (MulAut Y)} {W W' N : Subgroup Y} (hW' : Stab E W')
    (hNW' : N ≤ W') (hW'W : W' ≤ W) : cI E W W' * cI E W' N ≤ cI E W N := by
  unfold cI
  set D := G6.commOn E W ⊔ N
  have hND : N ≤ D ⊓ W' := le_inf le_sup_right hNW'
  have h1 := Subgroup.relIndex_mul_relIndex N (D ⊓ W') D hND inf_le_left
  have h2 : (D ⊓ W').relIndex D = W'.relIndex (G6.commOn E W ⊔ W') := by
    rw [inf_comm, Subgroup.inf_relIndex_right, ← Subgroup.relIndex_sup_right]
    congr 1
    rw [sup_assoc, sup_eq_right.mpr hNW']
  have hle : G6.commOn E W' ⊔ N ≤ D ⊓ W' :=
    le_inf (sup_le_sup_right (commOn_mono hW'W) N) (sup_le (commOn_le hW') hNW')
  have h3 : N.relIndex (G6.commOn E W' ⊔ N) ≤ N.relIndex (D ⊓ W') :=
    Subgroup.relIndex_le_of_le_right hle (relIndex_ne_zero' _ _)
  rw [← h1, h2, mul_comm]
  exact Nat.mul_le_mul_right _ h3

theorem aI_le_of_le {E : Subgroup (MulAut Y)} {W W' N : Subgroup Y} (hW' : Stab E W')
    (hNW' : N ≤ W') (hW'W : W' ≤ W) : aI E W' N ≤ aI E W N := by
  have h := aI_mul_le hW' hNW' hW'W
  have h0 : 0 < aI E W W' := Nat.pos_of_ne_zero (relIndex_ne_zero' _ _)
  calc aI E W' N ≤ aI E W W' * aI E W' N := Nat.le_mul_of_pos_left _ h0
    _ ≤ aI E W N := h

theorem aI_le_of_le' {E : Subgroup (MulAut Y)} {W W' N : Subgroup Y} (hW' : Stab E W')
    (hNW' : N ≤ W') (hW'W : W' ≤ W) : aI E W W' ≤ aI E W N := by
  have h := aI_mul_le hW' hNW' hW'W
  have h0 : 0 < aI E W' N := Nat.pos_of_ne_zero (relIndex_ne_zero' _ _)
  calc aI E W W' ≤ aI E W W' * aI E W' N := Nat.le_mul_of_pos_right _ h0
    _ ≤ aI E W N := h

theorem cI_le_of_le {E : Subgroup (MulAut Y)} {W W' N : Subgroup Y} (hW' : Stab E W')
    (hNW' : N ≤ W') (hW'W : W' ≤ W) : cI E W' N ≤ cI E W N := by
  have h := cI_mul_le hW' hNW' hW'W
  have h0 : 0 < cI E W W' := Nat.pos_of_ne_zero (relIndex_ne_zero' _ _)
  calc cI E W' N ≤ cI E W W' * cI E W' N := Nat.le_mul_of_pos_left _ h0
    _ ≤ cI E W N := h

theorem cI_le_of_le' {E : Subgroup (MulAut Y)} {W W' N : Subgroup Y} (hW' : Stab E W')
    (hNW' : N ≤ W') (hW'W : W' ≤ W) : cI E W W' ≤ cI E W N := by
  have h := cI_mul_le hW' hNW' hW'W
  have h0 : 0 < cI E W' N := Nat.pos_of_ne_zero (relIndex_ne_zero' _ _)
  calc cI E W W' ≤ cI E W W' * cI E W' N := Nat.le_mul_of_pos_right _ h0
    _ ≤ cI E W N := h

theorem two_le_aI {E : Subgroup (MulAut Y)} {W N : Subgroup Y} {e : MulAut Y} (he : e ∈ E)
    {w : Y} (hw : w ∈ W) (hne : e w * w⁻¹ ∉ N) : 2 ≤ aI E W N := by
  have h1 : (fixRel E W N).relIndex W ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    intro hle
    exact hne ((hle hw).2 e he)
  have h0 := relIndex_ne_zero' (fixRel E W N) W
  unfold aI
  omega

theorem two_le_cI {E : Subgroup (MulAut Y)} {W N : Subgroup Y} {e : MulAut Y} (he : e ∈ E)
    {w : Y} (hw : w ∈ W) (hne : e w * w⁻¹ ∉ N) : 2 ≤ cI E W N := by
  have h1 : N.relIndex (G6.commOn E W ⊔ N) ≠ 1 := by
    rw [Ne, Subgroup.relIndex_eq_one]
    intro hle
    exact hne (hle (le_sup_left (b := N) (mem_commOn_of he hw)))
  have h0 := relIndex_ne_zero' N (G6.commOn E W ⊔ N)
  unfold cI
  omega

omit [Finite Y] in
theorem exists_of_relIndex_eq_two {F W : Subgroup Y} (h : F.relIndex W = 2) :
    ∃ a ∈ W, a ∉ F ∧ ∀ b ∈ W, b * a ∈ F ∨ b ∈ F := by
  obtain ⟨a, ha, hb⟩ := Subgroup.index_eq_two_iff_exists_notMem_and.mp h
  refine ⟨a, a.2, fun h' => ha (Subgroup.mem_subgroupOf.mpr h'), fun b hb' => ?_⟩
  rcases hb ⟨b, hb'⟩ with h1 | h1
  · exact Or.inl (Subgroup.mem_subgroupOf.mp h1)
  · exact Or.inr (Subgroup.mem_subgroupOf.mp h1)

omit [Finite Y] in
theorem quad_of_cI_eq_two (hY : ∀ y : Y, y ^ 2 = 1) {E : Subgroup (MulAut Y)}
    {W N : Subgroup Y} (hW : Stab E W) (hN : Stab E N) (hc : cI E W N = 2) :
    ∀ e₁ ∈ E, ∀ e₂ ∈ E, ∀ w ∈ W, e₁ (e₂ w * w⁻¹) * (e₂ w * w⁻¹)⁻¹ ∈ N := by
  obtain ⟨d, -, -, hdD⟩ := exists_of_relIndex_eq_two hc
  intro e₁ he₁ e₂ he₂ w hw
  set u := e₂ w * w⁻¹ with hu
  have huW : u ∈ W := W.mul_mem (hW e₂ he₂ w hw) (W.inv_mem hw)
  have huD : u ∈ G6.commOn E W ⊔ N := le_sup_left (b := N) (mem_commOn_of he₂ hw)
  have hvD : e₁ u * u⁻¹ ∈ G6.commOn E W ⊔ N := le_sup_left (b := N) (mem_commOn_of he₁ huW)
  by_contra hv
  have huN : u ∉ N := fun h => hv (N.mul_mem (hN e₁ he₁ u h) (N.inv_mem h))
  have h1 := (hdD _ hvD).resolve_right hv
  have h2 := (hdD _ huD).resolve_right huN
  have h3 := N.mul_mem h1 (N.inv_mem h2)
  have e : e₁ u * u⁻¹ * d * (u * d)⁻¹ = e₁ u * (u * u)⁻¹ := by
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [e, show u * u = 1 by rw [← pow_two]; exact hY u, inv_one, mul_one] at h3
  apply huN
  have h4 := hN e₁⁻¹ (E.inv_mem he₁) _ h3
  rwa [MulAut.inv_apply_self] at h4

omit [Finite Y] in
theorem relIndex_kerRel_le_two (hY : ∀ y : Y, y ^ 2 = 1) {E : Subgroup (MulAut Y)}
    {W N : Subgroup Y} (hW : Stab E W) (hN : Stab E N)
    (ha : aI E W N = 2) (hc : cI E W N = 2) : (kerRel E W N hN).relIndex E ≤ 2 := by
  have hq := quad_of_cI_eq_two hY hW hN hc
  have hsq : ∀ y : Y, y * y = 1 := fun y => by rw [← pow_two]; exact hY y
  obtain ⟨w₀, hw₀W, hw₀F, hdec⟩ := exists_of_relIndex_eq_two ha
  obtain ⟨d, -, -, hdD⟩ := exists_of_relIndex_eq_two hc
  have hker : ∀ e ∈ E, e w₀ * w₀⁻¹ ∈ N → e ∈ kerRel E W N hN := by
    intro e he hew
    refine ⟨he, fun w hw => ?_⟩
    rcases hdec w hw with h1 | h1
    · have e1 : e w * w⁻¹ = (e (w * w₀) * (w * w₀)⁻¹) * (e w₀ * w₀⁻¹)⁻¹ := by
        rw [map_mul]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      rw [e1]
      exact N.mul_mem (h1.2 e he) (N.inv_mem hew)
    · exact h1.2 e he
  have hD : ∀ u ∈ G6.commOn E W ⊔ N, u ∉ N → u * d ∈ N := fun u hu hun =>
    (hdD u hu).resolve_right hun
  by_cases hall : ∀ e ∈ E, e ∈ kerRel E W N hN
  · rw [Subgroup.relIndex_eq_one.mpr (fun e he => hall e he)]
    omega
  push Not at hall
  obtain ⟨e₁, he₁E, he₁K⟩ := hall
  have hu₁ : e₁ w₀ * w₀⁻¹ ∉ N := fun h => he₁K (hker e₁ he₁E h)
  refine relIndex_le_two_of (kerRel_le _ _ _ _) (a := e₁) fun e he => ?_
  by_cases heK : e ∈ kerRel E W N hN
  · exact Or.inl heK
  · refine Or.inr (hker _ (E.mul_mem he₁E he) ?_)
    have hu : e w₀ * w₀⁻¹ ∉ N := fun h => heK (hker e he h)
    have hmem : ∀ f ∈ E, f w₀ * w₀⁻¹ ∈ G6.commOn E W ⊔ N := fun f hf =>
      le_sup_left (b := N) (mem_commOn_of hf hw₀W)
    have h1 := hD _ (hmem e he) hu
    have h2 := hD _ (hmem e₁ he₁E) hu₁
    have h3 := hq e₁ he₁E e he w₀ hw₀W
    have e1 : (e₁ * e) w₀ * w₀⁻¹ = (e₁ (e w₀ * w₀⁻¹) * (e w₀ * w₀⁻¹)⁻¹) *
        ((e w₀ * w₀⁻¹ * d) * (e₁ w₀ * w₀⁻¹ * d)) := by
      rw [MulAut.mul_apply, map_mul, map_inv]
      have hd : d * d = 1 := hsq d
      have hd' : d = d⁻¹ := eq_inv_of_mul_eq_one_left hd
      conv_rhs => rw [show (e w₀ * w₀⁻¹ * d) * (e₁ w₀ * w₀⁻¹ * d) =
        (e w₀ * w₀⁻¹) * (e₁ w₀ * w₀⁻¹) * (d * d) by ac_rfl, hd, mul_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    rw [e1]
    exact N.mul_mem h3 (N.mul_mem h1 h2)

omit [Finite Y] in
theorem perfect_trivial_of_two_step {K : Subgroup (MulAut Y)} (hK : ⁅K, K⁆ = K)
    {W W' N : Subgroup Y} (hW : Stab K W) (hN : Stab K N)
    (h1 : ∀ k ∈ K, ∀ w ∈ W, k w * w⁻¹ ∈ W') (h2 : ∀ k ∈ K, ∀ w ∈ W', k w * w⁻¹ ∈ N) :
    ∀ k ∈ K, ∀ w ∈ W, k w * w⁻¹ ∈ N := by
  have key : ⁅K, K⁆ ≤ kerRel K W N hN := by
    rw [Subgroup.commutator_le]
    intro k₁ hk₁ k₂ hk₂
    refine ⟨Subgroup.commutator_mem_commutator hk₁ hk₂ |> fun h => hK ▸ h, fun w hw => ?_⟩
    have hagree : ∀ v ∈ W, (k₁ * k₂) v * ((k₂ * k₁) v)⁻¹ ∈ N := by
      intro v hv
      have d₁ := h1 k₁ hk₁ v hv
      have d₂ := h1 k₂ hk₂ v hv
      have a₁ := h2 k₁ hk₁ _ d₂
      have a₂ := h2 k₂ hk₂ _ d₁
      have e1 : (k₁ * k₂) v * ((k₂ * k₁) v)⁻¹ =
          (k₁ (k₂ v * v⁻¹) * (k₂ v * v⁻¹)⁻¹) * (k₂ (k₁ v * v⁻¹) * (k₁ v * v⁻¹)⁻¹)⁻¹ := by
        rw [MulAut.mul_apply, MulAut.mul_apply, map_mul, map_mul, map_inv, map_inv]
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel
      rw [e1]
      exact N.mul_mem a₁ (N.inv_mem a₂)
    have hv : ((k₂ * k₁)⁻¹) w ∈ W := hW _ (K.inv_mem (K.mul_mem hk₂ hk₁)) w hw
    have := hagree _ hv
    have e2 : (k₁ * k₂) ((k₂ * k₁)⁻¹ w) * ((k₂ * k₁) ((k₂ * k₁)⁻¹ w))⁻¹ =
        ⁅k₁, k₂⁆ w * w⁻¹ := by
      have e3 : (k₁ * k₂) * (k₂ * k₁)⁻¹ = ⁅k₁, k₂⁆ := by
        rw [commutatorElement_def]
        group
      rw [MulAut.apply_inv_self, ← MulAut.mul_apply, e3]
    rw [← e2]
    exact this
  intro k hk w hw
  rw [← hK] at hk
  exact (key hk).2 w hw

end CFSG.Quasithin.MS93.S38E
