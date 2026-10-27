module

public import CFSG.Quasithin.MS93.MSPGen3
public import CFSG.Quasithin.MS93.MSPQuad

public section

namespace CFSG.Quasithin.MS93.MSP

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

variable {F : Type} [Field F]

structure IsQuadOf (Q : V4 F → F) : Prop where
  map_add : ∀ x y : V4 F, Q (x + y) = Q x + Q y + form F x y
  map_smul : ∀ (c : F) (x : V4 F), Q (c • x) = c ^ 2 * Q x

@[expose] def orthSp (Q : V4 F → F) : Subgroup (Sp4 F) where
  carrier := {g | ∀ x, Q (mat g *ᵥ x) = Q x}
  one_mem' := fun x => by rw [mat_one, one_mulVec]
  mul_mem' := fun {g h} hg hh x => by
    change Q (mat (g * h) *ᵥ x) = Q x
    rw [mat_mul_mulVec, hg, hh]
  inv_mem' := fun {g} hg x => by
    change Q (mat g⁻¹ *ᵥ x) = Q x
    conv_rhs => rw [← mat_mulVec_inv g x]
    exact (hg _).symm

theorem mem_orthSp {Q : V4 F → F} {g : Sp4 F} : g ∈ orthSp Q ↔ ∀ x, Q (mat g *ᵥ x) = Q x :=
  Iff.rfl

theorem IsQuadOf.comp {Q : V4 F → F} (hQ : IsQuadOf Q) (g : Sp4 F) :
    IsQuadOf fun x => Q (mat g *ᵥ x) :=
  ⟨fun x y => by rw [mulVec_add, hQ.map_add, form_mat],
    fun c x => by rw [mulVec_smul, hQ.map_smul]⟩

theorem orthSp_map_conj (Q : V4 F → F) (g : Sp4 F) :
    (orthSp Q).map (MulAut.conj g).toMonoidHom = orthSp fun x => Q (mat g⁻¹ *ᵥ x) := by
  ext h
  rw [mem_map_conj, mem_orthSp, mem_orthSp]
  constructor
  · intro H x
    have := H (mat g⁻¹ *ᵥ x)
    rw [mat_mul_mulVec, mat_mul_mulVec, mat_mulVec_inv] at this
    exact this
  · intro H x
    have := H (mat g *ᵥ x)
    rw [mat_inv_mulVec] at this
    rw [mat_mul_mulVec, mat_mul_mulVec]
    exact this

theorem eq_zero_or_eq_one_of_card_two (hq : Nat.card F = 2) (a : F) : a = 0 ∨ a = 1 := by
  by_contra h
  push Not at h
  have : Finite F := Nat.finite_of_card_ne_zero (by omega)
  have := Fintype.ofFinite F
  have h3 : 3 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    have hinj : Function.Injective ![(0 : F), 1, a] := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
    simpa using Fintype.card_le_of_injective _ hinj
  omega

theorem IsQuadOf.map_zero {Q : V4 F → F} (hQ : IsQuadOf Q) : Q 0 = 0 := by
  have := hQ.map_smul 0 0
  rwa [zero_smul, zero_pow two_ne_zero, zero_mul] at this

section CharTwo

variable [CharP F 2]

theorem IsQuadOf.map_transv {Q : V4 F → F} (hQ : IsQuadOf Q) (v : V4 F) (c : F) (x : V4 F) :
    Q (mat (transv v c) *ᵥ x) = Q x + form F v x ^ 2 * (c ^ 2 * Q v + c) := by
  rw [transv_mulVec, hQ.map_add, hQ.map_smul, (form F x).map_smul, smul_eq_mul]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination (c * form F v x) * form_swap x v - (c * form F v x ^ 2) * h2

theorem transv_mem_orthSp_iff {Q : V4 F → F} (hQ : IsQuadOf Q) {v : V4 F} (hv : v ≠ 0) (c : F) :
    transv v c ∈ orthSp Q ↔ c * (c * Q v + 1) = 0 := by
  obtain ⟨y, hy⟩ := exists_form_eq_one hv
  constructor
  · intro h
    have := h y
    rw [hQ.map_transv, hy] at this
    linear_combination this
  · intro h x
    rw [hQ.map_transv]
    have : c ^ 2 * Q v + c = 0 := by linear_combination h
    rw [this, mul_zero, add_zero]

theorem card_xPoint_inf_orthSp_le [Finite F] {Q : V4 F → F} (hQ : IsQuadOf Q)
    {p : Submodule F (V4 F)} (hp : IsPoint p) : Nat.card ↥(xPoint p ⊓ orthSp Q) ≤ 2 := by
  classical
  obtain ⟨v, hv, rfl⟩ := exists_eq_span_of_isPoint hp
  have key : ∀ g : ↥(xPoint (F ∙ v) ⊓ orthSp Q), ∃ c : F, transv v c = g ∧
      (c = 0 ∨ c = (Q v)⁻¹) := fun g => by
    obtain ⟨c, hc⟩ := (mem_xPoint_span hv).1 g.2.1
    have h := (transv_mem_orthSp_iff hQ hv c).1 (hc ▸ g.2.2)
    refine ⟨c, hc, ?_⟩
    rcases mul_eq_zero.1 h with h | h
    · exact Or.inl h
    · right
      have hQv : Q v ≠ 0 := by
        rintro hQv
        rw [hQv, mul_zero, zero_add] at h
        exact one_ne_zero h
      field_simp
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      linear_combination h - h2
  choose cf hcf hcf' using key
  have := Fintype.ofFinite ↥(xPoint (F ∙ v) ⊓ orthSp Q)
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  calc (Finset.univ : Finset ↥(xPoint (F ∙ v) ⊓ orthSp Q)).card
      ≤ ({0, (Q v)⁻¹} : Finset F).card :=
        Finset.card_le_card_of_injOn cf (fun g _ => by rcases hcf' g with h | h <;> simp [h])
          fun g _ g' _ h => Subtype.ext (by rw [← hcf g, ← hcf g', h])
    _ ≤ 2 := (Finset.card_insert_le _ _).trans (by simp)

theorem IsQuadOf.map_of_mem_Q₁ {Q : V4 F → F} (hQ : IsQuadOf Q) {g : Sp4 F} (hg : g ∈ Q₁ F)
    (x : V4 F) : Q (mat g *ᵥ x) = Q x +
      (mat g (.inl 0) (.inr 0) ^ 2 * Q (e₁ F) + mat g (.inl 0) (.inr 1) ^ 2 * Q (e₂ F) +
        mat g (.inl 0) (.inr 0)) * x (.inr 0) ^ 2 +
      (mat g (.inl 0) (.inr 1) ^ 2 * Q (e₁ F) + mat g (.inl 1) (.inr 1) ^ 2 * Q (e₂ F) +
        mat g (.inl 1) (.inr 1)) * x (.inr 1) ^ 2 := by
  rw [mulVec_of_mem_Q₁ hg, hQ.map_add, hQ.map_add, hQ.map_smul, hQ.map_smul]
  simp [form_apply]
  grind

theorem card_Q₁_inf_orthSp_le_mul [Finite F] {Q : V4 F → F} (hQ : IsQuadOf Q)
    (h0 : Q (e₁ F) = 0) (T : Finset F) (hT : ∀ d : F, d * (d * Q (e₂ F) + 1) = 0 → d ∈ T) :
    Nat.card ↥(Q₁ F ⊓ orthSp Q) ≤ Nat.card F * T.card := by
  classical
  have := Fintype.ofFinite F
  have := Fintype.ofFinite ↥(Q₁ F ⊓ orthSp Q)
  have key : ∀ g : ↥(Q₁ F ⊓ orthSp Q),
      mat (g : Sp4 F) (.inl 0) (.inr 0) = mat (g : Sp4 F) (.inl 0) (.inr 1) ^ 2 * Q (e₂ F) ∧
        mat (g : Sp4 F) (.inl 1) (.inr 1) ∈ T := fun g => by
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    have hf₁ := g.2.2 (f₁ F)
    have hf₂ := g.2.2 (f₂ F)
    rw [hQ.map_of_mem_Q₁ g.2.1, h0] at hf₁ hf₂
    simp at hf₁ hf₂
    refine ⟨by linear_combination hf₁ - (mat (g : Sp4 F) (.inl 0) (.inr 1) ^ 2 * Q (e₂ F)) * h2,
      hT _ (by linear_combination hf₂)⟩
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ, Nat.card_eq_fintype_card, ← Finset.card_univ,
    ← Finset.card_product]
  refine Finset.card_le_card_of_injOn (fun g => (mat (g : Sp4 F) (.inl 0) (.inr 1),
    mat (g : Sp4 F) (.inl 1) (.inr 1))) (fun g _ => Finset.mem_product.2 ⟨Finset.mem_univ _,
      (key g).2⟩) fun g _ g' _ h => ?_
  have hc := congrArg Prod.fst h
  have hd := congrArg Prod.snd h
  simp only at hc hd
  exact Subtype.ext (eq_of_mem_Q₁ g.2.1 g'.2.1 (by rw [(key g).1, (key g').1, hc]) hc hd)

theorem card_Q₁_inf_orthSp_le [Finite F] {Q : V4 F → F} (hQ : IsQuadOf Q) (h0 : Q (e₁ F) = 0) :
    Nat.card ↥(Q₁ F ⊓ orthSp Q) ≤ 2 * Nat.card F := by
  classical
  refine (card_Q₁_inf_orthSp_le_mul hQ h0 {0, (Q (e₂ F))⁻¹} fun d hd => ?_).trans ?_
  · rcases mul_eq_zero.1 hd with h | h
    · simp [h]
    · have hQ2 : Q (e₂ F) ≠ 0 := by
        rintro hQ2
        rw [hQ2, mul_zero, zero_add] at h
        exact one_ne_zero h
      have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
      have : d = (Q (e₂ F))⁻¹ := by
        field_simp
        linear_combination h - h2
      simp [this]
  · rw [mul_comm]
    exact Nat.mul_le_mul_right _ ((Finset.card_insert_le _ _).trans (by simp))

theorem card_Q₁_inf_orthSp_le_of_zero [Finite F] {Q : V4 F → F} (hQ : IsQuadOf Q)
    (h0 : Q (e₁ F) = 0) (h1 : Q (e₂ F) = 0) : Nat.card ↥(Q₁ F ⊓ orthSp Q) ≤ Nat.card F := by
  refine (card_Q₁_inf_orthSp_le_mul hQ h0 {0} fun d hd => ?_).trans (by simp)
  rw [h1, mul_zero, zero_add, mul_one] at hd
  simp [hd]

theorem IsQuadOf.exists_singular [Finite F] {Q : V4 F → F} (hQ : IsQuadOf Q)
    {l : Submodule F (V4 F)} (hl : IsLine l) : ∃ u ∈ l, u ≠ 0 ∧ Q u = 0 := by
  have hl0 : l ≠ ⊥ := fun h => by
    have := hl.1
    rw [h, finrank_bot] at this
    exact absurd this (by norm_num)
  obtain ⟨u₁, hu₁, hu₁0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hl0
  by_cases hQ₁ : Q u₁ = 0
  · exact ⟨u₁, hu₁, hu₁0, hQ₁⟩
  have hlt : (F ∙ u₁) < l := by
    refine lt_of_le_of_ne ((Submodule.span_singleton_le_iff_mem _ _).2 hu₁) fun h => ?_
    have := hl.1
    rw [← h, finrank_span_singleton hu₁0] at this
    exact absurd this (by norm_num)
  obtain ⟨u₂, hu₂, hu₂n⟩ := IsConcreteLE.exists_of_lt hlt
  obtain ⟨t, ht⟩ : ∃ t : F, t ^ 2 = Q u₂ / Q u₁ := ⟨(frobeniusEquiv F 2).symm (Q u₂ / Q u₁), by
    rw [← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]⟩
  refine ⟨u₂ + t • u₁, add_mem hu₂ (Submodule.smul_mem _ _ hu₁), fun h => hu₂n ?_, ?_⟩
  · rw [Submodule.mem_span_singleton]
    exact ⟨-t, by rw [neg_smul, neg_eq_iff_add_eq_zero, add_comm, h]⟩
  · rw [hQ.map_add, hQ.map_smul, ht, hl.2 _ hu₂ _ (Submodule.smul_mem _ _ hu₁)]
    field_simp
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination Q u₂ * h2

theorem card_qLine_inf_orthSp_le [Finite F] {Q : V4 F → F} (hQ : IsQuadOf Q)
    {l : Submodule F (V4 F)} (hl : IsLine l) :
    Nat.card ↥(qLine l ⊓ orthSp Q) ≤ 2 * Nat.card F ∧
      ((∀ v ∈ l, Q v = 0) → Nat.card ↥(qLine l ⊓ orthSp Q) ≤ Nat.card F) := by
  obtain ⟨u, hu, hu0, hQu⟩ := hQ.exists_singular hl
  obtain ⟨g, hgp, hgl⟩ := exists_map_flag (p := F ∙ u) (l := l)
    ⟨isPoint_span hu0, hl, (Submodule.span_singleton_le_iff_mem _ _).2 hu⟩
  have hmap : (qLine l ⊓ orthSp Q).map (MulAut.conj g⁻¹).toMonoidHom =
      Q₁ F ⊓ orthSp fun x => Q (mat g *ᵥ x) := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g⁻¹).injective, qLine_map_conj_inv g hgl,
      orthSp_map_conj, inv_inv]
  have hcard : Nat.card ↥(qLine l ⊓ orthSp Q) =
      Nat.card ↥(Q₁ F ⊓ orthSp fun x => Q (mat g *ᵥ x)) := by
    rw [← hmap, card_map_conj]
  have he₁ : Q (mat g *ᵥ e₁ F) = 0 := by
    have : mat g *ᵥ e₁ F ∈ F ∙ u := hgp ▸ mulVec_mem_map g (by
      rw [pt₀_eq_span]; exact Submodule.mem_span_singleton_self _)
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 this
    rw [← hc, hQ.map_smul, hQu, mul_zero]
  refine ⟨hcard ▸ card_Q₁_inf_orthSp_le (hQ.comp g) he₁, fun hz => ?_⟩
  have he₂ : Q (mat g *ᵥ e₂ F) = 0 :=
    hz _ (hgl ▸ mulVec_mem_map g (mem_ln₀.2 ⟨by simp, by simp⟩))
  exact hcard ▸ card_Q₁_inf_orthSp_le_of_zero (hQ.comp g) he₁ he₂

theorem eq_bot_or_of_le_orthSp [Finite F] {Q : V4 F → F} (hQ : IsQuadOf Q)
    {E : Subgroup (Sp4 F)} (hEQ : E ≤ orthSp Q) (hE2 : IsPGroup 2 E)
    (h1 : Nat.card (V4 F) ≤ Nat.card (fixSp E) * Nat.card E)
    (h2 : Nat.card (V4 F) ≤ Nat.card (fixSp E) * Nat.card F ^ 2) :
    E = ⊥ ∨ (Nat.card F = 2 ∧ ∃ p p' : Submodule F (V4 F), IsPoint p ∧ IsPoint p' ∧
      p' ≤ perp p ∧ E = xPoint p ⊔ xPoint p') := by
  by_cases hE : E = ⊥
  · exact Or.inl hE
  right
  have hq1 : 1 < Nat.card F := Finite.one_lt_card
  have hk4 : Module.finrank F (fixSp E) ≤ 4 := by
    have := Submodule.finrank_le (fixSp E)
    simpa using this
  rw [card_V4, card_fixSp] at h1 h2
  have hk2 : 2 ≤ Module.finrank F (fixSp E) := by
    rw [← pow_add] at h2
    have := (Nat.pow_le_pow_iff_right hq1).1 h2
    omega
  have hk3 : Module.finrank F (fixSp E) ≠ 4 := by
    intro h4
    refine hE (eq_bot_iff.2 fun g hg => ?_)
    have htop : fixSp E = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [h4]; simp)
    rw [Subgroup.mem_bot]
    refine ext_mulVec fun v => ?_
    rw [mat_one, one_mulVec]
    exact mem_fixSp.1 (htop ▸ Submodule.mem_top) g hg
  rcases (show Module.finrank F (fixSp E) = 2 ∨ Module.finrank F (fixSp E) = 3 by omega)
    with hk | hk
  ·
    obtain ⟨hl, hEl⟩ := isLine_fixSp_of_finrank_two hE2 hk
    rw [hk] at h1
    have hcE : Nat.card F ^ 2 ≤ Nat.card E := by
      have : Nat.card F ^ 2 * Nat.card F ^ 2 ≤ Nat.card F ^ 2 * Nat.card E := by
        rw [← pow_add]; exact h1
      exact Nat.le_of_mul_le_mul_left this (by positivity)
    have hEle : Nat.card E ≤ Nat.card ↥(qLine (fixSp E) ⊓ orthSp Q) :=
      Subgroup.card_le_of_le (le_inf hEl hEQ)
    obtain ⟨hS, hS0⟩ := card_qLine_inf_orthSp_le hQ hl
    have hq2 : Nat.card F = 2 := by nlinarith
    refine ⟨hq2, ?_⟩
    have hE4 : Nat.card E = 4 := by rw [hq2] at hcE hS; omega
    have hES : E = qLine (fixSp E) ⊓ orthSp Q :=
      Subgroup.eq_of_le_of_card_ge (le_inf hEl hEQ) (by rw [hq2] at hS; omega)
    obtain ⟨w, hw, hQw⟩ : ∃ w ∈ fixSp E, Q w ≠ 0 := by
      by_contra hw
      push Not at hw
      have := hS0 hw
      omega
    obtain ⟨u, hu, hu0, hQu⟩ := hQ.exists_singular hl
    have hQw1 : Q w = 1 := (eq_zero_or_eq_one_of_card_two hq2 _).resolve_left hQw
    have hw0 : w ≠ 0 := fun h => hQw (by rw [h, hQ.map_zero])
    have hQw₂ : Q (w + u) = 1 := by
      rw [hQ.map_add, hQw1, hQu, hl.2 _ hw _ hu, add_zero, add_zero]
    have hw₂0 : w + u ≠ 0 := fun h => by
      rw [h, hQ.map_zero] at hQw₂
      exact zero_ne_one hQw₂
    have hwu : w + u ≠ w := fun h => hu0 (by simpa using h)
    have htw : ∀ x ∈ fixSp E, Q x = 1 → xPoint (F ∙ x) ≤ E := fun x hx hQx => by
      have hx0 : x ≠ 0 := fun h => by rw [h, hQ.map_zero] at hQx; exact zero_ne_one hQx
      intro g hg
      obtain ⟨c, rfl⟩ := (mem_xPoint_span hx0).1 hg
      rw [hES]
      refine ⟨transv_mem_qLine hl hx c, (transv_mem_orthSp_iff hQ hx0 c).2 ?_⟩
      rcases eq_zero_or_eq_one_of_card_two hq2 c with rfl | rfl
      · simp
      · rw [hQx, one_mul, one_mul, CharTwo.add_self_eq_zero]
    refine ⟨F ∙ w, F ∙ (w + u), isPoint_span hw0, isPoint_span hw₂0, ?_, ?_⟩
    · rw [Submodule.span_singleton_le_iff_mem, mem_perp_span]
      exact hl.2 _ hw _ (add_mem hw hu)
    · have hle : xPoint (F ∙ w) ⊔ xPoint (F ∙ (w + u)) ≤ E :=
        sup_le (htw w hw hQw1) (htw _ (add_mem hw hu) hQw₂)
      refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
      have h1w : transv w 1 ≠ 1 := fun h => one_ne_zero (transv_injective hw0
        (h.trans (transv_zero w).symm))
      have h1w₂ : transv (w + u) 1 ≠ 1 := fun h => one_ne_zero (transv_injective hw₂0
        (h.trans (transv_zero _).symm))
      have hww₂ : transv (w + u) 1 ≠ transv w 1 := fun h => hwu ((transv_eq_transv_iff hw0).1 h)
      have hmem1 : transv w 1 ∈ xPoint (F ∙ w) ⊔ xPoint (F ∙ (w + u)) :=
        Subgroup.mem_sup_left (transv_mem_xPoint w 1)
      have hmem2 : transv (w + u) 1 ∈ xPoint (F ∙ w) ⊔ xPoint (F ∙ (w + u)) :=
        Subgroup.mem_sup_right (transv_mem_xPoint _ 1)
      have h3 : 3 ≤ Nat.card ↥(xPoint (F ∙ w) ⊔ xPoint (F ∙ (w + u))) := by
        let f : Fin 3 → ↥(xPoint (F ∙ w) ⊔ xPoint (F ∙ (w + u))) :=
          ![1, ⟨_, hmem1⟩, ⟨_, hmem2⟩]
        have hf : Function.Injective f := by
          intro i j hij
          have hij' := congrArg Subtype.val hij
          fin_cases i <;> fin_cases j <;> simp [f] at hij' ⊢ <;>
            first | exact absurd hij' h1w | exact absurd hij'.symm h1w |
              exact absurd hij' h1w₂ | exact absurd hij'.symm h1w₂ |
              exact absurd hij' hww₂.symm | exact absurd hij'.symm hww₂.symm
        simpa using Nat.card_le_card_of_injective f hf
      have hdvd := Subgroup.card_dvd_of_le hle
      rw [hE4] at hdvd ⊢
      have hle4 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases h : Nat.card ↥(xPoint (F ∙ w) ⊔ xPoint (F ∙ (w + u))) <;> omega
  ·
    obtain ⟨p, hp, -, hEp⟩ := exists_point_of_finrank_fixSp_three hk
    rw [hk] at h1
    have hcE : Nat.card F ≤ Nat.card E := by
      have : Nat.card F ^ 3 * Nat.card F ≤ Nat.card F ^ 3 * Nat.card E := by
        rw [← pow_succ]; exact h1
      exact Nat.le_of_mul_le_mul_left this (by positivity)
    have hEle : Nat.card E ≤ Nat.card ↥(xPoint p ⊓ orthSp Q) :=
      Subgroup.card_le_of_le (le_inf hEp hEQ)
    have hq2 : Nat.card F = 2 := by
      have := card_xPoint_inf_orthSp_le hQ hp
      omega
    refine ⟨hq2, p, p, hp, hp, ?_, ?_⟩
    · obtain ⟨v, -, rfl⟩ := exists_eq_span_of_isPoint hp
      rw [Submodule.span_singleton_le_iff_mem, mem_perp_span]
      exact form_self v
    · rw [sup_idem]
      exact Subgroup.eq_of_le_of_card_ge hEp (by rw [card_xPoint hp]; exact hcE)

@[expose] def quad₀ (x : V4 F) : F := x (.inl 0) * x (.inr 0) + x (.inl 1) * x (.inr 1)

theorem isQuadOf_quad₀ : IsQuadOf (quad₀ (F := F)) := by
  refine ⟨fun x y => ?_, fun c x => ?_⟩
  · rw [quad₀, quad₀, quad₀, form_apply]
    simp only [Pi.add_apply]
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination (x (.inr 0) * y (.inl 0) + x (.inr 1) * y (.inl 1)) * h2
  · simp only [quad₀, Pi.smul_apply, smul_eq_mul]
    ring

theorem exists_trace_rep [Finite F] (f₂ : F →+ ZMod 2) :
    ∃ θ : F, ∀ s : F, @Algebra.trace (ZMod 2) F _ _ (ZMod.algebra F 2) (θ * s) = f₂ s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hnd := traceForm_nondegenerate (ZMod 2) F
  let fl : Module.Dual (ZMod 2) F :=
    { toFun := f₂
      map_add' := f₂.map_add
      map_smul' := fun c s => by
        fin_cases c
        · change f₂ ((0 : ZMod 2) • s) = (0 : ZMod 2) * f₂ s
          rw [zero_smul, map_zero, zero_mul]
        · change f₂ ((1 : ZMod 2) • s) = (1 : ZMod 2) * f₂ s
          rw [one_smul, one_mul] }
  refine ⟨((Algebra.traceForm (ZMod 2) F).toDual hnd).symm fl, fun s => ?_⟩
  have := LinearMap.BilinForm.apply_toDual_symm_apply (hB := hnd) fl s
  rw [Algebra.traceForm_apply] at this
  exact this

theorem exists_isQuadOf_of_fix [Finite F] (f : V4 F × F →+ ZMod 2)
    (hf : ∃ s : F, f (0, s) ≠ 0) : ∃ Q : V4 F → F, IsQuadOf Q ∧ ∀ g : Sp4 F,
      (∀ (x : V4 F) (s : F), f (mat g *ᵥ x, s + quad₀ x + quad₀ (mat g *ᵥ x)) = f (x, s)) →
        g ∈ orthSp Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hnd := traceForm_nondegenerate (ZMod 2) F
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have h2' : (2 : ZMod 2) = 0 := rfl
  set tr := Algebra.trace (ZMod 2) F
  obtain ⟨θ, hθ⟩ := exists_trace_rep (f.comp (AddMonoidHom.inr (V4 F) F))
  choose θi hθi using fun i : Fin 2 ⊕ Fin 2 =>
    exists_trace_rep (f.comp ((AddMonoidHom.inl (V4 F) F).comp
      (AddMonoidHom.single (fun _ : Fin 2 ⊕ Fin 2 => F) i)))
  have hθs : ∀ s, tr (θ * s) = f (0, s) := fun s => by rw [hθ]; rfl
  have hθ0 : θ ≠ 0 := by
    rintro rfl
    obtain ⟨s, hs⟩ := hf
    rw [← hθs, zero_mul, map_zero] at hs
    exact hs rfl
  let ξ : V4 F → F := fun x => ∑ i, θi i * x i
  have hξadd : ∀ x y, ξ (x + y) = ξ x + ξ y := fun x y => by
    simp only [ξ, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  have hξsmul : ∀ (c : F) x, ξ (c • x) = c * ξ x := fun c x => by
    simp only [ξ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hfx : ∀ x : V4 F, f (x, 0) = tr (ξ x) := fun x => by
    have hx : ((x, 0) : V4 F × F) = ∑ i, (Pi.single i (x i), 0) := by
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_sum]
        exact (Finset.univ_sum_single x).symm
      · rw [Prod.snd_sum]
        simp
    rw [hx, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hθi]
    rfl
  have hfsplit : ∀ (x : V4 F) (s : F), f (x, s) = f (x, 0) + f (0, s) := fun x s => by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]
  obtain ⟨r, hr⟩ : ∃ r : F, r ^ 2 = θ := ⟨(frobeniusEquiv F 2).symm θ, by
    rw [← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]⟩
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact hθ0 (by rw [← hr]; ring)
  let μ : V4 F → F := fun x => ξ x / r
  refine ⟨fun x => quad₀ x + μ x ^ 2, ⟨fun x y => ?_, fun c x => ?_⟩, fun g hg => ?_⟩
  · have key : ((ξ x + ξ y) / r) ^ 2 = (ξ x / r) ^ 2 + (ξ y / r) ^ 2 := by
      rw [add_div, add_sq]
      linear_combination (ξ x / r * (ξ y / r)) * h2
    simp only [μ, hξadd]
    rw [isQuadOf_quad₀.map_add, key]
    ring
  · simp only [μ, hξsmul]
    rw [isQuadOf_quad₀.map_smul]
    ring
  · intro x
    set η := ξ (mat g *ᵥ x) + ξ x
    set D := quad₀ x + quad₀ (mat g *ᵥ x)
    have hc : ∀ c : F, tr (c ^ 2 * (η ^ 2 + θ * D)) = 0 := fun c => by
      have h := hg (c • x) 0
      rw [mulVec_smul, isQuadOf_quad₀.map_smul, isQuadOf_quad₀.map_smul, zero_add,
        hfsplit, hfx, hfx, ← hθs, hξsmul, hξsmul] at h
      have hfrob : tr (c * η) = tr ((c * η) ^ 2) := by
        rw [← Algebra.trace_eq_of_algEquiv (FiniteField.frobeniusAlgEquiv (ZMod 2) F 2) (c * η)]
        congr 1
      have hsum : tr (c * η) = tr (c * ξ (mat g *ᵥ x)) + tr (c * ξ x) := by
        rw [← map_add, mul_add]
      have hD : c ^ 2 * quad₀ x + c ^ 2 * quad₀ (mat g *ᵥ x) = c ^ 2 * D := by ring
      rw [hD] at h
      have : tr (c ^ 2 * (η ^ 2 + θ * D)) = tr ((c * η) ^ 2) + tr (θ * (c ^ 2 * D)) := by
        rw [← map_add]
        congr 1
        ring
      rw [this, ← hfrob, hsum, ← h]
      linear_combination (tr (c * ξ (mat g *ᵥ x)) + tr (θ * (c ^ 2 * D))) * h2'
    have hzero : η ^ 2 + θ * D = 0 := by
      refine hnd.1 _ fun y => ?_
      obtain ⟨c, hc'⟩ : ∃ c : F, c ^ 2 = y := ⟨(frobeniusEquiv F 2).symm y, by
        rw [← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]⟩
      rw [Algebra.traceForm_apply, mul_comm, ← hc']
      exact hc c
    show quad₀ (mat g *ᵥ x) + μ (mat g *ᵥ x) ^ 2 = quad₀ x + μ x ^ 2
    have hθD : r ^ 2 * D = η ^ 2 := by rw [hr]; linear_combination hzero - η ^ 2 * h2
    have hD : quad₀ x + quad₀ (mat g *ᵥ x) = (ξ (mat g *ᵥ x) / r + ξ x / r) ^ 2 := by
      rw [← add_div, div_pow, eq_div_iff (pow_ne_zero 2 hr0), mul_comm]
      exact hθD
    simp only [μ]
    linear_combination hD + ((ξ (mat g *ᵥ x) / r) ^ 2 + ξ (mat g *ᵥ x) / r * (ξ x / r) -
      quad₀ x) * h2

end CharTwo

end CFSG.Quasithin.MS93.MSP
