module

public import CFSG.Quasithin.MS93.MSPSix
public import CFSG.Quasithin.MS93.MSPOrth

public section

namespace CFSG.Quasithin.MS93.S33

open Matrix CFSG.Assembly.LowTwoRank

variable {F : Type} [Field F]

theorem perp_commSp_le_fixSp (Γ : Subgroup (MSP.Sp4 F)) :
    MSP.perp (MSP.commSp Γ) ≤ MSP.fixSp Γ := by
  intro v hv
  rw [MSP.mem_fixSp]
  intro g hg
  have key : ∀ x : MSP.V4 F, MSP.form F x (MSP.mat g *ᵥ v - v) = 0 := by
    intro x
    have h1 : MSP.form F x (MSP.mat g *ᵥ v) = MSP.form F (MSP.mat g⁻¹ *ᵥ x) v := by
      conv_lhs => rw [← MSP.mat_mulVec_inv g x]
      exact MSP.form_mat g _ v
    have h2 : MSP.form F (MSP.mat g⁻¹ *ᵥ x - x) v = 0 :=
      MSP.mem_perp.1 hv _ (MSP.sub_mem_commSp (inv_mem hg) x)
    rw [map_sub, h1, ← h2, map_sub, LinearMap.sub_apply]
  have hw : MSP.mat g *ᵥ v - v = 0 := by
    refine MSP.form_nondegenerate.1 _ fun x => ?_
    rw [MSP.form_swap, key, neg_zero]
  exact sub_eq_zero.1 hw

theorem two_le_finrank_fixSp {Γ : Subgroup (MSP.Sp4 F)} (hq : MSP.commSp Γ ≤ MSP.fixSp Γ) :
    2 ≤ Module.finrank F (MSP.fixSp Γ) := by
  have h1 := MSP.finrank_perp (MSP.commSp Γ)
  have h2 := Submodule.finrank_mono (perp_commSp_le_fixSp Γ)
  have h3 := Submodule.finrank_mono hq
  omega

theorem line_of_quadratic [Finite F] [CharP F 2] {Γ : Subgroup (MSP.Sp4 F)} (hΓ : IsPGroup 2 Γ)
    (hq : MSP.commSp Γ ≤ MSP.fixSp Γ) (hd : Module.finrank F (MSP.fixSp Γ) ≤ 2) :
    MSP.IsLine (MSP.fixSp Γ) ∧ Γ ≤ MSP.qLine (MSP.fixSp Γ) ∧ MSP.commSp Γ = MSP.fixSp Γ := by
  have h2 := two_le_finrank_fixSp hq
  have hf : Module.finrank F (MSP.fixSp Γ) = 2 := by omega
  obtain ⟨hl, hΓl⟩ := MSP.isLine_fixSp_of_finrank_two hΓ hf
  refine ⟨hl, hΓl, Submodule.eq_of_le_of_finrank_le hq ?_⟩
  have h1 := MSP.finrank_perp (MSP.commSp Γ)
  have h3 := Submodule.finrank_mono (perp_commSp_le_fixSp Γ)
  omega

theorem transv_mul_comm {v w : MSP.V4 F} (h : MSP.form F v w = 0) (a b : F) :
    MSP.transv v a * MSP.transv w b = MSP.transv w b * MSP.transv v a := by
  have h' : MSP.form F w v = 0 := by rw [MSP.form_swap, h, neg_zero]
  refine MSP.ext_mulVec fun x => ?_
  rw [MSP.mat_mul_mulVec, MSP.mat_mul_mulVec, MSP.transv_mulVec, MSP.transv_mulVec,
    MSP.transv_mulVec, MSP.transv_mulVec]
  simp only [map_add, map_smul, smul_eq_mul, h, h', mul_zero, add_zero]
  abel

variable [Finite F]

omit [Finite F] in
theorem eq_one_or_eq_transv (hq : Nat.card F = 2) {v : MSP.V4 F} (hv : v ≠ 0) {g : MSP.Sp4 F}
    (hg : g ∈ MSP.xPoint (F ∙ v)) : g = 1 ∨ g = MSP.transv v 1 := by
  obtain ⟨c, rfl⟩ := (MSP.mem_xPoint_span hv).1 hg
  rcases MSP.eq_zero_or_eq_one_of_card_two hq c with rfl | rfl
  · exact Or.inl (MSP.transv_zero v)
  · exact Or.inr rfl

omit [Finite F] in
theorem exists_eq_of_mem_sup {v v' : MSP.V4 F} (hv : v ≠ 0)
    (hv' : v' ≠ 0) (hvv : MSP.form F v v' = 0) {g : MSP.Sp4 F}
    (hg : g ∈ MSP.xPoint (F ∙ v) ⊔ MSP.xPoint (F ∙ v')) :
    ∃ a b : F, g = MSP.transv v a * MSP.transv v' b := by
  have hcomm : ∀ x ∈ MSP.xPoint (F ∙ v), ∀ y ∈ MSP.xPoint (F ∙ v'), x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := (MSP.mem_xPoint_span hv).1 hx
    obtain ⟨b, rfl⟩ := (MSP.mem_xPoint_span hv').1 hy
    exact transv_mul_comm hvv a b
  have hN : MSP.xPoint (F ∙ v) ≤ Subgroup.normalizer (MSP.xPoint (F ∙ v') : Set (MSP.Sp4 F)) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hcomm x hx y hy, mul_inv_cancel_right]
      exact hy
    · intro hy
      have h1 := hcomm x⁻¹ (inv_mem hx) _ hy
      have e : y = x * y * x⁻¹ :=
        calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
          _ = (x * y * x⁻¹) * x⁻¹ * x := by rw [h1]
          _ = x * y * x⁻¹ := by group
      rw [e]
      exact hy
  have hg' : g ∈ ((MSP.xPoint (F ∙ v) ⊔ MSP.xPoint (F ∙ v') : Subgroup (MSP.Sp4 F)) :
      Set (MSP.Sp4 F)) := hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hg'
  obtain ⟨x, hx, y, hy, rfl⟩ := hg'
  obtain ⟨a, rfl⟩ := (MSP.mem_xPoint_span hv).1 hx
  obtain ⟨b, rfl⟩ := (MSP.mem_xPoint_span hv').1 hy
  exact ⟨a, b, rfl⟩

theorem transv_add_not_mem_sup (hq : Nat.card F = 2) {v v' : MSP.V4 F} (hv : v ≠ 0)
    (hv' : v' ≠ 0) (hvv : MSP.form F v v' = 0) (hind : v' ∉ F ∙ v) :
    MSP.transv (v + v') 1 ∉ MSP.xPoint (F ∙ v) ⊔ MSP.xPoint (F ∙ v') := by
  have : CharP F 2 := by
    have := Fintype.ofFinite F
    have hc : Fintype.card F = 2 ^ 1 := by rw [← Nat.card_eq_fintype_card, hq, pow_one]
    exact charP_of_card_eq_prime_pow hc
  have hvv' : MSP.form F v' v = 0 := by rw [MSP.form_swap, hvv, neg_zero]
  have hsum : v + v' ≠ 0 := by
    intro h0
    apply hind
    have : v' = (-1 : F) • v := by
      rw [neg_one_smul]
      exact (neg_eq_of_add_eq_zero_right h0).symm
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  intro hmem
  obtain ⟨a, b, hab⟩ := exists_eq_of_mem_sup hv hv' hvv hmem
  obtain ⟨x, hx⟩ := MSP.exists_form_eq_one hv
  have hL : MSP.mat (MSP.transv (v + v') 1) *ᵥ x = x + (1 + MSP.form F v' x) • (v + v') := by
    rw [MSP.transv_mulVec, map_add, LinearMap.add_apply, hx, one_mul]
  have hR : MSP.mat (MSP.transv v a * MSP.transv v' b) *ᵥ x =
      x + ((b * MSP.form F v' x) • v' + a • v) := by
    rw [MSP.mat_mul_mulVec, MSP.transv_mulVec, MSP.transv_mulVec, map_add, map_smul, hx, hvv,
      smul_eq_mul, mul_zero, add_zero, mul_one, add_assoc]
  have e := congrArg (fun g : MSP.Sp4 F => MSP.mat g *ᵥ x) hab
  rw [hL, hR] at e
  have e2 := add_left_cancel e
  rcases MSP.eq_zero_or_eq_one_of_card_two hq (MSP.form F v' x) with hc | hc
  ·
    rw [hc, add_zero, one_smul, mul_zero, zero_smul, zero_add] at e2
    apply hind
    have : v' = (a - 1) • v := by rw [sub_smul, one_smul, ← e2, add_sub_cancel_left]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  ·
    rw [hc, CharTwo.add_self_eq_zero, zero_smul, mul_one] at e2
    have e' : a • v + b • v' = 0 := by rw [add_comm]; exact e2.symm
    rcases MSP.eq_zero_or_eq_one_of_card_two hq a with ha | ha
    · rw [ha, zero_smul, zero_add] at e'
      rcases MSP.eq_zero_or_eq_one_of_card_two hq b with hb | hb
      · rw [ha, hb, MSP.transv_zero, MSP.transv_zero, one_mul] at hab
        have h0 : MSP.transv (v + v') 1 = MSP.transv (v + v') 0 := by rw [hab, MSP.transv_zero]
        exact one_ne_zero (MSP.transv_injective hsum h0)
      · rw [hb, one_smul] at e'
        exact hv' e'
    · rw [ha, one_smul] at e'
      apply hind
      have hb0 : b ≠ 0 := by
        intro hb0
        rw [hb0, zero_smul, add_zero] at e'
        exact hv e'
      have : v' = (-b⁻¹) • v := by
        have h1 : b • v' = -v := eq_neg_of_add_eq_zero_right e'
        calc v' = b⁻¹ • (b • v') := by rw [smul_smul, inv_mul_cancel₀ hb0, one_smul]
          _ = (-b⁻¹) • v := by rw [h1, smul_neg, neg_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)

theorem card_qLine_inf_commutator_le {l : Submodule (ZMod 2) (MSP.V4 (ZMod 2))}
    (hl : MSP.IsLine l) :
    Nat.card ↥(MSP.qLine l ⊓ commutator (MSP.Sp4 (ZMod 2))) ≤ 4 := by
  have : Finite (MSP.Sp4 (ZMod 2)) := Subtype.finite
  have h8 : Nat.card (MSP.qLine l) = 8 := by
    rw [MSP.card_qLine hl, Nat.card_eq_fintype_card, ZMod.card]
    norm_num
  have hl0 : l ≠ ⊥ := fun h => by
    have := hl.1
    rw [h, finrank_bot] at this
    exact absurd this (by norm_num)
  obtain ⟨x, hxl, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hl0
  have hτ : MSP.transv x 1 ∈ MSP.qLine l := MSP.transv_mem_qLine hl hxl 1
  have hτc : MSP.transv x 1 ∉ commutator (MSP.Sp4 (ZMod 2)) :=
    MSP.transv_not_mem_commutator (RingEquiv.refl _) hx0
  have hd : Nat.card ↥(MSP.qLine l ⊓ commutator (MSP.Sp4 (ZMod 2))) ∣ 8 :=
    h8 ▸ Subgroup.card_dvd_of_le inf_le_left
  have hne : Nat.card ↥(MSP.qLine l ⊓ commutator (MSP.Sp4 (ZMod 2))) ≠ 8 := by
    intro h
    have heq := Subgroup.eq_of_le_of_card_ge (inf_le_left :
      MSP.qLine l ⊓ commutator (MSP.Sp4 (ZMod 2)) ≤ MSP.qLine l) (by rw [h, h8])
    have hmem : MSP.transv x 1 ∈ MSP.qLine l ⊓ commutator (MSP.Sp4 (ZMod 2)) := by
      rw [heq]
      exact hτ
    exact hτc hmem.2
  have hdiv : Nat.card ↥(MSP.qLine l ⊓ commutator (MSP.Sp4 (ZMod 2))) ∈ Nat.divisors 8 :=
    Nat.mem_divisors.2 ⟨hd, by norm_num⟩
  have h8d : Nat.divisors 8 = {1, 2, 4, 8} := by decide
  rw [h8d] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  omega

end CFSG.Quasithin.MS93.S33
