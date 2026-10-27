module

public import CFSG.Quasithin.Background.C1PackBasic

public section

namespace CFSG.Quasithin.C1Pack

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def barImage (H B : Subgroup G) : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) :=
  (B.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))

omit [Finite G] in
theorem coe_mem_pCoreOf_iff (H : Subgroup G) (x : ↥H) :
    (x : G) ∈ pCoreOf 2 H ↔ x ∈ CFSG.pCore 2 ↥H := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [← this]
  · intro hx
    exact ⟨x, hx, rfl⟩

@[expose] noncomputable def barHom {H B : Subgroup G} (hBH : B ≤ H) :
    ↥B →* ↥H ⧸ CFSG.pCore 2 ↥H :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion hBH)

omit [Finite G] in
theorem barHom_apply {H B : Subgroup G} (hBH : B ≤ H) (x : ↥B) :
    barHom hBH x = QuotientGroup.mk (⟨x, hBH x.2⟩ : ↥H) := rfl

omit [Finite G] in
theorem range_barHom {H B : Subgroup G} (hBH : B ≤ H) :
    (barHom hBH).range = barImage H B := by
  ext y
  simp only [MonoidHom.mem_range, barImage, Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨⟨x, hBH x.2⟩, x.2, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩

theorem ker_barHom {H B : Subgroup G} (hB : IsBlock2 H B) :
    (barHom hB.2.1).ker = CFSG.pCore 2 ↥B := by
  ext x
  have hBH : B ≤ H := hB.2.1
  rw [MonoidHom.mem_ker, barHom_apply, QuotientGroup.eq_one_iff, ← coe_mem_pCoreOf_iff,
    ← coe_mem_pCoreOf_iff]
  have hq := blockQ_eq_inf_pCoreOf hB
  constructor
  · intro h
    have : (x : G) ∈ blockQ B := by
      rw [hq]
      exact ⟨x.2, h⟩
    exact this
  · intro h
    have : (x : G) ∈ B ⊓ pCoreOf 2 H := by
      rw [← hq]
      exact h
    exact this.2

theorem barEquiv {H B : Subgroup G} (hB : IsBlock2 H B) :
    Nonempty (↥B ⧸ CFSG.pCore 2 ↥B ≃* ↥(barImage H B)) := by
  have hker := ker_barHom hB
  have hrange := range_barHom hB.2.1
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange (barHom hB.2.1))).trans
      (MulEquiv.subgroupCongr hrange)⟩

omit [Finite G] in
theorem barImage_subnormal {H B : Subgroup G} (hB : IsBlock2 H B) : (barImage H B).IsSubnormal :=
  Subgroup.IsSubnormal.map (QuotientGroup.mk'_surjective _) hB.2.2

theorem isComponent_barImage {H B : Subgroup G} (hB : IsBlock2 H B)
    (hq : CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B)) : CFSG.IsComponent (barImage H B) := by
  obtain ⟨e⟩ := barEquiv hB
  exact ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, barImage_subnormal hB⟩

theorem card_barImage {H B : Subgroup G} (hB : IsBlock2 H B) :
    Nat.card ↥(barImage H B) = Nat.card (↥B ⧸ CFSG.pCore 2 ↥B) := by
  obtain ⟨e⟩ := barEquiv hB
  exact (Nat.card_congr e.toEquiv).symm

omit [Finite G] in
theorem le_sup_pCoreOf_of_barImage_le {H B₁ B₂ : Subgroup G} (hB₁ : B₁ ≤ H)
    (h : barImage H B₁ ≤ barImage H B₂) : B₁ ≤ B₂ ⊔ pCoreOf 2 H := by
  intro b hb
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨b, hB₁ hb⟩ : ↥H) ∈ barImage H B₁ :=
    ⟨⟨b, hB₁ hb⟩, hb, rfl⟩
  obtain ⟨y, hy, hyb⟩ := h hmem
  have hy' : (y : G) ∈ B₂ := hy
  have hq : y⁻¹ * (⟨b, hB₁ hb⟩ : ↥H) ∈ CFSG.pCore 2 ↥H := by
    rw [← QuotientGroup.eq]
    exact hyb
  have hq' : (y : G)⁻¹ * b ∈ pCoreOf 2 H := (coe_mem_pCoreOf_iff H _).mpr hq
  have : b = (y : G) * ((y : G)⁻¹ * b) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hy' hq'

omit [Finite G] in
theorem commutator_mem_pCoreOf_of_barImage {H B₁ B₂ : Subgroup G} (hB₁ : B₁ ≤ H) (hB₂ : B₂ ≤ H)
    (h : ⁅barImage H B₁, barImage H B₂⁆ = ⊥) :
    ∀ x ∈ B₁, ∀ y ∈ B₂, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H := by
  intro x hx y hy
  have hxm : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨x, hB₁ hx⟩ : ↥H) ∈ barImage H B₁ :=
    ⟨⟨x, hB₁ hx⟩, hx, rfl⟩
  have hym : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨y, hB₂ hy⟩ : ↥H) ∈ barImage H B₂ :=
    ⟨⟨y, hB₂ hy⟩, hy, rfl⟩
  have hc := Subgroup.commutator_mem_commutator hxm hym
  rw [h, Subgroup.mem_bot, ← map_commutatorElement, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hc
  have := (coe_mem_pCoreOf_iff H _).mpr hc
  simpa [commutatorElement_def] using this

theorem false_of_le_of_commutator_eq_bot {Γ : Type*} [Group Γ] {K U : Subgroup Γ}
    (hK : CFSG.IsQuasisimple ↥K) (hKU : K ≤ U) (h : ⁅K, U⁆ = ⊥) : False := by
  have h1 : ⁅K, K⁆ = ⊥ := le_bot_iff.mp (h ▸ Subgroup.commutator_mono le_rfl hKU)
  have h2 : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hK.1
  have h3 : K = ⊥ := h2.symm.trans h1
  have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hK
  exact (Subgroup.nontrivial_iff_ne_bot K).mp this h3

theorem commutator_mem_pCoreOf_of_quasisimple {H B₁ B₂ : Subgroup G} (hB₁ : IsBlock2 H B₁)
    (hq : CFSG.IsQuasisimple (↥B₁ ⧸ CFSG.pCore 2 ↥B₁)) (hB₂ : IsBlock2 H B₂) (hne : B₁ ≠ B₂) :
    ∀ x ∈ B₁, ∀ y ∈ B₂, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 H := by
  have hc₁ := isComponent_barImage hB₁ hq
  rcases CFSG.LocalCores.component_subnormal_subgroup hc₁ (barImage_subnormal hB₂) with hle | hcomm
  · exfalso
    rcases hB₂.1.2.2.2.1 with hq₂ | h3
    · have hc₂ := isComponent_barImage hB₂ hq₂
      rcases CFSG.LocalCores.component_subnormal_subgroup hc₂ (barImage_subnormal hB₁) with
        hle' | hcomm'
      · have heq : barImage H B₁ = barImage H B₂ := le_antisymm hle hle'
        have h1 : B₁ ≤ B₂ ⊔ pCoreOf 2 H :=
          le_sup_pCoreOf_of_barImage_le hB₁.2.1 heq.le
        have h2 : B₂ ≤ B₁ ⊔ pCoreOf 2 H :=
          le_sup_pCoreOf_of_barImage_le hB₂.2.1 heq.ge
        have e1 : B₁ ≤ B₂ := by
          calc B₁ = oTwoUpper B₁ := isShort2_eq_oTwoUpper hB₁.1
            _ ≤ oTwoUpper (B₂ ⊔ pCoreOf 2 H) := oTwoUpper_mono h1
            _ = B₂ := (isBlock2_normal_sup_pCore hB₂).1.symm
        have e2 : B₂ ≤ B₁ := by
          calc B₂ = oTwoUpper B₂ := isShort2_eq_oTwoUpper hB₂.1
            _ ≤ oTwoUpper (B₁ ⊔ pCoreOf 2 H) := oTwoUpper_mono h2
            _ = B₁ := (isBlock2_normal_sup_pCore hB₁).1.symm
        exact hne (le_antisymm e1 e2)
      · rw [Subgroup.commutator_comm] at hcomm'
        exact false_of_le_of_commutator_eq_bot hc₁.1 hle hcomm'
    · have hcard : Nat.card ↥(barImage H B₂) = 3 := (card_barImage hB₂).trans h3
      have : Fact (Nat.card ↥(barImage H B₂)).Prime := ⟨by rw [hcard]; exact Nat.prime_three⟩
      have hcomm₂ : ∀ a b : ↥(barImage H B₂), a * b = b * a := by
        have := isCyclic_of_prime_card (α := ↥(barImage H B₂)) hcard
        exact fun a b => (IsCyclic.commGroup (α := ↥(barImage H B₂))).mul_comm a b
      refine false_of_le_of_commutator_eq_bot hc₁.1 hle (le_bot_iff.mp ?_)
      refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
      rw [Subgroup.mem_bot]
      have := hcomm₂ ⟨a, hle ha⟩ ⟨b, hb⟩
      have h2 : a * b = b * a := congrArg Subtype.val this
      rw [commutatorElement_def, h2]
      group
  · exact commutator_mem_pCoreOf_of_barImage hB₁.2.1 hB₂.2.1 hcomm

end CFSG.Quasithin.C1Pack
