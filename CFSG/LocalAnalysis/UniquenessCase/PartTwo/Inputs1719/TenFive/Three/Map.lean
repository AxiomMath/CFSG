module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.Defs
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3Heis
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralProductExtraspecial
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.Heis
import CFSG.Monster.B.Short.Extraspecial

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.Open Subgroup
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3 (Heis)

theorem IsExtraGood.map {S T : Type*} [Group S] [Group T] {f : S →* T}
    (hf : Function.Injective f) {x : S} (h : IsExtraGood x) : IsExtraGood (f x) := by
  obtain ⟨H, N, hxH, hH, hN⟩ := h
  exact ⟨H.map f, N, Subgroup.mem_map_of_mem f hxH,
    IsSpecialType.of_mulEquiv (Subgroup.equivMapOfInjective H f hf) hH, hN⟩

private theorem congr_congr_symm {S T : Type*} [Group S] [Group T] (φ : S ≃* T) (σ : MulAut T) :
    MulAut.congr φ (MulAut.congr φ.symm σ) = σ := by
  ext x
  simp [MulAut.congr_apply]

theorem IsGenGood.of_mulEquiv {S T : Type*} [Group S] [Group T] (φ : S ≃* T) {σ : MulAut S}
    (h : IsGenGood σ) : IsGenGood (MulAut.congr φ σ) := by
  obtain ⟨k, g, y, r, hr, hy, hyD, hd⟩ := h
  refine ⟨k, fun i => φ (g i), φ y, r, hr, (MulEquiv.orderOf_eq φ y).trans hy, ?_, hd⟩
  have hrange : Set.range (fun i => (φ (g i))⁻¹ * (MulAut.congr φ σ) (φ (g i)))
      = (φ : S →* T) '' Set.range (fun i => (g i)⁻¹ * σ (g i)) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, by simp [map_mul, MulAut.congr_apply]⟩
    · rintro ⟨-, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, by simp [map_mul, MulAut.congr_apply]⟩
  have hmem : φ y ∈ (Subgroup.closure (Set.range fun i => (g i)⁻¹ * σ (g i))).map
      (φ : S →* T) := Subgroup.mem_map_of_mem _ hyD
  rwa [MonoidHom.map_closure, ← hrange] at hmem

theorem IsGenGood.conj {S : Type*} [Group S] {σ σ₀ γ : MulAut S} (hσ : σ = γ * σ₀ * γ⁻¹)
    (h : IsGenGood σ₀) : IsGenGood σ := by
  obtain ⟨k, g, y, r, hr, hy, hyD, hd⟩ := h
  have hkey : ∀ z, σ (γ z) = γ (σ₀ z) := by
    intro z
    rw [hσ]
    simp [MulAut.mul_apply]
  refine ⟨k, fun i => γ (g i), γ y, r, hr, (MulEquiv.orderOf_eq γ y).trans hy, ?_, hd⟩
  have hrange : Set.range (fun i => (γ (g i))⁻¹ * σ (γ (g i)))
      = (γ : S →* S) '' Set.range (fun i => (g i)⁻¹ * σ₀ (g i)) := by
    ext z
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, by simp [hkey, map_mul, map_inv]⟩
    · rintro ⟨-, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, by simp [hkey, map_mul, map_inv]⟩
  have hmem : γ y ∈ (Subgroup.closure (Set.range fun i => (g i)⁻¹ * σ₀ (g i))).map
      (γ : S →* S) := Subgroup.mem_map_of_mem _ hyD
  rwa [MonoidHom.map_closure, ← hrange] at hmem

theorem exists_inv_extraGood_of_conj {S : Type*} [Group S] {σ σ₀ γ : MulAut S}
    (hσ : σ = γ * σ₀ * γ⁻¹) {x : S} (hx : orderOf x = 3) (hinv : σ₀ x = x⁻¹)
    (hgood : IsExtraGood x) : ∃ y : S, orderOf y = 3 ∧ σ y = y⁻¹ ∧ IsExtraGood y := by
  refine ⟨γ x, (MulEquiv.orderOf_eq γ x).trans hx, ?_,
    IsExtraGood.map (f := (γ : S →* S)) γ.injective hgood⟩
  rw [hσ]
  simp [MulAut.mul_apply, hinv]

theorem InvolGood.of_mulEquiv {S T : Type*} [Group S] [Group T] (φ : S ≃* T)
    (h : InvolGood S) : InvolGood T := by
  intro σ hσ
  let σ' : MulAut S := MulAut.congr φ.symm σ
  have hσ' : orderOf σ' = 2 :=
    (MulEquiv.orderOf_eq (MulAut.congr φ.symm) σ).trans hσ
  rcases h σ' hσ' with ⟨x, hx, hinv, hgood⟩ | hgen
  · refine Or.inl ⟨φ x, (MulEquiv.orderOf_eq φ x).trans hx, ?_, ?_⟩
    · have hconj : σ (φ x) = φ (σ' x) := by
        simp [σ', MulAut.congr_apply]
      rw [hconj, hinv, map_inv]
    · exact IsExtraGood.map (f := (φ : S →* T)) φ.injective hgood
  · refine Or.inr ?_
    have hh : IsGenGood (MulAut.congr φ σ') := IsGenGood.of_mulEquiv φ hgen
    rwa [show MulAut.congr φ σ' = σ from congr_congr_symm φ σ] at hh

theorem InvolGen.of_mulEquiv {S T : Type*} [Group S] [Group T] (φ : S ≃* T)
    (h : InvolGen S) : InvolGen T := by
  intro σ hσ
  let σ' : MulAut S := MulAut.congr φ.symm σ
  have hσ' : orderOf σ' = 2 :=
    (MulEquiv.orderOf_eq (MulAut.congr φ.symm) σ).trans hσ
  have hh : IsGenGood (MulAut.congr φ σ') := IsGenGood.of_mulEquiv φ (h σ' hσ')
  rwa [show MulAut.congr φ σ' = σ from congr_congr_symm φ σ] at hh

theorem InvolGen.involGood {S : Type*} [Group S] (h : InvolGen S) : InvolGood S :=
  fun σ hσ => Or.inr (h σ hσ)

private theorem isExtraspecialPGroup_of_mulEquiv {p : ℕ} {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (h : CFSG.IsExtraspecialPGroup p G) : CFSG.IsExtraspecialPGroup p H := by
  obtain ⟨hp, hcomm, hfrat, hcard⟩ := h
  have hc : (Subgroup.center G).map (e : G →* H) = Subgroup.center H :=
    Subgroup.map_center_eq e
  have hcomm' : (_root_.commutator G).map (e : G →* H) = _root_.commutator H := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      ← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 e.surjective]
  have hfrat' : (frattini G).map (e : G →* H) = frattini H := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      exact frattini_le_comap_frattini_of_surjective e.surjective
    · intro x hx
      refine ⟨e.symm x, frattini_le_comap_frattini_of_surjective
        (φ := (e.symm : H →* G)) e.symm.surjective hx, ?_⟩
      exact e.apply_symm_apply x
  refine ⟨hp.of_equiv e, ?_, ?_, ?_⟩
  · rw [← hcomm', ← hc, hcomm]
  · rw [← hfrat', ← hc, hfrat]
  · rw [← hc, ← hcard]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ _ e.injective).toEquiv).symm

private theorem isExtraspecial_range_heis {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 3) {S : Type*} [Group S] {ι : Heis F →* S}
    (hι : Function.Injective ι) :
    CFSG.IsExtraspecial 3 ι.range ∧ Nat.card ↥ι.range = 27 ∧
      (∀ a : ↥ι.range, a ^ 3 = 1) := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 3 := by simpa using hF
  have : CharP F 3 := charP_of_card_eq_prime hF'
  have hsp : IsSpecialType 3 1 1 (Heis F) :=
    isSpecialType_heis (p := 3) (e := 1) (by norm_num) (by norm_num) (by rw [hF, pow_one])
  have hsp' : IsSpecialType 3 1 1 ↥ι.range :=
    hsp.of_mulEquiv (MonoidHom.ofInjective hι)
  have hcard : Nat.card ↥ι.range = 27 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hι).toEquiv, Heis.card_eq, hF]
    norm_num
  have hcardZ : Nat.card (Subgroup.center ↥ι.range) = 3 := by
    simpa using hsp'.2.2.1
  have hbotrel : (⊥ : Subgroup ↥ι.range).relIndex (Subgroup.center ↥ι.range) = 3 := by
    have h := Subgroup.relIndex_mul_card (H := ⊥) (K := Subgroup.center ↥ι.range)
    rw [bot_inf_eq, Subgroup.card_bot, Nat.mul_one, hcardZ] at h
    exact h
  have hPq : CFSG.IsExtraspecialPGroup 3 (↥ι.range ⧸ ⊥) :=
    hsp'.2.2.2 (D := ⊥) bot_le hbotrel
  have hP : CFSG.IsExtraspecialPGroup 3 ↥ι.range :=
    isExtraspecialPGroup_of_mulEquiv QuotientGroup.quotientBot hPq
  have : Finite ↥ι.range := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact ⟨(CFSG.isExtraspecialPGroup_iff_isExtraspecial).mp hP, hcard, hsp'.1⟩

private theorem inf_range_eq_center_map {F : Type*} [Field F] {S : Type*} [Group S]
    {ι₁ ι₂ : Heis F →* S} (h₁ : Function.Injective ι₁)
    (hcomm : ∀ a b, Commute (ι₁ a) (ι₂ b)) (hcen : ∀ c : F, ι₁ ⟨0, 0, c⟩ = ι₂ ⟨0, 0, c⟩) :
    ι₁.range ⊓ ι₂.range = (Subgroup.center (Heis F)).map ι₁ := by
  apply le_antisymm
  · rintro z ⟨hz₁, hz₂⟩
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hz₁
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hz₂
    refine Subgroup.mem_map_of_mem ι₁ ?_
    rw [Subgroup.mem_center_iff]
    intro y
    have h := (hcomm y b).eq
    rw [hb] at h
    exact h₁ (by rw [map_mul, map_mul]; exact h)
  · rintro z ⟨c, hc, rfl⟩
    refine ⟨MonoidHom.mem_range.mpr ⟨c, rfl⟩, ?_⟩
    have hc' := Heis.mem_center.mp hc
    have hceq : c = ⟨0, 0, c.c⟩ := by ext <;> simp [hc'.1, hc'.2]
    rw [hceq, hcen]
    exact MonoidHom.mem_range.mpr ⟨⟨0, 0, c.c⟩, rfl⟩

theorem isSpecialType_sup_heis_pair {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 3) {S : Type} [Group S] {ι₁ ι₂ : Heis F →* S}
    (h₁ : Function.Injective ι₁) (h₂ : Function.Injective ι₂)
    (hcomm : ∀ a b, Commute (ι₁ a) (ι₂ b))
    (hcen : ∀ c : F, ι₁ ⟨0, 0, c⟩ = ι₂ ⟨0, 0, c⟩) :
    IsSpecialType 3 1 2 ↥(ι₁.range ⊔ ι₂.range) := by
  obtain ⟨hEA, hcardA, hAexp⟩ := isExtraspecial_range_heis (ι := ι₁) hF h₁
  obtain ⟨hEB, hcardB, hBexp⟩ := isExtraspecial_range_heis (ι := ι₂) hF h₂
  have hcomm' : ∀ a ∈ ι₁.range, ∀ b ∈ ι₂.range, a * b = b * a := by
    rintro a ⟨u, rfl⟩ b ⟨v, rfl⟩
    exact (hcomm u v).eq
  have hAB : ι₁.range ⊓ ι₂.range = (Subgroup.center (Heis F)).map ι₁ :=
    inf_range_eq_center_map h₁ hcomm hcen
  have hcomp₁ : ι₁.range.subtype.comp (↑(MonoidHom.ofInjective h₁)) = ι₁ := by
    ext y
    exact MonoidHom.ofInjective_apply h₁
  have hcomp₂ : ι₂.range.subtype.comp (↑(MonoidHom.ofInjective h₂)) = ι₂ := by
    ext y
    exact MonoidHom.ofInjective_apply h₂
  have hcenterA : (Subgroup.center ↥ι₁.range).map ι₁.range.subtype
      = (Subgroup.center (Heis F)).map ι₁ := by
    rw [← Subgroup.map_center_eq (MonoidHom.ofInjective h₁), Subgroup.map_map, hcomp₁]
  have hcenterB : (Subgroup.center ↥ι₂.range).map ι₂.range.subtype
      = (Subgroup.center (Heis F)).map ι₂ := by
    rw [← Subgroup.map_center_eq (MonoidHom.ofInjective h₂), Subgroup.map_map, hcomp₂]
  have hcenmap : (Subgroup.center (Heis F)).map ι₁
      = (Subgroup.center (Heis F)).map ι₂ := by
    apply le_antisymm
    · rintro z ⟨c, hc, rfl⟩
      have hc' := Heis.mem_center.mp hc
      have hceq : c = ⟨0, 0, c.c⟩ := by ext <;> simp [hc'.1, hc'.2]
      rw [hceq, hcen]
      exact Subgroup.mem_map_of_mem ι₂ (Heis.mem_center.mpr ⟨rfl, rfl⟩)
    · rintro z ⟨c, hc, rfl⟩
      have hc' := Heis.mem_center.mp hc
      have hceq : c = ⟨0, 0, c.c⟩ := by ext <;> simp [hc'.1, hc'.2]
      rw [hceq, ← hcen]
      exact Subgroup.mem_map_of_mem ι₁ (Heis.mem_center.mpr ⟨rfl, rfl⟩)
  have hZA : ι₁.range ⊓ ι₂.range
      = (Subgroup.center ↥ι₁.range).map ι₁.range.subtype := hAB.trans hcenterA.symm
  have hZB : ι₁.range ⊓ ι₂.range
      = (Subgroup.center ↥ι₂.range).map ι₂.range.subtype :=
    (hAB.trans hcenmap).trans hcenterB.symm
  obtain ⟨hEsup, hsupcard⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.isExtraspecial_sup_of_two_extraspecial_27
      hEA hEB hcardA hcardB hAexp hBexp hcomm' hZA hZB
  have hExp : Monoid.exponent ↥(ι₁.range ⊔ ι₂.range) = 3 :=
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.exponent_sup_eq_three
      hcomm' hAexp hBexp hsupcard
  have hexp : ∀ y : ↥(ι₁.range ⊔ ι₂.range), y ^ 3 = 1 := by
    intro y
    rw [← hExp]
    exact Monoid.pow_exponent_eq_one y
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Finite ↥(ι₁.range ⊔ ι₂.range) :=
    Nat.finite_of_card_ne_zero (by rw [hsupcard]; norm_num)
  refine ⟨hexp, ?_, ?_, ?_⟩
  · rw [hsupcard]
  · rw [hEsup.center_order_p]
    norm_num
  · intro D hDnorm hDle hDrel
    have hDbot : D = ⊥ := by
      have h := Subgroup.relIndex_mul_card (H := D)
        (K := Subgroup.center ↥(ι₁.range ⊔ ι₂.range))
      rw [inf_eq_left.mpr hDle, hDrel, hEsup.center_order_p] at h
      have hcardD : Nat.card ↥D = 1 := by omega
      exact Subgroup.eq_bot_of_card_eq D hcardD
    have hP : CFSG.IsExtraspecialPGroup 3 (↥(ι₁.range ⊔ ι₂.range) ⧸ ⊥) :=
      isExtraspecialPGroup_of_mulEquiv QuotientGroup.quotientBot.symm
        (CFSG.IsExtraspecial.isExtraspecialPGroup (p := 3) (hE := hEsup))
    exact isExtraspecialPGroup_of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq hDbot).symm hP

theorem isExtraGood_of_mem_sup_heis_pair {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 3)
    {S : Type} [Group S] {ι₁ ι₂ : Heis F →* S} (h₁ : Function.Injective ι₁)
    (h₂ : Function.Injective ι₂) (hcomm : ∀ a b, Commute (ι₁ a) (ι₂ b))
    (hcen : ∀ c : F, ι₁ ⟨0, 0, c⟩ = ι₂ ⟨0, 0, c⟩) {x : S} (hx : x ∈ ι₁.range ⊔ ι₂.range) :
    IsExtraGood x :=
  ⟨ι₁.range ⊔ ι₂.range, 2, hx, isSpecialType_sup_heis_pair hF h₁ h₂ hcomm hcen, le_rfl⟩

theorem isExtraGood_of_heis_pair {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 3)
    {S : Type*} [Group S] {ι₁ ι₂ : Heis F →* S} (h₁ : Function.Injective ι₁)
    (h₂ : Function.Injective ι₂) (hcomm : ∀ a b, Commute (ι₁ a) (ι₂ b))
    (hcen : ∀ c : F, ι₁ ⟨0, 0, c⟩ = ι₂ ⟨0, 0, c⟩) (x : Heis F) : IsExtraGood (ι₁ x) := by
  classical
  obtain ⟨hEA, hcardA, -⟩ := isExtraspecial_range_heis (ι := ι₁) hF h₁
  obtain ⟨-, hcardB, -⟩ := isExtraspecial_range_heis (ι := ι₂) hF h₂
  have hcomm' : ∀ a ∈ ι₁.range, ∀ b ∈ ι₂.range, a * b = b * a := by
    rintro a ⟨u, rfl⟩ b ⟨v, rfl⟩
    exact (hcomm u v).eq
  have hAB : ι₁.range ⊓ ι₂.range = (Subgroup.center (Heis F)).map ι₁ :=
    inf_range_eq_center_map h₁ hcomm hcen
  have hcomp₁ : ι₁.range.subtype.comp (↑(MonoidHom.ofInjective h₁)) = ι₁ := by
    ext y
    exact MonoidHom.ofInjective_apply h₁
  have hcomp₂ : ι₂.range.subtype.comp (↑(MonoidHom.ofInjective h₂)) = ι₂ := by
    ext y
    exact MonoidHom.ofInjective_apply h₂
  have hcenterA : (Subgroup.center ↥ι₁.range).map ι₁.range.subtype
      = (Subgroup.center (Heis F)).map ι₁ := by
    rw [← Subgroup.map_center_eq (MonoidHom.ofInjective h₁), Subgroup.map_map, hcomp₁]
  have hcenterB : (Subgroup.center ↥ι₂.range).map ι₂.range.subtype
      = (Subgroup.center (Heis F)).map ι₂ := by
    rw [← Subgroup.map_center_eq (MonoidHom.ofInjective h₂), Subgroup.map_map, hcomp₂]
  have hcenmap : (Subgroup.center (Heis F)).map ι₁
      = (Subgroup.center (Heis F)).map ι₂ := by
    apply le_antisymm
    · rintro z ⟨c, hc, rfl⟩
      have hc' := Heis.mem_center.mp hc
      have hceq : c = ⟨0, 0, c.c⟩ := by ext <;> simp [hc'.1, hc'.2]
      rw [hceq, hcen]
      exact Subgroup.mem_map_of_mem ι₂ (Heis.mem_center.mpr ⟨rfl, rfl⟩)
    · rintro z ⟨c, hc, rfl⟩
      have hc' := Heis.mem_center.mp hc
      have hceq : c = ⟨0, 0, c.c⟩ := by ext <;> simp [hc'.1, hc'.2]
      rw [hceq, ← hcen]
      exact Subgroup.mem_map_of_mem ι₁ (Heis.mem_center.mpr ⟨rfl, rfl⟩)
  have hZA : ι₁.range ⊓ ι₂.range
      = (Subgroup.center ↥ι₁.range).map ι₁.range.subtype := hAB.trans hcenterA.symm
  have hZB : ι₁.range ⊓ ι₂.range
      = (Subgroup.center ↥ι₂.range).map ι₂.range.subtype :=
    (hAB.trans hcenmap).trans hcenterB.symm
  have hcardZ : Nat.card ↥(ι₁.range ⊓ ι₂.range) = 3 := by
    rw [hZA, Subgroup.card_map_of_injective ι₁.range.subtype_injective]
    exact hEA.center_order_p
  have hcardH : Nat.card ↥(ι₁.range ⊔ ι₂.range) = 3 ^ 5 := by
    have h := CFSG.GH74.GLS.Stage1.Thm3.Sec7.A.card_sup_mul_card_inf_of_commute hcomm'
    rw [hcardA, hcardB, hcardZ] at h
    have h' : Nat.card ↥(ι₁.range ⊔ ι₂.range) * 3 = 3 ^ 5 * 3 := by
      calc Nat.card ↥(ι₁.range ⊔ ι₂.range) * 3 = 27 * 27 := h
        _ = 3 ^ 5 * 3 := by norm_num
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'
  have : Finite ↥(ι₁.range ⊔ ι₂.range) :=
    Nat.finite_of_card_ne_zero (by rw [hcardH]; norm_num)
  have : Small.{0} ↥(ι₁.range ⊔ ι₂.range) := inferInstance
  let H : Subgroup S := ι₁.range ⊔ ι₂.range
  let e : Shrink.{0} ↥H ≃* ↥H := Shrink.mulEquiv
  let j₁ : Heis F →* ↥H :=
    { toFun := fun a => ⟨ι₁ a, Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨a, rfl⟩)⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  let j₂ : Heis F →* ↥H :=
    { toFun := fun b => ⟨ι₂ b, Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨b, rfl⟩)⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by ext; simp }
  have hj₁ : Function.Injective j₁ := by
    intro a b hab
    exact h₁ (by simpa [j₁] using congrArg (fun z : ↥H => (z : S)) hab)
  have hj₂ : Function.Injective j₂ := by
    intro a b hab
    exact h₂ (by simpa [j₂] using congrArg (fun z : ↥H => (z : S)) hab)
  let ι₁' : Heis F →* Shrink.{0} ↥H := e.symm.toMonoidHom.comp j₁
  let ι₂' : Heis F →* Shrink.{0} ↥H := e.symm.toMonoidHom.comp j₂
  have hι₁' : Function.Injective ι₁' := e.symm.injective.comp hj₁
  have hι₂' : Function.Injective ι₂' := e.symm.injective.comp hj₂
  have hcomm'' : ∀ a b, Commute (ι₁' a) (ι₂' b) := by
    intro a b
    have hH : Commute (j₁ a) (j₂ b) := by
      rw [commute_iff_eq]
      exact Subtype.ext (hcomm a b).eq
    exact hH.map e.symm.toMonoidHom
  have hcen'' : ∀ c, ι₁' ⟨0, 0, c⟩ = ι₂' ⟨0, 0, c⟩ := by
    intro c
    have hH : j₁ ⟨0, 0, c⟩ = j₂ ⟨0, 0, c⟩ := Subtype.ext (hcen c)
    exact congrArg e.symm hH
  have hspecial : IsSpecialType 3 1 2 ↥(ι₁'.range ⊔ ι₂'.range) :=
    isSpecialType_sup_heis_pair hF hι₁' hι₂' hcomm'' hcen''
  have hgood : IsExtraGood (ι₁' x) :=
    ⟨ι₁'.range ⊔ ι₂'.range, 2, Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨x, rfl⟩),
      hspecial, le_rfl⟩
  have hinj : Function.Injective (H.subtype.comp e.toMonoidHom) :=
    H.subtype_injective.comp e.injective
  have hmap := IsExtraGood.map (f := H.subtype.comp e.toMonoidHom) hinj hgood
  simpa [j₁, ι₁'] using hmap

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
