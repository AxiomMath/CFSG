module

public import CFSG.RankThree.PartTwo.Sec15.Item155w3ProofE81
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree.PartTwo
open scoped commutatorElement

namespace Wales154

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def barR (Y R : Subgroup G) : Subgroup (MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y)) :=
  (R.subgroupOf (Subgroup.normalizer (Y : Set G))).map (Sec17.Proof17Res6.actQ Y)

@[expose] noncomputable def innQ (Y : Subgroup G) : Subgroup (MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y)) :=
  (MulAut.conj : (↥Y ⧸ CFSG.pCore 2 ↥Y) →* MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y)).range

omit [Finite G] in
theorem mem_barR {Y R : Subgroup G} {r : G} (hr : r ∈ R)
    (hrY : r ∈ Subgroup.normalizer (Y : Set G)) :
    Sec17.Proof17Res6.actQ Y ⟨r, hrY⟩ ∈ barR Y R :=
  ⟨⟨r, hrY⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩

omit [Finite G] in
theorem actQ_mem_innQ {Y : Subgroup G} {y : G} (hy : y ∈ Y) :
    Sec17.Proof17Res6.actQ Y ⟨y, Y.le_normalizer hy⟩ ∈ innQ Y :=
  ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨y, hy⟩,
    (Sec17.Proof17Res6.actQ_of_mem (Y₀ := Y) ⟨y, hy⟩).symm⟩

omit [Finite G] in
theorem mul_conj_mul_inv_eq {Q : Type*} [Group Q] (σ : MulAut Q) (g : Q) :
    σ * MulAut.conj g * σ⁻¹ = MulAut.conj (σ g) := by
  ext y
  change σ (g * σ.symm y * g⁻¹) = σ g * y * (σ g)⁻¹
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

omit [Finite G] in
theorem innQ_normal (Y : Subgroup G) : (innQ Y).Normal := by
  refine ⟨fun τ hτ σ => ?_⟩
  obtain ⟨g, rfl⟩ := hτ
  exact ⟨σ g, (mul_conj_mul_inv_eq σ g).symm⟩

theorem commutator_le_pCoreOf_of_barR_eq_bot {Y R : Subgroup G}
    (hRY : R ≤ Subgroup.normalizer (Y : Set G)) (h : barR Y R = ⊥) :
    ⁅R, Y⁆ ≤ CFSG.Open.pCoreOf 2 Y := by
  rw [Subgroup.commutator_le]
  intro r hr y hy
  have h1 : Sec17.Proof17Res6.actQ Y ⟨r, hRY hr⟩ = 1 := by
    have h2 := mem_barR hr (hRY hr)
    rw [h, Subgroup.mem_bot] at h2
    exact h2
  rw [commutatorElement_def]
  exact Proof155w3.commutator_mem_of_actQ_eq_one h1 y hy

omit [Finite G] in
theorem actQ_mem_normalizer_barR {Y R : Subgroup G} {x : G}
    (hxY : x ∈ Subgroup.normalizer (Y : Set G)) (hxR : x ∈ Subgroup.normalizer (R : Set G)) :
    Sec17.Proof17Res6.actQ Y ⟨x, hxY⟩ ∈ Subgroup.normalizer (barR Y R : Set _) := by
  have key : ∀ {x : G} (hxY : x ∈ Subgroup.normalizer (Y : Set G)),
      x ∈ Subgroup.normalizer (R : Set G) → ∀ σ ∈ barR Y R,
        Sec17.Proof17Res6.actQ Y ⟨x, hxY⟩ * σ * (Sec17.Proof17Res6.actQ Y ⟨x, hxY⟩)⁻¹ ∈
          barR Y R := by
    intro x hxY hxR σ hσ
    obtain ⟨⟨r, hrN⟩, hrR, rfl⟩ := hσ
    have hrR' : r ∈ R := Subgroup.mem_subgroupOf.mp hrR
    rw [← map_inv, ← map_mul, ← map_mul]
    refine ⟨_, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hxR r).mp hrR'
  rw [Subgroup.mem_normalizer_iff]
  intro σ
  refine ⟨key hxY hxR σ, fun hσ => ?_⟩
  have h1 := key (inv_mem hxY) (inv_mem hxR) _ hσ
  have e : (⟨x⁻¹, inv_mem hxY⟩ : Subgroup.normalizer (Y : Set G)) = (⟨x, hxY⟩)⁻¹ := rfl
  rw [e, map_inv, inv_inv] at h1
  simpa [mul_assoc] using h1

theorem commute_of_barR_inf_innQ_eq_bot {X Y R : Subgroup G} (hXY : X ≤ Y)
    (hXR : X ≤ Subgroup.normalizer (R : Set G)) (h : barR Y R ⊓ innQ Y = ⊥)
    {σ : MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y)} (hσ : σ ∈ barR Y R) {x : G} (hx : x ∈ X) :
    σ * Sec17.Proof17Res6.actQ Y ⟨x, Y.le_normalizer (hXY hx)⟩ =
      Sec17.Proof17Res6.actQ Y ⟨x, Y.le_normalizer (hXY hx)⟩ * σ := by
  set τ := Sec17.Proof17Res6.actQ Y ⟨x, Y.le_normalizer (hXY hx)⟩ with hτdef
  have hτ : τ ∈ innQ Y := actQ_mem_innQ (hXY hx)
  have hτN : τ ∈ Subgroup.normalizer (barR Y R : Set _) :=
    actQ_mem_normalizer_barR (Y.le_normalizer (hXY hx)) (hXR hx)
  have hτσ : τ * σ⁻¹ * τ⁻¹ ∈ barR Y R :=
    (Subgroup.mem_normalizer_iff.mp hτN σ⁻¹).mp (inv_mem hσ)
  have hc1 : σ * τ * σ⁻¹ * τ⁻¹ ∈ barR Y R := by
    have e : σ * τ * σ⁻¹ * τ⁻¹ = σ * (τ * σ⁻¹ * τ⁻¹) := by group
    rw [e]
    exact mul_mem hσ hτσ
  have hc2 : σ * τ * σ⁻¹ * τ⁻¹ ∈ innQ Y :=
    mul_mem ((innQ_normal Y).conj_mem τ hτ σ) (inv_mem hτ)
  have hbot : σ * τ * σ⁻¹ * τ⁻¹ = 1 := by
    have h3 : σ * τ * σ⁻¹ * τ⁻¹ ∈ barR Y R ⊓ innQ Y := ⟨hc1, hc2⟩
    rw [h, Subgroup.mem_bot] at h3
    exact h3
  calc σ * τ = (σ * τ * σ⁻¹ * τ⁻¹) * τ * σ := by group
    _ = τ * σ := by rw [hbot, one_mul]

theorem barR_inf_innQ_facts {X Y R A : Subgroup G} (hRY : R ≤ Subgroup.normalizer (Y : Set G))
    (hR2 : IsPGroup 2 R) (hXY : X ≤ Y) (hXR : X ≤ Subgroup.normalizer (R : Set G))
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hAR : A ≤ Subgroup.normalizer (R : Set G)) :
    IsPGroup 2 (barR Y R ⊓ innQ Y : Subgroup _) ∧
      (∀ x (hx : x ∈ X), Sec17.Proof17Res6.actQ Y ⟨x, Y.le_normalizer (hXY hx)⟩ ∈
        Subgroup.normalizer ((barR Y R ⊓ innQ Y : Subgroup _) : Set _)) ∧
      ∀ a (ha : a ∈ A), Sec17.Proof17Res6.actQ Y ⟨a, hAY ha⟩ ∈
        Subgroup.normalizer ((barR Y R ⊓ innQ Y : Subgroup _) : Set _) := by
  have hR2' : IsPGroup 2 (R.subgroupOf (Subgroup.normalizer (Y : Set G))) :=
    hR2.of_equiv (Subgroup.subgroupOfEquivOfLe hRY).symm
  have hbar2 : IsPGroup 2 (barR Y R) := hR2'.map _
  have hnorm : ∀ τ : MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y),
      τ ∈ Subgroup.normalizer (barR Y R : Set _) →
        τ ∈ Subgroup.normalizer ((barR Y R ⊓ innQ Y : Subgroup _) : Set _) := by
    intro τ hτ
    rw [Subgroup.mem_normalizer_iff]
    intro σ
    rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp hτ σ]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, (innQ_normal Y).conj_mem σ h2 τ⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have h3 := (innQ_normal Y).conj_mem _ h2 τ⁻¹
      simpa [mul_assoc] using h3
  refine ⟨hbar2.to_le inf_le_left, fun x hx => hnorm _ ?_, fun a ha => hnorm _ ?_⟩
  · exact actQ_mem_normalizer_barR (Y.le_normalizer (hXY hx)) (hXR hx)
  · exact actQ_mem_normalizer_barR (hAY ha) (hAR ha)

theorem trichotomy154 {X Y R : Subgroup G} (hRY : R ≤ Subgroup.normalizer (Y : Set G))
    (hXY : X ≤ Y) (hXR : X ≤ Subgroup.normalizer (R : Set G)) :
    ⁅R, Y⁆ ≤ CFSG.Open.pCoreOf 2 Y ∨ barR Y R ⊓ innQ Y ≠ ⊥ ∨
      (barR Y R ≠ ⊥ ∧ barR Y R ⊓ innQ Y = ⊥ ∧
        ∀ σ ∈ barR Y R, ∀ x (hx : x ∈ X),
          σ * Sec17.Proof17Res6.actQ Y ⟨x, Y.le_normalizer (hXY hx)⟩ =
            Sec17.Proof17Res6.actQ Y ⟨x, Y.le_normalizer (hXY hx)⟩ * σ) := by
  by_cases h1 : barR Y R = ⊥
  · exact Or.inl (commutator_le_pCoreOf_of_barR_eq_bot hRY h1)
  by_cases h2 : barR Y R ⊓ innQ Y = ⊥
  · exact Or.inr (Or.inr ⟨h1, h2, fun σ hσ x hx =>
      commute_of_barR_inf_innQ_eq_bot hXY hXR h2 hσ hx⟩)
  · exact Or.inr (Or.inl h2)

end Wales154

end CFSG.RankThree.PartTwo.Sec15
