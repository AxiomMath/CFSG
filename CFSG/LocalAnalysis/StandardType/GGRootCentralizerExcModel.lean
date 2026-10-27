module

public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerSUBasic
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinberg

public section

namespace CFSG.StandardType

namespace RootCentExc

open Subgroup

section General

variable {C : Type*} [Group C]

abbrev CentTwoGen (z : C) : Prop :=
  Subgroup.centralizer ({z} : Set C) ≤ ggOTwoPrime (Subgroup.centralizer ({z} : Set C))

theorem CentTwoGen.conj {z : C} (h : CentTwoGen z) (g : C) : CentTwoGen (g * z * g⁻¹) :=
  OTwoGen.centralizer_conj_le_ggOTwoPrime h g

theorem CentTwoGen.of_conj {z g : C} (h : CentTwoGen (g * z * g⁻¹)) : CentTwoGen z := by
  have h' := h.conj g⁻¹
  rwa [show g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z by group] at h'

theorem centralizer_map_mulEquiv {C' : Type*} [Group C'] (α : C ≃* C') (z : C) :
    Subgroup.centralizer ({α z} : Set C') =
      (Subgroup.centralizer ({z} : Set C)).map α.toMonoidHom := by
  ext y
  constructor
  · intro hy
    refine ⟨α.symm y, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    apply α.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hw
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hw]

theorem CentTwoGen.map {C' : Type*} [Group C'] {z : C} (h : CentTwoGen z) (α : C ≃* C') :
    CentTwoGen (α z) := by
  rw [CentTwoGen, centralizer_map_mulEquiv]
  exact (Subgroup.map_mono h).trans (LinFusion.map_ggOTwoPrime_le _ _)

theorem centTwoGen_of_le_closure {z : C}
    (h : Subgroup.centralizer ({z} : Set C) ≤ Subgroup.closure
      {y | y ∈ Subgroup.centralizer ({z} : Set C) ∧ y * y = 1}) :
    CentTwoGen z :=
  h.trans (Subgroup.closure_mono fun y hy => ⟨hy.1, 1, by rw [pow_one, pow_two, hy.2]⟩)

end General

section Model

variable {U C G : Type*} [Group U] [Group C] [Group G]

theorem mem_range_of_mul_mem_centralizer {ψ : U →* G}
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {y g : G} (hg : g ∈ ψ.range)
    (hyg : y * g ∈ Subgroup.centralizer (ψ.range : Set G)) : y ∈ ψ.range := by
  rw [hC, Subgroup.mem_bot] at hyg
  rw [eq_inv_of_mul_eq_one_left hyg]
  exact ψ.range.inv_mem hg

theorem inf_centralizer_le_of_model {ψ : U →* G} {π : U →* C} (hπ : Function.Surjective π)
    (hker : π.ker = ψ.ker) {w : U} (hw : CentTwoGen (π w)) :
    ψ.range ⊓ Subgroup.centralizer {ψ w} ≤ ggOTwoPrime (ψ.range ⊓ Subgroup.centralizer {ψ w}) := by
  set Θ := AutSt.modelEquiv ψ π hπ hker
  let Θ' : C →* G := ψ.range.subtype.comp Θ.toMonoidHom
  have hΘ' : ∀ v, Θ' (π v) = ψ v := fun v => AutSt.modelEquiv_apply ψ π hπ hker v
  have hinj : Function.Injective Θ' := Subtype.val_injective.comp Θ.injective
  have hrange : Θ'.range = ψ.range := by
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      exact (Θ c).2
    · intro hx
      exact ⟨Θ.symm ⟨x, hx⟩, by simp [Θ']⟩
  have h := OTwoGen.inf_centralizer_le_ggOTwoPrime Θ' hinj hw
  rwa [hrange, hΘ'] at h

theorem exists_zpowers_sup_of_model {ψ : U →* G} {π : U →* C} (hπ : Function.Surjective π)
    (hker : π.ker = ψ.ker) {w : U} (hw : CentTwoGen (π w)) (Y : Subgroup G)
    (hY : ∀ y ∈ Y, y ∈ ψ.range ⊓ Subgroup.centralizer {ψ w}) :
    ∃ y₀ ∈ Y, Y ≤ Subgroup.zpowers y₀ ⊔ ggOTwoPrime (ψ.range ⊓ Subgroup.centralizer {ψ w}) :=
  ⟨1, Y.one_mem, fun y hy =>
    Subgroup.mem_sup_right (inf_centralizer_le_of_model hπ hker hw (hY y hy))⟩

end Model

section Param

theorem mulAut_mul_conj_mul_inv_eq {M : Type*} [Group M] (φ : MulAut M) (g : M) :
    φ * MulAut.conj g * φ⁻¹ = MulAut.conj (φ g) := by
  ext x
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul,
    map_inv, MulAut.apply_inv_self]

theorem normal_range_mulAutConj {M : Type*} [Group M] :
    (MulAut.conj : M →* MulAut M).range.Normal :=
  ⟨fun _ ⟨g, hg⟩ φ => ⟨φ g, by rw [← hg, mulAut_mul_conj_mul_inv_eq]⟩⟩

variable {G : Type*} [Group G] {H : Subgroup G}

theorem mem_of_normalizerMonoidHom_mem_range (hC : Subgroup.centralizer (H : Set G) = ⊥)
    {y : Subgroup.normalizer (H : Set G)}
    (hy : H.normalizerMonoidHom y ∈ (MulAut.conj : H →* MulAut H).range) : (y : G) ∈ H := by
  obtain ⟨w, hw⟩ := hy
  have hcent : (w : G)⁻¹ * y ∈ Subgroup.centralizer (H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h := congrArg (fun φ : MulAut H => ((φ ⟨x, hx⟩ : H) : G)) hw
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv] at h
    change (w : G) * x * (w : G)⁻¹ = (y : G) * x * (y : G)⁻¹ at h
    calc x * ((w : G)⁻¹ * y) = (w : G)⁻¹ * ((w : G) * x * (w : G)⁻¹) * y := by group
      _ = (w : G)⁻¹ * ((y : G) * x * (y : G)⁻¹) * y := by rw [h]
      _ = (w : G)⁻¹ * y * x := by group
  rw [hC, Subgroup.mem_bot, inv_mul_eq_one] at hcent
  rw [← hcent]
  exact w.2

theorem exists_mem_zpowers_mul_of_param (hC : Subgroup.centralizer (H : Set G) = ⊥)
    {A : Type*} [CommGroup A] (T : Subgroup A)
    (hT : ∀ a a' : A, a' ∉ T → ∃ k : ℕ, a * (a' ^ k)⁻¹ ∈ T)
    (D : A →* MulAut H) (hDT : ∀ t ∈ T, D t ∈ (MulAut.conj : H →* MulAut H).range)
    {Y : Subgroup G} (hYN : Y ≤ Subgroup.normalizer (H : Set G))
    (hY : ∀ y (hy : y ∈ Y), ∃ a : A,
      H.normalizerMonoidHom ⟨y, hYN hy⟩ * (D a)⁻¹ ∈ (MulAut.conj : H →* MulAut H).range) :
    ∃ y₀ ∈ Y, ∀ y ∈ Y, ∃ k : ℕ, y * (y₀ ^ k)⁻¹ ∈ H := by
  set I := (MulAut.conj : H →* MulAut H).range with hI
  have hIn : I.Normal := normal_range_mulAutConj
  set π := QuotientGroup.mk' I with hπ
  set κ := H.normalizerMonoidHom with hκ
  have hpar : ∀ y (hy : y ∈ Y), ∃ a, π (κ ⟨y, hYN hy⟩) = π (D a) := by
    intro y hy
    obtain ⟨a, ha⟩ := hY y hy
    refine ⟨a, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have h := hIn.conj_mem _ (I.inv_mem ha) (κ ⟨y, hYN hy⟩)⁻¹
    convert h using 1
    group
  have hinn : ∀ y (hy : y ∈ Y), π (κ ⟨y, hYN hy⟩) = 1 → y ∈ H := fun y hy h =>
    mem_of_normalizerMonoidHom_mem_range hC ((QuotientGroup.eq_one_iff _).mp h)
  by_cases hall : ∀ y (hy : y ∈ Y), π (κ ⟨y, hYN hy⟩) = 1
  · refine ⟨1, Y.one_mem, fun y hy => ⟨0, ?_⟩⟩
    rw [pow_zero, inv_one, mul_one]
    exact hinn y hy (hall y hy)
  · push Not at hall
    obtain ⟨y₀, hy₀, hne⟩ := hall
    obtain ⟨a₀, ha₀⟩ := hpar y₀ hy₀
    have ha₀T : a₀ ∉ T := fun h =>
      hne (by rw [ha₀]; exact (QuotientGroup.eq_one_iff _).mpr (hDT a₀ h))
    refine ⟨y₀, hy₀, fun y hy => ?_⟩
    obtain ⟨a, ha⟩ := hpar y hy
    obtain ⟨k, hk⟩ := hT a a₀ ha₀T
    refine ⟨k, ?_⟩
    have hmem : y * (y₀ ^ k)⁻¹ ∈ Y := Y.mul_mem hy (Y.inv_mem (Y.pow_mem hy₀ k))
    refine hinn _ hmem ?_
    have e : (⟨y * (y₀ ^ k)⁻¹, hYN hmem⟩ : Subgroup.normalizer (H : Set G)) =
        ⟨y, hYN hy⟩ * (⟨y₀, hYN hy₀⟩ ^ k)⁻¹ := Subtype.ext (by simp)
    rw [e, map_mul, map_mul, map_inv, map_inv, map_pow, map_pow, ha, ha₀, ← map_pow, ← map_inv,
      ← map_mul, ← map_pow D, ← map_inv D, ← map_mul D]
    exact (QuotientGroup.eq_one_iff _).mpr (hDT _ hk)

theorem exists_zpowers_sup_of_model_param {U C : Type*} [Group U] [Group C] {ψ : U →* G}
    {π : U →* C} (hπ : Function.Surjective π) (hker : π.ker = ψ.ker)
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {w : U} (hw : CentTwoGen (π w))
    {A : Type*} [CommGroup A] (T : Subgroup A)
    (hT : ∀ a a' : A, a' ∉ T → ∃ k : ℕ, a * (a' ^ k)⁻¹ ∈ T)
    (D : A →* MulAut ψ.range) (hDT : ∀ t ∈ T, D t ∈ (MulAut.conj : ψ.range →* MulAut ψ.range).range)
    (Y : Subgroup G) (hYN : Y ≤ Subgroup.normalizer (ψ.range : Set G))
    (hYr : Y ≤ Subgroup.centralizer {ψ w})
    (hY : ∀ y (hy : y ∈ Y), ∃ a : A, ψ.range.normalizerMonoidHom ⟨y, hYN hy⟩ * (D a)⁻¹ ∈
      (MulAut.conj : ψ.range →* MulAut ψ.range).range) :
    ∃ y₀ ∈ Y, Y ≤ Subgroup.zpowers y₀ ⊔ ggOTwoPrime (ψ.range ⊓ Subgroup.centralizer {ψ w}) := by
  obtain ⟨y₀, hy₀, hk⟩ := exists_mem_zpowers_mul_of_param hC T hT D hDT hYN hY
  refine ⟨y₀, hy₀, fun y hy => ?_⟩
  obtain ⟨k, hyk⟩ := hk y hy
  have hmem : y * (y₀ ^ k)⁻¹ ∈ ψ.range ⊓ Subgroup.centralizer {ψ w} :=
    ⟨hyk, hYr (Y.mul_mem hy (Y.inv_mem (Y.pow_mem hy₀ k)))⟩
  have h1 := inf_centralizer_le_of_model hπ hker hw hmem
  have e : y = y * (y₀ ^ k)⁻¹ * y₀ ^ k := by group
  rw [e, sup_comm]
  exact Subgroup.mul_mem_sup h1 (Subgroup.pow_mem _ (Subgroup.mem_zpowers y₀) k)

end Param

end RootCentExc

end CFSG.StandardType
