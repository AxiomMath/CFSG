module

public import CFSG.RankThree.PartTwo.Sec4.Item424Res3ProofE9
public import CFSG.RankThree.PartTwo.Sec4.Item424Res3ProofOrder

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item424Res3

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GH74.GLS.IVK (fixedField fixedField_apply mem_fixedField_iff fixedField_card_pow)

theorem commutator_mul_central {G : Type*} [Group G] {a b u v : G}
    (hu : u ∈ Subgroup.center G) (hv : v ∈ Subgroup.center G) :
    (a * u) * (b * v) * (a * u)⁻¹ * (b * v)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have hu' := Subgroup.mem_center_iff.mp hu
  have hv' := Subgroup.mem_center_iff.mp hv
  have h1 : u * (b * v) * u⁻¹ = b * v := by rw [← hu' (b * v), mul_inv_cancel_right]
  have h2 : v * a⁻¹ * v⁻¹ = a⁻¹ := by rw [← hv' a⁻¹, mul_inv_cancel_right]
  calc (a * u) * (b * v) * (a * u)⁻¹ * (b * v)⁻¹ =
      a * (u * (b * v) * u⁻¹) * a⁻¹ * (b * v)⁻¹ := by group
    _ = a * b * (v * a⁻¹ * v⁻¹) * b⁻¹ := by rw [h1]; group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [h2]

section Fixed

variable {F : Type} [Field F] {n : ℕ}

theorem slMap_subtype_injective (σ : F ≃+* F) :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin n) (fixedField σ).subtype) := by
  intro A B hAB
  ext i j
  have h := congrArg (fun C : Matrix.SpecialLinearGroup (Fin n) F =>
    (C : Matrix (Fin n) (Fin n) F) i j) hAB
  exact h

theorem exists_slMap_subtype_eq {σ : F ≃+* F} {A : Matrix.SpecialLinearGroup (Fin n) F}
    (hA : Matrix.SpecialLinearGroup.map σ.toRingHom A = A) :
    ∃ A₀ : Matrix.SpecialLinearGroup (Fin n) (fixedField σ),
      Matrix.SpecialLinearGroup.map (fixedField σ).subtype A₀ = A := by
  set K₀ := fixedField σ
  have hfix : ∀ i j, σ ((A : Matrix (Fin n) (Fin n) F) i j) = (A : Matrix (Fin n) (Fin n) F) i j :=
    fun i j => congrFun (congrFun (congrArg (fun B : Matrix.SpecialLinearGroup (Fin n) F =>
      (B : Matrix (Fin n) (Fin n) F)) hA) i) j
  set M : Matrix (Fin n) (Fin n) K₀ := fun i j =>
    ⟨(A : Matrix (Fin n) (Fin n) F) i j, (mem_fixedField_iff σ _).mpr (hfix i j)⟩
  have hM : M.map K₀.subtype = (A : Matrix (Fin n) (Fin n) F) := by
    ext i j
    rfl
  have hdet : M.det = 1 := by
    apply K₀.subtype_injective
    rw [map_one, RingHom.map_det, RingHom.mapMatrix_apply, hM]
    exact A.2
  exact ⟨⟨M, hdet⟩, Subtype.ext hM⟩

theorem slMap_map_subtype (σ : F ≃+* F) (A₀ : Matrix.SpecialLinearGroup (Fin n) (fixedField σ)) :
    Matrix.SpecialLinearGroup.map σ.toRingHom
        (Matrix.SpecialLinearGroup.map (fixedField σ).subtype A₀) =
      Matrix.SpecialLinearGroup.map (fixedField σ).subtype A₀ := by
  ext i j
  exact fixedField_apply σ (A₀ i j)

theorem mem_center_of_slMap_mem_center (σ : F ≃+* F)
    {A₀ : Matrix.SpecialLinearGroup (Fin n) (fixedField σ)}
    (h : Matrix.SpecialLinearGroup.map (fixedField σ).subtype A₀ ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F)) :
    A₀ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (fixedField σ)) := by
  rw [Subgroup.mem_center_iff]
  intro B₀
  apply slMap_subtype_injective σ
  rw [map_mul, map_mul]
  exact Subgroup.mem_center_iff.mp h _

end Fixed

theorem center_sl_three_eq_bot {K : Type} [Field K] (hK : Nat.card K % 3 = 2) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  have h1 := KFacts.units_eq_one_of_pow_three_eq_one (K := K) hK (c := Units.mk0 r hr0)
    (Units.ext (by simpa using hr))
  have hr1 : r = 1 := by simpa using congrArg Units.val h1
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hrA, hr1]
  simp

theorem exists_two_pow_of_hasType424_of_hom {F₀ : Type} [Field F₀] [Finite F₀] {n : ℕ}
    (hn : 3 ≤ n) {Γ : Type} [Group Γ] [Finite Γ]
    (ρ : Matrix.SpecialLinearGroup (Fin n) F₀ →* Γ)
    (hker : ρ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F₀))
    (hcomm : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ ρ.range)
    (h : Sec11.KS11Lie2Proof.HasType424 Γ) :
    n = 3 ∧ ∃ m : ℕ, Nat.card F₀ = 2 ^ m ∧ Odd m := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hY : IsQuasisimple (Matrix.SpecialLinearGroup (Fin (m + 1)) F₀) :=
    CFSG.LieType.Universal.SpecialLinear.isQuasisimple m F₀ (by omega)
  set ρ' := ρ.rangeRestrict with hρ'
  have hρ's : Function.Surjective ρ' := ρ.rangeRestrict_surjective
  have hker' : ρ'.ker ≤ Subgroup.center _ := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  have hN : IsQuasisimple ρ.range := CFSG.LocalCores.isQuasisimple_of_surjective hY ρ' hρ's hker'
  obtain ⟨hT, hQ⟩ := isType424_of_hasType424 ρ.range hN hcomm h
  set ψ := (QuotientGroup.mk' (aschbacherSolvableCore 3 ρ.range)).comp ρ' with hψ
  have hψker : ψ.ker ≤ Subgroup.center _ := ker_le_center_of_comp hY ρ' hρ's hker'
  obtain ⟨hm3, hq⟩ := eq_three_and_mod_of_isType424 (by omega) hT hQ ψ hψker
  obtain rfl : m = 2 := by omega
  refine ⟨rfl, ?_⟩
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    exact hψker.trans (center_sl_three_eq_bot hq).le
  have hψsurj : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hρ's
  have hcard : Nat.card (ρ.range ⧸ aschbacherSolvableCore 3 ρ.range) =
      Nat.card F₀ ^ 3 * ((Nat.card F₀ ^ 2 - 1) * (Nat.card F₀ ^ 3 - 1)) := by
    rw [← Nat.card_congr (MulEquiv.ofBijective ψ ⟨hψinj, hψsurj⟩).toEquiv]
    exact KFacts.card_sl_three_eq F₀
  have : Fintype F₀ := Fintype.ofFinite F₀
  obtain ⟨p, hpc⟩ := CharP.exists F₀
  obtain ⟨k, hp, hk⟩ := FiniteField.card F₀ p
  rw [← Nat.card_eq_fintype_card] at hk
  have hp2 : p = 2 := by
    by_contra hp2
    have hq5 : 5 ≤ p ^ (k : ℕ) := by
      have h1 : 1 < p ^ (k : ℕ) := Nat.one_lt_pow (PNat.ne_zero k) hp.one_lt
      have hodd : Odd (p ^ (k : ℕ)) := (hp.odd_of_ne_two hp2).pow
      rw [hk] at hq
      obtain ⟨j, hj⟩ := hodd
      omega
    rw [hk] at hcard
    exact not_isType424_of_card hp hp2 hq5 hcard hT
  subst hp2
  refine ⟨k, hk, ?_⟩
  rcases Nat.even_or_odd (k : ℕ) with ⟨j, hj⟩ | hodd
  · exfalso
    rw [hk, hj, ← two_mul, pow_mul, Nat.pow_mod] at hq
    norm_num at hq
  · exact hodd

section Models

variable {F : Type} [Field F] {n : ℕ}

@[expose] noncomputable def projFixHom (σ : F ≃+* F) :
    Matrix.SpecialLinearGroup (Fin n) (fixedField σ) →* Item426.fixSub (fieldAut n F σ) :=
  ((proj n F).comp (Matrix.SpecialLinearGroup.map (fixedField σ).subtype)).codRestrict _
    fun A₀ => by
      rw [Item426.mem_fixSub, MonoidHom.comp_apply, fieldAut_proj]
      exact congrArg (proj n F) (slMap_map_subtype σ A₀)

theorem projFixHom_ker_le (σ : F ≃+* F) :
    (projFixHom (n := n) σ).ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (fixedField σ)) := by
  intro A₀ hA₀
  have h1 : proj n F (Matrix.SpecialLinearGroup.map (fixedField σ).subtype A₀) = 1 :=
    congrArg Subtype.val hA₀
  rw [proj_eq_one_iff, scalars_eq_center] at h1
  exact mem_center_of_slMap_mem_center σ h1

theorem commutator_mem_range_projFixHom (σ : F ≃+* F) (a b : Item426.fixSub (fieldAut n F σ)) :
    a * b * a⁻¹ * b⁻¹ ∈ (projFixHom (n := n) σ).range := by
  obtain ⟨A, hA⟩ := proj_surjective n F a
  obtain ⟨B, hB⟩ := proj_surjective n F b
  have hσ : ∀ {A : Matrix.SpecialLinearGroup (Fin n) F}, fieldAut n F σ (proj n F A) = proj n F A →
      ∃ u ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F),
        Matrix.SpecialLinearGroup.map σ.toRingHom A = A * u := by
    intro A hA
    rw [fieldAut_proj, eq_comm, proj_eq_proj_iff, scalars_eq_center] at hA
    exact ⟨_, hA, by group⟩
  obtain ⟨u, hu, hAu⟩ := hσ (hA ▸ a.2 : fieldAut n F σ (proj n F A) = proj n F A)
  obtain ⟨v, hv, hBv⟩ := hσ (hB ▸ b.2 : fieldAut n F σ (proj n F B) = proj n F B)
  have hfix :
      Matrix.SpecialLinearGroup.map σ.toRingHom (A * B * A⁻¹ * B⁻¹) = A * B * A⁻¹ * B⁻¹ := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hAu, hBv]
    exact commutator_mul_central hu hv
  obtain ⟨M₀, hM₀⟩ := exists_slMap_subtype_eq hfix
  refine ⟨M₀, Subtype.ext ?_⟩
  change proj n F (Matrix.SpecialLinearGroup.map (fixedField σ).subtype M₀) =
    ((a * b * a⁻¹ * b⁻¹ : Item426.fixSub (fieldAut n F σ)) : projectiveSL n F)
  rw [hM₀, map_mul, map_mul, map_mul, map_inv, map_inv, hA, hB]
  rfl

theorem hasType424_fieldAut_imp [Finite F] (hn : 3 ≤ n) (σ : F ≃+* F)
    (h : Sec11.KS11Lie2Proof.HasType424 (Item426.fixSub (fieldAut n F σ))) :
    n = 3 ∧ ∃ m : ℕ, Nat.card (fixedField σ) = 2 ^ m ∧ Odd m :=
  exists_two_pow_of_hasType424_of_hom hn (projFixHom σ) (projFixHom_ker_le σ)
    (commutator_mem_range_projFixHom σ) h

@[expose] noncomputable def slFixHom (σ : F ≃+* F) :
    Matrix.SpecialLinearGroup (Fin n) (fixedField σ) →*
      Item426.fixSub (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut
        (Fin n) F σ) :=
  (Matrix.SpecialLinearGroup.map (fixedField σ).subtype).codRestrict _ fun A₀ =>
    slMap_map_subtype σ A₀

theorem slFixHom_surjective (σ : F ≃+* F) : Function.Surjective (slFixHom (n := n) σ) := by
  rintro ⟨A, hA⟩
  obtain ⟨A₀, hA₀⟩ := exists_slMap_subtype_eq (σ := σ) (A := A) hA
  exact ⟨A₀, Subtype.ext hA₀⟩

theorem hasType424_slFieldAut_imp [Finite F] (hn : 3 ≤ n) (σ : F ≃+* F)
    (h : Sec11.KS11Lie2Proof.HasType424 (Item426.fixSub
      (CFSG.ComponentClassification.CatalogueBHigherLinearField.slFieldAut (Fin n) F σ))) :
    n = 3 ∧ ∃ m : ℕ, Nat.card (fixedField σ) = 2 ^ m ∧ Odd m := by
  refine exists_two_pow_of_hasType424_of_hom hn (slFixHom σ) ?_
    (fun a b => (slFixHom_surjective σ) _) h
  intro A₀ hA₀
  have h1 : slFixHom (n := n) σ A₀ = slFixHom σ 1 := by rw [hA₀, map_one]
  rw [slMap_subtype_injective σ (congrArg Subtype.val h1)]
  exact Subgroup.one_mem _

end Models

end CFSG.RankThree.PartTwo.Sec4.Item424Res3
