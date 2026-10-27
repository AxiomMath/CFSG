module

public import CFSG.Open.StatedDefs
public import CFSG.Assembly.Defs
public import CFSG.Assembly.Subnormal
public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmBlock
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatParMax.ProdComponents

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.Open (StatedOmega StatedClassicalModel)

variable {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [CharP K 2]

omit [Finite K] [CharP K 2] in
private theorem isComponentOf_map_toLin_statedOmega_four (Φ : QuadraticForm K (ι → K))
    {C : Subgroup (GL ι K)}
    (hC : CFSG.Assembly.IsComponentOf C (StatedOmega ⇑Φ)) :
    CFSG.Assembly.IsComponentOf
      (C.map (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom)
      ⁅TauCeti.QuadraticMap.orthogonalGroup Φ,
        TauCeti.QuadraticMap.orthogonalGroup Φ⁆ := by
  classical
  let f := (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom
  have hmap : (StatedOmega ⇑Φ).map f =
      ⁅TauCeti.QuadraticMap.orthogonalGroup Φ,
        TauCeti.QuadraticMap.orthogonalGroup Φ⁆ := by
    rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap (Q := Φ) (Q₀ := ⇑Φ) rfl]
    exact Subgroup.map_comap_eq_self_of_surjective
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).surjective _
  have := isComponentOf_map_of_injective f
    (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).injective hC
  rwa [hmap] at this

private theorem not_card_two_of_isComponentOf_statedOmega_four
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h4 : Fintype.card ι = 4)
    (hplus : ∃ T : Submodule K (ι → K), Module.finrank K T = 2 ∧ ∀ x ∈ T, Φ x = 0)
    {C : Subgroup (GL ι K)} (hC : CFSG.Assembly.IsComponentOf C (StatedOmega ⇑Φ)) :
    Nat.card K ≠ 2 := by
  classical
  intro hK2
  let O : Subgroup ((ι → K) ≃ₗ[K] (ι → K)) := TauCeti.QuadraticMap.orthogonalGroup Φ
  have hC' := isComponentOf_map_toLin_statedOmega_four Φ hC
  have hcommle : ⁅O, O⁆ ≤ O := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
      (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
  let O' : Subgroup ↥O := ⁅(⊤ : Subgroup ↥O), (⊤ : Subgroup ↥O)⁆
  have hmapO' : O'.map O.subtype = ⁅O, O⁆ := by
    rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have hO'norm : (⁅O, O⁆.subgroupOf O).Normal := by
    have hsubeq : (⁅O, O⁆.subgroupOf O) = O' := by
      rw [← hmapO']
      change Subgroup.comap O.subtype (Subgroup.map O.subtype O') = O'
      exact Subgroup.comap_map_eq_self_of_injective O.subtype_injective O'
    rw [hsubeq]
    exact Subgroup.commutator_normal _ _
  have hO'O : CFSG.Assembly.IsSubnormal ⁅O, O⁆ O :=
    CFSG.Assembly.IsSubnormal.step hcommle hO'norm (CFSG.Assembly.IsSubnormal.refl O)
  have hTs : CFSG.Assembly.IsSubnormal (C.map
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom) O :=
    hC'.2.1.trans hO'O
  have hTq : CFSG.IsQuasisimple (C.map
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp hC'.2.2
  have hsp : CFSG.StandardType.OmNonsplit.SplitFour Φ :=
    ⟨by rw [Module.finrank_fintype_fun_eq_card, h4], hplus⟩
  obtain ⟨-, hcase⟩ := CFSG.StandardType.OmNonsplit.structure_of_isSubnormal hΦ hTq hTs
  rcases hcase with ⟨hns, -⟩ | ⟨-, hK4, -⟩
  · exact hns hsp
  · omega

private theorem four_le_card_of_isComponentOf_statedOmega_four
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h4 : Fintype.card ι = 4)
    (hplus : ∃ T : Submodule K (ι → K), Module.finrank K T = 2 ∧ ∀ x ∈ T, Φ x = 0)
    {C : Subgroup (GL ι K)} (hC : CFSG.Assembly.IsComponentOf C (StatedOmega ⇑Φ)) :
    4 ≤ Nat.card K := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have hK2 := not_card_two_of_isComponentOf_statedOmega_four Φ hΦ h4 hplus hC
  have heven := FiniteField.even_card_of_char_two (F := K) (ringChar.eq K 2)
  have hge2 : 2 ≤ Nat.card K := by
    have := Finite.one_lt_card (α := K)
    omega
  have hevenNat : Even (Nat.card K) := by
    rw [Nat.even_iff, Nat.card_eq_fintype_card]
    exact heven
  rcases hevenNat with ⟨m, hm⟩
  omega

omit [Finite K] [CharP K 2] in
private theorem normalizes_and_commutes_of_split_factors
    {Φ : QuadraticForm K (ι → K)}
    {T₁ T₂ : Subgroup ((ι → K) ≃ₗ[K] (ι → K))}
    {D₁ D₂ : Subgroup (GL ι K)}
    (hmapΩ : (StatedOmega ⇑Φ).map
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom =
      ⁅TauCeti.QuadraticMap.orthogonalGroup Φ,
        TauCeti.QuadraticMap.orthogonalGroup Φ⁆)
    (hD₁ : D₁ = Subgroup.comap
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom T₁)
    (hD₂ : D₂ = Subgroup.comap
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom T₂)
    (hn₁ : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Φ,
        TauCeti.QuadraticMap.orthogonalGroup Φ⁆, ∀ t ∈ T₁, g * t * g⁻¹ ∈ T₁)
    (hn₂ : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Φ,
        TauCeti.QuadraticMap.orthogonalGroup Φ⁆, ∀ t ∈ T₂, g * t * g⁻¹ ∈ T₂)
    (hcomm : ∀ x ∈ T₁, ∀ y ∈ T₂, x * y = y * x) :
    (∀ g ∈ StatedOmega ⇑Φ, ∀ t ∈ D₁, g * t * g⁻¹ ∈ D₁) ∧
    (∀ g ∈ StatedOmega ⇑Φ, ∀ t ∈ D₂, g * t * g⁻¹ ∈ D₂) ∧
    (∀ x ∈ D₁, ∀ y ∈ D₂, x * y = y * x) := by
  classical
  have hfg : ∀ g ∈ StatedOmega ⇑Φ,
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K) g ∈
        ⁅TauCeti.QuadraticMap.orthogonalGroup Φ,
          TauCeti.QuadraticMap.orthogonalGroup Φ⁆ := by
    intro g hg
    rw [← hmapΩ]
    exact Subgroup.mem_map_of_mem _ hg
  have hnormD₁ : ∀ g ∈ StatedOmega ⇑Φ, ∀ t ∈ D₁, g * t * g⁻¹ ∈ D₁ := by
    intro g hg t ht
    rw [hD₁, Subgroup.mem_comap] at ht ⊢
    simpa using hn₁ _ (hfg g hg) _ ht
  have hnormD₂ : ∀ g ∈ StatedOmega ⇑Φ, ∀ t ∈ D₂, g * t * g⁻¹ ∈ D₂ := by
    intro g hg t ht
    rw [hD₂, Subgroup.mem_comap] at ht ⊢
    simpa using hn₂ _ (hfg g hg) _ ht
  have hcommD : ∀ x ∈ D₁, ∀ y ∈ D₂, x * y = y * x := by
    intro x hx y hy
    rw [hD₁, Subgroup.mem_comap] at hx
    rw [hD₂, Subgroup.mem_comap] at hy
    change (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K) x ∈ T₁ at hx
    change (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K) y ∈ T₂ at hy
    apply (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).injective
    simpa only [map_mul] using hcomm _ hx _ hy
  exact ⟨hnormD₁, hnormD₂, hcommD⟩

omit [Finite K] [CharP K 2] in
private theorem isComponentOf_of_split_factors
    {Φ : QuadraticForm K (ι → K)}
    {T₁ T₂ : Subgroup ((ι → K) ≃ₗ[K] (ι → K))}
    {D₁ D₂ : Subgroup (GL ι K)}
    (hsup : D₁ ⊔ D₂ = StatedOmega ⇑Φ)
    (hmapΩ : (StatedOmega ⇑Φ).map
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom =
      ⁅TauCeti.QuadraticMap.orthogonalGroup Φ,
        TauCeti.QuadraticMap.orthogonalGroup Φ⁆)
    (hD₁ : D₁ = Subgroup.comap
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom T₁)
    (hD₂ : D₂ = Subgroup.comap
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom T₂)
    (hc₁ : CFSG.Assembly.IsComponentOf T₁
      (TauCeti.QuadraticMap.orthogonalGroup Φ))
    (hc₂ : CFSG.Assembly.IsComponentOf T₂
      (TauCeti.QuadraticMap.orthogonalGroup Φ)) :
    CFSG.Assembly.IsComponentOf D₁ (StatedOmega ⇑Φ) ∧
      CFSG.Assembly.IsComponentOf D₂ (StatedOmega ⇑Φ) := by
  classical
  have hcommle : ⁅TauCeti.QuadraticMap.orthogonalGroup Φ,
      TauCeti.QuadraticMap.orthogonalGroup Φ⁆ ≤
      TauCeti.QuadraticMap.orthogonalGroup Φ := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hx hy)
      (Subgroup.inv_mem _ hx)) (Subgroup.inv_mem _ hy)
  have hmapD₁ : D₁.map
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom = T₁ := by
    rw [hD₁]
    exact Subgroup.map_comap_eq_self_of_surjective
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).surjective T₁
  have hmapD₂ : D₂.map
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom = T₂ := by
    rw [hD₂]
    exact Subgroup.map_comap_eq_self_of_surjective
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).surjective T₂
  have hle₁ : T₁ ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Φ,
      TauCeti.QuadraticMap.orthogonalGroup Φ⁆ := by
    rw [← hmapD₁, ← hmapΩ]
    exact Subgroup.map_mono (by rw [← hsup]; exact le_sup_left)
  have hle₂ : T₂ ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Φ,
      TauCeti.QuadraticMap.orthogonalGroup Φ⁆ := by
    rw [← hmapD₂, ← hmapΩ]
    exact Subgroup.map_mono (by rw [← hsup]; exact le_sup_right)
  refine ⟨?_, ?_⟩
  · have h := hc₁.of_le_of_le hle₁ hcommle
    have h' : CFSG.Assembly.IsComponentOf T₁ ((StatedOmega ⇑Φ).map
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom) := by
      rwa [hmapΩ]
    rw [hD₁]
    exact (isComponentOf_comap_of_injective _
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).injective h').1
  · have h := hc₂.of_le_of_le hle₂ hcommle
    have h' : CFSG.Assembly.IsComponentOf T₂ ((StatedOmega ⇑Φ).map
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom) := by
      rwa [hmapΩ]
    rw [hD₂]
    exact (isComponentOf_comap_of_injective _
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).injective h').1

omit [Finite K] [CharP K 2] in
private theorem nonempty_iso_of_split_factors
    {T₁ T₂ : Subgroup ((ι → K) ≃ₗ[K] (ι → K))}
    {D₁ D₂ : Subgroup (GL ι K)}
    {ψ₁ ψ₂ : Matrix.SpecialLinearGroup (Fin 2) K →*
      ((ι → K) ≃ₗ[K] (ι → K))}
    (hD₁ : D₁ = Subgroup.comap
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom T₁)
    (hD₂ : D₂ = Subgroup.comap
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom T₂)
    (hψ₁ : Function.Injective ψ₁) (hψ₂ : Function.Injective ψ₂)
    (hr₁ : ψ₁.range = T₁) (hr₂ : ψ₂.range = T₂) :
    Nonempty (↥D₁ ≃* Matrix.SpecialLinearGroup (Fin 2) K) ∧
      Nonempty (↥D₂ ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  have hmapD₁ : D₁.map
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom = T₁ := by
    rw [hD₁]
    exact Subgroup.map_comap_eq_self_of_surjective
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).surjective T₁
  have hmapD₂ : D₂.map
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom = T₂ := by
    rw [hD₂]
    exact Subgroup.map_comap_eq_self_of_surjective
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).surjective T₂
  constructor
  · exact ⟨(Subgroup.equivMapOfInjective D₁ _
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).injective).trans
      ((MulEquiv.subgroupCongr hmapD₁).trans
        ((MulEquiv.subgroupCongr hr₁).symm.trans (MonoidHom.ofInjective hψ₁).symm))⟩
  · exact ⟨(Subgroup.equivMapOfInjective D₂ _
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).injective).trans
      ((MulEquiv.subgroupCongr hmapD₂).trans
        ((MulEquiv.subgroupCongr hr₂).symm.trans (MonoidHom.ofInjective hψ₂).symm))⟩

private theorem exists_split_of_statedOmega_four
    (Φ : QuadraticForm K (ι → K)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h4 : Fintype.card ι = 4)
    (hplus : ∃ T : Submodule K (ι → K), Module.finrank K T = 2 ∧ ∀ x ∈ T, Φ x = 0)
    (hK2 : Nat.card K ≠ 2) :
    ∃ D₁ D₂ : Subgroup (GL ι K),
      D₁ ⊔ D₂ = StatedOmega ⇑Φ ∧
      (∀ g ∈ StatedOmega ⇑Φ, ∀ t ∈ D₁, g * t * g⁻¹ ∈ D₁) ∧
      (∀ g ∈ StatedOmega ⇑Φ, ∀ t ∈ D₂, g * t * g⁻¹ ∈ D₂) ∧
      (∀ x ∈ D₁, ∀ y ∈ D₂, x * y = y * x) ∧
      CFSG.Assembly.IsComponentOf D₁ (StatedOmega ⇑Φ) ∧
      CFSG.Assembly.IsComponentOf D₂ (StatedOmega ⇑Φ) ∧
      Nonempty (↥D₁ ≃* Matrix.SpecialLinearGroup (Fin 2) K) ∧
      Nonempty (↥D₂ ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have hsp : CFSG.StandardType.OmNonsplit.SplitFour Φ :=
    ⟨by rw [Module.finrank_fintype_fun_eq_card, h4], hplus⟩
  have hK3 : Nat.card K ≠ 3 := by
    intro h3
    have heven := FiniteField.even_card_of_char_two (F := K) (ringChar.eq K 2)
    rw [← Nat.card_eq_fintype_card, h3] at heven
    norm_num at heven
  let O : Subgroup ((ι → K) ≃ₗ[K] (ι → K)) := TauCeti.QuadraticMap.orthogonalGroup Φ
  let f := (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).toMonoidHom
  obtain ⟨T₁, T₂, hsupLin, hnLin₁, hnLin₂, hcommLin, hcLin₁, hcLin₂,
    ⟨ψ₁, hψ₁, hr₁⟩, ⟨ψ₂, hψ₂, hr₂⟩, -⟩ :=
    CFSG.StandardType.SevOm.splitFour_factors hΦ hsp hK2 hK3
  have hmapΩ : (StatedOmega ⇑Φ).map f = ⁅O, O⁆ := by
    rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap (Q := Φ) (Q₀ := ⇑Φ) rfl]
    exact Subgroup.map_comap_eq_self_of_surjective
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).surjective _
  let D₁ : Subgroup (GL ι K) := T₁.comap f
  let D₂ : Subgroup (GL ι K) := T₂.comap f
  have hDsup : D₁ ⊔ D₂ = StatedOmega ⇑Φ := by
    calc D₁ ⊔ D₂ = Subgroup.comap f T₁ ⊔ Subgroup.comap f T₂ := rfl
      _ = Subgroup.comap f (T₁ ⊔ T₂) :=
        Subgroup.comap_sup_eq f T₁ T₂
          (CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι K).surjective
      _ = Subgroup.comap f ⁅O, O⁆ := by rw [hsupLin]
      _ = StatedOmega ⇑Φ :=
        (CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap (Q := Φ) (Q₀ := ⇑Φ) rfl).symm
  obtain ⟨hnD₁, hnD₂, hcommD⟩ :=
    normalizes_and_commutes_of_split_factors hmapΩ rfl rfl hnLin₁ hnLin₂ hcommLin
  obtain ⟨hcompD₁, hcompD₂⟩ :=
    isComponentOf_of_split_factors hDsup hmapΩ rfl rfl hcLin₁ hcLin₂
  obtain ⟨hiso₁, hiso₂⟩ :=
    nonempty_iso_of_split_factors rfl rfl hψ₁ hψ₂ hr₁ hr₂
  exact ⟨D₁, D₂, hDsup, hnD₁, hnD₂, hcommD, hcompD₁, hcompD₂, hiso₁, hiso₂⟩

omit [Finite K] [CharP K 2] in
private theorem nonempty_centerQuotient_equiv_statedProj_of_mulEquiv
    {C : Subgroup (GL ι K)}
    (eC : ↥C ≃* Matrix.SpecialLinearGroup (Fin 2) K) :
    Nonempty (↥C ⧸ Subgroup.center ↥C ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSL 2 K)) :=
  ⟨(QuotientGroup.congr (Subgroup.center ↥C)
      (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) eC
      (Subgroup.map_center_eq eC)).trans
    (QuotientGroup.congr (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))
      ((CFSG.Open.StatedScalars (Fin 2) K).subgroupOf (CFSG.Open.StatedSL 2 K))
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K)
      (CFSG.Assembly.LowTwoRank.map_center_eq_statedScalars 2 K))⟩

private theorem exists_admissible_card_pow_two (hK4 : 4 ≤ Nat.card K) :
    ∃ n : ℕ, CFSG.Open.StatedLieAdmissible .PSL 2 2 n ∧ Nat.card K = 2 ^ n := by
  classical
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hcard⟩ := FiniteField.card K 2
  have hcardNat : Nat.card K = 2 ^ (n : ℕ) := by
    rwa [Nat.card_eq_fintype_card]
  have hn2 : 2 ≤ (n : ℕ) := by
    by_contra h
    have hle : (n : ℕ) ≤ 1 := by omega
    have hpow : 2 ^ (n : ℕ) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hle
    have hpow' : 2 ^ (n : ℕ) ≤ 2 := by simpa using hpow
    omega
  have hge4 : 4 ≤ 2 ^ (n : ℕ) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n : ℕ) := Nat.pow_le_pow_right (by norm_num) hn2
  have hadm : CFSG.Open.StatedLieAdmissible .PSL 2 2 (n : ℕ) := by
    refine ⟨Nat.prime_two, n.pos, by norm_num, ?_, ?_⟩
    · intro h
      have := congrArg Prod.snd h
      omega
    · intro h
      have := congrArg Prod.snd h
      omega
  exact ⟨(n : ℕ), hadm, hcardNat⟩

omit [CharP K 2] in
private theorem eq_left_or_right_of_isComponentOf_statedOmega_four
    {Φ : QuadraticForm K (ι → K)} {D₁ D₂ : Subgroup (GL ι K)}
    (hsup : D₁ ⊔ D₂ = StatedOmega ⇑Φ)
    (h₁ : CFSG.Assembly.IsComponentOf D₁ (StatedOmega ⇑Φ))
    (h₂ : CFSG.Assembly.IsComponentOf D₂ (StatedOmega ⇑Φ))
    {C : Subgroup (GL ι K)} (hC : CFSG.Assembly.IsComponentOf C (StatedOmega ⇑Φ)) :
    C = D₁ ∨ C = D₂ := by
  rw [CFSG.Assembly.isComponentOf_iff_open] at h₁ h₂ hC
  exact CFSG.LocalAnalysis.UniquenessCase.UC22.NatParMax.eq_factor_of_isComponentOf
    hsup h₁ h₂ hC

theorem statedClassicalModel_of_isComponentOf_statedOmega_four (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h4 : Fintype.card ι = 4)
    (hplus : ∃ T : Submodule K (ι → K), Module.finrank K T = 2 ∧ ∀ x ∈ T, Φ x = 0)
    {C : Subgroup (GL ι K)} (hC : IsComponentOf C (StatedOmega ⇑Φ)) :
    ∃ f : ℕ, StatedClassicalModel (↥C ⧸ Subgroup.center ↥C) .PSL 2 2 f := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have hK4 := four_le_card_of_isComponentOf_statedOmega_four Φ hΦ h4 hplus hC
  have hK2 : Nat.card K ≠ 2 := by omega
  obtain ⟨D₁, D₂, hsup, -, -, -, hcomp₁, hcomp₂, ⟨e₁⟩, ⟨e₂⟩⟩ :=
    exists_split_of_statedOmega_four Φ hΦ h4 hplus hK2
  obtain ⟨n, hadm, hcard⟩ := exists_admissible_card_pow_two hK4
  rcases eq_left_or_right_of_isComponentOf_statedOmega_four hsup hcomp₁ hcomp₂ hC with
    hCeq | hCeq
  · exact ⟨n, hadm, K, inferInstance, inferInstance, hcard,
      nonempty_centerQuotient_equiv_statedProj_of_mulEquiv
        ((MulEquiv.subgroupCongr hCeq).trans e₁)⟩
  · exact ⟨n, hadm, K, inferInstance, inferInstance, hcard,
      nonempty_centerQuotient_equiv_statedProj_of_mulEquiv
        ((MulEquiv.subgroupCongr hCeq).trans e₂)⟩

omit [Finite K] [CharP K 2] in
private theorem exists_mul_eq_of_mem_split_statedOmega_four
    {Φ : QuadraticForm K (ι → K)} {D₁ D₂ : Subgroup (GL ι K)}
    (hsup : D₁ ⊔ D₂ = StatedOmega ⇑Φ)
    (hn₁ : ∀ g ∈ StatedOmega ⇑Φ, ∀ t ∈ D₁, g * t * g⁻¹ ∈ D₁)
    {g : GL ι K} (hg : g ∈ StatedOmega ⇑Φ) :
    ∃ c ∈ D₁, ∃ d ∈ D₂, g = c * d := by
  classical
  have hD₁S : D₁ ≤ StatedOmega ⇑Φ := by
    rw [← hsup]; exact le_sup_left
  have hN₁ : (D₁.subgroupOf (StatedOmega ⇑Φ)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hD₁S]
    intro h k hh hk
    exact hn₁ k hk h hh
  have hsupSub : D₁.subgroupOf (StatedOmega ⇑Φ) ⊔
      D₂.subgroupOf (StatedOmega ⇑Φ) = ⊤ := by
    have h := Subgroup.subgroupOf_sup (A := D₁) (A' := D₂) (B := StatedOmega ⇑Φ)
      hD₁S (by rw [← hsup]; exact le_sup_right)
    rw [hsup, Subgroup.subgroupOf_self] at h
    exact h.symm
  have : (D₁.subgroupOf (StatedOmega ⇑Φ)).Normal := hN₁
  have hgS : (⟨g, hg⟩ : ↥(StatedOmega ⇑Φ)) ∈
      D₁.subgroupOf (StatedOmega ⇑Φ) ⊔ D₂.subgroupOf (StatedOmega ⇑Φ) := by
    rw [hsupSub]
    exact Subgroup.mem_top _
  obtain ⟨cS, hcS, dS, hdS, hcd⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := D₁.subgroupOf (StatedOmega ⇑Φ))
      (t := D₂.subgroupOf (StatedOmega ⇑Φ))).1 hgS
  have hc : (cS : GL ι K) ∈ D₁ := Subgroup.mem_subgroupOf.mp hcS
  have hd : (dS : GL ι K) ∈ D₂ := Subgroup.mem_subgroupOf.mp hdS
  have hgd : g = (cS : GL ι K) * (dS : GL ι K) := by
    have := congrArg Subtype.val hcd
    simpa using this.symm
  exact ⟨(cS : GL ι K), hc, (dS : GL ι K), hd, hgd⟩

omit [Finite K] [CharP K 2] in
private theorem exists_conj_eq_of_split_statedOmega_four
    {Φ : QuadraticForm K (ι → K)} {D₁ D₂ : Subgroup (GL ι K)}
    (hsup : D₁ ⊔ D₂ = StatedOmega ⇑Φ)
    (hn₁ : ∀ g ∈ StatedOmega ⇑Φ, ∀ t ∈ D₁, g * t * g⁻¹ ∈ D₁)
    (hcomm : ∀ x ∈ D₁, ∀ y ∈ D₂, x * y = y * x)
    {g : GL ι K} (hg : g ∈ StatedOmega ⇑Φ) :
    ∃ c ∈ D₁, ∀ l ∈ D₁, g⁻¹ * l * g = c⁻¹ * l * c := by
  classical
  obtain ⟨c, hc, d, hd, hgd⟩ :=
    exists_mul_eq_of_mem_split_statedOmega_four hsup hn₁ hg
  have hd_cent : d ∈ Subgroup.centralizer (D₁ : Set (GL ι K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hcomm x hx d hd
  refine ⟨c, hc, fun l hl => ?_⟩
  have hdl : c⁻¹ * l * c ∈ D₁ :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hl) hc
  have hcomm1 : d * (c⁻¹ * l * c) = (c⁻¹ * l * c) * d := by
    rw [Subgroup.mem_centralizer_iff] at hd_cent
    exact (hd_cent _ hdl).symm
  calc g⁻¹ * l * g
      = d⁻¹ * (c⁻¹ * l * c) * d := by rw [hgd]; group
    _ = c⁻¹ * l * c := by rw [mul_assoc, ← hcomm1, inv_mul_cancel_left]

theorem exists_mem_conj_eq_of_isComponentOf_statedOmega_four (Φ : QuadraticForm K (ι → K))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate) (h4 : Fintype.card ι = 4)
    (hplus : ∃ T : Submodule K (ι → K), Module.finrank K T = 2 ∧ ∀ x ∈ T, Φ x = 0)
    {C : Subgroup (GL ι K)} (hC : IsComponentOf C (StatedOmega ⇑Φ)) :
    ∀ g ∈ StatedOmega ⇑Φ, ∃ c ∈ C, ∀ l ∈ C, g⁻¹ * l * g = c⁻¹ * l * c := by
  classical
  let : Fintype K := Fintype.ofFinite K
  intro g hg
  have hK4 := four_le_card_of_isComponentOf_statedOmega_four Φ hΦ h4 hplus hC
  have hK2 : Nat.card K ≠ 2 := by omega
  obtain ⟨D₁, D₂, hsup, hn₁, hn₂, hcomm, hcomp₁, hcomp₂, -, -⟩ :=
    exists_split_of_statedOmega_four Φ hΦ h4 hplus hK2
  rcases eq_left_or_right_of_isComponentOf_statedOmega_four hsup hcomp₁ hcomp₂ hC with
    hCeq | hCeq
  · rw [hCeq] at ⊢
    exact exists_conj_eq_of_split_statedOmega_four hsup hn₁ hcomm hg
  · rw [hCeq] at ⊢
    exact exists_conj_eq_of_split_statedOmega_four (D₁ := D₂) (D₂ := D₁)
      (by rw [sup_comm]; exact hsup) hn₂
      (fun x hx y hy => (hcomm y hy x hx).symm) hg

end CFSG.StandardType
