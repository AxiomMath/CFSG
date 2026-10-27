module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_7_11
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_9
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection7.PFsection7_6

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section7

universe v
universe u

@[expose] public def theorem_7_8_a_statement
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L H : Subgroup G)
    (K : G → Subgroup G)
    (T : Finset (Section1.ClassFunction L))
    (S : Finset (Section1.ClassFunction L))
    (τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ζ : Section1.ClassFunction L) : Prop :=
  hypothesis_7_6_statement A L H K T →
    agreesWithDadeTransform A L K τ →
    theorem_7_8_hypothesis L H T S τ ν ζ →
    ∃ a : ℤ, ∃ r : Section1.ClassFunction G,
      theorem_7_8_decompositionData L H S τ ν ζ (H.relIndex L) a r

/-- Peterfalvi `(7.8)(b)`. -/


private theorem scalarProduct_add_right_pf78
    {G : Type*} [Finite G]
    (φ ψ₁ ψ₂ : Section1.ClassFunction G) :
    Section1.scalarProduct G φ (ψ₁ + ψ₂) =
      Section1.scalarProduct G φ ψ₁ + Section1.scalarProduct G φ ψ₂ := by
  simp [Section1.scalarProduct, mul_add, Finset.sum_add_distrib]

private theorem scalarProduct_sub_left_pf78
    {G : Type*} [Finite G]
    (φ₁ φ₂ ψ : Section1.ClassFunction G) :
    Section1.scalarProduct G (φ₁ - φ₂) ψ =
      Section1.scalarProduct G φ₁ ψ - Section1.scalarProduct G φ₂ ψ := by
  rw [sub_eq_add_neg, Section1.scalarProduct_add_left]
  rw [show -φ₂ = (-1 : ℂ) • φ₂ by ext g; simp]
  rw [Section1.scalarProduct_smul_left]
  ring

private theorem scalarProduct_sub_right_pf78
    {G : Type*} [Finite G]
    (φ ψ₁ ψ₂ : Section1.ClassFunction G) :
    Section1.scalarProduct G φ (ψ₁ - ψ₂) =
      Section1.scalarProduct G φ ψ₁ - Section1.scalarProduct G φ ψ₂ := by
  rw [sub_eq_add_neg, scalarProduct_add_right_pf78]
  rw [show -ψ₂ = (-1 : ℂ) • ψ₂ by ext g; simp]
  rw [Section1.scalarProduct_smul_right]
  simp [sub_eq_add_neg]

private noncomputable def uliftRepresentation_pf78
    {G : Type u} [Group G] {V : Type}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    Representation ℂ G (ULift.{u} V) := by
  let e : V ≃ₗ[ℂ] ULift.{u} V := ULift.moduleEquiv.symm
  refine
    { toFun := fun g => e.conj (ρ g)
      map_one' := by
        ext x
        simp [LinearEquiv.conj_apply]
      map_mul' := by
        intro g h
        ext x
        simp [LinearEquiv.conj_apply, map_mul] }

private theorem uliftRepresentation_pf78_character
    {G : Type u} [Group G] {V : Type}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    (uliftRepresentation_pf78 (G := G) (V := V) ρ).character g = ρ.character g := by
  dsimp [uliftRepresentation_pf78, Representation.character]
  exact LinearMap.trace_conj' (R := ℂ) (M := V)
    (N := ULift.{u} V) (ρ g) (ULift.moduleEquiv.symm)

private theorem isCharacter_of_isIrreducibleCharacterOnGroup_pf78
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsCharacter χ := by
  rcases hχ with ⟨n, ρ, _hirr, hchar⟩
  refine ⟨ULift.{u} (Fin n → ℂ), inferInstance, inferInstance, inferInstance,
    uliftRepresentation_pf78 (G := G) (V := Fin n → ℂ) ρ, ?_⟩
  ext g
  simpa [hchar] using
    (uliftRepresentation_pf78_character (G := G) (V := Fin n → ℂ) (ρ := ρ) g).symm

public theorem theorem_7_8_nu_scalarProduct_of_mem
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ φ ψ : Section1.ClassFunction L}
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ)
    (hφ : φ ∈ S) (hψ : ψ ∈ S) :
    Section1.scalarProduct G (ν φ) (ν ψ) =
      Section1.scalarProduct L φ ψ := by
  rcases h78 with ⟨_hHL, _hST, _hpunctured, _hcoherent, hν, _hζS, _hζ, _hdeg⟩
  exact Section5.isCFLinearIsometryOnSpan_apply_of_mem hν.1 hφ hψ

public theorem theorem_7_8_nu_zeta_norm
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L}
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ) :
    Section1.scalarProduct G (ν ζ) (ν ζ) = 1 := by
  rcases h78 with ⟨_hHL, _hST, _hpunctured, _hcoherent, hν, hζS, hζ, _hdeg⟩
  have hνζ :
      Section1.scalarProduct G (ν ζ) (ν ζ) =
        Section1.scalarProduct L ζ ζ :=
    Section5.isCFLinearIsometryOnSpan_apply_of_mem hν.1 hζS hζS
  have hζself : Section1.scalarProduct L ζ ζ = 1 := by
    rcases hζ with ⟨n, ρ, hρ, rfl⟩
    exact Section1.scalarProduct_representation_char_self ρ hρ
  exact hνζ.trans hζself

private theorem theorem_7_8_zeta_scalarProduct_self
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L}
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ) :
    Section1.scalarProduct L ζ ζ = 1 := by
  rcases h78 with ⟨_hHL, _hST, _hpunctured, _hcoherent, _hν, _hζS, hζ, _hdeg⟩
  rcases hζ with ⟨n, ρ, hρ, rfl⟩
  exact Section1.scalarProduct_representation_char_self ρ hρ

public theorem theorem_7_8_exists_distinct_member
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L}
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ) :
    ∃ φ : Section1.ClassFunction L, φ ∈ S ∧ φ ≠ ζ := by
  classical
  by_contra hnone
  rcases h78 with ⟨_hHL, _hST, _hpunctured, hcoherent, _hν, hζS, _hζ, hdegζ⟩
  rcases hcoherent with ⟨_hsource, hnonempty, _hExtension⟩
  rcases hnonempty with ⟨χ, ⟨hχspan, hχsupport⟩, hχne⟩
  rcases hχspan with ⟨v, hχeq⟩
  let c : ℂ := ∑ X : S, (v X : ℂ)
  have hall : ∀ X : S, (X : Section1.ClassFunction L) = ζ := by
    intro X
    by_contra hXne
    exact hnone ⟨X, X.2, hXne⟩
  have hEval :
      Section1.evalCoeff (fun X : S => (X : Section1.ClassFunction L)) v =
        c • ζ := by
    ext x
    simp [Section1.evalCoeff, c, hall, Finset.sum_mul]
  have hχ_one : χ 1 = 0 := by
    exact (Section1.supportedOn_iff.mp hχsupport) 1 (by simp [Section5.puncturedSet])
  have hζ_one_ne : ζ 1 ≠ 0 := by
    haveI : (H.subgroupOf L).FiniteIndex := inferInstance
    have hrel : H.relIndex L ≠ 0 := by
      simpa [Subgroup.relIndex] using
        (Subgroup.FiniteIndex.index_ne_zero (H := H.subgroupOf L))
    have hζ_one : ζ 1 = (H.relIndex L : ℂ) := by
      simpa [Section1.degree_apply] using hdegζ
    rw [hζ_one]
    exact_mod_cast hrel
  have hc_mul : c * ζ 1 = 0 := by
    calc
      c * ζ 1 = (c • ζ) 1 := by simp [smul_eq_mul]
      _ = Section1.evalCoeff (fun X : S => (X : Section1.ClassFunction L)) v 1 := by
        rw [hEval]
      _ = χ 1 := by rw [hχeq]
      _ = 0 := hχ_one
  have hc : c = 0 := (mul_eq_zero.mp hc_mul).resolve_right hζ_one_ne
  apply hχne
  rw [hχeq, hEval, hc]
  ext x
  simp

public theorem theorem_7_8_degree_zero_combo_mem_integerSpanOn
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ φ : Section1.ClassFunction L}
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ)
    (hφ : φ ∈ S) :
    ∃ m : ℕ,
      m ≠ 0 ∧
      Section1.degree φ = (H.relIndex L : ℂ) * (m : ℂ) ∧
        Section5.integerSpanOn S Section5.puncturedSet (φ - (m : ℂ) • ζ) := by
  classical
  rcases h78 with ⟨_hHL, _hST, hpunctured, _hcoherent, _hν, hζS, _hζ, hdegζ⟩
  rcases (hpunctured φ).mp hφ with ⟨θ, hθ, _hθne, hφeq⟩
  rcases hθ with ⟨m, ρ, hρ, hθeq⟩
  have hm_ne : m ≠ 0 := by
    letI : Representation.IsIrreducible ρ := hρ
    have hnon : Nontrivial (Fin m → ℂ) :=
      Subrepresentation.irreducible_module_nontrivial ρ
    intro hm
    subst hm
    have hsub : Subsingleton (Fin 0 → ℂ) := inferInstance
    exact (not_subsingleton (Fin 0 → ℂ)) hsub
  have hdegθ : Section1.degree θ = (m : ℂ) := by
    rw [hθeq]
    simp [Section1.degree, Representation.character]
  have hdegφ : Section1.degree φ = (H.relIndex L : ℂ) * (m : ℂ) := by
    rw [hφeq, Section1.degree_inducedClassFunction, hdegθ]
    rfl
  refine ⟨m, hm_ne, hdegφ, ?_⟩
  constructor
  · exact Section5.integerSpan_sub (Section5.integerSpan_of_mem S hφ)
      (Section5.integerSpan_zsmul (S := S) (φ := ζ) (m : ℤ)
        (Section5.integerSpan_of_mem S hζS))
  · apply (Section5.supportedOn_puncturedSet_iff_degree_eq_zero
      (φ - (m : ℂ) • ζ)).2
    have hφ_one : φ 1 = (H.relIndex L : ℂ) * (m : ℂ) := by
      simpa [Section1.degree_apply] using hdegφ
    have hζ_one : ζ 1 = (H.relIndex L : ℂ) := by
      simpa [Section1.degree_apply] using hdegζ
    rw [Section1.degree_apply]
    simp [hφ_one, hζ_one, smul_eq_mul, mul_comm]

private theorem theorem_7_8_member_isCharacter
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ φ : Section1.ClassFunction L}
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ)
    (hφ : φ ∈ S) :
    Section1.IsCharacter φ := by
  rcases h78 with ⟨_hHL, _hST, hpunctured, _hcoherent, _hν, _hζS, _hζ, _hdeg⟩
  rcases (hpunctured φ).mp hφ with ⟨θ, hθ, _hθne, hφeq⟩
  have hθchar : Section1.IsCharacter θ :=
    isCharacter_of_isIrreducibleCharacterOnGroup_pf78 hθ
  rw [hφeq]
  exact Section1.isCharacter_inducedCF_of_isCharacter (H.subgroupOf L) θ hθchar

public theorem theorem_7_8_member_scalarProduct_self_eq_cfNormSq
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ φ : Section1.ClassFunction L}
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ)
    (hφ : φ ∈ S) :
    Section1.scalarProduct L φ φ = (Section5.cfNormSq φ : ℂ) :=
  Section5.scalarProduct_self_eq_cfNormSq_of_character
    (theorem_7_8_member_isCharacter h78 hφ)

public theorem theorem_7_8_member_cfNormSq_ne_zero
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ φ : Section1.ClassFunction L}
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ)
    (hφ : φ ∈ S) :
    (Section5.cfNormSq φ : ℂ) ≠ 0 := by
  rcases theorem_7_8_degree_zero_combo_mem_integerSpanOn h78 hφ with
    ⟨m, hm_ne, hdeg, _hcombo⟩
  have hrel_ne : (H.relIndex L : ℂ) ≠ 0 := by
    haveI : (H.subgroupOf L).FiniteIndex := inferInstance
    have hrel : H.relIndex L ≠ 0 := by
      simpa [Subgroup.relIndex] using
        (Subgroup.FiniteIndex.index_ne_zero (H := H.subgroupOf L))
    exact_mod_cast hrel
  have hmC_ne : (m : ℂ) ≠ 0 := by
    exact_mod_cast hm_ne
  have hdeg_ne : Section1.degree φ ≠ 0 := by
    rw [hdeg]
    exact mul_ne_zero hrel_ne hmC_ne
  intro hnorm
  have hnormR : Section5.cfNormSq φ = 0 := by
    exact_mod_cast hnorm
  have hφzero : φ = 0 := Section5.cfNormSq_eq_zero hnormR
  have hdeg_zero : Section1.degree φ = 0 := by
    rw [hφzero]
    simp [Section1.degree]
  exact hdeg_ne hdeg_zero

public theorem theorem_7_8_punctured_member_principal_orthogonal
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {φ : Section1.ClassFunction L}
    (hpunctured : puncturedInducedFamily (H.subgroupOf L) S)
    (hφ : φ ∈ S) :
    Section1.scalarProduct L φ (Section1.principalCharacter L) = 0 := by
  rcases (hpunctured φ).mp hφ with ⟨θ, hθ, hθne, hφeq⟩
  rw [hφeq]
  have hclass : Section1.IsClassFunction (Section1.principalCharacter L) := by
    intro x g
    simp [Section1.principalCharacter]
  rw [Section1.scalarProduct_inducedCF_left (H.subgroupOf L) θ
    (Section1.principalCharacter L) hclass]
  have hres :
      Section1.subgroupRestriction (H.subgroupOf L) (Section1.principalCharacter L) =
        Section1.principalCharacter (H.subgroupOf L) := by
    ext x
    simp [Section1.subgroupRestriction, Section1.principalCharacter]
  rw [hres]
  exact Section1.scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne hθ hθne

private theorem theorem_7_8_member_principal_orthogonal
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ φ : Section1.ClassFunction L}
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ)
    (hφ : φ ∈ S) :
    Section1.scalarProduct L φ (Section1.principalCharacter L) = 0 := by
  rcases h78 with ⟨_hHL, _hST, hpunctured, _hcoherent, _hν, _hζS, _hζ, _hdeg⟩
  exact theorem_7_8_punctured_member_principal_orthogonal hpunctured hφ

public theorem theorem_7_8_combo_CFOn
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ φ : Section1.ClassFunction L}
    (h76 : hypothesis_7_6_statement A L H K T)
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ)
    (hφ : φ ∈ S) {m : ℕ}
    (hdeg : Section1.degree φ = (H.relIndex L : ℂ) * (m : ℂ)) :
    Section2.CFOn L A (φ - (m : ℂ) • ζ) := by
  rcases h76 with ⟨_hHL76, hHnorm, _h71, hAeq, _hT⟩
  haveI : (H.subgroupOf L).Normal := hHnorm
  rcases h78 with ⟨_hHL, _hST, hpunctured, _hcoherent, _hν, hζS, _hζ, hdegζ⟩
  rcases (hpunctured φ).mp hφ with ⟨θφ, _hθφ, _hθφne, hφeq⟩
  rcases (hpunctured ζ).mp hζS with ⟨θζ, _hθζ, _hθζne, hζeq⟩
  have hφclass : Section1.IsClassFunction φ := by
    rw [hφeq]
    exact Section1.inducedCF_isClassFunction (H.subgroupOf L) θφ
  have hζclass : Section1.IsClassFunction ζ := by
    rw [hζeq]
    exact Section1.inducedCF_isClassFunction (H.subgroupOf L) θζ
  constructor
  · intro x g
    simp [Pi.sub_apply, hφclass x g, hζclass x g]
  · intro l hlA
    have hφ_one : φ 1 = (H.relIndex L : ℂ) * (m : ℂ) := by
      simpa [Section1.degree_apply] using hdeg
    have hζ_one : ζ 1 = (H.relIndex L : ℂ) := by
      simpa [Section1.degree_apply] using hdegζ
    have hα_one : (φ - (m : ℂ) • ζ) (1 : L) = 0 := by
      simp [Pi.sub_apply, hφ_one, hζ_one, smul_eq_mul, mul_comm]
    by_cases hl_one : l = 1
    · simpa [hl_one] using hα_one
    · have hl_ne_oneG : (l : G) ≠ 1 := by
        intro hG
        apply hl_one
        ext
        exact hG
      have hlnotH : (l : G) ∉ H := by
        intro hlH
        apply hlA
        rw [hAeq]
        exact ⟨hlH, hl_ne_oneG⟩
      have hlnotHsub : l ∉ H.subgroupOf L := by
        intro hlHsub
        exact hlnotH hlHsub
      have hφ_zero : φ l = 0 := by
        rw [hφeq]
        exact Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal
          (H.subgroupOf L) θφ hlnotHsub
      have hζ_zero : ζ l = 0 := by
        rw [hζeq]
        exact Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal
          (H.subgroupOf L) θζ hlnotHsub
      simp [Pi.sub_apply, hφ_zero, hζ_zero]

private theorem theorem_7_8_combo_principal_orthogonal
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ φ : Section1.ClassFunction L}
    (h76 : hypothesis_7_6_statement A L H K T)
    (hτ : agreesWithDadeTransform A L K τ)
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ)
    (hφ : φ ∈ S) :
    ∃ m : ℕ,
      m ≠ 0 ∧
      Section1.degree φ = (H.relIndex L : ℂ) * (m : ℂ) ∧
        Section1.scalarProduct G (ν (φ - (m : ℂ) • ζ))
          (Section1.principalCharacter G) = 0 := by
  rcases theorem_7_8_degree_zero_combo_mem_integerSpanOn h78 hφ with ⟨m, hm_ne, hdeg, hcombo⟩
  refine ⟨m, hm_ne, hdeg, ?_⟩
  let α : Section1.ClassFunction L := φ - (m : ℂ) • ζ
  have hCFOn : Section2.CFOn L A α :=
    theorem_7_8_combo_CFOn h76 h78 hφ hdeg
  have h78orig := h78
  rcases h78 with ⟨_hHL, _hST, _hpunctured, _hcoherent, hν, hζS, _hζ, _hdegζ⟩
  rcases hτ with ⟨hAL, hτ_eq⟩
  rcases h76 with ⟨_hHL76, _hHnorm, h71, _hAeq, _hT⟩
  have hντ : ν α = τ α := hν.2.2 α hcombo
  have hτdade : τ α = Section2.dadeTransform K hAL α :=
    hτ_eq α hCFOn
  have hprincipalG : Section1.IsClassFunction (Section1.principalCharacter G) := by
    intro x g
    simp [Section1.principalCharacter]
  have hprincipalL : Section1.IsClassFunction (Section1.principalCharacter L) := by
    intro x g
    simp [Section1.principalCharacter]
  have hprincipalAgree :
      ∀ ⦃a : G⦄, (ha : a ∈ A) →
        Section1.principalCharacter L ⟨a, hAL a ha⟩ =
          Section2.dadeAveragingFunction L K (Section1.principalCharacter G)
            ⟨a, hAL a ha⟩ := by
    intro a ha
    unfold Section2.dadeAveragingFunction
    simp only [Section1.principalCharacter, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    rw [← Nat.card_eq_fintype_card]
    have hcard : (Nat.card (K a) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := K a)).ne'
    field_simp [hcard]
  have hDade :=
    (Section2.proposition_2_7 A L K h71 hAL α
      (Section1.principalCharacter G) hCFOn hprincipalG
      (Section1.principalCharacter L) hprincipalL hprincipalAgree).1
  have hφ0 := theorem_7_8_member_principal_orthogonal h78orig hφ
  have hζ0 := theorem_7_8_member_principal_orthogonal h78orig hζS
  have hLzero : Section1.scalarProduct L α (Section1.principalCharacter L) = 0 := by
    have hmζ0 :
        Section1.scalarProduct L ((m : ℂ) • ζ) (Section1.principalCharacter L) = 0 := by
      rw [Section1.scalarProduct_smul_left, hζ0, mul_zero]
    have hneg :
        Section1.scalarProduct L (-((m : ℂ) • ζ)) (Section1.principalCharacter L) = 0 := by
      have h := Section1.scalarProduct_smul_left (-1 : ℂ) ((m : ℂ) • ζ)
        (Section1.principalCharacter L)
      rw [hmζ0] at h
      simpa using h
    change Section1.scalarProduct L (φ - (m : ℂ) • ζ) (Section1.principalCharacter L) = 0
    rw [sub_eq_add_neg, Section1.scalarProduct_add_left]
    rw [hφ0, hneg]
    simp
  calc
    Section1.scalarProduct G (ν (φ - (m : ℂ) • ζ)) (Section1.principalCharacter G)
        = Section1.scalarProduct G (ν α) (Section1.principalCharacter G) := by rfl
    _ = Section1.scalarProduct G (τ α) (Section1.principalCharacter G) := by rw [hντ]
    _ = Section1.scalarProduct G (Section2.dadeTransform K hAL α)
        (Section1.principalCharacter G) := by rw [hτdade]
    _ = Section1.scalarProduct L α (Section1.principalCharacter L) := hDade
    _ = 0 := hLzero

public theorem theorem_7_8_scalarProduct_distinct_members
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ φ ψ : Section1.ClassFunction L}
    (h76 : hypothesis_7_6_statement A L H K T)
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ)
    (hφ : φ ∈ S) (hψ : ψ ∈ S) (hneq : φ ≠ ψ) :
    Section1.scalarProduct L φ ψ = 0 := by
  rcases h76 with ⟨_hHL76, hHnorm, _h71, _hAeq, _hT⟩
  haveI : (H.subgroupOf L).Normal := hHnorm
  rcases h78 with ⟨_hHL, _hST, hpunctured, _hcoherent, _hν, _hζS, _hζ, _hdeg⟩
  rcases (hpunctured φ).mp hφ with ⟨θφ, hθφ, _hθφne, hφeq⟩
  rcases (hpunctured ψ).mp hψ with ⟨θψ, hθψ, _hθψne, hψeq⟩
  rcases hθφ with ⟨nφ, ρφ, hρφ, hθφeq⟩
  rcases hθψ with ⟨nψ, ρψ, hρψ, hθψeq⟩
  rw [hφeq, hψeq, hθφeq, hθψeq]
  refine Section1.proposition_1_5_c_nonconjugate_rep_orbit_relIndex_canonical
    (H.subgroupOf L) ρφ.character ρφ ρψ rfl hρφ hρψ ?_
  intro i hconj
  apply hneq
  rw [hφeq, hψeq, hθφeq, hθψeq]
  exact Section1.proposition_1_5_c_conjugate_orbit_canonical
    (H.subgroupOf L) ρψ ρφ.character i hconj

public theorem theorem_7_8_weightedSum_scalarProduct_of_mem
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ χ : Section1.ClassFunction L}
    (h76 : hypothesis_7_6_statement A L H K T)
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ)
    (hχ : χ ∈ S) :
    Section1.scalarProduct G
      (theorem_7_8_weightedSum S ν (H.relIndex L)) (ν χ) =
        χ 1 / (H.relIndex L : ℂ) := by
  classical
  let e : ℕ := H.relIndex L
  change Section1.scalarProduct G (theorem_7_8_weightedSum S ν e) (ν χ) =
    χ 1 / (e : ℂ)
  let χS : S := ⟨χ, hχ⟩
  have heC : (e : ℂ) ≠ 0 := by
    haveI : (H.subgroupOf L).FiniteIndex := inferInstance
    have hrel : H.relIndex L ≠ 0 := by
      simpa [Subgroup.relIndex] using
        (Subgroup.FiniteIndex.index_ne_zero (H := H.subgroupOf L))
    exact_mod_cast hrel
  have hsum :
      theorem_7_8_weightedSum S ν e =
        fun g =>
          ∑ X : S,
            ((((X : Section1.ClassFunction L) 1) /
              ((e : ℂ) * (Section5.cfNormSq (X : Section1.ClassFunction L) : ℂ))) •
                ν (X : Section1.ClassFunction L)) g := by
    ext g
    simp only [theorem_7_8_weightedSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact (Finset.sum_attach S
      (fun x : Section1.ClassFunction L =>
        x 1 / ((e : ℂ) * (Section5.cfNormSq x : ℂ)) * ν x g)).symm
  calc
    Section1.scalarProduct G (theorem_7_8_weightedSum S ν e) (ν χ) =
        ∑ X : S,
          Section1.scalarProduct G
            ((((X : Section1.ClassFunction L) 1) /
              ((e : ℂ) * (Section5.cfNormSq (X : Section1.ClassFunction L) : ℂ))) •
                ν (X : Section1.ClassFunction L)) (ν χ) := by
          rw [hsum, Section1.scalarProduct_fintype_sum_left]
    _ = ∑ X : S, if X = χS then χ 1 / (e : ℂ) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro X _hX
          by_cases hXχ : X = χS
          · subst hXχ
            simp only [↓reduceIte]
            have hselfν := theorem_7_8_nu_scalarProduct_of_mem h78 hχ hχ
            have hselfL := theorem_7_8_member_scalarProduct_self_eq_cfNormSq h78 hχ
            have hcf_ne := theorem_7_8_member_cfNormSq_ne_zero h78 hχ
            calc
              Section1.scalarProduct G
                  (((χ 1) / ((e : ℂ) * (Section5.cfNormSq χ : ℂ))) • ν χ) (ν χ) =
                    ((χ 1) / ((e : ℂ) * (Section5.cfNormSq χ : ℂ))) *
                      Section1.scalarProduct G (ν χ) (ν χ) := by
                        rw [Section1.scalarProduct_smul_left]
              _ = ((χ 1) / ((e : ℂ) * (Section5.cfNormSq χ : ℂ))) *
                    (Section5.cfNormSq χ : ℂ) := by
                        rw [hselfν, hselfL]
              _ = χ 1 / (e : ℂ) := by
                        field_simp [heC, hcf_ne]
          · simp only [hXχ, ↓reduceIte]
            have hneq_val : (X : Section1.ClassFunction L) ≠ χ := by
              intro hval
              exact hXχ (Subtype.ext hval)
            have horthL :
                Section1.scalarProduct L (X : Section1.ClassFunction L) χ = 0 :=
              theorem_7_8_scalarProduct_distinct_members h76 h78 X.2 hχ hneq_val
            have horthG :
                Section1.scalarProduct G (ν (X : Section1.ClassFunction L)) (ν χ) = 0 := by
              rw [theorem_7_8_nu_scalarProduct_of_mem h78 X.2 hχ, horthL]
            rw [Section1.scalarProduct_smul_left, horthG, mul_zero]
    _ = χ 1 / (e : ℂ) := by
          simp [χS]

private theorem theorem_7_8_nu_zeta_signed
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L}
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ) :
    Section3.IsSignedIrreducibleCharacter (ν ζ) := by
  have h78orig := h78
  rcases h78 with ⟨_hHL, _hST, _hpunctured, _hcoherent, hν, hζS, _hζ, _hdeg⟩
  have hvirt : Theory.Character.IsVirtualCharacter (ν ζ) :=
    hν.2.1 ζ (Section5.integerSpan_of_mem S hζS)
  exact Section5.signed_irreducible_of_virtual_norm_one_pf59 hvirt
    (theorem_7_8_nu_zeta_norm h78orig)

private theorem signed_scalarProduct_principal_eq_zero_or_eq_or_neg
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    Section1.scalarProduct G χ (Section1.principalCharacter G) = 0 ∨
      χ = Section1.principalCharacter G ∨ χ = -Section1.principalCharacter G := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  rcases hε with rfl | rfl
  · by_cases hμprin : μ = Section1.principalCharacter G
    · right; left; ext g; simp [hμprin]
    · left
      simpa using
        Section1.scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne hμ hμprin
  · by_cases hμprin : μ = Section1.principalCharacter G
    · right; right; ext g; simp [hμprin]
    · left
      have hzero :=
        Section1.scalarProduct_irreducibleCharacter_principal_eq_zero_of_ne hμ hμprin
      rw [Section1.scalarProduct_smul_left]
      simp [hzero]

private theorem theorem_7_8_principal_orthogonal_to_image
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L}
    (h76 : hypothesis_7_6_statement A L H K T)
    (hτ : agreesWithDadeTransform A L K τ)
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ) :
    orthogonalToImage S ν (Section1.principalCharacter G) := by
  classical
  let principalG : Section1.ClassFunction G := Section1.principalCharacter G
  let spToPrincipal := fun χ : Section1.ClassFunction G =>
    Section1.scalarProduct G χ principalG
  have hcombo_relation :
      ∀ {χ : Section1.ClassFunction L} {m : ℕ},
        Section1.scalarProduct G (ν (χ - (m : ℂ) • ζ)) principalG = 0 →
          spToPrincipal (ν χ) =
            (m : ℂ) * spToPrincipal (ν ζ) := by
    intro χ m hcombo
    have hcombo_expand :
        Section1.scalarProduct G (ν χ - (m : ℂ) • ν ζ) principalG = 0 := by
      simpa [principalG] using hcombo
    have hformula :
        Section1.scalarProduct G (ν χ - (m : ℂ) • ν ζ) principalG =
          spToPrincipal (ν χ) - (m : ℂ) * spToPrincipal (ν ζ) := by
      have hneg :
          Section1.scalarProduct G (-((m : ℂ) • ν ζ)) principalG =
            -((m : ℂ) * spToPrincipal (ν ζ)) := by
        rw [show -((m : ℂ) • ν ζ) = (-(m : ℂ)) • ν ζ by
          ext g
          simp]
        rw [Section1.scalarProduct_smul_left]
        ring
      rw [sub_eq_add_neg, Section1.scalarProduct_add_left, hneg]
      ring
    rw [hformula] at hcombo_expand
    exact sub_eq_zero.mp hcombo_expand
  have hνζ_principal : spToPrincipal (ν ζ) = 0 := by
    have hsigned := theorem_7_8_nu_zeta_signed h78
    rcases signed_scalarProduct_principal_eq_zero_or_eq_or_neg hsigned with hzero | hcases
    · simpa [spToPrincipal, principalG] using hzero
    · rcases theorem_7_8_exists_distinct_member h78 with ⟨φ, hφS, hφneζ⟩
      rcases theorem_7_8_combo_principal_orthogonal h76 hτ h78 hφS with
        ⟨m, hm_ne, _hdeg, hcombo⟩
      rcases h78 with ⟨_hHL, _hST, _hpunctured, _hcoherent, _hν, hζS, _hζ, _hdeg⟩
      have hφζ_L : Section1.scalarProduct L φ ζ = 0 :=
        theorem_7_8_scalarProduct_distinct_members h76
          (show theorem_7_8_hypothesis L H T S τ ν ζ from
            ⟨_hHL, _hST, _hpunctured, _hcoherent, _hν, hζS, _hζ, _hdeg⟩)
          hφS hζS hφneζ
      have hνφνζ : Section1.scalarProduct G (ν φ) (ν ζ) = 0 := by
        rw [theorem_7_8_nu_scalarProduct_of_mem
          (show theorem_7_8_hypothesis L H T S τ ν ζ from
            ⟨_hHL, _hST, _hpunctured, _hcoherent, _hν, hζS, _hζ, _hdeg⟩)
          hφS hζS, hφζ_L]
      have hνφ_principal : spToPrincipal (ν φ) = 0 := by
        rcases hcases with hζeq | hζeqneg
        · simpa [spToPrincipal, principalG, hζeq] using hνφνζ
        · have htmp :
              Section1.scalarProduct G (ν φ) (-(Section1.principalCharacter G)) = 0 := by
            simpa [hζeqneg] using hνφνζ
          rw [show (-(Section1.principalCharacter G) : Section1.ClassFunction G) =
              (-1 : ℂ) • Section1.principalCharacter G by
            ext g
            simp] at htmp
          rw [Section1.scalarProduct_smul_right] at htmp
          simpa [spToPrincipal, principalG] using htmp
      have hrel := hcombo_relation hcombo
      rw [hνφ_principal] at hrel
      have hmul_zero : (m : ℂ) * spToPrincipal (ν ζ) = 0 := by
        simpa using hrel.symm
      have hνζ_principal_ne : spToPrincipal (ν ζ) ≠ 0 := by
        have hpp : Section1.scalarProduct G
            (Section1.principalCharacter G) (Section1.principalCharacter G) = 1 := by
          simp [Section1.scalarProduct, Section1.principalCharacter]
        rcases hcases with hζeq | hζeqneg
        · simp [spToPrincipal, principalG, hζeq, hpp]
        · dsimp [spToPrincipal, principalG]
          rw [hζeqneg]
          rw [show (-(Section1.principalCharacter G) : Section1.ClassFunction G) =
              (-1 : ℂ) • Section1.principalCharacter G by
            ext g
            simp]
          rw [Section1.scalarProduct_smul_left]
          simp [hpp]
      have hmC : (m : ℂ) ≠ 0 := by
        exact_mod_cast hm_ne
      exact False.elim ((mul_eq_zero.mp hmul_zero).elim hmC hνζ_principal_ne)
  intro χ hχS
  rcases theorem_7_8_combo_principal_orthogonal h76 hτ h78 hχS with
    ⟨m, _hm_ne, _hdeg, hcombo⟩
  have hχ_principal : spToPrincipal (ν χ) = 0 := by
    rw [hcombo_relation hcombo, hνζ_principal, mul_zero]
  have hχ_principal' : Section1.scalarProduct G (ν χ) principalG = 0 := by
    simpa [spToPrincipal] using hχ_principal
  have hswap := Section1.scalarProduct_star_swap (G := G) principalG (ν χ)
  rw [hχ_principal'] at hswap
  simpa [spToPrincipal, principalG] using hswap.symm

public theorem theorem_7_8_principalInduced_principal_scalar
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G} :
    Section1.scalarProduct L (principalInducedCharacter L H)
      (Section1.principalCharacter L) = 1 := by
  unfold principalInducedCharacter
  have hclass : Section1.IsClassFunction (Section1.principalCharacter L) := by
    intro x g
    simp [Section1.principalCharacter]
  rw [Section1.scalarProduct_inducedCF_left (H.subgroupOf L)
    (Section1.principalCharacter (H.subgroupOf L))
    (Section1.principalCharacter L) hclass]
  have hres :
      Section1.subgroupRestriction (H.subgroupOf L) (Section1.principalCharacter L) =
        Section1.principalCharacter (H.subgroupOf L) := by
    ext x
    simp [Section1.subgroupRestriction, Section1.principalCharacter]
  rw [hres]
  simp [Section1.scalarProduct, Section1.principalCharacter]

public theorem theorem_7_8_principalInduced_punctured_member_scalar
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    {S : Finset (Section1.ClassFunction L)}
    {φ : Section1.ClassFunction L}
    (hHnorm : (H.subgroupOf L).Normal)
    (hpunctured : puncturedInducedFamily (H.subgroupOf L) S)
    (hφ : φ ∈ S) :
    Section1.scalarProduct L (principalInducedCharacter L H) φ = 0 := by
  classical
  haveI : (H.subgroupOf L).Normal := hHnorm
  rcases (hpunctured φ).mp hφ with ⟨θ, hθ, hθne, hφeq⟩
  rcases hθ with ⟨n, ρθ, hρθ, hθeq⟩
  rcases (Section3.principalCharacter_isIrreducibleCharacterOnGroup
      (G := H.subgroupOf L)) with
    ⟨nprin, ρprin, hprin_irred, hprin_char⟩
  have hnotConj :
      ∀ i : Section1.conjugateOrbitIndex (H.subgroupOf L) ρθ.character,
        ρprin.character ≠
          Section1.conjugateOrbitConj (H.subgroupOf L) ρθ.character i := by
    intro i hbad
    apply hθne
    rw [hθeq]
    ext h
    revert hbad
    refine Quotient.inductionOn i ?_
    intro x hbad
    have hmem : x⁻¹ * (h : H.subgroupOf L) * x ∈ H.subgroupOf L := by
      simpa using hHnorm.conj_mem (h : L) h.2 x⁻¹
    have happ := congrArg
      (fun f : Section1.ClassFunction (H.subgroupOf L) =>
        f ⟨x⁻¹ * (h : H.subgroupOf L) * x, hmem⟩) hbad
    have hval :
        ρθ.character h =
          ρprin.character ⟨x⁻¹ * (h : H.subgroupOf L) * x, hmem⟩ := by
      simpa [Section1.conjugateOrbitConj, Section1.conjugateOnNormal,
        mul_assoc] using happ.symm
    have hprin_one :
        ρprin.character ⟨x⁻¹ * (h : H.subgroupOf L) * x, hmem⟩ = 1 := by
      rw [← hprin_char]
      simp [Section1.principalCharacter]
    exact hval.trans hprin_one
  calc
    Section1.scalarProduct L (principalInducedCharacter L H) φ =
        Section1.scalarProduct L
          (Section1.inducedCF (H.subgroupOf L)
            (Section1.principalCharacter (H.subgroupOf L)))
          (Section1.inducedCF (H.subgroupOf L) θ) := by
            rw [principalInducedCharacter, hφeq]
    _ = Section1.scalarProduct L
          (Section1.inducedCF (H.subgroupOf L) ρprin.character)
          (Section1.inducedCF (H.subgroupOf L) ρθ.character) := by
            rw [hprin_char, hθeq]
    _ = 0 := by
          exact Section1.proposition_1_5_c_nonconjugate_rep_orbit_relIndex_canonical
            (H.subgroupOf L) ρprin.character ρprin ρθ rfl
            hprin_irred hρθ hnotConj

private theorem theorem_7_8_principalInduced_member_scalar
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ φ : Section1.ClassFunction L}
    (h76 : hypothesis_7_6_statement A L H K T)
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ)
    (hφ : φ ∈ S) :
    Section1.scalarProduct L (principalInducedCharacter L H) φ = 0 := by
  rcases h76 with ⟨_hHL76, hHnorm, _h71, _hAeq, _hT⟩
  rcases h78 with
    ⟨_hHL, _hST, hpunctured, _hcoherent, _hν, _hζS, _hζ, _hdegζ⟩
  exact theorem_7_8_principalInduced_punctured_member_scalar
    hHnorm hpunctured hφ

public theorem theorem_7_8_principalInduced_self_scalar
    {G : Type u} [Group G] [Finite G]
    {L H : Subgroup G}
    (hHnorm : (H.subgroupOf L).Normal) :
    Section1.scalarProduct L (principalInducedCharacter L H)
      (principalInducedCharacter L H) = (H.relIndex L : ℂ) := by
  haveI : (H.subgroupOf L).Normal := hHnorm
  rcases (Section3.principalCharacter_isIrreducibleCharacterOnGroup
      (G := H.subgroupOf L)) with ⟨n, ρ, hρirr, hρchar⟩
  have hself := Section1.proposition_1_5_b_rep_orbit_relIndex_canonical
    (H.subgroupOf L) ρ hρirr
  have hinertia : Section1.inertiaSubgroup (H.subgroupOf L) ρ.character = ⊤ := by
    ext x
    constructor
    · intro _hx
      simp
    · intro _hx
      ext h
      simp [Section1.conjugateOnNormal, ← hρchar, Section1.principalCharacter]
  have hrel :
      (H.subgroupOf L).relIndex
          (Section1.inertiaSubgroup (H.subgroupOf L) ρ.character) =
        H.relIndex L := by
    rw [hinertia]
    simpa using
      (Subgroup.relIndex_subgroupOf (H := H) (K := L) (L := L) le_rfl)
  calc
    Section1.scalarProduct L (principalInducedCharacter L H)
        (principalInducedCharacter L H) =
        Section1.scalarProduct L (Section1.inducedCF (H.subgroupOf L) ρ.character)
          (Section1.inducedCF (H.subgroupOf L) ρ.character) := by
          rw [principalInducedCharacter, hρchar]
    _ = (H.relIndex L : ℂ) := by
          rw [hself, hrel]

private theorem theorem_7_8_betaInput_CFOn
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L}
    (h76 : hypothesis_7_6_statement A L H K T)
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ) :
    Section2.CFOn L A (theorem_7_8_betaInput L H ζ) := by
  rcases h76 with ⟨_hHL76, hHnorm, _h71, hAeq, _hT⟩
  haveI : (H.subgroupOf L).Normal := hHnorm
  rcases h78 with ⟨_hHL, _hST, hpunctured, _hcoherent, _hν, hζS, _hζ, hdegζ⟩
  rcases (hpunctured ζ).mp hζS with ⟨θζ, _hθζ, _hθζne, hζeq⟩
  have hprincipalClass : Section1.IsClassFunction (principalInducedCharacter L H) := by
    unfold principalInducedCharacter
    exact Section1.inducedCF_isClassFunction (H.subgroupOf L)
      (Section1.principalCharacter (H.subgroupOf L))
  have hζclass : Section1.IsClassFunction ζ := by
    rw [hζeq]
    exact Section1.inducedCF_isClassFunction (H.subgroupOf L) θζ
  constructor
  · intro x g
    simp [theorem_7_8_betaInput, Pi.sub_apply, hprincipalClass x g, hζclass x g]
  · intro l hlA
    have hprincipal_degree :
        Section1.degree (principalInducedCharacter L H) = (H.relIndex L : ℂ) := by
      unfold principalInducedCharacter
      rw [Section1.degree_inducedClassFunction]
      simp [Section1.degree, Section1.principalCharacter, Subgroup.relIndex]
    have hprincipal_one : principalInducedCharacter L H (1 : L) = (H.relIndex L : ℂ) := by
      simpa [Section1.degree_apply] using hprincipal_degree
    have hζ_one : ζ 1 = (H.relIndex L : ℂ) := by
      simpa [Section1.degree_apply] using hdegζ
    have hβ_one : theorem_7_8_betaInput L H ζ (1 : L) = 0 := by
      simp [theorem_7_8_betaInput, Pi.sub_apply, hprincipal_one, hζ_one]
    by_cases hl_one : l = 1
    · simpa [hl_one] using hβ_one
    · have hl_ne_oneG : (l : G) ≠ 1 := by
        intro hG
        apply hl_one
        ext
        exact hG
      have hlnotH : (l : G) ∉ H := by
        intro hlH
        apply hlA
        rw [hAeq]
        exact ⟨hlH, hl_ne_oneG⟩
      have hlnotHsub : l ∉ H.subgroupOf L := by
        intro hlHsub
        exact hlnotH hlHsub
      have hprincipal_zero : principalInducedCharacter L H l = 0 := by
        unfold principalInducedCharacter
        exact Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal
          (H.subgroupOf L) (Section1.principalCharacter (H.subgroupOf L)) hlnotHsub
      have hζ_zero : ζ l = 0 := by
        rw [hζeq]
        exact Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal
          (H.subgroupOf L) θζ hlnotHsub
      simp [theorem_7_8_betaInput, Pi.sub_apply, hprincipal_zero, hζ_zero]

private theorem theorem_7_8_beta_combo_scalarProduct_of_ne
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ φ : Section1.ClassFunction L}
    (h76 : hypothesis_7_6_statement A L H K T)
    (hτ : agreesWithDadeTransform A L K τ)
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ)
    (hφ : φ ∈ S) (hφne : φ ≠ ζ) :
    ∃ m : ℕ,
      m ≠ 0 ∧
      Section1.degree φ = (H.relIndex L : ℂ) * (m : ℂ) ∧
        Section1.scalarProduct G (theorem_7_8_beta L H τ ζ)
          (ν (φ - (m : ℂ) • ζ)) = (m : ℂ) := by
  rcases theorem_7_8_degree_zero_combo_mem_integerSpanOn h78 hφ with
    ⟨m, hm_ne, hdeg, hcombo⟩
  refine ⟨m, hm_ne, hdeg, ?_⟩
  let βL : Section1.ClassFunction L := theorem_7_8_betaInput L H ζ
  let α : Section1.ClassFunction L := φ - (m : ℂ) • ζ
  have hβCFOn : Section2.CFOn L A βL := theorem_7_8_betaInput_CFOn h76 h78
  have hαCFOn : Section2.CFOn L A α :=
    theorem_7_8_combo_CFOn h76 h78 hφ hdeg
  rcases hτ with ⟨hAL, hτ_eq⟩
  rcases h76 with ⟨_hHL76, _hHnorm, h71, _hAeq, _hT⟩
  rcases h78 with ⟨_hHL, _hST, _hpunctured, _hcoherent, hν, hζS, _hζ, _hdegζ⟩
  have hντ : ν α = τ α := hν.2.2 α hcombo
  have hτβ : τ βL = Section2.dadeTransform K hAL βL :=
    hτ_eq βL hβCFOn
  have hτα : τ α = Section2.dadeTransform K hAL α :=
    hτ_eq α hαCFOn
  have hDade :=
    (Section2.theorem_2_6 A L K h71 hAL).1 βL α hβCFOn hαCFOn
  have hprincipalφ :
      Section1.scalarProduct L (principalInducedCharacter L H) φ = 0 :=
    theorem_7_8_principalInduced_member_scalar
      (show hypothesis_7_6_statement A L H K T from
        ⟨_hHL76, _hHnorm, h71, _hAeq, _hT⟩)
      (show theorem_7_8_hypothesis L H T S τ ν ζ from
        ⟨_hHL, _hST, _hpunctured, _hcoherent, hν, hζS, _hζ, _hdegζ⟩)
      hφ
  have hprincipalζ :
      Section1.scalarProduct L (principalInducedCharacter L H) ζ = 0 :=
    theorem_7_8_principalInduced_member_scalar
      (show hypothesis_7_6_statement A L H K T from
        ⟨_hHL76, _hHnorm, h71, _hAeq, _hT⟩)
      (show theorem_7_8_hypothesis L H T S τ ν ζ from
        ⟨_hHL, _hST, _hpunctured, _hcoherent, hν, hζS, _hζ, _hdegζ⟩)
      hζS
  have hφζ :
      Section1.scalarProduct L φ ζ = 0 :=
    theorem_7_8_scalarProduct_distinct_members
      (show hypothesis_7_6_statement A L H K T from
        ⟨_hHL76, _hHnorm, h71, _hAeq, _hT⟩)
      (show theorem_7_8_hypothesis L H T S τ ν ζ from
        ⟨_hHL, _hST, _hpunctured, _hcoherent, hν, hζS, _hζ, _hdegζ⟩)
      hφ hζS hφne
  have hζφ :
      Section1.scalarProduct L ζ φ = 0 := by
    have hswap := Section1.scalarProduct_star_swap (G := L) ζ φ
    rw [hφζ] at hswap
    simpa using hswap.symm
  have hζζ : Section1.scalarProduct L ζ ζ = 1 :=
    theorem_7_8_zeta_scalarProduct_self
      (show theorem_7_8_hypothesis L H T S τ ν ζ from
        ⟨_hHL, _hST, _hpunctured, _hcoherent, hν, hζS, _hζ, _hdegζ⟩)
  have hL :
      Section1.scalarProduct L βL α = (m : ℂ) := by
    change Section1.scalarProduct L
      (principalInducedCharacter L H - ζ) (φ - (m : ℂ) • ζ) = (m : ℂ)
    rw [scalarProduct_sub_left_pf78, scalarProduct_sub_right_pf78,
      scalarProduct_sub_right_pf78]
    rw [Section1.scalarProduct_smul_right, Section1.scalarProduct_smul_right]
    simp [hprincipalφ, hprincipalζ, hζφ, hζζ]
  calc
    Section1.scalarProduct G (theorem_7_8_beta L H τ ζ)
        (ν (φ - (m : ℂ) • ζ))
        = Section1.scalarProduct G (τ βL) (ν α) := by
            rfl
    _ = Section1.scalarProduct G (τ βL) (τ α) := by rw [hντ]
    _ = Section1.scalarProduct G (Section2.dadeTransform K hAL βL)
        (Section2.dadeTransform K hAL α) := by rw [hτβ, hτα]
    _ = Section1.scalarProduct L βL α := hDade
    _ = (m : ℂ) := hL

public theorem theorem_7_8_beta_virtual
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L}
    (h76 : hypothesis_7_6_statement A L H K T)
    (hτ : agreesWithDadeTransform A L K τ)
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ) :
    Theory.Character.IsVirtualCharacter (theorem_7_8_beta L H τ ζ) := by
  let βL : Section1.ClassFunction L := theorem_7_8_betaInput L H ζ
  have hCFOn : Section2.CFOn L A βL := theorem_7_8_betaInput_CFOn h76 h78
  rcases h76 with ⟨_hHL76, _hHnorm, h71, _hAeq, _hT⟩
  rcases hτ with ⟨hAL, hτ_eq⟩
  rcases h78 with ⟨_hHL, _hST, _hpunctured, _hcoherent, _hν, _hζS, hζ, _hdegζ⟩
  have hprincipalVirt :
      Theory.Character.IsVirtualCharacter (principalInducedCharacter L H) := by
    unfold principalInducedCharacter
    exact Section2.inducedCF_isVirtualCharacter_of_virtualCharacter
      (H.subgroupOf L) Section3.isVirtualCharacter_principalCharacter
  have hβLvirt : Theory.Character.IsVirtualCharacter βL := by
    exact Section3.isVirtualCharacter_sub hprincipalVirt
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup hζ)
  have hβLvirtOn : Section2.virtualCharacterOn L A βL := ⟨hβLvirt, hCFOn.2⟩
  have hτβ : τ βL = Section2.dadeTransform K hAL βL :=
    hτ_eq βL hCFOn
  have hDadeVirt :=
    (Section2.theorem_2_6 A L K h71 hAL).2 βL hβLvirtOn
  change Theory.Character.IsVirtualCharacter
    (Section2.dadeTransform K hAL βL) at hDadeVirt
  change Theory.Character.IsVirtualCharacter (τ βL)
  rw [hτβ]
  exact hDadeVirt

private theorem theorem_7_8_beta_principal_scalar
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L}
    (h76 : hypothesis_7_6_statement A L H K T)
    (hτ : agreesWithDadeTransform A L K τ)
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ) :
    Section1.scalarProduct G (theorem_7_8_beta L H τ ζ)
      (Section1.principalCharacter G) = 1 := by
  let βL : Section1.ClassFunction L := theorem_7_8_betaInput L H ζ
  have hCFOn : Section2.CFOn L A βL := theorem_7_8_betaInput_CFOn h76 h78
  rcases hτ with ⟨hAL, hτ_eq⟩
  rcases h76 with ⟨_hHL76, _hHnorm, h71, _hAeq, _hT⟩
  have hτβ : τ βL = Section2.dadeTransform K hAL βL :=
    hτ_eq βL hCFOn
  have hprincipalG : Section1.IsClassFunction (Section1.principalCharacter G) := by
    intro x g
    simp [Section1.principalCharacter]
  have hprincipalL : Section1.IsClassFunction (Section1.principalCharacter L) := by
    intro x g
    simp [Section1.principalCharacter]
  have hprincipalAgree :
      ∀ ⦃a : G⦄, (ha : a ∈ A) →
        Section1.principalCharacter L ⟨a, hAL a ha⟩ =
          Section2.dadeAveragingFunction L K (Section1.principalCharacter G)
            ⟨a, hAL a ha⟩ := by
    intro a ha
    unfold Section2.dadeAveragingFunction
    simp only [Section1.principalCharacter, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    rw [← Nat.card_eq_fintype_card]
    have hcard : (Nat.card (K a) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := K a)).ne'
    field_simp [hcard]
  have hDade :=
    (Section2.proposition_2_7 A L K h71 hAL βL
      (Section1.principalCharacter G) hCFOn hprincipalG
      (Section1.principalCharacter L) hprincipalL hprincipalAgree).1
  rcases h78 with ⟨_hHL, _hST, _hpunctured, _hcoherent, _hν, hζS, _hζ, _hdegζ⟩
  have hζ0 := theorem_7_8_member_principal_orthogonal
    (show theorem_7_8_hypothesis L H T S τ ν ζ from
      ⟨_hHL, _hST, _hpunctured, _hcoherent, _hν, hζS, _hζ, _hdegζ⟩)
    hζS
  have hLzero :
      Section1.scalarProduct L βL (Section1.principalCharacter L) = 1 := by
    have hneg :
        Section1.scalarProduct L (-ζ) (Section1.principalCharacter L) = 0 := by
      have h := Section1.scalarProduct_smul_left (-1 : ℂ) ζ
        (Section1.principalCharacter L)
      rw [hζ0] at h
      simpa using h
    change Section1.scalarProduct L
      (principalInducedCharacter L H - ζ) (Section1.principalCharacter L) = 1
    rw [sub_eq_add_neg, Section1.scalarProduct_add_left]
    rw [theorem_7_8_principalInduced_principal_scalar, hneg]
    simp
  calc
    Section1.scalarProduct G (theorem_7_8_beta L H τ ζ)
        (Section1.principalCharacter G)
        = Section1.scalarProduct G (τ βL) (Section1.principalCharacter G) := by
            rfl
    _ = Section1.scalarProduct G (Section2.dadeTransform K hAL βL)
        (Section1.principalCharacter G) := by rw [hτβ]
    _ = Section1.scalarProduct L βL (Section1.principalCharacter L) := hDade
    _ = 1 := hLzero

public theorem theorem_7_8_beta_norm
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L}
    (h76 : hypothesis_7_6_statement A L H K T)
    (hτ : agreesWithDadeTransform A L K τ)
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ) :
    Section5.cfNormSq (theorem_7_8_beta L H τ ζ) =
      (H.relIndex L : ℝ) + 1 := by
  let βL : Section1.ClassFunction L := theorem_7_8_betaInput L H ζ
  have hβCFOn : Section2.CFOn L A βL := theorem_7_8_betaInput_CFOn h76 h78
  rcases hτ with ⟨hAL, hτ_eq⟩
  rcases h76 with ⟨_hHL76, hHnorm, h71, _hAeq, _hT⟩
  haveI : (H.subgroupOf L).Normal := hHnorm
  have h78orig := h78
  rcases h78 with ⟨_hHL, _hST, _hpunctured, _hcoherent, _hν, hζS, _hζ, _hdegζ⟩
  have hτβ : τ βL = Section2.dadeTransform K hAL βL :=
    hτ_eq βL hβCFOn
  have hDade :=
    (Section2.theorem_2_6 A L K h71 hAL).1 βL βL hβCFOn hβCFOn
  have hprincipalζ :
      Section1.scalarProduct L (principalInducedCharacter L H) ζ = 0 :=
    theorem_7_8_principalInduced_member_scalar
      (show hypothesis_7_6_statement A L H K T from
        ⟨_hHL76, hHnorm, h71, _hAeq, _hT⟩)
      h78orig hζS
  have hζprincipal :
      Section1.scalarProduct L ζ (principalInducedCharacter L H) = 0 := by
    have hswap := Section1.scalarProduct_star_swap (G := L)
      (principalInducedCharacter L H) ζ
    have hstarzero :
        star (Section1.scalarProduct L ζ (principalInducedCharacter L H)) = 0 := by
      simpa [hprincipalζ] using hswap
    simpa using congrArg star hstarzero
  have hζζ : Section1.scalarProduct L ζ ζ = 1 :=
    theorem_7_8_zeta_scalarProduct_self h78orig
  have hprincipalprincipal :
      Section1.scalarProduct L (principalInducedCharacter L H)
        (principalInducedCharacter L H) = (H.relIndex L : ℂ) :=
    theorem_7_8_principalInduced_self_scalar hHnorm
  have hβLnorm :
      Section1.scalarProduct L βL βL = (H.relIndex L : ℂ) + 1 := by
    change Section1.scalarProduct L (principalInducedCharacter L H - ζ)
      (principalInducedCharacter L H - ζ) = (H.relIndex L : ℂ) + 1
    rw [scalarProduct_sub_left_pf78, scalarProduct_sub_right_pf78,
      scalarProduct_sub_right_pf78]
    rw [hprincipalprincipal, hprincipalζ, hζprincipal, hζζ]
    ring
  have hβscalar :
      Section1.scalarProduct G (theorem_7_8_beta L H τ ζ)
        (theorem_7_8_beta L H τ ζ) = (H.relIndex L : ℂ) + 1 := by
    calc
      Section1.scalarProduct G (theorem_7_8_beta L H τ ζ)
          (theorem_7_8_beta L H τ ζ) =
          Section1.scalarProduct G (τ βL) (τ βL) := by
            rfl
      _ = Section1.scalarProduct G (Section2.dadeTransform K hAL βL)
          (Section2.dadeTransform K hAL βL) := by
            rw [hτβ]
      _ = Section1.scalarProduct L βL βL := hDade
      _ = (H.relIndex L : ℂ) + 1 := hβLnorm
  unfold Section5.cfNormSq
  rw [hβscalar]
  simp

public theorem theorem_7_8_beta_zeta_coeff_int
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L}
    (h76 : hypothesis_7_6_statement A L H K T)
    (hτ : agreesWithDadeTransform A L K τ)
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ) :
    ∃ a : ℤ,
      Section1.scalarProduct G (theorem_7_8_beta L H τ ζ) (ν ζ) =
        (a : ℂ) - 1 := by
  have hβvirt := theorem_7_8_beta_virtual h76 hτ h78
  rcases h78 with ⟨_hHL, _hST, _hpunctured, _hcoherent, hν, hζS, _hζ, _hdegζ⟩
  have hνζvirt : Theory.Character.IsVirtualCharacter (ν ζ) :=
    hν.2.1 ζ (Section5.integerSpan_of_mem S hζS)
  rcases Section3.scalarProduct_isVirtualCharacter_eq_int hβvirt hνζvirt with
    ⟨z, hz⟩
  refine ⟨z + 1, ?_⟩
  rw [hz]
  norm_num

public theorem theorem_7_8_beta_scalarProduct_of_mem
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ χ : Section1.ClassFunction L} {a : ℤ}
    (h76 : hypothesis_7_6_statement A L H K T)
    (hτ : agreesWithDadeTransform A L K τ)
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ)
    (hβζ :
      Section1.scalarProduct G (theorem_7_8_beta L H τ ζ) (ν ζ) =
        (a : ℂ) - 1)
    (hχ : χ ∈ S) :
    Section1.scalarProduct G (theorem_7_8_beta L H τ ζ) (ν χ) =
      if χ = ζ then (a : ℂ) - 1
      else (a : ℂ) * (χ 1 / (H.relIndex L : ℂ)) := by
  classical
  by_cases hχζ : χ = ζ
  · subst hχζ
    simp [hβζ]
  · simp only [hχζ, ↓reduceIte]
    rcases theorem_7_8_beta_combo_scalarProduct_of_ne h76 hτ h78 hχ hχζ with
      ⟨m, _hm_ne, hdeg, hcombo⟩
    let b : ℂ := Section1.scalarProduct G (theorem_7_8_beta L H τ ζ) (ν χ)
    have hνcombo :
        ν (χ - (m : ℂ) • ζ) = ν χ - (m : ℂ) • ν ζ := by
      simp
    have hcombo' :
        Section1.scalarProduct G (theorem_7_8_beta L H τ ζ)
          (ν χ - (m : ℂ) • ν ζ) = (m : ℂ) := by
      rw [← hνcombo]
      exact hcombo
    have hcombo_expand :
        b - (m : ℂ) * ((a : ℂ) - 1) = (m : ℂ) := by
      calc
        b - (m : ℂ) * ((a : ℂ) - 1) =
            Section1.scalarProduct G (theorem_7_8_beta L H τ ζ)
              (ν χ - (m : ℂ) • ν ζ) := by
                dsimp [b]
                rw [scalarProduct_sub_right_pf78, Section1.scalarProduct_smul_right, hβζ]
                simp
        _ = (m : ℂ) := hcombo'
    have hb : b = (a : ℂ) * (m : ℂ) := by
      calc
        b = (b - (m : ℂ) * ((a : ℂ) - 1)) +
            (m : ℂ) * ((a : ℂ) - 1) := by ring
        _ = (m : ℂ) + (m : ℂ) * ((a : ℂ) - 1) := by rw [hcombo_expand]
        _ = (a : ℂ) * (m : ℂ) := by ring
    have heC : (H.relIndex L : ℂ) ≠ 0 := by
      haveI : (H.subgroupOf L).FiniteIndex := inferInstance
      have hrel : H.relIndex L ≠ 0 := by
        simpa [Subgroup.relIndex] using
          (Subgroup.FiniteIndex.index_ne_zero (H := H.subgroupOf L))
      exact_mod_cast hrel
    have hχ_one : χ 1 = (H.relIndex L : ℂ) * (m : ℂ) := by
      simpa [Section1.degree_apply] using hdeg
    have hχ_div : χ 1 / (H.relIndex L : ℂ) = (m : ℂ) := by
      rw [hχ_one]
      field_simp [heC]
    rw [show Section1.scalarProduct G (theorem_7_8_beta L H τ ζ) (ν χ) = b by rfl]
    rw [hb, hχ_div]

private theorem theorem_7_8_weightedSum_principal_scalar
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T S : Finset (Section1.ClassFunction L)}
    {τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {ζ : Section1.ClassFunction L}
    (h76 : hypothesis_7_6_statement A L H K T)
    (hτ : agreesWithDadeTransform A L K τ)
    (h78 : theorem_7_8_hypothesis L H T S τ ν ζ) :
    Section1.scalarProduct G
      (theorem_7_8_weightedSum S ν (H.relIndex L))
      (Section1.principalCharacter G) = 0 := by
  classical
  let e : ℕ := H.relIndex L
  change Section1.scalarProduct G (theorem_7_8_weightedSum S ν e)
    (Section1.principalCharacter G) = 0
  have hprincipal := theorem_7_8_principal_orthogonal_to_image h76 hτ h78
  have hsum :
      theorem_7_8_weightedSum S ν e =
        fun g =>
          ∑ X : S,
            ((((X : Section1.ClassFunction L) 1) /
              ((e : ℂ) * (Section5.cfNormSq (X : Section1.ClassFunction L) : ℂ))) •
                ν (X : Section1.ClassFunction L)) g := by
    ext g
    simp only [theorem_7_8_weightedSum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact (Finset.sum_attach S
      (fun x : Section1.ClassFunction L =>
        x 1 / ((e : ℂ) * (Section5.cfNormSq x : ℂ)) * ν x g)).symm
  calc
    Section1.scalarProduct G (theorem_7_8_weightedSum S ν e)
        (Section1.principalCharacter G) =
        ∑ X : S,
          Section1.scalarProduct G
            ((((X : Section1.ClassFunction L) 1) /
              ((e : ℂ) * (Section5.cfNormSq (X : Section1.ClassFunction L) : ℂ))) •
                ν (X : Section1.ClassFunction L))
            (Section1.principalCharacter G) := by
          rw [hsum, Section1.scalarProduct_fintype_sum_left]
    _ = ∑ X : S, 0 := by
          refine Finset.sum_congr rfl ?_
          intro X _hX
          have hleft :
              Section1.scalarProduct G (Section1.principalCharacter G)
                (ν (X : Section1.ClassFunction L)) = 0 :=
            hprincipal (X : Section1.ClassFunction L) X.2
          have hright :
              Section1.scalarProduct G (ν (X : Section1.ClassFunction L))
                (Section1.principalCharacter G) = 0 := by
            have hswap := Section1.scalarProduct_star_swap
              (G := G) (Section1.principalCharacter G) (ν (X : Section1.ClassFunction L))
            have hstarzero :
                star (Section1.scalarProduct G (ν (X : Section1.ClassFunction L))
                  (Section1.principalCharacter G)) = 0 := by
              simpa [hleft] using hswap
            simpa using congrArg star hstarzero
          rw [Section1.scalarProduct_smul_left, hright, mul_zero]
    _ = 0 := by simp

public theorem theorem_7_8_a
    {G : Type u} [Group G] [Finite G]
    (A : Set G) (L H : Subgroup G)
    (K : G → Subgroup G)
    (T : Finset (Section1.ClassFunction L))
    (S : Finset (Section1.ClassFunction L))
    (τ ν : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (ζ : Section1.ClassFunction L) :
    theorem_7_8_a_statement A L H K T S τ ν ζ := by
  rw [theorem_7_8_a_statement]
  intro h76 hτ h78
  classical
  have h78orig := h78
  rcases h78 with ⟨_hHL, _hST, _hpunctured, _hcoherent, _hν, hζS, _hζ, hdegζ⟩
  rcases theorem_7_8_beta_zeta_coeff_int h76 hτ h78orig with ⟨a, hβζ⟩
  let β : Section1.ClassFunction G := theorem_7_8_beta L H τ ζ
  let W : Section1.ClassFunction G := theorem_7_8_weightedSum S ν (H.relIndex L)
  let p : Section1.ClassFunction G := Section1.principalCharacter G
  let r : Section1.ClassFunction G := β - (p - ν ζ + (a : ℂ) • W)
  refine ⟨a, r, ?_⟩
  have hprincipal : orthogonalToImage S ν p :=
    theorem_7_8_principal_orthogonal_to_image h76 hτ h78orig
  have heC : (H.relIndex L : ℂ) ≠ 0 := by
    haveI : (H.subgroupOf L).FiniteIndex := inferInstance
    have hrel : H.relIndex L ≠ 0 := by
      simpa [Subgroup.relIndex] using
        (Subgroup.FiniteIndex.index_ne_zero (H := H.subgroupOf L))
    exact_mod_cast hrel
  have hζ_one_div : ζ 1 / (H.relIndex L : ℂ) = 1 := by
    have hζ_one : ζ 1 = (H.relIndex L : ℂ) := by
      simpa [Section1.degree_apply] using hdegζ
    rw [hζ_one]
    field_simp [heC]
  dsimp [theorem_7_8_decompositionData]
  constructor
  · exact hprincipal
  constructor
  · intro χ hχS
    have hpχ : Section1.scalarProduct G p (ν χ) = 0 :=
      hprincipal χ hχS
    have hβχ :=
      theorem_7_8_beta_scalarProduct_of_mem h76 hτ h78orig hβζ hχS
    have hWχ :
        Section1.scalarProduct G W (ν χ) =
          χ 1 / (H.relIndex L : ℂ) := by
      simpa [W] using theorem_7_8_weightedSum_scalarProduct_of_mem h76 h78orig hχS
    dsimp [r, β, W, p]
    rw [scalarProduct_sub_left_pf78, Section1.scalarProduct_add_left,
      scalarProduct_sub_left_pf78, Section1.scalarProduct_smul_left]
    by_cases hχζ : χ = ζ
    · have hνζχ : Section1.scalarProduct G (ν ζ) (ν χ) = 1 := by
        rw [hχζ]
        exact theorem_7_8_nu_zeta_norm h78orig
      have hβζ' :
          Section1.scalarProduct G (theorem_7_8_beta L H τ ζ) (ν χ) =
            (a : ℂ) - 1 := by
        simpa [hχζ] using hβχ
      have hWχ' : Section1.scalarProduct G W (ν χ) = 1 := by
        rw [hWχ, hχζ, hζ_one_div]
      rw [hβζ', hpχ, hνζχ, hWχ']
      ring
    · have hβχ' :
          Section1.scalarProduct G (theorem_7_8_beta L H τ ζ) (ν χ) =
            (a : ℂ) * (χ 1 / (H.relIndex L : ℂ)) := by
        simpa [hχζ] using hβχ
      have hζχL : Section1.scalarProduct L ζ χ = 0 :=
        theorem_7_8_scalarProduct_distinct_members h76 h78orig hζS hχS
          (by intro h; exact hχζ h.symm)
      have hνζχ : Section1.scalarProduct G (ν ζ) (ν χ) = 0 := by
        rw [theorem_7_8_nu_scalarProduct_of_mem h78orig hζS hχS, hζχL]
      rw [hβχ', hpχ, hνζχ, hWχ]
      ring
  constructor
  · have hβp :
        Section1.scalarProduct G β p = 1 := by
      simpa [β, p] using theorem_7_8_beta_principal_scalar h76 hτ h78orig
    have hpp : Section1.scalarProduct G p p = 1 := by
      simp [p, Section1.scalarProduct]
    have hpζ : Section1.scalarProduct G p (ν ζ) = 0 :=
      hprincipal ζ hζS
    have hζp : Section1.scalarProduct G (ν ζ) p = 0 := by
      have hswap := Section1.scalarProduct_star_swap (G := G) p (ν ζ)
      have hstarzero :
          star (Section1.scalarProduct G (ν ζ) p) = 0 := by
        simpa [hpζ] using hswap
      simpa using congrArg star hstarzero
    have hWp : Section1.scalarProduct G W p = 0 := by
      simpa [W, p] using theorem_7_8_weightedSum_principal_scalar h76 hτ h78orig
    dsimp [r]
    rw [scalarProduct_sub_left_pf78, Section1.scalarProduct_add_left,
      scalarProduct_sub_left_pf78, Section1.scalarProduct_smul_left]
    rw [hβp, hpp, hζp, hWp]
    ring
  · ext g
    dsimp [r, β, W, p]
    simp

end CFSG.Section7
