module

import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_7_11
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

@[expose] public def theorem_7_7_statement
    {G : Type u} [Group G] [Finite G]
    {n : ℕ}
    (A : Set G) (L H : Subgroup G)
    (K : G → Subgroup G)
    (T : Finset (Section1.ClassFunction L))
    (ζ : Fin (n + 1) → Section1.ClassFunction L)
    (d : Fin n → ℂ)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (χ : Section1.ClassFunction G) (c : Fin n → ℂ) : Prop :=
  hypothesis_7_6_statement A L H K T →
    agreesWithDadeTransform A L K τ →
      inducedFamilyEnumeration T ζ d →
        projectionBasisPackage A L H ζ d →
        Section1.IsClassFunction χ →
          projectionCoefficientPackage ζ d τ χ c →
            (∀ x : L, (x : G) ∈ A →
              dadeProjection L K χ x =
                ∑ i : Fin n,
                  (star (c i) / (Section5.cfNormSq (ζ (Fin.succ i)) : ℂ)) *
                    ζ (Fin.succ i) x) ∧
              (Section5.cfNormSq (dadeProjectionOn A L K χ) : ℂ) =
                ∑ i : Fin n, ∑ j : Fin n,
                  (star (c i) * c j) /
                    ((Section5.cfNormSq (ζ (Fin.succ i)) : ℂ) *
                      (Section5.cfNormSq (ζ (Fin.succ j)) : ℂ)) *
                    (Section1.scalarProduct L (ζ (Fin.succ i)) (ζ (Fin.succ j)) -
                      (ζ (Fin.succ i) 1 * ζ (Fin.succ j) 1) /
                        ((H.relIndex L : ℂ) * (Nat.card H : ℂ)))

/-- Peterfalvi `(7.8)(a)`. -/


private theorem scalarProduct_add_right_pf77
    {G : Type*} [Group G] [Finite G]
    (φ ψ η : Section1.ClassFunction G) :
    Section1.scalarProduct G φ (ψ + η) =
      Section1.scalarProduct G φ ψ + Section1.scalarProduct G φ η := by
  simp [Section1.scalarProduct, mul_add, Finset.sum_add_distrib]

private theorem scalarProduct_sub_right_pf77
    {G : Type*} [Group G] [Finite G]
    (φ ψ η : Section1.ClassFunction G) :
    Section1.scalarProduct G φ (ψ - η) =
      Section1.scalarProduct G φ ψ - Section1.scalarProduct G φ η := by
  rw [sub_eq_add_neg, scalarProduct_add_right_pf77]
  have hneg : Section1.scalarProduct G φ (-η) = -Section1.scalarProduct G φ η := by
    simp [Section1.scalarProduct, Finset.sum_neg_distrib]
  rw [hneg]
  ring

private theorem dadeProjectionOn_CFon_pf77
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h : Section2.Hypothesis2 A L H) (hAL : ∀ a ∈ A, a ∈ L)
    (χ : Section1.ClassFunction G) (hχclass : Section1.IsClassFunction χ) :
    Section2.CFOn L A (dadeProjectionOn A L H χ) := by
  constructor
  · intro x a
    have hxAiff : ((x * a * x⁻¹ : L) : G) ∈ A ↔ (a : G) ∈ A := by
      have hxAiff' := h.L_le_normalizer x.2 (a : G)
      change (↑x * ↑a * (↑x)⁻¹ : G) ∈ A ↔ (↑a : G) ∈ A at hxAiff'
      exact hxAiff'
    by_cases ha : (a : G) ∈ A
    · have hxa : ((x * a * x⁻¹ : L) : G) ∈ A := hxAiff.2 ha
      have hxa' : (↑x * ↑a * (↑x)⁻¹ : G) ∈ A := by
        simpa using hxa
      simp [dadeProjectionOn, hxa', ha, dadeProjection]
      exact Section2.dadeAveragingFunction_isClassFunction_on_A A L H h hAL χ hχclass a ha x
    · have hxa : ((x * a * x⁻¹ : L) : G) ∉ A := fun hmem => ha (hxAiff.1 hmem)
      have hxa' : (↑x * ↑a * (↑x)⁻¹ : G) ∉ A := by
        simpa using hxa
      simp [dadeProjectionOn, hxa', ha]
  · intro a ha
    simp [dadeProjectionOn, ha]

public theorem inducedFamilyEnumeration_induced_irreducible_pf77
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T : Finset (Section1.ClassFunction L)} {n : ℕ}
    {ζ : Fin (n + 1) → Section1.ClassFunction L} {d : Fin n → ℂ}
    (h76 : hypothesis_7_6_statement A L H K T)
    (henum : inducedFamilyEnumeration T ζ d)
    (i : Fin (n + 1)) :
    ∃ θ : Section1.ClassFunction (H.subgroupOf L),
      Section1.IsIrreducibleCharacterOnGroup θ ∧
        ζ i = Section1.inducedCF (H.subgroupOf L) θ := by
  rcases h76 with ⟨_hHL, _hHnormal, _h71, _hA, hT⟩
  rcases henum with ⟨henum_mem, _hζinj, _hdeg⟩
  exact (hT (ζ i)).mp ((henum_mem (ζ i)).2 ⟨i, rfl⟩)

private theorem inducedFamilyEnumeration_classFunction_pf77
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T : Finset (Section1.ClassFunction L)} {n : ℕ}
    {ζ : Fin (n + 1) → Section1.ClassFunction L} {d : Fin n → ℂ}
    (h76 : hypothesis_7_6_statement A L H K T)
    (henum : inducedFamilyEnumeration T ζ d)
    (i : Fin (n + 1)) :
    Section1.IsClassFunction (ζ i) := by
  rcases inducedFamilyEnumeration_induced_irreducible_pf77
      (A := A) (L := L) (H := H) (K := K) (T := T)
      (ζ := ζ) (d := d) h76 henum i with
    ⟨θ, _hθ, hζ⟩
  rw [hζ]
  exact Section1.inducedCF_isClassFunction (H.subgroupOf L) θ

public theorem projectionBasisPackage_CFon_of_inducedFamilyEnumeration_pf77
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T : Finset (Section1.ClassFunction L)} {n : ℕ}
    {ζ : Fin (n + 1) → Section1.ClassFunction L} {d : Fin n → ℂ}
    (h76 : hypothesis_7_6_statement A L H K T)
    (henum : inducedFamilyEnumeration T ζ d) :
    ∀ i : Fin n,
      Section2.CFOn L A (ζ (Fin.succ i) - d i • ζ 0) := by
  classical
  intro i
  have h76orig := h76
  have henumorig := henum
  rcases h76 with ⟨_hHL, hHnormal, _h71, hAeq, _hT⟩
  haveI : (H.subgroupOf L).Normal := hHnormal
  rcases henum with ⟨_henum_mem, _hζinj, hdeg⟩
  rcases inducedFamilyEnumeration_induced_irreducible_pf77
      (A := A) (L := L) (H := H) (K := K) (T := T)
      (ζ := ζ) (d := d) h76orig henumorig (Fin.succ i) with
    ⟨θi, _hθi, hζi⟩
  rcases inducedFamilyEnumeration_induced_irreducible_pf77
      (A := A) (L := L) (H := H) (K := K) (T := T)
      (ζ := ζ) (d := d) h76orig henumorig 0 with
    ⟨θ0, _hθ0, hζ0⟩
  have hζiClass : Section1.IsClassFunction (ζ (Fin.succ i)) := by
    rw [hζi]
    exact Section1.inducedCF_isClassFunction (H.subgroupOf L) θi
  have hζ0Class : Section1.IsClassFunction (ζ 0) := by
    rw [hζ0]
    exact Section1.inducedCF_isClassFunction (H.subgroupOf L) θ0
  constructor
  · intro x g
    simp [Pi.sub_apply, hζiClass x g, hζ0Class x g]
  · intro l hlA
    have hpsi_one :
        (ζ (Fin.succ i) - d i • ζ 0) (1 : L) = 0 := by
      have hval : ζ (Fin.succ i) (1 : L) = d i * ζ 0 (1 : L) := by
        simpa [Section1.degree_apply] using hdeg i
      simp [Pi.sub_apply, smul_eq_mul, hval]
    by_cases hlH : (l : G) ∈ H
    · have hl_one : l = 1 := by
        by_contra hl_ne
        apply hlA
        rw [hAeq]
        exact ⟨hlH, fun hG => hl_ne (Subtype.ext hG)⟩
      simpa [hl_one] using hpsi_one
    · have hlHsub : l ∉ H.subgroupOf L := by
        intro hl
        exact hlH hl
      have hζi_zero : ζ (Fin.succ i) l = 0 := by
        rw [hζi]
        exact Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal
          (H.subgroupOf L) θi hlHsub
      have hζ0_zero : ζ 0 l = 0 := by
        rw [hζ0]
        exact Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal
          (H.subgroupOf L) θ0 hlHsub
      simp [Pi.sub_apply, hζi_zero, hζ0_zero]

private theorem inducedFamilyEnumeration_scalarProduct_ne_zero_pf77
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T : Finset (Section1.ClassFunction L)} {n : ℕ}
    {ζ : Fin (n + 1) → Section1.ClassFunction L} {d : Fin n → ℂ}
    (h76 : hypothesis_7_6_statement A L H K T)
    (henum : inducedFamilyEnumeration T ζ d)
    (i : Fin (n + 1)) :
    Section1.scalarProduct L (ζ i) (ζ i) ≠ 0 := by
  have h76orig := h76
  rcases h76 with ⟨_hHL, hHnormal, _h71, _hA, _hT⟩
  haveI : (H.subgroupOf L).Normal := hHnormal
  rcases inducedFamilyEnumeration_induced_irreducible_pf77
      (A := A) (L := L) (H := H) (K := K) (T := T)
      (ζ := ζ) (d := d) h76orig henum i with
    ⟨θ, hθ, hζ⟩
  rcases hθ with ⟨m, ρ, hρirr, hθeq⟩
  have hself := Section1.proposition_1_5_b_rep_orbit_relIndex_canonical
    (H.subgroupOf L) ρ hρirr
  have hrel_ne :
      ((H.subgroupOf L).relIndex
        (Section1.inertiaSubgroup (H.subgroupOf L) ρ.character) : ℂ) ≠ 0 := by
    have hrel :
        (H.subgroupOf L).relIndex
          (Section1.inertiaSubgroup (H.subgroupOf L) ρ.character) ≠ 0 := by
      haveI :
          ((H.subgroupOf L).subgroupOf
            (Section1.inertiaSubgroup (H.subgroupOf L) ρ.character)).FiniteIndex :=
        inferInstance
      simpa [Subgroup.relIndex] using
        (Subgroup.FiniteIndex.index_ne_zero
          (H := (H.subgroupOf L).subgroupOf
            (Section1.inertiaSubgroup (H.subgroupOf L) ρ.character)))
    exact_mod_cast hrel
  rw [hζ, hθeq, hself]
  exact hrel_ne

private theorem inducedFamilyEnumeration_scalarProduct_self_eq_cfNormSq_pf77
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T : Finset (Section1.ClassFunction L)} {n : ℕ}
    {ζ : Fin (n + 1) → Section1.ClassFunction L} {d : Fin n → ℂ}
    (h76 : hypothesis_7_6_statement A L H K T)
    (henum : inducedFamilyEnumeration T ζ d)
    (i : Fin (n + 1)) :
    Section1.scalarProduct L (ζ i) (ζ i) =
      (Section5.cfNormSq (ζ i) : ℂ) := by
  rcases inducedFamilyEnumeration_induced_irreducible_pf77
      (A := A) (L := L) (H := H) (K := K) (T := T)
      (ζ := ζ) (d := d) h76 henum i with
    ⟨θ, hθ, hζ⟩
  have hθchar : Section1.IsCharacter θ :=
    Section1.isCharacter_of_isIrreducibleCharacterOnGroup hθ
  have hζchar : Section1.IsCharacter (ζ i) := by
    rw [hζ]
    exact Section1.isCharacter_inducedCF_of_isCharacter
      (H.subgroupOf L) θ hθchar
  exact Section5.scalarProduct_self_eq_cfNormSq_of_character hζchar

public theorem projectionBasisPackage_norm_ne_of_inducedFamilyEnumeration_pf77
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T : Finset (Section1.ClassFunction L)} {n : ℕ}
    {ζ : Fin (n + 1) → Section1.ClassFunction L} {d : Fin n → ℂ}
    (h76 : hypothesis_7_6_statement A L H K T)
    (henum : inducedFamilyEnumeration T ζ d) :
    ∀ i : Fin n,
      (Section5.cfNormSq (ζ (Fin.succ i)) : ℂ) ≠ 0 := by
  intro i hzero
  have hself :=
    inducedFamilyEnumeration_scalarProduct_self_eq_cfNormSq_pf77
      (A := A) (L := L) (H := H) (K := K) (T := T)
      (ζ := ζ) (d := d) h76 henum (Fin.succ i)
  have hsp_zero :
      Section1.scalarProduct L (ζ (Fin.succ i)) (ζ (Fin.succ i)) = 0 := by
    simpa [hzero] using hself
  exact inducedFamilyEnumeration_scalarProduct_ne_zero_pf77
    (A := A) (L := L) (H := H) (K := K) (T := T)
    (ζ := ζ) (d := d) h76 henum (Fin.succ i) hsp_zero

private theorem inducedFamilyEnumeration_scalarProduct_eq_zero_of_ne_pf77
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T : Finset (Section1.ClassFunction L)} {n : ℕ}
    {ζ : Fin (n + 1) → Section1.ClassFunction L} {d : Fin n → ℂ}
    (h76 : hypothesis_7_6_statement A L H K T)
    (henum : inducedFamilyEnumeration T ζ d)
    {i j : Fin (n + 1)} (hij : i ≠ j) :
    Section1.scalarProduct L (ζ i) (ζ j) = 0 := by
  have h76orig := h76
  have henumorig := henum
  rcases h76 with ⟨_hHL, hHnormal, _h71, _hA, _hT⟩
  haveI : (H.subgroupOf L).Normal := hHnormal
  rcases henum with ⟨henum_mem, hζinj, hdeg⟩
  rcases inducedFamilyEnumeration_induced_irreducible_pf77
      (A := A) (L := L) (H := H) (K := K) (T := T)
      (ζ := ζ) (d := d) h76orig henumorig i with
    ⟨θi, hθi, hζi⟩
  rcases inducedFamilyEnumeration_induced_irreducible_pf77
      (A := A) (L := L) (H := H) (K := K) (T := T)
      (ζ := ζ) (d := d) h76orig henumorig j with
    ⟨θj, hθj, hζj⟩
  rcases hθi with ⟨mi, ρi, hρi, hθi_eq⟩
  rcases hθj with ⟨mj, ρj, hρj, hθj_eq⟩
  have hnotConj :
      ∀ k : Section1.conjugateOrbitIndex (H.subgroupOf L) ρj.character,
        θi ≠ Section1.conjugateOrbitConj (H.subgroupOf L) ρj.character k := by
    intro k hk
    apply hij
    apply hζinj
    calc
      ζ i = Section1.inducedCF (H.subgroupOf L) θi := hζi
      _ = Section1.inducedCF (H.subgroupOf L) ρj.character := by
          exact Section1.proposition_1_5_c_conjugate_orbit_canonical
            (H.subgroupOf L) ρj θi k hk
      _ = Section1.inducedCF (H.subgroupOf L) θj := by rw [hθj_eq]
      _ = ζ j := hζj.symm
  calc
    Section1.scalarProduct L (ζ i) (ζ j) =
        Section1.scalarProduct L
          (Section1.inducedCF (H.subgroupOf L) θi)
          (Section1.inducedCF (H.subgroupOf L) ρj.character) := by
            rw [hζi, hζj, hθj_eq]
    _ = 0 := by
        exact Section1.proposition_1_5_c_nonconjugate_rep_orbit_relIndex_canonical
          (H.subgroupOf L) θi ρi ρj hθi_eq hρi hρj hnotConj

public theorem projectionBasisPackage_diagonal_of_inducedFamilyEnumeration_pf77
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T : Finset (Section1.ClassFunction L)} {n : ℕ}
    {ζ : Fin (n + 1) → Section1.ClassFunction L} {d : Fin n → ℂ}
    (h76 : hypothesis_7_6_statement A L H K T)
    (henum : inducedFamilyEnumeration T ζ d) :
    ∀ i j : Fin n,
      Section1.scalarProduct L (ζ (Fin.succ i) - d i • ζ 0)
          (ζ (Fin.succ j)) =
        if i = j then (Section5.cfNormSq (ζ (Fin.succ i)) : ℂ) else 0 := by
  intro i j
  have h0j :
      Section1.scalarProduct L (ζ 0) (ζ (Fin.succ j)) = 0 := by
    apply inducedFamilyEnumeration_scalarProduct_eq_zero_of_ne_pf77
      (A := A) (L := L) (H := H) (K := K) (T := T)
      (ζ := ζ) (d := d) h76 henum
    intro h
    have hval : 0 = j.val + 1 := by
      simpa using congrArg Fin.val h
    omega
  rw [Section5.scalarProduct_sub_left, Section1.scalarProduct_smul_left, h0j,
    mul_zero, sub_zero]
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    exact inducedFamilyEnumeration_scalarProduct_self_eq_cfNormSq_pf77
      (A := A) (L := L) (H := H) (K := K) (T := T)
      (ζ := ζ) (d := d) h76 henum (Fin.succ i)
  · rw [if_neg hij]
    apply inducedFamilyEnumeration_scalarProduct_eq_zero_of_ne_pf77
      (A := A) (L := L) (H := H) (K := K) (T := T)
      (ζ := ζ) (d := d) h76 henum
    intro hsucc
    apply hij
    apply Fin.ext
    have hval : i.val + 1 = j.val + 1 := by
      simpa using congrArg Fin.val hsucc
    omega

private theorem scalarProduct_eq_of_left_supported_and_right_eq_on_pf77
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G}
    (α β γ : Section1.ClassFunction L)
    (hαsupp : ∀ x : L, (x : G) ∉ A → α x = 0)
    (hβγ : ∀ x : L, (x : G) ∈ A → β x = γ x) :
    Section1.scalarProduct L α β = Section1.scalarProduct L α γ := by
  classical
  unfold Section1.scalarProduct
  congr 1
  refine Finset.sum_congr rfl ?_
  intro x _hx
  by_cases hxA : (x : G) ∈ A
  · rw [hβγ x hxA]
  · rw [hαsupp x hxA]
    simp

private theorem scalarProduct_self_eq_zero_of_mem_span_left_pf77
    {G : Type u} [Group G] [Finite G]
    {n : ℕ} {L : Subgroup G}
    {ψ : Fin n → Section1.ClassFunction L} {φ : Section1.ClassFunction L}
    (hφspan : φ ∈ Submodule.span ℂ (Set.range ψ))
    (horth : ∀ i : Fin n, Section1.scalarProduct L (ψ i) φ = 0) :
    Section1.scalarProduct L φ φ = 0 := by
  classical
  refine Submodule.span_induction
    (p := fun η : Section1.ClassFunction L =>
      fun _ : η ∈ Submodule.span ℂ (Set.range ψ) =>
      Section1.scalarProduct L η φ = 0)
    ?hgen ?hzero ?hadd ?hsmul hφspan
  · intro η hη
    rcases hη with ⟨i, rfl⟩
    exact horth i
  · simp [Section1.scalarProduct]
  · intro η θ _hηmem _hθmem hη hθ
    rw [Section1.scalarProduct_add_left, hη, hθ, add_zero]
  · intro a η _hηmem hη
    rw [Section1.scalarProduct_smul_left, hη, mul_zero]

private theorem classFunction_eq_weighted_sum_irreducibles_pf77
    {G : Type u} [Group G] [Finite G]
    (φ : Section1.ClassFunction G) (hφ : Section1.IsClassFunction φ) :
    ∃ ι : Type, ∃ _ : Fintype ι,
      ∃ a : ι → ℂ, ∃ ψ : ι → Section1.ClassFunction G,
        (∀ i : ι, Section1.IsIrreducibleCharacterOnGroup (ψ i)) ∧
          φ = Section1.weightedFamilySum a ψ := by
  classical
  rcases Theory.Character.irreducible_characters_form_basis (G := G) with
    ⟨ι, hι, χ, hχ, b, hb⟩
  letI : Fintype ι := hι
  let a : ι → ℂ := fun i => b.repr (Section1.toConjClassFunction φ hφ) i
  let ψ : ι → Section1.ClassFunction G :=
    fun i => Section1.ofConjClassFunction (χ i)
  refine ⟨ι, hι, a, ψ, ?_, ?_⟩
  · intro i
    exact Section1.isIrreducibleCharacterOnGroup_of_isBookIrreducibleCharacter
      (ψ i)
      (Section1.isBookIrreducibleCharacter_of_representation_irreducible
        (χ i) (hχ.1 i))
  · have hsumφ :
        Section1.toConjClassFunction φ hφ = ∑ i : ι, a i • χ i := by
      calc
        Section1.toConjClassFunction φ hφ =
            ∑ i : ι, b.repr (Section1.toConjClassFunction φ hφ) i • b i := by
              rw [Module.Basis.sum_repr]
        _ = ∑ i : ι, a i • χ i := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              rw [hb i]
    ext g
    have hg := congrFun hsumφ (ConjClasses.mk g)
    have hg' : φ g = ∑ i : ι, a i * ψ i g := by
      simpa [ψ, a, Section1.toConjClassFunction_apply,
        Section1.ofConjClassFunction] using hg
    have hsum_eq :
        (∑ i : ι, a i * ψ i g) = Section1.weightedFamilySum a ψ g := by
      unfold Section1.weightedFamilySum
      apply Finset.sum_congr
      · ext i
        simp
      · intro i _hi
        rfl
    exact hg'.trans hsum_eq

private theorem weightedFamilySum_mem_span_of_mem_pf77
    {G ι : Type*} [Group G] [Fintype ι]
    {S : Set (Section1.ClassFunction G)}
    (a : ι → ℂ) (ψ : ι → Section1.ClassFunction G)
    (hψ : ∀ i : ι, ψ i ∈ Submodule.span ℂ S) :
    Section1.weightedFamilySum a ψ ∈ Submodule.span ℂ S := by
  classical
  haveI : Finite ι := Finite.of_fintype ι
  have hsum :
      Section1.weightedFamilySum a ψ =
        @Finset.sum ι (Section1.ClassFunction G) _ (@Finset.univ ι (Fintype.ofFinite ι))
          (fun i => a i • ψ i) := by
    ext g
    unfold Section1.weightedFamilySum
    rw [Finset.sum_apply]
    rfl
  rw [hsum]
  exact Submodule.sum_mem (Submodule.span ℂ S) (by
    intro i _hi
    exact Submodule.smul_mem _ (a i) (hψ i))

private theorem induced_irreducible_mem_span_zeta_pf77
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T : Finset (Section1.ClassFunction L)} {n : ℕ}
    {ζ : Fin (n + 1) → Section1.ClassFunction L} {d : Fin n → ℂ}
    (h76 : hypothesis_7_6_statement A L H K T)
    (henum : inducedFamilyEnumeration T ζ d)
    {θ : Section1.ClassFunction (H.subgroupOf L)}
    (hθ : Section1.IsIrreducibleCharacterOnGroup θ) :
    Section1.inducedCF (H.subgroupOf L) θ ∈
      Submodule.span ℂ (Set.range ζ) := by
  rcases h76 with ⟨_hHL, _hHnormal, _h71, _hAeq, hT⟩
  rcases henum with ⟨henum_mem, _hζinj, _hdeg⟩
  have hmemT : Section1.inducedCF (H.subgroupOf L) θ ∈ T := by
    exact (hT (Section1.inducedCF (H.subgroupOf L) θ)).2 ⟨θ, hθ, rfl⟩
  rcases (henum_mem (Section1.inducedCF (H.subgroupOf L) θ)).1 hmemT with
    ⟨i, hi⟩
  rw [hi]
  exact Submodule.subset_span ⟨i, rfl⟩

private theorem induced_restriction_mem_span_zeta_of_CFon_pf77
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T : Finset (Section1.ClassFunction L)} {n : ℕ}
    {ζ : Fin (n + 1) → Section1.ClassFunction L} {d : Fin n → ℂ}
    (h76 : hypothesis_7_6_statement A L H K T)
    (henum : inducedFamilyEnumeration T ζ d)
    {φ : Section1.ClassFunction L} (hφ : Section2.CFOn L A φ) :
    Section1.inducedCF (H.subgroupOf L)
        (Section1.subgroupRestriction (H.subgroupOf L) φ) ∈
      Submodule.span ℂ (Set.range ζ) := by
  classical
  have hres_class : Section1.IsClassFunction
      (Section1.subgroupRestriction (H.subgroupOf L) φ) :=
    Section1.subgroupRestriction_isClassFunction_of_isClassFunction
      (H.subgroupOf L) φ hφ.1
  rcases classFunction_eq_weighted_sum_irreducibles_pf77
      (Section1.subgroupRestriction (H.subgroupOf L) φ) hres_class with
    ⟨ι, hι, a, θ, hθirr, hres_eq⟩
  letI : Fintype ι := hι
  have hind_eq :
      Section1.inducedCF (H.subgroupOf L)
          (Section1.subgroupRestriction (H.subgroupOf L) φ) =
        Section1.weightedFamilySum a
          (fun i : ι => Section1.inducedCF (H.subgroupOf L) (θ i)) := by
    rw [hres_eq]
    exact Section1.inducedCF_weightedFamilySum (H.subgroupOf L) a θ
  rw [hind_eq]
  exact weightedFamilySum_mem_span_of_mem_pf77 a
    (fun i : ι => Section1.inducedCF (H.subgroupOf L) (θ i)) (by
      intro i
      exact induced_irreducible_mem_span_zeta_pf77
        (A := A) (L := L) (H := H) (K := K) (T := T)
        (ζ := ζ) (d := d) h76 henum (hθirr i))


private theorem mem_span_psi_of_mem_span_zeta_and_value_one_zero_pf77
    {G : Type u} [Group G] [Finite G]
    {n : ℕ} {L : Subgroup G}
    {ζ : Fin (n + 1) → Section1.ClassFunction L} {d : Fin n → ℂ}
    {φ : Section1.ClassFunction L}
    (hdeg : ∀ i : Fin n,
      Section1.degree (ζ (Fin.succ i)) = d i * Section1.degree (ζ 0))
    (hζ0_ne : ζ 0 (1 : L) ≠ 0)
    (hφspan : φ ∈ Submodule.span ℂ (Set.range ζ))
    (hφone : φ (1 : L) = 0) :
    φ ∈ Submodule.span ℂ
      (Set.range fun i : Fin n => ζ (Fin.succ i) - d i • ζ 0) := by
  classical
  rcases (Submodule.mem_span_range_iff_exists_fun ℂ).mp hφspan with ⟨a, ha⟩
  have hcoeff0 : a 0 = -∑ i : Fin n, a (Fin.succ i) * d i := by
    have hval := congrFun ha (1 : L)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at hval
    rw [Fin.sum_univ_succ] at hval
    rw [hφone] at hval
    have hfactor :
        (a 0 + ∑ i : Fin n, a (Fin.succ i) * d i) * ζ 0 (1 : L) = 0 := by
      calc
        (a 0 + ∑ i : Fin n, a (Fin.succ i) * d i) * ζ 0 (1 : L)
            = a 0 * ζ 0 (1 : L) +
                ∑ i : Fin n, (a (Fin.succ i) * d i) * ζ 0 (1 : L) := by
                rw [add_mul, Finset.sum_mul]
        _ = a 0 * ζ 0 (1 : L) +
              ∑ i : Fin n, a (Fin.succ i) * (d i * ζ 0 (1 : L)) := by
                simp [mul_assoc]
        _ = a 0 * ζ 0 (1 : L) +
              ∑ i : Fin n, a (Fin.succ i) * ζ (Fin.succ i) (1 : L) := by
                refine congrArg (fun z => a 0 * ζ 0 (1 : L) + z) ?_
                refine Finset.sum_congr rfl ?_
                intro i _hi
                rw [show ζ (Fin.succ i) (1 : L) = d i * ζ 0 (1 : L) by
                  simpa [Section1.degree_apply] using hdeg i]
        _ = 0 := hval
    have hsum_zero : a 0 + ∑ i : Fin n, a (Fin.succ i) * d i = 0 :=
      (mul_eq_zero.mp hfactor).resolve_right hζ0_ne
    exact eq_neg_of_add_eq_zero_left hsum_zero
  have hφeq_psi :
      φ = ∑ i : Fin n, a (Fin.succ i) • (ζ (Fin.succ i) - d i • ζ 0) := by
    rw [← ha]
    ext x
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [Fin.sum_univ_succ]
    rw [hcoeff0]
    calc
      (-∑ i : Fin n, a (Fin.succ i) * d i) * ζ 0 x +
          ∑ i : Fin n, a (Fin.succ i) * ζ (Fin.succ i) x
          = ∑ i : Fin n,
              (a (Fin.succ i) * ζ (Fin.succ i) x -
                (a (Fin.succ i) * d i) * ζ 0 x) := by
              rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
              simp
              ring
      _ = ∑ i : Fin n,
            a (Fin.succ i) * (ζ (Fin.succ i) x - d i * ζ 0 x) := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              ring
  rw [hφeq_psi]
  exact Submodule.sum_mem
    (Submodule.span ℂ (Set.range fun i : Fin n => ζ (Fin.succ i) - d i • ζ 0)) (by
    intro i _hi
    exact Submodule.smul_mem _ (a (Fin.succ i))
      (Submodule.subset_span ⟨i, rfl⟩))

private theorem inducedFamilyEnumeration_degree_zero_ne_pf77
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T : Finset (Section1.ClassFunction L)} {n : ℕ}
    {ζ : Fin (n + 1) → Section1.ClassFunction L} {d : Fin n → ℂ}
    (h76 : hypothesis_7_6_statement A L H K T)
    (henum : inducedFamilyEnumeration T ζ d) :
    ζ 0 (1 : L) ≠ 0 := by
  rcases inducedFamilyEnumeration_induced_irreducible_pf77
      (A := A) (L := L) (H := H) (K := K) (T := T)
      (ζ := ζ) (d := d) h76 henum 0 with
    ⟨θ, hθ, hζ⟩
  have hθbook : Section1.IsBookIrreducibleCharacter θ :=
    Section1.isBookIrreducibleCharacter_of_isIrreducibleCharacterOnGroup hθ
  have hθdeg_ne : Section1.degree θ ≠ 0 :=
    Section1.degree_ne_zero_of_isBookIrreducibleCharacter θ hθbook
  have hidx_ne : ((H.subgroupOf L).index : ℂ) ≠ 0 := by
    exact_mod_cast (Subgroup.FiniteIndex.index_ne_zero (H := H.subgroupOf L))
  change Section1.degree (ζ 0) ≠ 0
  rw [hζ, Section1.degree_inducedClassFunction]
  exact mul_ne_zero hidx_ne hθdeg_ne

public theorem CFOn_eq_inv_relIndex_smul_induced_restriction_source_bridge_pf77
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T : Finset (Section1.ClassFunction L)}
    (h76 : hypothesis_7_6_statement A L H K T) :
    ∀ φ : Section1.ClassFunction L,
      Section2.CFOn L A φ →
        φ = ((H.relIndex L : ℂ)⁻¹) •
          Section1.inducedCF (H.subgroupOf L)
            (Section1.subgroupRestriction (H.subgroupOf L) φ) := by
  classical
  intro φ hφ
  rcases h76 with ⟨_hHL, hHnormal, _h71, hAeq, _hT⟩
  haveI : (H.subgroupOf L).Normal := hHnormal
  have hrel_ne_nat : H.relIndex L ≠ 0 := by
    simpa [Subgroup.relIndex] using
      (Subgroup.FiniteIndex.index_ne_zero (H := H.subgroupOf L))
  have hrel_ne : (H.relIndex L : ℂ) ≠ 0 := by
    exact_mod_cast hrel_ne_nat
  have hcoef :
      (Nat.card (H.subgroupOf L) : ℂ)⁻¹ * (Nat.card L : ℂ) =
        (H.relIndex L : ℂ) := by
    have hcardH_ne : (Nat.card (H.subgroupOf L) : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.card_pos (α := H.subgroupOf L)).ne'
    have hindex :
        ((H.subgroupOf L).index : ℂ) * Nat.card (H.subgroupOf L) =
          Nat.card L := by
      exact_mod_cast (H.subgroupOf L).index_mul_card
    have hindex' :
        (Nat.card L : ℂ) =
          ((H.subgroupOf L).index : ℂ) * Nat.card (H.subgroupOf L) := by
      simpa [mul_comm] using hindex.symm
    rw [hindex']
    field_simp [hcardH_ne]
    rfl
  letI : Fintype L := Fintype.ofFinite L
  ext y
  by_cases hyH : y ∈ H.subgroupOf L
  · have hsum :
        (∑ x : L,
          if hx : x * y * x⁻¹ ∈ H.subgroupOf L then
            Section1.subgroupRestriction (H.subgroupOf L) φ ⟨x * y * x⁻¹, hx⟩
          else 0) = (Nat.card L : ℂ) * φ y := by
      calc
        (∑ x : L,
          if hx : x * y * x⁻¹ ∈ H.subgroupOf L then
            Section1.subgroupRestriction (H.subgroupOf L) φ ⟨x * y * x⁻¹, hx⟩
          else 0) = ∑ _x : L, φ y := by
            refine Finset.sum_congr rfl ?_
            intro x _hx
            have hxmem : x * y * x⁻¹ ∈ H.subgroupOf L :=
              hHnormal.conj_mem y hyH x
            have hclass : φ (x * y * x⁻¹) = φ y := hφ.1 x y
            simp [Section1.subgroupRestriction, hxmem, hclass]
        _ = (Nat.card L : ℂ) * φ y := by
            simp [Finset.card_univ]
    have hind :
        Section1.inducedCF (H.subgroupOf L)
          (Section1.subgroupRestriction (H.subgroupOf L) φ) y =
          (H.relIndex L : ℂ) * φ y := by
      calc
        Section1.inducedCF (H.subgroupOf L)
          (Section1.subgroupRestriction (H.subgroupOf L) φ) y =
            (Nat.card (H.subgroupOf L) : ℂ)⁻¹ *
              ∑ x : L,
                if hx : x * y * x⁻¹ ∈ H.subgroupOf L then
                  Section1.subgroupRestriction (H.subgroupOf L) φ
                    ⟨x * y * x⁻¹, hx⟩
                else 0 := by
              unfold Section1.inducedCF Section1.inducedClassFunction
              rfl
        _ = ((Nat.card (H.subgroupOf L) : ℂ)⁻¹ * (Nat.card L : ℂ)) *
              φ y := by
              rw [hsum]
              ring
        _ = (H.relIndex L : ℂ) * φ y := by
              rw [hcoef]
    simp [hind, hrel_ne]
  · have hyA_not : (y : G) ∉ A := by
      intro hyA
      apply hyH
      rw [hAeq] at hyA
      exact hyA.1
    have hφy : φ y = 0 := hφ.2 y hyA_not
    have hind0 :
        Section1.inducedCF (H.subgroupOf L)
          (Section1.subgroupRestriction (H.subgroupOf L) φ) y = 0 := by
      exact Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal
        (H.subgroupOf L) (Section1.subgroupRestriction (H.subgroupOf L) φ) hyH
    simp [hφy, hind0]

private theorem projectionBasisPackage_CFon_mem_span_zeta_of_inducedFamilyEnumeration_pf77
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T : Finset (Section1.ClassFunction L)} {n : ℕ}
    {ζ : Fin (n + 1) → Section1.ClassFunction L} {d : Fin n → ℂ}
    (h76 : hypothesis_7_6_statement A L H K T)
    (henum : inducedFamilyEnumeration T ζ d) :
    ∀ φ : Section1.ClassFunction L,
      Section2.CFOn L A φ → φ ∈ Submodule.span ℂ (Set.range ζ) := by
  intro φ hφ
  have hind_span :=
    induced_restriction_mem_span_zeta_of_CFon_pf77
      (A := A) (L := L) (H := H) (K := K) (T := T)
      (ζ := ζ) (d := d) h76 henum hφ
  rw [CFOn_eq_inv_relIndex_smul_induced_restriction_source_bridge_pf77
    (A := A) (L := L) (H := H) (K := K) (T := T) h76 φ hφ]
  exact Submodule.smul_mem _ _ hind_span

public theorem projectionBasisPackage_CFon_mem_span_psi_of_inducedFamilyEnumeration_source_bridge
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T : Finset (Section1.ClassFunction L)} {n : ℕ}
    {ζ : Fin (n + 1) → Section1.ClassFunction L} {d : Fin n → ℂ}
    (h76 : hypothesis_7_6_statement A L H K T)
    (henum : inducedFamilyEnumeration T ζ d) :
    ∀ φ : Section1.ClassFunction L,
      Section2.CFOn L A φ →
        φ ∈ Submodule.span ℂ
          (Set.range fun i : Fin n => ζ (Fin.succ i) - d i • ζ 0) := by
  intro φ hφ
  have h76orig := h76
  have henumorig := henum
  rcases h76 with ⟨_hHL, _hHnormal, _h71, hAeq, _hT⟩
  rcases henum with ⟨_henum_mem, _hζinj, hdeg⟩
  have hφspanζ :
      φ ∈ Submodule.span ℂ (Set.range ζ) :=
    projectionBasisPackage_CFon_mem_span_zeta_of_inducedFamilyEnumeration_pf77
      (A := A) (L := L) (H := H) (K := K) (T := T)
      (ζ := ζ) (d := d) h76orig henumorig φ hφ
  have hφone : φ (1 : L) = 0 := by
    apply hφ.2
    intro h1A
    rw [hAeq] at h1A
    exact h1A.2 (by simp)
  exact mem_span_psi_of_mem_span_zeta_and_value_one_zero_pf77
    hdeg
    (inducedFamilyEnumeration_degree_zero_ne_pf77
      (A := A) (L := L) (H := H) (K := K) (T := T)
      (ζ := ζ) (d := d) h76orig henumorig)
    hφspanζ hφone

public theorem projectionBasisPackage_detection_CFon_of_inducedFamilyEnumeration_source_bridge
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T : Finset (Section1.ClassFunction L)} {n : ℕ}
    {ζ : Fin (n + 1) → Section1.ClassFunction L} {d : Fin n → ℂ}
    (h76 : hypothesis_7_6_statement A L H K T)
    (henum : inducedFamilyEnumeration T ζ d) :
    ∀ φ : Section1.ClassFunction L,
      Section2.CFOn L A φ →
      (∀ i : Fin n,
        Section1.scalarProduct L (ζ (Fin.succ i) - d i • ζ 0) φ = 0) →
        ∀ x : L, (x : G) ∈ A → φ x = 0 := by
  classical
  intro φ hφ horth x _hx
  let ψ : Fin n → Section1.ClassFunction L :=
    fun i => ζ (Fin.succ i) - d i • ζ 0
  have hφspan :
      φ ∈ Submodule.span ℂ (Set.range ψ) := by
    simpa [ψ] using
      projectionBasisPackage_CFon_mem_span_psi_of_inducedFamilyEnumeration_source_bridge
        (A := A) (L := L) (H := H) (K := K) (T := T)
        (ζ := ζ) (d := d) h76 henum φ hφ
  have hself_zero : Section1.scalarProduct L φ φ = 0 :=
    scalarProduct_self_eq_zero_of_mem_span_left_pf77 (ψ := ψ) hφspan (by
      intro i
      simpa [ψ] using horth i)
  have hnorm_zero : Section5.cfNormSq φ = 0 := by
    unfold Section5.cfNormSq
    rw [hself_zero]
    simp
  have hφzero : φ = 0 := Section5.cfNormSq_eq_zero hnorm_zero
  simpa using congrFun hφzero x

public theorem projectionBasisPackage_detection_of_inducedFamilyEnumeration_source_bridge
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T : Finset (Section1.ClassFunction L)} {n : ℕ}
    {ζ : Fin (n + 1) → Section1.ClassFunction L} {d : Fin n → ℂ}
    (h76 : hypothesis_7_6_statement A L H K T)
    (henum : inducedFamilyEnumeration T ζ d) :
    ∀ φ : Section1.ClassFunction L,
      Section1.IsClassFunction φ →
      (∀ i : Fin n,
        Section1.scalarProduct L (ζ (Fin.succ i) - d i • ζ 0) φ = 0) →
        ∀ x : L, (x : G) ∈ A → φ x = 0 := by
  classical
  intro φ hφclass horth x hxA
  have h76orig := h76
  rcases h76 with ⟨hHL, hHnormal, _h71, hAeq, _hT⟩
  have hA_conj :
      ∀ y z : L, ((y * z * y⁻¹ : L) : G) ∈ A ↔ (z : G) ∈ A := by
    intro y z
    rw [hAeq]
    simp only [puncturedSubgroupSet, Set.mem_setOf_eq]
    constructor
    · intro hz
      rcases hz with ⟨hzH, hz_ne⟩
      constructor
      · have hzHsub : (y * z * y⁻¹ : L) ∈ H.subgroupOf L := hzH
        have hback :
            y⁻¹ * (y * z * y⁻¹) * (y⁻¹)⁻¹ ∈ H.subgroupOf L :=
          hHnormal.conj_mem (y * z * y⁻¹ : L) hzHsub y⁻¹
        change z ∈ H.subgroupOf L
        simpa [mul_assoc] using hback
      · intro hz1
        apply hz_ne
        have hz1L : z = 1 := Subtype.ext hz1
        simp [hz1L]
    · intro hz
      rcases hz with ⟨hzH, hz_ne⟩
      constructor
      · have hzHsub : z ∈ H.subgroupOf L := hzH
        exact hHnormal.conj_mem z hzHsub y
      · intro hconj_one
        apply hz_ne
        have hconjL : y * z * y⁻¹ = 1 := Subtype.ext hconj_one
        have hzL : z = 1 := by
          have h := congrArg (fun t : L => y⁻¹ * t * y) hconjL
          simpa [mul_assoc] using h
        simpa using congrArg Subtype.val hzL
  let φA : Section1.ClassFunction L :=
    fun y => if (y : G) ∈ A then φ y else 0
  have hφA_class : Section1.IsClassFunction φA := by
    intro y z
    by_cases hzA : (z : G) ∈ A
    · have hyzA : ((y * z * y⁻¹ : L) : G) ∈ A := (hA_conj y z).2 hzA
      simp only [φA, if_pos hyzA, if_pos hzA]
      exact hφclass y z
    · have hyzA : ((y * z * y⁻¹ : L) : G) ∉ A :=
        fun hmem => hzA ((hA_conj y z).1 hmem)
      simp only [φA, if_neg hyzA, if_neg hzA]
  have hφA_supp : ∀ y : L, (y : G) ∉ A → φA y = 0 := by
    intro y hy
    simp [φA, hy]
  have hφA_on : ∀ y : L, (y : G) ∈ A → φA y = φ y := by
    intro y hy
    simp [φA, hy]
  have horthA :
      ∀ i : Fin n,
        Section1.scalarProduct L (ζ (Fin.succ i) - d i • ζ 0) φA = 0 := by
    intro i
    have hψCF :=
      projectionBasisPackage_CFon_of_inducedFamilyEnumeration_pf77
        (A := A) (L := L) (H := H) (K := K) (T := T)
        (ζ := ζ) (d := d) h76orig henum i
    calc
      Section1.scalarProduct L (ζ (Fin.succ i) - d i • ζ 0) φA =
          Section1.scalarProduct L (ζ (Fin.succ i) - d i • ζ 0) φ := by
            exact scalarProduct_eq_of_left_supported_and_right_eq_on_pf77
              (A := A) (ζ (Fin.succ i) - d i • ζ 0) φA φ
              hψCF.2 hφA_on
      _ = 0 := horth i
  have hzeroA :=
    projectionBasisPackage_detection_CFon_of_inducedFamilyEnumeration_source_bridge
      (A := A) (L := L) (H := H) (K := K) (T := T)
      (ζ := ζ) (d := d) h76orig henum φA ⟨hφA_class, hφA_supp⟩ horthA x hxA
  simpa [φA, hxA] using hzeroA

private theorem scalarProduct_self_eq_cfNormSq_pf77
    {G : Type*} [Group G] [Finite G]
    (φ : Section1.ClassFunction G) :
    Section1.scalarProduct G φ φ = (Section5.cfNormSq φ : ℂ) := by
  unfold Section5.cfNormSq Section1.scalarProduct
  simp [Complex.mul_conj]

private theorem character_value_one_star_pf77
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G} (hχ : Section1.IsCharacter χ) :
    star (χ 1) = χ 1 := by
  rcases hχ with ⟨V, _hadd, _hmod, _hfd, ρ, hχeq⟩
  have hdeg : Section1.degree ρ.character = (Module.finrank ℂ V : ℂ) :=
    Section1.degree_representation_character ρ
  have hone : ρ.character (1 : G) = (Module.finrank ℂ V : ℂ) := by
    exact hdeg
  rw [hχeq, hone]
  simp

private theorem scalarProduct_eq_sub_identity_of_eq_off_identity_pf77
    {L : Type*} [Group L] [Finite L]
    (f approx : Section1.ClassFunction L)
    (hf1 : f 1 = 0)
    (hf_approx : ∀ x : L, x ≠ 1 → f x = approx x) :
    Section1.scalarProduct L f f =
      Section1.scalarProduct L approx approx -
        (Nat.card L : ℂ)⁻¹ * (approx 1 * star (approx 1)) := by
  classical
  unfold Section1.scalarProduct
  have hterm_erase :
      (Finset.univ.erase (1 : L)).sum (fun x => f x * star (f x)) =
        (Finset.univ.erase (1 : L)).sum (fun x => approx x * star (approx x)) := by
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hxne : x ≠ 1 := (Finset.mem_erase.mp hx).1
    rw [hf_approx x hxne]
  have hsplit_f := Finset.sum_erase_add (Finset.univ : Finset L)
    (fun x => f x * star (f x)) (Finset.mem_univ (1 : L))
  have hsplit_a := Finset.sum_erase_add (Finset.univ : Finset L)
    (fun x => approx x * star (approx x)) (Finset.mem_univ (1 : L))
  have hsum_f :
      (∑ x : L, f x * star (f x)) =
        (∑ x : L, approx x * star (approx x)) - approx 1 * star (approx 1) := by
    calc
      (∑ x : L, f x * star (f x)) =
          (Finset.univ.erase (1 : L)).sum (fun x => f x * star (f x)) := by
            rw [← hsplit_f]
            simp [hf1]
      _ = (Finset.univ.erase (1 : L)).sum
            (fun x => approx x * star (approx x)) := hterm_erase
      _ = (∑ x : L, approx x * star (approx x)) -
            approx 1 * star (approx 1) := by
            rw [← hsplit_a]
            ring
  rw [hsum_f]
  ring

private theorem scalarProduct_weighted_sum_self_pf77
    {L : Type*} [Group L] [Finite L]
    {n : ℕ} (b : Fin n → ℂ) (ζ : Fin n → Section1.ClassFunction L) :
    Section1.scalarProduct L (∑ i : Fin n, b i • ζ i)
        (∑ i : Fin n, b i • ζ i) =
      ∑ i : Fin n, ∑ j : Fin n,
        b i * star (b j) * Section1.scalarProduct L (ζ i) (ζ j) := by
  have hsum : (∑ i : Fin n, b i • ζ i) =
      (fun x : L => ∑ i : Fin n, (b i • ζ i) x) := by
    funext x
    simp
  rw [hsum]
  rw [Section1.scalarProduct_fintype_sum_left]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [Section1.scalarProduct_fintype_sum_right]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
  ring

private theorem weighted_sum_identity_term_pf77
    {L : Type*} [Group L] [Finite L]
    {n : ℕ} (b : Fin n → ℂ) (ζ : Fin n → Section1.ClassFunction L)
    (hζone : ∀ j : Fin n, star (ζ j 1) = ζ j 1) :
    ((∑ i : Fin n, b i • ζ i) : Section1.ClassFunction L) 1 *
      star (((∑ i : Fin n, b i • ζ i) : Section1.ClassFunction L) 1) =
      ∑ i : Fin n, ∑ j : Fin n,
        b i * star (b j) * (ζ i 1 * ζ j 1) := by
  have hsum : (∑ i : Fin n, b i • ζ i) =
      (fun x : L => ∑ i : Fin n, (b i • ζ i) x) := by
    funext x
    simp
  have happly' : ((∑ i : Fin n, b i • ζ i) : Section1.ClassFunction L) 1 =
      ∑ i : Fin n, (b i • ζ i) (1 : L) :=
    congrArg (fun f : Section1.ClassFunction L => f 1) hsum
  have happly : ((∑ i : Fin n, b i • ζ i) : Section1.ClassFunction L) 1 =
      ∑ i : Fin n, b i * ζ i 1 := by
    rw [happly']
    simp
  rw [happly]
  simp [Finset.sum_mul_sum, hζone, mul_assoc, mul_left_comm, mul_comm]

private theorem double_sum_sub_inv_mul_pf77
    {n : ℕ} (a p q : Fin n → Fin n → ℂ) (D : ℂ) :
    (∑ i : Fin n, ∑ j : Fin n, a i j * p i j) -
      D⁻¹ * (∑ i : Fin n, ∑ j : Fin n, a i j * q i j) =
    ∑ i : Fin n, ∑ j : Fin n, a i j * (p i j - q i j / D) := by
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum, ← mul_assoc]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  ring

private theorem projectionBasisPackage_normExpansion_of_inducedFamilyEnumeration_pf77
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T : Finset (Section1.ClassFunction L)} {n : ℕ}
    {ζ : Fin (n + 1) → Section1.ClassFunction L} {d : Fin n → ℂ}
    (h76 : hypothesis_7_6_statement A L H K T)
    (henum : inducedFamilyEnumeration T ζ d) :
    ∀ c : Fin n → ℂ,
      (Section5.cfNormSq
          ((by
            classical
            exact fun x : L =>
              if (x : G) ∈ A then
                ∑ i : Fin n,
                  (star (c i) / (Section5.cfNormSq (ζ (Fin.succ i)) : ℂ)) *
                    ζ (Fin.succ i) x
              else 0) : Section1.ClassFunction L) : ℂ) =
        ∑ i : Fin n, ∑ j : Fin n,
          (star (c i) * c j) /
            ((Section5.cfNormSq (ζ (Fin.succ i)) : ℂ) *
              (Section5.cfNormSq (ζ (Fin.succ j)) : ℂ)) *
            (Section1.scalarProduct L (ζ (Fin.succ i)) (ζ (Fin.succ j)) -
              (ζ (Fin.succ i) 1 * ζ (Fin.succ j) 1) /
                ((H.relIndex L : ℂ) * (Nat.card H : ℂ))) := by
  classical
  intro c
  have h76orig := h76
  rcases h76 with ⟨hHL, hHnormal, _h71, hAeq, _hT⟩
  haveI : (H.subgroupOf L).Normal := hHnormal
  let ζtail : Fin n → Section1.ClassFunction L := fun i => ζ (Fin.succ i)
  let b : Fin n → ℂ := fun i => star (c i) / (Section5.cfNormSq (ζtail i) : ℂ)
  let approx : Section1.ClassFunction L := ∑ i : Fin n, b i • ζtail i
  let f : Section1.ClassFunction L := fun x : L =>
    if (x : G) ∈ A then ∑ i : Fin n, b i * ζtail i x else 0
  change (Section5.cfNormSq f : ℂ) = _
  have hcardHsub : Nat.card (H.subgroupOf L) = Nat.card H := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := H) (K := L) hHL).toEquiv
  have hcardL_nat : H.relIndex L * Nat.card H = Nat.card L := by
    rw [Subgroup.relIndex, ← hcardHsub]
    exact Subgroup.index_mul_card (H := H.subgroupOf L)
  have hcardL : (Nat.card L : ℂ) = (H.relIndex L : ℂ) * (Nat.card H : ℂ) := by
    have hcast : ((H.relIndex L * Nat.card H : ℕ) : ℂ) = (Nat.card L : ℂ) := by
      exact_mod_cast hcardL_nat
    simpa [Nat.cast_mul] using hcast.symm
  have hζzero : ∀ i : Fin n, ∀ x : L, (x : G) ∉ H → ζtail i x = 0 := by
    intro i x hxH
    rcases inducedFamilyEnumeration_induced_irreducible_pf77
        (A := A) (L := L) (H := H) (K := K) (T := T)
        (ζ := ζ) (d := d) h76orig henum (Fin.succ i) with
      ⟨θ, _hθ, hζ⟩
    have hxHsub : x ∉ H.subgroupOf L := by
      intro hx
      exact hxH hx
    dsimp [ζtail]
    rw [hζ]
    exact Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal
      (H.subgroupOf L) θ hxHsub
  have hζone : ∀ j : Fin n, star (ζtail j 1) = ζtail j 1 := by
    intro j
    have hchar : Section1.IsCharacter (ζtail j) := by
      rcases inducedFamilyEnumeration_induced_irreducible_pf77
          (A := A) (L := L) (H := H) (K := K) (T := T)
          (ζ := ζ) (d := d) h76orig henum (Fin.succ j) with
        ⟨θ, hθ, hζ⟩
      have hθchar : Section1.IsCharacter θ :=
        Section1.isCharacter_of_isIrreducibleCharacterOnGroup hθ
      dsimp [ζtail]
      rw [hζ]
      exact Section1.isCharacter_inducedCF_of_isCharacter
        (H.subgroupOf L) θ hθchar
    exact character_value_one_star_pf77 hchar
  have hf_one : f 1 = 0 := by
    have h1notA : (1 : G) ∉ A := by
      intro h1A
      rw [hAeq] at h1A
      exact h1A.2 (by simp)
    dsimp [f]
    rw [if_neg h1notA]
  have hf_approx : ∀ x : L, x ≠ 1 → f x = approx x := by
    intro x hxne
    by_cases hxA : (x : G) ∈ A
    · simp [f, approx, ζtail, b, hxA]
    · have hxHnot : (x : G) ∉ H := by
        intro hxH
        apply hxA
        rw [hAeq]
        exact ⟨hxH, by intro hxG1; exact hxne (Subtype.ext hxG1)⟩
      simp [f, approx, ζtail, b, hxA, hζzero, hxHnot]
  have hrestrict := scalarProduct_eq_sub_identity_of_eq_off_identity_pf77
    f approx hf_one hf_approx
  have hsp_approx := scalarProduct_weighted_sum_self_pf77 b ζtail
  have hidentity := weighted_sum_identity_term_pf77 b ζtail hζone
  calc
    (Section5.cfNormSq f : ℂ) = Section1.scalarProduct L f f := by
      rw [scalarProduct_self_eq_cfNormSq_pf77]
    _ = Section1.scalarProduct L approx approx -
          (Nat.card L : ℂ)⁻¹ * (approx 1 * star (approx 1)) := hrestrict
    _ = (∑ i : Fin n, ∑ j : Fin n,
            b i * star (b j) * Section1.scalarProduct L (ζtail i) (ζtail j)) -
          (Nat.card L : ℂ)⁻¹ *
            (∑ i : Fin n, ∑ j : Fin n,
              b i * star (b j) * (ζtail i 1 * ζtail j 1)) := by
        rw [hsp_approx, hidentity]
    _ = ∑ i : Fin n, ∑ j : Fin n,
          (star (c i) * c j) /
            ((Section5.cfNormSq (ζ (Fin.succ i)) : ℂ) *
              (Section5.cfNormSq (ζ (Fin.succ j)) : ℂ)) *
            (Section1.scalarProduct L (ζ (Fin.succ i)) (ζ (Fin.succ j)) -
              (ζ (Fin.succ i) 1 * ζ (Fin.succ j) 1) /
                ((H.relIndex L : ℂ) * (Nat.card H : ℂ))) := by
        rw [hcardL]
        let D : ℂ := (H.relIndex L : ℂ) * (Nat.card H : ℂ)
        calc
          (∑ i : Fin n, ∑ j : Fin n,
              b i * star (b j) * Section1.scalarProduct L (ζtail i) (ζtail j)) -
            D⁻¹ *
              (∑ i : Fin n, ∑ j : Fin n,
                b i * star (b j) * (ζtail i 1 * ζtail j 1)) =
              ∑ i : Fin n, ∑ j : Fin n,
                (b i * star (b j)) *
                  (Section1.scalarProduct L (ζtail i) (ζtail j) -
                    (ζtail i 1 * ζtail j 1) / D) := by
                exact double_sum_sub_inv_mul_pf77
                  (fun i j : Fin n => b i * star (b j))
                  (fun i j : Fin n => Section1.scalarProduct L (ζtail i) (ζtail j))
                  (fun i j : Fin n => ζtail i 1 * ζtail j 1) D
          _ = ∑ i : Fin n, ∑ j : Fin n,
              (star (c i) * c j) /
                ((Section5.cfNormSq (ζ (Fin.succ i)) : ℂ) *
                  (Section5.cfNormSq (ζ (Fin.succ j)) : ℂ)) *
                (Section1.scalarProduct L (ζ (Fin.succ i)) (ζ (Fin.succ j)) -
                  (ζ (Fin.succ i) 1 * ζ (Fin.succ j) 1) /
                    ((H.relIndex L : ℂ) * (Nat.card H : ℂ))) := by
                refine Finset.sum_congr rfl ?_
                intro i _hi
                refine Finset.sum_congr rfl ?_
                intro j _hj
                simp [D, ζtail, b, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

public theorem projectionBasisPackage_normExpansion_of_inducedFamilyEnumeration_source_bridge
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T : Finset (Section1.ClassFunction L)} {n : ℕ}
    {ζ : Fin (n + 1) → Section1.ClassFunction L} {d : Fin n → ℂ}
    (h76 : hypothesis_7_6_statement A L H K T)
    (henum : inducedFamilyEnumeration T ζ d) :
    ∀ c : Fin n → ℂ,
      (Section5.cfNormSq
          ((by
            classical
            exact fun x : L =>
              if (x : G) ∈ A then
                ∑ i : Fin n,
                  (star (c i) / (Section5.cfNormSq (ζ (Fin.succ i)) : ℂ)) *
                    ζ (Fin.succ i) x
              else 0) : Section1.ClassFunction L) : ℂ) =
        ∑ i : Fin n, ∑ j : Fin n,
          (star (c i) * c j) /
            ((Section5.cfNormSq (ζ (Fin.succ i)) : ℂ) *
              (Section5.cfNormSq (ζ (Fin.succ j)) : ℂ)) *
            (Section1.scalarProduct L (ζ (Fin.succ i)) (ζ (Fin.succ j)) -
              (ζ (Fin.succ i) 1 * ζ (Fin.succ j) 1) /
                ((H.relIndex L : ℂ) * (Nat.card H : ℂ))) := by
  exact projectionBasisPackage_normExpansion_of_inducedFamilyEnumeration_pf77 h76 henum

public theorem projectionBasisPackage_tail_of_inducedFamilyEnumeration_source_bridge
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T : Finset (Section1.ClassFunction L)} {n : ℕ}
    {ζ : Fin (n + 1) → Section1.ClassFunction L} {d : Fin n → ℂ}
    (h76 : hypothesis_7_6_statement A L H K T)
    (henum : inducedFamilyEnumeration T ζ d) :
    (∀ φ : Section1.ClassFunction L,
      Section1.IsClassFunction φ →
      (∀ i : Fin n,
        Section1.scalarProduct L (ζ (Fin.succ i) - d i • ζ 0) φ = 0) →
        ∀ x : L, (x : G) ∈ A → φ x = 0) ∧
    (∀ c : Fin n → ℂ,
      (Section5.cfNormSq
          ((by
            classical
            exact fun x : L =>
              if (x : G) ∈ A then
                ∑ i : Fin n,
                  (star (c i) / (Section5.cfNormSq (ζ (Fin.succ i)) : ℂ)) *
                    ζ (Fin.succ i) x
              else 0) : Section1.ClassFunction L) : ℂ) =
        ∑ i : Fin n, ∑ j : Fin n,
          (star (c i) * c j) /
            ((Section5.cfNormSq (ζ (Fin.succ i)) : ℂ) *
              (Section5.cfNormSq (ζ (Fin.succ j)) : ℂ)) *
            (Section1.scalarProduct L (ζ (Fin.succ i)) (ζ (Fin.succ j)) -
              (ζ (Fin.succ i) 1 * ζ (Fin.succ j) 1) /
                ((H.relIndex L : ℂ) * (Nat.card H : ℂ)))) := by
  exact ⟨
    projectionBasisPackage_detection_of_inducedFamilyEnumeration_source_bridge h76 henum,
    projectionBasisPackage_normExpansion_of_inducedFamilyEnumeration_source_bridge h76 henum⟩

public theorem projectionBasisPackage_of_inducedFamilyEnumeration_source_bridge
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L H : Subgroup G} {K : G → Subgroup G}
    {T : Finset (Section1.ClassFunction L)} {n : ℕ}
    {ζ : Fin (n + 1) → Section1.ClassFunction L} {d : Fin n → ℂ}
    (h76 : hypothesis_7_6_statement A L H K T)
    (henum : inducedFamilyEnumeration T ζ d) :
    projectionBasisPackage A L H ζ d := by
  refine ⟨
    projectionBasisPackage_CFon_of_inducedFamilyEnumeration_pf77 h76 henum,
    projectionBasisPackage_norm_ne_of_inducedFamilyEnumeration_pf77 h76 henum,
    projectionBasisPackage_diagonal_of_inducedFamilyEnumeration_pf77 h76 henum,
    ?_, ?_⟩
  · exact (projectionBasisPackage_tail_of_inducedFamilyEnumeration_source_bridge
      h76 henum).1
  · exact (projectionBasisPackage_tail_of_inducedFamilyEnumeration_source_bridge
      h76 henum).2

public theorem theorem_7_7
    {G : Type u} [Group G] [Finite G]
    {n : ℕ}
    (A : Set G) (L H : Subgroup G)
    (K : G → Subgroup G)
    (T : Finset (Section1.ClassFunction L))
    (ζ : Fin (n + 1) → Section1.ClassFunction L)
    (d : Fin n → ℂ)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (χ : Section1.ClassFunction G) (c : Fin n → ℂ) :
    theorem_7_7_statement A L H K T ζ d τ χ c := by
  classical
  rw [theorem_7_7_statement]
  intro h76 hτ henum hbasis hχclass hcoeff
  have h76orig := h76
  rcases h76 with ⟨_hHL, _hHnormal, h71, _hA, _hT⟩
  rcases hτ with ⟨hAL, hτspec⟩
  rcases hbasis with ⟨hψCF, hnorm_ne, hψζ, hspan, hnormExpansion⟩
  let ψ : Fin n → Section1.ClassFunction L :=
    fun i => ζ (Fin.succ i) - d i • ζ 0
  let ρ : Section1.ClassFunction L := dadeProjectionOn A L K χ
  let b : Fin n → ℂ :=
    fun i => star (c i) / (Section5.cfNormSq (ζ (Fin.succ i)) : ℂ)
  let approx : Section1.ClassFunction L :=
    ∑ i : Fin n, b i • ζ (Fin.succ i)
  have hρCF : Section2.CFOn L A ρ :=
    dadeProjectionOn_CFon_pf77 h71 hAL χ hχclass
  have hcoeffL :
      ∀ i : Fin n, c i = Section1.scalarProduct L (ψ i) ρ := by
    intro i
    have hτψ :
        τ (ψ i) = Section2.dadeTransform K hAL (ψ i) := by
      exact hτspec (ψ i) (by simpa [ψ] using hψCF i)
    have h27 := Section2.proposition_2_7 A L K h71 hAL
      (ψ i) χ (by simpa [ψ] using hψCF i) hχclass ρ hρCF.1 (by
        intro a ha
        simp [ρ, dadeProjectionOn, dadeProjection, ha])
    calc
      c i = Section1.scalarProduct G (τ (ψ i)) χ := by
        simpa [projectionCoefficientPackage, ψ] using hcoeff i
      _ = Section1.scalarProduct G
            (Section2.dadeTransform K hAL (ψ i)) χ := by
          rw [hτψ]
      _ = Section1.scalarProduct L (ψ i) ρ := h27.1
  have hstar_b_mul_norm :
      ∀ i : Fin n,
        star (b i) * (Section5.cfNormSq (ζ (Fin.succ i)) : ℂ) = c i := by
    intro i
    have hn : (Section5.cfNormSq (ζ (Fin.succ i)) : ℂ) ≠ 0 := hnorm_ne i
    calc
      star (b i) * (Section5.cfNormSq (ζ (Fin.succ i)) : ℂ) =
          (c i / (Section5.cfNormSq (ζ (Fin.succ i)) : ℂ)) *
          (Section5.cfNormSq (ζ (Fin.succ i)) : ℂ) := by
        simp [b]
      _ = c i := by
        field_simp [hn]
  have happrox_apply :
      approx =
        (fun x : L => ∑ i : Fin n, (b i • ζ (Fin.succ i)) x) := by
    funext x
    simp [approx]
  have hspApprox :
      ∀ j : Fin n, Section1.scalarProduct L (ψ j) approx = c j := by
    intro j
    calc
      Section1.scalarProduct L (ψ j) approx =
          ∑ i : Fin n,
            Section1.scalarProduct L (ψ j) (b i • ζ (Fin.succ i)) := by
        rw [happrox_apply, Section1.scalarProduct_fintype_sum_right]
      _ = ∑ i : Fin n,
            star (b i) *
              Section1.scalarProduct L (ψ j) (ζ (Fin.succ i)) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [Section1.scalarProduct_smul_right]
      _ = ∑ i : Fin n, if i = j then c j else 0 := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        by_cases hij : i = j
        · subst i
          simpa [ψ, hψζ] using hstar_b_mul_norm j
        · have hji : j ≠ i := fun h => hij h.symm
          simp [ψ, hψζ, hij, hji]
      _ = c j := by
        simp
  have happroxClass : Section1.IsClassFunction approx := by
    intro x g
    simp [approx]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    have hζclass :
        Section1.IsClassFunction (ζ (Fin.succ i)) :=
      inducedFamilyEnumeration_classFunction_pf77
        (A := A) (L := L) (H := H) (K := K) (T := T)
        (ζ := ζ) (d := d) h76orig henum (Fin.succ i)
    rw [hζclass x g]
  have hdiffClass : Section1.IsClassFunction (ρ - approx) := by
    intro x g
    simp [Pi.sub_apply, hρCF.1 x g, happroxClass x g]
  have horthDiff :
      ∀ j : Fin n, Section1.scalarProduct L (ψ j) (ρ - approx) = 0 := by
    intro j
    rw [scalarProduct_sub_right_pf77, ← hcoeffL j, hspApprox j]
    simp
  have hpointOn : ∀ x : L, (x : G) ∈ A → ρ x = approx x := by
    intro x hx
    have hv := hspan (ρ - approx) hdiffClass horthDiff x hx
    exact sub_eq_zero.mp (by simpa using hv)
  have hρ_eq :
      ρ =
        (fun x : L =>
          if (x : G) ∈ A then
            ∑ i : Fin n,
              (star (c i) / (Section5.cfNormSq (ζ (Fin.succ i)) : ℂ)) *
                ζ (Fin.succ i) x
          else 0) := by
    funext x
    by_cases hx : (x : G) ∈ A
    · have hpt := hpointOn x hx
      simpa [approx, b, hx] using hpt
    · simp [ρ, dadeProjectionOn, hx]
  constructor
  · intro x hx
    have hpt := hpointOn x hx
    simpa [ρ, dadeProjectionOn, dadeProjection, approx, b, hx] using hpt
  · change (Section5.cfNormSq ρ : ℂ) =
        ∑ i : Fin n, ∑ j : Fin n,
          (star (c i) * c j) /
            ((Section5.cfNormSq (ζ (Fin.succ i)) : ℂ) *
              (Section5.cfNormSq (ζ (Fin.succ j)) : ℂ)) *
            (Section1.scalarProduct L (ζ (Fin.succ i)) (ζ (Fin.succ j)) -
              (ζ (Fin.succ i) 1 * ζ (Fin.succ j) 1) /
                ((H.relIndex L : ℂ) * (Nat.card H : ℂ)))
    rw [hρ_eq]
    exact hnormExpansion c

end CFSG.Section7
