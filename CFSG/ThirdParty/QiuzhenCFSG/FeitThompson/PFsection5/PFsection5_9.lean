module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_7
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_3
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.Basic
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_1
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_4
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_5
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.FieldTheory.IsAlgClosed.Classification
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 5, Theorem (5.9)

This file isolates PF `(5.9)(a)` and `(5.9)(b)` as a single theorem target
with separate Lean declarations for the two clauses.  The part `(a)` statement
uses the exponent/argument avatar of the source cyclotomic Galois action.
-/

noncomputable section

open scoped BigOperators
open IsCyclotomicExtension

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section5

universe u v

/-! ## (5.9) -/

/--
Peterfalvi `(5.9)(a)`: under Hypothesis `(2.2)`, if `S ⊆ Irr(L)` and
`Z[S,L#] = Z[S,A]`, then any isometric extension on `Z[S]` commuting with the
Dade transform on `Z[S,A]` also commutes with the cyclotomic Galois transport
on members of `S`.

This is recorded in the repository's exponent/argument avatar: a field
automorphism is represented by an `e`-power companion on group elements.
-/
@[expose] public def theorem_5_9_a_statement
    {G : Type u} [Group G] [Finite G]
    (A : Set G)
    (L : Subgroup G)
    (H : G → Subgroup G)
    (hAL : ∀ a ∈ A, a ∈ L)
    (S : Finset (Section1.ClassFunction L)) : Prop :=
  Section2.Hypothesis2 A L H →
    (∀ X : Section1.ClassFunction L,
      X ∈ S → Section1.IsIrreducibleCharacterOnGroup X) →
      (∀ χ : Section1.ClassFunction L,
        integerSpanOn S puncturedSet χ ↔
          integerSpanOn S (Section4Scratch.subgroupPullbackSet L A) χ) →
        1 < S.card →
          ∀ T1 : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G,
            isCFLinearIsometryOnSpan S T1 →
              mapsIntegerSpanToVirtualCharacters S T1 →
                (∀ χ : Section1.ClassFunction L,
                  integerSpanOn S (Section4Scratch.subgroupPullbackSet L A) χ →
                    T1 χ = Section2.dadeTransform H hAL χ) →
                  ∀ {e : ℕ},
                    e.Coprime (Nat.card G) →
                      (∀ φ : Section1.ClassFunction L,
                        φ ∈ S →
                          ∃ φu : Section1.ClassFunction L,
                            φu ∈ S ∧
                              Section3.classFunctionArgumentPow φ φu e) →
                        ∀ {X Xu : Section1.ClassFunction L},
                          X ∈ S →
                            Xu ∈ S →
                              Section3.classFunctionArgumentPow X Xu e →
                                Section3.classFunctionArgumentPow (T1 X) (T1 Xu) e


private noncomputable def standardizeRepresentation_pf59
    {G : Type u} {V : Type v} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    Representation ℂ G (Fin (Module.finrank ℂ V) → ℂ) := by
  let b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V := Module.finBasis ℂ V
  let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := b.equivFun
  refine
    { toFun := fun g => e.conj (ρ g)
      map_one' := by
        ext x
        simp [LinearEquiv.conj_apply]
      map_mul' := by
        intro g h
        ext x
        simp [LinearEquiv.conj_apply, map_mul] }

private theorem standardizeRepresentation_character_pf59
    {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    (standardizeRepresentation_pf59 ρ).character g = ρ.character g := by
  dsimp [standardizeRepresentation_pf59, Representation.character]
  exact LinearMap.trace_conj' (R := ℂ) (M := V)
    (N := Fin (Module.finrank ℂ V) → ℂ) (ρ g)
    (Module.Basis.equivFun (Module.finBasis ℂ V))

private theorem standardizeRepresentation_irreducible_pf59
    {G : Type u} {V : Type v} [Group G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : Representation.IsIrreducible ρ) :
    Representation.IsIrreducible (standardizeRepresentation_pf59 ρ) := by
  let b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V := Module.finBasis ℂ V
  let e : V ≃ₗ[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := b.equivFun
  let eRep : Theory.Representation.RepEquiv ρ (standardizeRepresentation_pf59 ρ) := by
    refine
      { toLinearEquiv := e
        isIntertwining' := ?_ }
    intro g
    ext v i
    simp [standardizeRepresentation_pf59, e, b, b.equivFun_apply]
  exact (Theory.Representation.RepEquiv.irreducible_euqiv eRep).1 hρ

private def dualCoannihilatorSubrepresentation_pf59
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V)
    (S : Subrepresentation ρ.dual) : Subrepresentation ρ where
  toSubmodule := S.toSubmodule.dualCoannihilator
  apply_mem_toSubmodule := by
    intro g v hv
    rw [Submodule.mem_dualCoannihilator] at hv ⊢
    intro f hf
    have hS : ρ.dual g⁻¹ f ∈ S.toSubmodule := S.apply_mem_toSubmodule g⁻¹ hf
    have hvzero := hv (ρ.dual g⁻¹ f) hS
    simpa only [Representation.dual_apply, inv_inv, Module.Dual.transpose_apply,
      LinearMap.comp_apply] using hvzero

private theorem dualCoannihilatorSubrepresentation_eq_top_of_eq_bot_pf59
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :
    dualCoannihilatorSubrepresentation_pf59 ρ (⊥ : Subrepresentation ρ.dual) = ⊤ := by
  apply Subrepresentation.toSubmodule_injective
  change (⊥ : Submodule ℂ (Module.Dual ℂ V)).dualCoannihilator = (⊤ : Submodule ℂ V)
  simp

private theorem dualCoannihilatorSubrepresentation_eq_bot_of_eq_top_pf59
    {G V : Type*} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) :
    dualCoannihilatorSubrepresentation_pf59 ρ (⊤ : Subrepresentation ρ.dual) = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  change (⊤ : Submodule ℂ (Module.Dual ℂ V)).dualCoannihilator = (⊥ : Submodule ℂ V)
  simp

private theorem representation_dual_irreducible_of_pf59
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hρ : Representation.IsIrreducible ρ) :
    Representation.IsIrreducible ρ.dual := by
  letI : Representation.IsIrreducible ρ := hρ
  refine
    { exists_pair_ne := ?_
      eq_bot_or_eq_top := ?_ }
  · refine ⟨⊥, ⊤, ?_⟩
    intro hbotTop
    have hcong := congrArg (dualCoannihilatorSubrepresentation_pf59 ρ) hbotTop
    have htop : (⊤ : Subrepresentation ρ) = ⊥ := by
      rw [dualCoannihilatorSubrepresentation_eq_top_of_eq_bot_pf59 ρ,
        dualCoannihilatorSubrepresentation_eq_bot_of_eq_top_pf59 ρ] at hcong
      exact hcong
    exact IsSimpleOrder.bot_ne_top (α := Subrepresentation ρ) htop.symm
  · intro S
    have hN := eq_bot_or_eq_top (dualCoannihilatorSubrepresentation_pf59 ρ S)
    rcases hN with hNbot | hNtop
    · right
      apply Subrepresentation.toSubmodule_injective
      have hdual :
          S.toSubmodule.dualCoannihilator.dualAnnihilator = S.toSubmodule :=
        Subspace.dualCoannihilator_dualAnnihilator_eq
      have hNsub : S.toSubmodule.dualCoannihilator = ⊥ := by
        have htmp := congrArg Subrepresentation.toSubmodule hNbot
        change S.toSubmodule.dualCoannihilator = (⊥ : Submodule ℂ V) at htmp
        exact htmp
      rw [hNsub] at hdual
      change S.toSubmodule = (⊤ : Submodule ℂ (Module.Dual ℂ V))
      simpa only [Submodule.dualAnnihilator_bot] using hdual.symm
    · left
      apply Subrepresentation.toSubmodule_injective
      apply le_antisymm ?_ bot_le
      intro f hf
      rw [Submodule.mem_bot]
      ext v
      have hNsub : S.toSubmodule.dualCoannihilator = ⊤ := by
        have htmp := congrArg Subrepresentation.toSubmodule hNtop
        change S.toSubmodule.dualCoannihilator = (⊤ : Submodule ℂ V) at htmp
        exact htmp
      have hv : v ∈ S.toSubmodule.dualCoannihilator := by
        rw [hNsub]
        exact Submodule.mem_top
      exact (Submodule.mem_dualCoannihilator v).mp hv f hf


private theorem conjugateCharacter_representationCharacter_eq_dual_pf59
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    Section1.conjugateCharacter ρ.character = ρ.dual.character := by
  funext g
  calc
    Section1.conjugateCharacter ρ.character g = star (ρ.character g) := by
      simp [Section1.conjugateCharacter]
    _ = ρ.character g⁻¹ := by
      exact (Section1.representation_character_inv_eq_star_character ρ g).symm
    _ = ρ.dual.character g := by
      rw [Representation.char_dual]


private theorem isIrreducibleCharacterOnGroup_conjugateCharacter_pf59
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsIrreducibleCharacterOnGroup (Section1.conjugateCharacter χ) := by
  rcases hχ with ⟨n, ρ, hρirr, hχchar⟩
  refine ⟨Module.finrank ℂ (Module.Dual ℂ (Fin n → ℂ)),
    standardizeRepresentation_pf59 (G := G) (ρ := ρ.dual), ?_, ?_⟩
  · exact standardizeRepresentation_irreducible_pf59
      (ρ := ρ.dual) (representation_dual_irreducible_of_pf59 ρ hρirr)
  · calc
      Section1.conjugateCharacter χ
          = Section1.conjugateCharacter ρ.character := by rw [hχchar]
      _ = ρ.dual.character := conjugateCharacter_representationCharacter_eq_dual_pf59 ρ
      _ = (standardizeRepresentation_pf59 (G := G) (ρ := ρ.dual)).character := by
            ext g
            exact (standardizeRepresentation_character_pf59
              (G := G) (ρ := ρ.dual) g).symm


private theorem isVirtualCharacter_zsmul_pf59
    {G : Type u} [Group G] [Finite G]
    (n : ℤ) {χ : Section1.ClassFunction G}
    (hχ : Theory.Character.IsVirtualCharacter χ) :
    Theory.Character.IsVirtualCharacter (n • χ) := by
  classical
  rcases hχ with ⟨r, m, k, ρ, rfl⟩
  refine ⟨r, fun i => n * m i, k, ρ, ?_⟩
  ext g
  simp [Theory.Character.virtualCharacterOfRepresentations, Finset.mul_sum, mul_assoc]

private theorem isVirtualCharacter_finset_sum_pf59
    {G : Type u} [Group G] [Finite G]
    {ι : Type*} (s : Finset ι) (Φ : ι → Section1.ClassFunction G)
    (hΦ : ∀ i ∈ s, Theory.Character.IsVirtualCharacter (Φ i)) :
    Theory.Character.IsVirtualCharacter (Finset.sum s Φ) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, (fun i => nomatch i), (fun i => nomatch i), (fun i => nomatch i), ?_⟩
      ext g
      simp [Theory.Character.virtualCharacterOfRepresentations]
  | @insert a s ha ih =>
      have ha' : Theory.Character.IsVirtualCharacter (Φ a) := hΦ a (Finset.mem_insert_self a s)
      have hs' : Theory.Character.IsVirtualCharacter (Finset.sum s Φ) := by
        refine ih ?_
        intro i hi
        exact hΦ i (Finset.mem_insert_of_mem hi)
      simpa [Finset.sum_insert ha] using Section3.isVirtualCharacter_add ha' hs'

public theorem isVirtualCharacter_evalCoeff_pf59
    {G : Type u} [Group G] [Finite G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Section1.ClassFunction G)
    (hμ : ∀ i, Theory.Character.IsVirtualCharacter (μ i))
    (v : Section1.CoeffVector ι) :
    Theory.Character.IsVirtualCharacter (Section1.evalCoeff μ v) := by
  classical
  rw [Section1.evalCoeff]
  refine isVirtualCharacter_finset_sum_pf59 (Finset.univ : Finset ι)
    (fun i => (v i : ℂ) • μ i) ?_
  intro i _hi
  have hsmul :
      (v i : ℂ) • μ i = (v i • μ i : Section1.ClassFunction G) := by
    ext g
    simp [zsmul_eq_mul]
  rw [hsmul]
  exact isVirtualCharacter_zsmul_pf59 (v i) (hμ i)

private theorem scalarProduct_self_of_irreducibleCharacterOnGroup_pf59
    {G : Type*} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.scalarProduct G χ χ = 1 := by
  rcases hχ with ⟨n, ρ, hρ, rfl⟩
  simpa using Section1.scalarProduct_representation_char_self ρ hρ

private theorem one_not_mem_dadeSupport_pf59
    {G : Type u} [Group G] [Finite G]
    {A : Set G} {L : Subgroup G} {H : G → Subgroup G}
    (h22 : Section2.Hypothesis2 A L H) :
    (1 : G) ∉ Section2.dadeSupport A H := by
  intro h1
  rcases h1 with ⟨a, ha, h, hh, hconj⟩
  rcases hconj with ⟨x, hx⟩
  have hah : a * h = 1 := by
    simpa [Section2.conjBy] using hx.symm
  have hah' : a = h⁻¹ := by
    calc
      a = a * 1 := by simp
      _ = a * (h * h⁻¹) := by simp
      _ = (a * h) * h⁻¹ := by simp [mul_assoc]
      _ = h⁻¹ := by simp [hah]
  have haH : a ∈ H a := by
    simpa [hah'] using (H a).inv_mem hh
  have haCent : a ∈ Section2.elementCentralizer a := by
    rw [Section2.elementCentralizer, Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y = a := by simpa using hy
    simp [hy']
  have haCL : a ∈ Section2.centralizerIn L a := by
    exact Subgroup.mem_inf.mpr ⟨h22.subset_L a ha, haCent⟩
  have haInf : a ∈ H a ⊓ Section2.centralizerIn L a := by
    exact Subgroup.mem_inf.mpr ⟨haH, haCL⟩
  have haBot : a ∈ (⊥ : Subgroup G) := by
    simpa [(h22.centralizer_eq_product ha).inf_eq_bot] using haInf
  exact h22.subset_punctured a ha (by simpa using haBot)


private theorem degree_conjugateCharacter_eq_of_isIrreducibleCharacterOnGroup_pf59
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.degree (Section1.conjugateCharacter χ) = Section1.degree χ := by
  rcases hχ with ⟨n, ρ, _hρirr, rfl⟩
  rw [conjugateCharacter_representationCharacter_eq_dual_pf59]
  simp [Section1.degree_representation_character]


private theorem integerSpan_of_mem_pf59
    {G : Type*} [Group G]
    (S : Finset (Section1.ClassFunction G))
    {χ : Section1.ClassFunction G}
    (hχ : χ ∈ S) :
    integerSpan S χ := by
  classical
  refine ⟨Section1.basisVector ⟨χ, hχ⟩, ?_⟩
  ext g
  rw [Section1.evalCoeff, Finset.sum_eq_single ⟨χ, hχ⟩]
  · simp [Section1.basisVector]
  · intro x _hx hxne
    simp [Section1.basisVector, hxne]
  · intro hFalse
    exact (hFalse (Finset.mem_univ _)).elim

private theorem integerSpan_add_pf59
    {G : Type*} [Group G]
    {S : Finset (Section1.ClassFunction G)}
    {φ ψ : Section1.ClassFunction G} :
    integerSpan S φ → integerSpan S ψ → integerSpan S (φ + ψ) := by
  classical
  rintro ⟨v, rfl⟩ ⟨w, rfl⟩
  refine ⟨v + w, ?_⟩
  ext g
  simp [Section1.evalCoeff, Finset.sum_add_distrib, add_mul]

private theorem integerSpan_neg_pf59
    {G : Type*} [Group G]
    {S : Finset (Section1.ClassFunction G)}
    {φ : Section1.ClassFunction G} :
    integerSpan S φ → integerSpan S (-φ) := by
  classical
  rintro ⟨v, rfl⟩
  refine ⟨-v, ?_⟩
  ext g
  simp [Section1.evalCoeff]

private theorem integerSpan_sub_pf59
    {G : Type*} [Group G]
    {S : Finset (Section1.ClassFunction G)}
    {φ ψ : Section1.ClassFunction G} :
    integerSpan S φ → integerSpan S ψ → integerSpan S (φ - ψ) := by
  intro hφ hψ
  simpa [sub_eq_add_neg] using integerSpan_add_pf59 hφ (integerSpan_neg_pf59 hψ)


private theorem scalarProduct_irreducible_eq_zero_of_ne_pf59
    {G : Type u} [Group G] [Finite G]
    {φ ψ : Section1.ClassFunction G}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hne : φ ≠ ψ) :
    Section1.scalarProduct G φ ψ = 0 := by
  rcases hφ with ⟨n, ρ, hρirr, hρchar⟩
  rcases hψ with ⟨m, σ, hσirr, hσchar⟩
  exact Section1.scalarProduct_irreducible_representationCharacter_eq_zero_of_ne
    φ ψ ρ σ hρchar hσchar hρirr hσirr hne


private theorem scalarProduct_sub_left_pf59
    {G : Type*} [Finite G] (φ1 φ2 ψ : Section1.ClassFunction G) :
    Section1.scalarProduct G (φ1 - φ2) ψ =
      Section1.scalarProduct G φ1 ψ - Section1.scalarProduct G φ2 ψ := by
  calc
    Section1.scalarProduct G (φ1 - φ2) ψ
        = Section1.scalarProduct G (φ1 + (-1 : ℂ) • φ2) ψ := by
            congr 1
            ext g
            simp [sub_eq_add_neg]
    _ = Section1.scalarProduct G φ1 ψ +
          Section1.scalarProduct G ((-1 : ℂ) • φ2) ψ := by
          rw [Section1.scalarProduct_add_left]
    _ = Section1.scalarProduct G φ1 ψ - Section1.scalarProduct G φ2 ψ := by
          rw [Section1.scalarProduct_smul_left]
          simp [sub_eq_add_neg]


public theorem isSignedIrreducibleCharacter_conjugateCharacter_pf59
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    Section3.IsSignedIrreducibleCharacter (Section1.conjugateCharacter χ) := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  refine ⟨ε, hε, Section1.conjugateCharacter μ,
    isIrreducibleCharacterOnGroup_conjugateCharacter_pf59 hμ, ?_⟩
  rcases hε with rfl | rfl <;>
    ext g <;> simp [Section1.conjugateCharacter]

private theorem degree_conjugateCharacter_eq_of_signedIrreducible_pf59
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    Section1.degree (Section1.conjugateCharacter χ) = Section1.degree χ := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  rcases hε with rfl | rfl
  · simpa using degree_conjugateCharacter_eq_of_isIrreducibleCharacterOnGroup_pf59 hμ
  · calc
      Section1.degree (Section1.conjugateCharacter ((-1 : ℂ) • μ))
          = (-1 : ℂ) * Section1.degree (Section1.conjugateCharacter μ) := by
              simp [Section1.degree_apply, Section1.conjugateCharacter]
      _ = (-1 : ℂ) * Section1.degree μ := by
            rw [degree_conjugateCharacter_eq_of_isIrreducibleCharacterOnGroup_pf59 hμ]
      _ = Section1.degree ((-1 : ℂ) • μ) := by
            simp [Section1.degree_apply]

private theorem degree_ne_zero_of_signedIrreducible_pf59
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    Section1.degree χ ≠ 0 := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  rcases hε with rfl | rfl
  · simpa [Section1.degree_apply] using
      Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup μ hμ
  · simpa [Section1.degree_apply] using
      neg_ne_zero.mpr (Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup μ hμ)

public theorem conjugateCharacter_ne_neg_of_signedIrreducible_pf59
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    Section1.conjugateCharacter χ ≠ -χ := by
  intro hEq
  have hdegEq : Section1.degree (Section1.conjugateCharacter χ) = -Section1.degree χ := by
    simpa [Section1.degree] using congrArg Section1.degree hEq
  have hdegConj : Section1.degree (Section1.conjugateCharacter χ) = Section1.degree χ :=
    degree_conjugateCharacter_eq_of_signedIrreducible_pf59 hχ
  have hneg : Section1.degree χ = -Section1.degree χ := by
    calc
      Section1.degree χ = Section1.degree (Section1.conjugateCharacter χ) := hdegConj.symm
      _ = -Section1.degree χ := hdegEq
  have htwo : (2 : ℂ) * Section1.degree χ = 0 := by
    have hsum := congrArg (fun z => z + Section1.degree χ) hneg
    simpa [two_mul, add_comm, add_left_comm, add_assoc] using hsum
  have hdeg0 : Section1.degree χ = 0 := by
    have h2ne : (2 : ℂ) ≠ 0 := by norm_num
    exact (mul_eq_zero.mp htwo).resolve_left h2ne
  exact degree_ne_zero_of_signedIrreducible_pf59 hχ hdeg0

public theorem signedIrreducible_eq_or_eq_neg_of_scalarProduct_ne_zero_pf59
    {G : Type u} [Group G] [Finite G]
    {χ ψ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ)
    (hψ : Section3.IsSignedIrreducibleCharacter ψ)
    (hsp : Section1.scalarProduct G χ ψ ≠ 0) :
    ψ = χ ∨ ψ = -χ := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  rcases hψ with ⟨δ, hδ, ν, hν, rfl⟩
  by_cases hμν : μ = ν
  · subst hμν
    rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl
    · left
      simp
    · right
      simp
    · right
      simp
    · left
      simp
  · have horth : Section1.scalarProduct G μ ν = 0 :=
      scalarProduct_irreducible_eq_zero_of_ne_pf59 hμ hν hμν
    exfalso
    rcases hε with rfl | rfl <;> rcases hδ with rfl | rfl
    · exact hsp (by simpa using horth)
    · have hzero : Section1.scalarProduct G μ (-ν) = 0 := by
        rw [show (-ν : Section1.ClassFunction G) = (-1 : ℂ) • ν by
              ext g
              simp,
            Section1.scalarProduct_smul_right]
        simp [horth]
      exact hsp (by simpa using hzero)
    · have hzero : Section1.scalarProduct G (-μ) ν = 0 := by
        rw [show (-μ : Section1.ClassFunction G) = (-1 : ℂ) • μ by
              ext g
              simp,
            Section1.scalarProduct_smul_left]
        simp [horth]
      exact hsp (by simpa using hzero)
    · have hzero : Section1.scalarProduct G (-μ) (-ν) = 0 := by
        rw [show (-μ : Section1.ClassFunction G) = (-1 : ℂ) • μ by
              ext g
              simp,
            show (-ν : Section1.ClassFunction G) = (-1 : ℂ) • ν by
              ext g
              simp,
            Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
        simp [horth]
      exact hsp (by simpa using hzero)


public theorem eq_neg_of_scalarProduct_eq_neg_one_signed_pf59
    {G : Type u} [Group G] [Finite G]
    {χ ψ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ)
    (hψ : Section3.IsSignedIrreducibleCharacter ψ)
    (hsp : Section1.scalarProduct G χ ψ = -1) :
    ψ = -χ := by
  rcases signedIrreducible_eq_or_eq_neg_of_scalarProduct_ne_zero_pf59 hχ hψ (by simp [hsp]) with
    hEq | hEq
  · have hself : Section1.scalarProduct G χ χ = 1 := by
      rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
      rcases hε with rfl | rfl
      · simpa using scalarProduct_self_of_irreducibleCharacterOnGroup_pf59 hμ
      · calc
          Section1.scalarProduct G ((-1 : ℂ) • μ) ((-1 : ℂ) • μ)
              = (-1 : ℂ) * star (-1 : ℂ) * Section1.scalarProduct G μ μ := by
                  rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
                  ring
          _ = 1 := by simp [scalarProduct_self_of_irreducibleCharacterOnGroup_pf59 hμ]
    have hcontra : (1 : ℂ) = -1 := by
      simpa [hEq, hself] using hsp
    norm_num at hcontra
  · exact hEq

private theorem int_sq_sum_eq_zero_all_zero_pf59
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (z : ι → ℤ)
    (hsum : Finset.sum s (fun i => z i * z i) = 0) :
    ∀ i, i ∈ s → z i = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro i hi
      simp at hi
  | @insert a s ha ih =>
      intro i hi
      have hnonneg_a : 0 ≤ z a * z a := by
        simpa [pow_two] using (sq_nonneg (z a))
      have hnonneg_s : 0 ≤ Finset.sum s (fun j => z j * z j) := by
        exact Finset.sum_nonneg (by
          intro j _hj
          simpa [pow_two] using (sq_nonneg (z j)))
      have hsplit : z a * z a + Finset.sum s (fun j => z j * z j) = 0 := by
        simpa [Finset.sum_insert ha, add_assoc, add_left_comm, add_comm] using hsum
      have hsq_a : z a * z a = 0 := by
        nlinarith
      have hsq_s : Finset.sum s (fun j => z j * z j) = 0 := by
        nlinarith
      rcases Finset.mem_insert.mp hi with rfl | hi'
      · exact sq_eq_zero_iff.mp (by simpa [pow_two] using hsq_a)
      · exact ih hsq_s i hi'

private theorem exists_sign_of_int_sq_sum_eq_one_pf59
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (z : ι → ℤ)
    (hsum : Finset.sum s (fun i => z i * z i) = 1) :
    ∃ i, i ∈ s ∧ (z i = 1 ∨ z i = -1) ∧
      ∀ j, j ∈ s → j ≠ i → z j = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp at hsum
  | @insert a s ha ih =>
      have hnonneg_a : 0 ≤ z a * z a := by
        simpa [pow_two] using (sq_nonneg (z a))
      have hnonneg_s : 0 ≤ Finset.sum s (fun j => z j * z j) := by
        exact Finset.sum_nonneg (by
          intro j _hj
          simpa [pow_two] using (sq_nonneg (z j)))
      have hsplit : z a * z a + Finset.sum s (fun j => z j * z j) = 1 := by
        simpa [Finset.sum_insert ha, add_assoc, add_left_comm, add_comm] using hsum
      by_cases hza : z a = 0
      · have hsq_s : Finset.sum s (fun j => z j * z j) = 1 := by
          nlinarith [hsplit]
        rcases ih hsq_s with ⟨i, hi, hsign, hzero⟩
        refine ⟨i, Finset.mem_insert_of_mem hi, hsign, ?_⟩
        intro j hj hji
        rcases Finset.mem_insert.mp hj with rfl | hj'
        · exact hza
        · exact hzero j hj' hji
      · have hsq_pos : 0 < z a * z a := by
          have hsq_ne : z a * z a ≠ 0 := by
            intro hsq
            exact hza (sq_eq_zero_iff.mp (by simpa [pow_two] using hsq))
          exact lt_of_le_of_ne hnonneg_a (Ne.symm hsq_ne)
        have hsq_a : z a * z a = 1 := by
          nlinarith [hsplit, hnonneg_s]
        have hsq_s : Finset.sum s (fun j => z j * z j) = 0 := by
          nlinarith [hsplit, hsq_a]
        have hsign_a : z a = 1 ∨ z a = -1 := by
          exact sq_eq_one_iff.mp (by simpa [pow_two] using hsq_a)
        have hzero_s : ∀ j ∈ s, z j = 0 :=
          int_sq_sum_eq_zero_all_zero_pf59 s z hsq_s
        refine ⟨a, Finset.mem_insert_self a s, hsign_a, ?_⟩
        intro j hj hja
        rcases Finset.mem_insert.mp hj with rfl | hj'
        · exact False.elim (hja rfl)
        · exact hzero_s j hj'

public theorem signed_irreducible_of_virtual_norm_one_pf59
    {G : Type u} [Group G] [Finite G]
    {φ : Section1.ClassFunction G}
    (hvirt : Theory.Character.IsVirtualCharacter φ)
    (hself : Section1.scalarProduct G φ φ = 1) :
    Section3.IsSignedIrreducibleCharacter φ := by
  classical
  have hφclass : Section1.IsClassFunction φ :=
    Section3.isVirtualCharacter_isClassFunction hvirt
  rcases Theory.Character.irreducible_characters_form_basis (G := G) with
    ⟨ι, hι, χ, hχ, _b, _hb⟩
  letI : Fintype ι := hι
  letI : Finite ι := Finite.of_fintype ι
  letI : Fintype ι := Fintype.ofFinite ι
  rcases hχ with ⟨hirr, hall, _hinj⟩
  let ψ : ι → Section1.ClassFunction G := fun i => Section1.ofConjClassFunction (χ i)
  have hψclass : ∀ i, Section1.IsClassFunction (ψ i) := by
    intro i
    exact Section1.ofConjClassFunction_isClassFunction (χ i)
  have hψirr : ∀ i, Section1.IsIrreducibleCharacterOnGroup (ψ i) := by
    intro i
    exact Section3.ofConjClassFunction_isIrreducibleCharacterOnGroup (hirr i)
  have horthψ :
      ∀ i j,
        Section1.scalarProduct G (ψ i) (ψ j) = if i = j then 1 else 0 := by
    intro i j
    change Section1.scalarProduct G (Section1.ofConjClassFunction (χ i))
      (Section1.ofConjClassFunction (χ j)) = if i = j then 1 else 0
    rw [Section1.scalarProduct_ofConjClassFunction]
    exact Section1.representation_completeFamily_orthonormal
      (chi := χ) ⟨hirr, hall, _hinj⟩ i j
  have hcoeff_int :
      ∀ i, ∃ z : ℤ, Section1.scalarProduct G φ (ψ i) = (z : ℂ) := by
    intro i
    exact Section3.scalarProduct_isVirtualCharacter_eq_int
      hvirt
      (Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hψirr i))
  let a : ι → ℤ := fun i => Classical.choose (hcoeff_int i)
  have ha : ∀ i, Section1.scalarProduct G φ (ψ i) = (a i : ℂ) := by
    intro i
    exact Classical.choose_spec (hcoeff_int i)
  let φsum : Section1.ClassFunction G :=
    Section1.weightedFamilySum (fun i => (a i : ℂ)) ψ
  have hφsumclass : Section1.IsClassFunction φsum := by
    intro x g
    unfold φsum Section1.weightedFamilySum
    refine Finset.sum_congr rfl ?_
    intro i _hi
    simp [hψclass i x g]
  have hEq : φsum = φ := by
    apply Section1.classFunction_eq_of_inner_irreducible
      (phi := φsum) (psi := φ) hφsumclass hφclass
    intro ξ hξ
    rcases hall ξ hξ with ⟨i, rfl⟩
    calc
      Theory.Character.classFunctionInner
          (Section1.toConjClassFunction φsum hφsumclass) (χ i) =
        Section1.scalarProduct G φsum (ψ i) := by
          rw [← Section1.toConjClassFunction_ofConjClassFunction (χ i)]
          exact Section1.classFunctionInner_toConjClassFunction
            φsum (ψ i) hφsumclass (hψclass i)
      _ = (a i : ℂ) := by
          exact Section1.scalarProduct_weightedFamilySum_left_orthonormal
            (w := fun i => (a i : ℂ)) (chi := ψ) horthψ i
      _ = Section1.scalarProduct G φ (ψ i) := (ha i).symm
      _ = Theory.Character.classFunctionInner
          (Section1.toConjClassFunction φ hφclass) (χ i) := by
          rw [← Section1.toConjClassFunction_ofConjClassFunction (χ i)]
          exact (Section1.classFunctionInner_toConjClassFunction
            φ (ψ i) hφclass (hψclass i)).symm
  have hcoeff_sum :
      Section1.scalarProduct G φsum φsum =
        ∑ i : ι, star ((a i : ℂ)) * (a i : ℂ) := by
    calc
      Section1.scalarProduct G φsum φsum =
        ∑ i : ι, star ((a i : ℂ)) * Section1.scalarProduct G φsum (ψ i) := by
          unfold φsum Section1.weightedFamilySum
          rw [Section1.scalarProduct_fintype_sum_right]
          refine Finset.sum_congr rfl ?_
          intro i _hi
          change
            Section1.scalarProduct G
                (fun g => ∑ i, (a i : ℂ) * ψ i g)
                (((a i : ℂ)) • ψ i) =
              star ((a i : ℂ)) *
                Section1.scalarProduct G
                  (fun g => ∑ i, (a i : ℂ) * ψ i g) (ψ i)
          rw [Section1.scalarProduct_smul_right]
      _ = ∑ i : ι, star ((a i : ℂ)) * (a i : ℂ) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [Section1.scalarProduct_weightedFamilySum_left_orthonormal
            (w := fun i => (a i : ℂ)) (chi := ψ) horthψ i]
  have hsq_complex : ((∑ i : ι, a i * a i : ℤ) : ℂ) = 1 := by
    calc
      ((∑ i : ι, a i * a i : ℤ) : ℂ) =
        ∑ i : ι, star ((a i : ℂ)) * (a i : ℂ) := by
          simp [Int.cast_sum, Int.cast_mul]
      _ = Section1.scalarProduct G φsum φsum := hcoeff_sum.symm
      _ = 1 := by
          simpa [hEq] using hself
  have hsq_int : ∑ i : ι, a i * a i = 1 := by
    exact_mod_cast hsq_complex
  rcases exists_sign_of_int_sq_sum_eq_one_pf59 (Finset.univ) a hsq_int with
    ⟨i0, _hi0, hsign0, hzero0⟩
  have hsingle :
      φsum = (a i0 : ℂ) • ψ i0 := by
    ext g
    unfold φsum Section1.weightedFamilySum
    rw [Finset.sum_eq_single i0]
    · simp
    · intro j _hj hji
      simp [hzero0 j (by simp) hji]
    · intro hi0not
      exact False.elim (hi0not (by simp))
  rcases hsign0 with hi0 | hi0
  · refine ⟨1, Or.inl rfl, ψ i0, hψirr i0, ?_⟩
    calc
      φ = φsum := hEq.symm
      _ = (a i0 : ℂ) • ψ i0 := hsingle
      _ = (1 : ℂ) • ψ i0 := by simp [hi0]
  · refine ⟨-1, Or.inr rfl, ψ i0, hψirr i0, ?_⟩
    calc
      φ = φsum := hEq.symm
      _ = (a i0 : ℂ) • ψ i0 := hsingle
      _ = (-1 : ℂ) • ψ i0 := by simp [hi0]


private theorem positive_degree_nat_of_isIrreducibleCharacterOnGroup_pf59
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    ∃ n : ℕ, 0 < n ∧ Section1.degree χ = (n : ℂ) := by
  rcases hχ with ⟨n, ρ, hρirr, hχchar⟩
  refine ⟨n, ?_, ?_⟩
  · by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    have hdeg : Section1.degree χ = 0 := by
      simp [hχchar, Section1.degree_representation_character ρ, hn0]
    exact Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup χ
      ⟨n, ρ, hρirr, hχchar⟩ hdeg
  · rw [hχchar]
    simpa using Section1.degree_representation_character ρ

private theorem integerSpan_zsmul_pf59
    {H : Type*} [Group H]
    {S : Finset (Section1.ClassFunction H)}
    {φ : Section1.ClassFunction H} (z : ℤ) :
    integerSpan S φ → integerSpan S ((z : ℂ) • φ) := by
  classical
  rintro ⟨v, rfl⟩
  refine ⟨z • v, ?_⟩
  ext g
  simp [Section1.evalCoeff, Finset.mul_sum, mul_assoc]


private theorem degree_zero_combo_mem_integerSpanOn_punctured_pf59
    {H : Type*} [Group H] [Finite H]
    {S : Finset (Section1.ClassFunction H)}
    {X ψ : Section1.ClassFunction H}
    (m n : ℕ)
    (hXspan : integerSpan S X)
    (hψspan : integerSpan S ψ)
    (hdegX : Section1.degree X = (n : ℂ))
    (hdegψ : Section1.degree ψ = (m : ℂ)) :
    integerSpanOn S puncturedSet (((m : ℂ) • X) - ((n : ℂ) • ψ)) := by
  refine ⟨integerSpan_sub_pf59
      (integerSpan_zsmul_pf59 (S := S) (φ := X) (m : ℤ) hXspan)
      (integerSpan_zsmul_pf59 (S := S) (φ := ψ) (n : ℤ) hψspan), ?_⟩
  rw [Section1.supportedOn_iff]
  intro g hg
  have hg1 : g = 1 := by simpa [puncturedSet] using hg
  subst hg1
  have hX1 : X 1 = (n : ℂ) := by simpa [Section1.degree_apply] using hdegX
  have hψ1 : ψ 1 = (m : ℂ) := by simpa [Section1.degree_apply] using hdegψ
  simp [hX1, hψ1, sub_eq_add_neg]
  ring

public theorem pow_surjective_of_coprime_natCard_pf59
    {G : Type u} [Group G] [Finite G] {e : ℕ}
    (he : e.Coprime (Nat.card G)) :
    Function.Surjective (fun g : G => g ^ e) := by
  intro g
  have hcop_order : e.Coprime (orderOf g) :=
    Nat.Coprime.of_dvd_right (orderOf_dvd_natCard g) he
  by_cases h1 : orderOf g = 1
  · refine ⟨1, ?_⟩
    simp [orderOf_eq_one_iff.mp h1]
  have hlt : 1 < orderOf g := by
    exact lt_of_le_of_ne (Nat.succ_le_of_lt (orderOf_pos g)) (Ne.symm h1)
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop_order hlt
  refine ⟨g ^ m, ?_⟩
  change (g ^ m) ^ e = g
  rw [← pow_mul, Nat.mul_comm, ← pow_mod_orderOf, hm, pow_one]

private theorem pow_bijective_of_coprime_natCard_pf59
    {G : Type u} [Group G] [Finite G] {e : ℕ}
    (he : e.Coprime (Nat.card G)) :
    Function.Bijective (fun g : G => g ^ e) := by
  have hsurj : Function.Surjective (fun g : G => g ^ e) :=
    pow_surjective_of_coprime_natCard_pf59 (G := G) (e := e) he
  refine ⟨?_, hsurj⟩
  rw [Finite.injective_iff_surjective]
  exact hsurj

public theorem scalarProduct_argumentPow_eq_of_coprime_natCard_pf59
    {G : Type u} [Group G] [Finite G]
    {φ ψ : Section1.ClassFunction G} {e : ℕ}
    (he : e.Coprime (Nat.card G)) :
    Section1.scalarProduct G (fun g : G => φ (g ^ e)) (fun g : G => ψ (g ^ e)) =
      Section1.scalarProduct G φ ψ := by
  classical
  let pe : G ≃ G :=
    Equiv.ofBijective (fun g : G => g ^ e)
      (pow_bijective_of_coprime_natCard_pf59 (G := G) (e := e) he)
  have hsum :
      ∑ g : G, φ (g ^ e) * star (ψ (g ^ e)) =
        ∑ g : G, φ g * star (ψ g) := by
    simpa [pe] using
      (Equiv.sum_comp pe (fun g : G => φ g * star (ψ g)))
  unfold Section1.scalarProduct
  rw [hsum]

public theorem scalarProduct_self_signedIrreducible_pf59
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    Section1.scalarProduct G χ χ = 1 := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  rcases hε with rfl | rfl
  · simpa using scalarProduct_self_of_irreducibleCharacterOnGroup_pf59 hμ
  · calc
      Section1.scalarProduct G ((-1 : ℂ) • μ) ((-1 : ℂ) • μ)
          = (-1 : ℂ) * star (-1 : ℂ) * Section1.scalarProduct G μ μ := by
              rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
              ring
      _ = 1 := by simp [scalarProduct_self_of_irreducibleCharacterOnGroup_pf59 hμ]

public theorem signed_irreducible_eq_of_scalarProduct_eq_one_pf59
    {G : Type u} [Group G] [Finite G]
    {χ ψ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ)
    (hψ : Section3.IsSignedIrreducibleCharacter ψ)
    (hsp : Section1.scalarProduct G χ ψ = 1) :
    ψ = χ := by
  rcases signedIrreducible_eq_or_eq_neg_of_scalarProduct_ne_zero_pf59
      hχ hψ (by simp [hsp]) with hEq | hEq
  · exact hEq
  · have hcontra : (-1 : ℂ) = 1 := by
      calc
        (-1 : ℂ) = Section1.scalarProduct G χ (-χ) := by
            rw [show -χ = (-1 : ℂ) • χ by ext g; simp]
            rw [Section1.scalarProduct_smul_right, scalarProduct_self_signedIrreducible_pf59 hχ]
            simp
        _ = 1 := by simpa [hEq] using hsp
    norm_num at hcontra

private noncomputable def matrixMapRepresentation_pf59
    {G : Type u} [Group G] (τ : ℂ ≃+* ℂ)
    {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ)) :
    Representation ℂ G (Fin n → ℂ) := by
  refine
    { toFun := fun g =>
        Matrix.toLin' ((LinearMap.toMatrix' (ρ g)).map τ.toRingHom)
      map_one' := ?_
      map_mul' := ?_ }
  · apply LinearMap.toMatrix'.injective
    simp [LinearMap.toMatrix'_one]
  · intro g h
    have hmat :
        ((LinearMap.toMatrix' (ρ (g * h))).map τ.toRingHom) =
          ((LinearMap.toMatrix' (ρ g)).map τ.toRingHom) *
            ((LinearMap.toMatrix' (ρ h)).map τ.toRingHom) := by
      simp [LinearMap.toMatrix'_mul, map_mul]
    calc
      Matrix.toLin' ((LinearMap.toMatrix' (ρ (g * h))).map τ.toRingHom)
          = Matrix.toLin'
              (((LinearMap.toMatrix' (ρ g)).map τ.toRingHom) *
                ((LinearMap.toMatrix' (ρ h)).map τ.toRingHom)) := by
              rw [hmat]
      _ = Matrix.toLin' ((LinearMap.toMatrix' (ρ g)).map τ.toRingHom) ∘ₗ
            Matrix.toLin' ((LinearMap.toMatrix' (ρ h)).map τ.toRingHom) := by
              rw [Matrix.toLin'_mul]
      _ = Matrix.toLin' ((LinearMap.toMatrix' (ρ g)).map τ.toRingHom) *
            Matrix.toLin' ((LinearMap.toMatrix' (ρ h)).map τ.toRingHom) := by
              rw [Module.End.mul_eq_comp]

private theorem matrixMapRepresentation_pf59_character
    {G : Type u} [Group G] (τ : ℂ ≃+* ℂ)
    {n : ℕ} (ρ : Representation ℂ G (Fin n → ℂ)) (g : G) :
    (matrixMapRepresentation_pf59 (G := G) τ ρ).character g = τ (ρ.character g) := by
  unfold matrixMapRepresentation_pf59
  change
    LinearMap.trace ℂ (Fin n → ℂ)
        (Matrix.toLin' ((LinearMap.toMatrix' (ρ g)).map τ.toRingHom)) =
      τ (ρ.character g)
  calc
    LinearMap.trace ℂ (Fin n → ℂ)
        (Matrix.toLin' ((LinearMap.toMatrix' (ρ g)).map τ.toRingHom))
        = τ ((LinearMap.toMatrix' (ρ g)).trace) := by
            rw [Matrix.trace_toLin'_eq]
            simp [Matrix.trace]
    _ = τ (LinearMap.trace ℂ (Fin n → ℂ) (ρ g)) := by
          congr 1
          exact (LinearMap.trace_eq_matrix_trace ℂ
            (Pi.basisFun ℂ (Fin n)) (ρ g)).symm
    _ = τ (ρ.character g) := by
          rw [Representation.character]

private theorem irreducibleCharacterOnGroup_argumentPow_of_ringEquiv_pf59
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ)
    {e : ℕ} (he : e.Coprime (Nat.card G))
    (τ : ℂ ≃+* ℂ)
    (hτ : ∀ g : G, τ (χ g) = χ (g ^ e)) :
    Section1.IsIrreducibleCharacterOnGroup (fun g : G => χ (g ^ e)) := by
  have hχself : Section1.scalarProduct G χ χ = 1 :=
    scalarProduct_self_of_irreducibleCharacterOnGroup_pf59 hχ
  rcases hχ with ⟨n, ρ, _hirr, hchar⟩
  let ρτ : Representation ℂ G (Fin n → ℂ) := matrixMapRepresentation_pf59 τ ρ
  have hcharτ : ∀ g : G, ρτ.character g = χ (g ^ e) := by
    intro g
    have hτρ : τ (ρ.character g) = ρ.character (g ^ e) := by
      simpa [hchar] using hτ g
    calc
      ρτ.character g = τ (ρ.character g) := by
        simpa [ρτ] using matrixMapRepresentation_pf59_character (G := G) τ ρ g
      _ = ρ.character (g ^ e) := hτρ
      _ = χ (g ^ e) := by rw [hchar]
  have hnorm :
      Section1.scalarProduct G (fun g : G => χ (g ^ e)) (fun g : G => χ (g ^ e)) = 1 := by
    calc
      Section1.scalarProduct G (fun g : G => χ (g ^ e)) (fun g : G => χ (g ^ e)) =
        Section1.scalarProduct G χ χ :=
          scalarProduct_argumentPow_eq_of_coprime_natCard_pf59
            (G := G) (φ := χ) (ψ := χ) (e := e) he
      _ = 1 := hχself
  have hcfτ : Section1.IsClassFunction ρτ.character := by
    intro x g
    simpa [mul_assoc] using Representation.char_conj (ρ := ρτ) g x
  have hinnerτ :
      Theory.Character.classFunctionInner (Theory.Character.characterClassFunction ρτ) (Theory.Character.characterClassFunction ρτ) =
        Section1.scalarProduct G (fun g : G => χ (g ^ e)) (fun g : G => χ (g ^ e)) := by
    calc
      Theory.Character.classFunctionInner (Theory.Character.characterClassFunction ρτ) (Theory.Character.characterClassFunction ρτ) =
          Section1.scalarProduct G ρτ.character ρτ.character := by
            change Theory.Character.classFunctionInner
                (Section1.toConjClassFunction ρτ.character hcfτ)
                (Section1.toConjClassFunction ρτ.character hcfτ) =
              Section1.scalarProduct G ρτ.character ρτ.character
            exact Section1.classFunctionInner_toConjClassFunction
              ρτ.character ρτ.character hcfτ hcfτ
      _ = Section1.scalarProduct G (fun g : G => χ (g ^ e)) (fun g : G => χ (g ^ e)) := by
            congr 1 <;> ext g <;> exact hcharτ g
  have hirrτ : Representation.IsIrreducible ρτ := by
    apply (Theory.Character.irreducible_iff_character_norm_one (ρ := ρτ)).2
    rw [hinnerτ]
    exact hnorm
  exact ⟨n, ρτ, hirrτ, (funext hcharτ).symm⟩

private theorem same_sign_smul_ne_neg_same_sign_smul_pf59
    {G : Type u} [Group G] [Finite G]
    {ε : ℂ}
    (hε : Section1.IsSign ε)
    {μ ν : Section1.ClassFunction G}
    (hμ : Section1.IsIrreducibleCharacterOnGroup μ)
    (hν : Section1.IsIrreducibleCharacterOnGroup ν) :
    ε • ν ≠ -(ε • μ) := by
  intro hEq
  rcases positive_degree_nat_of_isIrreducibleCharacterOnGroup_pf59 hμ with
    ⟨m, hmpos, hμdeg⟩
  rcases positive_degree_nat_of_isIrreducibleCharacterOnGroup_pf59 hν with
    ⟨n, hnpos, hνdeg⟩
  have hμ1 : μ 1 = (m : ℂ) := by
    simpa [Section1.degree_apply] using hμdeg
  have hν1 : ν 1 = (n : ℂ) := by
    simpa [Section1.degree_apply] using hνdeg
  have hdegEq : ε * (n : ℂ) = -(ε * (m : ℂ)) := by
    calc
      ε * (n : ℂ) = Section1.degree (ε • ν) := by
            simp [Section1.degree_apply, hν1, smul_eq_mul]
      _ = Section1.degree (-(ε • μ)) := by simp [hEq]
      _ = -Section1.degree (ε • μ) := by simp [Section1.degree]
      _ = -(ε * (m : ℂ)) := by
            simp [Section1.degree_apply, hμ1, smul_eq_mul]
  rcases hε with rfl | rfl
  · have hdegRe : (n : ℝ) = -(m : ℝ) := by
      simpa using congrArg Complex.re hdegEq
    have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    nlinarith
  · have hdegRe : -(n : ℝ) = (m : ℝ) := by
      simpa using congrArg Complex.re hdegEq
    have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
    have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
    nlinarith

private theorem complex_galois_aut_pow_on_roots_pf59
    {n e : ℕ} (hn : n ≠ 0) (he : e.Coprime n) :
    ∃ τ : Gal(ℂ/ℚ), ∀ z : ℂ, z ^ n = 1 → τ z = z ^ e := by
  classical
  letI : NeZero n := ⟨hn⟩
  haveI : NeZero (n : ℚ) := ⟨by exact_mod_cast hn⟩
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hζ : IsPrimitiveRoot ζ n := by
    dsimp [ζ]
    exact Complex.isPrimitiveRoot_exp n hn
  have hζalg : IsAlgebraic ℚ ζ := by
    refine ⟨Polynomial.cyclotomic n ℚ, Polynomial.cyclotomic_ne_zero n ℚ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
      Polynomial.map_cyclotomic, ← Polynomial.IsRoot.def,
      Polynomial.isRoot_cyclotomic_iff]
    exact hζ
  let F : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ ({ζ} : Set ℂ)
  have hFcyc : IsCyclotomicExtension {n} ℚ F := by
    change IsCyclotomicExtension {n} ℚ F.toSubalgebra
    rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hζalg]
    exact hζ.adjoin_isCyclotomicExtension ℚ
  haveI : IsCyclotomicExtension {n} ℚ F := hFcyc
  haveI : IsCyclotomicExtension {n} ℚ F.toSubalgebra := by
    change IsCyclotomicExtension {n} ℚ F
    exact hFcyc
  haveI : NumberField F := IsCyclotomicExtension.numberField {n} ℚ F
  let u : (ZMod n)ˣ := ZMod.unitOfCoprime e he
  let σF : Gal(F/ℚ) := (IsCyclotomicExtension.Rat.galEquivZMod n F).symm u
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F ℂ
  let x : s → ℂ := fun a => (a : ℂ)
  have hsx : IsTranscendenceBasis F x := by
    simpa [x] using hs
  let B := Algebra.adjoin F (Set.range x)
  let ae : MvPolynomial s F ≃ₐ[F] B := hsx.1.aevalEquiv
  have hrepr_const (y : F) : ae.symm (algebraMap F B y) = MvPolynomial.C y := by
    apply ae.injective
    rw [AlgEquiv.apply_symm_apply]
    exact (ae.commutes y).symm
  have hmap_const (y : F) :
      (MvPolynomial.mapAlgEquiv (σ := s) (R := ℚ) σF) (MvPolynomial.C y) =
        MvPolynomial.C (σF y) := by
    rw [MvPolynomial.mapAlgEquiv_apply, MvPolynomial.map_C]
    rfl
  let baseAut : B ≃+* B :=
    (ae.symm.toRingEquiv.trans
      (MvPolynomial.mapAlgEquiv (σ := s) (R := ℚ) σF).toRingEquiv).trans
        ae.toRingEquiv
  have hbase_const (y : F) :
      baseAut (algebraMap F B y) = algebraMap F B (σF y) := by
    dsimp [baseAut]
    change ae ((MvPolynomial.mapAlgEquiv (σ := s) (R := ℚ) σF)
      (ae.symm (algebraMap F B y))) = algebraMap F B (σF y)
    rw [hrepr_const y]
    rw [hmap_const y]
    exact ae.commutes (σF y)
  have hbase_Q (q : ℚ) :
      baseAut (algebraMap ℚ B q) = algebraMap ℚ B q := by
    have hq : algebraMap ℚ B q = algebraMap F B (algebraMap ℚ F q) := by
      exact (IsScalarTower.algebraMap_apply ℚ F B q).symm
    rw [hq, hbase_const]
    simp
  let baseAlgAut : B ≃ₐ[ℚ] B := AlgEquiv.ofRingEquiv hbase_Q
  have hbaseAlg_const (y : F) :
      baseAlgAut (algebraMap F B y) = algebraMap F B (σF y) := by
    exact hbase_const y
  have hclosure : IsAlgClosure B ℂ := by
    dsimp [B]
    exact IsAlgClosed.isAlgClosure_of_transcendence_basis x hsx
  let τR : ℂ ≃+* ℂ := by
    letI : IsAlgClosure B ℂ := hclosure
    exact IsAlgClosure.equivOfEquiv ℂ ℂ baseAlgAut.toRingEquiv
  have hτR_Q (q : ℚ) : τR (algebraMap ℚ ℂ q) = algebraMap ℚ ℂ q := by
    letI : IsAlgClosure B ℂ := hclosure
    have hBq := IsAlgClosure.equivOfEquiv_algebraMap (L := ℂ) (M := ℂ)
      baseAlgAut.toRingEquiv (algebraMap ℚ B q)
    simp [τR, baseAlgAut] at hBq ⊢
  let τ : Gal(ℂ/ℚ) := AlgEquiv.ofRingEquiv hτR_Q
  have hτ_on_F (y : F) : τ (y : ℂ) = (σF y : ℂ) := by
    letI : IsAlgClosure B ℂ := hclosure
    have hB := IsAlgClosure.equivOfEquiv_algebraMap (L := ℂ) (M := ℂ)
      baseAlgAut.toRingEquiv (algebraMap F B y)
    change (IsAlgClosure.equivOfEquiv ℂ ℂ baseAlgAut.toRingEquiv)
        (algebraMap B ℂ (algebraMap F B y)) =
      algebraMap B ℂ (baseAlgAut (algebraMap F B y)) at hB
    rw [hbaseAlg_const y] at hB
    simpa [τ, τR, baseAlgAut, hbaseAlg_const y] using hB
  refine ⟨τ, ?_⟩
  intro z hz
  have hzFmem : z ∈ F := by
    exact IsCyclotomicExtension.mem_of_pow_eq_one F.toSubalgebra
      (S := ({n} : Set ℕ)) (by simp) hn hz
  let zF : F := ⟨z, hzFmem⟩
  have hzFpow : zF ^ n = 1 := by
    ext
    exact hz
  have hσu : IsCyclotomicExtension.Rat.galEquivZMod n F σF = u := by
    exact MulEquiv.apply_symm_apply (IsCyclotomicExtension.Rat.galEquivZMod n F) u
  have hmodeq : ((u : ZMod n).val : ℕ) ≡ e [MOD n] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    calc
      (((u : ZMod n).val : ℕ) : ZMod n) = (u : ZMod n) := ZMod.natCast_zmod_val _
      _ = e := ZMod.coe_unitOfCoprime e he
  have hpow_eq :
      zF ^ (IsCyclotomicExtension.Rat.galEquivZMod n F σF).val.val = zF ^ e := by
    rw [hσu]
    exact pow_eq_pow_of_modEq hmodeq hzFpow
  have hσFz : σF zF = zF ^ e := by
    rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq n F σF hzFpow]
    exact hpow_eq
  calc
    τ z = τ (zF : ℂ) := rfl
    _ = (σF zF : ℂ) := hτ_on_F zF
    _ = ((zF ^ e : F) : ℂ) := by rw [hσFz]
    _ = z ^ e := by rfl

public theorem complex_galois_aut_pow_on_roots
    {n e : ℕ} (he : e.Coprime n) :
    ∃ τ : Gal(ℂ/ℚ), ∀ z : ℂ, z ^ n = 1 → τ z = z ^ e := by
  by_cases hn : n = 0
  · have he1 : e = 1 := by
      simpa [hn, Nat.coprime_zero_right] using he
    refine ⟨1, ?_⟩
    intro z _hz
    simp [he1]
  · exact complex_galois_aut_pow_on_roots_pf59 hn he

private theorem representation_character_apply_galois_eq_argumentPow_aux_pf59
    {G V : Type*} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {N e : ℕ} {τ : Gal(ℂ/ℚ)}
    (hτroot : ∀ z : ℂ, z ^ N = 1 → τ z = z ^ e)
    (ρ : Representation ℂ G V)
    (hdivGN : Nat.card G ∣ N) :
    ∀ g : G, τ (ρ.character g) = ρ.character (g ^ e) := by
  intro g
  let f : Module.End ℂ V := ρ g
  let n : ℕ := orderOf g
  have hn : n ≠ 0 := Nat.ne_of_gt (orderOf_pos g)
  have hpow : f ^ n = 1 := by
    dsimp [f, n]
    rw [← MonoidHom.map_pow, pow_orderOf_eq_one, MonoidHom.map_one]
  have hdiv : n ∣ N := by
    exact dvd_trans (by simpa [n] using orderOf_dvd_natCard g) hdivGN
  calc
    τ (ρ.character g) = τ (LinearMap.trace ℂ V (f ^ 1)) := by
      simp [Representation.character, f]
    _ =
        τ (∑ μ : f.Eigenvalues,
          ((μ : ℂ) ^ 1 * Module.finrank ℂ (f.eigenspace (μ : ℂ)))) := by
        rw [Theory.Representation.trace_pow_eq_sum_eigenvalues (f := f) (n := n) (k := 1) hn hpow]
    _ =
        ∑ μ : f.Eigenvalues,
          τ (((μ : ℂ) ^ 1) * Module.finrank ℂ (f.eigenspace (μ : ℂ))) := by
        simp
    _ =
        ∑ μ : f.Eigenvalues,
          ((μ : ℂ) ^ e * Module.finrank ℂ (f.eigenspace (μ : ℂ))) := by
        refine Finset.sum_congr rfl ?_
        intro μ hμ
        have hμn : (μ : ℂ) ^ n = 1 :=
          Section1.eigenvalue_pow_eq_one_of_pow_eq_one hpow μ.property
        have hμN : (μ : ℂ) ^ N = 1 := by
          rcases hdiv with ⟨k, rfl⟩
          rw [pow_mul, hμn, one_pow]
        simp [map_mul, hτroot (μ : ℂ) hμN]
    _ = LinearMap.trace ℂ V (f ^ e) := by
        symm
        rw [Theory.Representation.trace_pow_eq_sum_eigenvalues (f := f) (n := n) (k := e) hn hpow]
    _ = ρ.character (g ^ e) := by
      simp [Representation.character, f]

public theorem virtualCharacter_apply_galois_eq_argumentPow_aux_pf59
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    {N e : ℕ} {τ : Gal(ℂ/ℚ)}
    (hτroot : ∀ z : ℂ, z ^ N = 1 → τ z = z ^ e)
    (hχ : Theory.Character.IsVirtualCharacter χ)
    (hdivGN : Nat.card G ∣ N) :
    ∀ g : G, τ (χ g) = χ (g ^ e) := by
  classical
  rcases hχ with ⟨r, m, n, ρ, hχeq⟩
  intro g
  rw [hχeq, Theory.Character.virtualCharacterOfRepresentations]
  rw [map_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  have hρg :=
    representation_character_apply_galois_eq_argumentPow_aux_pf59
      (N := N) (e := e) (τ := τ) hτroot (ρ i) hdivGN g
  simp [map_mul, hρg]

public theorem isIrreducibleCharacterOnGroup_argumentPow_pf59
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ)
    {e : ℕ} (he : e.Coprime (Nat.card G)) :
    Section1.IsIrreducibleCharacterOnGroup (fun g : G => χ (g ^ e)) := by
  rcases hχ with ⟨n, ρ, hρirr, hchar⟩
  have hcardGne : Nat.card G ≠ 0 := (Nat.card_pos (α := G)).ne'
  rcases complex_galois_aut_pow_on_roots_pf59
      (n := Nat.card G) (e := e) hcardGne he with ⟨τ, hτroot⟩
  have hτ : ∀ g : G, τ (χ g) = χ (g ^ e) := by
    intro g
    calc
      τ (χ g) = τ (ρ.character g) := by rw [hchar]
      _ = ρ.character (g ^ e) := by
            exact representation_character_apply_galois_eq_argumentPow_aux_pf59
              (N := Nat.card G) (e := e) (τ := τ) hτroot ρ dvd_rfl g
      _ = χ (g ^ e) := by rw [hchar]
  exact irreducibleCharacterOnGroup_argumentPow_of_ringEquiv_pf59
    (G := G) (χ := χ) ⟨n, ρ, hρirr, hchar⟩ he τ hτ

private theorem isSignedIrreducibleCharacter_argumentPow_pf59
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ)
    {e : ℕ} (he : e.Coprime (Nat.card G)) :
    Section3.IsSignedIrreducibleCharacter (fun g : G => χ (g ^ e)) := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  refine ⟨ε, hε, (fun g : G => μ (g ^ e)), ?_, ?_⟩
  · exact isIrreducibleCharacterOnGroup_argumentPow_pf59 hμ he
  · ext g
    simp

public theorem galois_dadeTransform_pf59
    {G : Type u} [Group G]
    {A : Set G} {L : Subgroup G}
    (H : G → Subgroup G)
    (hAL : ∀ a ∈ A, a ∈ L)
    (τ : Gal(ℂ/ℚ))
    (α : Section1.ClassFunction L) :
    (fun g : G => τ (Section2.dadeTransform H hAL α g)) =
      Section2.dadeTransform H hAL (fun l : L => τ (α l)) := by
  ext g
  by_cases hg : ∃ a ∈ A, ∃ h ∈ H a, Section2.conjugateIn g (a * h)
  · simp [Section2.dadeTransform, hg]
  · simp [Section2.dadeTransform, hg]

private theorem classFunctionArgumentPow_smul_pf59
    {G : Type*} [Group G]
    {φ ψ : Section1.ClassFunction G}
    {e : ℕ} (z : ℂ)
    (h : Section3.classFunctionArgumentPow φ ψ e) :
    Section3.classFunctionArgumentPow ((z : ℂ) • φ) ((z : ℂ) • ψ) e := by
  intro g
  simp [h g]

private theorem classFunctionArgumentPow_sub_pf59
    {G : Type*} [Group G]
    {φ₁ φ₂ ψ₁ ψ₂ : Section1.ClassFunction G}
    {e : ℕ}
    (h₁ : Section3.classFunctionArgumentPow φ₁ ψ₁ e)
    (h₂ : Section3.classFunctionArgumentPow φ₂ ψ₂ e) :
    Section3.classFunctionArgumentPow (φ₁ - φ₂) (ψ₁ - ψ₂) e := by
  intro g
  simp [h₁ g, h₂ g]

private theorem degree_eq_of_classFunctionArgumentPow_pf59
    {G : Type*} [Group G]
    {φ ψ : Section1.ClassFunction G}
    {e : ℕ}
    (h : Section3.classFunctionArgumentPow φ ψ e) :
    Section1.degree ψ = Section1.degree φ := by
  simpa [Section1.degree] using h 1

private theorem classFunctionArgumentPow_source_eq_of_target_eq_pf59
    {G : Type u} [Group G] [Finite G]
    {φ ψ φu ψu : Section1.ClassFunction G}
    {e : ℕ}
    (he : e.Coprime (Nat.card G))
    (hφ : Section3.classFunctionArgumentPow φ φu e)
    (hψ : Section3.classFunctionArgumentPow ψ ψu e)
    (hu : φu = ψu) :
    φ = ψ := by
  ext g
  obtain ⟨x, rfl⟩ := pow_surjective_of_coprime_natCard_pf59 (G := G) (e := e) he g
  simpa [hφ x, hψ x] using congrArg (fun η : Section1.ClassFunction G => η x) hu

public theorem conjugateCharacter_dadeTransform_pf59
    {G : Type u} [Group G]
    {A : Set G} {L : Subgroup G}
    (H : G → Subgroup G)
    (hAL : ∀ a ∈ A, a ∈ L)
    (α : Section1.ClassFunction L) :
    Section1.conjugateCharacter (Section2.dadeTransform H hAL α) =
      Section2.dadeTransform H hAL (Section1.conjugateCharacter α) := by
  ext g
  by_cases hg : ∃ a ∈ A, ∃ h ∈ H a, Section2.conjugateIn g (a * h)
  · simp [Section2.dadeTransform, hg, Section1.conjugateCharacter]
  · simp [Section2.dadeTransform, hg, Section1.conjugateCharacter]

public theorem theorem_5_9_a
    {G : Type u} [Group G] [Finite G]
    (A : Set G)
    (L : Subgroup G)
    (H : G → Subgroup G)
    (hAL : ∀ a ∈ A, a ∈ L)
    (S : Finset (Section1.ClassFunction L)) :
    theorem_5_9_a_statement A L H hAL S := by
  intro h22 hIrrS hSpanEq hcard T1 hIso hVirt hAgree e he hClosed X Xu hXS hXuS hArg
  classical
  have hXspan : integerSpan S X := integerSpan_of_mem_pf59 S hXS
  have hXuspan : integerSpan S Xu := integerSpan_of_mem_pf59 S hXuS
  have hTXvirt : Theory.Character.IsVirtualCharacter (T1 X) := hVirt X hXspan
  have hTXuvirt : Theory.Character.IsVirtualCharacter (T1 Xu) := hVirt Xu hXuspan
  have hTXself : Section1.scalarProduct G (T1 X) (T1 X) = 1 := by
    calc
      Section1.scalarProduct G (T1 X) (T1 X)
          = Section1.scalarProduct L X X := hIso X X hXspan hXspan
      _ = 1 := scalarProduct_self_of_irreducibleCharacterOnGroup_pf59 (hIrrS X hXS)
  have hTXuself : Section1.scalarProduct G (T1 Xu) (T1 Xu) = 1 := by
    calc
      Section1.scalarProduct G (T1 Xu) (T1 Xu)
          = Section1.scalarProduct L Xu Xu := hIso Xu Xu hXuspan hXuspan
      _ = 1 := scalarProduct_self_of_irreducibleCharacterOnGroup_pf59 (hIrrS Xu hXuS)
  have hTXsigned : Section3.IsSignedIrreducibleCharacter (T1 X) :=
    signed_irreducible_of_virtual_norm_one_pf59 hTXvirt hTXself
  have hTXusigned : Section3.IsSignedIrreducibleCharacter (T1 Xu) :=
    signed_irreducible_of_virtual_norm_one_pf59 hTXuvirt hTXuself
  have heL : e.Coprime (Nat.card L) := by
    exact Nat.Coprime.of_dvd_right (Subgroup.card_subgroup_dvd_card L) he
  obtain ⟨ψ, hψS, hψne⟩ : ∃ ψ, ψ ∈ S ∧ ψ ≠ X := by
    by_contra hNo
    push Not at hNo
    have hsubset : S ⊆ ({X} : Finset (Section1.ClassFunction L)) := by
      intro φ hφ
      simp [hNo φ hφ]
    have hcardle := Finset.card_le_card hsubset
    simp at hcardle
    linarith
  obtain ⟨ψu, hψuS, hψArg⟩ := hClosed ψ hψS
  have hψspan : integerSpan S ψ := integerSpan_of_mem_pf59 S hψS
  have hψuspan : integerSpan S ψu := integerSpan_of_mem_pf59 S hψuS
  have hTψvirt : Theory.Character.IsVirtualCharacter (T1 ψ) := hVirt ψ hψspan
  have hTψself : Section1.scalarProduct G (T1 ψ) (T1 ψ) = 1 := by
    calc
      Section1.scalarProduct G (T1 ψ) (T1 ψ)
          = Section1.scalarProduct L ψ ψ := hIso ψ ψ hψspan hψspan
      _ = 1 := scalarProduct_self_of_irreducibleCharacterOnGroup_pf59 (hIrrS ψ hψS)
  have hTψsigned : Section3.IsSignedIrreducibleCharacter (T1 ψ) :=
    signed_irreducible_of_virtual_norm_one_pf59 hTψvirt hTψself
  rcases positive_degree_nat_of_isIrreducibleCharacterOnGroup_pf59 (hIrrS X hXS) with
    ⟨nX, hnXpos, hdegX⟩
  rcases positive_degree_nat_of_isIrreducibleCharacterOnGroup_pf59 (hIrrS ψ hψS) with
    ⟨nψ, hnψpos, hdegψ⟩
  have hdegXu : Section1.degree Xu = (nX : ℂ) := by
    rw [degree_eq_of_classFunctionArgumentPow_pf59 hArg, hdegX]
  have hdegψu : Section1.degree ψu = (nψ : ℂ) := by
    rw [degree_eq_of_classFunctionArgumentPow_pf59 hψArg, hdegψ]
  have hψu_ne_Xu : ψu ≠ Xu := by
    intro hEq
    exact hψne
      (classFunctionArgumentPow_source_eq_of_target_eq_pf59
        (G := L) (e := e) heL hψArg hArg hEq)
  let χ : Section1.ClassFunction L :=
    ((nψ : ℂ) • X) - ((nX : ℂ) • ψ)
  let χu : Section1.ClassFunction L :=
    ((nψ : ℂ) • Xu) - ((nX : ℂ) • ψu)
  have hχspanOn : integerSpanOn S puncturedSet χ := by
    dsimp [χ]
    exact degree_zero_combo_mem_integerSpanOn_punctured_pf59
      nψ nX hXspan hψspan hdegX hdegψ
  have hχuSpanOn : integerSpanOn S puncturedSet χu := by
    dsimp [χu]
    exact degree_zero_combo_mem_integerSpanOn_punctured_pf59
      nψ nX hXuspan hψuspan hdegXu hdegψu
  have hχA : integerSpanOn S (Section4Scratch.subgroupPullbackSet L A) χ :=
    (hSpanEq χ).mp hχspanOn
  have hχuA : integerSpanOn S (Section4Scratch.subgroupPullbackSet L A) χu :=
    (hSpanEq χu).mp hχuSpanOn
  have hχArg : Section3.classFunctionArgumentPow χ χu e := by
    dsimp [χ, χu]
    exact classFunctionArgumentPow_sub_pf59
      (classFunctionArgumentPow_smul_pf59 (nψ : ℂ) hArg)
      (classFunctionArgumentPow_smul_pf59 (nX : ℂ) hψArg)
  have hTχ : T1 χ = Section2.dadeTransform H hAL χ := hAgree χ hχA
  have hTχu : T1 χu = Section2.dadeTransform H hAL χu := hAgree χu hχuA
  have hχvirtSource : Theory.Character.IsVirtualCharacter χ := by
    rcases hχA.1 with ⟨v, hv⟩
    rw [hv]
    refine isVirtualCharacter_evalCoeff_pf59 _ ?_ v
    intro Y
    exact Section3.isVirtualCharacter_of_irreducibleCharacterOnGroup (hIrrS Y Y.2)
  have hTχvirt : Theory.Character.IsVirtualCharacter (T1 χ) := hVirt χ hχA.1
  have hTχ1 : (T1 χ) 1 = 0 := by
    rw [hTχ]
    exact Section2.dadeTransform_eq_zero_of_not_mem_support
      (H := H) (hAL := hAL) (α := χ) (g := 1)
      (one_not_mem_dadeSupport_pf59 h22)
  have hvanish1 : (((nψ : ℂ) • T1 X) - ((nX : ℂ) • T1 ψ)) 1 = 0 := by
    calc
      (((nψ : ℂ) • T1 X) - ((nX : ℂ) • T1 ψ)) 1 = (T1 χ) 1 := by
        simp [χ, map_sub, map_smul]
      _ = 0 := hTχ1
  rcases hTXsigned with ⟨εX, hεX, μX, hμX, hTXeq⟩
  rcases hTψsigned with ⟨εψ, hεψ, μψ, hμψ, hTψeq⟩
  have hTXsigned' : Section3.IsSignedIrreducibleCharacter (T1 X) := ⟨εX, hεX, μX, hμX, hTXeq⟩
  have hTψsigned' : Section3.IsSignedIrreducibleCharacter (T1 ψ) := ⟨εψ, hεψ, μψ, hμψ, hTψeq⟩
  rcases positive_degree_nat_of_isIrreducibleCharacterOnGroup_pf59 hμX with
    ⟨mX, hmXpos, hμXdeg⟩
  rcases positive_degree_nat_of_isIrreducibleCharacterOnGroup_pf59 hμψ with
    ⟨mψ, hmψpos, hμψdeg⟩
  have hdegT1X : Section1.degree (T1 X) = εX * (mX : ℂ) := by
    calc
      Section1.degree (T1 X) = Section1.degree (εX • μX) := by rw [hTXeq]
      _ = εX * Section1.degree μX := by
            simp [Section1.degree, smul_eq_mul]
      _ = εX * (mX : ℂ) := by rw [hμXdeg]
  have hdegT1ψ : Section1.degree (T1 ψ) = εψ * (mψ : ℂ) := by
    calc
      Section1.degree (T1 ψ) = Section1.degree (εψ • μψ) := by rw [hTψeq]
      _ = εψ * Section1.degree μψ := by
            simp [Section1.degree, smul_eq_mul]
      _ = εψ * (mψ : ℂ) := by rw [hμψdeg]
  have hdegRelation :
      (nψ : ℂ) * Section1.degree (T1 X) -
          (nX : ℂ) * Section1.degree (T1 ψ) = 0 := by
    simpa [Section1.degree, χ, map_sub, map_smul, smul_eq_mul, mul_assoc,
      mul_comm, mul_left_comm, sub_eq_add_neg] using hvanish1
  have hsameSignψ : εψ = εX := by
    rcases hεX with rfl | rfl <;> rcases hεψ with rfl | rfl
    · rfl
    · exfalso
      have hsum : ((nψ : ℂ) * (mX : ℂ) + (nX : ℂ) * (mψ : ℂ)) = 0 := by
        simpa [hdegT1X, hdegT1ψ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
          mul_assoc, mul_comm, mul_left_comm]
          using hdegRelation
      have hsumRe : (nψ : ℝ) * mX + (nX : ℝ) * mψ = 0 := by
        simpa using congrArg Complex.re hsum
      have hnψR : (0 : ℝ) < nψ := by exact_mod_cast hnψpos
      have hnXR : (0 : ℝ) < nX := by exact_mod_cast hnXpos
      have hmXR : (0 : ℝ) < mX := by exact_mod_cast hmXpos
      have hmψR : (0 : ℝ) < mψ := by exact_mod_cast hmψpos
      nlinarith
    · exfalso
      have hsum : -((nψ : ℂ) * (mX : ℂ) + (nX : ℂ) * (mψ : ℂ)) = 0 := by
        simpa [hdegT1X, hdegT1ψ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
          mul_assoc, mul_comm, mul_left_comm]
          using hdegRelation
      have hsumRe : -((nψ : ℝ) * mX + (nX : ℝ) * mψ) = 0 := by
        simpa using congrArg Complex.re hsum
      have hnψR : (0 : ℝ) < nψ := by exact_mod_cast hnψpos
      have hnXR : (0 : ℝ) < nX := by exact_mod_cast hnXpos
      have hmXR : (0 : ℝ) < mX := by exact_mod_cast hmXpos
      have hmψR : (0 : ℝ) < mψ := by exact_mod_cast hmψpos
      nlinarith
    · rfl
  have hsameSignOf_mem :
      ∀ {φ : Section1.ClassFunction L}, φ ∈ S →
        ∃ μ : Section1.ClassFunction G,
          Section1.IsIrreducibleCharacterOnGroup μ ∧
          T1 φ = εX • μ := by
    intro φ hφ
    by_cases hφX : φ = X
    · subst hφX
      exact ⟨μX, hμX, hTXeq⟩
    · have hφspan : integerSpan S φ := integerSpan_of_mem_pf59 S hφ
      have hTφvirt : Theory.Character.IsVirtualCharacter (T1 φ) := hVirt φ hφspan
      have hTφself : Section1.scalarProduct G (T1 φ) (T1 φ) = 1 := by
        calc
          Section1.scalarProduct G (T1 φ) (T1 φ)
              = Section1.scalarProduct L φ φ := hIso φ φ hφspan hφspan
          _ = 1 := scalarProduct_self_of_irreducibleCharacterOnGroup_pf59 (hIrrS φ hφ)
      have hTφsigned : Section3.IsSignedIrreducibleCharacter (T1 φ) :=
        signed_irreducible_of_virtual_norm_one_pf59 hTφvirt hTφself
      rcases hTφsigned with ⟨εφ, hεφ, μφ, hμφ, hTφeq⟩
      rcases positive_degree_nat_of_isIrreducibleCharacterOnGroup_pf59 (hIrrS φ hφ) with
        ⟨nφ, hnφpos, hdegφ⟩
      let χφ : Section1.ClassFunction L :=
        ((nφ : ℂ) • X) - ((nX : ℂ) • φ)
      have hχφspanOn : integerSpanOn S puncturedSet χφ := by
        dsimp [χφ]
        exact degree_zero_combo_mem_integerSpanOn_punctured_pf59
          nφ nX hXspan hφspan hdegX hdegφ
      have hχφA : integerSpanOn S (Section4Scratch.subgroupPullbackSet L A) χφ :=
        (hSpanEq χφ).mp hχφspanOn
      have hTχφ : T1 χφ = Section2.dadeTransform H hAL χφ := hAgree χφ hχφA
      have hTχφ1 : (T1 χφ) 1 = 0 := by
        rw [hTχφ]
        exact Section2.dadeTransform_eq_zero_of_not_mem_support
          (H := H) (hAL := hAL) (α := χφ) (g := 1)
          (one_not_mem_dadeSupport_pf59 h22)
      have hvanishφ : (((nφ : ℂ) • T1 X) - ((nX : ℂ) • T1 φ)) 1 = 0 := by
        calc
          (((nφ : ℂ) • T1 X) - ((nX : ℂ) • T1 φ)) 1 = (T1 χφ) 1 := by
            simp [χφ, map_sub, map_smul]
          _ = 0 := hTχφ1
      rcases positive_degree_nat_of_isIrreducibleCharacterOnGroup_pf59 hμφ with
        ⟨mφ, hmφpos, hμφdeg⟩
      have hdegT1φ : Section1.degree (T1 φ) = εφ * (mφ : ℂ) := by
        calc
          Section1.degree (T1 φ) = Section1.degree (εφ • μφ) := by rw [hTφeq]
          _ = εφ * Section1.degree μφ := by
                simp [Section1.degree, smul_eq_mul]
          _ = εφ * (mφ : ℂ) := by rw [hμφdeg]
      have hdegRelationφ :
          (nφ : ℂ) * Section1.degree (T1 X) -
              (nX : ℂ) * Section1.degree (T1 φ) = 0 := by
        simpa [Section1.degree, χφ, map_sub, map_smul, smul_eq_mul, mul_assoc,
          mul_comm, mul_left_comm, sub_eq_add_neg] using hvanishφ
      have hsameSignφ : εφ = εX := by
        rcases hεX with rfl | rfl <;> rcases hεφ with rfl | rfl
        · rfl
        · exfalso
          have hsum : ((nφ : ℂ) * (mX : ℂ) + (nX : ℂ) * (mφ : ℂ)) = 0 := by
            simpa [hdegT1X, hdegT1φ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
              mul_assoc, mul_comm, mul_left_comm]
              using hdegRelationφ
          have hsumRe : (nφ : ℝ) * mX + (nX : ℝ) * mφ = 0 := by
            simpa using congrArg Complex.re hsum
          have hnφR : (0 : ℝ) < nφ := by exact_mod_cast hnφpos
          have hnXR : (0 : ℝ) < nX := by exact_mod_cast hnXpos
          have hmXR : (0 : ℝ) < mX := by exact_mod_cast hmXpos
          have hmφR : (0 : ℝ) < mφ := by exact_mod_cast hmφpos
          nlinarith
        · exfalso
          have hsum : -((nφ : ℂ) * (mX : ℂ) + (nX : ℂ) * (mφ : ℂ)) = 0 := by
            simpa [hdegT1X, hdegT1φ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
              mul_assoc, mul_comm, mul_left_comm]
              using hdegRelationφ
          have hsumRe : -((nφ : ℝ) * mX + (nX : ℝ) * mφ) = 0 := by
            simpa using congrArg Complex.re hsum
          have hnφR : (0 : ℝ) < nφ := by exact_mod_cast hnφpos
          have hnXR : (0 : ℝ) < nX := by exact_mod_cast hnXpos
          have hmXR : (0 : ℝ) < mX := by exact_mod_cast hmXpos
          have hmφR : (0 : ℝ) < mφ := by exact_mod_cast hmφpos
          nlinarith
        · rfl
      exact ⟨μφ, hμφ, by simpa [hsameSignφ] using hTφeq⟩
  obtain ⟨μXu, hμXu, hTXueq⟩ := hsameSignOf_mem hXuS
  obtain ⟨μψu, hμψu, hTψueq⟩ := hsameSignOf_mem hψuS
  have hTXpowSigned :
      Section3.IsSignedIrreducibleCharacter (fun g : G => T1 X (g ^ e)) := by
    exact isSignedIrreducibleCharacter_argumentPow_pf59 hTXsigned' he
  have hTψpowSigned :
      Section3.IsSignedIrreducibleCharacter (fun g : G => T1 ψ (g ^ e)) := by
    exact isSignedIrreducibleCharacter_argumentPow_pf59 hTψsigned' he
  let Xpow : Section1.ClassFunction G := fun g => T1 X (g ^ e)
  let ψpow : Section1.ClassFunction G := fun g => T1 ψ (g ^ e)
  have hμXpow : Section1.IsIrreducibleCharacterOnGroup (fun g : G => μX (g ^ e)) :=
    isIrreducibleCharacterOnGroup_argumentPow_pf59 hμX he
  have hμψpow : Section1.IsIrreducibleCharacterOnGroup (fun g : G => μψ (g ^ e)) :=
    isIrreducibleCharacterOnGroup_argumentPow_pf59 hμψ he
  have hXpowEq : Xpow = εX • (fun g : G => μX (g ^ e)) := by
    ext g
    simp [Xpow, hTXeq]
  have hψpowEq : ψpow = εX • (fun g : G => μψ (g ^ e)) := by
    ext g
    simp [ψpow, hTψeq, hsameSignψ]
  have hT1Xu_signed : Section3.IsSignedIrreducibleCharacter (T1 Xu) :=
    ⟨εX, hεX, μXu, hμXu, hTXueq⟩
  have hscalar_zero_or_one_of_same_sign :
      ∀ {α β μ ν : Section1.ClassFunction G},
        α = εX • μ →
        β = εX • ν →
        Section1.IsIrreducibleCharacterOnGroup μ →
        Section1.IsIrreducibleCharacterOnGroup ν →
        Section1.scalarProduct G α β = 0 ∨
          Section1.scalarProduct G α β = 1 := by
    intro α β μ ν hα hβ hμ hν
    by_cases hsp : Section1.scalarProduct G α β = 0
    · exact Or.inl hsp
    · have hαsigned : Section3.IsSignedIrreducibleCharacter α := ⟨εX, hεX, μ, hμ, hα⟩
      have hβsigned : Section3.IsSignedIrreducibleCharacter β := ⟨εX, hεX, ν, hν, hβ⟩
      rcases signedIrreducible_eq_or_eq_neg_of_scalarProduct_ne_zero_pf59
          hαsigned hβsigned hsp with hEq | hEq
      · right
        simpa [hEq] using scalarProduct_self_signedIrreducible_pf59 hαsigned
      · exfalso
        exact (same_sign_smul_ne_neg_same_sign_smul_pf59 hεX hμ hν)
          (by simpa [hα, hβ] using hEq)
  have hχpow : Section3.classFunctionArgumentPow (T1 χ) (T1 χu) e := by
    have hcardGne : Nat.card G ≠ 0 := (Nat.card_pos (α := G)).ne'
    obtain ⟨τ, hτroot⟩ :=
      complex_galois_aut_pow_on_roots_pf59 (n := Nat.card G) (e := e) hcardGne he
    have hτχ : ∀ l : L, τ (χ l) = χ (l ^ e) :=
      virtualCharacter_apply_galois_eq_argumentPow_aux_pf59
        (N := Nat.card G) (e := e) (τ := τ) hτroot hχvirtSource
        (Subgroup.card_subgroup_dvd_card L)
    have hτχu : (fun l : L => τ (χ l)) = χu := by
      ext l
      simpa [hχArg l] using hτχ l
    have hτTχ : ∀ g : G, τ (T1 χ g) = T1 χ (g ^ e) :=
      virtualCharacter_apply_galois_eq_argumentPow_aux_pf59
        (N := Nat.card G) (e := e) (τ := τ) hτroot hTχvirt (dvd_refl _)
    have hτTχu : (fun g : G => τ (T1 χ g)) = T1 χu := by
      ext g
      calc
        τ (T1 χ g) = τ (Section2.dadeTransform H hAL χ g) := by rw [hTχ]
        _ = Section2.dadeTransform H hAL (fun l : L => τ (χ l)) g := by
            simpa using congrArg (fun f : Section1.ClassFunction G => f g)
              (galois_dadeTransform_pf59 (H := H) (hAL := hAL) τ χ)
        _ = Section2.dadeTransform H hAL χu g := by rw [hτχu]
        _ = T1 χu g := by rw [hTχu]
    intro g
    calc
      T1 χu g = τ (T1 χ g) := by
        simpa using (congrArg (fun f : Section1.ClassFunction G => f g) hτTχu).symm
      _ = T1 χ (g ^ e) := hτTχ g
  have hEqχpow :
      ((nψ : ℂ) • Xpow) - ((nX : ℂ) • ψpow) =
        ((nψ : ℂ) • T1 Xu) - ((nX : ℂ) • T1 ψu) := by
    ext g
    simpa [χ, χu, Xpow, ψpow, map_sub, map_smul] using (hχpow g).symm
  have hsp_ψu_Xu : Section1.scalarProduct G (T1 ψu) (T1 Xu) = 0 := by
    calc
      Section1.scalarProduct G (T1 ψu) (T1 Xu)
          = Section1.scalarProduct L ψu Xu := hIso ψu Xu hψuspan hXuspan
      _ = 0 := scalarProduct_irreducible_eq_zero_of_ne_pf59
            (hIrrS ψu hψuS) (hIrrS Xu hXuS) hψu_ne_Xu
  have hspEq :
      (nψ : ℂ) * Section1.scalarProduct G Xpow (T1 Xu) -
          (nX : ℂ) * Section1.scalarProduct G ψpow (T1 Xu) = nψ := by
    have hraw := congrArg
      (fun ζ : Section1.ClassFunction G => Section1.scalarProduct G ζ (T1 Xu))
      hEqχpow
    simpa [scalarProduct_sub_left_pf59, Section1.scalarProduct_smul_left,
      scalarProduct_self_signedIrreducible_pf59 hT1Xu_signed, hsp_ψu_Xu] using hraw
  have hspXpowXu_cases :
      Section1.scalarProduct G Xpow (T1 Xu) = 0 ∨
        Section1.scalarProduct G Xpow (T1 Xu) = 1 := by
    exact hscalar_zero_or_one_of_same_sign hXpowEq hTXueq hμXpow hμXu
  have hspψpowXu_cases :
      Section1.scalarProduct G ψpow (T1 Xu) = 0 ∨
        Section1.scalarProduct G ψpow (T1 Xu) = 1 := by
    exact hscalar_zero_or_one_of_same_sign hψpowEq hTXueq hμψpow hμXu
  have hspXpowXu : Section1.scalarProduct G Xpow (T1 Xu) = 1 := by
    rcases hspXpowXu_cases with hX0 | hX1
    · rcases hspψpowXu_cases with hψ0 | hψ1
      · have hcontra : (0 : ℂ) = (nψ : ℂ) := by
          simpa [hX0, hψ0] using hspEq
        have hcontraNat : nψ = 0 := by
          exact_mod_cast hcontra.symm
        exfalso
        exact (Nat.ne_of_gt hnψpos) hcontraNat
      · have hcontra : (-(nX : ℂ)) = (nψ : ℂ) := by
          simpa [hX0, hψ1] using hspEq
        have hcontraRe : -(nX : ℝ) = nψ := by
          simpa using congrArg Complex.re hcontra
        have hnXR : (0 : ℝ) < nX := by exact_mod_cast hnXpos
        have hnψR : (0 : ℝ) < nψ := by exact_mod_cast hnψpos
        exfalso
        nlinarith
    · rcases hspψpowXu_cases with hψ0 | hψ1
      · exact hX1
      · have hcontra : ((nψ : ℂ) - (nX : ℂ)) = (nψ : ℂ) := by
          simpa [hX1, hψ1] using hspEq
        have hcontraRe : (nψ : ℝ) - nX = nψ := by
          simpa using congrArg Complex.re hcontra
        have hnXR : (0 : ℝ) < nX := by exact_mod_cast hnXpos
        exfalso
        nlinarith
  have hXu_eq_pow : T1 Xu = Xpow :=
    signed_irreducible_eq_of_scalarProduct_eq_one_pf59 hTXpowSigned hT1Xu_signed hspXpowXu
  intro g
  simpa [Xpow] using congrArg (fun η : Section1.ClassFunction G => η g) hXu_eq_pow


end CFSG.Section5
