module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection4.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_7_Core
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_5

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 4, Proposition (4.1)

This file formalizes the opening orthogonality lemma of PF section 4.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section4

universe u v

/-! ## (4.1) -/

/--
Peterfalvi (4.1): if four signed irreducible characters satisfy the two
orthogonality assumptions, the mixed scalar-product relation, and the two
degree-at-identity equalities from the book, then they are pairwise
orthogonal.
-/
@[expose] public def proposition_4_1_statement
    {X : Type u} [Group X] [Finite X]
    (α β γ δ : Section1.ClassFunction X) (u v : ℝ) : Prop :=
  Section3.IsSignedIrreducibleCharacter α →
    Section3.IsSignedIrreducibleCharacter β →
    Section3.IsSignedIrreducibleCharacter γ →
    Section3.IsSignedIrreducibleCharacter δ →
    u ≠ 0 →
    v ≠ 0 →
    Section1.scalarProduct X α β = 0 →
    Section1.scalarProduct X γ δ = 0 →
    Section1.scalarProduct X (α - β) (((u : ℂ) • γ) - ((v : ℂ) • δ)) = 0 →
    Section1.degree (α - β) = 0 →
    Section1.degree (((u : ℂ) • γ) - ((v : ℂ) • δ)) = 0 →
    pairwiseOrthogonal4 α β γ δ


private noncomputable def uliftRepresentation_pf41
    {X : Type u} [Group X] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ X V) :
    Representation ℂ X (ULift.{u} V) := by
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

private theorem uliftRepresentation_pf41_character
    {X : Type u} [Group X] {V : Type v}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ X V) (g : X) :
    (uliftRepresentation_pf41 (X := X) (V := V) ρ).character g = ρ.character g := by
  dsimp [uliftRepresentation_pf41, Representation.character]
  exact LinearMap.trace_conj' (R := ℂ) (M := V)
    (N := ULift.{u} V) (ρ g) (ULift.moduleEquiv.symm)

private theorem isBookIrreducibleCharacter_of_group_irreducible_pf41
    {X : Type u} [Group X] [Finite X]
    {χ : Section1.ClassFunction X}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsBookIrreducibleCharacter χ := by
  rcases hχ with ⟨n, ρ, hirr, hchar⟩
  constructor
  · refine ⟨ULift.{u} (Fin n → ℂ), inferInstance, inferInstance, inferInstance,
      uliftRepresentation_pf41 (X := X) (V := Fin n → ℂ) ρ, ?_⟩
    ext g
    simpa [hchar] using
      (uliftRepresentation_pf41_character (X := X) (V := Fin n → ℂ) (ρ := ρ) g).symm
  · rw [Section1.IsIrreducibleCharacter]
    have hρclass : Section1.IsClassFunction ρ.character :=
      by
        intro x g
        simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
    have htoeq :
        Section1.toConjClassFunction ρ.character hρclass =
          Theory.Character.characterClassFunction ρ := by
      apply Section1.toConjClassFunction_eq_of_apply
      intro g
      rfl
    calc
      Section1.scalarProduct X χ χ =
          Section1.scalarProduct X ρ.character ρ.character := by rw [hchar]
      _ = Theory.Character.classFunctionInner
          (Section1.toConjClassFunction ρ.character hρclass)
          (Section1.toConjClassFunction ρ.character hρclass) :=
        (Section1.classFunctionInner_toConjClassFunction
          ρ.character ρ.character hρclass hρclass).symm
      _ = Theory.Character.classFunctionInner
          (Theory.Character.characterClassFunction ρ)
          (Theory.Character.characterClassFunction ρ) := by rw [htoeq]
      _ = 1 :=
        (Theory.Character.irreducible_iff_character_norm_one (ρ := ρ)).1 hirr

private theorem scalarProduct_signed_irreducible_ne_zero_iff_pf41
    {X : Type u} [Group X] [Finite X]
    {χ ψ : Section1.ClassFunction X}
    (hχ : Section3.IsSignedIrreducibleCharacter χ)
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ) :
    Section1.scalarProduct X χ ψ ≠ 0 ↔
      ∃ ε : ℂ, Section1.IsSign ε ∧ χ = ε • ψ := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  have hμ_book := isBookIrreducibleCharacter_of_group_irreducible_pf41 hμ
  have hψ_book := isBookIrreducibleCharacter_of_group_irreducible_pf41 hψ
  constructor
  · intro hsp
    by_cases hμψ : μ = ψ
    · exact ⟨ε, hε, by simp [hμψ]⟩
    · have hzeroμ : Section1.scalarProduct X μ ψ = 0 := by
        exact Section1.scalarProduct_isBookIrreducible_ne μ ψ hμ_book hψ_book hμψ
      have hzero :
          Section1.scalarProduct X (ε • μ) ψ = 0 := by
        rw [Section1.scalarProduct_smul_left, hzeroμ]
        simp
      exact (hsp hzero).elim
  · rintro ⟨ε', hε', hEq⟩
    rcases hε' with rfl | rfl
    · have hself : Section1.scalarProduct X ψ ψ = (1 : ℂ) := by
        simpa [Section1.IsIrreducibleCharacter] using
          (isBookIrreducibleCharacter_of_group_irreducible_pf41 hψ).2
      rw [hEq, Section1.scalarProduct_smul_left, hself]
      rcases hε with rfl | rfl <;> norm_num
    · have hself : Section1.scalarProduct X ψ ψ = (1 : ℂ) := by
        simpa [Section1.IsIrreducibleCharacter] using
          (isBookIrreducibleCharacter_of_group_irreducible_pf41 hψ).2
      rw [hEq, Section1.scalarProduct_smul_left, hself]
      rcases hε with rfl | rfl <;> norm_num

private theorem scalarProduct_self_signed_irreducible_pf41
    {X : Type u} [Group X] [Finite X]
    {χ : Section1.ClassFunction X}
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    Section1.scalarProduct X χ χ = 1 := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  rcases hμ with ⟨n, ρ, hρ, hchar⟩
  have hself : Section1.scalarProduct X μ μ = 1 := by
    simpa [hchar] using Section1.scalarProduct_representation_char_self (G := X) ρ hρ
  rcases hε with rfl | rfl
  · simpa using hself
  · calc
      Section1.scalarProduct X ((-1 : ℂ) • μ) ((-1 : ℂ) • μ)
          = Section1.scalarProduct X μ μ := by
              rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
              simp
      _ = 1 := hself


private theorem degree_ne_zero_of_signed_irreducible_pf41
    {X : Type u} [Group X] [Finite X]
    {χ : Section1.ClassFunction X}
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    Section1.degree χ ≠ 0 := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  have hμ_ne : Section1.degree μ ≠ 0 :=
    Section3.degree_ne_zero_of_isIrreducibleCharacterOnGroup μ hμ
  rcases hε with rfl | rfl
  · simpa using hμ_ne
  · simpa [Section1.degree] using neg_ne_zero.mpr hμ_ne

private theorem signed_irreducible_eq_sign_smul_of_scalarProduct_ne_zero_pf41
    {X : Type u} [Group X] [Finite X]
    {X1 Y1 : Section1.ClassFunction X}
    (hX1 : Section3.IsSignedIrreducibleCharacter X1)
    (hY1 : Section3.IsSignedIrreducibleCharacter Y1)
    (hXY : Section1.scalarProduct X X1 Y1 ≠ 0) :
    ∃ ε : ℂ, Section1.IsSign ε ∧ X1 = ε • Y1 := by
  rcases hY1 with ⟨δ, hδ, ψ, hψ, rfl⟩
  have hXψ : Section1.scalarProduct X X1 ψ ≠ 0 := by
    intro hzero
    apply hXY
    rw [Section1.scalarProduct_smul_right, hzero]
    simp
  rcases (scalarProduct_signed_irreducible_ne_zero_iff_pf41 hX1 hψ).1 hXψ with
    ⟨ε, hε, hEq⟩
  rcases hδ with rfl | rfl
  · exact ⟨ε, hε, by simpa using hEq⟩
  · refine ⟨-ε, ?_, ?_⟩
    · rcases hε with rfl | rfl <;> simp [Section1.IsSign]
    · simpa [smul_smul] using hEq

private theorem eq_sign_smul_symm_pf41
    {X : Type u} [Group X] [Finite X]
    {φ ψ : Section1.ClassFunction X} {ε : ℂ}
    (hε : Section1.IsSign ε)
    (h : φ = ε • ψ) :
    ψ = ε • φ := by
  rcases hε with rfl | rfl
  · simpa using h.symm
  · have h' : (-1 : ℂ) • φ = ψ := by
      calc
        (-1 : ℂ) • φ = (-1 : ℂ) • ((-1 : ℂ) • ψ) := by rw [h]
        _ = ψ := by simp
    simpa using h'.symm

private theorem orthogonal_reverse_of_signed_irreducible_pf41
    {X : Type u} [Group X] [Finite X]
    {χ ψ : Section1.ClassFunction X}
    (hχ : Section3.IsSignedIrreducibleCharacter χ)
    (hψ : Section3.IsSignedIrreducibleCharacter ψ)
    (hχψ : Section1.scalarProduct X χ ψ = 0) :
    Section1.scalarProduct X ψ χ = 0 := by
  by_contra hψχ
  rcases signed_irreducible_eq_sign_smul_of_scalarProduct_ne_zero_pf41 hψ hχ hψχ with
    ⟨ε, hε, hEq⟩
  have hself : Section1.scalarProduct X χ χ = 1 :=
    scalarProduct_self_signed_irreducible_pf41 hχ
  rw [hEq, Section1.scalarProduct_smul_right, hself] at hχψ
  rcases hε with rfl | rfl <;> simp at hχψ

private theorem scalarProduct_add_right_pf41
    {X : Type u} [Finite X]
    (φ ψ1 ψ2 : Section1.ClassFunction X) :
    Section1.scalarProduct X φ (ψ1 + ψ2) =
      Section1.scalarProduct X φ ψ1 + Section1.scalarProduct X φ ψ2 := by
  simp [Section1.scalarProduct, mul_add, Finset.sum_add_distrib]

private theorem scalarProduct_sub_left_pf41
    {X : Type u} [Finite X]
    (φ1 φ2 ψ : Section1.ClassFunction X) :
    Section1.scalarProduct X (φ1 - φ2) ψ =
      Section1.scalarProduct X φ1 ψ - Section1.scalarProduct X φ2 ψ := by
  calc
    Section1.scalarProduct X (φ1 - φ2) ψ
        = Section1.scalarProduct X (φ1 + (-1 : ℂ) • φ2) ψ := by
            congr 1
            ext g
            simp [sub_eq_add_neg]
    _ = Section1.scalarProduct X φ1 ψ +
          Section1.scalarProduct X ((-1 : ℂ) • φ2) ψ := by
            rw [Section1.scalarProduct_add_left]
    _ = Section1.scalarProduct X φ1 ψ - Section1.scalarProduct X φ2 ψ := by
          rw [Section1.scalarProduct_smul_left]
          simp [sub_eq_add_neg]

private theorem scalarProduct_sub_right_pf41
    {X : Type u} [Finite X]
    (φ ψ1 ψ2 : Section1.ClassFunction X) :
    Section1.scalarProduct X φ (ψ1 - ψ2) =
      Section1.scalarProduct X φ ψ1 - Section1.scalarProduct X φ ψ2 := by
  calc
    Section1.scalarProduct X φ (ψ1 - ψ2)
        = Section1.scalarProduct X φ (ψ1 + (-1 : ℂ) • ψ2) := by
            congr 1
            ext g
            simp [sub_eq_add_neg]
    _ = Section1.scalarProduct X φ ψ1 +
          Section1.scalarProduct X φ ((-1 : ℂ) • ψ2) := by
            rw [scalarProduct_add_right_pf41]
    _ = Section1.scalarProduct X φ ψ1 - Section1.scalarProduct X φ ψ2 := by
          rw [Section1.scalarProduct_smul_right]
          simp [sub_eq_add_neg]

private theorem proposition_4_1_core_cross_zero_pf41
    {X : Type u} [Group X] [Finite X]
    {X1 X2 Y1 Y2 : Section1.ClassFunction X}
    {u v : ℝ}
    (hX1 : Section3.IsSignedIrreducibleCharacter X1)
    (hX2 : Section3.IsSignedIrreducibleCharacter X2)
    (hY1 : Section3.IsSignedIrreducibleCharacter Y1)
    (hY2 : Section3.IsSignedIrreducibleCharacter Y2)
    (hu : u ≠ 0) (_hv : v ≠ 0)
    (hX12 : Section1.scalarProduct X X1 X2 = 0)
    (hY12 : Section1.scalarProduct X Y1 Y2 = 0)
    (hcross : Section1.scalarProduct X (X1 - X2)
        (((u : ℂ) • Y1) - ((v : ℂ) • Y2)) = 0)
    (hdegX : Section1.degree (X1 - X2) = 0)
    (hdegY : Section1.degree (((u : ℂ) • Y1) - ((v : ℂ) • Y2)) = 0) :
    Section1.scalarProduct X X1 Y1 = 0 := by
  by_contra hX1Y1
  rcases signed_irreducible_eq_sign_smul_of_scalarProduct_ne_zero_pf41 hX1 hY1 hX1Y1 with
    ⟨ε, hε, hX1eq⟩
  have hY1eq : Y1 = ε • X1 := eq_sign_smul_symm_pf41 hε hX1eq
  have hselfX1 : Section1.scalarProduct X X1 X1 = 1 :=
    scalarProduct_self_signed_irreducible_pf41 hX1
  have hselfX2 : Section1.scalarProduct X X2 X2 = 1 :=
    scalarProduct_self_signed_irreducible_pf41 hX2
  have hX2X1 : Section1.scalarProduct X X2 X1 = 0 :=
    orthogonal_reverse_of_signed_irreducible_pf41 hX1 hX2 hX12
  have hX1Y2 : Section1.scalarProduct X X1 Y2 = 0 := by
    have h := hY12
    rw [hY1eq, Section1.scalarProduct_smul_left] at h
    rcases hε with rfl | rfl <;> simpa using h
  have hX2Y1 : Section1.scalarProduct X X2 Y1 = 0 := by
    rw [hY1eq, Section1.scalarProduct_smul_right, hX2X1]
    simp
  have hcross_expand :
      Section1.scalarProduct X X1 ((u : ℂ) • Y1) -
        Section1.scalarProduct X X2 ((u : ℂ) • Y1) -
        (Section1.scalarProduct X X1 ((v : ℂ) • Y2) -
          Section1.scalarProduct X X2 ((v : ℂ) • Y2)) = 0 := by
    simpa [scalarProduct_sub_left_pf41, scalarProduct_sub_right_pf41] using hcross
  have hX2Y2_ne : Section1.scalarProduct X X2 Y2 ≠ 0 := by
    intro hX2Y2
    rcases hε with rfl | rfl
    · have hu0 : (u : ℂ) = 0 := by
        have h1 : Section1.scalarProduct X X1 ((u : ℂ) • X1) = (u : ℂ) := by
          rw [Section1.scalarProduct_smul_right, hselfX1]
          simp
        have h2 : Section1.scalarProduct X X2 ((u : ℂ) • X1) = 0 := by
          rw [Section1.scalarProduct_smul_right, hX2X1]
          simp
        have h3 : Section1.scalarProduct X X1 ((v : ℂ) • Y2) = 0 := by
          rw [Section1.scalarProduct_smul_right, hX1Y2]
          simp
        have h4 : Section1.scalarProduct X X2 ((v : ℂ) • Y2) = 0 := by
          rw [Section1.scalarProduct_smul_right, hX2Y2]
          simp
        have htmp :
            Section1.scalarProduct X X1 ((u : ℂ) • X1) -
              Section1.scalarProduct X X2 ((u : ℂ) • X1) -
              (Section1.scalarProduct X X1 ((v : ℂ) • Y2) -
                Section1.scalarProduct X X2 ((v : ℂ) • Y2)) = 0 := by
          simpa [hY1eq, smul_smul] using hcross_expand
        rw [h1, h2, h3, h4] at htmp
        simpa using htmp
      exact hu (by exact_mod_cast hu0)
    · have hu0 : -(u : ℂ) = 0 := by
        have h1 : Section1.scalarProduct X X1 ((u : ℂ) • Y1) = -(u : ℂ) := by
          rw [hY1eq, smul_smul, Section1.scalarProduct_smul_right, hselfX1]
          simp
        have h2 : Section1.scalarProduct X X2 ((u : ℂ) • Y1) = 0 := by
          rw [hY1eq, smul_smul, Section1.scalarProduct_smul_right, hX2X1]
          simp
        have h3 : Section1.scalarProduct X X1 ((v : ℂ) • Y2) = 0 := by
          rw [Section1.scalarProduct_smul_right, hX1Y2]
          simp
        have h4 : Section1.scalarProduct X X2 ((v : ℂ) • Y2) = 0 := by
          rw [Section1.scalarProduct_smul_right, hX2Y2]
          simp
        have htmp :
            Section1.scalarProduct X X1 ((u : ℂ) • Y1) -
              Section1.scalarProduct X X2 ((u : ℂ) • Y1) -
              (Section1.scalarProduct X X1 ((v : ℂ) • Y2) -
                Section1.scalarProduct X X2 ((v : ℂ) • Y2)) = 0 := by
          simpa using hcross_expand
        rw [h1, h2, h3, h4] at htmp
        simpa using htmp
      exact hu (by exact_mod_cast neg_eq_zero.mp hu0)
  rcases signed_irreducible_eq_sign_smul_of_scalarProduct_ne_zero_pf41 hX2 hY2 hX2Y2_ne with
    ⟨η, hη, hX2eq⟩
  have hY2eq : Y2 = η • X2 := eq_sign_smul_symm_pf41 hη hX2eq
  have hdegXeq : Section1.degree X1 = Section1.degree X2 := by
    simpa [Section1.degree, sub_eq_zero] using hdegX
  have hdegX1_ne : Section1.degree X1 ≠ 0 :=
    degree_ne_zero_of_signed_irreducible_pf41 hX1
  have hsum_ne : Section1.degree X1 + Section1.degree X2 ≠ 0 := by
    intro hsum0
    have htwo : (2 : ℂ) * Section1.degree X1 = 0 := by
      calc
        (2 : ℂ) * Section1.degree X1
            = Section1.degree X1 + Section1.degree X2 := by
                rw [hdegXeq]
                ring
        _ = 0 := hsum0
    exact (mul_ne_zero (by norm_num) hdegX1_ne) htwo
  rcases hε with rfl | rfl <;> rcases hη with rfl | rfl
  · have huv0 : ((u : ℂ) + (v : ℂ)) = 0 := by
      have h1 : Section1.scalarProduct X X1 ((u : ℂ) • X1) = (u : ℂ) := by
        rw [Section1.scalarProduct_smul_right, hselfX1]
        simp
      have h2 : Section1.scalarProduct X X2 ((u : ℂ) • X1) = 0 := by
        rw [Section1.scalarProduct_smul_right, hX2X1]
        simp
      have h3 : Section1.scalarProduct X X1 ((v : ℂ) • X2) = 0 := by
        rw [Section1.scalarProduct_smul_right, hX12]
        simp
      have h4 : Section1.scalarProduct X X2 ((v : ℂ) • X2) = (v : ℂ) := by
        rw [Section1.scalarProduct_smul_right, hselfX2]
        simp
      have htmp :
          (u : ℂ) - 0 - (0 - (v : ℂ)) = 0 := by
        have htmp' :
            Section1.scalarProduct X X1 ((u : ℂ) • X1) -
              Section1.scalarProduct X X2 ((u : ℂ) • X1) -
              (Section1.scalarProduct X X1 ((v : ℂ) • X2) -
                Section1.scalarProduct X X2 ((v : ℂ) • X2)) = 0 := by
          simpa [hY1eq, hY2eq, smul_smul] using hcross_expand
        rw [h1, h2, h3, h4] at htmp'
        simpa using htmp'
      ring_nf at htmp
      exact htmp
    have huv : v = -u := by
      have huvR : u + v = 0 := by exact_mod_cast huv0
      linarith
    have hsum : (u : ℂ) * (Section1.degree X1 + Section1.degree X2) = 0 := by
      have hdeg : (u : ℂ) * Section1.degree X1 - (v : ℂ) * Section1.degree X2 = 0 := by
        simpa [hY1eq, hY2eq, Section1.degree, smul_smul, mul_assoc] using hdegY
      rw [show (v : ℂ) = -((u : ℂ)) by exact_mod_cast huv] at hdeg
      simpa [sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc] using hdeg
    have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu
    exact (mul_ne_zero huC hsum_ne) hsum
  · have huv0 : ((u : ℂ) - (v : ℂ)) = 0 := by
      have h1 : Section1.scalarProduct X X1 ((u : ℂ) • X1) = (u : ℂ) := by
        rw [Section1.scalarProduct_smul_right, hselfX1]
        simp
      have h2 : Section1.scalarProduct X X2 ((u : ℂ) • X1) = 0 := by
        rw [Section1.scalarProduct_smul_right, hX2X1]
        simp
      have h3 : Section1.scalarProduct X X1 ((v : ℂ) • Y2) = 0 := by
        rw [hY2eq, smul_smul, Section1.scalarProduct_smul_right, hX12]
        simp
      have h4 : Section1.scalarProduct X X2 ((v : ℂ) • Y2) = -(v : ℂ) := by
        rw [hY2eq, smul_smul, Section1.scalarProduct_smul_right, hselfX2]
        simp
      have htmp :
          (u : ℂ) - 0 - (0 - (-(v : ℂ))) = 0 := by
        have htmp' :
            Section1.scalarProduct X X1 ((u : ℂ) • X1) -
              Section1.scalarProduct X X2 ((u : ℂ) • X1) -
              (Section1.scalarProduct X X1 ((v : ℂ) • Y2) -
                Section1.scalarProduct X X2 ((v : ℂ) • Y2)) = 0 := by
          simpa [hY1eq, hY2eq, smul_smul] using hcross_expand
        rw [h1, h2, h3, h4] at htmp'
        simpa using htmp'
      ring_nf at htmp
      exact htmp
    have huv : v = u := by
      have huvR : u - v = 0 := by exact_mod_cast huv0
      linarith
    have hsum : (u : ℂ) * (Section1.degree X1 + Section1.degree X2) = 0 := by
      have hdeg : (u : ℂ) * Section1.degree X1 - ((-(v : ℂ))) * Section1.degree X2 = 0 := by
        simpa [hY1eq, hY2eq, Section1.degree, smul_smul, mul_assoc] using hdegY
      rw [show (v : ℂ) = (u : ℂ) by exact_mod_cast huv] at hdeg
      simpa [sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc] using hdeg
    have huC : (u : ℂ) ≠ 0 := by exact_mod_cast hu
    exact (mul_ne_zero huC hsum_ne) hsum
  · have huv0 : ((-(u : ℂ)) + (v : ℂ)) = 0 := by
      have h1 : Section1.scalarProduct X X1 ((u : ℂ) • Y1) = -(u : ℂ) := by
        rw [hY1eq, smul_smul, Section1.scalarProduct_smul_right, hselfX1]
        simp
      have h2 : Section1.scalarProduct X X2 ((u : ℂ) • Y1) = 0 := by
        rw [hY1eq, smul_smul, Section1.scalarProduct_smul_right, hX2X1]
        simp
      have h3 : Section1.scalarProduct X X1 ((v : ℂ) • X2) = 0 := by
        rw [Section1.scalarProduct_smul_right, hX12]
        simp
      have h4 : Section1.scalarProduct X X2 ((v : ℂ) • X2) = (v : ℂ) := by
        rw [Section1.scalarProduct_smul_right, hselfX2]
        simp
      have htmp :
          (-(u : ℂ)) - 0 - (0 - (v : ℂ)) = 0 := by
        have htmp' :
            Section1.scalarProduct X X1 ((u : ℂ) • Y1) -
              Section1.scalarProduct X X2 ((u : ℂ) • Y1) -
              (Section1.scalarProduct X X1 ((v : ℂ) • X2) -
                Section1.scalarProduct X X2 ((v : ℂ) • X2)) = 0 := by
          simpa [hY1eq, hY2eq, smul_smul] using hcross_expand
        rw [h1, h2, h3, h4] at htmp'
        simpa using htmp'
      ring_nf at htmp
      exact htmp
    have huv : v = u := by
      have huvR : -u + v = 0 := by exact_mod_cast huv0
      linarith
    have hsum : (-(u : ℂ)) * (Section1.degree X1 + Section1.degree X2) = 0 := by
      have hdeg : (-(u : ℂ)) * Section1.degree X1 - (v : ℂ) * Section1.degree X2 = 0 := by
        simpa [hY1eq, hY2eq, Section1.degree, smul_smul, mul_assoc] using hdegY
      rw [show (v : ℂ) = (u : ℂ) by exact_mod_cast huv] at hdeg
      simpa [sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc] using hdeg
    have huC : (-(u : ℂ)) ≠ 0 := by exact neg_ne_zero.mpr (by exact_mod_cast hu)
    exact (mul_ne_zero huC hsum_ne) hsum
  · have huv0 : ((-(u : ℂ)) - (v : ℂ)) = 0 := by
      have h1 : Section1.scalarProduct X X1 ((u : ℂ) • Y1) = -(u : ℂ) := by
        rw [hY1eq, smul_smul, Section1.scalarProduct_smul_right, hselfX1]
        simp
      have h2 : Section1.scalarProduct X X2 ((u : ℂ) • Y1) = 0 := by
        rw [hY1eq, smul_smul, Section1.scalarProduct_smul_right, hX2X1]
        simp
      have h3 : Section1.scalarProduct X X1 ((v : ℂ) • Y2) = 0 := by
        rw [hY2eq, smul_smul, Section1.scalarProduct_smul_right, hX12]
        simp
      have h4 : Section1.scalarProduct X X2 ((v : ℂ) • Y2) = -(v : ℂ) := by
        rw [hY2eq, smul_smul, Section1.scalarProduct_smul_right, hselfX2]
        simp
      have htmp :
          (-(u : ℂ)) - 0 - (0 - (-(v : ℂ))) = 0 := by
        have htmp' :
            Section1.scalarProduct X X1 ((u : ℂ) • Y1) -
              Section1.scalarProduct X X2 ((u : ℂ) • Y1) -
              (Section1.scalarProduct X X1 ((v : ℂ) • Y2) -
                Section1.scalarProduct X X2 ((v : ℂ) • Y2)) = 0 := by
          simpa [hY1eq, hY2eq, smul_smul] using hcross_expand
        rw [h1, h2, h3, h4] at htmp'
        simpa using htmp'
      ring_nf at htmp
      exact htmp
    have huv : v = -u := by
      have huvR : -u - v = 0 := by exact_mod_cast huv0
      linarith
    have hsum : (-(u : ℂ)) * (Section1.degree X1 + Section1.degree X2) = 0 := by
      have hdeg : (-(u : ℂ)) * Section1.degree X1 - ((-(v : ℂ))) * Section1.degree X2 = 0 := by
        simpa [hY1eq, hY2eq, Section1.degree, smul_smul, mul_assoc] using hdegY
      rw [show (v : ℂ) = -((u : ℂ)) by exact_mod_cast huv] at hdeg
      simpa [sub_eq_add_neg, mul_add, add_comm, add_left_comm, add_assoc] using hdeg
    have huC : (-(u : ℂ)) ≠ 0 := by exact neg_ne_zero.mpr (by exact_mod_cast hu)
    exact (mul_ne_zero huC hsum_ne) hsum

public theorem proposition_4_1
    {X : Type u} [Group X] [Finite X]
    {α β γ δ : Section1.ClassFunction X}
    {u v : ℝ} :
    proposition_4_1_statement α β γ δ u v := by
  intro hα hβ hγ hδ hu hv hαβ hγδ hcross hdegAB hdegGD
  have hnegvC : (((-v : ℝ) : ℂ)) = -((v : ℂ)) := by simp
  have hneguC : (((-u : ℝ) : ℂ)) = -((u : ℂ)) := by simp
  have hswapGD :
      ((((-v) : ℂ) • δ) - (((-u) : ℂ) • γ)) =
        (((u : ℂ) • γ) - ((v : ℂ) • δ)) := by
    ext g
    simp [sub_eq_add_neg, add_comm]
  have hnegAB : β - α = (-1 : ℂ) • (α - β) := by
    ext g
    simp [sub_eq_add_neg]
  have hαγ : Section1.scalarProduct X α γ = 0 := by
    exact proposition_4_1_core_cross_zero_pf41 hα hβ hγ hδ hu hv hαβ hγδ hcross hdegAB hdegGD
  have hαδ : Section1.scalarProduct X α δ = 0 := by
    have hγδ' : Section1.scalarProduct X δ γ = 0 :=
      orthogonal_reverse_of_signed_irreducible_pf41 hγ hδ hγδ
    have hcross' :
        Section1.scalarProduct X (α - β)
          ((((-v : ℝ) : ℂ) • δ) - (((-u : ℝ) : ℂ) • γ)) = 0 := by
      rw [hnegvC, hneguC]
      rw [hswapGD]
      exact hcross
    have hdegGD' :
        Section1.degree
          ((((-v : ℝ) : ℂ) • δ) - (((-u : ℝ) : ℂ) • γ)) = 0 := by
      rw [hnegvC, hneguC]
      rw [hswapGD]
      exact hdegGD
    exact proposition_4_1_core_cross_zero_pf41
      hα hβ hδ hγ (neg_ne_zero.mpr hv) (neg_ne_zero.mpr hu)
      hαβ hγδ' hcross' hdegAB hdegGD'
  have hβγ : Section1.scalarProduct X β γ = 0 := by
    have hβα : Section1.scalarProduct X β α = 0 :=
      orthogonal_reverse_of_signed_irreducible_pf41 hα hβ hαβ
    have hcross' :
        Section1.scalarProduct X (β - α) (((u : ℂ) • γ) - ((v : ℂ) • δ)) = 0 := by
      rw [hnegAB, Section1.scalarProduct_smul_left, hcross]
      simp
    have hdegAB' : Section1.degree (β - α) = 0 := by
      simpa [hnegAB, Section1.degree] using
        congrArg (fun z : ℂ => (-1 : ℂ) * z) hdegAB
    exact proposition_4_1_core_cross_zero_pf41 hβ hα hγ hδ hu hv hβα hγδ hcross' hdegAB' hdegGD
  have hβδ : Section1.scalarProduct X β δ = 0 := by
    have hβα : Section1.scalarProduct X β α = 0 :=
      orthogonal_reverse_of_signed_irreducible_pf41 hα hβ hαβ
    have hγδ' : Section1.scalarProduct X δ γ = 0 :=
      orthogonal_reverse_of_signed_irreducible_pf41 hγ hδ hγδ
    have hcross' :
        Section1.scalarProduct X (β - α)
          ((((-v : ℝ) : ℂ) • δ) - (((-u : ℝ) : ℂ) • γ)) = 0 := by
      rw [hnegvC, hneguC]
      rw [hnegAB, hswapGD, Section1.scalarProduct_smul_left, hcross]
      simp
    have hdegAB' : Section1.degree (β - α) = 0 := by
      simpa [hnegAB, Section1.degree] using
        congrArg (fun z : ℂ => (-1 : ℂ) * z) hdegAB
    have hdegGD' :
        Section1.degree
          ((((-v : ℝ) : ℂ) • δ) - (((-u : ℝ) : ℂ) • γ)) = 0 := by
      rw [hnegvC, hneguC]
      rw [hswapGD]
      exact hdegGD
    exact proposition_4_1_core_cross_zero_pf41
      hβ hα hδ hγ (neg_ne_zero.mpr hv) (neg_ne_zero.mpr hu)
      hβα hγδ' hcross' hdegAB' hdegGD'
  exact ⟨hαβ, hαγ, hαδ, hβγ, hβδ, hγδ⟩

end CFSG.Section4
