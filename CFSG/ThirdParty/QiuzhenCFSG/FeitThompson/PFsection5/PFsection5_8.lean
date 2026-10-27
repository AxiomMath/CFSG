module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.PFsection5_3
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_5
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_9

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 5, Theorem (5.8)

This file isolates PF `(5.8)` as its own proof target.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section5

universe v
universe u

/-! ## (5.8) -/

/--
Proof-support core for PF `(5.8)`, using the expanded `(5.3)(b)` core context
needed by the current formal proof.
-/
@[expose] public def theorem_5_8_core_statement
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (K W1 W2 W H : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (piChar : I → J → Section1.ClassFunction L)
    (xChar : J → Section1.ClassFunction K)
    (deltaSign : J → ℂ)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction L)) : Prop :=
  theorem_5_3_b_core_context_statement
      K W1 W2 W H A i0 j0 ω σL σ piChar xChar deltaSign τ →
    hypothesis_5_2_a_statement S →
      (∃ X : S,
          Section1.IsIrreducibleCharacterOnGroup
            (X : Section1.ClassFunction L)) →
        inducedFromNonkernelFamily_statement K H S →
          ∀ k : J, k ≠ j0 →
              Section4Scratch.piColumn piChar k ∈ S →
                ∀ j : J,
                  Section1.conjugateCharacter
                      (Section4Scratch.piColumn piChar k) =
                    Section4Scratch.piColumn piChar j →
                    ∀ T1 :
                        Section1.ClassFunction L →ₗ[ℂ]
                          Section1.ClassFunction G,
                      isCFLinearIsometryOnSpan S T1 →
                        mapsIntegerSpanToVirtualCharacters S T1 →
                          agreesOnIntegerSpanOn S puncturedSet τ T1 →
                            (T1 (Section4Scratch.piColumn piChar k) =
                                deltaSign k •
                                  Section4Scratch.omegaColumnSigma σ ω k) ∨
                              (T1 (Section4Scratch.piColumn piChar k) =
                                  (-deltaSign k) •
                                    Section4Scratch.omegaColumnSigma σ ω j ∧
                                ∀ l : J, l ≠ j0 →
                                  Section4Scratch.piColumn piChar l ∈ S →
                                    Section1.degree
                                        (Section4Scratch.piColumn
                                          piChar l) =
                                      Section1.degree
                                        (Section4Scratch.piColumn
                                          piChar k) →
                                      l = j ∨ l = k)

/--
Peterfalvi `(5.8)`: assuming the source hypotheses of `(5.3)(b)`,
`S ∩ Irr(L) ≠ ∅`, and `μₖ ∈ S` for some non-base column `k`, any coherent
extension on `Z[S]` sends `μₖ` either to the signed `k`-column of `ω^σ`, or
to the signed conjugate column; in the second case, `j` and `k` are the only
non-base columns of the same degree that still lie in `S`.
-/
@[expose] public def theorem_5_8_statement
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G) [Finite L]
    (K W1 W2 W H : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (piChar : I → J → Section1.ClassFunction L)
    (xChar : J → Section1.ClassFunction K)
    (deltaSign : J → ℂ)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (H_A H_A0 : G → Subgroup G)
    (S : Finset (Section1.ClassFunction L)) : Prop :=
  Section4Scratch.hypothesis_4_6_full_statement
      L K W1 W2 W H A i0 j0 ω σL σ piChar xChar deltaSign τ H_A H_A0 →
    hypothesis_5_2_a_statement S →
      (∃ X : S,
          Section1.IsIrreducibleCharacterOnGroup
            (X : Section1.ClassFunction L)) →
        inducedFromNonkernelFamily_statement K H S →
          ∀ k : J, k ≠ j0 →
              Section4Scratch.piColumn piChar k ∈ S →
                ∀ j : J,
                  Section1.conjugateCharacter
                      (Section4Scratch.piColumn piChar k) =
                    Section4Scratch.piColumn piChar j →
                    ∀ T1 :
                        Section1.ClassFunction L →ₗ[ℂ]
                          Section1.ClassFunction G,
                      isCFLinearIsometryOnSpan S T1 →
                        mapsIntegerSpanToVirtualCharacters S T1 →
                          agreesOnIntegerSpanOn S puncturedSet τ T1 →
                            (T1 (Section4Scratch.piColumn piChar k) =
                                deltaSign k •
                                  Section4Scratch.omegaColumnSigma σ ω k) ∨
                              (T1 (Section4Scratch.piColumn piChar k) =
                                  (-deltaSign k) •
                                    Section4Scratch.omegaColumnSigma σ ω j ∧
                                ∀ l : J, l ≠ j0 →
                                  Section4Scratch.piColumn piChar l ∈ S →
                                    Section1.degree
                                        (Section4Scratch.piColumn
                                          piChar l) =
                                      Section1.degree
                                        (Section4Scratch.piColumn
                                          piChar k) →
                                      l = j ∨ l = k)


private noncomputable def uliftRepresentation_pf58
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

private theorem uliftRepresentation_pf58_character
    {G : Type u} [Group G] {V : Type}
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (g : G) :
    (uliftRepresentation_pf58 (G := G) (V := V) ρ).character g = ρ.character g := by
  dsimp [uliftRepresentation_pf58, Representation.character]
  exact LinearMap.trace_conj' (R := ℂ) (M := V)
    (N := ULift.{u} V) (ρ g) (ULift.moduleEquiv.symm)

private theorem isCharacter_of_isIrreducibleCharacterOnGroup_pf58
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsCharacter χ := by
  rcases hχ with ⟨n, ρ, _hirr, hchar⟩
  refine ⟨ULift.{u} (Fin n → ℂ), inferInstance, inferInstance, inferInstance,
    uliftRepresentation_pf58 (G := G) (V := Fin n → ℂ) ρ, ?_⟩
  ext g
  simpa [hchar] using
    (uliftRepresentation_pf58_character (G := G) (V := Fin n → ℂ) (ρ := ρ) g).symm

private theorem isBookIrreducibleCharacter_of_group_irreducible_pf58
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.IsBookIrreducibleCharacter χ := by
  rcases hχ with ⟨n, ρ, hirr, hchar⟩
  constructor
  · exact isCharacter_of_isIrreducibleCharacterOnGroup_pf58 ⟨n, ρ, hirr, hchar⟩
  · rw [Section1.IsIrreducibleCharacter]
    have hρclass : Section1.IsClassFunction ρ.character := by
      intro x g
      simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
    have htoeq :
        Section1.toConjClassFunction ρ.character hρclass =
          Theory.Character.characterClassFunction ρ := by
      apply Section1.toConjClassFunction_eq_of_apply
      intro g
      rfl
    calc
      Section1.scalarProduct G χ χ =
          Section1.scalarProduct G ρ.character ρ.character := by rw [hchar]
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

private theorem scalarProduct_zero_of_distinct_irreducibles_pf58
    {G : Type u} [Group G] [Finite G]
    {χ ψ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ)
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hneq : χ ≠ ψ) :
    Section1.scalarProduct G χ ψ = 0 := by
  exact Section1.scalarProduct_isBookIrreducible_ne χ ψ
    (isBookIrreducibleCharacter_of_group_irreducible_pf58 hχ)
    (isBookIrreducibleCharacter_of_group_irreducible_pf58 hψ)
    hneq

private theorem integerSpan_of_mem_pf58
    {H : Type*} [Group H] [Finite H]
    (S : Finset (Section1.ClassFunction H))
    {χ : Section1.ClassFunction H}
    (hχ : χ ∈ S) :
    integerSpan S χ := by
  classical
  refine ⟨Section1.basisVector ⟨χ, hχ⟩, ?_⟩
  ext g
  rw [Section1.evalCoeff, Finset.sum_eq_single ⟨χ, hχ⟩]
  · simp [Section1.basisVector]
  · intro x _hx hxne
    simp [Section1.basisVector, hxne]
  · intro hmem
    exact (hmem (Finset.mem_univ _)).elim

private theorem integerSpan_mono_pf58
    {H : Type*} [Group H]
    {S1 S2 : Finset (Section1.ClassFunction H)}
    (hsub : S1 ⊆ S2)
    {χ : Section1.ClassFunction H} :
    integerSpan S1 χ → integerSpan S2 χ := by
  classical
  rintro ⟨v, rfl⟩
  let w : Section1.CoeffVector S2 := fun y =>
    if hy : (y : Section1.ClassFunction H) ∈ S1 then v ⟨y, hy⟩ else 0
  refine ⟨w, ?_⟩
  ext g
  have hsum := Finset.sum_subset
      (s₁ := S1) (s₂ := S2)
      (f := fun y : Section1.ClassFunction H =>
        (((if hy : y ∈ S1 then v ⟨y, hy⟩ else 0 : Int) : ℂ) * y g))
      hsub
      (by
        intro y hyS2 hyS1
        simp [hyS1])
  simpa +contextual [Section1.evalCoeff, w, smul_eq_mul, ← S1.sum_attach, ← S2.sum_attach] using
    hsum

private theorem integerSpan_add_pf58
    {H : Type*} [Group H]
    {S : Finset (Section1.ClassFunction H)}
    {φ ψ : Section1.ClassFunction H} :
    integerSpan S φ → integerSpan S ψ → integerSpan S (φ + ψ) := by
  classical
  rintro ⟨v, rfl⟩ ⟨w, rfl⟩
  refine ⟨v + w, ?_⟩
  ext g
  simp [Section1.evalCoeff, Finset.sum_add_distrib, add_mul]

private theorem integerSpan_neg_pf58
    {H : Type*} [Group H]
    {S : Finset (Section1.ClassFunction H)}
    {φ : Section1.ClassFunction H} :
    integerSpan S φ → integerSpan S (-φ) := by
  classical
  rintro ⟨v, rfl⟩
  refine ⟨-v, ?_⟩
  ext g
  simp [Section1.evalCoeff]

private theorem integerSpan_sub_pf58
    {H : Type*} [Group H]
    {S : Finset (Section1.ClassFunction H)}
    {φ ψ : Section1.ClassFunction H} :
    integerSpan S φ → integerSpan S ψ → integerSpan S (φ - ψ) := by
  intro hφ hψ
  simpa [sub_eq_add_neg] using integerSpan_add_pf58 hφ (integerSpan_neg_pf58 hψ)

private theorem integerSpanOn_mono_pf58
    {H : Type*} [Group H]
    {S1 S2 : Finset (Section1.ClassFunction H)}
    (hsub : S1 ⊆ S2)
    {A : Set H}
    {χ : Section1.ClassFunction H} :
    integerSpanOn S1 A χ → integerSpanOn S2 A χ := by
  rintro ⟨hχ, hχA⟩
  exact ⟨integerSpan_mono_pf58 hsub hχ, hχA⟩

private theorem isCFLinearIsometryOnSpan_mono_pf58
    {L G : Type u} [Group L] [Finite L] [Group G] [Finite G]
    {S1 S2 : Finset (Section1.ClassFunction L)}
    (hsub : S1 ⊆ S2)
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G} :
    isCFLinearIsometryOnSpan S2 T → isCFLinearIsometryOnSpan S1 T := by
  intro hIso φ ψ hφ hψ
  exact hIso φ ψ (integerSpan_mono_pf58 hsub hφ) (integerSpan_mono_pf58 hsub hψ)

private theorem mapsIntegerSpanToVirtualCharacters_mono_pf58
    {L G : Type u} [Group L] [Group G]
    {S1 S2 : Finset (Section1.ClassFunction L)}
    (hsub : S1 ⊆ S2)
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G} :
    mapsIntegerSpanToVirtualCharacters S2 T →
      mapsIntegerSpanToVirtualCharacters S1 T := by
  intro hvirt χ hχ
  exact hvirt χ (integerSpan_mono_pf58 hsub hχ)

private theorem isCFLinearIsometryOnSpanOn_mono_pf58
    {L G : Type u} [Group L] [Finite L] [Group G] [Finite G]
    {S1 S2 : Finset (Section1.ClassFunction L)}
    (hsub : S1 ⊆ S2)
    {A : Set L}
    {T : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G} :
    isCFLinearIsometryOnSpanOn S2 A T → isCFLinearIsometryOnSpanOn S1 A T := by
  intro hIso φ ψ hφ hψ
  exact hIso φ ψ (integerSpanOn_mono_pf58 hsub hφ) (integerSpanOn_mono_pf58 hsub hψ)

private theorem supportedOn_puncturedSet_iff_degree_eq_zero_pf58
    {H : Type*} [Group H]
    (φ : Section1.ClassFunction H) :
    Section1.supportedOn φ puncturedSet ↔ Section1.degree φ = 0 := by
  constructor
  · intro hSupp
    rw [Section1.degree_apply]
    exact (Section1.supportedOn_iff.mp hSupp) 1 (by simp [puncturedSet])
  · intro hdeg
    rw [Section1.supportedOn_iff]
    intro g hg
    have hg1 : g = 1 := by
      by_contra hne
      exact hg (by simp [puncturedSet, hne])
    subst hg1
    simpa [Section1.degree_apply] using hdeg

private theorem cfNormSq_eq_inv_card_mul_sum_normSq_pf58
    {H : Type*} [Group H] [Finite H]
    (φ : Section1.ClassFunction H) :
    cfNormSq φ = (Nat.card H : ℝ)⁻¹ * ∑ g : H, Complex.normSq (φ g) := by
  unfold cfNormSq Section1.scalarProduct
  have hcast :
      ((Nat.card H : ℂ)⁻¹) = (((Nat.card H : ℝ)⁻¹ : ℝ) : ℂ) := by
    simp
  rw [hcast, Complex.re_ofReal_mul, Complex.re_sum]
  congr 1
  refine Finset.sum_congr rfl ?_
  intro g _hg
  calc
    Complex.re (φ g * star (φ g))
      = Complex.re (star (φ g) * φ g) := by rw [mul_comm]
    _ = Complex.re ((Complex.normSq (φ g) : ℝ) : ℂ) := by
          congr 1
          simpa using (Complex.normSq_eq_conj_mul_self (z := φ g)).symm
    _ = Complex.normSq (φ g) := by simp

private theorem cfNormSq_eq_zero_pf58
    {H : Type*} [Group H] [Finite H]
    {φ : Section1.ClassFunction H}
    (hφ : cfNormSq φ = 0) :
    φ = 0 := by
  rw [cfNormSq_eq_inv_card_mul_sum_normSq_pf58] at hφ
  have hcardNat : 0 < Nat.card H := Nat.card_pos
  have hcardReal : 0 < (Nat.card H : ℝ) := by exact_mod_cast hcardNat
  have hcard : 0 < (Nat.card H : ℝ)⁻¹ := inv_pos.mpr hcardReal
  have hsumZero : (∑ g : H, Complex.normSq (φ g)) = 0 := by
    nlinarith
  have hzeroAll :
      ∀ g ∈ (Finset.univ : Finset H), Complex.normSq (φ g) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun g _hg => Complex.normSq_nonneg (φ g))).1 hsumZero
  ext g
  exact Complex.normSq_eq_zero.mp (hzeroAll g (by simp))

private theorem sign_smul_sign_smul_eq_self_pf58
    {G : Type*} [Group G]
    {ε : ℂ} (hε : Section1.IsSign ε)
    (φ : Section1.ClassFunction G) :
    ε • (ε • φ) = φ := by
  rcases hε with rfl | rfl <;> ext g <;> simp

private theorem normal_K_of_hypothesis_4_2_pf58
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W) :
    K.Normal := by
  rcases h42 with ⟨hprod, _hHall, _hCyc1, _hne1, _hCyc2, _hne2, _hcent, _hW1, _hW2, _hdir, _hOdd⟩
  refine ⟨?_⟩
  intro n hn g
  rcases hprod.mul_surjective g (by simp : g ∈ (⊤ : Subgroup L)) with ⟨h, hh, k, hk, rfl⟩
  have hkn : Section2.conjBy k n ∈ K := hprod.right_normalizes_left k hk n hn
  simpa [Section2.conjBy, mul_assoc] using
    K.mul_mem hh (K.mul_mem hkn (K.inv_mem hh))

private theorem conjugateCharacter_inducedCF_pf58
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) [Finite H] [H.Normal]
    (theta : Section1.ClassFunction H) :
    Section1.conjugateCharacter (Section1.inducedCF H theta) =
      Section1.inducedCF H (Section1.conjugateCharacter theta) := by
  classical
  funext g
  unfold Section1.conjugateCharacter Section1.inducedCF Section1.inducedClassFunction
  calc
    star ((Nat.card H : ℂ)⁻¹ *
        ∑ x : G, (if hx : x * g * x⁻¹ ∈ H then theta ⟨x * g * x⁻¹, hx⟩ else 0))
        =
      (Nat.card H : ℂ)⁻¹ *
        star (∑ x : G, (if hx : x * g * x⁻¹ ∈ H then theta ⟨x * g * x⁻¹, hx⟩ else 0)) := by
          simp
    _ = (Nat.card H : ℂ)⁻¹ *
        ∑ x : G, star (if hx : x * g * x⁻¹ ∈ H then theta ⟨x * g * x⁻¹, hx⟩ else 0) := by
          rw [star_sum]
    _ = (Nat.card H : ℂ)⁻¹ *
        ∑ x : G,
          (if hx : x * g * x⁻¹ ∈ H then
            (Section1.conjugateCharacter theta) ⟨x * g * x⁻¹, hx⟩ else 0) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro x _hx
          by_cases hmem : x * g * x⁻¹ ∈ H
          · simp [hmem]
            rfl
          · simp [hmem]

private theorem base_piChar_sign_principal_pf58
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {deltaSign : J → ℂ}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω) :
    piChar i0 j0 = deltaSign j0 • Section1.principalCharacter L := by
  rcases h43b with ⟨hσmap, hsign, _hirr, _hdistinct, _hind, hSigma⟩
  rcases hσmap with ⟨_hisom, _hvirt, _hagrees, _hclass, hσprincipal, _hcyc, _hvanish⟩
  have hbase :
      Section1.principalCharacter L = deltaSign j0 • piChar i0 j0 := by
    calc
      Section1.principalCharacter L = σL (Section1.principalCharacter W) := by
        symm
        exact hσprincipal
      _ = σL (ω i0 j0) := by rw [hω.principal]
      _ = deltaSign j0 • piChar i0 j0 := hSigma i0 j0
  calc
    piChar i0 j0 = deltaSign j0 • (deltaSign j0 • piChar i0 j0) := by
      symm
      exact sign_smul_sign_smul_eq_self_pf58 (hsign j0) (piChar i0 j0)
    _ = deltaSign j0 • Section1.principalCharacter L := by rw [← hbase]

private theorem base_xChar_sign_principal_pf58
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar) :
    xChar j0 = deltaSign j0 • Section1.principalCharacter K := by
  calc
    xChar j0 = Section1.subgroupRestriction K (piChar i0 j0) := by
      symm
      exact h45a.1 i0 j0
    _ = Section1.subgroupRestriction K (deltaSign j0 • Section1.principalCharacter L) := by
      rw [base_piChar_sign_principal_pf58 hω h43b]
    _ = deltaSign j0 • Section1.subgroupRestriction K (Section1.principalCharacter L) := by
      ext a
      simp [Section1.subgroupRestriction]
    _ = deltaSign j0 • Section1.principalCharacter K := by
      ext a
      simp [Section1.subgroupRestriction, Section1.principalCharacter]

private theorem base_piColumn_conjugate_self_pf58
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    (h42 : Section4.hypothesis_4_2_statement K W1 W2 W)
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
  (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar) :
    Section1.conjugateCharacter (Section4Scratch.piColumn piChar j0) =
      Section4Scratch.piColumn piChar j0 := by
  haveI : K.Normal := normal_K_of_hypothesis_4_2_pf58 h42
  have h43b_full := h43b
  rcases h43b with ⟨_hσmap, hsign, _hirr, _hdistinct, _hind, _hSigma⟩
  have hprin : Section1.conjugateCharacter (Section1.principalCharacter K) =
      Section1.principalCharacter K := by
    ext a
    simp [Section1.conjugateCharacter, Section1.principalCharacter]
  calc
    Section1.conjugateCharacter (Section4Scratch.piColumn piChar j0) =
        Section1.conjugateCharacter (Section1.inducedCF K (xChar j0)) := by
          rw [← h45a.2.2 j0]
    _ = Section1.inducedCF K (Section1.conjugateCharacter (xChar j0)) := by
          exact conjugateCharacter_inducedCF_pf58 K (xChar j0)
    _ = Section1.inducedCF K (deltaSign j0 • Section1.principalCharacter K) := by
          rw [base_xChar_sign_principal_pf58 hω h43b_full h45a]
          rcases hsign j0 with h1 | hneg
          · rw [h1]
            simp [hprin]
          · rw [hneg]
            congr 1
            ext a
            simp [Section1.conjugateCharacter]
    _ = Section1.inducedCF K (xChar j0) := by
          rw [base_xChar_sign_principal_pf58 hω h43b_full h45a]
    _ = Section4Scratch.piColumn piChar j0 := h45a.2.2 j0

private theorem degree_eq_nat_of_isCharacter_pf58
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsCharacter χ) :
    ∃ d : ℕ, Section1.degree χ = (d : ℂ) := by
  rcases hχ with ⟨V, _hadd, _hmod, _hfd, ρ, rfl⟩
  exact ⟨Module.finrank ℂ V, Section1.degree_representation_character ρ⟩

private theorem degree_conjugateCharacter_eq_of_isCharacter_pf58
    {G : Type u} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsCharacter χ) :
    Section1.degree (Section1.conjugateCharacter χ) = Section1.degree χ := by
  rcases degree_eq_nat_of_isCharacter_pf58 hχ with ⟨d, hd⟩
  calc
    Section1.degree (Section1.conjugateCharacter χ) = star (Section1.degree χ) := by
      simp [Section1.degree, Section1.conjugateCharacter]
    _ = Section1.degree χ := by
      rw [hd]
      simp

private theorem isSign_mul_pf58
    {ε η : ℂ} (hε : Section1.IsSign ε) (hη : Section1.IsSign η) :
    Section1.IsSign (ε * η) := by
  rcases hε with rfl | rfl <;> rcases hη with rfl | rfl <;> simp [Section1.IsSign]

private theorem isSign_neg_pf58 {ε : ℂ}
    (hε : Section1.IsSign ε) :
    Section1.IsSign (-ε) := by
  rcases hε with rfl | rfl <;> simp [Section1.IsSign]

private theorem isSign_ne_zero_pf58 {ε : ℂ}
    (hε : Section1.IsSign ε) :
    ε ≠ 0 := by
  rcases hε with rfl | rfl <;> norm_num

private theorem scalarProduct_zero_smul_both_pf58
    {G : Type*} [Finite G]
    {φ ψ : Section1.ClassFunction G} {z w : ℂ}
    (h : Section1.scalarProduct G φ ψ = 0) :
    Section1.scalarProduct G (z • φ) (w • ψ) = 0 := by
  rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right, h]
  simp

private theorem scalarProduct_add_right_pf58
    {G : Type*} [Finite G] (φ ψ1 ψ2 : Section1.ClassFunction G) :
    Section1.scalarProduct G φ (ψ1 + ψ2) =
      Section1.scalarProduct G φ ψ1 + Section1.scalarProduct G φ ψ2 := by
  simp [Section1.scalarProduct, mul_add, Finset.sum_add_distrib]

private theorem scalarProduct_sub_right_pf58
    {G : Type*} [Finite G] (φ ψ1 ψ2 : Section1.ClassFunction G) :
    Section1.scalarProduct G φ (ψ1 - ψ2) =
      Section1.scalarProduct G φ ψ1 - Section1.scalarProduct G φ ψ2 := by
  calc
    Section1.scalarProduct G φ (ψ1 - ψ2)
        = Section1.scalarProduct G φ (ψ1 + (-1 : ℂ) • ψ2) := by
            congr 1
            ext g
            simp [sub_eq_add_neg]
    _ = Section1.scalarProduct G φ ψ1 +
          Section1.scalarProduct G φ ((-1 : ℂ) • ψ2) := by
            rw [scalarProduct_add_right_pf58]
    _ = Section1.scalarProduct G φ ψ1 - Section1.scalarProduct G φ ψ2 := by
          rw [Section1.scalarProduct_smul_right]
          simp [sub_eq_add_neg]


private theorem scalarProduct_sub_left_pf58
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

private theorem scalarProduct_sign_smul_self_pf58
    {G : Type*} [Finite G]
    {ε : ℂ} (hε : Section1.IsSign ε)
    {φ : Section1.ClassFunction G}
    (hφ : Section1.scalarProduct G φ φ = 1) :
    Section1.scalarProduct G (ε • φ) (ε • φ) = 1 := by
  rcases hε with rfl | rfl
  · simpa using hφ
  · rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right, hφ]
    simp

private theorem isSignedIrreducibleCharacter_sign_smul_pf58
    {G : Type*} [Group G] [Finite G]
    {ε : ℂ} {φ : Section1.ClassFunction G}
    (hε : Section1.IsSign ε)
    (hφ : Section3.IsSignedIrreducibleCharacter φ) :
    Section3.IsSignedIrreducibleCharacter (ε • φ) := by
  rcases hφ with ⟨η, hη, μ, hμ, rfl⟩
  refine ⟨ε * η, isSign_mul_pf58 hε hη, μ, hμ, ?_⟩
  ext g
  simp [mul_assoc]

private theorem signedOrthonormalFinset_image_pf58
    {G : Type u} [Group G] [Finite G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : ι → Section1.ClassFunction G)
    (hSigned : ∀ i, Section3.IsSignedIrreducibleCharacter (ψ i))
    (hOrth : ∀ i i', i ≠ i' → Section1.scalarProduct G (ψ i) (ψ i') = 0) :
    signedOrthonormalFinset (Finset.univ.image ψ) := by
  constructor
  · intro φ hφ
    rcases Finset.mem_image.mp hφ with ⟨i, _hi, rfl⟩
    exact hSigned i
  · intro φ ψ' hφ hψ hneq
    rcases Finset.mem_image.mp hφ with ⟨i, _hi, rfl⟩
    rcases Finset.mem_image.mp hψ with ⟨i', _hi', rfl⟩
    exact hOrth i i' (by
      intro hii'
      apply hneq
      simp [hii'])

private noncomputable def muSignedFamily_pf58
    {G : Type u} [Group G] [Finite G]
    {I J : Type*}
    (deltaLeft deltaRight : ℂ)
    (chi : I → J → Section1.ClassFunction G)
    (j k : J) :
    I ⊕ I → Section1.ClassFunction G
  | Sum.inl i => deltaLeft • chi i j
  | Sum.inr i => deltaRight • chi i k

private theorem muSignedFamily_signed_pf58
    {G : Type u} [Group G] [Finite G]
    {I J : Type*}
    {deltaLeft deltaRight : ℂ}
    {chi : I → J → Section1.ClassFunction G}
    {j k : J}
    (hLeft : Section1.IsSign deltaLeft)
    (hRight : Section1.IsSign deltaRight)
    (hChiSigned : ∀ i j, Section3.IsSignedIrreducibleCharacter (chi i j)) :
    ∀ p : I ⊕ I,
      Section3.IsSignedIrreducibleCharacter
        (muSignedFamily_pf58 deltaLeft deltaRight chi j k p)
  | Sum.inl i => by
      simpa [muSignedFamily_pf58] using
        isSignedIrreducibleCharacter_sign_smul_pf58 hLeft (hChiSigned i j)
  | Sum.inr i => by
      simpa [muSignedFamily_pf58] using
        isSignedIrreducibleCharacter_sign_smul_pf58 hRight (hChiSigned i k)

private theorem muSignedFamily_orthogonal_pf58
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    {deltaLeft deltaRight : ℂ}
    {chi : I → J → Section1.ClassFunction G}
    {j k : J}
    (hChiOrth : Section3.IsOrthonormalDoubleFamily chi)
    (hjk : j ≠ k) :
    ∀ p q : I ⊕ I, p ≠ q →
      Section1.scalarProduct G
        (muSignedFamily_pf58 deltaLeft deltaRight chi j k p)
        (muSignedFamily_pf58 deltaLeft deltaRight chi j k q) = 0
  | Sum.inl i, Sum.inl i', hpq => by
      have hii' : i ≠ i' := by
        intro h
        apply hpq
        simp [h]
      have hbase : Section1.scalarProduct G (chi i j) (chi i' j) = 0 := by
        simpa [hii'] using hChiOrth (i, j) (i', j)
      simpa [muSignedFamily_pf58] using
        (scalarProduct_zero_smul_both_pf58
          (φ := chi i j) (ψ := chi i' j) (z := deltaLeft) (w := deltaLeft) hbase)
  | Sum.inl i, Sum.inr i', _hpq => by
      have hbase : Section1.scalarProduct G (chi i j) (chi i' k) = 0 := by
        have hpair : (i, j) ≠ (i', k) := by
          intro hEq
          exact hjk (by simpa using congrArg Prod.snd hEq)
        simpa [hpair] using hChiOrth (i, j) (i', k)
      simpa [muSignedFamily_pf58] using
        (scalarProduct_zero_smul_both_pf58
          (φ := chi i j) (ψ := chi i' k) (z := deltaLeft) (w := deltaRight) hbase)
  | Sum.inr i, Sum.inl i', _hpq => by
      have hbase : Section1.scalarProduct G (chi i k) (chi i' j) = 0 := by
        have hpair : (i, k) ≠ (i', j) := by
          intro hEq
          exact hjk (by simpa using (congrArg Prod.snd hEq).symm)
        simpa [hpair] using hChiOrth (i, k) (i', j)
      simpa [muSignedFamily_pf58] using
        (scalarProduct_zero_smul_both_pf58
          (φ := chi i k) (ψ := chi i' j) (z := deltaRight) (w := deltaLeft) hbase)
  | Sum.inr i, Sum.inr i', hpq => by
      have hii' : i ≠ i' := by
        intro h
        apply hpq
        simp [h]
      have hbase : Section1.scalarProduct G (chi i k) (chi i' k) = 0 := by
        simpa [hii'] using hChiOrth (i, k) (i', k)
      simpa [muSignedFamily_pf58] using
        (scalarProduct_zero_smul_both_pf58
          (φ := chi i k) (ψ := chi i' k) (z := deltaRight) (w := deltaRight) hbase)

private theorem muSignedFamily_self_pf58
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    {deltaLeft deltaRight : ℂ}
    {chi : I → J → Section1.ClassFunction G}
    {j k : J}
    (hLeft : Section1.IsSign deltaLeft)
    (hRight : Section1.IsSign deltaRight)
    (hChiOrth : Section3.IsOrthonormalDoubleFamily chi) :
    ∀ p : I ⊕ I,
      Section1.scalarProduct G
        (muSignedFamily_pf58 deltaLeft deltaRight chi j k p)
        (muSignedFamily_pf58 deltaLeft deltaRight chi j k p) = 1
  | Sum.inl i => by
      have hbase : Section1.scalarProduct G (chi i j) (chi i j) = 1 := by
        simpa using hChiOrth (i, j) (i, j)
      simpa [muSignedFamily_pf58] using scalarProduct_sign_smul_self_pf58 hLeft hbase
  | Sum.inr i => by
      have hbase : Section1.scalarProduct G (chi i k) (chi i k) = 1 := by
        simpa using hChiOrth (i, k) (i, k)
      simpa [muSignedFamily_pf58] using scalarProduct_sign_smul_self_pf58 hRight hbase

private theorem muSignedFamily_injective_pf58
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    {deltaLeft deltaRight : ℂ}
    {chi : I → J → Section1.ClassFunction G}
    {j k : J}
    (hLeft : Section1.IsSign deltaLeft)
    (hRight : Section1.IsSign deltaRight)
    (hChiOrth : Section3.IsOrthonormalDoubleFamily chi)
    (hjk : j ≠ k) :
    Function.Injective (muSignedFamily_pf58 deltaLeft deltaRight chi j k) := by
  intro p q hEq
  by_contra hpq
  have hzero :=
      muSignedFamily_orthogonal_pf58
        (deltaLeft := deltaLeft) (deltaRight := deltaRight)
        hChiOrth hjk p q hpq
  have hself :=
      muSignedFamily_self_pf58
        (deltaLeft := deltaLeft) (deltaRight := deltaRight) (chi := chi)
        (j := j) (k := k) hLeft hRight hChiOrth p
  have hzero' :
      Section1.scalarProduct G
        (muSignedFamily_pf58 deltaLeft deltaRight chi j k p)
        (muSignedFamily_pf58 deltaLeft deltaRight chi j k p) = 0 := by
    simpa [hEq] using hzero
  have hcontr : (1 : ℂ) = 0 := by
    simp [hself] at hzero'
  norm_num at hcontr

private theorem muSignedFamily_sum_pf58
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [DecidableEq I]
    {deltaLeft deltaRight : ℂ}
    {chi : I → J → Section1.ClassFunction G}
    {j k : J}
    (hInj : Function.Injective (muSignedFamily_pf58 deltaLeft deltaRight chi j k)) :
    Finset.sum
        (Finset.univ.image (muSignedFamily_pf58 deltaLeft deltaRight chi j k))
        (fun φ => φ) =
      (∑ i : I, deltaLeft • chi i j) + ∑ i : I, deltaRight • chi i k := by
  calc
    Finset.sum
        (Finset.univ.image (muSignedFamily_pf58 deltaLeft deltaRight chi j k))
        (fun φ => φ)
        = ∑ p : I ⊕ I, muSignedFamily_pf58 deltaLeft deltaRight chi j k p := by
            exact Finset.sum_image
              (s := Finset.univ)
              (g := muSignedFamily_pf58 deltaLeft deltaRight chi j k)
              (f := fun φ => φ)
              (by
                intro p _hp q _hq hpq
                exact hInj hpq)
    _ = (∑ i : I, deltaLeft • chi i j) + ∑ i : I, deltaRight • chi i k := by
          simp [muSignedFamily_pf58]

private theorem piColumn_isCharacter_pf58
    {L : Type u} [Group L] [Finite L]
    {K : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar)
    (j : J) :
    Section1.IsCharacter (Section4Scratch.piColumn piChar j) := by
  rcases h45a with ⟨_hres, hIrr, hInd⟩
  rw [← hInd j]
  exact Section1.isCharacter_inducedCF_of_isCharacter K (xChar j)
    (isCharacter_of_isIrreducibleCharacterOnGroup_pf58 (hIrr j))

private theorem degree_piColumn_eq_of_conjugate_pf58
    {L : Type u} [Group L] [Finite L]
    {K : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar)
    {j k : J}
    (hconj :
      Section1.conjugateCharacter (Section4Scratch.piColumn piChar k) =
        Section4Scratch.piColumn piChar j) :
    Section1.degree (Section4Scratch.piColumn piChar j) =
      Section1.degree (Section4Scratch.piColumn piChar k) := by
  calc
    Section1.degree (Section4Scratch.piColumn piChar j) =
        Section1.degree
          (Section1.conjugateCharacter (Section4Scratch.piColumn piChar k)) := by
            rw [hconj]
    _ = Section1.degree (Section4Scratch.piColumn piChar k) :=
      degree_conjugateCharacter_eq_of_isCharacter_pf58
        (piColumn_isCharacter_pf58 h45a k)

private theorem degree_entry_eq_of_equal_degree_column_pf58
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L)
    {I J : Type*} [Fintype I] [Fintype J]
    (piChar : I → J → Section1.ClassFunction L)
    (xChar : J → Section1.ClassFunction K)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar)
    {i : I} {j k : J}
    (hdegCol :
      Section1.degree (Section4Scratch.piColumn piChar j) =
        Section1.degree (Section4Scratch.piColumn piChar k)) :
    Section1.degree (piChar i j) = Section1.degree (piChar i k) := by
  rcases h45a with ⟨hres, _hirrX, hindX⟩
  have hidxC : (Subgroup.index K : ℂ) ≠ 0 := by
    exact_mod_cast Subgroup.index_ne_zero_of_finite (G := L) (H := K)
  have hdegX :
      Section1.degree (xChar j) = Section1.degree (xChar k) := by
    have hmul :
        (Subgroup.index K : ℂ) * Section1.degree (xChar j) =
          (Subgroup.index K : ℂ) * Section1.degree (xChar k) := by
      calc
        (Subgroup.index K : ℂ) * Section1.degree (xChar j)
            = Section1.degree (Section4Scratch.piColumn piChar j) := by
                rw [← hindX j]
                simpa using (Section1.degree_inducedClassFunction K (xChar j)).symm
        _ = Section1.degree (Section4Scratch.piColumn piChar k) := hdegCol
        _ = (Subgroup.index K : ℂ) * Section1.degree (xChar k) := by
              rw [← hindX k]
              simpa using Section1.degree_inducedClassFunction K (xChar k)
    exact mul_left_cancel₀ hidxC hmul
  have hresj := congrFun (hres i j) 1
  have hresk := congrFun (hres i k) 1
  calc
    Section1.degree (piChar i j) = Section1.degree (xChar j) := by
      simpa [Section1.degree, Section1.subgroupRestriction] using hresj
    _ = Section1.degree (xChar k) := hdegX
    _ = Section1.degree (piChar i k) := by
      simpa [Section1.degree, Section1.subgroupRestriction] using hresk.symm

private theorem omegaColumnSigma_eq_sumChi_pf58
    {W : Type*} [Group W] {G : Type*} [Group G]
    {I J : Type*} [Fintype I]
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {chi : I → J → Section1.ClassFunction G}
    (hChiSigma : ∀ i j, σ (ω i j) = chi i j)
    (j : J) :
    Section4Scratch.omegaColumnSigma σ ω j = ∑ i : I, chi i j := by
  simp [Section4Scratch.omegaColumnSigma, hChiSigma]

private theorem scalarProduct_omegaColumnSigma_chi_eq_ite_pf58
    {L : Type u} [Group L]
    {G : Type u} [Group G] [Finite G]
    {W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {chi : I → J → Section1.ClassFunction G}
    (hChiOrth : Section3.IsOrthonormalDoubleFamily chi)
    (hChiSigma : ∀ i j, σ (ω i j) = chi i j)
    (i : I) (j k : J) :
    Section1.scalarProduct G (Section4Scratch.omegaColumnSigma σ ω j) (chi i k) =
      if j = k then 1 else 0 := by
  classical
  rw [omegaColumnSigma_eq_sumChi_pf58 hChiSigma j]
  have hsum :
      ((∑ p : I, chi p j : Section1.ClassFunction G)) =
        fun g => ∑ p : I, chi p j g := by
    ext g
    simp
  rw [hsum, Section1.scalarProduct_fintype_sum_left]
  by_cases hjk : j = k
  · subst k
    calc
      (∑ p : I, Section1.scalarProduct G (chi p j) (chi i j)) =
          ∑ p : I, if (p, j) = (i, j) then (1 : ℂ) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro p _hp
            exact hChiOrth (p, j) (i, j)
      _ = if j = j then (1 : ℂ) else 0 := by simp
  · calc
      (∑ p : I, Section1.scalarProduct G (chi p j) (chi i k)) =
          ∑ p : I, (0 : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro p _hp
            have hp : (p, j) ≠ (i, k) := by
              intro hpair
              exact hjk (congrArg Prod.snd hpair)
            simpa [hp] using hChiOrth (p, j) (i, k)
      _ = if j = k then (1 : ℂ) else 0 := by simp [hjk]


private theorem piColumn_difference_family_pf58
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {piChar : I → J → Section1.ClassFunction L}
    {deltaSign : J → ℂ}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {chi : I → J → Section1.ClassFunction G}
    {A : Set L} {K W1 W2 : Subgroup L}
    {xChar : J → Section1.ClassFunction K} {k j : J}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar)
    (h49a : Section4Scratch.theorem_4_9_a_statement A j0 k piChar)
    (h49b : Section4Scratch.theorem_4_9_b_statement
      A j0 k W ω σ piChar deltaSign τ)
    (h48 : Section4Scratch.theorem_4_8_statement W2 W A j0 ω σ piChar deltaSign τ)
    (hChiOrth : Section3.IsOrthonormalDoubleFamily chi)
    (hChiSigned : ∀ i j, Section3.IsSignedIrreducibleCharacter (chi i j))
    (hChiSigma : ∀ i j, σ (ω i j) = chi i j)
    (hj0 : j ≠ j0) (hk0 : k ≠ j0)
    (hjk : j ≠ k)
    (hdegjk :
      Section1.degree (Section4Scratch.piColumn piChar j) =
        Section1.degree (Section4Scratch.piColumn piChar k)) :
    let Rμ : Finset (Section1.ClassFunction G) :=
      Finset.univ.image
        (muSignedFamily_pf58 (deltaSign k) (-deltaSign j) chi k j)
    signedOrthonormalFinset Rμ ∧
      τ (Section4Scratch.piColumn piChar k - Section4Scratch.piColumn piChar j) =
        Finset.sum Rμ (fun φ => φ) := by
  classical
  rcases h43b with ⟨_hσmap, hsign, _hirr, _hdistinct, _hind, _hSigmaL⟩
  let T : Type _ := Section4Scratch.equalDegreeColumnIndex piChar j0 k
  let tj : T := ⟨j, ⟨hj0, hdegjk⟩⟩
  let tk : T := ⟨k, ⟨hk0, rfl⟩⟩
  let muL : T → Section1.ClassFunction L := fun t => Section4Scratch.piColumn piChar t.1
  let muG : T → Section1.ClassFunction G :=
    fun t => deltaSign t.1 • Section4Scratch.omegaColumnSigma σ ω t.1
  let muG0 : T → Section1.ClassFunction G :=
    fun t => deltaSign k • Section4Scratch.omegaColumnSigma σ ω t.1
  have hdelta_jk : deltaSign j = deltaSign k := by
    exact (h48 i0 j k hj0 hk0
      (degree_entry_eq_of_equal_degree_column_pf58 K piChar xChar h45a hdegjk)).2.1
  have hmuG0_eval :
      Section1.evalCoeff muG0 (Section1.signedBasisDifference 1 tj tk) =
        Section1.evalCoeff muG (Section1.signedBasisDifference 1 tj tk) := by
    calc
      Section1.evalCoeff muG0 (Section1.signedBasisDifference 1 tj tk) =
          muG0 tk - muG0 tj := by
            simpa [Section1.signIntToComplex] using
              (Section1.evalCoeff_signedBasisDifference muG0 1 tj tk)
      _ = deltaSign k • Section4Scratch.omegaColumnSigma σ ω k -
            deltaSign k • Section4Scratch.omegaColumnSigma σ ω j := by
            simp [muG0, tj, tk]
      _ = deltaSign k • Section4Scratch.omegaColumnSigma σ ω k -
            deltaSign j • Section4Scratch.omegaColumnSigma σ ω j := by
            rw [hdelta_jk]
      _ = muG tk - muG tj := by
            simp [muG, tj, tk]
      _ = Section1.evalCoeff muG (Section1.signedBasisDifference 1 tj tk) := by
            simpa [Section1.signIntToComplex] using
              (Section1.evalCoeff_signedBasisDifference muG 1 tj tk).symm
  let v : Section1.CoeffVector T := Section1.signedBasisDifference 1 tj tk
  have hEvalL :
      Section1.evalCoeff muL v =
        Section4Scratch.piColumn piChar k - Section4Scratch.piColumn piChar j := by
    calc
      Section1.evalCoeff muL v = muL tk - muL tj := by
        dsimp [v]
        simpa [Section1.signIntToComplex] using
          (Section1.evalCoeff_signedBasisDifference muL 1 tj tk)
      _ = Section4Scratch.piColumn piChar k - Section4Scratch.piColumn piChar j := by
        simp [muL, tj, tk]
  have hPunct :
      Section1.supportedOn (Section1.evalCoeff muL v) puncturedSet := by
    rw [hEvalL, Section1.supportedOn_iff]
    intro x hx
    have hx1 : x = 1 := by simpa [puncturedSet] using hx
    subst hx1
    calc
      Section4Scratch.piColumn piChar k 1 - Section4Scratch.piColumn piChar j 1 =
          Section1.degree (Section4Scratch.piColumn piChar k) -
            Section1.degree (Section4Scratch.piColumn piChar j) := by
              rfl
      _ = 0 := by simp [hdegjk]
  have hA :
      Section1.supportedOn (Section1.evalCoeff muL v) A := (h49a hk0).2.2 v |>.1 hPunct
  have hTau :
      τ (Section1.evalCoeff muL v) = Section1.evalCoeff muG v := by
    calc
      τ (Section1.evalCoeff muL v) = Section1.evalCoeff muG0 v := (h49b hk0).2 v hA
      _ = Section1.evalCoeff muG v := by simpa [v] using hmuG0_eval
  have hEvalG :
      Section1.evalCoeff muG v =
        (∑ i : I, deltaSign k • chi i k) + ∑ i : I, (-deltaSign j) • chi i j := by
    calc
      Section1.evalCoeff muG v = muG tk - muG tj := by
        dsimp [v]
        simpa [Section1.signIntToComplex] using
          (Section1.evalCoeff_signedBasisDifference muG 1 tj tk)
      _ = deltaSign k • Section4Scratch.omegaColumnSigma σ ω k -
            deltaSign j • Section4Scratch.omegaColumnSigma σ ω j := by
            simp [muG, tj, tk]
      _ = deltaSign k • (∑ i : I, chi i k) -
            deltaSign j • (∑ i : I, chi i j) := by
        simp [Section4Scratch.omegaColumnSigma, hChiSigma]
      _ = (∑ i : I, deltaSign k • chi i k) + ∑ i : I, (-deltaSign j) • chi i j := by
            simp [sub_eq_add_neg, Finset.smul_sum]
  let Rμ : Finset (Section1.ClassFunction G) :=
    Finset.univ.image (muSignedFamily_pf58 (deltaSign k) (-deltaSign j) chi k j)
  have hRμorth : signedOrthonormalFinset Rμ := by
    dsimp [Rμ]
    refine signedOrthonormalFinset_image_pf58
      (ψ := muSignedFamily_pf58 (deltaSign k) (-deltaSign j) chi k j) ?_ ?_
    · intro p
      exact muSignedFamily_signed_pf58
        (hLeft := hsign k) (hRight := isSign_neg_pf58 (hsign j))
        (hChiSigned := hChiSigned) p
    · intro p q hpq
      exact muSignedFamily_orthogonal_pf58
        (deltaLeft := deltaSign k) (deltaRight := -deltaSign j)
        hChiOrth hjk.symm p q hpq
  have hRμsum :
      Finset.sum Rμ (fun φ => φ) =
        (∑ i : I, deltaSign k • chi i k) + ∑ i : I, (-deltaSign j) • chi i j := by
    dsimp [Rμ]
    exact muSignedFamily_sum_pf58
      (deltaLeft := deltaSign k) (deltaRight := -deltaSign j)
      (chi := chi) (j := k) (k := j)
      (muSignedFamily_injective_pf58
        (deltaLeft := deltaSign k) (deltaRight := -deltaSign j)
        (chi := chi) (j := k) (k := j)
        (hLeft := hsign k) (hRight := isSign_neg_pf58 (hsign j))
        hChiOrth hjk.symm)
  refine ⟨hRμorth, ?_⟩
  calc
    τ (Section4Scratch.piColumn piChar k - Section4Scratch.piColumn piChar j) =
        τ (Section1.evalCoeff muL v) := by rw [hEvalL.symm]
    _ = Section1.evalCoeff muG v := hTau
    _ = (∑ i : I, deltaSign k • chi i k) + ∑ i : I, (-deltaSign j) • chi i j := hEvalG
    _ = Finset.sum Rμ (fun φ => φ) := hRμsum.symm

private theorem tau_piColumn_sub_eq_signed_omegaColumnSigma_sub_pf58
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    {W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq J]
    {j0 k : J}
    {ω : I → J → Section1.ClassFunction W}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {piChar : I → J → Section1.ClassFunction L}
    {deltaSign : J → ℂ}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {A : Set L}
    (h49a : Section4Scratch.theorem_4_9_a_statement A j0 k piChar)
    (h49b : Section4Scratch.theorem_4_9_b_statement
      A j0 k W ω σ piChar deltaSign τ)
    (hk0 : k ≠ j0)
    {j : J}
    (hj : j ∈ Section4Scratch.equalDegreeColumnSet piChar j0 k) :
    τ (Section4Scratch.piColumn piChar k - Section4Scratch.piColumn piChar j) =
      deltaSign k •
        (Section4Scratch.omegaColumnSigma σ ω k -
          Section4Scratch.omegaColumnSigma σ ω j) := by
  classical
  let T := Section4Scratch.equalDegreeColumnIndex piChar j0 k
  let tk : T := ⟨k, ⟨hk0, rfl⟩⟩
  let tj : T := ⟨j, hj⟩
  let muL : T → Section1.ClassFunction L := fun t => Section4Scratch.piColumn piChar t.1
  let muG : T → Section1.ClassFunction G :=
    fun t => deltaSign k • Section4Scratch.omegaColumnSigma σ ω t.1
  let v : Section1.CoeffVector T := Section1.signedBasisDifference 1 tj tk
  have hEvalL :
      Section1.evalCoeff muL v =
        Section4Scratch.piColumn piChar k - Section4Scratch.piColumn piChar j := by
    calc
      Section1.evalCoeff muL v = muL tk - muL tj := by
        dsimp [v]
        simpa [Section1.signIntToComplex] using
          (Section1.evalCoeff_signedBasisDifference muL 1 tj tk)
      _ = Section4Scratch.piColumn piChar k - Section4Scratch.piColumn piChar j := by
        simp [muL, tj, tk]
  have hPunct :
      Section1.supportedOn (Section1.evalCoeff muL v) puncturedSet := by
    rw [hEvalL, Section1.supportedOn_iff]
    intro x hx
    have hx1 : x = 1 := by simpa [puncturedSet] using hx
    subst hx1
    calc
      Section4Scratch.piColumn piChar k 1 - Section4Scratch.piColumn piChar j 1 =
          Section1.degree (Section4Scratch.piColumn piChar k) -
            Section1.degree (Section4Scratch.piColumn piChar j) := by
            rfl
      _ = 0 := by simp [hj.2]
  have hA :
      Section1.supportedOn (Section1.evalCoeff muL v) A :=
    (h49a hk0).2.2 v |>.1 hPunct
  have hTau :
      τ (Section1.evalCoeff muL v) = Section1.evalCoeff muG v :=
    (h49b hk0).2 v hA
  have hEvalG :
      Section1.evalCoeff muG v =
        deltaSign k • Section4Scratch.omegaColumnSigma σ ω k -
          deltaSign k • Section4Scratch.omegaColumnSigma σ ω j := by
    calc
      Section1.evalCoeff muG v = muG tk - muG tj := by
        dsimp [v]
        simpa [Section1.signIntToComplex] using
          (Section1.evalCoeff_signedBasisDifference muG 1 tj tk)
      _ = deltaSign k • Section4Scratch.omegaColumnSigma σ ω k -
            deltaSign k • Section4Scratch.omegaColumnSigma σ ω j := by
        simp [muG, tj, tk]
  calc
    τ (Section4Scratch.piColumn piChar k - Section4Scratch.piColumn piChar j) =
        τ (Section1.evalCoeff muL v) := by rw [hEvalL]
    _ = Section1.evalCoeff muG v := hTau
    _ = deltaSign k • Section4Scratch.omegaColumnSigma σ ω k -
          deltaSign k • Section4Scratch.omegaColumnSigma σ ω j := hEvalG
    _ = deltaSign k •
          (Section4Scratch.omegaColumnSigma σ ω k -
            Section4Scratch.omegaColumnSigma σ ω j) := by
      rw [smul_sub]

private theorem scalarProduct_piColumn_eq_zero_of_ne_pf58
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {deltaSign : J → ℂ}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    {j k : J}
    (hjk : j ≠ k) :
    Section1.scalarProduct L
      (Section4Scratch.piColumn piChar j)
      (Section4Scratch.piColumn piChar k) = 0 := by
  rcases h43b with ⟨_hσmap, _hsign, hirr, hdistinct, _hind, _hSigmaL⟩
  have hsumj :
      (Section4Scratch.piColumn piChar j : Section1.ClassFunction L) =
        fun g => ∑ i : I, piChar i j g := by
    ext g
    simp [Section4Scratch.piColumn]
  have hsumk :
      (Section4Scratch.piColumn piChar k : Section1.ClassFunction L) =
        fun g => ∑ i : I, piChar i k g := by
    ext g
    simp [Section4Scratch.piColumn]
  rw [hsumj, Section1.scalarProduct_fintype_sum_left]
  refine Finset.sum_eq_zero ?_
  intro i _hi
  rw [hsumk, Section1.scalarProduct_fintype_sum_right]
  refine Finset.sum_eq_zero ?_
  intro p _hp
  have hneq : piChar i j ≠ piChar p k := by
    refine hdistinct (i, j) (p, k) ?_
    intro hpair
    exact hjk (congrArg Prod.snd hpair)
  exact scalarProduct_zero_of_distinct_irreducibles_pf58
    (hirr i j) (hirr p k) hneq

private theorem scalarProduct_self_of_irreducibleCharacterOnGroup_pf58
    {G : Type*} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    Section1.scalarProduct G χ χ = 1 := by
  rcases hχ with ⟨n, ρ, hρ, rfl⟩
  simpa using Section1.scalarProduct_representation_char_self ρ hρ

private theorem positive_degree_nat_of_isIrreducibleCharacterOnGroup_pf58
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

private theorem scalarProduct_self_of_signedIrreducible_pf58
    {G : Type*} [Group G] [Finite G]
    {χ : Section1.ClassFunction G}
    (hχ : Section3.IsSignedIrreducibleCharacter χ) :
    Section1.scalarProduct G χ χ = 1 := by
  rcases hχ with ⟨ε, hε, μ, hμ, rfl⟩
  have hμself : Section1.scalarProduct G μ μ = 1 :=
    scalarProduct_self_of_irreducibleCharacterOnGroup_pf58 hμ
  rcases hε with rfl | rfl
  · simp [hμself]
  · calc
      Section1.scalarProduct G ((-1 : ℂ) • μ) ((-1 : ℂ) • μ)
          = (-1 : ℂ) * star (-1 : ℂ) * Section1.scalarProduct G μ μ := by
              rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_right]
              ring
      _ = 1 := by simp [hμself]

private theorem scalarProduct_eq_ite_of_signedOrthonormalFinset_pf58
    {G : Type*} [Group G] [Finite G]
    {R : Finset (Section1.ClassFunction G)}
    (hR : signedOrthonormalFinset R) :
    ∀ a b : R, Section1.scalarProduct G (a : Section1.ClassFunction G) b =
      if a = b then 1 else 0 := by
  intro a b
  by_cases hab : a = b
  · subst hab
    simpa using scalarProduct_self_of_signedIrreducible_pf58 (hR.1 _ a.2)
  · simpa [hab] using hR.2 a.2 b.2 (fun hEq => hab (Subtype.ext hEq))

private theorem scalarProduct_evalCoeff_eq_coeffDot_of_orthonormal_pf58
    {G : Type*} [Group G] [Finite G]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : ι → Section1.ClassFunction G)
    (horth : ∀ i j, Section1.scalarProduct G (μ i) (μ j) = if i = j then 1 else 0)
    (v w : Section1.CoeffVector ι) :
    Section1.scalarProduct G (Section1.evalCoeff μ v) (Section1.evalCoeff μ w) =
      (Section1.coeffDot v w : ℂ) := by
  classical
  have hleft :
      (∑ j : ι, (v j : ℂ) • μ j) =
        (fun g : G => ∑ j : ι, ((v j : ℂ) • μ j) g) := by
    ext g
    simp
  have hright :
      (∑ j : ι, (w j : ℂ) • μ j) =
        (fun g : G => ∑ j : ι, ((w j : ℂ) • μ j) g) := by
    ext g
    simp
  simp only [Section1.evalCoeff]
  rw [hleft, hright]
  rw [Section1.scalarProduct_fintype_sum_left]
  simp_rw [Section1.scalarProduct_smul_left]
  change ∑ i : ι, (v i : ℂ) *
      Section1.scalarProduct G (μ i) (fun g : G => ∑ j : ι, ((w j : ℂ) • μ j) g) =
    ((∑ i : ι, v i * w i : ℤ) : ℂ)
  rw [show ((∑ i : ι, v i * w i : ℤ) : ℂ) =
      ∑ i : ι, ((v i * w i : ℤ) : ℂ) by simp]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  rw [Section1.scalarProduct_fintype_sum_right]
  simp_rw [Section1.scalarProduct_smul_right]
  calc
    (v i : ℂ) * (∑ x : ι, star (w x : ℂ) * Section1.scalarProduct G (μ i) (μ x)) =
        (v i : ℂ) * (w i : ℂ) := by
          simp [horth]
    _ = (v i * w i : ℤ) := by
          simp [Int.cast_mul]

private theorem subsetSum_self_eq_card_pf58
    {G : Type*} [Group G] [Finite G]
    {R E : Finset (Section1.ClassFunction G)}
    (hR : signedOrthonormalFinset R)
    (hEsub : E ⊆ R) :
    Section1.scalarProduct G (Finset.sum E fun ψ => ψ)
        (Finset.sum E fun ψ => ψ) = (E.card : ℂ) := by
  classical
  let μE : E → Section1.ClassFunction G := fun ψ => (ψ : Section1.ClassFunction G)
  let oneE : Section1.CoeffVector E := fun _ => 1
  have hμEorth :
      ∀ a b : E,
        Section1.scalarProduct G (μE a) (μE b) = if a = b then 1 else 0 := by
    intro a b
    exact scalarProduct_eq_ite_of_signedOrthonormalFinset_pf58
      ⟨fun φ hφ => hR.1 _ (hEsub hφ),
        fun φ ψ hφ hψ hne => hR.2 (hEsub hφ) (hEsub hψ) hne⟩ a b
  have hsumE : Section1.evalCoeff μE oneE = Finset.sum E fun φ => φ := by
    ext g
    simp [Section1.evalCoeff, μE, oneE]
    simpa using (Finset.sum_attach E fun c : Section1.ClassFunction G => c g)
  calc
    Section1.scalarProduct G (Finset.sum E fun ψ => ψ) (Finset.sum E fun ψ => ψ)
        = (Section1.coeffDot oneE oneE : ℂ) := by
            rw [← hsumE]
            simpa using
              scalarProduct_evalCoeff_eq_coeffDot_of_orthonormal_pf58 μE hμEorth oneE oneE
    _ = (E.card : ℂ) := by
          simp [Section1.coeffDot, oneE]

private theorem scalarProduct_sum_left_pf58
    {G : Type*} [Group G] [Finite G]
    (E : Finset (Section1.ClassFunction G))
    (ψ : Section1.ClassFunction G) :
    Section1.scalarProduct G (Finset.sum E fun φ => φ) ψ =
      Finset.sum E (fun φ => Section1.scalarProduct G φ ψ) := by
  classical
  unfold Section1.scalarProduct
  simp only [Finset.sum_apply]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [Finset.mul_sum]

private theorem scalarProduct_subsetSum_right_eq_ite_pf58
    {G : Type*} [Group G] [Finite G]
    {R E : Finset (Section1.ClassFunction G)}
    (hR : signedOrthonormalFinset R)
    (hEsub : E ⊆ R)
    {ψ : Section1.ClassFunction G}
    (hψR : ψ ∈ R) :
    Section1.scalarProduct G (Finset.sum E fun φ => φ) ψ =
      if ψ ∈ E then (1 : ℂ) else 0 := by
  classical
  rw [scalarProduct_sum_left_pf58]
  by_cases hψE : ψ ∈ E
  · rw [Finset.sum_eq_single ψ]
    · simpa [hψE] using scalarProduct_self_of_signedIrreducible_pf58 (hR.1 ψ hψR)
    · intro φ hφE hφne
      exact hR.2 (hEsub hφE) hψR hφne
    · intro hnot
      exact False.elim (hnot hψE)
  · rw [Finset.sum_eq_zero]
    · simp [hψE]
    · intro φ hφE
      exact hR.2 (hEsub hφE) hψR (fun hφψ => hψE (hφψ ▸ hφE))

private theorem scalarProduct_subsetSum_left_eq_zero_of_orthogonalFinsets_pf58
    {G : Type*} [Group G] [Finite G]
    {R Ω : Finset (Section1.ClassFunction G)}
    {φ ψ : Section1.ClassFunction G}
    (hsubset : isSubsetSumOf R φ)
    (horth : orthogonalFinsets R Ω)
    (hψ : ψ ∈ Ω) :
    Section1.scalarProduct G φ ψ = 0 := by
  classical
  rcases hsubset with ⟨E, hER, rfl⟩
  rw [scalarProduct_sum_left_pf58]
  exact Finset.sum_eq_zero (by
    intro χ hχ
    exact horth (hER hχ) hψ)


private theorem scalarProduct_piColumn_piChar_eq_ite_pf58
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {deltaSign : J → ℂ}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (_r i : I) (s q : J) :
    Section1.scalarProduct L
        (Section4Scratch.piColumn piChar s)
        (piChar i q) =
      if s = q then 1 else 0 := by
  classical
  rcases h43b with ⟨_hσmap, _hsign, hirr, hdistinct, _hind, _hSigmaL⟩
  unfold Section4Scratch.piColumn
  have hsum :
      ((∑ r : I, piChar r s : Section1.ClassFunction L)) =
        fun g => ∑ r : I, piChar r s g := by
    ext g
    simp
  rw [hsum, Section1.scalarProduct_fintype_sum_left]
  by_cases hsq : s = q
  · subst q
    calc
      ∑ r : I, Section1.scalarProduct L (piChar r s) (piChar i s)
          = ∑ r : I, if r = i then (1 : ℂ) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro r _hr
            by_cases hri : r = i
            · subst r
              simpa using scalarProduct_self_of_irreducibleCharacterOnGroup_pf58 (hirr i s)
            · simpa [hri] using
                scalarProduct_zero_of_distinct_irreducibles_pf58
                  (hirr r s) (hirr i s)
                  (hdistinct (r, s) (i, s) (by
                    intro hEq
                    exact hri (congrArg Prod.fst hEq)))
      _ = if s = s then (1 : ℂ) else 0 := by simp
  · calc
      ∑ r : I, Section1.scalarProduct L (piChar r s) (piChar i q)
          = ∑ r : I, (0 : ℂ) := by
            refine Finset.sum_congr rfl ?_
            intro r _hr
            simpa using
              scalarProduct_zero_of_distinct_irreducibles_pf58
                (hirr r s) (hirr i q)
                (hdistinct (r, s) (i, q) (by
                  intro hEq
                  exact hsq (congrArg Prod.snd hEq)))
      _ = if s = q then (1 : ℂ) else 0 := by simp [hsq]

private theorem scalarProduct_piColumn_eq_card_ite_pf58
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {deltaSign : J → ℂ}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (j k : J) :
    Section1.scalarProduct L
        (Section4Scratch.piColumn piChar j)
        (Section4Scratch.piColumn piChar k) =
      if j = k then (Fintype.card I : ℂ) else 0 := by
  classical
  unfold Section4Scratch.piColumn
  have hsumk :
      ((∑ p : I, piChar p k : Section1.ClassFunction L)) =
        fun g => ∑ p : I, piChar p k g := by
    ext g
    simp
  rw [hsumk, Section1.scalarProduct_fintype_sum_right]
  calc
    ∑ p : I,
        Section1.scalarProduct L (∑ r : I, piChar r j) (piChar p k)
        =
      ∑ p : I, if j = k then (1 : ℂ) else 0 := by
        refine Finset.sum_congr rfl ?_
        intro p _hp
        exact scalarProduct_piColumn_piChar_eq_ite_pf58 hω h43b i0 p j k
    _ = if j = k then (Fintype.card I : ℂ) else 0 := by
      by_cases hjk : j = k <;> simp [hjk]

public theorem piColumn_injective_pf58
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {deltaSign : J → ℂ}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω) :
    Function.Injective (Section4Scratch.piColumn piChar) := by
  classical
  intro j k hEq
  by_contra hjk
  have hleft :
      Section1.scalarProduct L
          (Section4Scratch.piColumn piChar j)
          (piChar i0 j) = 1 := by
    simpa using scalarProduct_piColumn_piChar_eq_ite_pf58 hω h43b i0 i0 j j
  have hright :
      Section1.scalarProduct L
          (Section4Scratch.piColumn piChar k)
          (piChar i0 j) = 0 := by
    have hkj : k ≠ j := by
      intro hkj
      exact hjk hkj.symm
    simpa [hkj] using scalarProduct_piColumn_piChar_eq_ite_pf58 hω h43b i0 i0 k j
  have hsame :
      Section1.scalarProduct L
          (Section4Scratch.piColumn piChar j)
          (piChar i0 j) =
        Section1.scalarProduct L
          (Section4Scratch.piColumn piChar k)
          (piChar i0 j) := by
    rw [hEq]
  rw [hleft, hright] at hsame
  norm_num at hsame

private theorem conjugateCharacter_conjugateCharacter_pf58
    {G : Type*} [Group G] (φ : Section1.ClassFunction G) :
    Section1.conjugateCharacter (Section1.conjugateCharacter φ) = φ := by
  ext g
  simp [Section1.conjugateCharacter]

private theorem iff_of_ite_one_zero_eq_pf58 {p q : Prop}
    [Decidable p] [Decidable q]
    (h : (if p then (1 : ℂ) else 0) = if q then (1 : ℂ) else 0) :
    p ↔ q := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq] at h ⊢


private theorem sum_image_muSignedFamily_left_pf58
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [DecidableEq I]
    {deltaLeft deltaRight : ℂ}
    {chi : I → J → Section1.ClassFunction G}
    {j k : J}
    (hinj : Function.Injective (muSignedFamily_pf58 deltaLeft deltaRight chi j k)) :
    Finset.sum
        (Finset.univ.image fun i : I =>
          muSignedFamily_pf58 deltaLeft deltaRight chi j k (Sum.inl i))
        (fun φ => φ) =
      ∑ i : I, deltaLeft • chi i j := by
  calc
    Finset.sum
        (Finset.univ.image fun i : I =>
          muSignedFamily_pf58 deltaLeft deltaRight chi j k (Sum.inl i))
        (fun φ => φ) =
      ∑ i : I, muSignedFamily_pf58 deltaLeft deltaRight chi j k (Sum.inl i) := by
        exact Finset.sum_image
          (s := Finset.univ)
          (g := fun i : I => muSignedFamily_pf58 deltaLeft deltaRight chi j k (Sum.inl i))
          (f := fun φ => φ)
          (by
            intro a _ha b _hb hab
            exact Sum.inl.inj (hinj hab))
    _ = ∑ i : I, deltaLeft • chi i j := by
      simp [muSignedFamily_pf58]

private theorem sum_image_muSignedFamily_right_pf58
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [DecidableEq I]
    {deltaLeft deltaRight : ℂ}
    {chi : I → J → Section1.ClassFunction G}
    {j k : J}
    (hinj : Function.Injective (muSignedFamily_pf58 deltaLeft deltaRight chi j k)) :
    Finset.sum
        (Finset.univ.image fun i : I =>
          muSignedFamily_pf58 deltaLeft deltaRight chi j k (Sum.inr i))
        (fun φ => φ) =
      ∑ i : I, deltaRight • chi i k := by
  calc
    Finset.sum
        (Finset.univ.image fun i : I =>
          muSignedFamily_pf58 deltaLeft deltaRight chi j k (Sum.inr i))
        (fun φ => φ) =
      ∑ i : I, muSignedFamily_pf58 deltaLeft deltaRight chi j k (Sum.inr i) := by
        exact Finset.sum_image
          (s := Finset.univ)
          (g := fun i : I => muSignedFamily_pf58 deltaLeft deltaRight chi j k (Sum.inr i))
          (f := fun φ => φ)
          (by
            intro a _ha b _hb hab
            exact Sum.inr.inj (hinj hab))
    _ = ∑ i : I, deltaRight • chi i k := by
      simp [muSignedFamily_pf58]

private theorem scalarProduct_subsetSum_muSignedFamily_left_chi_pf58
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    {deltaLeft deltaRight : ℂ}
    {chi : I → J → Section1.ClassFunction G}
    {j k : J}
    {E : Finset (Section1.ClassFunction G)}
    (hLeft : Section1.IsSign deltaLeft)
    (hR :
      signedOrthonormalFinset
        (Finset.univ.image (muSignedFamily_pf58 deltaLeft deltaRight chi j k)))
    (hEsub :
      E ⊆ Finset.univ.image (muSignedFamily_pf58 deltaLeft deltaRight chi j k))
    (i : I) :
    Section1.scalarProduct G (Finset.sum E fun φ => φ) (chi i j) =
      deltaLeft *
        (if muSignedFamily_pf58 deltaLeft deltaRight chi j k (Sum.inl i) ∈ E
          then (1 : ℂ) else 0) := by
  classical
  let ψ := muSignedFamily_pf58 deltaLeft deltaRight chi j k (Sum.inl i)
  have hψR :
      ψ ∈ Finset.univ.image (muSignedFamily_pf58 deltaLeft deltaRight chi j k) := by
    simp [ψ]
  have hcoeff :
      Section1.scalarProduct G (Finset.sum E fun φ => φ) ψ =
        if ψ ∈ E then (1 : ℂ) else 0 :=
    scalarProduct_subsetSum_right_eq_ite_pf58 hR hEsub hψR
  have hstar : star deltaLeft = deltaLeft := by
    rcases hLeft with rfl | rfl <;> simp
  have hsq : deltaLeft * deltaLeft = 1 := by
    rcases hLeft with rfl | rfl <;> norm_num
  have hcoeff' :
      deltaLeft *
          Section1.scalarProduct G (Finset.sum E fun φ => φ) (chi i j) =
        if ψ ∈ E then (1 : ℂ) else 0 := by
    simpa [ψ, muSignedFamily_pf58, Section1.scalarProduct_smul_right, hstar]
      using hcoeff
  calc
    Section1.scalarProduct G (Finset.sum E fun φ => φ) (chi i j)
        = 1 * Section1.scalarProduct G (Finset.sum E fun φ => φ) (chi i j) := by
            ring
    _ = (deltaLeft * deltaLeft) *
          Section1.scalarProduct G (Finset.sum E fun φ => φ) (chi i j) := by
            rw [hsq]
    _ = deltaLeft *
          (deltaLeft *
            Section1.scalarProduct G (Finset.sum E fun φ => φ) (chi i j)) := by
            ring
    _ = deltaLeft * (if ψ ∈ E then (1 : ℂ) else 0) := by
            rw [hcoeff']

private theorem scalarProduct_subsetSum_muSignedFamily_right_chi_pf58
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    {deltaLeft deltaRight : ℂ}
    {chi : I → J → Section1.ClassFunction G}
    {j k : J}
    {E : Finset (Section1.ClassFunction G)}
    (hRight : Section1.IsSign deltaRight)
    (hR :
      signedOrthonormalFinset
        (Finset.univ.image (muSignedFamily_pf58 deltaLeft deltaRight chi j k)))
    (hEsub :
      E ⊆ Finset.univ.image (muSignedFamily_pf58 deltaLeft deltaRight chi j k))
    (i : I) :
    Section1.scalarProduct G (Finset.sum E fun φ => φ) (chi i k) =
      deltaRight *
        (if muSignedFamily_pf58 deltaLeft deltaRight chi j k (Sum.inr i) ∈ E
          then (1 : ℂ) else 0) := by
  classical
  let ψ := muSignedFamily_pf58 deltaLeft deltaRight chi j k (Sum.inr i)
  have hψR :
      ψ ∈ Finset.univ.image (muSignedFamily_pf58 deltaLeft deltaRight chi j k) := by
    simp [ψ]
  have hcoeff :
      Section1.scalarProduct G (Finset.sum E fun φ => φ) ψ =
        if ψ ∈ E then (1 : ℂ) else 0 :=
    scalarProduct_subsetSum_right_eq_ite_pf58 hR hEsub hψR
  have hstar : star deltaRight = deltaRight := by
    rcases hRight with rfl | rfl <;> simp
  have hsq : deltaRight * deltaRight = 1 := by
    rcases hRight with rfl | rfl <;> norm_num
  have hcoeff' :
      deltaRight *
          Section1.scalarProduct G (Finset.sum E fun φ => φ) (chi i k) =
        if ψ ∈ E then (1 : ℂ) else 0 := by
    simpa [ψ, muSignedFamily_pf58, Section1.scalarProduct_smul_right, hstar]
      using hcoeff
  calc
    Section1.scalarProduct G (Finset.sum E fun φ => φ) (chi i k)
        = 1 * Section1.scalarProduct G (Finset.sum E fun φ => φ) (chi i k) := by
            ring
    _ = (deltaRight * deltaRight) *
          Section1.scalarProduct G (Finset.sum E fun φ => φ) (chi i k) := by
            rw [hsq]
    _ = deltaRight *
          (deltaRight *
            Section1.scalarProduct G (Finset.sum E fun φ => φ) (chi i k)) := by
            ring
    _ = deltaRight * (if ψ ∈ E then (1 : ℂ) else 0) := by
            rw [hcoeff']

private theorem scalarProduct_subsetSum_muSignedFamily_chi_eq_zero_of_ne_pf58
    {G : Type u} [Group G] [Finite G]
    {I J : Type*} [Fintype I] [DecidableEq I] [DecidableEq J]
    {deltaLeft deltaRight : ℂ}
    {chi : I → J → Section1.ClassFunction G}
    {j k q : J}
    {E : Finset (Section1.ClassFunction G)}
    (hChiOrth : Section3.IsOrthonormalDoubleFamily chi)
    (hEsub :
      E ⊆ Finset.univ.image (muSignedFamily_pf58 deltaLeft deltaRight chi j k))
    (hqj : q ≠ j) (hqk : q ≠ k) (i : I) :
    Section1.scalarProduct G (Finset.sum E fun φ => φ) (chi i q) = 0 := by
  classical
  rw [scalarProduct_sum_left_pf58]
  refine Finset.sum_eq_zero ?_
  intro φ hφE
  rcases Finset.mem_image.mp (hEsub hφE) with ⟨p, _hp, rfl⟩
  cases p with
  | inl r =>
      have hpair : (r, j) ≠ (i, q) := by
        intro hp
        exact hqj (congrArg Prod.snd hp).symm
      have hbase :
          Section1.scalarProduct G (chi r j) (chi i q) = 0 := by
        simpa [hpair] using hChiOrth (r, j) (i, q)
      rw [muSignedFamily_pf58, Section1.scalarProduct_smul_left, hbase]
      simp
  | inr r =>
      have hpair : (r, k) ≠ (i, q) := by
        intro hp
        exact hqk (congrArg Prod.snd hp).symm
      have hbase :
          Section1.scalarProduct G (chi r k) (chi i q) = 0 := by
        simpa [hpair] using hChiOrth (r, k) (i, q)
      rw [muSignedFamily_pf58, Section1.scalarProduct_smul_left, hbase]
      simp

private theorem subsetSum_piColumn_of_conjugate_pf58
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (K W1 W2 W : Subgroup L)
    {A : Set L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G}
    {piChar : I → J → Section1.ClassFunction L}
    {xChar : J → Section1.ClassFunction K}
    {deltaSign : J → ℂ}
    {τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G}
    {chi : I → J → Section1.ClassFunction G}
    {S : Finset (Section1.ClassFunction L)}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (h45a : Section4Scratch.theorem_4_5_a_statement K piChar xChar)
    (h48 : Section4Scratch.theorem_4_8_statement W2 W A j0 ω σ piChar deltaSign τ)
    (h49a : ∀ k : J, k ≠ j0 →
      Section4Scratch.theorem_4_9_a_statement A j0 k piChar)
    (h49b : ∀ k : J, k ≠ j0 →
      Section4Scratch.theorem_4_9_b_statement A j0 k W ω σ piChar deltaSign τ)
    (hChiOrth : Section3.IsOrthonormalDoubleFamily chi)
    (hChiSigned : ∀ i j, Section3.IsSignedIrreducibleCharacter (chi i j))
    (hChiSigma : ∀ i j, σ (ω i j) = chi i j)
    (h52a : hypothesis_5_2_a_statement S)
    (h52b : hypothesis_5_2_b_statement S τ)
    {a b : J}
    (ha0 : a ≠ j0)
    (haS : Section4Scratch.piColumn piChar a ∈ S)
    (hb0 : b ≠ j0)
    (hconj :
      Section1.conjugateCharacter (Section4Scratch.piColumn piChar a) =
        Section4Scratch.piColumn piChar b)
    (T1 : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (hIso : isCFLinearIsometryOnSpan S T1)
    (hT1virt : mapsIntegerSpanToVirtualCharacters S T1)
    (hAgree : agreesOnIntegerSpanOn S puncturedSet τ T1) :
    let Rμa : Finset (Section1.ClassFunction G) :=
      Finset.univ.image (muSignedFamily_pf58 (deltaSign a) (-deltaSign b) chi a b)
    signedOrthonormalFinset Rμa ∧
      isSubsetSumOf Rμa (T1 (Section4Scratch.piColumn piChar a)) := by
  classical
  let muA : Section1.ClassFunction L := Section4Scratch.piColumn piChar a
  let muB : Section1.ClassFunction L := Section4Scratch.piColumn piChar b
  have hdegba :
      Section1.degree (Section4Scratch.piColumn piChar b) =
        Section1.degree (Section4Scratch.piColumn piChar a) :=
    degree_piColumn_eq_of_conjugate_pf58 h45a hconj
  have hbS : muB ∈ S := by
    simpa [muA, muB, hconj] using (h52a ⟨muA, by simpa [muA] using haS⟩).1
  have hmuBA : muB ≠ muA := by
    intro hEq
    have hself : Section1.conjugateCharacter muA = muA := by
      simpa [muA, muB, hEq] using hconj
    exact (h52a ⟨muA, by simpa [muA] using haS⟩).2 hself.symm
  have hba : b ≠ a := by
    intro hEq
    exact hmuBA (by simp [muA, muB, hEq])
  have hconjSymm : Section1.conjugateCharacter muB = muA := by
    calc
      Section1.conjugateCharacter muB =
          Section1.conjugateCharacter (Section1.conjugateCharacter muA) := by
            rw [hconj]
      _ = muA := conjugateCharacter_conjugateCharacter_pf58 muA
  let Rμa : Finset (Section1.ClassFunction G) :=
    Finset.univ.image (muSignedFamily_pf58 (deltaSign a) (-deltaSign b) chi a b)
  have hRμa :
      signedOrthonormalFinset Rμa ∧
        τ (muA - muB) = Finset.sum Rμa (fun φ => φ) := by
    simpa [Rμa, muA, muB] using
      (piColumn_difference_family_pf58
        (i0 := i0) (j0 := j0) (ω := ω) (σL := σL) (σ := σ)
        (piChar := piChar) (deltaSign := deltaSign) (τ := τ) (chi := chi)
        (A := A) (K := K) (W1 := W1) (W2 := W2) (xChar := xChar)
        (k := a) (j := b)
        hω h43b h45a (h49a a ha0) (h49b a ha0) h48 hChiOrth hChiSigned
        hChiSigma hb0 ha0 hba hdegba)
  let Rμb : Finset (Section1.ClassFunction G) :=
    Finset.univ.image (muSignedFamily_pf58 (deltaSign b) (-deltaSign a) chi b a)
  have hRμb :
      signedOrthonormalFinset Rμb ∧
        τ (muB - muA) = Finset.sum Rμb (fun φ => φ) := by
    simpa [Rμb, muA, muB] using
      (piColumn_difference_family_pf58
        (i0 := i0) (j0 := j0) (ω := ω) (σL := σL) (σ := σ)
        (piChar := piChar) (deltaSign := deltaSign) (τ := τ) (chi := chi)
        (A := A) (K := K) (W1 := W1) (W2 := W2) (xChar := xChar)
        (k := b) (j := a)
        hω h43b h45a (h49a b hb0) (h49b b hb0) h48 hChiOrth hChiSigned
        hChiSigma ha0 hb0 hba.symm hdegba.symm)
  let pairS : Finset (Section1.ClassFunction L) := {muA, muB}
  have hpairSubset : pairS ⊆ S := by
    intro ψ hψ
    simp [pairS] at hψ
    rcases hψ with rfl | rfl
    · simpa [muA] using haS
    · exact hbS
  have hpairOr : ∀ X : pairS,
      (X : Section1.ClassFunction L) = muA ∨ (X : Section1.ClassFunction L) = muB := by
    intro X
    have hmem :
        (X : Section1.ClassFunction L) ∈
          ({muA, muB} : Finset (Section1.ClassFunction L)) := by
      simp [pairS]
    rcases Finset.mem_insert.mp hmem with hX | hX
    · exact Or.inl hX
    · exact Or.inr (Finset.mem_singleton.mp hX)
  let Rpair : pairS → Finset (Section1.ClassFunction G) := fun X =>
    if hX : (X : Section1.ClassFunction L) = muA then Rμa else Rμb
  have hpairSetup : hypothesis_5_2_setup_statement pairS := by
    refine ⟨⟨muA, by simp [pairS]⟩, ?_⟩
    intro X
    rcases hpairOr X with hX | hX
    · simpa [hX, muA] using piColumn_isCharacter_pf58 h45a a
    · simpa [hX, muB] using piColumn_isCharacter_pf58 h45a b
  have hpair52a : hypothesis_5_2_a_statement pairS := by
    intro X
    rcases hpairOr X with hX | hX
    · refine ⟨?_, ?_⟩
      · simp [hX, pairS, hconj, muA, muB]
      · simpa [hX] using (h52a ⟨muA, by simpa [muA] using haS⟩).2
    · refine ⟨?_, ?_⟩
      · simp [hX, pairS, hconjSymm, muA, muB]
      · intro hEq
        exact hmuBA (by simpa [hX, hconjSymm] using hEq)
  have hpair52b : hypothesis_5_2_b_statement pairS τ := by
    refine ⟨?_, ?_⟩
    · exact isCFLinearIsometryOnSpanOn_mono_pf58 hpairSubset h52b.1
    · intro ψ hψ
      exact h52b.2 ψ (integerSpanOn_mono_pf58 hpairSubset hψ)
  have hpair52c : hypothesis_5_2_c_statement pairS := by
    intro χ ψ hχ hψ hneq
    rcases hpairOr ⟨χ, hχ⟩ with rfl | rfl
    · rcases hpairOr ⟨ψ, hψ⟩ with rfl | rfl
      · exact (hneq rfl).elim
      · simpa [muA, muB] using scalarProduct_piColumn_eq_zero_of_ne_pf58
          hω h43b hba.symm
    · rcases hpairOr ⟨ψ, hψ⟩ with rfl | rfl
      · simpa [muA, muB] using scalarProduct_piColumn_eq_zero_of_ne_pf58
          hω h43b hba
      · exact (hneq rfl).elim
  have hpair52d : hypothesis_5_2_d_statement pairS τ Rpair := by
    intro X
    rcases hpairOr X with hX | hX
    · simpa [Rpair, hX, hconj, muA, muB] using hRμa
    · have hBACol : Section4Scratch.piColumn piChar b ≠ Section4Scratch.piColumn piChar a := by
        simpa [muA, muB] using hmuBA
      simpa [Rpair, hX, hconjSymm, muA, muB, hBACol] using hRμb
  have hpairSelf_ne_zero :
      ∀ Y : pairS,
        Section1.scalarProduct L
          (Y : Section1.ClassFunction L)
          (Y : Section1.ClassFunction L) ≠ 0 := by
    intro Y hYY
    have hnorm : cfNormSq (Y : Section1.ClassFunction L) = 0 := by
      unfold cfNormSq
      simp [hYY]
    have hzero : (Y : Section1.ClassFunction L) = 0 := cfNormSq_eq_zero_pf58 hnorm
    exact (hpair52a Y).2 (by
      rw [hzero]
      ext g
      simp [Section1.conjugateCharacter])
  have hpair52e : hypothesis_5_2_e_statement pairS Rpair := by
    intro X Y hYX hYbarX
    rcases hpairOr X with hX | hX <;> rcases hpairOr Y with hY | hY
    · have hself := hYX
      rw [hX, hY] at hself
      exact False.elim (hpairSelf_ne_zero ⟨muA, by simp [pairS]⟩ hself)
    · have hself := hYbarX
      rw [hX, hY, hconj] at hself
      exact False.elim (hpairSelf_ne_zero ⟨muB, by simp [pairS]⟩ hself)
    · have hself := hYbarX
      rw [hX, hY, hconjSymm] at hself
      exact False.elim (hpairSelf_ne_zero ⟨muA, by simp [pairS]⟩ hself)
    · have hself := hYX
      rw [hX, hY] at hself
      exact False.elim (hpairSelf_ne_zero ⟨muB, by simp [pairS]⟩ hself)
  have hpairSetSubset :
      ({muA, Section1.conjugateCharacter muA} : Finset (Section1.ClassFunction L)) ⊆ S := by
    intro ψ hψ
    simp [hconj, muA] at hψ
    rcases hψ with rfl | rfl
    · simpa [muA] using haS
    · exact hbS
  have hpairIso :
      isCFLinearIsometryOnSpan
        ({muA, Section1.conjugateCharacter muA} : Finset (Section1.ClassFunction L)) T1 :=
    isCFLinearIsometryOnSpan_mono_pf58 hpairSetSubset hIso
  have hpairVirt :
      mapsIntegerSpanToVirtualCharacters
        ({muA, Section1.conjugateCharacter muA} : Finset (Section1.ClassFunction L)) T1 :=
    mapsIntegerSpanToVirtualCharacters_mono_pf58 hpairSetSubset hT1virt
  have hmuASpan : integerSpan S muA := integerSpan_of_mem_pf58 S (by simpa [muA] using haS)
  have hmuBSpan : integerSpan S muB := integerSpan_of_mem_pf58 S hbS
  have hpairDiffOn :
      integerSpanOn S puncturedSet (muA - Section1.conjugateCharacter muA) := by
    refine ⟨?_, ?_⟩
    · simpa [muA, muB, hconj] using integerSpan_sub_pf58 hmuASpan hmuBSpan
    · apply (supportedOn_puncturedSet_iff_degree_eq_zero_pf58 _).2
      rw [Section1.degree_apply, hconj]
      simpa [Section1.degree_apply] using sub_eq_zero.mpr hdegba.symm
  have hpairAgree :
      T1 (muA - Section1.conjugateCharacter muA) =
        τ (muA - Section1.conjugateCharacter muA) := by
    exact hAgree _ hpairDiffOn
  let Xa : pairS := ⟨muA, by simp [pairS]⟩
  have hsubset_muA :
      isSubsetSumOf (Rpair Xa) (T1 muA) := by
    exact theorem_5_5 pairS τ Rpair
      hpairSetup hpair52a hpair52b hpair52c hpair52d hpair52e
      Xa T1 hpairIso hpairVirt hpairAgree
  refine ⟨hRμa.1, ?_⟩
  simpa [Xa, Rpair, Rμa, muA] using hsubset_muA

private theorem source_bridge_eq_induced_alphaIJ_pf58
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {deltaSign : J → ℂ}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (i : I) (j : J) :
    deltaSign j • piChar i j - deltaSign j • piChar i0 j -
        piChar i j0 + piChar i0 j0 =
      Section1.inducedCF W (Section3.alphaIJ W i0 j0 ω i j) := by
  rcases h43b with ⟨_hσmapL, _hsign, _hirr, _hdistinct, hind, _hSigmaL⟩
  have hδ0 : deltaSign j0 = 1 :=
    (Section4.proposition_4_4_base
      (W1 := W1) (W2 := W2) (W := W)
      (I := I) (J := J) (i0 := i0) (j0 := j0)
      (ω := ω) (σ := σL) (piChar := piChar) (deltaSign := deltaSign)
      hω ⟨_hσmapL, _hsign, _hirr, _hdistinct, hind, _hSigmaL⟩).1
  calc
    deltaSign j • piChar i j - deltaSign j • piChar i0 j -
          piChar i j0 + piChar i0 j0
        = deltaSign j • (piChar i j - piChar i0 j) -
            deltaSign j0 • (piChar i j0 - piChar i0 j0) := by
              simp [hδ0, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = Section1.inducedCF W (ω i j - ω i0 j) -
          Section1.inducedCF W (ω i j0 - ω i0 j0) := by
            rw [hind i j, hind i j0]
    _ = Section1.inducedCFLinear W
          ((ω i j - ω i0 j) - (ω i j0 - ω i0 j0)) := by
            rw [LinearMap.map_sub, Section1.inducedCFLinear_apply,
              Section1.inducedCFLinear_apply]
    _ = Section1.inducedCF W (Section3.alphaIJ W i0 j0 ω i j) := by
          rw [Section1.inducedCFLinear_apply]
          simp [Section3.alphaIJ, hω.principal, sub_eq_add_neg,
            add_assoc, add_left_comm, add_comm]

private theorem source_bridge_supportedOn_primeDadeA0_pf58
    {L : Type u} [Group L] [Finite L]
    {W1 W2 W : Subgroup L}
    {A : Set L}
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    {i0 : I} {j0 : J}
    {ω : I → J → Section1.ClassFunction W}
    {σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L}
    {piChar : I → J → Section1.ClassFunction L}
    {deltaSign : J → ℂ}
    (hω : Section3.notation_3_3_statement W1 W2 W I J i0 j0 ω)
    (h43b : Section4.theorem_4_3_b_statement
      W1 W2 W I J i0 j0 ω σL piChar deltaSign hω)
    (i : I) (j : J) :
    Section1.supportedOn
      (deltaSign j • piChar i j - deltaSign j • piChar i0 j -
        piChar i j0 + piChar i0 j0)
      (Section4Scratch.primeDadeA0Set W1 W2 W A) := by
  rw [source_bridge_eq_induced_alphaIJ_pf58 hω h43b i j]
  rw [Section1.supportedOn_iff]
  intro x hx
  exact Section3.inducedCF_eq_zero_of_not_mem_conjugateSet_of_CFOn W
    (Section3.alphaIJ W i0 j0 ω i j)
    (Section3.alphaIJ_CFOn_cyclicTISet W1 W2 W I J i0 j0 ω hω i j)
    (by
      intro hxConj
      rcases hxConj with ⟨y, hy, hxy⟩
      exact hx (Or.inr ⟨y, hy, hxy⟩))

private theorem degree_zero_combo_mem_integerSpanOn_punctured_pf58
    {H : Type*} [Group H] [Finite H]
    {S : Finset (Section1.ClassFunction H)}
    {X ψ : Section1.ClassFunction H}
    (m n : ℕ)
    (hXspan : integerSpan S X)
    (hψspan : integerSpan S ψ)
    (hdegX : Section1.degree X = (n : ℂ))
    (hdegψ : Section1.degree ψ = (m : ℂ)) :
    integerSpanOn S puncturedSet (((m : ℂ) • X) - ((n : ℂ) • ψ)) := by
  refine ⟨integerSpan_sub
      (integerSpan_zsmul (S := S) (φ := X) (m : ℤ) hXspan)
      (integerSpan_zsmul (S := S) (φ := ψ) (n : ℤ) hψspan), ?_⟩
  rw [Section1.supportedOn_iff]
  intro g hg
  have hg1 : g = 1 := by simpa [puncturedSet] using hg
  subst hg1
  have hX1 : X 1 = (n : ℂ) := by simpa [Section1.degree_apply] using hdegX
  have hψ1 : ψ 1 = (m : ℂ) := by simpa [Section1.degree_apply] using hdegψ
  simp [hX1, hψ1, sub_eq_add_neg]
  ring

private theorem supportedOn_punctured_iff_supportedOn_of_supportedOn_withOne_pf58
    {H : Type*} [Group H]
    (A : Set H)
    (hA : A ⊆ puncturedSet)
    {φ : Section1.ClassFunction H}
    (hφ : Section1.supportedOn φ (Section4Scratch.withOne A)) :
    Section1.supportedOn φ puncturedSet ↔ Section1.supportedOn φ A := by
  constructor
  · intro hpunct
    rw [Section1.supportedOn_iff]
    intro x hxA
    by_cases hx1 : x = 1
    · exact (Section1.supportedOn_iff.mp hpunct) x (by simp [puncturedSet, hx1])
    · exact (Section1.supportedOn_iff.mp hφ) x
        (by simp [Section4Scratch.withOne, hxA, hx1])
  · intro hAon
    rw [Section1.supportedOn_iff]
    intro x hxpunct
    exact (Section1.supportedOn_iff.mp hAon) x (fun hxA => hxpunct (hA hxA))

private theorem supportedOn_evalCoeff_pf58
    {H : Type*} [Group H]
    {ι : Type*} [Fintype ι]
    {μ : ι → Section1.ClassFunction H}
    {A : Set H}
    (hμ : ∀ i, Section1.supportedOn (μ i) A)
    (v : Section1.CoeffVector ι) :
    Section1.supportedOn (Section1.evalCoeff μ v) A := by
  rw [Section1.supportedOn_iff]
  intro g hg
  have hzero : ∀ i, μ i g = 0 := by
    intro i
    exact (Section1.supportedOn_iff.mp (hμ i)) g hg
  simp [Section1.evalCoeff, hzero]

private theorem supportedOn_mono_pf58
    {H : Type*} [Group H]
    {A B : Set H} {φ : Section1.ClassFunction H}
    (hAB : A ⊆ B)
    (hφ : Section1.supportedOn φ A) :
    Section1.supportedOn φ B := by
  rw [Section1.supportedOn_iff] at hφ ⊢
  intro g hgB
  exact hφ g (fun hgA => hgB (hAB hgA))

private theorem integerSpan_support_withOne_of_induced_family_pf58
    {L : Type u} [Group L] [Finite L]
    {K H : Subgroup L}
    {A : Set L}
    {S : Finset (Section1.ClassFunction L)}
    (h47 : Section4Scratch.theorem_4_7_statement K H A)
    (hInd : inducedFromNonkernelFamily_statement K H S)
    {χ : Section1.ClassFunction L}
    (hχ : integerSpan S χ) :
    Section1.supportedOn χ (Section4Scratch.withOne A) := by
  classical
  rcases hχ with ⟨v, rfl⟩
  refine supportedOn_evalCoeff_pf58
    (μ := fun X : S => (X : Section1.ClassFunction L)) ?_ v
  intro X
  rcases hInd (X : Section1.ClassFunction L) X.2 with ⟨B, hBirr, hBker, hXeq⟩
  simpa [hXeq] using (h47 B hBirr hBker).2

private theorem induced_family_supportedOn_primeDadeA0_of_punctured_pf58
    {L : Type u} [Group L] [Finite L]
    {K W1 W2 W H : Subgroup L}
    {A : Set L}
    {S : Finset (Section1.ClassFunction L)}
    (h46 : Section4Scratch.hypothesis_4_6_statement K W1 W2 W H A)
    (h47 : Section4Scratch.theorem_4_7_statement K H A)
    (hInd : inducedFromNonkernelFamily_statement K H S)
    {χ : Section1.ClassFunction L}
    (hχ : integerSpanOn S puncturedSet χ) :
    Section1.supportedOn χ
      (Section4Scratch.primeDadeA0Set W1 W2 W A) := by
  rcases hχ with ⟨hχspan, hχpunct⟩
  have hA_punct : A ⊆ puncturedSet := by
    intro x hxA
    rcases h46 with ⟨_h42, _hHnorm, _hW2H, _hHK, _hcentA, hAinK⟩
    exact (hAinK hxA).2
  have hwithOne :
      Section1.supportedOn χ (Section4Scratch.withOne A) :=
    integerSpan_support_withOne_of_induced_family_pf58 h47 hInd hχspan
  have hA :
      Section1.supportedOn χ A :=
    (supportedOn_punctured_iff_supportedOn_of_supportedOn_withOne_pf58
      A hA_punct hwithOne).1 hχpunct
  exact supportedOn_mono_pf58 (by
    intro x hx
    exact Or.inl hx) hA

public theorem theorem_5_8_core
    {L : Type u} [Group L] [Finite L]
    {G : Type u} [Group G] [Finite G]
    (K W1 W2 W H : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (piChar : I → J → Section1.ClassFunction L)
    (xChar : J → Section1.ClassFunction K)
    (deltaSign : J → ℂ)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (S : Finset (Section1.ClassFunction L)) :
    theorem_5_8_core_statement
      K W1 W2 W H A i0 j0 ω σL σ piChar xChar deltaSign τ S := by
  intro hCtx h52a hIrrMem hInd k hk0 hkS j hconj T1 hIso hT1virt hAgree
  rcases hCtx with
    ⟨h46, hτcyclic, hτA0, hτisoA0, hτpunctA0, hτvirtA0,
      h52bOfInd, hω, chi, hChiOrth, hChiSigned, hChiSigma,
      h43b, h43c, h43d, h45a, h45b, h47, h48, h49a, h49b, h410⟩
  have h52b : hypothesis_5_2_b_statement S τ := h52bOfInd S hInd
  have hSne : S.Nonempty := ⟨Section4Scratch.piColumn piChar k, hkS⟩
  rcases hIrrMem with ⟨X, hXirr⟩
  have hkChar :
      Section1.IsCharacter (Section4Scratch.piColumn piChar k) :=
    piColumn_isCharacter_pf58 h45a k
  have hjChar :
      Section1.IsCharacter (Section4Scratch.piColumn piChar j) :=
    piColumn_isCharacter_pf58 h45a j
  have hdegjk :
      Section1.degree (Section4Scratch.piColumn piChar j) =
        Section1.degree (Section4Scratch.piColumn piChar k) :=
    degree_piColumn_eq_of_conjugate_pf58 h45a hconj
  let muK : Section1.ClassFunction L := Section4Scratch.piColumn piChar k
  let muJ : Section1.ClassFunction L := Section4Scratch.piColumn piChar j
  have hjS : muJ ∈ S := by
    simpa [muK, muJ, hconj] using (h52a ⟨muK, hkS⟩).1
  have hmuJK : muJ ≠ muK := by
    intro hEq
    have hself : Section1.conjugateCharacter muK = muK := by
      simpa [muK, muJ, hEq] using hconj
    exact (h52a ⟨muK, hkS⟩).2 hself.symm
  have hjk : j ≠ k := by
    intro hEq
    apply hmuJK
    simp [muJ, muK, hEq]
  have hconjSymm : Section1.conjugateCharacter muJ = muK := by
    calc
      Section1.conjugateCharacter muJ =
          Section1.conjugateCharacter (Section1.conjugateCharacter muK) := by
            rw [hconj]
      _ = muK := by
            ext g
            simp [Section1.conjugateCharacter]
  have hj0 : j ≠ j0 := by
    intro hjEq
    have hbase :
        Section1.conjugateCharacter (Section4Scratch.piColumn piChar j0) =
          Section4Scratch.piColumn piChar j0 :=
      base_piColumn_conjugate_self_pf58 h46.1 hω h43b h45a
    have hkBase : muK = Section4Scratch.piColumn piChar j0 := by
      calc
        muK = Section1.conjugateCharacter (Section1.conjugateCharacter muK) := by
          ext g
          simp [Section1.conjugateCharacter]
        _ = Section1.conjugateCharacter muJ := by rw [hconj]
        _ = Section1.conjugateCharacter (Section4Scratch.piColumn piChar j0) := by
              simp [muJ, hjEq]
        _ = Section4Scratch.piColumn piChar j0 := hbase
    have hkSelf : Section1.conjugateCharacter muK = muK := by
      calc
        Section1.conjugateCharacter muK = muJ := hconj
        _ = Section4Scratch.piColumn piChar j0 := by simp [muJ, hjEq]
        _ = muK := hkBase.symm
    exact (h52a ⟨muK, hkS⟩).2 hkSelf.symm
  let Rμk : Finset (Section1.ClassFunction G) :=
    Finset.univ.image (muSignedFamily_pf58 (deltaSign k) (-deltaSign j) chi k j)
  have hRμk :
      signedOrthonormalFinset Rμk ∧
        τ (muK - muJ) = Finset.sum Rμk (fun φ => φ) := by
    simpa [Rμk, muK, muJ] using
      (piColumn_difference_family_pf58
        (i0 := i0) (j0 := j0) (ω := ω) (σL := σL) (σ := σ)
        (piChar := piChar) (deltaSign := deltaSign) (τ := τ) (chi := chi)
        (A := A) (K := K) (W1 := W1) (W2 := W2) (xChar := xChar)
        (k := k) (j := j)
        hω h43b h45a (h49a k hk0) (h49b k hk0) h48 hChiOrth hChiSigned
        hChiSigma hj0 hk0 hjk hdegjk)
  let Rμj : Finset (Section1.ClassFunction G) :=
    Finset.univ.image (muSignedFamily_pf58 (deltaSign j) (-deltaSign k) chi j k)
  have hRμj :
      signedOrthonormalFinset Rμj ∧
        τ (muJ - muK) = Finset.sum Rμj (fun φ => φ) := by
    simpa [Rμj, muK, muJ] using
      (piColumn_difference_family_pf58
        (i0 := i0) (j0 := j0) (ω := ω) (σL := σL) (σ := σ)
        (piChar := piChar) (deltaSign := deltaSign) (τ := τ) (chi := chi)
        (A := A) (K := K) (W1 := W1) (W2 := W2) (xChar := xChar)
        (k := j) (j := k)
        hω h43b h45a (h49a j hj0) (h49b j hj0) h48 hChiOrth hChiSigned
        hChiSigma hk0 hj0 hjk.symm hdegjk.symm)
  let pairS : Finset (Section1.ClassFunction L) := {muK, muJ}
  have hpairSubset : pairS ⊆ S := by
    intro ψ hψ
    simp [pairS] at hψ
    rcases hψ with rfl | rfl
    · exact hkS
    · exact hjS
  have hpairOr : ∀ X : pairS,
      (X : Section1.ClassFunction L) = muK ∨ (X : Section1.ClassFunction L) = muJ := by
    intro X
    have hmem :
        (X : Section1.ClassFunction L) ∈
          ({muK, muJ} : Finset (Section1.ClassFunction L)) := by
      simp [pairS]
    rcases Finset.mem_insert.mp hmem with hX | hX
    · exact Or.inl hX
    · exact Or.inr (Finset.mem_singleton.mp hX)
  let Rpair : pairS → Finset (Section1.ClassFunction G) := fun X =>
    if hX : (X : Section1.ClassFunction L) = muK then Rμk else Rμj
  have hpairSetup : hypothesis_5_2_setup_statement pairS := by
    refine ⟨⟨muK, by simp [pairS]⟩, ?_⟩
    intro X
    rcases hpairOr X with hX | hX
    · simpa [hX] using hkChar
    · simpa [hX] using hjChar
  have hpair52a : hypothesis_5_2_a_statement pairS := by
    intro X
    rcases hpairOr X with hX | hX
    · refine ⟨?_, ?_⟩
      · simp [hX, pairS, hconj, muK, muJ]
      · simpa [hX] using (h52a ⟨muK, hkS⟩).2
    · refine ⟨?_, ?_⟩
      · simp [hX, pairS, hconjSymm, muK, muJ]
      · intro hEq
        exact hmuJK (by simpa [hX, hconjSymm] using hEq)
  have hpair52b : hypothesis_5_2_b_statement pairS τ := by
    refine ⟨?_, ?_⟩
    · exact isCFLinearIsometryOnSpanOn_mono_pf58 hpairSubset h52b.1
    · intro ψ hψ
      exact h52b.2 ψ (integerSpanOn_mono_pf58 hpairSubset hψ)
  have hpair52c : hypothesis_5_2_c_statement pairS := by
    intro χ ψ hχ hψ hneq
    rcases hpairOr ⟨χ, hχ⟩ with rfl | rfl
    · rcases hpairOr ⟨ψ, hψ⟩ with rfl | rfl
      · exact (hneq rfl).elim
      · simpa [muK, muJ] using scalarProduct_piColumn_eq_zero_of_ne_pf58
          hω h43b hjk.symm
    · rcases hpairOr ⟨ψ, hψ⟩ with rfl | rfl
      · simpa [muK, muJ] using scalarProduct_piColumn_eq_zero_of_ne_pf58
          hω h43b hjk
      · exact (hneq rfl).elim
  have hpair52d : hypothesis_5_2_d_statement pairS τ Rpair := by
    intro X
    rcases hpairOr X with hX | hX
    · simpa [Rpair, hX, hconj, muK, muJ] using hRμk
    · have hjkCol : Section4Scratch.piColumn piChar j ≠ Section4Scratch.piColumn piChar k := by
        simpa [muJ, muK] using hmuJK
      simpa [Rpair, hX, hconjSymm, muK, muJ, hjkCol] using hRμj
  have hpairSelf_ne_zero :
      ∀ Y : pairS,
        Section1.scalarProduct L
          (Y : Section1.ClassFunction L)
          (Y : Section1.ClassFunction L) ≠ 0 := by
    intro Y hYY
    have hnorm : cfNormSq (Y : Section1.ClassFunction L) = 0 := by
      unfold cfNormSq
      simp [hYY]
    have hzero : (Y : Section1.ClassFunction L) = 0 := cfNormSq_eq_zero_pf58 hnorm
    exact (hpair52a Y).2 (by
      rw [hzero]
      ext g
      simp [Section1.conjugateCharacter])
  have hpair52e : hypothesis_5_2_e_statement pairS Rpair := by
    intro X Y hYX hYbarX
    rcases hpairOr X with hX | hX <;> rcases hpairOr Y with hY | hY
    · have hself := hYX
      rw [hX, hY] at hself
      exact False.elim (hpairSelf_ne_zero ⟨muK, by simp [pairS]⟩ hself)
    · have hself := hYbarX
      rw [hX, hY, hconj] at hself
      exact False.elim (hpairSelf_ne_zero ⟨muJ, by simp [pairS]⟩ hself)
    · have hself := hYbarX
      rw [hX, hY, hconjSymm] at hself
      exact False.elim (hpairSelf_ne_zero ⟨muK, by simp [pairS]⟩ hself)
    · have hself := hYX
      rw [hX, hY] at hself
      exact False.elim (hpairSelf_ne_zero ⟨muJ, by simp [pairS]⟩ hself)
  have hpairSetSubset :
      ({muK, Section1.conjugateCharacter muK} : Finset (Section1.ClassFunction L)) ⊆ S := by
    intro ψ hψ
    simp at hψ
    rcases hψ with rfl | rfl
    · exact hkS
    · rw [hconj]
      exact hjS
  have hpairIso :
      isCFLinearIsometryOnSpan
        ({muK, Section1.conjugateCharacter muK} : Finset (Section1.ClassFunction L)) T1 := by
    exact isCFLinearIsometryOnSpan_mono_pf58 hpairSetSubset hIso
  have hpairVirt :
      mapsIntegerSpanToVirtualCharacters
        ({muK, Section1.conjugateCharacter muK} : Finset (Section1.ClassFunction L)) T1 := by
    exact mapsIntegerSpanToVirtualCharacters_mono_pf58 hpairSetSubset hT1virt
  have hmuKSpan : integerSpan S muK := integerSpan_of_mem_pf58 S hkS
  have hmuJSpan : integerSpan S muJ := integerSpan_of_mem_pf58 S hjS
  have hpairDiffOn :
      integerSpanOn S puncturedSet (muK - Section1.conjugateCharacter muK) := by
    refine ⟨?_, ?_⟩
    · simpa [muK, muJ, hconj] using integerSpan_sub_pf58 hmuKSpan hmuJSpan
    · apply (supportedOn_puncturedSet_iff_degree_eq_zero_pf58 _).2
      rw [Section1.degree_apply, hconj]
      simpa [Section1.degree_apply] using sub_eq_zero.mpr hdegjk.symm
  have hpairAgree :
      T1 (muK - Section1.conjugateCharacter muK) =
        τ (muK - Section1.conjugateCharacter muK) := by
    exact hAgree _ hpairDiffOn
  let Xk : pairS := ⟨muK, by simp [pairS]⟩
  have hsubset_muK :
      isSubsetSumOf (Rpair Xk) (T1 muK) := by
    exact theorem_5_5 pairS τ Rpair
      hpairSetup hpair52a hpair52b hpair52c hpair52d hpair52e
      Xk T1 hpairIso hpairVirt hpairAgree
  have hsubset_muK' : isSubsetSumOf Rμk (T1 muK) := by
    simpa [Xk, Rpair] using hsubset_muK
  have hCtx53 :
      theorem_5_3_b_core_context_statement
        K W1 W2 W H A i0 j0 ω σL σ piChar xChar deltaSign τ := by
    exact
      ⟨h46, hτcyclic, hτA0, hτisoA0, hτpunctA0, hτvirtA0,
        h52bOfInd, hω, chi, hChiOrth, hChiSigned, hChiSigma,
        h43b, h43c, h43d, h45a, h45b, h47, h48, h49a, h49b, h410⟩
  rcases theorem_5_3_b_core
      (K := K) (W1 := W1) (W2 := W2) (W := W) (H := H) (A := A)
      (i0 := i0) (j0 := j0) (ω := ω) (σL := σL) (σ := σ)
      (piChar := piChar) (xChar := xChar) (deltaSign := deltaSign)
      (τ := τ) (S := S) hCtx53 hSne h52a hInd with
    ⟨R53, hsetup53, h52a53, h52b53, h52c53, h52d53, h52e53, hExtra53⟩
  have hXpairSubset :
      ({(X : Section1.ClassFunction L),
        Section1.conjugateCharacter (X : Section1.ClassFunction L)} :
          Finset (Section1.ClassFunction L)) ⊆ S := by
    intro ψ hψ
    simp at hψ
    rcases hψ with rfl | rfl
    · exact X.2
    · exact (h52a X).1
  have hXpairIso :
      isCFLinearIsometryOnSpan
        ({(X : Section1.ClassFunction L),
          Section1.conjugateCharacter (X : Section1.ClassFunction L)} :
            Finset (Section1.ClassFunction L)) T1 :=
    isCFLinearIsometryOnSpan_mono_pf58 hXpairSubset hIso
  have hXpairVirt :
      mapsIntegerSpanToVirtualCharacters
        ({(X : Section1.ClassFunction L),
          Section1.conjugateCharacter (X : Section1.ClassFunction L)} :
            Finset (Section1.ClassFunction L)) T1 :=
    mapsIntegerSpanToVirtualCharacters_mono_pf58 hXpairSubset hT1virt
  have hXspan : integerSpan S (X : Section1.ClassFunction L) :=
    integerSpan_of_mem_pf58 S X.2
  have hXbarSpan :
      integerSpan S (Section1.conjugateCharacter (X : Section1.ClassFunction L)) :=
    integerSpan_of_mem_pf58 S (h52a X).1
  have hXdiffOn :
      integerSpanOn S puncturedSet
        ((X : Section1.ClassFunction L) -
          Section1.conjugateCharacter (X : Section1.ClassFunction L)) := by
    refine ⟨integerSpan_sub_pf58 hXspan hXbarSpan, ?_⟩
    rw [Section1.supportedOn_iff]
    intro g hg
    have hg1 : g = 1 := by simpa [puncturedSet] using hg
    subst hg1
    have hdegConj :
        Section1.degree
            (Section1.conjugateCharacter (X : Section1.ClassFunction L)) =
          Section1.degree (X : Section1.ClassFunction L) :=
      degree_conjugateCharacter_eq_of_isCharacter_pf58
        (isCharacter_of_isIrreducibleCharacterOnGroup_pf58 hXirr)
    simpa [Section1.degree_apply, sub_eq_zero] using hdegConj.symm
  have hXagree :
      T1 ((X : Section1.ClassFunction L) -
          Section1.conjugateCharacter (X : Section1.ClassFunction L)) =
        τ ((X : Section1.ClassFunction L) -
          Section1.conjugateCharacter (X : Section1.ClassFunction L)) :=
    hAgree _ hXdiffOn
  have hsubset_X :
      isSubsetSumOf (R53 X) (T1 (X : Section1.ClassFunction L)) :=
    theorem_5_5 S τ R53
      hsetup53 h52a53 h52b53 h52c53 h52d53 h52e53
      X T1 hXpairIso hXpairVirt hXagree
  have hXorthChi :
      ∀ i j, Section1.scalarProduct G (T1 (X : Section1.ClassFunction L)) (chi i j) = 0 := by
    intro i j
    have hRextra :
        orthogonalFinsets (R53 X)
          (Finset.univ.image fun p : I × J => σ (ω p.1 p.2)) :=
      hExtra53 X hXirr
    have hmemChi :
        chi i j ∈ (Finset.univ.image fun p : I × J => σ (ω p.1 p.2)) := by
      refine Finset.mem_image.mpr ?_
      exact ⟨(i, j), by simp, by simpa using hChiSigma i j⟩
    exact scalarProduct_subsetSum_left_eq_zero_of_orthogonalFinsets_pf58
      hsubset_X hRextra hmemChi
  rcases positive_degree_nat_of_isIrreducibleCharacterOnGroup_pf58 hXirr with
    ⟨nX, hnXpos, hdegXnat⟩
  rcases degree_eq_nat_of_isCharacter_pf58 hkChar with ⟨mK, hdegKnat⟩
  have hparticular :
      ∀ i q,
        Section1.scalarProduct G (T1 muK)
          ((chi i q - chi i0 q) - (chi i j0 - chi i0 j0)) = 0 := by
    intro i q
    let bridge : Section1.ClassFunction L :=
      deltaSign q • piChar i q - deltaSign q • piChar i0 q -
        piChar i j0 + piChar i0 j0
    let target : Section1.ClassFunction G :=
      (chi i q - chi i0 q) - (chi i j0 - chi i0 j0)
    let combo : Section1.ClassFunction L :=
      ((nX : ℂ) • muK) - ((mK : ℂ) • (X : Section1.ClassFunction L))
    have hcomboOn : integerSpanOn S puncturedSet combo := by
      simpa [combo] using
        (degree_zero_combo_mem_integerSpanOn_punctured_pf58
          (S := S) (X := muK) (ψ := (X : Section1.ClassFunction L))
          (m := nX) (n := mK) hmuKSpan hXspan hdegKnat hdegXnat)
    have hcomboA0 :
        Section1.supportedOn combo
          (Section4Scratch.primeDadeA0Set W1 W2 W A) :=
      induced_family_supportedOn_primeDadeA0_of_punctured_pf58
        h46 h47 hInd hcomboOn
    have hbridgeA0 :
        Section1.supportedOn bridge
          (Section4Scratch.primeDadeA0Set W1 W2 W A) := by
      simpa [bridge] using
        source_bridge_supportedOn_primeDadeA0_pf58
          (A := A) hω h43b i q
    have hcomboClass : Section1.IsClassFunction combo := by
      have hmuClass : Section1.IsClassFunction muK :=
        Section1.isCharacter_isClassFunction muK hkChar
      have hXClass : Section1.IsClassFunction (X : Section1.ClassFunction L) :=
        Section1.isBookIrreducibleCharacter_isClassFunction
          (X : Section1.ClassFunction L)
          (isBookIrreducibleCharacter_of_group_irreducible_pf58 hXirr)
      have h1 : Section1.IsClassFunction ((nX : ℂ) • muK) :=
        Section1.isClassFunction_smul (nX : ℂ) muK hmuClass
      have h2 :
          Section1.IsClassFunction
            ((mK : ℂ) • (X : Section1.ClassFunction L)) :=
        Section1.isClassFunction_smul (mK : ℂ) (X : Section1.ClassFunction L) hXClass
      intro x g
      simp [combo, h1 x g, h2 x g]
    have hbridgeClass : Section1.IsClassFunction bridge := by
      rcases h43b with ⟨_hσmap, _hsign, hirr, _hdistinct, _hind, _hSigmaL⟩
      have h1 : Section1.IsClassFunction (deltaSign q • piChar i q) :=
        Section1.isClassFunction_smul
          (deltaSign q) (piChar i q)
          (Section1.isBookIrreducibleCharacter_isClassFunction (piChar i q)
            (isBookIrreducibleCharacter_of_group_irreducible_pf58 (hirr i q)))
      have h2 : Section1.IsClassFunction (deltaSign q • piChar i0 q) :=
        Section1.isClassFunction_smul
          (deltaSign q) (piChar i0 q)
          (Section1.isBookIrreducibleCharacter_isClassFunction (piChar i0 q)
            (isBookIrreducibleCharacter_of_group_irreducible_pf58 (hirr i0 q)))
      have h3 : Section1.IsClassFunction (piChar i j0) :=
        Section1.isBookIrreducibleCharacter_isClassFunction (piChar i j0)
          (isBookIrreducibleCharacter_of_group_irreducible_pf58 (hirr i j0))
      have h4 : Section1.IsClassFunction (piChar i0 j0) :=
        Section1.isBookIrreducibleCharacter_isClassFunction (piChar i0 j0)
          (isBookIrreducibleCharacter_of_group_irreducible_pf58 (hirr i0 j0))
      intro x g
      simp [bridge, h1 x g, h2 x g, h3 x g, h4 x g]
    have hcomboAgree : T1 combo = τ combo := hAgree combo hcomboOn
    have htarget_eq : τ bridge = target := by
      calc
        τ bridge =
            (σ (ω i q) - σ (ω i0 q)) -
              (σ (ω i j0) - σ (ω i0 j0)) := by
              simpa [bridge] using h410 i q
        _ = target := by
              simp [target, hChiSigma]
    have hX_bridge_zero :
        Section1.scalarProduct L (X : Section1.ClassFunction L) bridge = 0 := by
      simpa [bridge] using
        Section5.scalarProduct_irreducible_source_bridge_eq_zero_pf53
          h46 hω h43b h45a h45b hInd X hXirr i q
    have hmu_iq :
        Section1.scalarProduct L muK (piChar i q) =
          if k = q then (1 : ℂ) else 0 := by
      simpa [muK] using scalarProduct_piColumn_piChar_eq_ite_pf58 hω h43b i0 i k q
    have hmu_i0q :
        Section1.scalarProduct L muK (piChar i0 q) =
          if k = q then (1 : ℂ) else 0 := by
      simpa [muK] using scalarProduct_piColumn_piChar_eq_ite_pf58 hω h43b i0 i0 k q
    have hmu_ij0 :
        Section1.scalarProduct L muK (piChar i j0) = 0 := by
      simpa [muK, hk0] using scalarProduct_piColumn_piChar_eq_ite_pf58 hω h43b i0 i k j0
    have hmu_i0j0 :
        Section1.scalarProduct L muK (piChar i0 j0) = 0 := by
      simpa [muK, hk0] using scalarProduct_piColumn_piChar_eq_ite_pf58 hω h43b i0 i0 k j0
    have hdeltaStar : star (deltaSign q) = deltaSign q := by
      rcases h43b with ⟨_hσmap, hsign, _hirr, _hdistinct, _hind, _hSigmaL⟩
      rcases hsign q with h | h <;> rw [h] <;> simp
    have hmu_bridge_zero :
        Section1.scalarProduct L muK bridge = 0 := by
      calc
        Section1.scalarProduct L muK bridge =
            (star (deltaSign q) * Section1.scalarProduct L muK (piChar i q) -
              star (deltaSign q) * Section1.scalarProduct L muK (piChar i0 q)) -
              Section1.scalarProduct L muK (piChar i j0) +
              Section1.scalarProduct L muK (piChar i0 j0) := by
              rw [show bridge =
                  (deltaSign q • piChar i q - deltaSign q • piChar i0 q) -
                    piChar i j0 + piChar i0 j0 by rfl]
              rw [scalarProduct_add_right_pf58, scalarProduct_sub_right_pf58,
                scalarProduct_sub_right_pf58, Section1.scalarProduct_smul_right,
                Section1.scalarProduct_smul_right]
        _ = 0 := by
              by_cases hkq : k = q <;> simp [hmu_iq, hmu_i0q, hmu_ij0, hmu_i0j0, hkq]
    have hsource_combo_zero :
        Section1.scalarProduct L combo bridge = 0 := by
      calc
        Section1.scalarProduct L combo bridge =
            Section1.scalarProduct L ((nX : ℂ) • muK) bridge -
              Section1.scalarProduct L ((mK : ℂ) • (X : Section1.ClassFunction L)) bridge := by
              change
                Section1.scalarProduct L
                    (((nX : ℂ) • muK) -
                      ((mK : ℂ) • (X : Section1.ClassFunction L))) bridge =
                  Section1.scalarProduct L ((nX : ℂ) • muK) bridge -
                    Section1.scalarProduct L ((mK : ℂ) • (X : Section1.ClassFunction L)) bridge
              rw [scalarProduct_sub_left_pf58]
        _ = (nX : ℂ) * Section1.scalarProduct L muK bridge -
              (mK : ℂ) * Section1.scalarProduct L (X : Section1.ClassFunction L) bridge := by
              rw [Section1.scalarProduct_smul_left, Section1.scalarProduct_smul_left]
        _ = 0 := by simp [hmu_bridge_zero, hX_bridge_zero]
    have htarget_X_zero :
        Section1.scalarProduct G (T1 (X : Section1.ClassFunction L)) target = 0 := by
      calc
        Section1.scalarProduct G (T1 (X : Section1.ClassFunction L)) target =
            (Section1.scalarProduct G (T1 (X : Section1.ClassFunction L)) (chi i q) -
              Section1.scalarProduct G (T1 (X : Section1.ClassFunction L)) (chi i0 q)) -
              (Section1.scalarProduct G (T1 (X : Section1.ClassFunction L)) (chi i j0) -
                Section1.scalarProduct G (T1 (X : Section1.ClassFunction L)) (chi i0 j0)) := by
              change
                Section1.scalarProduct G (T1 (X : Section1.ClassFunction L))
                    ((chi i q - chi i0 q) - (chi i j0 - chi i0 j0)) =
                  (Section1.scalarProduct G (T1 (X : Section1.ClassFunction L)) (chi i q) -
                    Section1.scalarProduct G (T1 (X : Section1.ClassFunction L)) (chi i0 q)) -
                    (Section1.scalarProduct G (T1 (X : Section1.ClassFunction L)) (chi i j0) -
                      Section1.scalarProduct G (T1 (X : Section1.ClassFunction L)) (chi i0 j0))
              rw [scalarProduct_sub_right_pf58, scalarProduct_sub_right_pf58,
                scalarProduct_sub_right_pf58]
        _ = 0 := by simp [hXorthChi]
    have htarget_combo_zero :
        Section1.scalarProduct G (T1 combo) target = 0 := by
      calc
        Section1.scalarProduct G (T1 combo) target =
            Section1.scalarProduct G (τ combo) (τ bridge) := by
              rw [hcomboAgree, htarget_eq]
        _ = Section1.scalarProduct L combo bridge :=
              hτisoA0 combo bridge hcomboClass hbridgeClass hcomboA0 hbridgeA0
        _ = 0 := hsource_combo_zero
    have htarget_combo_expand :
        Section1.scalarProduct G (T1 combo) target =
          (nX : ℂ) * Section1.scalarProduct G (T1 muK) target -
            (mK : ℂ) * Section1.scalarProduct G (T1 (X : Section1.ClassFunction L)) target := by
      have hmap :
          T1 combo = ((nX : ℂ) • T1 muK) -
            ((mK : ℂ) • T1 (X : Section1.ClassFunction L)) := by
        simp [combo, muK]
      rw [hmap, scalarProduct_sub_left_pf58, Section1.scalarProduct_smul_left,
        Section1.scalarProduct_smul_left]
    have hmul_zero :
        (nX : ℂ) * Section1.scalarProduct G (T1 muK) target = 0 := by
      have h := htarget_combo_zero
      rw [htarget_combo_expand, htarget_X_zero] at h
      simpa using h
    have hnX_ne : (nX : ℂ) ≠ 0 := by
      exact_mod_cast hnXpos.ne'
    exact mul_eq_zero.mp hmul_zero |>.resolve_left hnX_ne
  rcases hsubset_muK' with ⟨E, hEsub, hT1sum⟩
  let left : I → Section1.ClassFunction G := fun i =>
    muSignedFamily_pf58 (deltaSign k) (-deltaSign j) chi k j (Sum.inl i)
  let right : I → Section1.ClassFunction G := fun i =>
    muSignedFamily_pf58 (deltaSign k) (-deltaSign j) chi k j (Sum.inr i)
  let leftImage : Finset (Section1.ClassFunction G) := Finset.univ.image left
  let rightImage : Finset (Section1.ClassFunction G) := Finset.univ.image right
  have hsign : ∀ q : J, Section1.IsSign (deltaSign q) := h43b.2.1
  have hRμkSigned :
      signedOrthonormalFinset
        (Finset.univ.image
          (muSignedFamily_pf58 (deltaSign k) (-deltaSign j) chi k j)) := by
    simpa [Rμk] using hRμk.1
  have hEsubR :
      E ⊆ Finset.univ.image
        (muSignedFamily_pf58 (deltaSign k) (-deltaSign j) chi k j) := by
    simpa [Rμk] using hEsub
  have hcoeffK :
      ∀ i : I,
        Section1.scalarProduct G (T1 muK) (chi i k) =
          deltaSign k * (if left i ∈ E then (1 : ℂ) else 0) := by
    intro i
    rw [hT1sum]
    simpa [left] using
      (scalarProduct_subsetSum_muSignedFamily_left_chi_pf58
        (deltaLeft := deltaSign k) (deltaRight := -deltaSign j)
        (chi := chi) (j := k) (k := j)
        (E := E) (hLeft := hsign k) hRμkSigned hEsubR i)
  have hcoeffJ :
      ∀ i : I,
        Section1.scalarProduct G (T1 muK) (chi i j) =
          (-deltaSign j) * (if right i ∈ E then (1 : ℂ) else 0) := by
    intro i
    rw [hT1sum]
    simpa [right] using
      (scalarProduct_subsetSum_muSignedFamily_right_chi_pf58
        (deltaLeft := deltaSign k) (deltaRight := -deltaSign j)
        (chi := chi) (j := k) (k := j)
        (E := E) (hRight := isSign_neg_pf58 (hsign j)) hRμkSigned hEsubR i)
  have hcoeffJ0 :
      ∀ i : I, Section1.scalarProduct G (T1 muK) (chi i j0) = 0 := by
    intro i
    rw [hT1sum]
    exact
      scalarProduct_subsetSum_muSignedFamily_chi_eq_zero_of_ne_pf58
        (deltaLeft := deltaSign k) (deltaRight := -deltaSign j)
        (chi := chi) (j := k) (k := j) (q := j0)
        hChiOrth hEsubR hk0.symm hj0.symm i
  have hleftVal :
      ∀ i : I,
        (if left i ∈ E then (1 : ℂ) else 0) =
          if left i0 ∈ E then (1 : ℂ) else 0 := by
    intro i
    have h := hparticular i k
    rw [scalarProduct_sub_right_pf58, scalarProduct_sub_right_pf58,
      scalarProduct_sub_right_pf58, hcoeffK i, hcoeffK i0, hcoeffJ0 i,
      hcoeffJ0 i0] at h
    have hmul :
        deltaSign k *
          ((if left i ∈ E then (1 : ℂ) else 0) -
            (if left i0 ∈ E then (1 : ℂ) else 0)) = 0 := by
      linear_combination h
    exact sub_eq_zero.mp
      ((mul_eq_zero.mp hmul).resolve_left (isSign_ne_zero_pf58 (hsign k)))
  have hrightVal :
      ∀ i : I,
        (if right i ∈ E then (1 : ℂ) else 0) =
          if right i0 ∈ E then (1 : ℂ) else 0 := by
    intro i
    have h := hparticular i j
    rw [scalarProduct_sub_right_pf58, scalarProduct_sub_right_pf58,
      scalarProduct_sub_right_pf58, hcoeffJ i, hcoeffJ i0, hcoeffJ0 i,
      hcoeffJ0 i0] at h
    have hmul :
        (-deltaSign j) *
          ((if right i ∈ E then (1 : ℂ) else 0) -
            (if right i0 ∈ E then (1 : ℂ) else 0)) = 0 := by
      linear_combination h
    exact sub_eq_zero.mp
      ((mul_eq_zero.mp hmul).resolve_left
        (isSign_ne_zero_pf58 (isSign_neg_pf58 (hsign j))))
  have hleftMem : ∀ i : I, left i ∈ E ↔ left i0 ∈ E := by
    intro i
    exact iff_of_ite_one_zero_eq_pf58 (hleftVal i)
  have hrightMem : ∀ i : I, right i ∈ E ↔ right i0 ∈ E := by
    intro i
    exact iff_of_ite_one_zero_eq_pf58 (hrightVal i)
  have hEcardComplex : (E.card : ℂ) = (Fintype.card I : ℂ) := by
    calc
      (E.card : ℂ) =
          Section1.scalarProduct G (T1 muK) (T1 muK) := by
            rw [hT1sum]
            exact (subsetSum_self_eq_card_pf58 hRμk.1 hEsub).symm
      _ = Section1.scalarProduct L muK muK :=
            hIso muK muK hmuKSpan hmuKSpan
      _ = (Fintype.card I : ℂ) := by
            simpa [muK] using scalarProduct_piColumn_eq_card_ite_pf58 hω h43b k k
  have hEcard : E.card = Fintype.card I :=
    Nat.cast_injective hEcardComplex
  have hμInj :
      Function.Injective
        (muSignedFamily_pf58 (deltaSign k) (-deltaSign j) chi k j) :=
    muSignedFamily_injective_pf58
      (deltaLeft := deltaSign k) (deltaRight := -deltaSign j)
      (chi := chi) (j := k) (k := j)
      (hLeft := hsign k) (hRight := isSign_neg_pf58 (hsign j))
      hChiOrth hjk.symm
  have hleftInj : Function.Injective left := by
    intro a b hab
    exact Sum.inl.inj (hμInj (by simpa [left] using hab))
  have hrightInj : Function.Injective right := by
    intro a b hab
    exact Sum.inr.inj (hμInj (by simpa [right] using hab))
  have hleftCard : leftImage.card = Fintype.card I := by
    simpa [leftImage] using
      (Finset.card_image_of_injective (Finset.univ : Finset I) hleftInj)
  have hrightCard : rightImage.card = Fintype.card I := by
    simpa [rightImage] using
      (Finset.card_image_of_injective (Finset.univ : Finset I) hrightInj)
  by_cases hleftBase : left i0 ∈ E
  · have hleftImage_sub : leftImage ⊆ E := by
      intro φ hφ
      rcases Finset.mem_image.mp hφ with ⟨i, _hi, rfl⟩
      exact (hleftMem i).2 hleftBase
    have hE_eq_left : E = leftImage := by
      symm
      apply Finset.eq_of_subset_of_card_le hleftImage_sub
      rw [hEcard, hleftCard]
    have hsum_left :
        Finset.sum E (fun φ => φ) = ∑ i : I, deltaSign k • chi i k := by
      rw [hE_eq_left]
      simpa [leftImage, left] using
        (sum_image_muSignedFamily_left_pf58
          (deltaLeft := deltaSign k) (deltaRight := -deltaSign j)
          (chi := chi) (j := k) (k := j) hμInj)
    left
    change T1 muK = deltaSign k • Section4Scratch.omegaColumnSigma σ ω k
    calc
      T1 muK = Finset.sum E (fun φ => φ) := hT1sum
      _ = ∑ i : I, deltaSign k • chi i k := hsum_left
      _ = deltaSign k • (∑ i : I, chi i k) := by
            rw [Finset.smul_sum]
      _ = deltaSign k • Section4Scratch.omegaColumnSigma σ ω k := by
            rw [omegaColumnSigma_eq_sumChi_pf58 hChiSigma k]
  ·
    have hnoLeft : ∀ i : I, left i ∉ E := by
      intro i hi
      exact hleftBase ((hleftMem i).1 hi)
    have hE_sub_right : E ⊆ rightImage := by
        intro φ hφE
        have hφR :
            φ ∈ Finset.univ.image
              (muSignedFamily_pf58 (deltaSign k) (-deltaSign j) chi k j) :=
          hEsubR hφE
        rcases Finset.mem_image.mp hφR with ⟨p, _hp, hpφ⟩
        cases p with
        | inl r =>
            exact False.elim (hnoLeft r (by
              simpa [left, hpφ] using hφE))
        | inr r =>
            exact Finset.mem_image.mpr ⟨r, by simp, by simpa [right] using hpφ⟩
    have hE_eq_right : E = rightImage := by
        apply Finset.eq_of_subset_of_card_le hE_sub_right
        rw [hEcard, hrightCard]
    have hsum_right :
          Finset.sum E (fun φ => φ) = ∑ i : I, (-deltaSign j) • chi i j := by
        rw [hE_eq_right]
        simpa [rightImage, right] using
          (sum_image_muSignedFamily_right_pf58
            (deltaLeft := deltaSign k) (deltaRight := -deltaSign j)
            (chi := chi) (j := k) (k := j) hμInj)
    have hdelta_jk : deltaSign j = deltaSign k := by
        exact (h48 i0 j k hj0 hk0
          (degree_entry_eq_of_equal_degree_column_pf58 K piChar xChar h45a hdegjk)).2.1
    have hsecondImage :
          T1 muK = (-deltaSign k) • Section4Scratch.omegaColumnSigma σ ω j := by
        calc
          T1 muK = Finset.sum E (fun φ => φ) := hT1sum
          _ = ∑ i : I, (-deltaSign j) • chi i j := hsum_right
          _ = (-deltaSign j) • (∑ i : I, chi i j) := by
                rw [Finset.smul_sum]
          _ = (-deltaSign j) • Section4Scratch.omegaColumnSigma σ ω j := by
                rw [omegaColumnSigma_eq_sumChi_pf58 hChiSigma j]
          _ = (-deltaSign k) • Section4Scratch.omegaColumnSigma σ ω j := by
                rw [hdelta_jk]
    right
    refine ⟨by simpa [muK] using hsecondImage, ?_⟩
    intro l hl0 hlS hdegl
    by_cases hlj : l = j
    · exact Or.inl hlj
    · by_cases hlk : l = k
      · exact Or.inr hlk
      · exfalso
        let muL : Section1.ClassFunction L := Section4Scratch.piColumn piChar l
        have hl_mem_eq : l ∈ Section4Scratch.equalDegreeColumnSet piChar j0 l := by
          exact ⟨hl0, rfl⟩
        rcases ((h49a l hl0) hl0).1 l hl_mem_eq with ⟨m, hmSet, hconjLm, _hmneCol⟩
        have hm0 : m ≠ j0 := hmSet.1
        have hmk : m ≠ k := by
          intro hmk
          have hconjLk :
              Section1.conjugateCharacter (Section4Scratch.piColumn piChar l) =
                Section4Scratch.piColumn piChar k := by
            simpa [hmk] using hconjLm
          have hljCol :
              Section4Scratch.piColumn piChar l =
                Section4Scratch.piColumn piChar j := by
            calc
              Section4Scratch.piColumn piChar l =
                  Section1.conjugateCharacter
                    (Section1.conjugateCharacter (Section4Scratch.piColumn piChar l)) := by
                      rw [conjugateCharacter_conjugateCharacter_pf58]
              _ = Section1.conjugateCharacter (Section4Scratch.piColumn piChar k) := by
                    rw [hconjLk]
              _ = Section4Scratch.piColumn piChar j := hconj
          exact hlj ((piColumn_injective_pf58 hω h43b) hljCol)
        rcases
            subsetSum_piColumn_of_conjugate_pf58
              (K := K) (W1 := W1) (W2 := W2) (W := W)
              (A := A) (i0 := i0) (j0 := j0) (ω := ω)
              (σL := σL) (σ := σ) (piChar := piChar) (xChar := xChar)
              (deltaSign := deltaSign) (τ := τ) (chi := chi) (S := S)
              hω h43b h45a h48 h49a h49b hChiOrth hChiSigned hChiSigma
              h52a h52b hl0 hlS hm0 hconjLm T1 hIso hT1virt hAgree with
          ⟨_hRμl, hsubset_muL⟩
        rcases hsubset_muL with ⟨F, hFsub, hT1muLsum⟩
        have hFsubR :
            F ⊆ Finset.univ.image
              (muSignedFamily_pf58 (deltaSign l) (-deltaSign m) chi l m) := by
          simpa using hFsub
        have hmuL_chik :
            Section1.scalarProduct G (T1 muL) (chi i0 k) = 0 := by
          rw [hT1muLsum]
          exact
            scalarProduct_subsetSum_muSignedFamily_chi_eq_zero_of_ne_pf58
              (deltaLeft := deltaSign l) (deltaRight := -deltaSign m)
              (chi := chi) (j := l) (k := m) (q := k)
              hChiOrth hFsubR (fun hkl => hlk hkl.symm) (fun hkm => hmk hkm.symm) i0
        have hmuK_chik :
            Section1.scalarProduct G (T1 muK) (chi i0 k) = 0 := by
          rw [hsecondImage, Section1.scalarProduct_smul_left]
          have hjkCoeff :
              Section1.scalarProduct G
                  (Section4Scratch.omegaColumnSigma σ ω j) (chi i0 k) = 0 := by
            simpa [hjk] using
              scalarProduct_omegaColumnSigma_chi_eq_ite_pf58 hChiOrth hChiSigma i0 j k
          simp [hjkCoeff]
        have hdiffOn :
            integerSpanOn S puncturedSet (muK - muL) := by
          refine ⟨?_, ?_⟩
          · exact integerSpan_sub_pf58 hmuKSpan
              (integerSpan_of_mem_pf58 S (by simpa [muL] using hlS))
          · apply (supportedOn_puncturedSet_iff_degree_eq_zero_pf58 _).2
            rw [Section1.degree_apply]
            simpa [muK, muL, Section1.degree_apply] using sub_eq_zero.mpr hdegl.symm
        have hdiff_eq :
            T1 muK - T1 muL =
              deltaSign k •
                (Section4Scratch.omegaColumnSigma σ ω k -
                  Section4Scratch.omegaColumnSigma σ ω l) := by
          calc
            T1 muK - T1 muL = T1 (muK - muL) := by
              simp [muK, muL]
            _ = τ (muK - muL) := hAgree _ hdiffOn
            _ = deltaSign k •
                (Section4Scratch.omegaColumnSigma σ ω k -
                  Section4Scratch.omegaColumnSigma σ ω l) := by
              simpa [muK, muL] using
                tau_piColumn_sub_eq_signed_omegaColumnSigma_sub_pf58
                  (h49a k hk0) (h49b k hk0) hk0
                  (j := l) ⟨hl0, hdegl⟩
        have hleftScalar :
            Section1.scalarProduct G (T1 muK - T1 muL) (chi i0 k) = 0 := by
          rw [scalarProduct_sub_left_pf58, hmuK_chik, hmuL_chik]
          simp
        have hrightScalar :
            Section1.scalarProduct G
                (deltaSign k •
                  (Section4Scratch.omegaColumnSigma σ ω k -
                    Section4Scratch.omegaColumnSigma σ ω l)) (chi i0 k) =
              deltaSign k := by
          rw [Section1.scalarProduct_smul_left, scalarProduct_sub_left_pf58]
          have hkk :
              Section1.scalarProduct G
                  (Section4Scratch.omegaColumnSigma σ ω k) (chi i0 k) = 1 := by
            simpa using
              scalarProduct_omegaColumnSigma_chi_eq_ite_pf58 hChiOrth hChiSigma i0 k k
          have hlkCoeff :
              Section1.scalarProduct G
                  (Section4Scratch.omegaColumnSigma σ ω l) (chi i0 k) = 0 := by
            simpa [hlk] using
              scalarProduct_omegaColumnSigma_chi_eq_ite_pf58 hChiOrth hChiSigma i0 l k
          simp [hkk, hlkCoeff]
        have hzero_delta : deltaSign k = 0 := by
          calc
            deltaSign k =
                Section1.scalarProduct G
                  (deltaSign k •
                    (Section4Scratch.omegaColumnSigma σ ω k -
                      Section4Scratch.omegaColumnSigma σ ω l)) (chi i0 k) := hrightScalar.symm
            _ = Section1.scalarProduct G (T1 muK - T1 muL) (chi i0 k) := by
                  rw [hdiff_eq]
            _ = 0 := hleftScalar
        exact (isSign_ne_zero_pf58 (hsign k)) hzero_delta

public theorem theorem_5_8
    {G : Type u} [Group G] [Finite G]
    (L : Subgroup G) [Finite L]
    (K W1 W2 W H : Subgroup L)
    (A : Set L)
    {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J]
    (i0 : I) (j0 : J)
    (ω : I → J → Section1.ClassFunction W)
    (σL : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction L)
    (σ : Section1.ClassFunction W →ₗ[ℂ] Section1.ClassFunction G)
    (piChar : I → J → Section1.ClassFunction L)
    (xChar : J → Section1.ClassFunction K)
    (deltaSign : J → ℂ)
    (τ : Section1.ClassFunction L →ₗ[ℂ] Section1.ClassFunction G)
    (H_A H_A0 : G → Subgroup G)
    (S : Finset (Section1.ClassFunction L)) :
    theorem_5_8_statement
      L K W1 W2 W H A i0 j0 ω σL σ piChar xChar deltaSign τ H_A H_A0 S := by
  classical
  intro h46 h52a hIrrMem hInd k hk0 hkS j hconj T1 hIso hT1virt hAgree
  exact theorem_5_8_core K W1 W2 W H A i0 j0
    ω σL σ piChar xChar deltaSign τ S
    (theorem_5_3_b_core_context_of_full_pf53 L h46)
    h52a hIrrMem hInd k hk0 hkS j hconj T1 hIso hT1virt hAgree

end CFSG.Section5
