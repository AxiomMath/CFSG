module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitF4Three
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicSix
public import CFSG.RankThree.Chevalley.SteinbergBUF4A2Sextic
public import CFSG.LieType.Universal.Unitary.Comparison

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Chevalley.F4Weyl CFSG.RankThree.E6
open scoped Matrix

namespace F4Nonsplit

theorem card_unitarySL3 {L : Type} [Field L] [Finite L] [CharP L 2] {f : ℕ}
    (hL : Nat.card L = (2 ^ f) ^ 2) (σ : L ≃+* L) (hσ : ∀ b, σ b = b ^ 2 ^ f) :
    Nat.card {A : Matrix.SpecialLinearGroup (Fin 3) L //
        ((A : Matrix (Fin 3) (Fin 3) L).map σ)ᵀ * A = 1} =
      (2 ^ f) ^ 3 * ((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 3 + 1) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ' : σ = CFSG.LieType.BorelTits.unitaryInvolution L 2 f := RingEquiv.ext fun b => by
    rw [hσ, CFSG.LieType.BorelTits.unitaryInvolution_apply]
  subst hσ'
  rw [← CFSG.RankThree.PartOne.D4RC.rcl_card_statedSU_three hL,
    ← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hL 3]
  refine Nat.card_congr
    { toFun := fun A => ⟨Matrix.SpecialLinearGroup.toGL A.1,
        ⟨A.1.2, A.2⟩⟩
      invFun := fun B => ⟨⟨((B : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L), B.2.1⟩, B.2.2⟩
      left_inv := fun A => rfl
      right_inv := fun B => Subtype.ext (Units.ext rfl) }

theorem exists_f4A2UnitaryGroup
    {L : Type} [Field L] [CharP L 2] (σ : L ≃+* L) (κ : F4A2Kind) :
    ∃ U : Subgroup (ModGL .F4 L), ∀ w, w ∈ U ↔ ∃ hw : w ∈ subsystemGroup .F4 L {κ.i, κ.j},
      ((f4A2Equiv L κ ⟨w, hw⟩ : Matrix (Fin 3) (Fin 3) L).map σ)ᵀ *
        (f4A2Equiv L κ ⟨w, hw⟩ : Matrix (Fin 3) (Fin 3) L) = 1 := by
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : WeylGroup Tag.F4, ∀ v : Fin Tag.F4.rank → ℤ, w₀ • v = -v :=
    ⟨CFSG.LieType.Ree.ReeTag.F4.negOne, CFSG.LieType.Ree.ReeTag.negOne_smul .F4⟩
  refine ⟨subsystemGroup .F4 L {κ.i, κ.j} ⊓ (twistedEntrywise
    (canonicalRep (coxeterSystem .F4) L w₀) (σ : L →+* L)).eqLocus (MonoidHom.id _),
    fun w => ?_⟩
  rw [Subgroup.mem_inf]
  constructor
  · rintro ⟨hw, hfix⟩
    exact ⟨hw, (EvenF4QPlus.twistedEntrywise_eq_self_iff_unitary κ (σ : L →+* L) hw₀
      ⟨w, hw⟩).1 hfix⟩
  · rintro ⟨hw, hunit⟩
    exact ⟨hw, (EvenF4QPlus.twistedEntrywise_eq_self_iff_unitary κ (σ : L →+* L) hw₀
      ⟨w, hw⟩).2 hunit⟩

theorem card_f4A2UnitaryGroup
    {L : Type} [Field L] (σ : L ≃+* L) (κ : F4A2Kind) {U : Subgroup (ModGL .F4 L)}
    (hU : ∀ w, w ∈ U ↔ ∃ hw : w ∈ subsystemGroup .F4 L {κ.i, κ.j},
      ((f4A2Equiv L κ ⟨w, hw⟩ : Matrix (Fin 3) (Fin 3) L).map σ)ᵀ *
        (f4A2Equiv L κ ⟨w, hw⟩ : Matrix (Fin 3) (Fin 3) L) = 1) :
    Nat.card U = Nat.card {A : Matrix.SpecialLinearGroup (Fin 3) L //
        ((A : Matrix (Fin 3) (Fin 3) L).map σ)ᵀ * A = 1} := by
  refine Nat.card_eq_of_bijective (fun w => ⟨f4A2Equiv L κ ⟨w, ((hU w).1 w.2).1⟩,
    ((hU w).1 w.2).2⟩) ⟨fun w₁ w₂ h => ?_, fun A => ?_⟩
  · have h1 := (f4A2Equiv L κ).injective (congrArg Subtype.val h)
    have h2 := congrArg Subtype.val h1
    exact Subtype.ext h2
  · have hg' : (((f4A2Equiv L κ).symm A.1 : subsystemGroup .F4 L {κ.i, κ.j}) :
        ModGL .F4 L) ∈ U := (hU _).2 ⟨((f4A2Equiv L κ).symm A.1).2, by
      rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]
      exact A.2⟩
    refine ⟨⟨_, hg'⟩, Subtype.ext ?_⟩
    dsimp only
    rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]


theorem dvd_card_of_isComponentOf_phiSix {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) (hpd : p ∣ Nat.card K ^ 2 - Nat.card K + 1)
    {x₁ : adjointGroup .F4 K} (hx₁p : orderOf x₁ = p) {X : Subgroup (adjointGroup .F4 K)}
    (hX : IsComponentOf X (Subgroup.centralizer {x₁})) : p ∣ Nat.card X := by
  classical
  obtain ⟨f, hf, hK⟩ := exists_card_eq_two_pow K
  obtain ⟨F, hF⟩ := exists_frobenius_pow K
  set Ω := AlgebraicClosure K with hΩ
  have hεw : ((-1 : ℤ) = 1 ∧ f4PhiSix = f4Coxeter ^ 4 ∧
      p ∣ Nat.card K ^ 2 + Nat.card K + 1) ∨
      ((-1 : ℤ) = -1 ∧ f4PhiSix = f4PhiSix ∧ p ∣ Nat.card K ^ 2 - Nat.card K + 1) :=
    Or.inr ⟨rfl, rfl, hpd⟩
  obtain ⟨g, hg, hgn, x, hx, hxp, hx₁⟩ :=
    exists_lang_coordinate_three_six K Ω F hF hεw hp hp3 hx₁p
  obtain ⟨-, -, hcls⟩ := (F4_three_six_torus_data K Ω F hF hεw hp hp3).2 g hg hgn
  by_cases hne : {α | IsRoot .F4 α ∧ torusRootChar x α = 1}.Nonempty
  swap
  · exact absurd hX (not_isComponentOf_of_commutator_eq_bot
      (F4_three_six_regular_actor K Ω F hF hεw hp hp3 hg hgn hx hxp
        (Set.not_nonempty_iff_eq_empty.1 hne) hx₁).2)
  obtain ⟨u, κ, δ, hδ, hu, huw⟩ := ((hcls x hx hxp).1).resolve_left hne.ne_empty
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K₆, hK₆⟩ := EvenF4Actors.exists_intermediateField_finrank K Ω 6
  have : FiniteDimensional K K₆ := Module.finite_of_finrank_eq_succ hK₆
  have : Finite K₆ := Module.finite_of_finite K
  obtain ⟨L₂, hL₂⟩ := EvenF4Actors.exists_intermediateField_finrank K Ω 2
  obtain ⟨L₃, hL₃⟩ := EvenF4Actors.exists_intermediateField_finrank K Ω 3
  obtain ⟨e₂⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := K) (K := L₂) (L := K₆)
    (by rw [hL₂, hK₆]; norm_num)
  obtain ⟨e₃⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := K) (K := L₃) (L := K₆)
    (by rw [hL₃, hK₆]; norm_num)
  have h2 : Module.finrank K e₂.fieldRange = 2 := by
    rw [← e₂.equivFieldRange.toLinearEquiv.finrank_eq]
    exact hL₂
  have h3 : Module.finrank K e₃.fieldRange = 3 := by
    rw [← e₃.equivFieldRange.toLinearEquiv.finrank_eq]
    exact hL₃
  have : FiniteDimensional K e₂.fieldRange := Module.finite_of_finrank_eq_succ h2
  have : Finite e₂.fieldRange := Module.finite_of_finite K
  have : CharP e₂.fieldRange 2 :=
    charP_of_injective_algebraMap (algebraMap K e₂.fieldRange).injective 2
  set σ₂ : e₂.fieldRange ≃+* e₂.fieldRange :=
    CFSG.LieType.BorelTits.unitaryInvolution e₂.fieldRange 2 f with hσ₂def
  have hσ₂f : ∀ b, σ₂ b = b ^ 2 ^ f := fun b => by
    rw [hσ₂def, CFSG.LieType.BorelTits.unitaryInvolution_apply]
  have hσ₂ : ∀ b, σ₂ b = b ^ Nat.card K := fun b => by rw [hσ₂f, hK]
  obtain ⟨U, hU⟩ := exists_f4A2UnitaryGroup σ₂ κ
  obtain ⟨-, -, -, a, -, -, -, ⟨eU, -⟩, hRq, -, -, -, -, -, -, x₀, hx₀, hCx, -⟩ :=
    even_F4_cyclotomic_six_nonregular_derived_centralizer hf K hK Ω F hF hp hp3 hpd K₆ hK₆
      e₂.fieldRange e₃.fieldRange h2 h3 σ₂ hσ₂ _ g rfl hg hgn _ _ rfl rfl x hx hxp u κ δ hδ hu
      (fun z hz => by rw [huw z hz, neg_smul, one_smul]) _ _ rfl rfl _ _ _ rfl rfl rfl U hU
  have hx₀₁ : x₀ = x₁ := Subtype.ext (baseChangeGL_injective (τ := .F4)
    (algebraMap K Ω) (hx₀.trans hx₁.symm))
  subst hx₀₁
  have hι : Function.Injective ((baseChangeGL (algebraMap K Ω)).comp
      (adjointGroup .F4 K).subtype) :=
    (baseChangeGL_injective (τ := .F4) (algebraMap K Ω)).comp Subtype.val_injective
  have hcardU := card_f4A2UnitaryGroup σ₂ κ hU
  have hcardF : Nat.card e₂.fieldRange = (2 ^ f) ^ 2 := by
    rw [Module.natCard_eq_pow_finrank (K := K), h2, hK]
  rw [card_unitarySL3 hcardF σ₂ hσ₂f] at hcardU
  refine dvd_card_of_isComponentOf_of_map_eq hι (MulAut.conj _).injective hCx hRq ?_ hX
  have h1 : 1 ≤ Nat.card K := Nat.card_pos
  rw [← Nat.card_congr eU.toEquiv, hcardU, ← hK, pow_three_add_one_eq _ h1]
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right hpd _) _

end F4Nonsplit

end CFSG.StandardType
