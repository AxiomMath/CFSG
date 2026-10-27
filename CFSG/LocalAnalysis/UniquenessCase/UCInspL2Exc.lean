module

public import CFSG.LocalAnalysis.UniquenessCase.UCK461
public import CFSG.LocalAnalysis.UniquenessCase.UCInspBasic
public import CFSG.Adapters.Certificate43Check

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Insp

open CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.Assembly.LowTwoRank

section Alt6

theorem perm_six_pow_nine : ∀ σ : Equiv.Perm (Fin 6), σ ^ 9 = 1 → σ ^ 3 = 1 := by
  decide +kernel

theorem pRank_three_alternating_six :
    CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin 6))) = 2 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  obtain ⟨E, hE⟩ := Sylow.exists_subgroup_card_pow_prime (G := alternatingGroup (Fin 6)) 3
    (n := 2) (by rw [hcard]; norm_num)
  have hcomm : ∀ a b : E, a * b = b * a := IsPGroup.commutative_of_card_eq_prime_sq hE
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    have h9 : (⟨x, hx⟩ : E) ^ 9 = 1 := by
      have := pow_card_eq_one' (G := E) (x := ⟨x, hx⟩)
      rwa [hE] at this
    have h9' : x ^ 9 = 1 := by
      have := congrArg (fun y : E => (y : alternatingGroup (Fin 6))) h9
      simpa using this
    have h9'' : ((x : Equiv.Perm (Fin 6))) ^ 9 = 1 := by
      have := congrArg (fun y : alternatingGroup (Fin 6) => (y : Equiv.Perm (Fin 6))) h9'
      simpa using this
    have := perm_six_pow_nine _ h9''
    apply Subtype.ext
    simpa using this
  have hEa : IsElemAbelian 3 E := ⟨⟨⟨hcomm⟩⟩, hE3⟩
  refine pRank_eq (by norm_num) E le_top hEa hE fun E' _ _ j hj => ?_
  by_contra hj3
  push Not at hj3
  have hdvd : 3 ^ j ∣ 360 := by
    rw [← hcard, ← hj]
    exact Subgroup.card_subgroup_dvd_card E'
  have h27 : 3 ^ 3 ∣ 360 := (Nat.pow_dvd_pow 3 hj3).trans hdvd
  norm_num at h27

end Alt6

theorem lieModel_psl_two_five_two_two {G : Type} [Group G] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 5) (e : G ≃* StatedProj (StatedSL 2 K)) : LieModel G .PSL 2 2 2 := by
  haveI := CFSG.Adapters.certificate43_holds
  obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five K
    (Or.inr hK)
  have hK4 : Nat.card (GaloisField 2 2) = 2 ^ 2 := GaloisField.card 2 2 (by norm_num)
  obtain ⟨e5'⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
    (GaloisField 2 2) (Or.inl (by rw [hK4]; norm_num))
  exact Or.inl ⟨by decide, ⟨Nat.prime_two, by norm_num, le_rfl, by decide, by decide⟩,
    GaloisField 2 2, inferInstance, inferInstance, hK4, ⟨e.trans (e5.trans e5'.symm)⟩⟩

open CFSG.LocalAnalysis.ComponentInitial in
theorem lieModel_psl_two_seven_three_two {G : Type} [Group G] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 7) (e : G ≃* StatedProj (StatedSL 2 K)) : LieModel G .PSL 3 2 1 := by
  have h7 : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = Fintype.card (ZMod 7) := by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK]
  let φ : K ≃+* ZMod 7 := FiniteField.ringEquivOfCardEq hcard
  let e₁ : StatedProj (StatedSL 2 K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7) :=
    (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
      (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 2))
  let e₂ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    (QuotientGroup.quotientMulEquivOfEq center_SL_three_zmod_two_eq_bot).trans
      QuotientGroup.quotientBot
  let e₃ : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2) :=
    MulEquiv.ofBijective _ bijective_toGL_three_zmod_two
  obtain ⟨e₄⟩ := nonempty_GL_three_two_equiv_PSL_two_seven
  have e₅ : Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2) ≃*
      StatedProj (StatedSL 3 (ZMod 2)) :=
    projectiveSpecialLinearGroupEquivStatedProj 3 (ZMod 2)
  exact Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩, ZMod 2,
    inferInstance, inferInstance, by rw [Nat.card_zmod, pow_one],
    ⟨(((((e.trans e₁).trans e₄.symm).trans e₃.symm).trans e₂.symm).trans e₅)⟩⟩

open CFSG.LocalAnalysis.ComponentInitial in
theorem pRank_three_of_psl_two_nine {G : Type} [Group G] [Finite G] {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 9) (e : G ≃* StatedProj (StatedSL 2 K)) :
    CFSG.Open.pRank 3 (⊤ : Subgroup G) = 2 := by
  have : Fintype K := Fintype.ofFinite K
  have hK9 : Fintype.card K = 9 := by rw [← Nat.card_eq_fintype_card, hK]
  obtain ⟨e6⟩ := unique_field_nine_projective_linear_alternating_six_isomorphism K hK9
  have e' : G ≃* alternatingGroup (Fin 6) :=
    e.trans ((projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans e6)
  rw [pRank_congr (by norm_num) e', pRank_three_alternating_six]

end CFSG.LocalAnalysis.UniquenessCase.UCK.Insp

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UCK.Insp

theorem l2Exceptional_holds : L2Exceptional := by
  intro G _ _ p f _ hL
  rcases hL with ⟨-, ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
  · refine ⟨fun h5 => ?_, fun h7 => ?_, fun h9 => ?_⟩
    · exact lieModel_psl_two_five_two_two (hK.trans h5) e
    · exact lieModel_psl_two_seven_three_two (hK.trans h7) e
    · exact pRank_three_of_psl_two_nine (hK.trans h9) e
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

end CFSG.LocalAnalysis.UniquenessCase.UCK
