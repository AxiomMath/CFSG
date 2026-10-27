module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.ExcTwistBF
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningSemilinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley.ToralSign
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootChar rootDiagUnit)

private lemma ne_of_list_ne {α β : Fin Tag.E7.rank → ℤ}
    (h : List.ofFn α ≠ List.ofFn β) : α ≠ β := fun e => h (by rw [e])


private lemma theta_E7_delta (γ : Fin Tag.E7.rank → ℤ) (hγ : γ = ![0,-1,-1,-1,0,0,0]) :
    wordElt .E7 e7Word2_1 • γ = ![0,1,1,2,2,1,0] := by
  rw [ToralSign.wordElt]
  simp only [CFSG.LieType.Ree.wordProd_smul]
  rw [hγ]
  ext i
  fin_cases i <;> decide

private lemma theta_E7_thetadelta (γ : Fin Tag.E7.rank → ℤ)
    (hγ : γ = ![0,1,1,2,2,1,0]) :
    wordElt .E7 e7Word2_1 • γ = ![0,-1,-1,-1,0,0,0] := by
  rw [ToralSign.wordElt]
  simp only [CFSG.LieType.Ree.wordProd_smul]
  rw [hγ]
  ext i
  fin_cases i <;> decide

private lemma theta_E7_eps (γ : Fin Tag.E7.rank → ℤ) (hγ : γ = ![1,0,0,0,0,0,0]) :
    wordElt .E7 e7Word2_1 • γ = ![1,2,2,3,2,1,0] := by
  rw [ToralSign.wordElt]
  simp only [CFSG.LieType.Ree.wordProd_smul]
  rw [hγ]
  ext i
  fin_cases i <;> decide

private lemma theta_E7_thetaeps (γ : Fin Tag.E7.rank → ℤ)
    (hγ : γ = ![1,2,2,3,2,1,0]) :
    wordElt .E7 e7Word2_1 • γ = ![1,0,0,0,0,0,0] := by
  rw [ToralSign.wordElt]
  simp only [CFSG.LieType.Ree.wordProd_smul]
  rw [hγ]
  ext i
  fin_cases i <;> decide

private lemma theta_E7_gamma1 (γ : Fin Tag.E7.rank → ℤ) (hγ : γ = ![0,0,0,1,1,1,0]) :
    wordElt .E7 e7Word2_1 • γ = ![0,0,0,1,1,1,0] := by
  rw [ToralSign.wordElt]
  simp only [CFSG.LieType.Ree.wordProd_smul]
  rw [hγ]
  ext i
  fin_cases i <;> decide

private lemma theta_E7_gamma2 (γ : Fin Tag.E7.rank → ℤ) (hγ : γ = ![1,1,1,1,1,0,0]) :
    wordElt .E7 e7Word2_1 • γ = ![1,1,1,1,1,0,0] := by
  rw [ToralSign.wordElt]
  simp only [CFSG.LieType.Ree.wordProd_smul]
  rw [hγ]
  ext i
  fin_cases i <;> decide

private lemma theta_E7_alpha (γ : Fin Tag.E7.rank → ℤ) (hγ : γ = ![1,1,1,2,2,1,0]) :
    wordElt .E7 e7Word2_1 • γ = ![1,1,1,2,2,1,0] := by
  rw [ToralSign.wordElt]
  simp only [CFSG.LieType.Ree.wordProd_smul]
  rw [hγ]
  ext i
  fin_cases i <;> decide


private lemma exists_inv_extraGood_E7_twist_mask {k : Type} [Field k] [IsAlgClosed k]
    [CharP k 3] (m : ℕ)
    (hχ : rootChar (signCharTuple (k := k) (signMaskChar .E7 m)) ![0,-1,-1,-1,0,0,0] = -1)
    (hχ' : rootChar (signCharTuple (k := k) (signMaskChar .E7 m)) ![0,1,1,2,2,1,0] = -1) :
    ∃ u : fixedPointsIn (adjointGroup .E7 k)
        (frobTwistGL .E7 k 3 1 (wordWeylMatrix .E7 k e7Word2_1)),
      orderOf u = 3 ∧ IsExtraGood u ∧
      rootDiagUnit .E7 (signCharTuple (k := k) (signMaskChar .E7 m)) * (u : ModGL .E7 k) *
          (rootDiagUnit .E7 (signCharTuple (k := k) (signMaskChar .E7 m)))⁻¹ =
        (u : ModGL .E7 k)⁻¹ := by
  let δ : Fin Tag.E7.rank → ℤ := ![0,-1,-1,-1,0,0,0]
  let ε : Fin Tag.E7.rank → ℤ := ![1,0,0,0,0,0,0]
  let θδ : Fin Tag.E7.rank → ℤ := ![0,1,1,2,2,1,0]
  let θε : Fin Tag.E7.rank → ℤ := ![1,2,2,3,2,1,0]
  let γ₁ : Fin Tag.E7.rank → ℤ := ![0,0,0,1,1,1,0]
  let γ₂ : Fin Tag.E7.rank → ℤ := ![1,1,1,1,1,0,0]
  let α : Fin Tag.E7.rank → ℤ := ![1,1,1,2,2,1,0]
  have hθδ : wordElt .E7 e7Word2_1 • δ = θδ := theta_E7_delta δ rfl
  have hθε : wordElt .E7 e7Word2_1 • ε = θε := theta_E7_eps ε rfl
  have hθγ₁ : wordElt .E7 e7Word2_1 • γ₁ = γ₁ := theta_E7_gamma1 γ₁ rfl
  have hθγ₂ : wordElt .E7 e7Word2_1 • γ₂ = γ₂ := theta_E7_gamma2 γ₂ rfl
  have hθθδ : wordElt .E7 e7Word2_1 • (wordElt .E7 e7Word2_1 • δ) = δ := by
    rw [hθδ]
    exact (theta_E7_thetadelta θδ rfl).trans
      (by rw [show δ = ![0,-1,-1,-1,0,0,0] from rfl])
  have hθθε : wordElt .E7 e7Word2_1 • (wordElt .E7 e7Word2_1 • ε) = ε := by
    rw [hθε]
    exact (theta_E7_thetaeps θε rfl).trans
      (by rw [show ε = ![1,0,0,0,0,0,0] from rfl])
  have hα : δ + θε = α := by ext i; fin_cases i <;> decide
  have hθα : wordElt .E7 e7Word2_1 • (δ + wordElt .E7 e7Word2_1 • ε) =
      δ + wordElt .E7 e7Word2_1 • ε := by
    rw [hθε, hα]
    exact (theta_E7_alpha α rfl).trans
      (by rw [show α = ![1,1,1,2,2,1,0] from rfl])
  refine exists_twist_inv_extraGood (τ := .E7) (hτ := Or.inr (Or.inr (Or.inl rfl)))
    (Q := wordWeylMatrix .E7 k e7Word2_1)
    (θ := fun γ => wordElt .E7 e7Word2_1 • γ)
    (a := signCharTuple (k := k) (signMaskChar .E7 m)) (δ := δ) (ε := ε)
    (γ₁ := γ₁) (γ₂ := γ₂)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun γ hγ => wordWeylMatrix_conj_pinnedX e7Word2_1 hγ
  · exact isRoot_iff_mem_artifactRoots.2 (by decide)
  · rw [hθδ]
    exact isRoot_iff_mem_artifactRoots.2 (by decide)
  · exact isRoot_iff_mem_artifactRoots.2 (by decide)
  · rw [hθε]
    exact isRoot_iff_mem_artifactRoots.2 (by decide)
  · exact isRoot_iff_mem_artifactRoots.2 (by decide)
  · exact isRoot_iff_mem_artifactRoots.2 (by decide)
  · exact hθθδ
  · exact hθθε
  · exact hθγ₁
  · exact hθγ₂
  · exact hθα
  · rw [hθδ, hθε, hα]
    ext i
    fin_cases i <;> decide
  · rw [hθε, hα]
    ext i
    fin_cases i <;> decide
  · rw [hθε]
    refine ⟨ne_of_list_ne (by decide), ne_of_list_ne (by decide), ?_⟩
    rw [hα]
    exact isRoot_iff_mem_artifactRoots.2 (by decide)
  · rw [hθδ]
    exact ⟨ne_of_list_ne (by decide), ne_of_list_ne (by decide)⟩
  · exact ⟨ne_of_list_ne (by decide), ne_of_list_ne (by decide)⟩
  · rw [hθδ]
    exact rootsCommute_of_list (by decide) (by decide) (by decide)
  · rw [hθε]
    exact rootsCommute_of_list (by decide) (by decide) (by decide)
  · exact rootsCommute_of_list (by decide) (by decide) (by decide)
  · rw [hθδ, hθε]
    exact rootsCommute_of_list (by decide) (by decide) (by decide)
  · rw [hθδ, hθε, hα]
    intro γ hγ
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hγ
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact rootsCommute_of_list (by decide) (by decide) (by decide)
  · rw [hθδ, hθε]
    intro γ hγ η hη
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hγ hη
    rcases hγ with rfl | rfl <;> rcases hη with rfl | rfl | rfl | rfl
    all_goals exact rootsCommute_of_list (by decide) (by decide) (by decide)
  · show rootChar (signCharTuple (k := k) (signMaskChar .E7 m))
      ![0,-1,-1,-1,0,0,0] = -1
    exact hχ
  · rw [hθδ]
    exact hχ'

theorem exists_inv_extraGood_E7_twist_three {k : Type} [Field k] [IsAlgClosed k] [CharP k 3]
    {r : SignRep .E7} (hr : r ∈ e7SignDiagramReps) {l : List (Fin Tag.E7.rank)}
    (hl : l ∈ r.omegaWords) (hl0 : l ≠ []) :
    ∃ u : fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k 3 1 (wordWeylMatrix .E7 k l)),
      orderOf u = 3 ∧ IsExtraGood u ∧
      rootDiagUnit .E7 (signCharTuple (k := k) (signMaskChar .E7 r.mask)) * (u : ModGL .E7 k) *
          (rootDiagUnit .E7 (signCharTuple (k := k) (signMaskChar .E7 r.mask)))⁻¹ =
        (u : ModGL .E7 k)⁻¹ := by
  simp only [e7SignDiagramReps, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simp [e7OmegaWords0] at hl
    exact absurd hl hl0
  · simp [e7OmegaWords1] at hl
    exact absurd hl hl0
  · simp only [e7OmegaWords2, List.mem_cons, List.mem_nil_iff, or_false] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hl0
    · let d : Fin Tag.E7.rank → ℤ := ![0,-1,-1,-1,0,0,0]
      let td : Fin Tag.E7.rank → ℤ := ![0,1,1,2,2,1,0]
      have hχ : rootChar (signCharTuple (k := k) (signMaskChar .E7 2)) d = -1 := by
        rw [rootChar_signCharTuple]
        have h : signMaskChar .E7 2 (Multiplicative.ofAdd d) = -1 := by decide
        rw [h]
        simp [intUnitsMap]
      have hχ' : rootChar (signCharTuple (k := k) (signMaskChar .E7 2)) td = -1 := by
        rw [rootChar_signCharTuple]
        have h : signMaskChar .E7 2 (Multiplicative.ofAdd td) = -1 := by decide
        rw [h]
        simp [intUnitsMap]
      exact exists_inv_extraGood_E7_twist_mask 2 hχ hχ'
  · simp only [e7OmegaWords3, List.mem_cons, List.mem_nil_iff, or_false] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hl0
    · rw [show e7Word3_1 = e7Word2_1 from rfl]
      let d : Fin Tag.E7.rank → ℤ := ![0,-1,-1,-1,0,0,0]
      let td : Fin Tag.E7.rank → ℤ := ![0,1,1,2,2,1,0]
      have hχ : rootChar (signCharTuple (k := k) (signMaskChar .E7 3)) d = -1 := by
        rw [rootChar_signCharTuple]
        have h : signMaskChar .E7 3 (Multiplicative.ofAdd d) = -1 := by decide
        rw [h]
        simp [intUnitsMap]
      have hχ' : rootChar (signCharTuple (k := k) (signMaskChar .E7 3)) td = -1 := by
        rw [rootChar_signCharTuple]
        have h : signMaskChar .E7 3 (Multiplicative.ofAdd td) = -1 := by decide
        rw [h]
        simp [intUnitsMap]
      exact exists_inv_extraGood_E7_twist_mask 3 hχ hχ'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
