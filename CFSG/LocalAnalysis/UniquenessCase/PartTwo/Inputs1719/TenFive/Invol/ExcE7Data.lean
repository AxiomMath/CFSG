module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcTwistRoot
public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningSemilinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley.ToralSign
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

private lemma ne_of_list_ne {α β : Fin Tag.E7.rank → ℤ}
    (h : List.ofFn α ≠ List.ofFn β) : α ≠ β := fun e => h (by rw [e])


private lemma theta_mask2_alpha (α : Fin Tag.E7.rank → ℤ)
    (hα : α = ![0,0,0,0,0,0,1]) :
    wordElt .E7 e7Word2_1 • α = ![0,0,1,0,0,0,0] := by
  rw [ToralSign.wordElt]
  simp only [CFSG.LieType.Ree.wordProd_smul]
  rw [hα]
  ext i
  fin_cases i <;> decide

private lemma theta_mask2_beta (β : Fin Tag.E7.rank → ℤ)
    (hβ : β = ![1,1,1,1,1,1,0]) :
    wordElt .E7 e7Word2_1 • β = ![1,1,1,2,1,0,0] := by
  rw [ToralSign.wordElt]
  simp only [CFSG.LieType.Ree.wordProd_smul]
  rw [hβ]
  ext i
  fin_cases i <;> decide

private lemma theta_mask2_thetaalpha (γ : Fin Tag.E7.rank → ℤ)
    (hγ : γ = ![0,0,1,0,0,0,0]) :
    wordElt .E7 e7Word2_1 • γ = ![0,0,0,0,0,0,1] := by
  rw [ToralSign.wordElt]
  simp only [CFSG.LieType.Ree.wordProd_smul]
  rw [hγ]
  ext i
  fin_cases i <;> decide

private lemma theta_mask2_thetabeta (γ : Fin Tag.E7.rank → ℤ)
    (hγ : γ = ![1,1,1,2,1,0,0]) :
    wordElt .E7 e7Word2_1 • γ = ![1,1,1,1,1,1,0] := by
  rw [ToralSign.wordElt]
  simp only [CFSG.LieType.Ree.wordProd_smul]
  rw [hγ]
  ext i
  fin_cases i <;> decide

private lemma theta_mask3_alpha (α : Fin Tag.E7.rank → ℤ)
    (hα : α = ![0,0,0,0,0,0,1]) :
    wordElt .E7 e7Word3_1 • α = ![0,0,1,0,0,0,0] := by
  rw [ToralSign.wordElt]
  simp only [CFSG.LieType.Ree.wordProd_smul]
  rw [hα]
  ext i
  fin_cases i <;> decide

private lemma theta_mask3_beta (β : Fin Tag.E7.rank → ℤ)
    (hβ : β = ![1,2,2,3,2,1,0]) :
    wordElt .E7 e7Word3_1 • β = ![1,0,0,0,0,0,0] := by
  rw [ToralSign.wordElt]
  simp only [CFSG.LieType.Ree.wordProd_smul]
  rw [hβ]
  ext i
  fin_cases i <;> decide

private lemma theta_mask3_thetaalpha (γ : Fin Tag.E7.rank → ℤ)
    (hγ : γ = ![0,0,1,0,0,0,0]) :
    wordElt .E7 e7Word3_1 • γ = ![0,0,0,0,0,0,1] := by
  rw [ToralSign.wordElt]
  simp only [CFSG.LieType.Ree.wordProd_smul]
  rw [hγ]
  ext i
  fin_cases i <;> decide

private lemma theta_mask3_thetabeta (γ : Fin Tag.E7.rank → ℤ)
    (hγ : γ = ![1,0,0,0,0,0,0]) :
    wordElt .E7 e7Word3_1 • γ = ![1,2,2,3,2,1,0] := by
  rw [ToralSign.wordElt]
  simp only [CFSG.LieType.Ree.wordProd_smul]
  rw [hγ]
  ext i
  fin_cases i <;> decide


private lemma exists_inv_good_E7_twist_mask2 {K k : Type} [Field K] [Finite K]
    [Field k] [IsAlgClosed k] (ι : K →+* k) {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    [CharP K p] [CharP k p] (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) :
    ∃ u : fixedPointsIn (adjointGroup .E7 k)
        (frobTwistGL .E7 k p e (wordWeylMatrix .E7 k e7Word2_1)),
      orderOf u = p ∧ IsSpecialGood p u ∧
      rootDiagUnit .E7 (signCharTuple (k := k) (signMaskChar .E7 2)) * (u : ModGL .E7 k) *
          (rootDiagUnit .E7 (signCharTuple (k := k) (signMaskChar .E7 2)))⁻¹ =
        (u : ModGL .E7 k)⁻¹ := by
  let α : Fin Tag.E7.rank → ℤ := ![0,0,0,0,0,0,1]
  let β : Fin Tag.E7.rank → ℤ := ![1,1,1,1,1,1,0]
  let θα : Fin Tag.E7.rank → ℤ := ![0,0,1,0,0,0,0]
  let θβ : Fin Tag.E7.rank → ℤ := ![1,1,1,2,1,0,0]
  have hθα : wordElt .E7 e7Word2_1 • α = θα := theta_mask2_alpha α rfl
  have hθβ : wordElt .E7 e7Word2_1 • β = θβ := theta_mask2_beta β rfl
  have hθθα : wordElt .E7 e7Word2_1 • (wordElt .E7 e7Word2_1 • α) = α := by
    rw [hθα]
    exact (theta_mask2_thetaalpha θα rfl).trans
      (by rw [show α = ![0,0,0,0,0,0,1] from rfl])
  have hθθβ : wordElt .E7 e7Word2_1 • (wordElt .E7 e7Word2_1 • β) = β := by
    rw [hθβ]
    exact (theta_mask2_thetabeta θβ rfl).trans
      (by rw [show β = ![1,1,1,1,1,1,0] from rfl])
  refine exists_twist_pair_inv_good (τ := .E7) (hτ := Or.inr (Or.inr (Or.inl rfl)))
    (K := K) (k := k) (ι := ι) (p := p) (e := e) (hp2 := hp2) (hK := hK) (h3 := h3)
    (Q := wordWeylMatrix .E7 k e7Word2_1)
    (θ := fun γ => wordElt .E7 e7Word2_1 • γ)
    (a := signCharTuple (k := k) (signMaskChar .E7 2)) (α := α) (β := β)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun γ hγ => wordWeylMatrix_conj_pinnedX e7Word2_1 hγ
  · exact isRoot_iff_mem_artifactRoots.2 (by decide)
  · exact isRoot_iff_mem_artifactRoots.2 (by decide)
  · rw [hθα]
    exact isRoot_iff_mem_artifactRoots.2 (by decide)
  · rw [hθβ]
    exact isRoot_iff_mem_artifactRoots.2 (by decide)
  · exact hθθα
  · exact hθθβ
  · rw [hθα]
    exact rootsCommute_of_list (by decide) (by decide) (by decide)
  · rw [hθβ]
    exact rootsCommute_of_list (by decide) (by decide) (by decide)
  · rw [hθβ]
    exact rootsCommute_of_list (by decide) (by decide) (by decide)
  · rw [hθα]
    exact rootsCommute_of_list (by decide) (by decide) (by decide)
  · refine ⟨ne_of_list_ne (by decide), ne_of_list_ne (by decide), ?_⟩
    exact isRoot_iff_mem_artifactRoots.2 (by decide)
  · refine ⟨ne_of_list_ne (by decide), ne_of_list_ne (by decide), ?_⟩
    exact isRoot_iff_mem_artifactRoots.2 (by decide)
  · intro γ hγ
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hγ
    rcases hγ with rfl | rfl | rfl | rfl
    · exact ⟨rootsCommute_of_list (by decide) (by decide) (by decide),
        rootsCommute_of_list (by decide) (by decide) (by decide)⟩
    · exact ⟨rootsCommute_of_list (by decide) (by decide) (by decide),
        rootsCommute_of_list (by decide) (by decide) (by decide)⟩
    · exact ⟨rootsCommute_of_list (by decide) (by decide) (by decide),
        rootsCommute_of_list (by decide) (by decide) (by decide)⟩
    · exact ⟨rootsCommute_of_list (by decide) (by decide) (by decide),
        rootsCommute_of_list (by decide) (by decide) (by decide)⟩
  · exact rootsCommute_of_list (by decide) (by decide) (by decide)
  · exact ⟨by decide, by decide⟩
  · rw [rootChar_signCharTuple]
    have h : signMaskChar .E7 2 (Multiplicative.ofAdd β) = -1 := by decide
    rw [h]
    simp [intUnitsMap]
  · rw [hθβ, rootChar_signCharTuple]
    have h : signMaskChar .E7 2 (Multiplicative.ofAdd θβ) = -1 := by decide
    rw [h]
    simp [intUnitsMap]

private lemma exists_inv_good_E7_twist_mask3 {K k : Type} [Field K] [Finite K]
    [Field k] [IsAlgClosed k] (ι : K →+* k) {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    [CharP K p] [CharP k p] (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) :
    ∃ u : fixedPointsIn (adjointGroup .E7 k)
        (frobTwistGL .E7 k p e (wordWeylMatrix .E7 k e7Word3_1)),
      orderOf u = p ∧ IsSpecialGood p u ∧
      rootDiagUnit .E7 (signCharTuple (k := k) (signMaskChar .E7 3)) * (u : ModGL .E7 k) *
          (rootDiagUnit .E7 (signCharTuple (k := k) (signMaskChar .E7 3)))⁻¹ =
        (u : ModGL .E7 k)⁻¹ := by
  let α : Fin Tag.E7.rank → ℤ := ![0,0,0,0,0,0,1]
  let β : Fin Tag.E7.rank → ℤ := ![1,2,2,3,2,1,0]
  let θα : Fin Tag.E7.rank → ℤ := ![0,0,1,0,0,0,0]
  let θβ : Fin Tag.E7.rank → ℤ := ![1,0,0,0,0,0,0]
  have hθα : wordElt .E7 e7Word3_1 • α = θα := theta_mask3_alpha α rfl
  have hθβ : wordElt .E7 e7Word3_1 • β = θβ := theta_mask3_beta β rfl
  have hθθα : wordElt .E7 e7Word3_1 • (wordElt .E7 e7Word3_1 • α) = α := by
    rw [hθα]
    exact (theta_mask3_thetaalpha θα rfl).trans
      (by rw [show α = ![0,0,0,0,0,0,1] from rfl])
  have hθθβ : wordElt .E7 e7Word3_1 • (wordElt .E7 e7Word3_1 • β) = β := by
    rw [hθβ]
    exact (theta_mask3_thetabeta θβ rfl).trans
      (by rw [show β = ![1,2,2,3,2,1,0] from rfl])
  refine exists_twist_pair_inv_good (τ := .E7) (hτ := Or.inr (Or.inr (Or.inl rfl)))
    (K := K) (k := k) (ι := ι) (p := p) (e := e) (hp2 := hp2) (hK := hK) (h3 := h3)
    (Q := wordWeylMatrix .E7 k e7Word3_1)
    (θ := fun γ => wordElt .E7 e7Word3_1 • γ)
    (a := signCharTuple (k := k) (signMaskChar .E7 3)) (α := α) (β := β)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun γ hγ => wordWeylMatrix_conj_pinnedX e7Word3_1 hγ
  · exact isRoot_iff_mem_artifactRoots.2 (by decide)
  · exact isRoot_iff_mem_artifactRoots.2 (by decide)
  · rw [hθα]
    exact isRoot_iff_mem_artifactRoots.2 (by decide)
  · rw [hθβ]
    exact isRoot_iff_mem_artifactRoots.2 (by decide)
  · exact hθθα
  · exact hθθβ
  · rw [hθα]
    exact rootsCommute_of_list (by decide) (by decide) (by decide)
  · rw [hθβ]
    exact rootsCommute_of_list (by decide) (by decide) (by decide)
  · rw [hθβ]
    exact rootsCommute_of_list (by decide) (by decide) (by decide)
  · rw [hθα]
    exact rootsCommute_of_list (by decide) (by decide) (by decide)
  · refine ⟨ne_of_list_ne (by decide), ne_of_list_ne (by decide), ?_⟩
    exact isRoot_iff_mem_artifactRoots.2 (by decide)
  · refine ⟨ne_of_list_ne (by decide), ne_of_list_ne (by decide), ?_⟩
    exact isRoot_iff_mem_artifactRoots.2 (by decide)
  · intro γ hγ
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hγ
    rcases hγ with rfl | rfl | rfl | rfl
    · exact ⟨rootsCommute_of_list (by decide) (by decide) (by decide),
        rootsCommute_of_list (by decide) (by decide) (by decide)⟩
    · exact ⟨rootsCommute_of_list (by decide) (by decide) (by decide),
        rootsCommute_of_list (by decide) (by decide) (by decide)⟩
    · exact ⟨rootsCommute_of_list (by decide) (by decide) (by decide),
        rootsCommute_of_list (by decide) (by decide) (by decide)⟩
    · exact ⟨rootsCommute_of_list (by decide) (by decide) (by decide),
        rootsCommute_of_list (by decide) (by decide) (by decide)⟩
  · exact rootsCommute_of_list (by decide) (by decide) (by decide)
  · exact ⟨by decide, by decide⟩
  · rw [rootChar_signCharTuple]
    have h : signMaskChar .E7 3 (Multiplicative.ofAdd β) = -1 := by decide
    rw [h]
    simp [intUnitsMap]
  · rw [hθβ, rootChar_signCharTuple]
    have h : signMaskChar .E7 3 (Multiplicative.ofAdd θβ) = -1 := by decide
    rw [h]
    simp [intUnitsMap]

theorem exists_inv_good_E7_twist {K k : Type} [Field K] [Finite K] [Field k] [IsAlgClosed k]
    (ι : K →+* k) {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) [CharP K p] [CharP k p]
    (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) {r : SignRep .E7} (hr : r ∈ e7SignDiagramReps)
    {l : List (Fin Tag.E7.rank)} (hl : l ∈ r.omegaWords) (hl0 : l ≠ []) :
    ∃ u : fixedPointsIn (adjointGroup .E7 k) (frobTwistGL .E7 k p e (wordWeylMatrix .E7 k l)),
      orderOf u = p ∧ IsSpecialGood p u ∧
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
    · exact exists_inv_good_E7_twist_mask2 ι hp2 hK h3
  · simp only [e7OmegaWords3, List.mem_cons, List.mem_nil_iff, or_false] at hl
    rcases hl with rfl | rfl
    · exact absurd rfl hl0
    · exact exists_inv_good_E7_twist_mask3 ι hp2 hK h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
