module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcTwistRoot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcTwistTheta

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley.ToralSign
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)

private lemma ne_of_list_ne {α β : Fin Tag.E6.rank → ℤ}
    (h : List.ofFn α ≠ List.ofFn β) : α ≠ β := fun e => h (by rw [e])

private lemma wordElt_nil_smul_E6 (v : Fin Tag.E6.rank → ℤ) :
    wordElt Tag.E6 ([] : List (Fin Tag.E6.rank)) • v = v := by
  rw [ToralSign.wordElt, List.reverse_nil, CoxeterSystem.wordProd_nil, one_smul]

private lemma theta_E6_alpha (γ : Fin Tag.E6.rank → ℤ) (hγ : γ = ![-1,-1,-2,-2,-1,0]) :
    wordElt Tag.E6 ([] : List (Fin Tag.E6.rank)) • permLattice (τ := Tag.E6) TwistTag.E6.perm γ =
      ![0,-1,-1,-2,-2,-1] := by
  rw [hγ, wordElt_nil_smul_E6]
  ext i
  fin_cases i <;> decide

private lemma theta_E6_beta (γ : Fin Tag.E6.rank → ℤ) (hγ : γ = ![1,1,2,2,1,1]) :
    wordElt Tag.E6 ([] : List (Fin Tag.E6.rank)) • permLattice (τ := Tag.E6) TwistTag.E6.perm γ =
      ![1,1,1,2,2,1] := by
  rw [hγ, wordElt_nil_smul_E6]
  ext i
  fin_cases i <;> decide

private lemma theta_E6_thetaalpha (γ : Fin Tag.E6.rank → ℤ) (hγ : γ = ![0,-1,-1,-2,-2,-1]) :
    wordElt Tag.E6 ([] : List (Fin Tag.E6.rank)) • permLattice (τ := Tag.E6) TwistTag.E6.perm γ =
      ![-1,-1,-2,-2,-1,0] := by
  rw [hγ, wordElt_nil_smul_E6]
  ext i
  fin_cases i <;> decide

private lemma theta_E6_thetabeta (γ : Fin Tag.E6.rank → ℤ) (hγ : γ = ![1,1,1,2,2,1]) :
    wordElt Tag.E6 ([] : List (Fin Tag.E6.rank)) • permLattice (τ := Tag.E6) TwistTag.E6.perm γ =
      ![1,1,2,2,1,1] := by
  rw [hγ, wordElt_nil_smul_E6]
  ext i
  fin_cases i <;> decide


private lemma exists_inv_good_E6tw_twist_of_mask {K k : Type} [Field K] [Finite K] [Field k]
    [IsAlgClosed k] (ι : K →+* k) {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) [CharP K p]
    [CharP k p] (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) (m : ℕ)
    (hm : signMaskChar Tag.E6 m (Multiplicative.ofAdd (![1,1,2,2,1,1] : Fin Tag.E6.rank → ℤ)) = -1)
    (hm' : signMaskChar Tag.E6 m
      (Multiplicative.ofAdd (![1,1,1,2,2,1] : Fin Tag.E6.rank → ℤ)) = -1) :
    ∃ u : fixedPointsIn (adjointGroup Tag.E6 k)
        (frobTwistGL Tag.E6 k p e
          (wordWeylMatrix TwistTag.E6.tag k ([] : List (Fin TwistTag.E6.tag.rank)) *
            diagramMap TwistTag.E6 k)),
      orderOf u = p ∧ IsSpecialGood p u ∧
      rootDiagUnit Tag.E6 (signCharTuple (k := k) (signMaskChar Tag.E6 m)) * (u : ModGL Tag.E6 k) *
          (rootDiagUnit Tag.E6
            (signCharTuple (k := k) (signMaskChar Tag.E6 m)))⁻¹ =
        (u : ModGL Tag.E6 k)⁻¹ := by
  let α : Fin Tag.E6.rank → ℤ := ![-1,-1,-2,-2,-1,0]
  let β : Fin Tag.E6.rank → ℤ := ![1,1,2,2,1,1]
  let θα : Fin Tag.E6.rank → ℤ := ![0,-1,-1,-2,-2,-1]
  let θβ : Fin Tag.E6.rank → ℤ := ![1,1,1,2,2,1]
  have hθα : wordElt Tag.E6 ([] : List (Fin Tag.E6.rank)) •
      permLattice (τ := Tag.E6) TwistTag.E6.perm α = θα := theta_E6_alpha α rfl
  have hθβ : wordElt Tag.E6 ([] : List (Fin Tag.E6.rank)) •
      permLattice (τ := Tag.E6) TwistTag.E6.perm β = θβ := theta_E6_beta β rfl
  have hθθα : wordElt Tag.E6 ([] : List (Fin Tag.E6.rank)) •
      permLattice (τ := Tag.E6) TwistTag.E6.perm (wordElt Tag.E6 ([] : List (Fin Tag.E6.rank)) •
        permLattice (τ := Tag.E6) TwistTag.E6.perm α) = α := by
    rw [hθα]
    exact (theta_E6_thetaalpha θα rfl).trans (by rw [show α = ![-1,-1,-2,-2,-1,0] from rfl])
  have hθθβ : wordElt Tag.E6 ([] : List (Fin Tag.E6.rank)) •
      permLattice (τ := Tag.E6) TwistTag.E6.perm (wordElt Tag.E6 ([] : List (Fin Tag.E6.rank)) •
        permLattice (τ := Tag.E6) TwistTag.E6.perm β) = β := by
    rw [hθβ]
    exact (theta_E6_thetabeta θβ rfl).trans (by rw [show β = ![1,1,2,2,1,1] from rfl])
  refine exists_twist_pair_inv_good (τ := .E6) (hτ := Or.inr (Or.inl rfl))
    (K := K) (k := k) (ι := ι) (p := p) (e := e) (hp2 := hp2) (hK := hK) (h3 := h3)
    (Q := wordWeylMatrix TwistTag.E6.tag k ([] : List (Fin TwistTag.E6.tag.rank)) *
      diagramMap TwistTag.E6 k)
    (θ := fun γ => wordElt Tag.E6 ([] : List (Fin Tag.E6.rank)) •
      permLattice (τ := Tag.E6) TwistTag.E6.perm γ)
    (a := signCharTuple (k := k) (signMaskChar Tag.E6 m)) (α := α) (β := β)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun γ hγ => twistMatrix_conj_pinnedX TwistTag.E6 [] hγ
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
  · rw [hθα, hθβ]
    refine ⟨ne_of_list_ne (by decide), ne_of_list_ne (by decide), ?_⟩
    exact isRoot_iff_mem_artifactRoots.2 (by decide)
  · intro γ hγ
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hγ
    rcases hγ with rfl | rfl | rfl | rfl
    · exact ⟨rootsCommute_of_list (by decide) (by decide) (by decide),
        rootsCommute_of_list (by decide) (by decide) (by decide)⟩
    · rw [hθα]
      exact ⟨rootsCommute_of_list (by decide) (by decide) (by decide),
        rootsCommute_of_list (by decide) (by decide) (by decide)⟩
    · exact ⟨rootsCommute_of_list (by decide) (by decide) (by decide),
        rootsCommute_of_list (by decide) (by decide) (by decide)⟩
    · rw [hθβ]
      exact ⟨rootsCommute_of_list (by decide) (by decide) (by decide),
        rootsCommute_of_list (by decide) (by decide) (by decide)⟩
  · exact rootsCommute_of_list (by decide) (by decide) (by decide)
  · exact ⟨by decide, by decide⟩
  · rw [rootChar_signCharTuple]
    have h : signMaskChar Tag.E6 m (Multiplicative.ofAdd β) = -1 := hm
    rw [h]
    simp [intUnitsMap]
  · rw [hθβ, rootChar_signCharTuple]
    have h : signMaskChar Tag.E6 m (Multiplicative.ofAdd θβ) = -1 := hm'
    rw [h]
    simp [intUnitsMap]

theorem exists_inv_good_E6tw_twist {K k : Type} [Field K] [Finite K] [Field k] [IsAlgClosed k]
    (ι : K →+* k) {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) [CharP K p] [CharP k p]
    (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) {r : SignRep .E6} (hr : r ∈ e6SignDiagramReps)
    (hr0 : r.mask ≠ 0) {l : List (Fin Tag.E6.rank)} (hl : l ∈ r.omegaWords) :
    ∃ u : fixedPointsIn (adjointGroup TwistTag.E6.tag k) (frobTwistGL TwistTag.E6.tag k p e
        (wordWeylMatrix TwistTag.E6.tag k l * diagramMap TwistTag.E6 k)),
      orderOf u = p ∧ IsSpecialGood p u ∧
      rootDiagUnit TwistTag.E6.tag (signCharTuple (k := k) (signMaskChar TwistTag.E6.tag r.mask)) *
          (u : ModGL TwistTag.E6.tag k) *
          (rootDiagUnit TwistTag.E6.tag
            (signCharTuple (k := k) (signMaskChar TwistTag.E6.tag r.mask)))⁻¹ =
        (u : ModGL TwistTag.E6.tag k)⁻¹ := by
  simp only [e6SignDiagramReps, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact absurd rfl hr0
  · simp only [e6OmegaWords20, List.mem_cons, List.mem_nil_iff, or_false] at hl
    subst hl
    exact exists_inv_good_E6tw_twist_of_mask ι hp2 hK h3 20 (by decide) (by decide)
  · simp only [e6OmegaWords2, List.mem_cons, List.mem_nil_iff, or_false] at hl
    subst hl
    exact exists_inv_good_E6tw_twist_of_mask ι hp2 hK h3 2 (by decide) (by decide)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
