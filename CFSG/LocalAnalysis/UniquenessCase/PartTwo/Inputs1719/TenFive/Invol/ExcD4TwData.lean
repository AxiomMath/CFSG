module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcTwistRoot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcTwistTheta

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley.ToralSign
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootChar rootDiagUnit)


private lemma theta_D4_nil_alpha :
    wordElt .D4 [] • permLattice (τ := .D4) TwistTag.D4.perm
      (![0, 0, 1, 0] : Fin Tag.D4.rank → ℤ) = ![0, 0, 1, 0] := by
  rw [ToralSign.wordElt]
  simp only [CFSG.LieType.Chevalley.wordProd_smul]
  ext i
  fin_cases i <;> decide

private lemma theta_D4_nil_beta :
    wordElt .D4 [] • permLattice (τ := .D4) TwistTag.D4.perm
      (![1, 1, 1, 1] : Fin Tag.D4.rank → ℤ) = ![1, 1, 1, 1] := by
  rw [ToralSign.wordElt]
  simp only [CFSG.LieType.Chevalley.wordProd_smul]
  ext i
  fin_cases i <;> decide

private lemma theta_D4_word4_1_alpha :
    wordElt .D4 d4Word4_1 • permLattice (τ := .D4) TwistTag.D4.perm
      (![1, 0, 0, 0] : Fin Tag.D4.rank → ℤ) = ![1, 0, 0, 0] := by
  rw [ToralSign.wordElt]
  simp only [d4Word4_1, CFSG.LieType.Chevalley.wordProd_smul]
  ext i
  fin_cases i <;> decide

private lemma theta_D4_word4_1_beta :
    wordElt .D4 d4Word4_1 • permLattice (τ := .D4) TwistTag.D4.perm
      (![0, 1, 1, 1] : Fin Tag.D4.rank → ℤ) = ![0, 1, 1, 1] := by
  rw [ToralSign.wordElt]
  simp only [d4Word4_1, CFSG.LieType.Chevalley.wordProd_smul]
  ext i
  fin_cases i <;> decide

private lemma theta_D4_word4_2_alpha :
    wordElt .D4 d4Word4_2 • permLattice (τ := .D4) TwistTag.D4.perm
      (![0, 0, 0, 1] : Fin Tag.D4.rank → ℤ) = ![0, 0, 0, 1] := by
  rw [ToralSign.wordElt]
  simp only [d4Word4_2, CFSG.LieType.Chevalley.wordProd_smul]
  ext i
  fin_cases i <;> decide

private lemma theta_D4_word4_2_beta :
    wordElt .D4 d4Word4_2 • permLattice (τ := .D4) TwistTag.D4.perm
      (![1, 1, 1, 0] : Fin Tag.D4.rank → ℤ) = ![1, 1, 1, 0] := by
  rw [ToralSign.wordElt]
  simp only [d4Word4_2, CFSG.LieType.Chevalley.wordProd_smul]
  ext i
  fin_cases i <;> decide

private lemma theta_D4_word4_3_alpha :
    wordElt .D4 d4Word4_3 • permLattice (τ := .D4) TwistTag.D4.perm
      (![0, 1, 0, 0] : Fin Tag.D4.rank → ℤ) = ![0, 1, 0, 0] := by
  rw [ToralSign.wordElt]
  simp only [d4Word4_3, CFSG.LieType.Chevalley.wordProd_smul]
  ext i
  fin_cases i <;> decide

private lemma theta_D4_word4_3_beta :
    wordElt .D4 d4Word4_3 • permLattice (τ := .D4) TwistTag.D4.perm
      (![1, 0, 1, 1] : Fin Tag.D4.rank → ℤ) = ![1, 0, 1, 1] := by
  rw [ToralSign.wordElt]
  simp only [d4Word4_3, CFSG.LieType.Chevalley.wordProd_smul]
  ext i
  fin_cases i <;> decide


private lemma exists_inv_good_D4tw_twist_of {K k : Type} [Field K] [Finite K] [Field k]
    [IsAlgClosed k] (ι : K →+* k) {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    [CharP K p] [CharP k p] (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e)
    (l : List (Fin Tag.D4.rank)) {α β : Fin Tag.D4.rank → ℤ}
    (hθα : wordElt TwistTag.D4.tag l • permLattice TwistTag.D4.perm α = α)
    (hθβ : wordElt TwistTag.D4.tag l • permLattice TwistTag.D4.perm β = β)
    (hα : IsRoot .D4 α) (hβ : IsRoot .D4 β)
    (hαβ : α ≠ β ∧ α ≠ -β ∧ IsRoot .D4 (α + β))
    (hzα : RootsCommute .D4 (α + β) α) (hzβ : RootsCommute .D4 (α + β) β)
    (hχ : rootChar (signCharTuple (k := k) (signMaskChar .D4 4)) β = -1) :
    ∃ u : fixedPointsIn (adjointGroup TwistTag.D4.tag k) (frobTwistGL TwistTag.D4.tag k p e
        (wordWeylMatrix TwistTag.D4.tag k l * diagramMap TwistTag.D4 k)),
      orderOf u = p ∧ IsSpecialGood p u ∧
      rootDiagUnit TwistTag.D4.tag (signCharTuple (k := k) (signMaskChar .D4 4)) *
          (u : ModGL TwistTag.D4.tag k) *
          (rootDiagUnit TwistTag.D4.tag
            (signCharTuple (k := k) (signMaskChar .D4 4)))⁻¹ =
        (u : ModGL TwistTag.D4.tag k)⁻¹ := by
  have hQα : ∃ s : k, s * s = 1 ∧ ∀ c : k,
      (wordWeylMatrix TwistTag.D4.tag k l * diagramMap TwistTag.D4 k) *
          pinnedX TwistTag.D4.tag k α c *
          (wordWeylMatrix TwistTag.D4.tag k l * diagramMap TwistTag.D4 k)⁻¹ =
        pinnedX TwistTag.D4.tag k α (s * c) := by
    obtain ⟨s, hs, h⟩ := twistMatrix_conj_pinnedX (k := k) TwistTag.D4 l hα
    exact ⟨s, hs, fun c => by rw [h c, hθα]⟩
  have hQβ : ∃ s : k, s * s = 1 ∧ ∀ c : k,
      (wordWeylMatrix TwistTag.D4.tag k l * diagramMap TwistTag.D4 k) *
          pinnedX TwistTag.D4.tag k β c *
          (wordWeylMatrix TwistTag.D4.tag k l * diagramMap TwistTag.D4 k)⁻¹ =
        pinnedX TwistTag.D4.tag k β (s * c) := by
    obtain ⟨s, hs, h⟩ := twistMatrix_conj_pinnedX (k := k) TwistTag.D4 l hβ
    exact ⟨s, hs, fun c => by rw [h c, hθβ]⟩
  refine exists_twist_fixed_inv_good (τ := .D4) (hτ := Or.inl rfl) (K := K) (k := k)
    (ι := ι) (p := p) (e := e) (hp2 := hp2) (hK := hK) (h3 := h3)
    (Q := wordWeylMatrix TwistTag.D4.tag k l * diagramMap TwistTag.D4 k)
    (α := α) (β := β) hα hβ hQα hQβ hαβ hzα hzβ
    (t := rootDiagUnit .D4 (signCharTuple (k := k) (signMaskChar .D4 4))) ?_
  intro c
  rw [rootDiagUnit_conj_pinnedX _ hβ c, hχ, Units.val_neg, Units.val_one, neg_one_mul]

theorem exists_inv_good_D4tw_twist {K k : Type} [Field K] [Finite K] [Field k] [IsAlgClosed k]
    (ι : K →+* k) {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) [CharP K p] [CharP k p]
    (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) {r : SignRep .D4} (hr : r ∈ d4SignDiagramReps)
    (hr0 : r.mask ≠ 0) {l : List (Fin Tag.D4.rank)} (hl : l ∈ r.omegaWords) :
    ∃ u : fixedPointsIn (adjointGroup TwistTag.D4.tag k) (frobTwistGL TwistTag.D4.tag k p e
        (wordWeylMatrix TwistTag.D4.tag k l * diagramMap TwistTag.D4 k)),
      orderOf u = p ∧ IsSpecialGood p u ∧
      rootDiagUnit TwistTag.D4.tag (signCharTuple (k := k) (signMaskChar TwistTag.D4.tag r.mask)) *
          (u : ModGL TwistTag.D4.tag k) *
          (rootDiagUnit TwistTag.D4.tag
            (signCharTuple (k := k) (signMaskChar TwistTag.D4.tag r.mask)))⁻¹ =
        (u : ModGL TwistTag.D4.tag k)⁻¹ := by
  simp only [d4SignDiagramReps, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl
  · exact absurd rfl hr0
  · simp only [d4OmegaWords4, List.mem_cons, List.mem_nil_iff, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · let α : Fin Tag.D4.rank → ℤ := ![0, 0, 1, 0]
      let β : Fin Tag.D4.rank → ℤ := ![1, 1, 1, 1]
      have hθα : wordElt TwistTag.D4.tag [] • permLattice TwistTag.D4.perm α = α :=
        theta_D4_nil_alpha
      have hθβ : wordElt TwistTag.D4.tag [] • permLattice TwistTag.D4.perm β = β :=
        theta_D4_nil_beta
      have hχ : rootChar (signCharTuple (k := k) (signMaskChar .D4 4)) β = -1 := by
        rw [rootChar_signCharTuple]
        have h : signMaskChar .D4 4 (Multiplicative.ofAdd β) = -1 := by decide
        rw [h]
        simp [intUnitsMap]
      refine exists_inv_good_D4tw_twist_of ι hp2 hK h3 [] (α := α) (β := β) hθα hθβ
        (isRoot_iff_mem_artifactRoots.2 (by decide))
        (isRoot_iff_mem_artifactRoots.2 (by decide))
        ⟨fun e => (by decide : List.ofFn α ≠ List.ofFn β) (by rw [e]),
          fun e => (by decide : List.ofFn α ≠ List.ofFn (-β)) (by rw [e]),
          isRoot_iff_mem_artifactRoots.2 (by decide)⟩
        (rootsCommute_of_list (by decide) (by decide) (by decide))
        (rootsCommute_of_list (by decide) (by decide) (by decide)) hχ
    · let α : Fin Tag.D4.rank → ℤ := ![1, 0, 0, 0]
      let β : Fin Tag.D4.rank → ℤ := ![0, 1, 1, 1]
      have hθα : wordElt TwistTag.D4.tag d4Word4_1 • permLattice TwistTag.D4.perm α = α :=
        theta_D4_word4_1_alpha
      have hθβ : wordElt TwistTag.D4.tag d4Word4_1 • permLattice TwistTag.D4.perm β = β :=
        theta_D4_word4_1_beta
      have hχ : rootChar (signCharTuple (k := k) (signMaskChar .D4 4)) β = -1 := by
        rw [rootChar_signCharTuple]
        have h : signMaskChar .D4 4 (Multiplicative.ofAdd β) = -1 := by decide
        rw [h]
        simp [intUnitsMap]
      refine exists_inv_good_D4tw_twist_of ι hp2 hK h3 d4Word4_1 (α := α) (β := β) hθα hθβ
        (isRoot_iff_mem_artifactRoots.2 (by decide))
        (isRoot_iff_mem_artifactRoots.2 (by decide))
        ⟨fun e => (by decide : List.ofFn α ≠ List.ofFn β) (by rw [e]),
          fun e => (by decide : List.ofFn α ≠ List.ofFn (-β)) (by rw [e]),
          isRoot_iff_mem_artifactRoots.2 (by decide)⟩
        (rootsCommute_of_list (by decide) (by decide) (by decide))
        (rootsCommute_of_list (by decide) (by decide) (by decide)) hχ
    · let α : Fin Tag.D4.rank → ℤ := ![0, 0, 0, 1]
      let β : Fin Tag.D4.rank → ℤ := ![1, 1, 1, 0]
      have hθα : wordElt TwistTag.D4.tag d4Word4_2 • permLattice TwistTag.D4.perm α = α :=
        theta_D4_word4_2_alpha
      have hθβ : wordElt TwistTag.D4.tag d4Word4_2 • permLattice TwistTag.D4.perm β = β :=
        theta_D4_word4_2_beta
      have hχ : rootChar (signCharTuple (k := k) (signMaskChar .D4 4)) β = -1 := by
        rw [rootChar_signCharTuple]
        have h : signMaskChar .D4 4 (Multiplicative.ofAdd β) = -1 := by decide
        rw [h]
        simp [intUnitsMap]
      refine exists_inv_good_D4tw_twist_of ι hp2 hK h3 d4Word4_2 (α := α) (β := β) hθα hθβ
        (isRoot_iff_mem_artifactRoots.2 (by decide))
        (isRoot_iff_mem_artifactRoots.2 (by decide))
        ⟨fun e => (by decide : List.ofFn α ≠ List.ofFn β) (by rw [e]),
          fun e => (by decide : List.ofFn α ≠ List.ofFn (-β)) (by rw [e]),
          isRoot_iff_mem_artifactRoots.2 (by decide)⟩
        (rootsCommute_of_list (by decide) (by decide) (by decide))
        (rootsCommute_of_list (by decide) (by decide) (by decide)) hχ
    · let α : Fin Tag.D4.rank → ℤ := ![0, 1, 0, 0]
      let β : Fin Tag.D4.rank → ℤ := ![1, 0, 1, 1]
      have hθα : wordElt TwistTag.D4.tag d4Word4_3 • permLattice TwistTag.D4.perm α = α :=
        theta_D4_word4_3_alpha
      have hθβ : wordElt TwistTag.D4.tag d4Word4_3 • permLattice TwistTag.D4.perm β = β :=
        theta_D4_word4_3_beta
      have hχ : rootChar (signCharTuple (k := k) (signMaskChar .D4 4)) β = -1 := by
        rw [rootChar_signCharTuple]
        have h : signMaskChar .D4 4 (Multiplicative.ofAdd β) = -1 := by decide
        rw [h]
        simp [intUnitsMap]
      refine exists_inv_good_D4tw_twist_of ι hp2 hK h3 d4Word4_3 (α := α) (β := β) hθα hθβ
        (isRoot_iff_mem_artifactRoots.2 (by decide))
        (isRoot_iff_mem_artifactRoots.2 (by decide))
        ⟨fun e => (by decide : List.ofFn α ≠ List.ofFn β) (by rw [e]),
          fun e => (by decide : List.ofFn α ≠ List.ofFn (-β)) (by rw [e]),
          isRoot_iff_mem_artifactRoots.2 (by decide)⟩
        (rootsCommute_of_list (by decide) (by decide) (by decide))
        (rootsCommute_of_list (by decide) (by decide) (by decide)) hχ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
