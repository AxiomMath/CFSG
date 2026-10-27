module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.TwRoot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcTwistTheta

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley.ToralSign
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootChar rootDiagUnit)


private lemma d4Tw_apply {k : Type} [Field k] [IsAlgClosed k] [CharP k 3]
    (l : List (Fin Tag.D4.rank)) {α β : Fin Tag.D4.rank → ℤ}
    {δ γ : Fin 3 → Fin Tag.D4.rank → ℤ}
    (hθα : wordElt .D4 l • permLattice (τ := .D4) TwistTag.D4.perm α = α)
    (hθβ : wordElt .D4 l • permLattice (τ := .D4) TwistTag.D4.perm β = β)
    (hθε : wordElt .D4 l • permLattice (τ := .D4) TwistTag.D4.perm (α + β) = α + β)
    (hα : IsRoot .D4 α) (hβ : IsRoot .D4 β)
    (hαβ : α ≠ β ∧ α ≠ -β ∧ IsRoot .D4 (α + β))
    (hzα : RootsCommute .D4 (α + β) α) (hzβ : RootsCommute .D4 (α + β) β)
    (hδ : ∀ i, IsRoot .D4 (δ i)) (hγ : ∀ i, IsRoot .D4 (γ i))
    (hθδ : ∀ i, wordElt .D4 l • permLattice (τ := .D4) TwistTag.D4.perm (δ i) = δ (i + 1))
    (hθγ : ∀ i, wordElt .D4 l • permLattice (τ := .D4) TwistTag.D4.perm (γ i) = γ (i + 1))
    (hsum : ∀ i, δ i + γ i = α + β) (hne : ∀ i, δ i ≠ γ i ∧ δ i ≠ -γ i)
    (hδδ : ∀ i j, i ≠ j → RootsCommute .D4 (δ i) (δ j))
    (hγγ : ∀ i j, i ≠ j → RootsCommute .D4 (γ i) (γ j))
    (hδγ : ∀ i j, i ≠ j → RootsCommute .D4 (δ i) (γ j))
    (hz : ∀ i, RootsCommute .D4 (α + β) (δ i) ∧ RootsCommute .D4 (α + β) (γ i))
    (hcross : ∀ i, ∀ ρ ∈ [α, β], RootsCommute .D4 ρ (δ i) ∧ RootsCommute .D4 ρ (γ i))
    (hχ' : signMaskChar .D4 4 (Multiplicative.ofAdd β) = -1) :
    ∃ u : fixedPointsIn (adjointGroup TwistTag.D4.tag k) (frobTwistGL TwistTag.D4.tag k 3 1
        (wordWeylMatrix TwistTag.D4.tag k l * diagramMap TwistTag.D4 k)),
      orderOf u = 3 ∧ IsExtraGood u ∧
      rootDiagUnit TwistTag.D4.tag (signCharTuple (k := k) (signMaskChar .D4 4)) *
          (u : ModGL TwistTag.D4.tag k) *
          (rootDiagUnit TwistTag.D4.tag
            (signCharTuple (k := k) (signMaskChar .D4 4)))⁻¹ =
        (u : ModGL TwistTag.D4.tag k)⁻¹ := by
  have hχ : rootChar (signCharTuple (k := k) (signMaskChar .D4 4)) β = -1 := by
    rw [rootChar_signCharTuple, hχ']
    simp [intUnitsMap]
  refine exists_twist_fixed_orbit_three_inv_extraGood (τ := .D4) (Or.inl rfl) (k := k)
    (wordWeylMatrix TwistTag.D4.tag k l * diagramMap TwistTag.D4 k)
    (fun v => wordElt .D4 l • permLattice (τ := .D4) TwistTag.D4.perm v)
    ?_ (α := α) (β := β) hα hβ hθα hθβ hαβ hθε hzα hzβ
    (δ := δ) (γ := γ) hδ hγ hθδ hθγ hsum hne hδδ hγγ hδγ hz hcross
    (t := rootDiagUnit .D4 (signCharTuple (k := k) (signMaskChar .D4 4))) ?_
  · intro v hv
    exact twistMatrix_conj_pinnedX (k := k) TwistTag.D4 l hv
  · intro c
    rw [rootDiagUnit_conj_pinnedX _ hβ c, hχ, Units.val_neg, Units.val_one, neg_one_mul]

theorem exists_inv_extraGood_D4tw_twist {k : Type} [Field k] [IsAlgClosed k] [CharP k 3]
    {r : SignRep .D4} (hr : r ∈ d4SignDiagramReps) (hr0 : r.mask ≠ 0)
    {l : List (Fin Tag.D4.rank)} (hl : l ∈ r.omegaWords) :
    ∃ u : fixedPointsIn (adjointGroup TwistTag.D4.tag k) (frobTwistGL TwistTag.D4.tag k 3 1
        (wordWeylMatrix TwistTag.D4.tag k l * diagramMap TwistTag.D4 k)),
      orderOf u = 3 ∧ IsExtraGood u ∧
      rootDiagUnit TwistTag.D4.tag (signCharTuple (k := k) (signMaskChar TwistTag.D4.tag r.mask)) *
          (u : ModGL TwistTag.D4.tag k) *
          (rootDiagUnit TwistTag.D4.tag
            (signCharTuple (k := k) (signMaskChar TwistTag.D4.tag r.mask)))⁻¹ =
        (u : ModGL TwistTag.D4.tag k)⁻¹ := by
  simp only [d4SignDiagramReps, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl
  · exact absurd rfl hr0
  simp only [d4OmegaWords4, List.mem_cons, List.mem_nil_iff, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl <;>
  [(let α : Fin Tag.D4.rank → ℤ := ![0, 0, 1, 0]
    let β : Fin Tag.D4.rank → ℤ := ![1, 1, 1, 1]
    let δ : Fin 3 → Fin Tag.D4.rank → ℤ := ![![0, 1, 1, 0], ![0, 0, 1, 1], ![1, 0, 1, 0]]
    let γ : Fin 3 → Fin Tag.D4.rank → ℤ := ![![1, 0, 1, 1], ![1, 1, 1, 0], ![0, 1, 1, 1]]
    apply d4Tw_apply [] (α := α) (β := β) (δ := δ) (γ := γ));
   (let α : Fin Tag.D4.rank → ℤ := ![1, 0, 0, 0]
    let β : Fin Tag.D4.rank → ℤ := ![0, 1, 1, 1]
    let δ : Fin 3 → Fin Tag.D4.rank → ℤ := ![![0, 0, 0, 1], ![0, 1, 0, 0], ![1, 1, 2, 1]]
    let γ : Fin 3 → Fin Tag.D4.rank → ℤ := ![![1, 1, 1, 0], ![1, 0, 1, 1], ![0, 0, -1, 0]]
    apply d4Tw_apply d4Word4_1 (α := α) (β := β) (δ := δ) (γ := γ));
   (let α : Fin Tag.D4.rank → ℤ := ![0, 0, 0, 1]
    let β : Fin Tag.D4.rank → ℤ := ![1, 1, 1, 0]
    let δ : Fin 3 → Fin Tag.D4.rank → ℤ := ![![1, 0, 0, 0], ![1, 1, 2, 1], ![0, 1, 0, 0]]
    let γ : Fin 3 → Fin Tag.D4.rank → ℤ := ![![0, 1, 1, 1], ![0, 0, -1, 0], ![1, 0, 1, 1]]
    apply d4Tw_apply d4Word4_2 (α := α) (β := β) (δ := δ) (γ := γ));
   (let α : Fin Tag.D4.rank → ℤ := ![0, 1, 0, 0]
    let β : Fin Tag.D4.rank → ℤ := ![1, 0, 1, 1]
    let δ : Fin 3 → Fin Tag.D4.rank → ℤ := ![![1, 0, 0, 0], ![0, 0, 0, 1], ![1, 1, 2, 1]]
    let γ : Fin 3 → Fin Tag.D4.rank → ℤ := ![![0, 1, 1, 1], ![1, 1, 1, 0], ![0, 0, -1, 0]]
    apply d4Tw_apply d4Word4_3 (α := α) (β := β) (δ := δ) (γ := γ))]
  all_goals
    first
      | intro i
        fin_cases i <;>
          (rw [ToralSign.wordElt]
           simp only [CFSG.LieType.Chevalley.wordProd_smul, d4Word4_1, d4Word4_2, d4Word4_3]
           ext j
           fin_cases j <;> decide)
      | intro i
        fin_cases i <;> exact isRoot_iff_mem_artifactRoots.2 (by decide)
      | intro i
        fin_cases i <;> exact ⟨by decide, by decide⟩
      | intro i
        fin_cases i <;> decide
      | intro i j hij
        fin_cases i <;> fin_cases j <;>
          first
            | exact absurd rfl hij
            | exact rootsCommute_of_list (by decide) (by decide) (by decide)
      | intro i
        fin_cases i <;>
          exact ⟨rootsCommute_of_list (by decide) (by decide) (by decide),
            rootsCommute_of_list (by decide) (by decide) (by decide)⟩
      | intro i ρ hρ
        fin_cases i <;> simp only [List.mem_cons, List.mem_nil_iff, or_false] at hρ
        all_goals rcases hρ with rfl | rfl
        all_goals
          exact ⟨rootsCommute_of_list (by decide) (by decide) (by decide),
            rootsCommute_of_list (by decide) (by decide) (by decide)⟩
      | rw [ToralSign.wordElt]
        simp only [CFSG.LieType.Chevalley.wordProd_smul, d4Word4_1, d4Word4_2, d4Word4_3]
        ext i
        fin_cases i <;> decide
      | exact rootsCommute_of_list (by decide) (by decide) (by decide)
      | exact ⟨fun e => (by decide : List.ofFn α ≠ List.ofFn β) (by rw [e]),
          fun e => (by decide : List.ofFn α ≠ List.ofFn (-β)) (by rw [e]),
          isRoot_iff_mem_artifactRoots.2 (by decide)⟩
      | exact isRoot_iff_mem_artifactRoots.2 (by decide)
      | decide

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

end
