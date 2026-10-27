module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.TwRoot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.ExcTwistTheta

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley.ToralSign
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  (rootChar rootChar_nsmul_single rootDiagUnit)


private lemma twE6_exists_inv_extraGood_E6tw_twist_of_mask {k : Type} [Field k] [IsAlgClosed k]
    [CharP k 3] (m : ℕ)
    (hm : signMaskChar TwistTag.E6.tag m
      (Multiplicative.ofAdd (![1,1,1,1,0,0] : Fin TwistTag.E6.tag.rank → ℤ)) = -1)
    (hm' : signMaskChar TwistTag.E6.tag m
      (Multiplicative.ofAdd (![0,1,0,1,1,1] : Fin TwistTag.E6.tag.rank → ℤ)) = -1) :
    ∃ u : fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k 3 1
          (wordWeylMatrix TwistTag.E6.tag k ([] : List (Fin TwistTag.E6.tag.rank)) *
            diagramMap TwistTag.E6 k)),
      orderOf u = 3 ∧ IsExtraGood u ∧
      rootDiagUnit TwistTag.E6.tag
          (signCharTuple (k := k) (signMaskChar TwistTag.E6.tag m)) *
          (u : ModGL TwistTag.E6.tag k) *
          (rootDiagUnit TwistTag.E6.tag
            (signCharTuple (k := k) (signMaskChar TwistTag.E6.tag m)))⁻¹ =
        (u : ModGL TwistTag.E6.tag k)⁻¹ := by
  let β : Fin TwistTag.E6.tag.rank → ℤ := ![1,1,1,1,0,0]
  let γ : Fin TwistTag.E6.tag.rank → ℤ := ![0,1,1,2,2,1]
  let θβ : Fin TwistTag.E6.tag.rank → ℤ := ![0,1,0,1,1,1]
  let θγ : Fin TwistTag.E6.tag.rank → ℤ := ![1,1,2,2,1,0]
  let θ : (Fin TwistTag.E6.tag.rank → ℤ) → Fin TwistTag.E6.tag.rank → ℤ :=
    fun v => wordElt TwistTag.E6.tag ([] : List (Fin TwistTag.E6.tag.rank)) •
      permLattice (τ := TwistTag.E6.tag) TwistTag.E6.perm v
  have hθβ : θ β = θβ := by
    dsimp [θ, β, θβ]
    rw [wordElt_nil, one_smul]
    ext i
    fin_cases i <;> decide
  have hθγ : θ γ = θγ := by
    dsimp [θ, γ, θγ]
    rw [wordElt_nil, one_smul]
    ext i
    fin_cases i <;> decide
  have hθθβ : θ (θ β) = β := by
    rw [hθβ]
    dsimp [θ, β, θβ]
    rw [wordElt_nil, one_smul]
    ext i
    fin_cases i <;> decide
  have hθθγ : θ (θ γ) = γ := by
    rw [hθγ]
    dsimp [θ, γ, θγ]
    rw [wordElt_nil, one_smul]
    ext i
    fin_cases i <;> decide
  have hβ : IsRoot TwistTag.E6.tag β := isRoot_iff_mem_artifactRoots.2 (by decide)
  have hγ : IsRoot TwistTag.E6.tag γ := isRoot_iff_mem_artifactRoots.2 (by decide)
  have hθβr : IsRoot TwistTag.E6.tag (θ β) := by
    rw [hθβ]
    exact isRoot_iff_mem_artifactRoots.2 (by decide)
  have hθγr : IsRoot TwistTag.E6.tag (θ γ) := by
    rw [hθγ]
    exact isRoot_iff_mem_artifactRoots.2 (by decide)
  have hβγ : β ≠ γ ∧ β ≠ -γ ∧ IsRoot TwistTag.E6.tag (β + γ) := by
    refine ⟨?_, ?_, isRoot_iff_mem_artifactRoots.2 (by decide)⟩
    · intro h
      exact (by decide : List.ofFn β ≠ List.ofFn γ) (by rw [h])
    · intro h
      exact (by decide : List.ofFn β ≠ List.ofFn (-γ)) (by rw [h])
  have hθβθγ : θ β ≠ θ γ ∧ θ β ≠ -θ γ := by
    rw [hθβ, hθγ]
    refine ⟨?_, ?_⟩
    · intro h
      exact (by decide : List.ofFn θβ ≠ List.ofFn θγ) (by rw [h])
    · intro h
      exact (by decide : List.ofFn θβ ≠ List.ofFn (-θγ)) (by rw [h])
  have hsum : θ β + θ γ = β + γ := by
    rw [hθβ, hθγ]
    ext i
    fin_cases i <;> decide
  have hθε : θ (β + γ) = β + γ := by
    dsimp [θ]
    rw [wordElt_nil, one_smul]
    ext i
    fin_cases i <;> decide
  have hββ : RootsCommute TwistTag.E6.tag β (θ β) := by
    rw [hθβ]
    exact rootsCommute_of_list (by decide) (by decide) (by decide)
  have hγγ : RootsCommute TwistTag.E6.tag γ (θ γ) := by
    rw [hθγ]
    exact rootsCommute_of_list (by decide) (by decide) (by decide)
  have hβθγ : RootsCommute TwistTag.E6.tag β (θ γ) := by
    rw [hθγ]
    exact rootsCommute_of_list (by decide) (by decide) (by decide)
  have hθβγ : RootsCommute TwistTag.E6.tag (θ β) γ := by
    rw [hθβ]
    exact rootsCommute_of_list (by decide) (by decide) (by decide)
  have hz : ∀ ρ ∈ [β, θ β, γ, θ γ], RootsCommute TwistTag.E6.tag (β + γ) ρ := by
    intro ρ hρ
    rw [hθβ, hθγ] at hρ
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hρ
    rcases hρ with rfl | rfl | rfl | rfl
    · exact rootsCommute_of_list (by decide) (by decide) (by decide)
    · exact rootsCommute_of_list (by decide) (by decide) (by decide)
    · exact rootsCommute_of_list (by decide) (by decide) (by decide)
    · exact rootsCommute_of_list (by decide) (by decide) (by decide)
  obtain ⟨sb, hsb, hQβ⟩ := twistMatrix_conj_pinnedX (k := k) TwistTag.E6 [] hβ
  obtain ⟨sb', hsb', hQβ'⟩ := twistMatrix_conj_pinnedX (k := k) TwistTag.E6 [] hθβr
  have hQβ'' : ∀ c, (wordWeylMatrix TwistTag.E6.tag k [] * diagramMap TwistTag.E6 k) *
      pinnedX TwistTag.E6.tag k (θ β) c *
      (wordWeylMatrix TwistTag.E6.tag k [] * diagramMap TwistTag.E6 k)⁻¹ =
      pinnedX TwistTag.E6.tag k β (sb' * c) := by
    intro c
    rw [hQβ' c]
    dsimp [θ] at hθθβ ⊢
    rw [hθθβ]
  have hsb_mul : (sb * sb') * (sb * sb') = 1 := by
    rw [mul_mul_mul_comm, hsb, hsb', one_mul]
  obtain ⟨lam, hlam8⟩ := IsAlgClosed.exists_pow_nat_eq (sb * sb') (by decide : 0 < 8)
  have hlam0 : lam ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide : 8 ≠ 0)] at hlam8
    rw [← hlam8] at hsb_mul
    norm_num at hsb_mul
  have hlam : lam ^ 9 = lam * (sb * sb') := by
    rw [show 9 = 8 + 1 by decide, pow_succ, hlam8, mul_comm]
  obtain ⟨u, huval, huord, hugood⟩ :=
    exists_twist_orbit_two_extraGood (τ := TwistTag.E6.tag)
      (hτ := Or.inr (Or.inl (by decide)))
      (Q := wordWeylMatrix TwistTag.E6.tag k ([] : List (Fin TwistTag.E6.tag.rank)) *
        diagramMap TwistTag.E6 k)
      (θ := θ) (hQ := fun ρ hρ => twistMatrix_conj_pinnedX TwistTag.E6 [] hρ)
      (β := β) (γ := γ) hβ hγ hθβr hθγr hθθγ hβγ hθβθγ hsum hθε
      hββ hγγ hβθγ hθβγ hz hsb hsb' hQβ hQβ'' hlam0 hlam
  refine ⟨u, huord, hugood, ?_⟩
  rw [huval]
  let a := signCharTuple (k := k) (signMaskChar TwistTag.E6.tag m)
  have hrootCharβ : (rootChar (τ := TwistTag.E6.tag) a β : k) = -1 := by
    dsimp [a]
    rw [rootChar_signCharTuple]
    rw [show signMaskChar TwistTag.E6.tag m (Multiplicative.ofAdd β) = -1 from hm]
    simp [intUnitsMap]
  have hrootCharθβ : (rootChar (τ := TwistTag.E6.tag) a (θ β) : k) = -1 := by
    dsimp [a]
    rw [rootChar_signCharTuple]
    rw [hθβ]
    rw [show signMaskChar TwistTag.E6.tag m (Multiplicative.ofAdd θβ) = -1 from hm']
    simp [intUnitsMap]
  have hcomm : Commute (pinnedX TwistTag.E6.tag k β lam)
      (pinnedX TwistTag.E6.tag k (θ β) (sb * lam ^ 3)) :=
    (simply_laced_root_commutator_unit TwistTag.E6.tag (Or.inr (Or.inl (by decide)))
      hβ hθβr hββ.1 hββ.2.1).2 hββ.2.2 k (pinnedX TwistTag.E6.tag k β lam)
      (Subgroup.subset_closure ⟨lam, rfl⟩)
      (pinnedX TwistTag.E6.tag k (θ β) (sb * lam ^ 3))
      (Subgroup.subset_closure ⟨sb * lam ^ 3, rfl⟩)
  calc rootDiagUnit TwistTag.E6.tag a *
        (pinnedX TwistTag.E6.tag k β lam * pinnedX TwistTag.E6.tag k (θ β) (sb * lam ^ 3)) *
        (rootDiagUnit TwistTag.E6.tag a)⁻¹
      = (rootDiagUnit TwistTag.E6.tag a * pinnedX TwistTag.E6.tag k β lam *
            (rootDiagUnit TwistTag.E6.tag a)⁻¹) *
          (rootDiagUnit TwistTag.E6.tag a * pinnedX TwistTag.E6.tag k (θ β) (sb * lam ^ 3) *
            (rootDiagUnit TwistTag.E6.tag a)⁻¹) := by group
    _ = pinnedX TwistTag.E6.tag k β
          ((rootChar (τ := TwistTag.E6.tag) a β : k) * lam) *
          pinnedX TwistTag.E6.tag k (θ β)
            ((rootChar (τ := TwistTag.E6.tag) a (θ β) : k) * (sb * lam ^ 3)) := by
        rw [rootDiagUnit_conj_pinnedX a hβ lam,
          rootDiagUnit_conj_pinnedX a hθβr (sb * lam ^ 3)]
    _ = pinnedX TwistTag.E6.tag k β (-lam) *
          pinnedX TwistTag.E6.tag k (θ β) (-(sb * lam ^ 3)) := by
        rw [hrootCharβ, hrootCharθβ]
        ring_nf
    _ = (pinnedX TwistTag.E6.tag k β lam)⁻¹ *
          (pinnedX TwistTag.E6.tag k (θ β) (sb * lam ^ 3))⁻¹ := by
        rw [pinnedX_neg, pinnedX_neg]
    _ = (pinnedX TwistTag.E6.tag k β lam *
          pinnedX TwistTag.E6.tag k (θ β) (sb * lam ^ 3))⁻¹ := by
        rw [mul_inv_rev]
        exact hcomm.inv_inv.eq

theorem exists_inv_extraGood_E6tw_twist {k : Type} [Field k] [IsAlgClosed k] [CharP k 3]
    {r : SignRep .E6} (hr : r ∈ e6SignDiagramReps) (hr0 : r.mask ≠ 0)
    {l : List (Fin Tag.E6.rank)} (hl : l ∈ r.omegaWords) :
    ∃ u : fixedPointsIn (adjointGroup TwistTag.E6.tag k) (frobTwistGL TwistTag.E6.tag k 3 1
        (wordWeylMatrix TwistTag.E6.tag k l * diagramMap TwistTag.E6 k)),
      orderOf u = 3 ∧ IsExtraGood u ∧
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
    exact twE6_exists_inv_extraGood_E6tw_twist_of_mask 20 (by decide) (by decide)
  · simp only [e6OmegaWords2, List.mem_cons, List.mem_nil_iff, or_false] at hl
    subst hl
    exact twE6_exists_inv_extraGood_E6tw_twist_of_mask 2 (by decide) (by decide)

theorem exists_inv_extraGood_E6tw_graph {k : Type} [Field k] [IsAlgClosed k] [CharP k 3] :
    ∃ u : fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k 3 1 (diagramMap TwistTag.E6 k)),
      orderOf u = 3 ∧ IsExtraGood u ∧
      diagramMap TwistTag.E6 k * (u : ModGL TwistTag.E6.tag k) * (diagramMap TwistTag.E6 k)⁻¹ =
        (u : ModGL TwistTag.E6.tag k)⁻¹ := by
  let i0 : Fin TwistTag.E6.tag.rank := ⟨0, by decide⟩
  let i5 : Fin TwistTag.E6.tag.rank := ⟨5, by decide⟩
  let β : Fin TwistTag.E6.tag.rank → ℤ := Pi.single i0 1
  let γ : Fin TwistTag.E6.tag.rank → ℤ := ![0,1,1,2,1,1]
  let θβ : Fin TwistTag.E6.tag.rank → ℤ := Pi.single i5 1
  let θγ : Fin TwistTag.E6.tag.rank → ℤ := ![1,1,1,2,1,0]
  let θ : (Fin TwistTag.E6.tag.rank → ℤ) → Fin TwistTag.E6.tag.rank → ℤ :=
    fun v => permLattice (τ := TwistTag.E6.tag) TwistTag.E6.perm v
  have hθβ : θ β = θβ := by
    dsimp [θ, β, θβ]
    rw [permLattice_single]
    rfl
  have hθγ : θ γ = θγ := by
    dsimp [θ, γ, θγ]
    ext i
    fin_cases i <;> decide
  have hθθβ : θ (θ β) = β := by
    rw [hθβ]
    dsimp [θ, β, θβ]
    rw [permLattice_single]
    rfl
  have hθθγ : θ (θ γ) = γ := by
    rw [hθγ]
    dsimp [θ, γ, θγ]
    ext i
    fin_cases i <;> decide
  have hβ : IsRoot TwistTag.E6.tag β := by
    dsimp [β, i0]
    exact isRoot_iff_mem_artifactRoots.2 (by decide)
  have hγ : IsRoot TwistTag.E6.tag γ := isRoot_iff_mem_artifactRoots.2 (by decide)
  have hθβr : IsRoot TwistTag.E6.tag (θ β) := by
    rw [hθβ]
    dsimp [θβ, i5]
    exact isRoot_iff_mem_artifactRoots.2 (by decide)
  have hθγr : IsRoot TwistTag.E6.tag (θ γ) := by
    rw [hθγ]
    exact isRoot_iff_mem_artifactRoots.2 (by decide)
  have hβγ : β ≠ γ ∧ β ≠ -γ ∧ IsRoot TwistTag.E6.tag (β + γ) := by
    refine ⟨?_, ?_, isRoot_iff_mem_artifactRoots.2 (by decide)⟩
    · intro h
      exact (by decide : List.ofFn β ≠ List.ofFn γ) (by rw [h])
    · intro h
      exact (by decide : List.ofFn β ≠ List.ofFn (-γ)) (by rw [h])
  have hθβθγ : θ β ≠ θ γ ∧ θ β ≠ -θ γ := by
    rw [hθβ, hθγ]
    refine ⟨?_, ?_⟩
    · intro h
      exact (by decide : List.ofFn θβ ≠ List.ofFn θγ) (by rw [h])
    · intro h
      exact (by decide : List.ofFn θβ ≠ List.ofFn (-θγ)) (by rw [h])
  have hsum : θ β + θ γ = β + γ := by
    rw [hθβ, hθγ]
    ext i
    fin_cases i <;> decide
  have hθε : θ (β + γ) = β + γ := by
    dsimp [θ]
    ext i
    fin_cases i <;> decide
  have hββ : RootsCommute TwistTag.E6.tag β (θ β) := by
    rw [hθβ]
    exact rootsCommute_of_list (by decide) (by decide) (by decide)
  have hγγ : RootsCommute TwistTag.E6.tag γ (θ γ) := by
    rw [hθγ]
    exact rootsCommute_of_list (by decide) (by decide) (by decide)
  have hβθγ : RootsCommute TwistTag.E6.tag β (θ γ) := by
    rw [hθγ]
    exact rootsCommute_of_list (by decide) (by decide) (by decide)
  have hθβγ : RootsCommute TwistTag.E6.tag (θ β) γ := by
    rw [hθβ]
    exact rootsCommute_of_list (by decide) (by decide) (by decide)
  have hz : ∀ ρ ∈ [β, θ β, γ, θ γ], RootsCommute TwistTag.E6.tag (β + γ) ρ := by
    intro ρ hρ
    rw [hθβ, hθγ] at hρ
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hρ
    rcases hρ with rfl | rfl | rfl | rfl
    · exact rootsCommute_of_list (by decide) (by decide) (by decide)
    · exact rootsCommute_of_list (by decide) (by decide) (by decide)
    · exact rootsCommute_of_list (by decide) (by decide) (by decide)
    · exact rootsCommute_of_list (by decide) (by decide) (by decide)
  have hQβ : ∀ c, diagramMap TwistTag.E6 k * pinnedX TwistTag.E6.tag k β c *
      (diagramMap TwistTag.E6 k)⁻¹ =
      pinnedX TwistTag.E6.tag k (θ β) (1 * c) := by
    intro c
    rw [hθβ]
    have h := diagramMap_conj_pinnedX_single TwistTag.E6 i0 c
    rw [show TwistTag.E6.perm i0 = i5 from by decide] at h
    simpa [β, θβ] using h
  have hQβ' : ∀ c, diagramMap TwistTag.E6 k * pinnedX TwistTag.E6.tag k (θ β) c *
      (diagramMap TwistTag.E6 k)⁻¹ =
      pinnedX TwistTag.E6.tag k β (1 * c) := by
    intro c
    rw [hθβ]
    have h := diagramMap_conj_pinnedX_single TwistTag.E6 i5 c
    rw [show TwistTag.E6.perm i5 = i0 from by decide] at h
    simpa [β, θβ] using h
  obtain ⟨i, hi⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : k) (by decide : 0 < 2)
  have hi0 : i ≠ 0 := by
    intro h
    rw [h, zero_pow (by decide : 2 ≠ 0)] at hi
    norm_num at hi
  have hi3 : (1 : k) * i ^ 3 = -i := by
    rw [show (3 : ℕ) = 2 + 1 by decide, pow_succ, hi]
    ring
  have hi9 : i ^ 9 = i * (1 * 1) := by
    rw [show 9 = 2 * 4 + 1 by decide, pow_succ, pow_mul, hi]
    ring
  obtain ⟨u, huval, huord, hugood⟩ :=
    exists_twist_orbit_two_extraGood (τ := TwistTag.E6.tag)
      (hτ := Or.inr (Or.inl (by decide)))
      (Q := diagramMap TwistTag.E6 k) (θ := θ)
      (hQ := fun ρ hρ => diagramMap_conj_pinnedX TwistTag.E6 hρ)
      (β := β) (γ := γ) hβ hγ hθβr hθγr hθθγ hβγ hθβθγ hsum hθε
      hββ hγγ hβθγ hθβγ hz (one_mul 1) (one_mul 1) hQβ hQβ' hi0 hi9
  refine ⟨u, huord, hugood, ?_⟩
  rw [huval, hi3]
  calc diagramMap TwistTag.E6 k *
        (pinnedX TwistTag.E6.tag k β i * pinnedX TwistTag.E6.tag k (θ β) (-i)) *
        (diagramMap TwistTag.E6 k)⁻¹
      = (diagramMap TwistTag.E6 k * pinnedX TwistTag.E6.tag k β i *
            (diagramMap TwistTag.E6 k)⁻¹) *
          (diagramMap TwistTag.E6 k * pinnedX TwistTag.E6.tag k (θ β) (-i) *
            (diagramMap TwistTag.E6 k)⁻¹) := by group
    _ = pinnedX TwistTag.E6.tag k (θ β) (1 * i) *
          pinnedX TwistTag.E6.tag k β (1 * -i) := by
        rw [hQβ i, hQβ' (-i)]
    _ = pinnedX TwistTag.E6.tag k (θ β) i * pinnedX TwistTag.E6.tag k β (-i) := by
        rw [one_mul, one_mul]
    _ = (pinnedX TwistTag.E6.tag k β i * pinnedX TwistTag.E6.tag k (θ β) (-i))⁻¹ := by
        rw [mul_inv_rev, pinnedX_neg, pinnedX_neg, neg_neg]

theorem exists_inv_extraGood_E6tw_graph_diag {k : Type} [Field k] [IsAlgClosed k] [CharP k 3] :
    ∃ u : fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k 3 1 (diagramMap TwistTag.E6 k)),
      orderOf u = 3 ∧ IsExtraGood u ∧
      (rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] * diagramMap TwistTag.E6 k) *
          (u : ModGL TwistTag.E6.tag k) *
          (rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] * diagramMap TwistTag.E6 k)⁻¹ =
        (u : ModGL TwistTag.E6.tag k)⁻¹ := by
  let i1 : Fin TwistTag.E6.tag.rank := ⟨1, by decide⟩
  let i3 : Fin TwistTag.E6.tag.rank := ⟨3, by decide⟩
  let α : Fin TwistTag.E6.tag.rank → ℤ := Pi.single i3 1
  let β : Fin TwistTag.E6.tag.rank → ℤ := Pi.single i1 1
  let γ : Fin TwistTag.E6.tag.rank → ℤ := ![0,1,1,2,1,0]
  let δ : Fin TwistTag.E6.tag.rank → ℤ := ![0,0,-1,-1,-1,0]
  have hα : IsRoot TwistTag.E6.tag α := by
    dsimp [α, i3]
    exact isRoot_iff_mem_artifactRoots.2 (by decide)
  have hβ : IsRoot TwistTag.E6.tag β := by
    dsimp [β, i1]
    exact isRoot_iff_mem_artifactRoots.2 (by decide)
  have hγ : IsRoot TwistTag.E6.tag γ := isRoot_iff_mem_artifactRoots.2 (by decide)
  have hδ : IsRoot TwistTag.E6.tag δ := isRoot_iff_mem_artifactRoots.2 (by decide)
  have hpermα : permLattice (τ := TwistTag.E6.tag) TwistTag.E6.perm α = α := by
    dsimp [α]
    rw [permLattice_single]
    congr 1
  have hpermβ : permLattice (τ := TwistTag.E6.tag) TwistTag.E6.perm β = β := by
    dsimp [β]
    rw [permLattice_single]
    congr 1
  have hpermγ : permLattice (τ := TwistTag.E6.tag) TwistTag.E6.perm γ = γ := by
    dsimp [γ]
    ext i
    fin_cases i <;> decide
  have hpermδ : permLattice (τ := TwistTag.E6.tag) TwistTag.E6.perm δ = δ := by
    dsimp [δ]
    ext i
    fin_cases i <;> decide
  have hRP : RootPairs TwistTag.E6.tag α β γ δ := RootPairs.of_check (by decide)
  have hQ : ∀ ρ ∈ [α, β, γ, δ], ∃ s : k, s * s = 1 ∧
      ∀ c, diagramMap TwistTag.E6 k * pinnedX TwistTag.E6.tag k ρ c *
        (diagramMap TwistTag.E6 k)⁻¹ = pinnedX TwistTag.E6.tag k ρ (s * c) := by
    intro ρ hρ
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hρ
    rcases hρ with rfl | rfl | rfl | rfl
    · obtain ⟨s, hs, hX⟩ := diagramMap_conj_pinnedX (K := k) TwistTag.E6 hα
      exact ⟨s, hs, fun c => by rw [hX c, hpermα]⟩
    · obtain ⟨s, hs, hX⟩ := diagramMap_conj_pinnedX (K := k) TwistTag.E6 hβ
      exact ⟨s, hs, fun c => by rw [hX c, hpermβ]⟩
    · obtain ⟨s, hs, hX⟩ := diagramMap_conj_pinnedX (K := k) TwistTag.E6 hγ
      exact ⟨s, hs, fun c => by rw [hX c, hpermγ]⟩
    · obtain ⟨s, hs, hX⟩ := diagramMap_conj_pinnedX (K := k) TwistTag.E6 hδ
      exact ⟨s, hs, fun c => by rw [hX c, hpermδ]⟩
  have htB : ∀ c : k,
      (rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] * diagramMap TwistTag.E6 k) *
          pinnedX TwistTag.E6.tag k β c *
          (rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] * diagramMap TwistTag.E6 k)⁻¹ =
        pinnedX TwistTag.E6.tag k β (-c) := by
    intro c
    have hP : diagramMap TwistTag.E6 k * pinnedX TwistTag.E6.tag k β c *
        (diagramMap TwistTag.E6 k)⁻¹ = pinnedX TwistTag.E6.tag k β c := by
      have h := diagramMap_conj_pinnedX_single TwistTag.E6 i1 c
      rw [show TwistTag.E6.perm i1 = i1 from by decide] at h
      simpa [β] using h
    have hb : rootChar (τ := TwistTag.E6.tag)
        (![1, -1, 1, 1, 1, 1] : Fin TwistTag.E6.tag.rank → kˣ) β = -1 := by
      have h := rootChar_nsmul_single (τ := TwistTag.E6.tag) (K := k)
        (![1, -1, 1, 1, 1, 1] : Fin TwistTag.E6.tag.rank → kˣ) i1 1
      simp only [one_smul, pow_one] at h
      rw [h]
      rfl
    calc (rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] * diagramMap TwistTag.E6 k) *
          pinnedX TwistTag.E6.tag k β c *
          (rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] * diagramMap TwistTag.E6 k)⁻¹
        = rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] *
            (diagramMap TwistTag.E6 k * pinnedX TwistTag.E6.tag k β c *
              (diagramMap TwistTag.E6 k)⁻¹) *
            (rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1])⁻¹ := by group
      _ = rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] *
            pinnedX TwistTag.E6.tag k β c *
            (rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1])⁻¹ := by rw [hP]
      _ = pinnedX TwistTag.E6.tag k β
            ((rootChar (τ := TwistTag.E6.tag)
              (![1, -1, 1, 1, 1, 1] : Fin TwistTag.E6.tag.rank → kˣ) β : k) * c) :=
          rootDiagUnit_conj_pinnedX _ hβ c
      _ = pinnedX TwistTag.E6.tag k β (-c) := by
          rw [hb]
          simp
  obtain ⟨u, huord, hugood, hinv⟩ :=
    exists_twist_rootPairs_inv_extraGood (τ := TwistTag.E6.tag)
      (hτ := Or.inr (Or.inl (by decide)))
      (Q := diagramMap TwistTag.E6 k) (α := α) (β := β) (γ := γ) (δ := δ) hRP hQ
      (t := rootDiagUnit TwistTag.E6.tag ![1, -1, 1, 1, 1, 1] * diagramMap TwistTag.E6 k) htB
  exact ⟨u, huord, hugood, hinv⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
