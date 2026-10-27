module

public import CFSG.LieType.AlgebraicGroups.RootWordBruhatCover
public import CFSG.LieType.AlgebraicGroups.ToralRootCoverWords
public import CFSG.LieType.AlgebraicGroups.ConstructibleSubgroupGL
public import CFSG.LieType.Chevalley.StandardParabolicCells
public import CFSG.LieType.Chevalley.ParabolicRadicalLevi
public import CFSG.LieType.Chevalley.ParabolicRadicalLeviRoots
import CFSG.LieType.AlgebraicGroups.ConvolutionPoints

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.D4RC

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups WithConv

open scoped CFSG.ConvolutionPoints

variable {τ : Tag} {K : Type} [Field K]


@[expose] def rcpParabolicRoots (τ : Tag) (J : Set (Fin τ.rank)) : Set (Fin τ.rank → ℤ) :=
  {γ | IsRoot τ γ ∧ (0 < height γ ∨ ∀ i, i ∉ J → γ i = 0)}

theorem rcp_rootSubgroup_smul_le {M : Subgroup (ModGL τ K)} {w : WeylGroup τ}
    (hw : canonicalRep (coxeterSystem τ) K w ∈ M) {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ)
    (hδM : rootSubgroup τ K δ ≤ M) : rootSubgroup τ K (w • δ) ≤ M := by
  rw [← (canonical_weyl_root_transport τ K).2.1 w δ hδ]
  rintro _ ⟨x, hx, rfl⟩
  exact mul_mem (mul_mem hw (hδM hx)) (inv_mem hw)

theorem rcp_rootSubgroup_le_parabolicLevi {J : Set (Fin τ.rank)} {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ parabolicRoots τ J) : rootSubgroup τ K γ ≤ parabolicLevi τ K J := by
  have hsingle : ∀ j ∈ J, rootSubgroup τ K (Pi.single j 1) ≤ parabolicLevi τ K J := fun j hj =>
    (Subgroup.closure_le _).2 (by
      rintro _ ⟨c, rfl⟩
      rw [pinnedX_single]
      exact xUnit_mem_parabolicLevi hj c)
  have hnegsingle : ∀ j ∈ J, rootSubgroup τ K (-Pi.single j 1) ≤ parabolicLevi τ K J :=
    fun j hj => (Subgroup.closure_le _).2 (by
      rintro _ ⟨c, rfl⟩
      rw [pinnedX_neg_single]
      exact yUnit_mem_parabolicLevi hj c)
  rcases IsRoot.height_pos_or_neg hγ.1 with hpos | hneg
  · obtain ⟨w, hw, j, hj, hwj⟩ := exists_mem_parabolicWeylGroup_smul _ γ rfl ⟨hγ, hγ.1, hpos⟩
    rw [← hwj]
    exact rcp_rootSubgroup_smul_le (canonicalRep_mem_parabolicLevi hw) (isRoot_single τ j)
      (hsingle j hj)
  · have hneg' : -γ ∈ parabolicPosRoots τ J :=
      ⟨⟨IsRoot.neg hγ.1, fun i hi => by rw [Pi.neg_apply, hγ.2 i hi, neg_zero]⟩,
        IsRoot.neg hγ.1, by rw [height_neg]; omega⟩
    obtain ⟨w, hw, j, hj, hwj⟩ := exists_mem_parabolicWeylGroup_smul _ (-γ) rfl hneg'
    have e : γ = w • (-Pi.single j 1 : Fin τ.rank → ℤ) := by rw [smul_neg, hwj, neg_neg]
    rw [e]
    exact rcp_rootSubgroup_smul_le (canonicalRep_mem_parabolicLevi hw) (isRoot_neg_single τ j)
      (hnegsingle j hj)

theorem rcp_parabolicLevi_le (J : Set (Fin τ.rank)) :
    parabolicLevi τ K J ≤ torusGroup τ K ⊔ rootSpan τ K (parabolicRoots τ J) := by
  refine sup_le le_sup_left (le_sup_of_le_right ((Subgroup.closure_le _).2 ?_))
  rintro _ ⟨j, hj, c, rfl | rfl⟩
  · have hmem : (Pi.single j 1 : Fin τ.rank → ℤ) ∈ parabolicRoots τ J :=
      ⟨isRoot_single τ j, fun i hi =>
        Pi.single_eq_of_ne (show i ≠ j from fun h => hi (h ▸ hj)) _⟩
    exact le_iSup₂_of_le (f := fun δ (_ : δ ∈ parabolicRoots τ J) => rootSubgroup τ K δ) _ hmem
      le_rfl (xUnit_mem_rootSubgroup j c)
  · have hmem : (-Pi.single j 1 : Fin τ.rank → ℤ) ∈ parabolicRoots τ J :=
      ⟨isRoot_neg_single τ j, fun i hi => by
        rw [Pi.neg_apply, Pi.single_eq_of_ne (show i ≠ j from fun h => hi (h ▸ hj)), neg_zero]⟩
    exact le_iSup₂_of_le (f := fun δ (_ : δ ∈ parabolicRoots τ J) => rootSubgroup τ K δ) _ hmem
      le_rfl (yUnit_mem_rootSubgroup j c)

theorem rcp_parabolicSubgroup_eq (J : Set (Fin τ.rank)) :
    parabolicSubgroup τ K J = torusGroup τ K ⊔ rootSpan τ K (rcpParabolicRoots τ J) := by
  have hpar : parabolicRoots τ J ⊆ rcpParabolicRoots τ J := fun γ hγ => ⟨hγ.1, Or.inr hγ.2⟩
  have hrs : rootSpan τ K (parabolicRoots τ J) ≤ rootSpan τ K (rcpParabolicRoots τ J) :=
    iSup₂_le fun γ hγ => le_iSup₂_of_le γ (hpar hγ) le_rfl
  apply le_antisymm
  · refine sup_le (sup_le le_sup_left ?_) ((Subgroup.closure_le _).2 ?_)
    · exact le_sup_of_le_right (iSup₂_le fun γ hγ =>
        le_iSup₂_of_le γ ⟨hγ.1, Or.inl hγ.2⟩ le_rfl)
    · rintro _ ⟨j, hj, rfl⟩
      have := rcp_parabolicLevi_le (K := K) J (weylElt_mem_parabolicLevi (K := K) hj)
      exact (sup_le_sup_left hrs _) this
  · refine sup_le (torusGroup_le_parabolicSubgroup J) (iSup₂_le fun γ hγ => ?_)
    rcases hγ.2 with hpos | hJ
    · exact (le_iSup₂_of_le γ ⟨hγ.1, hpos⟩ le_rfl).trans (posUnipotent_le_parabolicSubgroup J)
    · exact (rcp_rootSubgroup_le_parabolicLevi ⟨hγ.1, hJ⟩).trans
        (parabolicLevi_le_parabolicSubgroup J)

section Connected

variable [IsAlgClosed K]

theorem rcp_isPointIrreducible_parabolic (J : Set (Fin τ.rank)) :
    IsPointIrreducible K (transportPoints (modGLPoint τ K)
      ((parabolicSubgroup τ K J : Subgroup (ModGL τ K)) : Set (ModGL τ K))) := by
  rw [rcp_parabolicSubgroup_eq]
  exact isPointIrreducible_torusGroup_sup_rootSpan fun γ hγ => hγ.1

theorem rcp_isPointConstructible_parabolic (J : Set (Fin τ.rank)) :
    IsPointConstructible K (transportPoints (modGLPoint τ K)
      ((parabolicSubgroup τ K J : Subgroup (ModGL τ K)) : Set (ModGL τ K))) := by
  classical
  obtain ⟨N₀, α₀, hα₀, hα₀r⟩ := exists_enum (finite_posRoots τ)
  choose m₀ β₀ hβ₀ hβ₀r using fun w : WeylGroup τ => exists_enum (inversionSet_finite w)
  have hfin : Finite ↥(parabolicWeylGroup τ J) := (parabolic_Weyl_coordinate_stabilizer τ J).2.2.1
  have hcells := (standard_parabolic_cells τ K).1 J
  have h := isPointConstructible_iUnion_range (k := K) (J := ↥(parabolicWeylGroup τ J))
    (fun w => TorusAffine K τ.rank (N₀ + m₀ (w : WeylGroup τ)))
    (fun w => bruhatCo τ K (w : WeylGroup τ) α₀ (β₀ w))
  convert h using 1
  ext y
  simp only [Set.mem_iUnion, Set.mem_range]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, ← SetLike.mem_coe, hcells] at hg
    obtain ⟨w, hw, hgw⟩ := Set.mem_iUnion₂.1 hg
    rw [← range_bruhatCo w α₀ hα₀ hα₀r (β₀ w) (hβ₀ w) (hβ₀r w)] at hgw
    obtain ⟨z, hz⟩ := hgw
    exact ⟨⟨w, hw⟩, z, eq_ofConv_of_symm_eq hz⟩
  · rintro ⟨⟨w, hw⟩, z, rfl⟩
    refine ⟨(modGLPoint τ K).symm (toConv (z.comp (bruhatCo τ K w α₀ (β₀ w)))), ?_, ?_⟩
    · rw [SetLike.mem_coe, ← SetLike.mem_coe, hcells]
      refine Set.mem_iUnion₂.2 ⟨w, hw, ?_⟩
      rw [← range_bruhatCo w α₀ hα₀ hα₀r (β₀ w) (hβ₀ w) (hβ₀r w)]
      exact ⟨z, rfl⟩
    · simp only [MulEquiv.apply_symm_apply, ofConv_toConv]

theorem rcp_isConnectedAlgebraicSubgroup_parabolic (J : Set (Fin τ.rank)) :
    IsConnectedAlgebraicSubgroup K
      ((parabolicSubgroup τ K J).map (modGLPoint τ K).toMonoidHom) :=
  (isConnectedAlgebraicSubgroup_map (modGLPoint τ K) (parabolicSubgroup τ K J)
    (rcp_isPointConstructible_parabolic J) (rcp_isPointIrreducible_parabolic J)).2.1

end Connected

end CFSG.RankThree.PartOne.D4RC
