module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongExcDatum
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongF4C2
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2HighestRootNormalizer
public import CFSG.LieType.HighestRoot.Defs
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.StandardType.LieKnownR2.Exc

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.HighestRoot CFSG.LieType.TitsSimplicity CFSG.Blueprint.Chevalley
  CFSG.SeitzReduction CFSG.LieType.Chevalley CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped commutatorElement

private theorem l10sxc2_row_E6 (l : Fin (Tag.rank .E6)) :
    ∑ k, (Tag.cartan .E6 l k : ℚ) * (highRoot .E6 k : ℚ) =
      if l = (⟨1, by decide⟩ : Fin (Tag.rank .E6)) then 1 else 0 := by
  fin_cases l <;> decide +kernel

private theorem l10sxc2_coord_E6 :
    ∀ γ ∈ rootFinset .E6, (0 < γ (⟨1, by decide⟩ : Fin (Tag.rank .E6)) ↔
      0 < height γ ∧ γ (⟨1, by decide⟩ : Fin (Tag.rank .E6)) ≠ 0) := by
  decide +kernel

private theorem l10sxc2_perp_E6 (i : Fin (Tag.rank .E6)) :
    i ∈ (thetaPerpF .E6 : Set (Fin Tag.E6.rank)) ↔ i ≠ (⟨1, by decide⟩ : Fin (Tag.rank .E6)) := by
  fin_cases i <;> decide

private theorem l10sxc2_row_E7 (l : Fin (Tag.rank .E7)) :
    ∑ k, (Tag.cartan .E7 l k : ℚ) * (highRoot .E7 k : ℚ) =
      if l = (⟨0, by decide⟩ : Fin (Tag.rank .E7)) then 1 else 0 := by
  fin_cases l <;> decide +kernel

private theorem l10sxc2_row_E8 (l : Fin (Tag.rank .E8)) :
    ∑ k, (Tag.cartan .E8 l k : ℚ) * (highRoot .E8 k : ℚ) =
      if l = (⟨7, by decide⟩ : Fin (Tag.rank .E8)) then 1 else 0 := by
  fin_cases l <;> decide +kernel

private theorem l10sxc2_coord_E7 :
    ∀ γ ∈ rootFinset .E7, (0 < γ (⟨0, by decide⟩ : Fin (Tag.rank .E7)) ↔
      0 < height γ ∧ γ (⟨0, by decide⟩ : Fin (Tag.rank .E7)) ≠ 0) := by
  decide +kernel

private theorem l10sxc2_coord_E8 :
    ∀ γ ∈ rootFinset .E8, (0 < γ (⟨7, by decide⟩ : Fin (Tag.rank .E8)) ↔
      0 < height γ ∧ γ (⟨7, by decide⟩ : Fin (Tag.rank .E8)) ≠ 0) := by
  decide +kernel

private theorem l10sxc2_perp_E7 (i : Fin (Tag.rank .E7)) :
    i ∈ (thetaPerpF .E7 : Set (Fin Tag.E7.rank)) ↔ i ≠ (⟨0, by decide⟩ : Fin (Tag.rank .E7)) := by
  fin_cases i <;> decide

private theorem l10sxc2_perp_E8 (i : Fin (Tag.rank .E8)) :
    i ∈ (thetaPerpF .E8 : Set (Fin Tag.E8.rank)) ↔ i ≠ (⟨7, by decide⟩ : Fin (Tag.rank .E8)) := by
  fin_cases i <;> decide

private theorem l10sxc2_form_highRoot (τ : Tag) (j : Fin τ.rank)
    (hA : TauCeti.IsFiniteType (Tag.cartan τ))
    (hrow : ∀ l : Fin τ.rank, ∑ k, (Tag.cartan τ l k : ℚ) * (highRoot τ k : ℚ) =
      if l = j then 1 else 0)
    (x : Fin τ.rank → ℚ) :
    form hA x (toRat (highRoot τ)) = symmetrizer hA j * x j := by
  calc form hA x (toRat (highRoot τ))
      = form hA (toRat (highRoot τ)) x := form_comm hA x _
    _ = ∑ l, x l * form hA (toRat (highRoot τ)) (Pi.single l 1) := form_eq_sum hA _ _
    _ = x j * form hA (toRat (highRoot τ)) (Pi.single j 1) :=
          Finset.sum_eq_single_of_mem j (Finset.mem_univ j) fun l _ hl => by
            rw [form_single_right]
            simp only [toRat_apply]
            rw [hrow l, if_neg hl, mul_zero, mul_zero]
    _ = symmetrizer hA j * x j := by
          rw [form_single_right]
          simp only [toRat_apply]
          rw [hrow j, if_pos rfl, mul_one]
          ring

private theorem l10sxc2_exists_ne_zero_iff_coord (τ : Tag) (j : Fin τ.rank)
    (hperp : ∀ i : Fin τ.rank, i ∈ (thetaPerpF τ : Set (Fin τ.rank)) ↔ i ≠ j)
    (γ : Fin τ.rank → ℤ) :
    (∃ i ∉ (thetaPerpF τ : Set (Fin τ.rank)), γ i ≠ 0) ↔ γ j ≠ 0 := by
  constructor
  · rintro ⟨i, hi, hne⟩
    have hij : i = j := by
      by_contra hne0
      exact hi ((hperp i).2 hne0)
    subst hij
    exact hne
  · intro h0
    exact ⟨j, fun h => ((hperp j).1 h) rfl, h0⟩

private theorem l10sxc2_mem_parabolicRadicalRoots (τ : Tag) (j : Fin τ.rank)
    (hperp : ∀ i : Fin τ.rank, i ∈ (thetaPerpF τ : Set (Fin τ.rank)) ↔ i ≠ j)
    (γ : Fin τ.rank → ℤ) :
    γ ∈ CFSG.LieType.Chevalley.parabolicRadicalRoots τ
        (thetaPerpF τ : Set (Fin τ.rank)) ↔
      IsRoot τ γ ∧ 0 < height γ ∧ γ j ≠ 0 := by
  rw [CFSG.LieType.Chevalley.mem_parabolicRadicalRoots_iff,
    l10sxc2_exists_ne_zero_iff_coord τ j hperp]

private theorem l10sxc2_map_rootGroup (τ : Tag) (K : Type) [Field K]
    (F : CFSG.LieType.Chevalley.RootOperatorFamily τ)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ((rootGroup F K γ)).map (adjointGroup τ K).subtype =
      CFSG.Blueprint.Chevalley.rootSubgroup τ K γ := by
  rw [rootGroup_of_isRoot (F := F) hγ,
    ← CFSG.LieType.Chevalley.RootOperatorFamily.subgroupOf_rootSubgroup_eq
      (F := F) (K := K) (α := ⟨γ, hγ⟩)]
  exact Subgroup.map_subgroupOf_eq_of_le
    (CFSG.Blueprint.Chevalley.rootSubgroup_le_adjointGroup (τ := τ) (α := γ))

private theorem l10sxc2_map_of
    (τ : Tag) (K : Type) [Field K] (j : Fin τ.rank)
    (hrow : ∀ l : Fin τ.rank, ∑ k, (Tag.cartan τ l k : ℚ) * (highRoot τ k : ℚ) =
      if l = j then 1 else 0)
    (hcoord : ∀ γ ∈ rootFinset τ, (0 < γ j ↔ 0 < height γ ∧ γ j ≠ 0))
    (hperp : ∀ i : Fin τ.rank, i ∈ (thetaPerpF τ : Set (Fin τ.rank)) ↔ i ≠ j) :
    (highestRootRadical (adjDatum (rootOperatorFamily τ) K) (highRoot τ)).map
        (adjointGroup τ K).subtype =
      parabolicRadical τ K (thetaPerpF τ : Set (Fin τ.rank)) ⊓ adjointGroup τ K := by
  let D := adjDatum (rootOperatorFamily τ) K
  let θ := highRoot τ
  let R : Set (Fin τ.rank → ℤ) :=
    CFSG.LieType.Chevalley.parabolicRadicalRoots τ (thetaPerpF τ : Set (Fin τ.rank))
  have hform : ∀ γ : Fin τ.rank → ℤ,
      rootForm D γ θ = (symmetrizer D.isFiniteType j : ℚ) * (γ j : ℚ) := by
    intro γ
    change form D.isFiniteType (toRat γ) (toRat (highRoot τ)) =
      (symmetrizer D.isFiniteType j : ℚ) * (γ j : ℚ)
    rw [l10sxc2_form_highRoot τ j D.isFiniteType hrow (toRat γ), toRat_apply]
  have hsets : {γ : Fin τ.rank → ℤ | γ ∈ D.roots ∧ 0 < rootForm D γ θ} = R := by
    ext γ
    rw [Set.mem_setOf_eq, l10sxc2_mem_parabolicRadicalRoots τ j hperp]
    constructor
    · rintro ⟨hγroot, hpos⟩
      have hγ : IsRoot τ γ := (mem_adjDatum_roots (F := rootOperatorFamily τ)).1 hγroot
      rw [hform γ] at hpos
      have hcoord' : 0 < γ j := by
        have hrat : 0 < (γ j : ℚ) :=
          pos_of_mul_pos_right hpos (symmetrizer_pos D.isFiniteType j).le
        exact_mod_cast hrat
      obtain ⟨h1, h2⟩ := (hcoord γ (mem_rootFinset.2 hγ)).1 hcoord'
      exact ⟨hγ, h1, h2⟩
    · rintro ⟨hγ, hheight, hcoord'⟩
      refine ⟨(mem_adjDatum_roots (F := rootOperatorFamily τ)).2 hγ, ?_⟩
      rw [hform γ]
      have hpos : 0 < γ j := (hcoord γ (mem_rootFinset.2 hγ)).2 ⟨hheight, hcoord'⟩
      exact mul_pos (symmetrizer_pos D.isFiniteType j) (by exact_mod_cast hpos)
  have hmap : ∀ γ ∈ {γ : Fin τ.rank → ℤ | γ ∈ D.roots ∧ 0 < rootForm D γ θ},
      (D.rootGroup γ).map (adjointGroup τ K).subtype =
        CFSG.Blueprint.Chevalley.rootSubgroup τ K γ :=
    fun γ hγ => l10sxc2_map_rootGroup τ K (rootOperatorFamily τ)
      ((mem_adjDatum_roots (F := rootOperatorFamily τ)).1 hγ.1)
  have hle : (⨆ γ ∈ R, CFSG.Blueprint.Chevalley.rootSubgroup τ K γ) ≤
      adjointGroup τ K :=
    iSup₂_le fun γ _ =>
      CFSG.Blueprint.Chevalley.rootSubgroup_le_adjointGroup (τ := τ) (α := γ)
  have hgoal : (highestRootRadical D θ).map (adjointGroup τ K).subtype =
      ⨆ γ ∈ R, CFSG.Blueprint.Chevalley.rootSubgroup τ K γ := by
    calc (highestRootRadical D θ).map (adjointGroup τ K).subtype
        = ⨆ γ ∈ {γ : Fin τ.rank → ℤ | γ ∈ D.roots ∧ 0 < rootForm D γ θ},
            (D.rootGroup γ).map (adjointGroup τ K).subtype := by
            simp only [highestRootRadical, Subgroup.map_iSup]
            rfl
      _ = ⨆ γ ∈ {γ : Fin τ.rank → ℤ | γ ∈ D.roots ∧ 0 < rootForm D γ θ},
            CFSG.Blueprint.Chevalley.rootSubgroup τ K γ := by
            exact iSup_congr fun γ => iSup_congr fun hγ => hmap γ hγ
      _ = ⨆ γ ∈ R, CFSG.Blueprint.Chevalley.rootSubgroup τ K γ := by rw [hsets]
  rw [show CFSG.LieType.Chevalley.parabolicRadical τ K
        (thetaPerpF τ : Set (Fin τ.rank)) =
      (⨆ γ ∈ R, CFSG.Blueprint.Chevalley.rootSubgroup τ K γ) from rfl,
    inf_eq_left.2 hle]
  exact hgoal

private theorem l10sxc2_jθ (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) :
    Jθ τ = (thetaPerpF τ : Set (Fin τ.rank)) := by
  rcases hτ with rfl | rfl | rfl <;>
  · ext i
    simp only [Jθ, thetaPerpF, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
    revert i
    decide +kernel

private theorem l10sxc2_even_highest_root_normalizer
    (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    (K : Type) [Field K] [Finite K] [CharP K 2] :
    Subgroup.normalizer (rootSubgroup τ K (highRoot τ) : Set (ModGL τ K)) ⊓
        adjointGroup τ K = parabolicSubgroup τ K (thetaPerpF τ : Set (Fin τ.rank)) ∧
      pCoreOf 2 (parabolicSubgroup τ K (thetaPerpF τ : Set (Fin τ.rank))) =
        parabolicRadical τ K (thetaPerpF τ : Set (Fin τ.rank)) ⊓ adjointGroup τ K := by
  rw [← l10sxc2_jθ τ hτ]
  exact even_highest_root_normalizer τ K

theorem map_highestRootRadical_adj
    (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : Type) [Field K] :
    (highestRootRadical (adjDatum (rootOperatorFamily τ) K) (highRoot τ)).map
        (adjointGroup τ K).subtype =
      parabolicRadical τ K
        (thetaPerpF τ : Set (Fin τ.rank)) ⊓ adjointGroup τ K := by
  rcases hτ with rfl | rfl | rfl
  · exact l10sxc2_map_of .E6 K ⟨1, by decide⟩ l10sxc2_row_E6 l10sxc2_coord_E6 l10sxc2_perp_E6
  · exact l10sxc2_map_of .E7 K ⟨0, by decide⟩ l10sxc2_row_E7 l10sxc2_coord_E7 l10sxc2_perp_E7
  · exact l10sxc2_map_of .E8 K ⟨7, by decide⟩ l10sxc2_row_E8 l10sxc2_coord_E8 l10sxc2_perp_E8

theorem pCoreOf_normalizer_rootGroup_highRoot_adj
    (τ : Tag) (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (K : Type) [Field K] [Finite K] [CharP K 2] :
    pCoreOf 2 (Subgroup.normalizer (((adjDatum (rootOperatorFamily τ) K).rootGroup (highRoot τ) :
        Subgroup ↥(adjointGroup τ K)) : Set ↥(adjointGroup τ K))) =
      highestRootRadical (adjDatum (rootOperatorFamily τ) K) (highRoot τ) := by
  have hθ : IsRoot τ (highRoot τ) := isRoot_highRoot τ
  have hX : (adjDatum (rootOperatorFamily τ) K).rootGroup (highRoot τ) =
      (CFSG.Blueprint.Chevalley.rootSubgroup τ K (highRoot τ)).subgroupOf
        (adjointGroup τ K) := by
    change rootGroup (rootOperatorFamily τ) K (highRoot τ) =
      (CFSG.Blueprint.Chevalley.rootSubgroup τ K (highRoot τ)).subgroupOf
        (adjointGroup τ K)
    rw [rootGroup_of_isRoot (F := rootOperatorFamily τ) hθ,
      ← CFSG.LieType.Chevalley.RootOperatorFamily.subgroupOf_rootSubgroup_eq
        (F := rootOperatorFamily τ) (K := K) (α := ⟨highRoot τ, hθ⟩)]
  have hH : CFSG.Blueprint.Chevalley.rootSubgroup τ K (highRoot τ) ≤
      adjointGroup τ K :=
    CFSG.Blueprint.Chevalley.rootSubgroup_le_adjointGroup (τ := τ) (α := highRoot τ)
  have hN : Subgroup.normalizer (((adjDatum (rootOperatorFamily τ) K).rootGroup (highRoot τ) :
        Subgroup ↥(adjointGroup τ K)) : Set ↥(adjointGroup τ K)) =
      (CFSG.LieType.Chevalley.parabolicSubgroup τ K
        (thetaPerpF τ : Set (Fin τ.rank))).subgroupOf (adjointGroup τ K) := by
    rw [hX, ← Subgroup.subgroupOf_normalizer_eq hH, Subgroup.subgroupOf_inj,
      (l10sxc2_even_highest_root_normalizer τ hτ K).1,
      inf_eq_left.2 (CFSG.LieType.Chevalley.parabolicSubgroup_le_adjointGroup τ K
        (thetaPerpF τ : Set (Fin τ.rank)))]
  apply Subgroup.map_injective (adjointGroup τ K).subtype_injective
  rw [hN]
  rw [CFSG.StandardType.LieKnownR2.Short.map_subtype_pCoreOf_subgroupOf (adjointGroup τ K)
    (CFSG.LieType.Chevalley.parabolicSubgroup τ K (thetaPerpF τ : Set (Fin τ.rank)))
    (CFSG.LieType.Chevalley.parabolicSubgroup_le_adjointGroup τ K
      (thetaPerpF τ : Set (Fin τ.rank)))]
  rw [(l10sxc2_even_highest_root_normalizer τ hτ K).2,
    (map_highestRootRadical_adj τ hτ K).symm]

end CFSG.StandardType.LieKnownR2.Exc
