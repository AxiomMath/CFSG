module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2HighestRootNormalizer
public import CFSG.LieType.HighestRoot.Defs
public import CFSG.LieType.Steinberg.Adjoint.Presentation
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.HighestRoot CFSG.Blueprint.Chevalley
  CFSG.SeitzReduction
open scoped commutatorElement

private abbrev zeroF4 : Fin (Tag.rank .F4) := ⟨0, by decide⟩

private theorem subtype_comp_subgroupOf {G : Type} [Group G] (G' H : Subgroup G) (hH : H ≤ G') :
    G'.subtype.comp (H.subgroupOf G').subtype =
      H.subtype.comp (Subgroup.subgroupOfEquivOfLe hH).toMonoidHom := by
  ext x
  rfl

theorem map_subtype_pCoreOf_subgroupOf {G : Type} [Group G] (G' H : Subgroup G) (hH : H ≤ G') :
    (pCoreOf 2 (H.subgroupOf G')).map G'.subtype = pCoreOf 2 H := by
  simp only [pCoreOf]
  rw [Subgroup.map_map, subtype_comp_subgroupOf G' H hH, ← Subgroup.map_map,
    CFSG.LieType.BorelTits.map_pCore_mulEquiv (r := 2) (e := Subgroup.subgroupOfEquivOfLe hH)]

private theorem cartan_mul_highRoot_F4_rat (l : Fin (Tag.rank .F4)) :
    ∑ k, (Tag.cartan .F4 l k : ℚ) * (highRoot .F4 k : ℚ) =
      if l = zeroF4 then 1 else 0 := by
  fin_cases l <;> decide +kernel

private theorem form_highRoot_F4 (hA : TauCeti.IsFiniteType (Tag.cartan .F4))
    (x : Fin (Tag.rank .F4) → ℚ) :
    form hA x (toRat (highRoot .F4)) = symmetrizer hA zeroF4 * x zeroF4 := by
  calc form hA x (toRat (highRoot .F4))
      = form hA (toRat (highRoot .F4)) x := form_comm hA x _
    _ = ∑ l, x l * form hA (toRat (highRoot .F4)) (Pi.single l 1) := form_eq_sum hA _ _
    _ = x zeroF4 * form hA (toRat (highRoot .F4)) (Pi.single zeroF4 1) :=
          Finset.sum_eq_single_of_mem zeroF4 (Finset.mem_univ zeroF4) fun l _ hl => by
            rw [form_single_right]
            simp only [toRat_apply]
            rw [cartan_mul_highRoot_F4_rat, if_neg hl, mul_zero, mul_zero]
    _ = symmetrizer hA zeroF4 * x zeroF4 := by
          rw [form_single_right]
          simp only [toRat_apply]
          rw [cartan_mul_highRoot_F4_rat, if_pos rfl, mul_one]
          ring

private theorem F4_coord0_iff :
    ∀ γ ∈ rootFinset .F4, (0 < γ zeroF4 ↔ 0 < height γ ∧ γ zeroF4 ≠ 0) := by
  decide +kernel

private theorem mem_thetaPerpF_F4 {i : Fin (Tag.rank .F4)} :
    i ∈ (thetaPerpF .F4 : Set (Fin Tag.F4.rank)) ↔ i ≠ zeroF4 := by
  fin_cases i <;> decide

private theorem exists_ne_zero_iff_coord0_F4 (γ : Fin (Tag.rank .F4) → ℤ) :
    (∃ i ∉ (thetaPerpF .F4 : Set (Fin Tag.F4.rank)), γ i ≠ 0) ↔ γ zeroF4 ≠ 0 := by
  constructor
  · rintro ⟨i, hi, hne⟩
    have hi0 : i = zeroF4 := by
      by_contra hne0
      exact hi (mem_thetaPerpF_F4.2 hne0)
    subst hi0
    exact hne
  · intro h0
    exact ⟨zeroF4, fun h => (mem_thetaPerpF_F4.mp h) rfl, h0⟩

private theorem mem_parabolicRadicalRoots_F4 (γ : Fin (Tag.rank .F4) → ℤ) :
    γ ∈ CFSG.LieType.Chevalley.parabolicRadicalRoots .F4
        (thetaPerpF .F4 : Set (Fin Tag.F4.rank)) ↔
      IsRoot .F4 γ ∧ 0 < height γ ∧ γ zeroF4 ≠ 0 := by
  rw [CFSG.LieType.Chevalley.mem_parabolicRadicalRoots_iff, exists_ne_zero_iff_coord0_F4]

private theorem map_rootGroup_F4 (K : Type) [Field K]
    (F : CFSG.LieType.Chevalley.RootOperatorFamily .F4)
    {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) :
    ((rootGroup F K γ)).map (adjointGroup .F4 K).subtype =
      CFSG.Blueprint.Chevalley.rootSubgroup .F4 K γ := by
  rw [rootGroup_of_isRoot (F := F) hγ,
    ← CFSG.LieType.Chevalley.RootOperatorFamily.subgroupOf_rootSubgroup_eq
      (F := F) (K := K) (α := ⟨γ, hγ⟩)]
  exact Subgroup.map_subgroupOf_eq_of_le
    (CFSG.Blueprint.Chevalley.rootSubgroup_le_adjointGroup (τ := .F4) (α := γ))

theorem map_highestRootRadical_F4
    (K : Type) [Field K]
    :
    (highestRootRadical (f4Datum K) (highRoot .F4)).map (adjointGroup .F4 K).subtype =
      CFSG.LieType.Chevalley.parabolicRadical .F4 K
        (thetaPerpF .F4 : Set (Fin Tag.F4.rank)) ⊓ adjointGroup .F4 K := by
  let D := f4Datum K
  let θ := highRoot .F4
  let R : Set (Fin (Tag.rank .F4) → ℤ) :=
    CFSG.LieType.Chevalley.parabolicRadicalRoots .F4 (thetaPerpF .F4 : Set (Fin Tag.F4.rank))
  have hform : ∀ γ : Fin (Tag.rank .F4) → ℤ,
      rootForm D γ θ = (symmetrizer D.isFiniteType zeroF4 : ℚ) * (γ zeroF4 : ℚ) := by
    intro γ
    change form D.isFiniteType (toRat γ) (toRat (highRoot .F4)) =
      (symmetrizer D.isFiniteType zeroF4 : ℚ) * (γ zeroF4 : ℚ)
    rw [form_highRoot_F4 D.isFiniteType (toRat γ), toRat_apply]
  have hsets : {γ : Fin (Tag.rank .F4) → ℤ | γ ∈ D.roots ∧ 0 < rootForm D γ θ} = R := by
    ext γ
    rw [Set.mem_setOf_eq, mem_parabolicRadicalRoots_F4]
    constructor
    · rintro ⟨hγroot, hpos⟩
      have hγ : IsRoot .F4 γ := mem_adjDatum_roots.1 hγroot
      rw [hform γ] at hpos
      have hcoord : 0 < γ zeroF4 := by
        have hrat : 0 < (γ zeroF4 : ℚ) :=
          pos_of_mul_pos_right hpos (symmetrizer_pos D.isFiniteType zeroF4).le
        exact_mod_cast hrat
      obtain ⟨h1, h2⟩ := (F4_coord0_iff γ (mem_rootFinset.2 hγ)).1 hcoord
      exact ⟨hγ, h1, h2⟩
    · rintro ⟨hγ, hheight, hcoord⟩
      refine ⟨mem_adjDatum_roots.2 hγ, ?_⟩
      rw [hform γ]
      have hcoord' : 0 < γ zeroF4 :=
        (F4_coord0_iff γ (mem_rootFinset.2 hγ)).2 ⟨hheight, hcoord⟩
      exact mul_pos (symmetrizer_pos D.isFiniteType zeroF4) (by exact_mod_cast hcoord')
  have hmap : ∀ γ ∈ {γ : Fin (Tag.rank .F4) → ℤ | γ ∈ D.roots ∧ 0 < rootForm D γ θ},
      (D.rootGroup γ).map (adjointGroup .F4 K).subtype =
        CFSG.Blueprint.Chevalley.rootSubgroup .F4 K γ :=
    fun γ hγ => map_rootGroup_F4 K (CFSG.LieType.Chevalley.rootOperatorFamily .F4)
      (mem_adjDatum_roots.1 hγ.1)
  have hle : (⨆ γ ∈ R, CFSG.Blueprint.Chevalley.rootSubgroup .F4 K γ) ≤
      adjointGroup .F4 K :=
    iSup₂_le fun γ _ =>
      CFSG.Blueprint.Chevalley.rootSubgroup_le_adjointGroup (τ := .F4) (α := γ)
  have hgoal : (highestRootRadical D θ).map (adjointGroup .F4 K).subtype =
      ⨆ γ ∈ R, CFSG.Blueprint.Chevalley.rootSubgroup .F4 K γ := by
    calc (highestRootRadical D θ).map (adjointGroup .F4 K).subtype
        = ⨆ γ ∈ {γ : Fin (Tag.rank .F4) → ℤ | γ ∈ D.roots ∧ 0 < rootForm D γ θ},
            (D.rootGroup γ).map (adjointGroup .F4 K).subtype := by
            simp only [highestRootRadical, Subgroup.map_iSup]
            rfl
      _ = ⨆ γ ∈ {γ : Fin (Tag.rank .F4) → ℤ | γ ∈ D.roots ∧ 0 < rootForm D γ θ},
            CFSG.Blueprint.Chevalley.rootSubgroup .F4 K γ := by
            exact iSup_congr fun γ => iSup_congr fun hγ => hmap γ hγ
      _ = ⨆ γ ∈ R, CFSG.Blueprint.Chevalley.rootSubgroup .F4 K γ := by rw [hsets]
  rw [show CFSG.LieType.Chevalley.parabolicRadical .F4 K
        (thetaPerpF .F4 : Set (Fin Tag.F4.rank)) =
      (⨆ γ ∈ R, CFSG.Blueprint.Chevalley.rootSubgroup .F4 K γ) from rfl,
    inf_eq_left.2 hle]
  exact hgoal

theorem pCoreOf_normalizer_rootGroup_highRoot_F4
    (K : Type) [Field K] [Finite K] [CharP K 2] :
    pCoreOf 2 (Subgroup.normalizer (((f4Datum K).rootGroup (highRoot .F4) :
        Subgroup ↥(adjointGroup .F4 K)) : Set ↥(adjointGroup .F4 K))) =
      highestRootRadical (f4Datum K) (highRoot .F4) := by
  have hθ : IsRoot .F4 (highRoot .F4) := isRoot_highRoot .F4
  have hX : (f4Datum K).rootGroup (highRoot .F4) =
      (CFSG.Blueprint.Chevalley.rootSubgroup .F4 K (highRoot .F4)).subgroupOf
        (adjointGroup .F4 K) := by
    change rootGroup (CFSG.LieType.Chevalley.rootOperatorFamily .F4) K (highRoot .F4) =
      (CFSG.Blueprint.Chevalley.rootSubgroup .F4 K (highRoot .F4)).subgroupOf
        (adjointGroup .F4 K)
    rw [rootGroup_of_isRoot (F := CFSG.LieType.Chevalley.rootOperatorFamily .F4) hθ,
      ← CFSG.LieType.Chevalley.RootOperatorFamily.subgroupOf_rootSubgroup_eq
        (F := CFSG.LieType.Chevalley.rootOperatorFamily .F4) (K := K)
        (α := ⟨highRoot .F4, hθ⟩)]
  have hH : CFSG.Blueprint.Chevalley.rootSubgroup .F4 K (highRoot .F4) ≤
      adjointGroup .F4 K :=
    CFSG.Blueprint.Chevalley.rootSubgroup_le_adjointGroup (τ := .F4) (α := highRoot .F4)
  have hN : Subgroup.normalizer (((f4Datum K).rootGroup (highRoot .F4) :
        Subgroup ↥(adjointGroup .F4 K)) : Set ↥(adjointGroup .F4 K)) =
      (CFSG.LieType.Chevalley.parabolicSubgroup .F4 K
        (thetaPerpF .F4 : Set (Fin Tag.F4.rank))).subgroupOf (adjointGroup .F4 K) := by
    rw [hX, ← Subgroup.subgroupOf_normalizer_eq hH, Subgroup.subgroupOf_inj,
      (even_exc_highest_root_normalizer .F4 (Or.inr (Or.inr rfl)) K).1,
      inf_eq_left.2 (CFSG.LieType.Chevalley.parabolicSubgroup_le_adjointGroup .F4 K
        (thetaPerpF .F4 : Set (Fin Tag.F4.rank)))]
  apply Subgroup.map_injective (adjointGroup .F4 K).subtype_injective
  rw [hN]
  rw [map_subtype_pCoreOf_subgroupOf (adjointGroup .F4 K)
    (CFSG.LieType.Chevalley.parabolicSubgroup .F4 K (thetaPerpF .F4 : Set (Fin Tag.F4.rank)))
    (CFSG.LieType.Chevalley.parabolicSubgroup_le_adjointGroup .F4 K
      (thetaPerpF .F4 : Set (Fin Tag.F4.rank)))]
  rw [(even_exc_highest_root_normalizer .F4 (Or.inr (Or.inr rfl)) K).2,
    (map_highestRootRadical_F4 K).symm]

end CFSG.StandardType.LieKnownR2.Short
