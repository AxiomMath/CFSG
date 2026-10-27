module

public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagCartan
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticEndNode
public import CFSG.LocalAnalysis.StandardType.MarkingChevalley
public import CFSG.LieType.Chevalley.AdjointCenter

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley

namespace TableBF4

variable (K : Type) [Field K]

abbrev RecipeGroup : Type :=
  LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanF4 K false)

abbrev RecipeID : Set (MulAut (RecipeGroup K)) :=
  LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenChevH LargeEvenCartanF4 K false)


@[expose] noncomputable def recipeEquiv [Finite K] : RecipeGroup K ≃* adjointGroup .F4 K :=
  (Classical.choice (centerQuot_chevGroup_equiv K .F4)).trans
    ((QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .F4) (K := K))).trans
      QuotientGroup.quotientBot)

theorem center_recipeGroup_eq_bot [Finite K] : Subgroup.center (RecipeGroup K) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : recipeEquiv K x ∈ Subgroup.center (adjointGroup .F4 K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := (recipeEquiv K).surjective g
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hx) y]
  rw [CFSG.LieType.Chevalley.center_adjointGroup_eq_bot, Subgroup.mem_bot] at hx'
  rw [Subgroup.mem_bot, ← (recipeEquiv K).map_eq_one_iff]
  exact hx'

theorem idImage_subset_inn :
    RecipeID K ⊆ Set.range (MulAut.conj : RecipeGroup K →* MulAut (RecipeGroup K)) := by
  have hT := TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K TableB.cartanF4_inv
    fun s => ⟨s, pow_one s⟩
  have hdiag : LargeEvenChevDiagImage LargeEvenCartanF4 K
      (LargeEvenChevH LargeEvenCartanF4 K false) ⊆
      (MulAut.conj : RecipeGroup K →* MulAut (RecipeGroup K)).range := by
    intro φ hφ
    obtain ⟨a, ha⟩ := TableB.exists_isDiagOf hφ
    have hmem : TableB.diagHom LargeEvenCartanF4 K a ∈ LargeEvenChevH LargeEvenCartanF4 K false :=
      TableB.diagHom_mem_of_mem_torusSubgroup .F4 K (hT ▸ Subgroup.mem_top a)
    rw [TableB.isDiagOf_eq_conj ha hmem]
    exact ⟨_, rfl⟩
  have hle : Subgroup.closure (LargeEvenInnSet (RecipeGroup K) ∪
      LargeEvenChevDiagImage LargeEvenCartanF4 K (LargeEvenChevH LargeEvenCartanF4 K false)) ≤
      (MulAut.conj : RecipeGroup K →* MulAut (RecipeGroup K)).range := by
    rw [Subgroup.closure_le]
    refine Set.union_subset ?_ hdiag
    rintro _ ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  intro φ hφ
  exact hle hφ

end TableBF4

namespace TableBF4

variable {p r : ℕ} {R R' : Type} [Group R] [Group R']

theorem ggTorusLift_of_mulEquiv (e : R ≃* R') (h : GGTorusLift p r R') : GGTorusLift p r R := by
  intro L' _ _ ψ hψ hker hperf
  have hk : (e.toMonoidHom.comp ψ).ker = ψ.ker := by
    ext l
    simp [MonoidHom.mem_ker]
  obtain ⟨U, E, hU, hU2, hEU, hE, hEc, hEk⟩ :=
    h L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ) (by rw [hk]; exact hker) hperf
  exact ⟨U, E, hU, hU2, hEU, hE, hEc, by rwa [hk] at hEk⟩

theorem ggEndNodeElt_of_mulEquiv (e : R ≃* R') (h : GGEndNodeElt p r R') :
    GGEndNodeElt p r R := by
  intro A hA hr h3
  have hcard : Nat.card (A.map e.toMonoidHom) = Nat.card A :=
    (Nat.card_congr (A.equivMapOfInjective _ e.injective).toEquiv).symm
  obtain ⟨t', ⟨t, htA, rfl⟩, ht1, hcomp, hcent⟩ :=
    h (A.map e.toMonoidHom) (TableB.isElemAbelian_map hA _) (hcard ▸ hr) (hcard ▸ h3)
  have hC : Subgroup.centralizer ({e.toMonoidHom t} : Set R') =
      (Subgroup.centralizer ({t} : Set R)).map e.toMonoidHom :=
    (TableBSymp.map_centralizer_singleton e t).symm
  have hL : LargeEvenLayer (Subgroup.centralizer ({e.toMonoidHom t} : Set R')) =
      (LargeEvenLayer (Subgroup.centralizer ({t} : Set R))).map e.toMonoidHom := by
    rw [hC, largeEvenLayer_map_of_injective _ e.injective]
  refine ⟨t, htA, fun h1 => ht1 (by rw [h1, map_one]), ?_, fun s hs => ?_⟩
  · rw [hL, hC] at hcomp
    have h1 := (isComponentOf_comap_of_injective e.toMonoidHom e.injective hcomp).1
    rwa [Subgroup.comap_map_eq_self_of_injective e.injective] at h1
  · have h1 := hcent (e.toMonoidHom s) ⟨s, hs, rfl⟩
    rw [hL] at h1
    constructor
    · intro hj
      have h2 : ∀ j ∈ (LargeEvenLayer (Subgroup.centralizer ({t} : Set R))).map e.toMonoidHom,
          e.toMonoidHom s * j = j * e.toMonoidHom s := by
        rintro _ ⟨j, hj', rfl⟩
        rw [← map_mul, ← map_mul, hj j hj']
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (h1.mp h2)
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, e.injective ?_⟩
      rw [map_zpow]
      exact hk
    · intro hmem j hj
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have h2 := h1.mpr (Subgroup.mem_zpowers_iff.mpr ⟨k, by rw [map_zpow]⟩) (e.toMonoidHom j)
        ⟨j, hj, rfl⟩
      apply e.injective
      rw [map_mul, map_mul]
      exact h2

end TableBF4

end CFSG.StandardType
