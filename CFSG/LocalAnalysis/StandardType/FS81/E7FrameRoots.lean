module

public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.ClassicalInvolution.ModelFacts.E7ModelWeyl
public import CFSG.ClassicalInvolution.Models.LinearPairs.Pairs
public import CFSG.LocalAnalysis.StandardType.FS81.FrameEm

public noncomputable section

namespace CFSG.StandardType.FrameRoute.FS81.E7FrameRoots

open CFSG.ClassicalInvolution.WeakCT CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Universal CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Levi
open CFSG.LieType.Chevalley.RootSpace
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Steinberg.Isogeny
open scoped MatrixGroups

@[expose] def starTwoRoot : Fin (Tag.rank .E7) → ℤ := ![-1, -1, -2, -2, -1, 0, 0]

@[expose] def sixStarRoot : Fin (Tag.rank .E7) → ℤ := ![-1, -2, -2, -4, -3, -2, -1]

theorem mem_rootFinset_sixStarRoot : sixStarRoot ∈ rootFinset .E7 := by
  decide +kernel

theorem mem_rootFinset_starTwoRoot : starTwoRoot ∈ rootFinset .E7 := by
  decide +kernel

theorem corrected_auxiliary_root_pairings :
    (∀ i : Fin (Tag.rank .E7), iform (τ := .E7) sixStarRoot (Pi.single i 1) =
      (![0, 0, 1, -1, 0, 0, 0] : Fin (Tag.rank .E7) → ℤ) i) ∧
      iform (τ := .E7) sixStarRoot starTwoRoot = 0 ∧
      iform (τ := .E7) sixStarRoot
        (![2, 2, 3, 4, 3, 2, 1] : Fin (Tag.rank .E7) → ℤ) = -1 := by
  constructor
  · intro i
    fin_cases i <;> decide +kernel
  · constructor <;> decide +kernel

theorem isRoot_starTwoRoot : IsRoot .E7 starTwoRoot :=
  mem_rootFinset.mp mem_rootFinset_starTwoRoot

theorem native_linearPair_of_roots (F : Type) [Field F] [Finite F]
    {α β : Fin (Tag.rank .E7) → ℤ} (hα : IsRoot .E7 α) (hβ : IsRoot .E7 β)
    (h : iform α β = 1 ∨ iform α β = -1) :
    ∃ W : Subgroup (ModGL .E7 F), LinearBlockStandardPair F W
      (rootRankOneGroup .E7 F α) (rootRankOneGroup .E7 F β) := by
  obtain ⟨W, hW⟩ := CFSG.ClassicalInvolution.ModelFacts.E7Model.linearPair_of_roots F hα hβ h
  have hmap := CFSG.ClassicalInvolution.RouteD.linearBlockStandardPair_map_central hW
    (CFSG.ClassicalInvolution.ModelFacts.E7Model.εm F)
    CFSG.ClassicalInvolution.ModelFacts.E7Model.εm_ker_le_center
  rw [CFSG.ClassicalInvolution.ModelFacts.E7Model.map_stdRankOne_εm hα,
    CFSG.ClassicalInvolution.ModelFacts.E7Model.map_stdRankOne_εm hβ] at hmap
  exact ⟨_, hmap⟩

theorem map_rootGroup_epsilon (F : Type) [Field F] [Finite F]
    {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) :
    ((e7Datum F).rootGroup γ).map (CFSG.ClassicalInvolution.ModelFacts.E7Model.εm F) =
      rootSubgroup .E7 F γ := by
  change (e7Data_valid.rootGroup F γ).map
    ((adjointGroup .E7 F).subtype.comp (e7Isogeny F)) = _
  rw [← Subgroup.map_map, map_e7Isogeny_rootGroup F hγ]
  rw [CFSG.LieType.Steinberg.Adjoint.rootGroup_of_isRoot hγ,
    ← RootOperatorFamily.subgroupOf_rootSubgroup_eq (rootOperatorFamily .E7) F ⟨γ, hγ⟩,
    Subgroup.map_subgroupOf_eq_of_le (rootSubgroup_le_adjointGroup γ)]

theorem exists_conj_rootSubgroup_wordAct (F : Type) [Field F] [Finite F] (ω : List ℕ) :
    ∃ m ∈ adjointGroup .E7 F, ∀ γ : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 γ →
      (rootSubgroup .E7 F γ).map (MulAut.conj m).toMonoidHom =
        rootSubgroup .E7 F (CFSG.ClassicalInvolution.ModelFacts.E7Model.wordAct ω γ) := by
  obtain ⟨k, hk⟩ := CFSG.ClassicalInvolution.ModelFacts.E7Model.exists_conj_rootGroup_wordAct F ω
  refine ⟨CFSG.ClassicalInvolution.ModelFacts.E7Model.εm F k,
    CFSG.ClassicalInvolution.ModelFacts.E7Model.εm_mem k, ?_⟩
  intro γ hγ
  have h := hk γ hγ
  change CFSG.ClassicalInvolution.Generic.conjSub k ((e7Datum F).rootGroup γ) =
    (e7Datum F).rootGroup (CFSG.ClassicalInvolution.ModelFacts.E7Model.wordAct ω γ) at h
  have hm := congrArg (fun U => U.map (CFSG.ClassicalInvolution.ModelFacts.E7Model.εm F)) h
  rw [CFSG.ClassicalInvolution.ModelFacts.E7Model.map_conjSub, map_rootGroup_epsilon F hγ,
    map_rootGroup_epsilon F (CFSG.ClassicalInvolution.ModelFacts.E7Model.isRoot_wordAct ω hγ)] at hm
  exact hm

end CFSG.StandardType.FrameRoute.FS81.E7FrameRoots
