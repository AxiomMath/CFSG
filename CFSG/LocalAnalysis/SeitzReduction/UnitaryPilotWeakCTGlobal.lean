module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotWeakCT
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotGenTwoWindows
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
import CFSG.LocalAnalysis.EvenSmallLie.SympSix.Child3SelL39Out

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear blockSpecialLinear_mono consecutiveBlock
  mem_consecutiveBlock)
open scoped MatrixGroups

section Consecutive

theorem subgroupOf_iSup_of_le {M : Type*} [Group M] {ι : Sort*} {A : ι → Subgroup M}
    {B : Subgroup M} (hA : ∀ j, A j ≤ B) :
    (⨆ j, A j).subgroupOf B = ⨆ j, (A j).subgroupOf B := by
  apply map_injective B.subtype_injective
  rw [subgroupOf_map_subtype, Subgroup.map_iSup, inf_eq_left.2 (iSup_le hA)]
  exact iSup_congr fun j => by rw [subgroupOf_map_subtype, inf_eq_left.2 (hA j)]

theorem blockSpecialLinear_consecutiveBlock_eq_iSup {F : Type} [Field F] {M i r : ℕ}
    (hir : i + (r + 1) ≤ M) :
    blockSpecialLinear (K := F) (consecutiveBlock M i (r + 1)) =
      ⨆ j : Fin r, blockSpecialLinear (K := F) (consecutiveBlock M (i + j) 2) := by
  rw [← LinearPilot.range_blockSL_eq hir, MonoidHom.range_eq_map,
    ← CFSG.ClassicalInvolution.WeakCT.iSup_range_blockSL2 (K := F) r, Subgroup.map_iSup]
  refine iSup_congr fun j => ?_
  rw [← MonoidHom.range_comp, CFSG.ClassicalInvolution.WeakCT.blockSL2,
    CFSG.ClassicalInvolution.WeakCT.blockSL_comp, LinearPilot.range_blockSL_eq]

theorem consecutiveBlock_two_subset {M i r : ℕ} (j : Fin r) :
    consecutiveBlock M (i + j) 2 ⊆ consecutiveBlock M i (r + 1) := by
  intro a ha
  rw [mem_consecutiveBlock] at ha ⊢
  have := j.isLt
  omega

theorem consecutiveBlock_two_eq_nodePair {m k : ℕ} (hk : k < m) :
    consecutiveBlock (m + 1) k 2 =
      ({(⟨k, hk⟩ : Fin m).castSucc, (⟨k, hk⟩ : Fin m).succ} : Finset (Fin (m + 1))) :=
  LinearPilot.consecutiveBlock_two ⟨k, hk⟩

end Consecutive

section Join

variable {G : Type*} [Group G] {L : Subgroup G} {m f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {e : L ≃* unitaryPSU h (m + 1)} {t : G} {X : Subgroup G}
  {N : Finset (Fin (m + 1))}

theorem GraphFieldNeighbourParam.pieceCore_consecutiveBlock_eq_iSup [Finite G]
    (P : GraphFieldNeighbourParam e t X N) {i r : ℕ} (hir : i + r ≤ m) (hr : 1 ≤ r)
    (hC : consecutiveBlock (m + 1) i (r + 1) ⊆ N) (hNc : 2 ≤ Nᶜ.card)
    (hX : X ≤ modelToG e (unitaryBlockTorus h (consecutiveBlock (m + 1) i (r + 1)))) :
    pieceCore e (consecutiveBlock (m + 1) i (r + 1)) =
      ⨆ j : Fin r, pieceCore e (consecutiveBlock (m + 1) (i + j) 2) := by
  have hcard2 : ∀ j : Fin r, (consecutiveBlock (m + 1) (i + j) 2).card = 2 := fun j => by
    have hj := j.isLt
    rw [consecutiveBlock_two_eq_nodePair (by omega : i + (j : ℕ) < m)]
    exact LinearPilot.card_nodePair _
  have hpair : ∀ j : Fin r, pieceCore e (consecutiveBlock (m + 1) (i + j) 2) =
      ((blockSpecialLinear (K := K) (consecutiveBlock (m + 1) (i + j) 2)).subgroupOf
        (blockSpecialLinear N)).map P.Φ := fun j =>
    P.pieceCore_eq_map_of_compl ((consecutiveBlock_two_subset j).trans hC) (hcard2 j).ge hNc
      (hX.trans (modelToG_mono e (unitaryBlockTorus_anti h (consecutiveBlock_two_subset j))))
  have hC2 : 2 ≤ (consecutiveBlock (m + 1) i (r + 1)).card := by
    have h0 := hcard2 ⟨0, by omega⟩
    have hsub := consecutiveBlock_two_subset (M := m + 1) (i := i) (⟨0, by omega⟩ : Fin r)
    rw [← h0]
    exact Finset.card_le_card hsub
  rw [P.pieceCore_eq_map_of_compl hC hC2 hNc hX,
    blockSpecialLinear_consecutiveBlock_eq_iSup (by omega),
    subgroupOf_iSup_of_le (fun j => blockSpecialLinear_mono ((consecutiveBlock_two_subset j).trans
      hC)), Subgroup.map_iSup]
  exact iSup_congr fun j => (hpair j).symm

theorem GraphFieldNeighbourParam.pieceCore_consecutiveBlock_le_iSup [Finite G]
    (P : GraphFieldNeighbourParam e t X N) {i r : ℕ} (hir : i + r ≤ m) (hr : 1 ≤ r)
    (hC : consecutiveBlock (m + 1) i (r + 1) ⊆ N) (hNc : 2 ≤ Nᶜ.card)
    (hX : X ≤ modelToG e (unitaryBlockTorus h (consecutiveBlock (m + 1) i (r + 1)))) :
    pieceCore e (consecutiveBlock (m + 1) i (r + 1)) ≤
      ⨆ k : Fin m, pieceCore e ({k.castSucc, k.succ} : Finset (Fin (m + 1))) := by
  rw [P.pieceCore_consecutiveBlock_eq_iSup hir hr hC hNc hX]
  refine iSup_le fun j => ?_
  have hj := j.isLt
  rw [consecutiveBlock_two_eq_nodePair (by omega : i + (j : ℕ) < m)]
  exact le_iSup (fun k : Fin m => pieceCore e ({k.castSucc, k.succ} : Finset (Fin (m + 1))))
    ⟨i + j, by omega⟩

theorem window4_eq_consecutiveBlock {n : ℕ} (i : Fin (n - 3)) :
    window4 i = consecutiveBlock n i (3 + 1) := by
  ext x
  rw [mem_window4, mem_consecutiveBlock]
  omega

theorem le_iSup_pieceCore_pair_of_graphFieldNeighbourCover [Finite G] (hm : 3 ≤ m)
    (hcov : GraphFieldNeighbourCover e t 4) :
    L ≤ ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) := by
  refine (modelToG_top e).symm.le.trans ?_
  rw [← iSup_blockSU_Icc_eq_top h (by omega : 4 ≤ m + 1), modelToG_iSup]
  refine iSup_le fun i => ?_
  have hW4 : (window4 i).card = 4 := card_window4 i
  obtain ⟨X, N, P, hWN, hNc, hX, -⟩ :=
    exists_pieceCore_eq_map_of_graphFieldNeighbourCover hcov (by omega : 2 ≤ (window4 i).card)
      hW4.le
  refine (P.modelToG_blockSU_le_pieceCore hWN (by omega)
    (hNc.trans (card_compl_le_card_compl_of_subset hWN)) hX).trans ?_
  rw [window4_eq_consecutiveBlock] at hWN hX ⊢
  exact P.pieceCore_consecutiveBlock_le_iSup (by have := i.isLt; omega) (by norm_num) hWN hNc hX

theorem mem_normalizer_iSup_pieceCore_pair (e : L ≃* unitaryPSU h (m + 1))
    (htC : t ∈ centralizer (L : Set G)) :
    t ∈ normalizer ((⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) :
      Subgroup G) : Set G) :=
  CFSG.LieType.Steinberg.le_normalizer_iSup
    (fun _ => (zpowers_le (G := G)).2 (le_normalizer_pieceCore e htC _)) (mem_zpowers t)

end Join

section Global

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {m f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {e : L ≃* unitaryPSU h (m + 1)} {t : G}

theorem nonempty_mulEquiv_projectiveSL_of_lieModel (h : UnitaryFieldData 2 f K) {Q : Type}
    [Group Q] {n : ℕ}
    (hQ : CFSG.Blueprint.LieModel Q CFSG.Assembly.LowTwoRank.StatedLieTag.PSL n 2 (2 * f)) :
    Nonempty (Q ≃* LinearFlag.projectiveSL n K) := by
  have := h.finite
  obtain ⟨F', _, _, hF', ⟨ψ₁⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel hQ
  have : Fintype F' := Fintype.ofFinite F'
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card F' = Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF', h.card]
  exact ⟨ψ₁.trans
    (CFSG.EvenSmallLie.Child3.SelL39.projectiveSLCongr (FiniteField.ringEquivOfCardEq hcard))⟩

theorem exists_globalField_of_graphFieldNeighbourCover (hm : 3 ≤ m)
    (htC : t ∈ centralizer (L : Set G)) (hcov : GraphFieldNeighbourCover e t 4)
    {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))) :
    L ≤ G₀ ∧ t ∈ normalizer (G₀ : Set G) ∧ CFSG.IsQuasisimple G₀ ∧
      CFSG.Blueprint.LieModel (G₀ ⧸ center G₀) CFSG.Assembly.LowTwoRank.StatedLieTag.PSL
        (m + 1) 2 (2 * f) ∧
      Nonempty (G₀ ⧸ center G₀ ≃* LinearFlag.projectiveSL (m + 1) K) ∧
      ∃ ψ : SL(m + 1, K) →* G₀, Function.Surjective ψ ∧ ψ.ker ≤ center SL(m + 1, K) ∧
        ∀ i : Fin m,
          (blockSpecialLinear (K := K) ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).map ψ =
            (pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).subgroupOf G₀ := by
  obtain ⟨ψ, hsurj, hker, himg, hqs, hmodel⟩ :=
    exists_weakCT_of_graphFieldNeighbourCover hm (hcov.mono (by norm_num))
      (fun i j hij => pieceCore_le_centralizer_of_graphFieldNeighbourCover hcov
        (LinearPilot.disjoint_nodePair_of_lt i j hij) (LinearPilot.card_nodePair i).ge
        (LinearPilot.card_nodePair j).ge (LinearPilot.card_union_nodePair_le i j)) hG₀
  refine ⟨hG₀ ▸ le_iSup_pieceCore_pair_of_graphFieldNeighbourCover hm hcov,
    hG₀ ▸ mem_normalizer_iSup_pieceCore_pair e htC, hqs, hmodel,
    nonempty_mulEquiv_projectiveSL_of_lieModel h hmodel, ψ, hsurj, hker, himg⟩

theorem exists_globalField_unitaryRootTorus (hm : 5 ≤ m) (htC : t ∈ centralizer (L : Set G))
    (hparam : ∀ (a b : Fin (m + 1)) (hab : a ≠ b),
      Nonempty (GraphFieldNeighbourParam e t (modelToG e (unitaryRootTorus h hab))
        ({a, b}ᶜ : Finset (Fin (m + 1)))))
    {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))) :
    L ≤ G₀ ∧ t ∈ normalizer (G₀ : Set G) ∧ CFSG.IsQuasisimple G₀ ∧
      CFSG.Blueprint.LieModel (G₀ ⧸ center G₀) CFSG.Assembly.LowTwoRank.StatedLieTag.PSL
        (m + 1) 2 (2 * f) ∧
      Nonempty (G₀ ⧸ center G₀ ≃* LinearFlag.projectiveSL (m + 1) K) ∧
      ∃ ψ : SL(m + 1, K) →* G₀, Function.Surjective ψ ∧ ψ.ker ≤ center SL(m + 1, K) ∧
        ∀ i : Fin m,
          (blockSpecialLinear (K := K) ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).map ψ =
            (pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1)))).subgroupOf G₀ :=
  exists_globalField_of_graphFieldNeighbourCover (by omega) htC
    (graphFieldNeighbourCover_rootTorus hparam (by omega)) hG₀

end Global

end CFSG.SeitzReduction.UnitaryPilot
