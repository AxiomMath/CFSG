module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotWeakCTNormal
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotUniqueGen

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.EvenSmallLie (StandardSetting)
open CFSG.SeitzReduction.LinearPilot (blockSL)
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem map_toPSL_unitaryBlockTorus_le_blockTorus {n : ℕ} (I : Finset (Fin n)) :
    (unitaryBlockTorus h I).map (toPSL h n) ≤ LinearPilot.blockTorus I := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨c, hc, rfl⟩ := (mem_unitaryBlockTorus h).1 hx
  rw [toPSL_unitaryProj, toSL_torusDiagSU]
  exact LinearPilot.proj_torusDiagSL_mem_blockTorus (unitaryTorusParam_le_blockTorusParam h I hc)

theorem toPSL_mem_centralizer_blockSL {n : ℕ} {I : Finset (Fin n)} {x : unitaryPSU h n}
    (hx : x ∈ unitaryBlockTorus h I) :
    toPSL h n x ∈ centralizer (blockSL (K := K) I : Set (LinearFlag.projectiveSL n K)) := by
  rw [mem_centralizer_iff]
  intro b hb
  have hT := map_toPSL_unitaryBlockTorus_le_blockTorus h I (mem_map_of_mem _ hx)
  exact (mem_centralizer_iff.1 (LinearPilot.blockSL_le_centralizer_blockTorus I hb) _ hT).symm

section Generation

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem le_iSup_pieceCore_of_le_unitary (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {m : ℕ} (hm : 2 ≤ m) (hnq : (m + 1, 2 ^ f) ≠ (3, 2))
    (e : L ≃* unitaryPSU h (m + 1)) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {M : Subgroup G} [Group.IsPerfect M]
    (ψ₀ : M ⧸ center M ≃* LinearFlag.projectiveSL (m + 1) K) (hLM : L ≤ M)
    (htM : t ∈ normalizer (M : Set G)) :
    M ≤ ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))) := by
  have hn : 3 ≤ m + 1 := by omega
  obtain ⟨ψ, hψL, -⟩ := exists_globalGraphField_center_of_standardSetting h hset hOut hn hnq e ψ₀
    hLM htC ht htM
  set π : M →* LinearFlag.projectiveSL (m + 1) K :=
    ψ.toMonoidHom.comp (QuotientGroup.mk' (center M)) with hπ
  have hπs : Function.Surjective π := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπker : π.ker = center M := by
    ext x
    rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hπL : ∀ x : L, π (inclusion hLM x) = toPSL h (m + 1) (e x) := fun x => hψL x
  have hF4 : 4 ≤ Nat.card K := four_le_card_of_unitaryFieldData h
  have := h.finite
  set I : Fin m → Finset (Fin (m + 1)) := fun i => {i.castSucc, i.succ} with hI
  set B : Fin m → Subgroup M := fun i => (blockSL (K := K) (I i)).comap π with hB
  set C : Fin m → Subgroup M := fun i => perfectCore (B i) with hC
  have hCB : ∀ i, C i ≤ B i := fun i => CFSG.Quasithin.perfectCore_le _
  have hCpiece : ∀ i, (C i).map M.subtype ≤ pieceCore e (I i) := by
    intro i
    have hperf : ⁅(C i).map M.subtype, (C i).map M.subtype⁆ = (C i).map M.subtype := by
      rw [← map_commutator, CFSG.Quasithin.perfectCore_perfect]
    refine F4Pilot.le_centralizerPerfectCore hperf
      (LinearPilot.le_centralizer_of_commutator_le_center (M := M) (map_subtype_le _) hperf ?_)
    rw [Subgroup.commutator_le]
    rintro _ ⟨c, hc, rfl⟩ y hy
    obtain ⟨x, hx, rfl⟩ := (mem_modelToG e).1 hy
    set j : M := inclusion hLM (e.symm x) with hj
    have hcB : π c ∈ blockSL (K := K) (I i) := hCB i hc
    have hjT : π j ∈ centralizer (blockSL (K := K) (I i) :
        Set (LinearFlag.projectiveSL (m + 1) K)) := by
      rw [hj, hπL, MulEquiv.apply_symm_apply]
      exact toPSL_mem_centralizer_blockSL h hx
    have hcomm : π ⁅c, j⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact (mem_centralizer_iff.1 hjT _ hcB)
    have hZ : ⁅c, j⁆ ∈ center M := by
      rw [← hπker]
      exact hcomm
    exact ⟨⁅c, j⁆, hZ, rfl⟩
  have hgen : (⨆ i, C i) = ⊤ := by
    refine LinearPilot.eq_top_of_sup_center_eq_top_of_perfect ?_
    rw [← hπker, ← Subgroup.comap_map_eq, Subgroup.map_iSup]
    have hi : ∀ i, (C i).map π = blockSL (K := K) (I i) := by
      intro i
      rw [hC, CFSG.Quasithin.map_perfectCore, hB, Subgroup.map_comap_eq_self_of_surjective hπs,
        CFSG.Quasithin.perfectCore_eq_self_of_perfect
          (LinearPilot.commutator_blockSL_eq_of_card_two (LinearPilot.card_nodePair i) hF4)]
    simp_rw [hi]
    rw [hI, LinearPilot.iSup_blockSL_pair_eq_top K m, Subgroup.comap_top]
  intro g hg
  have hmem : (⟨g, hg⟩ : M) ∈ ⨆ i, C i := hgen ▸ mem_top _
  have h2 : g ∈ (⨆ i, C i).map M.subtype := ⟨⟨g, hg⟩, hmem, rfl⟩
  rw [Subgroup.map_iSup] at h2
  exact (iSup_mono hCpiece) h2

theorem eq_of_le_of_card_le_unitary (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {m : ℕ} (hm : 2 ≤ m) (hnq : (m + 1, 2 ^ f) ≠ (3, 2))
    (e : L ≃* unitaryPSU h (m + 1)) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {M G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))))
    [Group.IsPerfect M] (ψ₀ : M ⧸ center M ≃* LinearFlag.projectiveSL (m + 1) K) (hLM : L ≤ M)
    (htM : t ∈ normalizer (M : Set G)) (hcard : Nat.card G₀ ≤ Nat.card M) : M = G₀ :=
  Subgroup.eq_of_le_of_card_ge
    (hG₀ ▸ le_iSup_pieceCore_of_le_unitary h hset hOut hm hnq e htC ht ψ₀ hLM htM) hcard

theorem conjugate_eq_of_le_unitary (hset : StandardSetting G L)
    (hOut : Group.IsSolvable (Outer L)) {m : ℕ} (hm : 2 ≤ m) (hnq : (m + 1, 2 ^ f) ≠ (3, 2))
    (e : L ≃* unitaryPSU h (m + 1)) {t : G} (htC : t ∈ centralizer (L : Set G))
    (ht : orderOf t = 2) {G₀ : Subgroup G}
    (hG₀ : G₀ = ⨆ i : Fin m, pieceCore e ({i.castSucc, i.succ} : Finset (Fin (m + 1))))
    [Group.IsPerfect G₀] (ψ : G₀ ⧸ center G₀ ≃* LinearFlag.projectiveSL (m + 1) K) (g : G)
    (htg : t ∈ normalizer (CFSG.conjugate G₀ g : Set G)) (hLg : L ≤ CFSG.conjugate G₀ g) :
    CFSG.conjugate G₀ g = G₀ := by
  have : Group.IsPerfect (CFSG.conjugate G₀ g) :=
    Group.IsPerfect.ofSurjective (f := (LinearPilot.conjugateEquiv G₀ g).toMonoidHom)
      (LinearPilot.conjugateEquiv G₀ g).surjective
  exact eq_of_le_of_card_le_unitary h hset hOut hm hnq e htC ht hG₀
    ((LinearPilot.conjugateQuotientCenterEquiv G₀ g).symm.trans ψ) hLg htg
    (Nat.card_congr (LinearPilot.conjugateEquiv G₀ g).toEquiv).le

end Generation

end CFSG.SeitzReduction.UnitaryPilot
