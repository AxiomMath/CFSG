module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGStructPSL
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoPSLCent
public import CFSG.LocalAnalysis.StandardType.GGRootCentKGMarkingSL
import CFSG.LocalAnalysis.StandardType.GGSixRootCentSummandStructPSL
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotInvolutionCentralizer
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotInvolutionCentralizerLevi
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotRestrictionField
import CFSG.LocalAnalysis.StandardType.GGRootCentKGSpCent
import CFSG.LocalAnalysis.SeitzReduction.EPilotCentralizerHighBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

namespace KGPSL

open CFSG.SeitzReduction.LinearPilot
open CFSG.ComponentClassification
open scoped Pointwise commutatorElement

@[expose] noncomputable def blockLevi {m : ℕ} {K : Type} [Field K] (hm : 1 ≤ m) :
    Subgroup (projectiveSL (m + 1) K) :=
  (blockSpecialLinear (K := K) (LinFusion.ggTransPlacement hm).free).map (proj (m + 1) K)

theorem blockLevi_le_leviFull {m : ℕ} {K : Type} [Field K] [CharP K 2] (hm : 1 ≤ m) :
    blockLevi (K := K) hm ≤ leviFull (K := K) hm := by
  rw [blockLevi, leviFull_eq_map hm]
  exact Subgroup.map_mono (blockSpecialLinear_le_leviSL hm)

theorem commutator_centralizer_rootInv_le {m : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] (hm : 3 ≤ m) :
    ⁅Subgroup.centralizer ({rootInvPSL m K (by omega)} :
        Set (projectiveSL (m + 1) K)),
      Subgroup.centralizer ({rootInvPSL m K (by omega)} :
        Set (projectiveSL (m + 1) K))⁆ ≤
      radical (K := K) (by omega) ⊔ blockLevi (K := K) (by omega) := by
  have hm1 : 1 ≤ m := by omega
  set P := LinFusion.ggTransPlacement hm1 with hP
  have hC : Subgroup.centralizer ({rootInvPSL m K (by omega)} :
        Set (projectiveSL (m + 1) K)) =
      (Subgroup.centralizer ({AutPSL.rootInv (K := K) hm1} :
        Set (SpecialLinearGroup (Fin (m + 1)) K))).map (proj (m + 1) K) := by
    exact centralizer_rootInv_eq_map (K := K) hm1
  have hcore : (P.core K).map (proj (m + 1) K) =
      radical (K := K) hm1 ⊔ blockLevi (K := K) hm1 := by
    rw [InvPlacement.map_core_eq P]
    change P.radicalP K ⊔ (P.leviOneP K ⊔ blockSL P.free) =
      P.radicalP K ⊔ blockSL P.free
    unfold InvPlacement.leviOneP
    rw [RCSPSL.leviOne_eq_bot P, Subgroup.map_bot, bot_sup_eq]
  calc ⁅Subgroup.centralizer ({rootInvPSL m K (by omega)} :
          Set (projectiveSL (m + 1) K)),
        Subgroup.centralizer ({rootInvPSL m K (by omega)} :
          Set (projectiveSL (m + 1) K))⁆
      = ⁅(Subgroup.centralizer ({AutPSL.rootInv (K := K) hm1} :
            Set (SpecialLinearGroup (Fin (m + 1)) K))).map (proj (m + 1) K),
          (Subgroup.centralizer ({AutPSL.rootInv (K := K) hm1} :
            Set (SpecialLinearGroup (Fin (m + 1)) K))).map (proj (m + 1) K)⁆ := by rw [hC]
    _ = (⁅Subgroup.centralizer ({AutPSL.rootInv (K := K) hm1} :
            Set (SpecialLinearGroup (Fin (m + 1)) K)),
          Subgroup.centralizer ({AutPSL.rootInv (K := K) hm1} :
            Set (SpecialLinearGroup (Fin (m + 1)) K))⁆).map (proj (m + 1) K) :=
        (Subgroup.map_commutator _ _ _).symm
    _ ≤ (P.core K).map (proj (m + 1) K) :=
        Subgroup.map_mono (by
          have hmat : (LinFusion.ggTransPlacement hm1).mat K = AutPSL.rootInv hm1 :=
            ggTransPlacement_mat_eq_rootInv (K := K) (m := m) hm1
          simpa [hP, hmat] using InvPlacement.commutator_centralizer_le_core (K := K) P)
    _ = radical (K := K) hm1 ⊔ blockLevi (K := K) hm1 := hcore

noncomputable def blockLeviEquiv {m : ℕ} {K : Type} [Field K] (hm : 1 ≤ m) :
    SpecialLinearGroup (LinFusion.ggTransPlacement hm).free K ≃*
      ↥(blockLevi (K := K) hm) := by
  classical
  set P := LinFusion.ggTransPlacement hm with hP
  let f : SpecialLinearGroup ↥P.free K →* ↥(blockLevi (K := K) hm) :=
    ((proj (m + 1) K).comp (blockEmbed P.free)).codRestrict (blockLevi (K := K) hm)
      fun A => Subgroup.mem_map_of_mem (proj (m + 1) K)
        (InvPlacement.blockEmbed_free_mem P A)
  have hf : Function.Injective f := by
    intro A B h
    refine proj_comp_blockEmbed_injective (K := K) (I := P.free) ?_ (congrArg Subtype.val h)
    rw [InvPlacement.card_free]
    omega
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨A, hA, hAx⟩ := Subgroup.mem_map.1 x.2
    rw [← range_blockEmbed] at hA
    obtain ⟨B, rfl⟩ := hA
    exact ⟨B, Subtype.ext hAx⟩
  exact MulEquiv.ofBijective f ⟨hf, hsurj⟩

noncomputable def blockLeviHom {m : ℕ} {K : Type} [Field K] (hm : 1 ≤ m) :
    SpecialLinearGroup (Fin (m - 1)) K →* ↥(blockLevi (K := K) hm) :=
  (blockLeviEquiv hm).toMonoidHom.comp
    (reindexSpecialLinear (freeEquiv hm)).symm.toMonoidHom

theorem isQuasisimple_blockLevi {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hm : 3 ≤ m) (hq : 4 ≤ m ∨ 4 ≤ Nat.card K) :
    CFSG.Assembly.IsQuasisimple ↥(blockLevi (K := K) (m := m) (by omega)) := by
  classical
  have hm1 : 1 ≤ m := by omega
  set P := LinFusion.ggTransPlacement hm1 with hP
  have hJ : 2 ≤ P.free.card := by rw [InvPlacement.card_free]; omega
  have hfree : 3 ≤ P.free.card ∨ 4 ≤ Nat.card K := by
    rcases hq with h4 | h4
    · left; rw [InvPlacement.card_free]; omega
    · exact Or.inr h4
  have hq1 : CFSG.IsQuasisimple (SpecialLinearGroup ↥P.free K) :=
    RCSPSL.isQuasisimple_free (F := K) P hJ hfree
  have hq2 : CFSG.IsQuasisimple (SpecialLinearGroup (Fin (m - 1)) K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (reindexSpecialLinear (K := K) (freeEquiv hm1)) hq1
  haveI : Subsingleton (SpecialLinearGroup (Fin 1) K) :=
    ⟨fun a b => by rw [LinFusion.eq_one_of_specialLinearGroup_fin_one a,
      LinFusion.eq_one_of_specialLinearGroup_fin_one b]⟩
  have hq3 : CFSG.IsQuasisimple ↥(blockLevi (K := K) hm1) := by
    refine CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (MulEquiv.ofBijective (blockLeviHom (K := K) hm1) ?_) hq2
    refine ⟨?_, ?_⟩
    · intro A B h
      have h' : ((blockLeviHom (K := K) hm1) A : projectiveSL (m + 1) K) =
          ((blockLeviHom (K := K) hm1) B : projectiveSL (m + 1) K) := congrArg Subtype.val h
      exact (reindexSpecialLinear (freeEquiv hm1)).symm.injective
        ((proj_comp_blockEmbed_injective (K := K) (I := P.free) (by
            rw [InvPlacement.card_free]; omega)) h')
    · intro x
      obtain ⟨B, rfl⟩ := (blockLeviEquiv hm1).surjective x
      exact ⟨(reindexSpecialLinear (freeEquiv hm1)) B, by
        simp [blockLeviHom]⟩
  exact ⟨hq3.1.commutator_eq_top, hq3.2.1⟩

theorem blockLevi_le_normalizer_radical {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hm : 2 ≤ m) :
    blockLevi (K := K) (Nat.le_of_succ_le hm) ≤
      Subgroup.normalizer ((radical (K := K) (Nat.le_of_succ_le hm) :
        Subgroup (projectiveSL (m + 1) K)) : Set (projectiveSL (m + 1) K)) :=
  (blockLevi_le_leviFull (K := K) (Nat.le_of_succ_le hm)).trans
    (leviFull_le_normalizer_radical (K := K) hm)

theorem disjoint_radical_blockLevi {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hm : 2 ≤ m) :
    Disjoint (radical (K := K) (Nat.le_of_succ_le hm))
      (blockLevi (K := K) (Nat.le_of_succ_le hm)) := by
  rw [disjoint_iff]
  refine le_antisymm ?_ bot_le
  calc radical (K := K) (Nat.le_of_succ_le hm) ⊓
        blockLevi (K := K) (Nat.le_of_succ_le hm)
      ≤ radical (K := K) (Nat.le_of_succ_le hm) ⊓ leviFull (K := K) (Nat.le_of_succ_le hm) :=
        inf_le_inf_left _ (blockLevi_le_leviFull (K := K) (Nat.le_of_succ_le hm))
    _ = ⊥ := disjoint_iff.mp (disjoint_radical_leviFull (K := K) hm)

theorem commutator_radical_sup_blockLevi {m : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] (hm : 3 ≤ m) (hq : 4 ≤ m ∨ 4 ≤ Nat.card K) :
    ⁅radical (K := K) (m := m) (by omega) ⊔ blockLevi (K := K) (m := m) (by omega),
      radical (K := K) (m := m) (by omega) ⊔ blockLevi (K := K) (m := m) (by omega)⁆ =
      radical (K := K) (m := m) (by omega) ⊔ blockLevi (K := K) (m := m) (by omega) := by
  classical
  have hm1 : 1 ≤ m := by omega
  set P := LinFusion.ggTransPlacement hm1 with hP
  have hJ : 2 ≤ P.free.card := by rw [InvPlacement.card_free]; omega
  have hfree : 3 ≤ P.free.card ∨ 4 ≤ Nat.card K := by
    rcases hq with h4 | h4
    · left; rw [InvPlacement.card_free]; omega
    · exact Or.inr h4
  haveI : Group.IsPerfect (SpecialLinearGroup ↥P.free K) :=
    (RCSPSL.isQuasisimple_free (F := K) P hJ hfree).1
  haveI : Group.IsPerfect (SpecialLinearGroup (Fin 1) K) := by
    refine ⟨le_antisymm le_top fun x _ => ?_⟩
    rw [LinFusion.eq_one_of_specialLinearGroup_fin_one x]
    exact Subgroup.one_mem _
  have hcore : ⁅P.core K, P.core K⁆ = P.core K :=
    InvPlacement.commutator_core (K := K) P hJ
  have hcoremap : (P.core K).map (proj (m + 1) K) =
      radical (K := K) hm1 ⊔ blockLevi (K := K) hm1 := by
    rw [InvPlacement.map_core_eq P]
    change P.radicalP K ⊔ (P.leviOneP K ⊔ blockSL P.free) =
      P.radicalP K ⊔ blockSL P.free
    unfold InvPlacement.leviOneP
    rw [RCSPSL.leviOne_eq_bot P, Subgroup.map_bot, bot_sup_eq]
  calc ⁅radical (K := K) hm1 ⊔ blockLevi (K := K) hm1,
        radical (K := K) hm1 ⊔ blockLevi (K := K) hm1⁆
      = ⁅(P.core K).map (proj (m + 1) K), (P.core K).map (proj (m + 1) K)⁆ := by
        rw [hcoremap]
    _ = (⁅P.core K, P.core K⁆).map (proj (m + 1) K) :=
        (Subgroup.map_commutator _ _ _).symm
    _ = (P.core K).map (proj (m + 1) K) := by rw [hcore]
    _ = radical (K := K) hm1 ⊔ blockLevi (K := K) hm1 := hcoremap

theorem blockLeviHom_injective {m : ℕ} {K : Type} [Field K] (hm : 1 ≤ m) :
    Function.Injective (blockLeviHom (K := K) hm) := by
  intro B₁ B₂ h
  have h' : ((blockLeviHom (K := K) hm B₁ : ↥(blockLevi (K := K) hm)) :
      projectiveSL (m + 1) K) =
      ((blockLeviHom (K := K) hm B₂ : ↥(blockLevi (K := K) hm)) :
        projectiveSL (m + 1) K) := congrArg Subtype.val h
  exact (reindexSpecialLinear (freeEquiv hm)).symm.injective
    ((proj_comp_blockEmbed_injective (K := K)
      (I := (LinFusion.ggTransPlacement hm).free) (by
        rw [InvPlacement.card_free]; omega)) h')

theorem blockLeviHom_surjective {m : ℕ} {K : Type} [Field K] (hm : 1 ≤ m) :
    Function.Surjective (blockLeviHom (K := K) hm) := by
  intro x
  obtain ⟨B, rfl⟩ := (blockLeviEquiv (K := K) hm).surjective x
  refine ⟨(reindexSpecialLinear (freeEquiv hm)) B, ?_⟩
  show blockLeviHom (K := K) hm ((reindexSpecialLinear (freeEquiv hm)) B) =
    blockLeviEquiv (K := K) hm B
  simp only [blockLeviHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]

private theorem reindex_reindex_apply {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] {K : Type*} [Field K] (e : ι ≃ κ) (M : Matrix κ κ K) :
    Matrix.reindex e e (Matrix.reindex e.symm e.symm M) = M := by
  ext i j
  rw [Matrix.reindex_apply, Matrix.reindex_apply]
  simp

theorem mul_inv_mem_of_inv_mul_mem_of_le_normalizer {G : Type*} [Group G] {Q C : Subgroup G}
    (hCN : C ≤ Subgroup.normalizer (Q : Set G)) {c a : G}
    (hc : c ∈ C) (h : a⁻¹ * c ∈ Q) : c * a⁻¹ ∈ Q := by
  have h' := (Subgroup.mem_normalizer_iff.1 (hCN hc)) (a⁻¹ * c)
  have h2 : c * (a⁻¹ * c) * c⁻¹ ∈ Q := h'.1 h
  have heq : c * a⁻¹ = c * (a⁻¹ * c) * c⁻¹ := by group
  rw [heq]
  exact h2

theorem conj_mul_inv_mem_of_mem_of_le_normalizer {G : Type*} [Group G] {Q C : Subgroup G}
    (hCN : C ≤ Subgroup.normalizer (Q : Set G)) {q c a : G}
    (hq : q ∈ Q) (ha : a ∈ C) (h : c * a⁻¹ ∈ Q) :
    MulAut.conj q c * a⁻¹ ∈ Q := by
  have h1 : MulAut.conj q (c * a⁻¹) ∈ Q := by
    have hqN := (Subgroup.le_normalizer_iff.1 (Subgroup.le_normalizer (H := Q))) q hq
    exact hqN _ h
  have h2 : MulAut.conj q a * a⁻¹ ∈ Q := by
    have h3 : a * q * a⁻¹ * q⁻¹ ∈ Q :=
      Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.1 (hCN ha) q).1 hq)
        (Subgroup.inv_mem _ hq)
    have h5 : MulAut.conj q a * a⁻¹ = (a * q * a⁻¹ * q⁻¹)⁻¹ := by
      simp only [MulAut.conj_apply]
      group
    rw [h5]
    exact Subgroup.inv_mem _ h3
  have hsplit : MulAut.conj q c * a⁻¹ =
      MulAut.conj q (c * a⁻¹) * (MulAut.conj q a * a⁻¹) := by
    simp only [MulAut.conj_apply]
    group
  rw [hsplit]
  exact Subgroup.mul_mem _ h1 h2

theorem conjAut_mem_centralizer {m : ℕ} {K : Type} [Field K]
    (X : GL (Fin (m + 1)) K) (hm : 1 ≤ m)
    (hX : X * SpecialLinearGroup.toGL (AutPSL.rootInv hm) =
      SpecialLinearGroup.toGL (AutPSL.rootInv hm) * X)
    {x : projectiveSL (m + 1) K}
    (hx : x ∈ Subgroup.centralizer
      ({proj (m + 1) K (AutPSL.rootInv hm)} : Set (projectiveSL (m + 1) K))) :
    conjAut (m + 1) K X x ∈ Subgroup.centralizer
      ({proj (m + 1) K (AutPSL.rootInv hm)} : Set (projectiveSL (m + 1) K)) := by
  have hXfix : conjAut (m + 1) K X (proj (m + 1) K (AutPSL.rootInv hm)) =
      proj (m + 1) K (AutPSL.rootInv hm) := conjAut_fixes_of_comm hX
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  calc conjAut (m + 1) K X x * proj (m + 1) K (AutPSL.rootInv hm)
      = conjAut (m + 1) K X x * conjAut (m + 1) K X (proj (m + 1) K (AutPSL.rootInv hm)) := by
        rw [hXfix]
    _ = conjAut (m + 1) K X (x * proj (m + 1) K (AutPSL.rootInv hm)) :=
        (map_mul _ _ _).symm
    _ = conjAut (m + 1) K X (proj (m + 1) K (AutPSL.rootInv hm) * x) := by rw [hx]
    _ = conjAut (m + 1) K X (proj (m + 1) K (AutPSL.rootInv hm)) * conjAut (m + 1) K X x :=
        map_mul _ _ _
    _ = proj (m + 1) K (AutPSL.rootInv hm) * conjAut (m + 1) K X x := by rw [hXfix]

theorem exists_alpha_of_mem_inndiag_fix {m' : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] :
    ∀ δ ∈ (AutPSL.inndiag : Subgroup (MulAut (projectiveSL (m' + 2 + 1) K))),
      δ (rootInvPSL (m' + 2) K (show 2 ≤ m' + 2 by omega)) =
        rootInvPSL (m' + 2) K (show 2 ≤ m' + 2 by omega) →
      ∃ α : MulAut ↥(blockLevi (K := K) (m := m' + 2) (show 1 ≤ m' + 2 by omega)),
        α ∈ KGND.slConjSet (m := m') (F := K)
          (blockLeviHom (K := K) (m := m' + 2) (show 1 ≤ m' + 2 by omega)) ∧
        ∀ s ∈ radical (K := K) (m := m' + 2) (show 1 ≤ m' + 2 by omega) ⊔
              blockLevi (K := K) (m := m' + 2) (show 1 ≤ m' + 2 by omega),
          ∀ l : ↥(blockLevi (K := K) (m := m' + 2) (show 1 ≤ m' + 2 by omega)),
            s * (l : projectiveSL (m' + 2 + 1) K)⁻¹ ∈
              radical (K := K) (m := m' + 2) (show 1 ≤ m' + 2 by omega) →
            δ s * ((α l : ↥(blockLevi (K := K) (m := m' + 2) (show 1 ≤ m' + 2 by omega))) :
              projectiveSL (m' + 2 + 1) K)⁻¹ ∈
              radical (K := K) (m := m' + 2) (show 1 ≤ m' + 2 by omega) := by
  intro δ hδmem hδz
  classical
  have hm2 : 2 ≤ m' + 2 := by omega
  have hm1 : 1 ≤ m' + 2 := by omega
  set P := LinFusion.ggTransPlacement hm1 with hP
  have hδmem' : δ ∈ (conjAut (m' + 2 + 1) K).range := hδmem
  obtain ⟨A, hA⟩ := MonoidHom.mem_range.1 hδmem'
  obtain ⟨s, D, hAD, hD1, hD2⟩ := exists_diag_decomp (K := K) (m := m' + 2) hm2 A
  set p : projectiveSL (m' + 2 + 1) K := proj (m' + 2 + 1) K s with hp
  have hδeq : δ = MulAut.conj p * conjAut (m' + 2 + 1) K D := by
    rw [← hA, hAD, map_mul, conjAut_toGL]
  have hDfix : conjAut (m' + 2 + 1) K D
      (rootInvPSL (m' + 2) K (show 2 ≤ m' + 2 by omega)) =
        rootInvPSL (m' + 2) K (show 2 ≤ m' + 2 by omega) := by
    rw [rootInvPSL]
    exact conjAut_fixes_of_comm hD1
  have hpfix : MulAut.conj p (rootInvPSL (m' + 2) K (show 2 ≤ m' + 2 by omega)) =
      rootInvPSL (m' + 2) K (show 2 ≤ m' + 2 by omega) := by
    have h := hδz
    rw [hδeq, MulAut.mul_apply, hDfix] at h
    exact h
  have hpC : p ∈ Subgroup.centralizer
      ({rootInvPSL (m' + 2) K (show 2 ≤ m' + 2 by omega)} : Set (projectiveSL (m' + 2 + 1) K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    rw [MulAut.conj_apply] at hpfix
    calc p * rootInvPSL (m' + 2) K (show 2 ≤ m' + 2 by omega)
        = (p * rootInvPSL (m' + 2) K (show 2 ≤ m' + 2 by omega) * p⁻¹) * p := by group
      _ = rootInvPSL (m' + 2) K (show 2 ≤ m' + 2 by omega) * p := by rw [hpfix]
  have hpC' : p ∈ radical (K := K) (m := m' + 2) (show 1 ≤ m' + 2 by omega) ⊔
      leviFull (K := K) (m := m' + 2) (show 1 ≤ m' + 2 by omega) := by
    rw [← centralizer_rootInv_eq_sup (K := K) hm2]
    exact hpC
  change p ∈ ((radical (K := K) (m := m' + 2) (show 1 ≤ m' + 2 by omega) ⊔
    leviFull (K := K) (m := m' + 2) (show 1 ≤ m' + 2 by omega) :
      Subgroup (projectiveSL (m' + 2 + 1) K)) :
      Set (projectiveSL (m' + 2 + 1) K)) at hpC'
  rw [Subgroup.coe_mul_of_right_le_normalizer_left
    (radical (K := K) (m := m' + 2) (show 1 ≤ m' + 2 by omega))
    (leviFull (K := K) (m := m' + 2) (show 1 ≤ m' + 2 by omega))
    (leviFull_le_normalizer_radical (K := K) hm2), Set.mem_mul] at hpC'
  obtain ⟨q, hq, h, hh, hqh⟩ := hpC'
  rw [leviFull_eq_map (K := K) hm1] at hh
  obtain ⟨hD', hhD'⟩ := hh
  set X : GL (Fin (m' + 2 + 1)) K := SpecialLinearGroup.toGL hD' * D with hX
  have hlev0 : ∀ x : Fin (m' + 2 + 1), P.level x = 0 ↔ x = Fin.last (m' + 2) := by
    intro x
    rw [InvPlacement.level_eq_zero_iff]
    constructor
    · rintro ⟨a, ha⟩
      rw [LinFusion.ggTransPlacement_u] at ha
      exact ha.symm
    · intro hx
      exact ⟨0, by rw [LinFusion.ggTransPlacement_u, hx]⟩
  have hlev2 : ∀ x : Fin (m' + 2 + 1), P.level x = 2 ↔ x = 0 := by
    intro x
    rw [InvPlacement.level_eq_two_iff]
    constructor
    · rintro ⟨a, ha⟩
      rw [LinFusion.ggTransPlacement_w] at ha
      exact ha.symm
    · intro hx
      exact ⟨0, by rw [LinFusion.ggTransPlacement_w, hx]⟩
  have hD1' : D * LinFusion.ggT0GL (m' + 2) K = LinFusion.ggT0GL (m' + 2) K * D := by
    have hroot : AutPSL.rootInv (m := m' + 2) hm1 = ggInvSL (m' + 2 + 1) 1 K :=
      (AutPSL.ggInvSL_eq_rootInv (m := m' + 2) hm1).symm
    rw [hroot] at hD1
    exact hD1
  have hD1mat : (D : Matrix (Fin (m' + 2 + 1)) (Fin (m' + 2 + 1)) K) *
      ggInvMatrix (m' + 2 + 1) 1 K =
      ggInvMatrix (m' + 2 + 1) 1 K * (D : Matrix (Fin (m' + 2 + 1)) (Fin (m' + 2 + 1)) K) := by
    have h := congrArg (fun Y : (Matrix (Fin (m' + 2 + 1)) (Fin (m' + 2 + 1)) K)ˣ =>
      (Y : Matrix (Fin (m' + 2 + 1)) (Fin (m' + 2 + 1)) K)) hD1'
    rwa [Units.val_mul, Units.val_mul, LinFusion.coe_ggT0GL] at h
  have hDtri : (D : Matrix (Fin (m' + 2 + 1)) (Fin (m' + 2 + 1)) K).BlockTriangular P.level := by
    intro i j hij
    have hi := InvPlacement.level_le_two P i
    have hj := InvPlacement.level_le_two P j
    rcases (by omega : P.level i = 1 ∨ P.level i = 2) with hi1 | hi2
    · have hj0 : P.level j = 0 := by omega
      have hji : j = Fin.last (m' + 2) := (hlev0 j).1 hj0
      have hcol := LinFusion.col_last_of_commute (F := K) hm1 hD1mat i
      rw [hji, hcol]
      rw [if_neg]
      intro h
      have h0 : P.level i = 0 := (hlev0 i).2 h
      omega
    · have hi0 : i = 0 := (hlev2 i).1 hi2
      rcases (by omega : P.level j = 0 ∨ P.level j = 1) with hj0 | hj1
      · have hji : j = Fin.last (m' + 2) := (hlev0 j).1 hj0
        have hrow := LinFusion.row_zero_of_commute (F := K) hm1 hD1mat (Fin.last (m' + 2))
        rw [hi0, hji, hrow, if_neg (AutPSL.last_ne_zero (m := m' + 2) hm1)]
      · have hrow := LinFusion.row_zero_of_commute (F := K) hm1 hD1mat j
        rw [hi0, hrow, if_neg]
        intro hj0
        have h2 : P.level j = 2 := (hlev2 j).2 hj0
        omega
  have hhtri : ((SpecialLinearGroup.toGL hD' : GL (Fin (m' + 2 + 1)) K) :
      Matrix (Fin (m' + 2 + 1)) (Fin (m' + 2 + 1)) K).BlockTriangular P.level := by
    have hpar : hD' ∈ P.parabolic K :=
      P.blockDiag_le_parabolic ((mem_leviSL.1 hhD'.1).1)
    exact (InvPlacement.mem_parabolic P).1 hpar
  have hXtri : ((X : GL (Fin (m' + 2 + 1)) K) :
      Matrix (Fin (m' + 2 + 1)) (Fin (m' + 2 + 1)) K).BlockTriangular P.level := by
    rw [hX]
    rw [Units.val_mul]
    exact hhtri.mul hDtri
  have hXitri : (((X⁻¹ : GL (Fin (m' + 2 + 1)) K) :
      Matrix (Fin (m' + 2 + 1)) (Fin (m' + 2 + 1)) K)).BlockTriangular P.level := by
    rw [coe_units_inv]
    exact blockTriangular_inv_of_blockTriangular hXtri
  set XJ : Matrix ↥P.free ↥P.free K :=
    (X : Matrix (Fin (m' + 2 + 1)) (Fin (m' + 2 + 1)) K).submatrix
      Subtype.val Subtype.val with hXJ
  set XJi : Matrix ↥P.free ↥P.free K :=
    (((X⁻¹ : GL (Fin (m' + 2 + 1)) K) :
      Matrix (Fin (m' + 2 + 1)) (Fin (m' + 2 + 1)) K)).submatrix
      Subtype.val Subtype.val with hXJi
  have hXJXJi : XJ * XJi = 1 := by
    have h := InvPlacement.submatrix_mul_free P hXtri hXitri
    rw [← h, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      submatrix_one _ Subtype.val_injective]
  have hXJiXJ : XJi * XJ = 1 := by
    have h := InvPlacement.submatrix_mul_free P hXitri hXtri
    rw [← h, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      submatrix_one _ Subtype.val_injective]
  let XJunit : (Matrix ↥P.free ↥P.free K)ˣ := ⟨XJ, XJi, hXJXJi, hXJiXJ⟩
  have hXJunit_val : ((XJunit : (Matrix ↥P.free ↥P.free K)ˣ) :
      Matrix ↥P.free ↥P.free K) = XJ := rfl
  have hXJunit_inv : (((XJunit⁻¹ : (Matrix ↥P.free ↥P.free K)ˣ)) :
      Matrix ↥P.free ↥P.free K) = XJi := rfl
  let e0 : ↥P.free ≃ Fin (m' + 1) := freeEquiv hm1
  let A : GL (Fin (m' + 1)) K :=
    Units.map (Matrix.reindexAlgEquiv K K e0).toRingEquiv.toMonoidHom XJunit
  have hAval : ((A : GL (Fin (m' + 1)) K) :
      Matrix (Fin (m' + 1)) (Fin (m' + 1)) K) =
      Matrix.reindex e0 e0 XJ := by
    rw [show ((A : GL (Fin (m' + 1)) K) : Matrix (Fin (m' + 1)) (Fin (m' + 1)) K) =
        (Matrix.reindexAlgEquiv K K e0) ((XJunit : (Matrix ↥P.free ↥P.free K)ˣ) :
          Matrix ↥P.free ↥P.free K) from by
      dsimp only [A]
      rw [Units.coe_map]
      rfl]
    rw [hXJunit_val, reindexAlgEquiv_apply]
  have hAival : (((A⁻¹ : GL (Fin (m' + 1)) K)) :
      Matrix (Fin (m' + 1)) (Fin (m' + 1)) K) =
      Matrix.reindex e0 e0 XJi := by
    rw [show (((A⁻¹ : GL (Fin (m' + 1)) K)) :
        Matrix (Fin (m' + 1)) (Fin (m' + 1)) K) =
        (Matrix.reindexAlgEquiv K K e0) (((XJunit⁻¹ : (Matrix ↥P.free ↥P.free K)ˣ)) :
          Matrix ↥P.free ↥P.free K) from by
      dsimp only [A]
      rw [← map_inv, Units.coe_map]
      rfl]
    rw [hXJunit_inv, reindexAlgEquiv_apply]
  have hinjφ : Function.Injective (blockLeviHom (K := K) (m := m' + 2) hm1) := by
    intro B₁ B₂ h
    have h' : ((blockLeviHom (K := K) (m := m' + 2) hm1 B₁ :
        ↥(blockLevi (K := K) (m := m' + 2) hm1)) : projectiveSL (m' + 2 + 1) K) =
        ((blockLeviHom (K := K) (m := m' + 2) hm1 B₂ :
          ↥(blockLevi (K := K) (m := m' + 2) hm1)) : projectiveSL (m' + 2 + 1) K) :=
      congrArg Subtype.val h
    exact (reindexSpecialLinear e0).symm.injective
      ((proj_comp_blockEmbed_injective (K := K) (I := P.free) (by
        rw [InvPlacement.card_free]; omega)) h')
  have hsurjφ : Function.Surjective (blockLeviHom (K := K) (m := m' + 2) hm1) := by
    intro x
    obtain ⟨B, rfl⟩ := (blockLeviEquiv (K := K) (m := m' + 2) hm1).surjective x
    refine ⟨(reindexSpecialLinear e0) B, ?_⟩
    show blockLeviHom (K := K) (m := m' + 2) hm1
      ((reindexSpecialLinear e0) B) = blockLeviEquiv (K := K) (m := m' + 2) hm1 B
    simp only [blockLeviHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, e0]
  let φEquiv : SpecialLinearGroup (Fin (m' + 1)) K ≃*
      ↥(blockLevi (K := K) (m := m' + 2) hm1) :=
    MulEquiv.ofBijective (blockLeviHom (K := K) (m := m' + 2) hm1) ⟨hinjφ, hsurjφ⟩
  have hinjcA : Function.Injective (InnerDiagA.conjSL (m := m') A) := by
    intro B₁ B₂ h
    have h' := congrArg (InnerDiagA.slEquiv m' K) h
    rw [InnerDiagA.slEquiv_conjSL, InnerDiagA.slEquiv_conjSL] at h'
    exact (InnerDiagA.slEquiv m' K).injective
      ((MulAut.conjNormal A).injective h')
  have hsurjcA : Function.Surjective (InnerDiagA.conjSL (m := m') A) := by
    intro y
    refine ⟨(InnerDiagA.slEquiv m' K).symm
      ((MulAut.conjNormal A)⁻¹ ((InnerDiagA.slEquiv m' K) y)), ?_⟩
    apply (InnerDiagA.slEquiv m' K).injective
    rw [InnerDiagA.slEquiv_conjSL]
    simp
  let cA : MulAut (SpecialLinearGroup (Fin (m' + 1)) K) :=
    MulEquiv.ofBijective (InnerDiagA.conjSL (m := m') A) ⟨hinjcA, hsurjcA⟩
  let α : MulAut ↥(blockLevi (K := K) (m := m' + 2) hm1) :=
    (φEquiv.symm.trans cA).trans φEquiv
  have hα : α ∈ KGND.slConjSet (m := m') (F := K)
      (blockLeviHom (K := K) (m := m' + 2) hm1) := by
    refine ⟨A, fun B => ?_⟩
    show ((φEquiv.symm.trans cA).trans φEquiv)
      (blockLeviHom (K := K) (m := m' + 2) hm1 B) =
      blockLeviHom (K := K) (m := m' + 2) hm1 (InnerDiagA.conjSL (m := m') A B)
    change φEquiv (cA (φEquiv.symm (φEquiv B))) =
      blockLeviHom (K := K) (m := m' + 2) hm1 (InnerDiagA.conjSL (m := m') A B)
    rw [MulEquiv.symm_apply_apply]
    dsimp only [cA, φEquiv]
    rfl
  have hδX : δ = MulAut.conj q * conjAut (m' + 2 + 1) K X := by
    rw [hδeq, ← hqh, map_mul]
    rw [show MulAut.conj h = conjAut (m' + 2 + 1) K (SpecialLinearGroup.toGL hD') from by
      rw [AutPSL.conjAut_toGL, hhD'.2]]
    rw [mul_assoc (MulAut.conj q), ← map_mul (conjAut (m' + 2 + 1) K), ← hX]
  have hXcomm : X * SpecialLinearGroup.toGL (AutPSL.rootInv (m := m' + 2) hm1) =
      SpecialLinearGroup.toGL (AutPSL.rootInv (m := m' + 2) hm1) * X := by
    rw [hX]
    have hhcomm : SpecialLinearGroup.toGL hD' *
        SpecialLinearGroup.toGL (AutPSL.rootInv (m := m' + 2) hm1) =
        SpecialLinearGroup.toGL (AutPSL.rootInv (m := m' + 2) hm1) *
          SpecialLinearGroup.toGL hD' := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subgroup.mem_centralizer_singleton_iff.mp
        (leviSL_le_centralizer (K := K) hm1 hhD'.1)
    calc SpecialLinearGroup.toGL hD' * D *
          SpecialLinearGroup.toGL (AutPSL.rootInv (m := m' + 2) hm1)
        = SpecialLinearGroup.toGL hD' *
            (D * SpecialLinearGroup.toGL (AutPSL.rootInv (m := m' + 2) hm1)) := by group
      _ = SpecialLinearGroup.toGL hD' *
            (SpecialLinearGroup.toGL (AutPSL.rootInv (m := m' + 2) hm1) * D) := by rw [hD1]
      _ = (SpecialLinearGroup.toGL hD' *
            SpecialLinearGroup.toGL (AutPSL.rootInv (m := m' + 2) hm1)) * D := by group
      _ = (SpecialLinearGroup.toGL (AutPSL.rootInv (m := m' + 2) hm1) *
            SpecialLinearGroup.toGL hD') * D := by rw [hhcomm]
      _ = SpecialLinearGroup.toGL (AutPSL.rootInv (m := m' + 2) hm1) *
            (SpecialLinearGroup.toGL hD' * D) := by group
  have hXfix : conjAut (m' + 2 + 1) K X (rootInvPSL (m' + 2) K
      (show 2 ≤ m' + 2 by omega)) = rootInvPSL (m' + 2) K (show 2 ≤ m' + 2 by omega) := by
    rw [rootInvPSL]
    exact conjAut_fixes_of_comm hXcomm
  have hδQmap : (radical (K := K) (m := m' + 2) hm1).map δ.toMonoidHom =
      radical (K := K) (m := m' + 2) hm1 := by
    have hpc := CFSG.StandardType.KGSp.pCoreOf_range_inf_centralizer (ψ := δ.toMonoidHom)
      (MulEquiv.injective δ) (rootInvPSL (m' + 2) K (show 2 ≤ m' + 2 by omega))
    rw [MonoidHom.range_eq_top_of_surjective _ (MulEquiv.surjective δ), top_inf_eq,
      show (MulEquiv.toMonoidHom δ) (rootInvPSL (m' + 2) K (show 2 ≤ m' + 2 by omega)) =
        δ (rootInvPSL (m' + 2) K (show 2 ≤ m' + 2 by omega)) from rfl,
      hδz, pCoreOf_centralizer_rootInv (K := K) hm2] at hpc
    exact hpc.symm
  have hδQ : ∀ x, x ∈ radical (K := K) (m := m' + 2) hm1 →
      δ x ∈ radical (K := K) (m := m' + 2) hm1 := by
    intro x hx
    rw [← hδQmap]
    exact Subgroup.mem_map_of_mem δ.toMonoidHom hx
  have hCN : (radical (K := K) (m := m' + 2) hm1 ⊔
      leviFull (K := K) (m := m' + 2) hm1 : Subgroup (projectiveSL (m' + 2 + 1) K)) ≤
      Subgroup.normalizer ((radical (K := K) (m := m' + 2) hm1 :
        Subgroup (projectiveSL (m' + 2 + 1) K)) : Set (projectiveSL (m' + 2 + 1) K)) :=
    sup_le Subgroup.le_normalizer (leviFull_le_normalizer_radical (K := K) hm2)
  have hconjQ : ∀ c ∈ (radical (K := K) (m := m' + 2) hm1 ⊔
        leviFull (K := K) (m := m' + 2) hm1 : Subgroup (projectiveSL (m' + 2 + 1) K)),
      ∀ q ∈ radical (K := K) (m := m' + 2) hm1,
        c * q * c⁻¹ ∈ radical (K := K) (m := m' + 2) hm1 := by
    intro c hc q hq
    exact (Subgroup.le_normalizer_iff.1 hCN) c hc q hq
  refine ⟨α, hα, ?_⟩
  intro s hs l hsl
  obtain ⟨B, rfl⟩ := φEquiv.surjective l
  let Z : SpecialLinearGroup ↥P.free K := (reindexSpecialLinear e0).symm B
  let W : SpecialLinearGroup ↥P.free K :=
    ⟨XJ * (Z : Matrix ↥P.free ↥P.free K) * XJi, by
      rw [det_mul, det_mul, Z.2, mul_one]
      have hdet : XJ.det * XJi.det = 1 := by
        have h := congrArg Matrix.det hXJXJi
        rwa [det_mul, det_one] at h
      exact hdet⟩
  have hWval : ((W : SpecialLinearGroup ↥P.free K) :
      Matrix ↥P.free ↥P.free K) = XJ * (Z : Matrix ↥P.free ↥P.free K) * XJi := rfl
  have hreindexW : reindexSpecialLinear e0 W =
      InnerDiagA.conjSL (m := m') A B := by
    apply Subtype.ext
    change Matrix.reindex e0 e0 ((W : SpecialLinearGroup ↥P.free K) :
      Matrix ↥P.free ↥P.free K) =
      ((InnerDiagA.conjSL (m := m') A B : SpecialLinearGroup (Fin (m' + 1)) K) :
        Matrix (Fin (m' + 1)) (Fin (m' + 1)) K)
    rw [hWval, InnerDiagA.coe_conjSL]
    rw [← reindexAlgEquiv_apply K K e0
      (XJ * (Z : Matrix ↥P.free ↥P.free K) * XJi)]
    rw [map_mul, map_mul]
    rw [reindexAlgEquiv_apply K K e0 XJ,
      reindexAlgEquiv_apply K K e0 (Z : Matrix ↥P.free ↥P.free K),
      reindexAlgEquiv_apply K K e0 XJi]
    rw [← hAval, ← hAival]
    have hZval : ((Z : SpecialLinearGroup ↥P.free K) :
        Matrix ↥P.free ↥P.free K) =
        Matrix.reindex e0.symm e0.symm
          ((B : SpecialLinearGroup (Fin (m' + 1)) K) :
            Matrix (Fin (m' + 1)) (Fin (m' + 1)) K) := by
      rw [show Z = (reindexSpecialLinear e0).symm B from rfl]
      rfl
    rw [hZval, reindex_reindex_apply]
  have hWalpha : ((φEquiv (InnerDiagA.conjSL (m := m') A B) :
      ↥(blockLevi (K := K) (m := m' + 2) hm1)) : projectiveSL (m' + 2 + 1) K) =
      proj (m' + 2 + 1) K ((blockEmbed P.free) W) := by
    rw [show ((φEquiv (InnerDiagA.conjSL (m := m') A B) :
        ↥(blockLevi (K := K) (m := m' + 2) hm1)) : projectiveSL (m' + 2 + 1) K) =
        proj (m' + 2 + 1) K ((blockEmbed P.free)
          ((reindexSpecialLinear e0).symm (InnerDiagA.conjSL (m := m') A B))) from rfl]
    rw [show (reindexSpecialLinear e0).symm (InnerDiagA.conjSL (m := m') A B) = W from by
      apply (reindexSpecialLinear e0).injective
      rw [hreindexW, MulEquiv.apply_symm_apply]]
  have hαB : α (φEquiv B) = φEquiv (InnerDiagA.conjSL (m := m') A B) := by
    change φEquiv (cA (φEquiv.symm (φEquiv B))) =
      φEquiv (InnerDiagA.conjSL (m := m') A B)
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hWalpha' : (α (φEquiv B) : projectiveSL (m' + 2 + 1) K) =
      proj (m' + 2 + 1) K ((blockEmbed P.free) W) := by
    rw [hαB]
    exact hWalpha
  have hZalpha : proj (m' + 2 + 1) K ((blockEmbed P.free) Z) =
      ((φEquiv B : ↥(blockLevi (K := K) (m := m' + 2) hm1)) :
        projectiveSL (m' + 2 + 1) K) := rfl
  have hrad := InvPlacement.inv_blockEmbed_mul_conj_mem_radical (P := P) (K := K) X hXtri Z W hWval
  have hQmap : (proj (m' + 2 + 1) K (((blockEmbed P.free) W)⁻¹) *
      (proj (m' + 2 + 1) K
        (((CatalogueBHigherLinearAction.slConjugation (m' + 2 + 1) K) X)
          ((blockEmbed P.free) Z)))) ∈ radical (K := K) (m := m' + 2) hm1 := by
    have h := Subgroup.mem_map_of_mem (proj (m' + 2 + 1) K) hrad
    change (proj (m' + 2 + 1) K ((blockEmbed P.free) W))⁻¹ *
      (proj (m' + 2 + 1) K
        (((CatalogueBHigherLinearAction.slConjugation (m' + 2 + 1) K) X)
          ((blockEmbed P.free) Z))) ∈ (P.radical K).map (proj (m' + 2 + 1) K)
    simpa only [map_mul, map_inv] using h
  have hC1 : proj (m' + 2 + 1) K
      (((CatalogueBHigherLinearAction.slConjugation (m' + 2 + 1) K) X)
        ((blockEmbed P.free) Z)) ∈
      (radical (K := K) (m := m' + 2) hm1 ⊔
        leviFull (K := K) (m := m' + 2) hm1 : Subgroup (projectiveSL (m' + 2 + 1) K)) := by
    rw [← conjAut_proj X ((blockEmbed P.free) Z), hZalpha]
    have hmem : conjAut (m' + 2 + 1) K X (φEquiv B) ∈
        Subgroup.centralizer ({rootInvPSL (m' + 2) K (show 2 ≤ m' + 2 by omega)} :
          Set (projectiveSL (m' + 2 + 1) K)) :=
      conjAut_mem_centralizer X hm1 hXcomm (by
        rw [centralizer_rootInv_eq_sup (K := K) hm2]
        exact Subgroup.mem_sup_right (blockLevi_le_leviFull (K := K) (m := m' + 2) hm1
          (φEquiv B).2))
    rwa [centralizer_rootInv_eq_sup (K := K) hm2] at hmem
  have hQ2' : conjAut (m' + 2 + 1) K X (φEquiv B) * (α (φEquiv B))⁻¹ ∈
      radical (K := K) (m := m' + 2) hm1 := by
    have hQmap' : (α (φEquiv B) : projectiveSL (m' + 2 + 1) K)⁻¹ *
        conjAut (m' + 2 + 1) K X (φEquiv B) ∈
        radical (K := K) (m := m' + 2) hm1 := by
      rw [hWalpha', ← hZalpha, conjAut_proj X ((blockEmbed P.free) Z)]
      exact hQmap
    exact mul_inv_mem_of_inv_mul_mem_of_le_normalizer hCN hC1 hQmap'
  have hδQ2 : δ (φEquiv B) * (α (φEquiv B))⁻¹ ∈
      radical (K := K) (m := m' + 2) hm1 := by
    rw [hδX, MulAut.mul_apply]
    exact conj_mul_inv_mem_of_mem_of_le_normalizer hCN hq
      (Subgroup.mem_sup_right (blockLevi_le_leviFull (K := K) (m := m' + 2) hm1
        (α (φEquiv B)).2)) hQ2'
  have hsplitδ : δ s * (α (φEquiv B))⁻¹ =
      δ (s * ((φEquiv B : ↥(blockLevi (K := K) (m := m' + 2) hm1)) :
          projectiveSL (m' + 2 + 1) K)⁻¹) * (δ (φEquiv B) * (α (φEquiv B))⁻¹) := by
    rw [map_mul, map_inv]
    group
  change δ s * ↑(α (φEquiv B))⁻¹ ∈ radical (K := K) (m := m' + 2) hm1
  rw [hsplitδ]
  exact Subgroup.mul_mem _ (hδQ _ hsl) hδQ2

theorem kgPiecesD_rootInv {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (hm : 3 ≤ m)
    (hq : 4 ≤ m ∨ 4 ≤ Nat.card K) :
    KGND.KGPiecesD (AutPSL.inndiag : Subgroup (MulAut (projectiveSL (m + 1) K)))
      (rootInvPSL m K (by omega)) := by
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 2 := ⟨m - 2, by omega⟩
  have hm' : 1 ≤ m' := by omega
  have hm2 : 2 ≤ m' + 2 := by omega
  have hm1 : 1 ≤ m' + 2 := by omega
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨fn, -, hF⟩ := FiniteField.card K 2
  let f : ℕ := (fn : ℕ)
  have hF' : Nat.card K = 2 ^ f := by rw [Nat.card_eq_fintype_card, hF]
  have h2K : 2 ≤ Nat.card K := by
    haveI : Nontrivial K := ⟨⟨0, 1, zero_ne_one⟩⟩
    exact (Finite.one_lt_card_iff_nontrivial (α := K)).2 inferInstance
  have hf : 1 ≤ f := by
    have := fn.pos
    omega
  have hm1' : m' = 1 → 2 ≤ f := by
    intro hm'
    have hq' : 4 ≤ Nat.card K := by
      rcases hq with h | h
      · omega
      · exact h
    rw [hF'] at hq'
    by_contra hf2
    have hf1 : f ≤ 1 := by omega
    have hle : 2 ^ f ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hf1
    norm_num at hle
    omega
  have hker : (blockLeviHom (K := K) (m := m' + 2) hm1).ker ≤
      Subgroup.center (SpecialLinearGroup (Fin (m' + 1)) K) := by
    rw [show (blockLeviHom (K := K) (m := m' + 2) hm1).ker = ⊥ from
      (MonoidHom.ker_eq_bot_iff _).mpr (blockLeviHom_injective (K := K) hm1)]
    exact bot_le
  refine KGND.kgPiecesD_of_decomp (𝒟 := (AutPSL.inndiag :
      Subgroup (MulAut (projectiveSL (m' + 2 + 1) K))))
    (z := rootInvPSL (m' + 2) K hm2)
    (Q := radical (K := K) (m := m' + 2) hm1)
    (L := blockLevi (K := K) (m := m' + 2) hm1)
    (pCoreOf_centralizer_rootInv (K := K) hm2) ?_ ?_ ?_ ?_ ?_
    (isQuasisimple_blockLevi (K := K) (m := m' + 2) (by omega) hq)
    (KGND.slConjSet (m := m') (F := K) (blockLeviHom (K := K) (m := m' + 2) hm1)) ?_ ?_
  · rw [centralizer_rootInv_eq_sup (K := K) hm2]
    exact sup_le le_sup_left ((blockLevi_le_leviFull (K := K) hm1).trans le_sup_right)
  · exact commutator_centralizer_rootInv_le (K := K) (by omega)
  · exact blockLevi_le_normalizer_radical (K := K) hm2
  · exact disjoint_iff.mp (disjoint_radical_blockLevi (K := K) hm2)
  · exact commutator_radical_sup_blockLevi (K := K) (by omega) hq
  · exact KGND.largeEvenMarking_slConjSet (m := m') (F := K) hF' hf hm' hm1'
      (blockLeviHom (K := K) (m := m' + 2) hm1)
      (blockLeviHom_surjective (K := K) hm1) hker
  · exact exists_alpha_of_mem_inndiag_fix (K := K)

end KGPSL

section Tag

theorem ggRootCentKGStructTag_PSL : GGRootCentKGStructTag .PSL :=
  ggRootCentKGStructTag_PSL_of fun _ _ _ _ _ hm hq => KGPSL.kgPiecesD_rootInv hm hq

end Tag

end CFSG.StandardType

end
