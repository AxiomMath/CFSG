module

public import CFSG.LocalAnalysis.StandardType.GGSixRootCentNotExcRows
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionFlatSeitzExc
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.Tools
public import CFSG.Holt.Centralizer
public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtFusion
public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtInner
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreL34
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Cover
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Esc
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMain
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreePerf
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FF
public import CFSG.LocalAnalysis.AGLEmbeddingD2.L34BetaHPara
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.PairFacts
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.FixedBlock
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightBridge
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TightModuleAux
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.AltSixBound
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.Frattini
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.Socle
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Hall
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

open scoped commutatorElement

section ShadowGeneric

variable {W : Type} [Group W] [Finite W] {p : ℕ} {H E : Subgroup W}

theorem ggShadow_exists_derivedSeries_le
    (hperf : ∀ P : Subgroup W, ⁅P, P⁆ = P → P ≤ CFSG.generalizedFitting W) :
    ∃ k : ℕ, derivedSeries ↥H k ≤ (CFSG.generalizedFitting W).subgroupOf H := by
  obtain ⟨k, hk⟩ :=
    CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.exists_isPerfect_derivedSeries ↥H
  refine ⟨k, ?_⟩
  have hD : ⁅derivedSeries ↥H k, derivedSeries ↥H k⁆ = derivedSeries ↥H k :=
    Subgroup.isPerfect_iff.mp hk
  have hP : ⁅(derivedSeries ↥H k).map H.subtype, (derivedSeries ↥H k).map H.subtype⁆ =
      (derivedSeries ↥H k).map H.subtype := by
    rw [← Subgroup.map_commutator (f := H.subtype), hD]
  exact (Subgroup.map_le_iff_le_comap (f := H.subtype)).mp (hperf _ hP)

private theorem ggShB_quot_ker_isSolvable
    (hperf : ∀ P : Subgroup W, ⁅P, P⁆ = P → P ≤ CFSG.generalizedFitting W) :
    Group.IsSolvable
      (↥H ⧸ ((QuotientGroup.mk' (CFSG.generalizedFitting W)).comp H.subtype).ker) := by
  have : (CFSG.generalizedFitting W).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  obtain ⟨k, hk⟩ := ggShadow_exists_derivedSeries_le hperf
  have hEq : ((QuotientGroup.mk' (CFSG.generalizedFitting W)).comp H.subtype).ker =
      (CFSG.generalizedFitting W).subgroupOf H := by
    ext x
    rw [ggMem_ker_mk_comp_subtype, Subgroup.mem_subgroupOf]
  have hk' : derivedSeries ↥H k ≤
      ((QuotientGroup.mk' (CFSG.generalizedFitting W)).comp H.subtype).ker := by
    rw [hEq]
    exact hk
  refine (Group.isSolvable_def _).mpr ⟨k, ?_⟩
  rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective
      ((QuotientGroup.mk' (CFSG.generalizedFitting W)).comp H.subtype).ker) k,
    Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  exact hk'

theorem ggShadow_not_isSolvable
    (hperf : ∀ P : Subgroup W, ⁅P, P⁆ = P → P ≤ CFSG.generalizedFitting W)
    (hL : LargeEvenLayer (⊤ : Subgroup (GGHypQuot H)) ≠ ⊥) :
    ¬ Group.IsSolvable ↥(H.subgroupOf (CFSG.generalizedFitting W)) := by
  intro hX
  have : (CFSG.generalizedFitting W).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  set N : Subgroup ↥H :=
    ((QuotientGroup.mk' (CFSG.generalizedFitting W)).comp H.subtype).ker with hNdef
  have hNsolv : Group.IsSolvable ↥N :=
    Group.isSolvable_of_isSolvable_injective
      (f := (ggSubgroupOfEquivKer H (CFSG.generalizedFitting W)).symm.toMonoidHom)
      (ggSubgroupOfEquivKer H (CFSG.generalizedFitting W)).symm.injective
  have hQ : Group.IsSolvable (↥H ⧸ N) := ggShB_quot_ker_isSolvable hperf
  exact ggNot_isSolvable_of_layer_ne_bot hL (Group.isSolvable_of_subgroup_quotient N)

theorem ggShadow_card_quotComponent_dvd
    (hperf : ∀ P : Subgroup W, ⁅P, P⁆ = P → P ≤ CFSG.generalizedFitting W)
    {C : Subgroup (GGHypQuot H)} (hC : CFSG.Assembly.IsComponentOf C ⊤) :
    Nat.card ↥C ∣ Nat.card ↥(H.subgroupOf (CFSG.generalizedFitting W)) := by
  have : (CFSG.generalizedFitting W).Normal :=
    CFSG.LocalCores.generalized_fitting_characteristic.2
  set N : Subgroup ↥H :=
    ((QuotientGroup.mk' (CFSG.generalizedFitting W)).comp H.subtype).ker with hNdef
  obtain ⟨k, hk⟩ := ggShadow_exists_derivedSeries_le hperf
  have hEq : N = (CFSG.generalizedFitting W).subgroupOf H := by
    rw [hNdef]
    ext x
    rw [ggMem_ker_mk_comp_subtype, Subgroup.mem_subgroupOf]
  have hk' : derivedSeries ↥H k ≤ N := by
    rw [hEq]
    exact hk
  set Q : Subgroup ↥H := CFSG.pCore 2 ↥H with hQdef
  set π : ↥H →* GGHypQuot H := QuotientGroup.mk' Q with hπ
  have hCN : C ≤ N.map π := by
    have h1 := ggLe_derivedSeries_of_perfect (ggComponent_perfect hC) k
    rw [← map_derivedSeries_eq (QuotientGroup.mk'_surjective Q) k] at h1
    exact h1.trans (Subgroup.map_mono hk')
  calc Nat.card ↥C ∣ Nat.card ↥(N.map π) := Subgroup.card_dvd_of_le hCN
    _ ∣ Nat.card ↥N := Subgroup.card_map_dvd (H := N) π
    _ = Nat.card ↥(H.subgroupOf (CFSG.generalizedFitting W)) :=
      Nat.card_congr (ggSubgroupOfEquivKer H (CFSG.generalizedFitting W)).symm.toEquiv

private theorem ggShB_isQuasisimple_of_simple {G : Type} [Group G] [IsSimpleGroup G]
    (hns : ¬ Group.IsSolvable G) : CFSG.Open.IsQuasisimple G := by
  have hnab : ∃ a b : G, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact hns (Group.isSolvable_of_comm fun a b => hcon a b)
  have hc : Subgroup.center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      apply hab
      have hmem : ⁅a, b⁆ ∈ commutator G :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    · exact h
  · have e : G ⧸ Subgroup.center G ≃* G :=
      (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
    exact (MulEquiv.isSimpleGroup_congr e).mpr inferInstance

private noncomputable def ggShB_quotCenterCongr {G G' : Type} [Group G] [Group G']
    (e : G ≃* G') : (G ⧸ Subgroup.center G) ≃* (G' ⧸ Subgroup.center G') :=
  QuotientGroup.congr (Subgroup.center G) (Subgroup.center G') e (Subgroup.map_center_eq e)

theorem ggShadow_exists_component_of_simple
    (hs : IsSimpleGroup ↥(commutator ↥(H.subgroupOf (CFSG.generalizedFitting W))))
    (hns : ¬ Group.IsSolvable ↥(H.subgroupOf (CFSG.generalizedFitting W))) :
    ∃ C : Subgroup ↥(H ⊓ CFSG.generalizedFitting W), CFSG.Open.IsComponentOf C ⊤ ∧
      Nonempty (↥C ⧸ Subgroup.center ↥C ≃*
        ↥(commutator ↥(H.subgroupOf (CFSG.generalizedFitting W)))) := by
  set K := CFSG.generalizedFitting W with hKdef
  set M : Subgroup W := ⁅H ⊓ K, H ⊓ K⁆ with hMdef
  let eM : ↥M ≃* ↥(commutator ↥(H.subgroupOf K)) := ggInfCommutatorEquiv H K
  have hMs : IsSimpleGroup ↥M := eM.isSimpleGroup
  have hX'ns : ¬ Group.IsSolvable ↥(commutator ↥(H.subgroupOf K)) :=
    fun hsolv => hns (ggIsSolvable_of_commutator hsolv)
  have hMns : ¬ Group.IsSolvable ↥M := fun hsolv =>
    hX'ns (Group.isSolvable_of_isSolvable_injective (f := eM.symm.toMonoidHom)
      eM.symm.injective)
  have hMq : CFSG.Open.IsQuasisimple ↥M := ggShB_isQuasisimple_of_simple (G := ↥M) hMns
  have hMA : M ≤ H ⊓ K := Subgroup.commutator_le_self (H ⊓ K)
  have hMsub : CFSG.Assembly.IsSubnormal M (H ⊓ K) :=
    (CFSG.Assembly.IsSubnormal.iff_subgroupOf hMA).2
      (Subgroup.Normal.isSubnormal (ggRCS_commutator_subgroupOf_normal (H ⊓ K)))
  have hCW : CFSG.Assembly.IsComponentOf M (H ⊓ K) := ⟨hMA, hMsub, hMq⟩
  have hCtop : CFSG.Open.IsComponentOf (M.subgroupOf (H ⊓ K)) ⊤ :=
    ggRCS_isComponentOf_subgroupOf ((CFSG.Assembly.isComponentOf_iff_open).1 hCW) hMA le_rfl
  obtain ⟨e⟩ := ggSeitzExc_component_quot_equiv hs hX'ns hCW
  exact ⟨M.subgroupOf (H ⊓ K), hCtop,
    ⟨(ggShB_quotCenterCongr (Subgroup.subgroupOfEquivOfLe hMA)).trans e⟩⟩

theorem ggShadow_component_map_eq
    (hs : IsSimpleGroup ↥(commutator ↥(H.subgroupOf (CFSG.generalizedFitting W))))
    {C : Subgroup ↥(H ⊓ CFSG.generalizedFitting W)} (hC : CFSG.Open.IsComponentOf C ⊤) :
    C.map (H ⊓ CFSG.generalizedFitting W).subtype =
      ⁅H ⊓ CFSG.generalizedFitting W, H ⊓ CFSG.generalizedFitting W⁆ := by
  exact ggSeitzExc_component_eq hs
    ((CFSG.Assembly.isComponentOf_iff_open).2 (ggRCS_isComponentOf_map_subtype hC))

theorem ggShadow_open_of_isComponentOf {C : Subgroup W}
    (hC : CFSG.Assembly.IsComponentOf C (H ⊓ CFSG.generalizedFitting W)) :
    CFSG.Open.IsComponentOf (C.subgroupOf (H ⊓ CFSG.generalizedFitting W)) ⊤ ∧
      Nat.card (↥(C.subgroupOf (H ⊓ CFSG.generalizedFitting W)) ⧸
          Subgroup.center ↥(C.subgroupOf (H ⊓ CFSG.generalizedFitting W))) =
        Nat.card (↥C ⧸ Subgroup.center ↥C) := by
  refine ⟨ggRCS_isComponentOf_subgroupOf ((CFSG.Assembly.isComponentOf_iff_open).1 hC) hC.1 le_rfl,
    ?_⟩
  exact Nat.card_congr (ggShB_quotCenterCongr (Subgroup.subgroupOfEquivOfLe hC.1)).toEquiv

end ShadowGeneric

theorem ggRCS_not_generalizedFitting_le {X : Type} [Group X] [Finite X] {V E K : Subgroup X}
    (hK : CFSG.IsComponent K) (hEK : E ≤ Subgroup.normalizer (K : Set X))
    (hE : ∀ a ∈ E, ∀ b ∈ E, Commute a b) (hEV : E ≤ V) (hKV : ¬ K ≤ V)
    [((ggRCSU V E K).subgroupOf (E ⊔ K)).Normal] :
    ¬ CFSG.generalizedFitting (ggRCSWt V E K) ≤ ggRCSTt V E K := by
  intro h
  have hperf := ggRCS_perfect_le_generalizedFitting (V := V) hK hEK hE
  set π : ↥(E ⊔ K) →* ggRCSWt V E K :=
    QuotientGroup.mk' ((ggRCSU V E K).subgroupOf (E ⊔ K)) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hKopen : CFSG.Open.IsQuasisimple ↥K := ⟨hK.1.1.commutator_eq_top, hK.1.2.1⟩
  have hKq : CFSG.Open.IsQuasisimple ↥(K.subgroupOf (E ⊔ K)) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe le_sup_right) hKopen
  have hKperf : ⁅K.subgroupOf (E ⊔ K), K.subgroupOf (E ⊔ K)⁆ = K.subgroupOf (E ⊔ K) :=
    Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hKq.1)
  have hKtilde_perf : ⁅(K.subgroupOf (E ⊔ K)).map π, (K.subgroupOf (E ⊔ K)).map π⁆ =
      (K.subgroupOf (E ⊔ K)).map π := by
    rw [← Subgroup.map_commutator (f := π), hKperf]
  have hKtilde_le : (K.subgroupOf (E ⊔ K)).map π ≤ ggRCSTt V E K :=
    (hperf _ hKtilde_perf).trans h
  have hEtilde_le : (E.subgroupOf (E ⊔ K)).map π ≤ ggRCSTt V E K :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono (E ⊔ K) (le_sup_left : E ≤ E ⊔ (K ⊓ V)))
  have hsup : (E.subgroupOf (E ⊔ K)) ⊔ (K.subgroupOf (E ⊔ K)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (le_sup_left : E ≤ E ⊔ K) (le_sup_right : K ≤ E ⊔ K),
      Subgroup.subgroupOf_self]
  have hsupmap : (E.subgroupOf (E ⊔ K)).map π ⊔ (K.subgroupOf (E ⊔ K)).map π = ⊤ := by
    rw [← Subgroup.map_sup, hsup, Subgroup.map_top, MonoidHom.range_eq_top.mpr hπs]
  have htop : ((E ⊔ (K ⊓ V)).subgroupOf (E ⊔ K)).map π = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← hsupmap]
    exact sup_le hEtilde_le hKtilde_le
  have hker' : π.ker ≤ (E ⊔ (K ⊓ V)).subgroupOf (E ⊔ K) := by
    intro w hw
    have hwU : w ∈ (ggRCSU V E K).subgroupOf (E ⊔ K) := by
      rwa [QuotientGroup.ker_mk'] at hw
    exact Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hwU)).1
  have hle : E ⊔ K ≤ V :=
    (ggAutK_le_of_map_eq_top π hker' htop).trans (sup_le hEV inf_le_right)
  exact hKV (le_sup_right.trans hle)

end CFSG.StandardType
