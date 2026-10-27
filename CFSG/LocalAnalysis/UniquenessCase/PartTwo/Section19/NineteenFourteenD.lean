module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteenR
public import CFSG.LocalAnalysis.UniquenessCase.UC6Grp
public import CFSG.CGT.Foote82.D1Steps
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09R912A5
public import CFSG.CGT.PushingUp.AlternatingFour
public import CFSG.GroupTheory.DedekindNormalizer
public import CFSG.GroupTheory.PGroup.LtInfNormalizer
public import CFSG.GroupTheory.PCoreJoin
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.Statements

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

variable {G : Type} [Group G] [Finite G]

theorem nineteen_glue_five_of_asc81b (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r)
    (h11 : R19_11At D V₀ V p L A t B r h) (hW : W7_9_1_4) (h640 : UC6.R6_40_1 D)
    (h84 : CFSG.AGLEmbedding.Asc81bEightFour)
    (Y N : Subgroup G) (hY : Y ∈ muStarSet D B) (hN : N ∈ calMOf Y ∧ N ≠ D.M) :
    R19_glue_5At D V₀ V p L A t B r h Y N hY hN := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLcal : L ∈ calC D.M := S17.calLp_subset_calC D p h.hyp.hL
  have hIM : IOf D p L ≤ D.M := IOf_le_M D p hLcal.1.le
  have hInorm : ((IOf D p L).subgroupOf D.M).Normal := IOf_normal D p hLcal
  have hBI : B ≤ IOf D p L := by
    rw [h.hB]
    exact sup_le h.hA (Subgroup.zpowers_le.mpr h.htA)
  have hBM : B ≤ D.M := hBI.trans hIM
  have hoI : S17.oUpperTwo B ≤ IOf D p L := (S17.oUpperTwo_le B).trans hBI
  have heta : ∀ R : Subgroup G, R ≤ D.M → IsPGroup 2 R → B ≤ normalizer (R : Set G) →
      pCoreOf 2 (IOf D p L) ≤ R → calMOf (D.M ⊓ normalizer (R : Set G)) = {D.M} :=
    fun R hRM hR2 hBR hOR => (h11 R ⟨hRM, hR2, hOR, hBR⟩).2
  have hYmem : Y ∈ muSet D B := hY.1
  have hYM : Y ≤ D.M := hYmem.1
  have hYN : Y ≤ N := hN.1.2
  have hBY : B ≤ Y := hYmem.2.1.ge.trans' le_sup_left
  have hNmax : IsMaxTwoLocalSubgroup N := hN.1.1
  have hNM : ¬ N ≤ D.M := fun hle => hN.2 (hNmax.2 D.M D.maxLocal.1 hle).symm
  have hNtop : N ≠ ⊤ := fun hNt => hN.2 (D.maxLocal.2 N hNmax.1 (hNt ▸ le_top))
  have hNne : pCoreOf 2 N ≠ ⊥ := UC6.pCoreOf_ne_bot_of_isTwoLocal hNmax.1
  have h914 : ∀ P : Subgroup G, P ≤ N → IsPGroup 2 P → Y ≤ normalizer (P : Set G) →
      P ≤ pCoreOf 2 Y := fun P hPN hP2 hYP =>
    hW G D.standing.simple D.standing.charTwo D.standing.kProper
      D.M (IOf D p L) B Y N D.maxLocal hIM hInorm hBM hoI heta hYM hYmem.2.1
      hYmem.2.2.1 hYmem.2.2.2
      (fun Z hZM hZ hZne hZcal hYZ => hY.2 Z ⟨hZM, hZ, hZne, hZcal⟩ hYZ)
      hYN hNM hNne P hPN hP2 hYP
  obtain ⟨S, hSdef⟩ : ∃ S : Subgroup G, S = pCoreOf 2 (N ⊓ D.M) := ⟨_, rfl⟩
  have hSle : S ≤ N ⊓ D.M := hSdef ▸ CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hS2 : IsPGroup 2 S := hSdef ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hNMS : N ⊓ D.M ≤ normalizer (S : Set G) :=
    hSdef ▸ CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hYS : Y ≤ normalizer (S : Set G) := (le_inf hYN hYM).trans hNMS
  have hQM : pCoreOf 2 N ≤ D.M :=
    (h914 _ (CFSG.LieType.BorelTits.pCoreOf_le 2 N) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
      (hYN.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N))).trans
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hYM)
  have hQS : pCoreOf 2 N ≤ S := hSdef ▸ CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 N) hQM)
    (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
  have hSne : S ≠ ⊥ := fun h0 => hNne (le_bot_iff.mp (h0 ▸ hQS))
  have hZ : ∃ Z : Subgroup G, Z ≤ normalizer (S : Set G) ∧ UniqueMax D.M Z := by
    by_cases hOI : pCoreOf 2 (IOf D p L) ≤ S
    · exact ⟨D.M ⊓ normalizer (S : Set G), inf_le_right,
        heta S (hSle.trans inf_le_right) hS2 (hBY.trans hYS) hOI⟩
    · set Q₀ := pCoreOf 2 (IOf D p L) with hQ₀
      have hQ₀2 : IsPGroup 2 Q₀ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
      have hMQ₀ : D.M ≤ normalizer (Q₀ : Set G) :=
        ((normal_subgroupOf_iff_le_normalizer hIM).mp hInorm).trans
          (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
      have hQ₀M : Q₀ ≤ D.M := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hIM
      set U := Q₀ ⊓ normalizer (S : Set G) with hU
      have hU2 : IsPGroup 2 U := hQ₀2.to_le inf_le_left
      have hYU : Y ≤ normalizer (U : Set G) :=
        (le_inf (hYM.trans hMQ₀) (hYS.trans le_normalizer)).trans
          inf_normalizer_le_normalizer_inf
      have hcov : pCoreOf 2 Y ⊔ U ≤ pCoreOf 2 (Y ⊔ U) :=
        CFSG.GroupTheory.pCoreOf_sup_le_pCoreOf_sup hU2 hYU
      refine ⟨Y ⊔ U, sup_le hYS inf_le_right, ?_⟩
      by_contra hcal
      have hmem : Y ⊔ U ∈ muSet D B := by
        refine ⟨sup_le hYM (inf_le_left.trans hQ₀M), le_antisymm ?_
          (sup_le (hBY.trans le_sup_left) (CFSG.LieType.BorelTits.pCoreOf_le 2 _)), ?_, hcal⟩
        · calc Y ⊔ U = B ⊔ (pCoreOf 2 Y ⊔ U) := by
                conv_lhs => rw [hYmem.2.1]
                rw [sup_assoc]
            _ ≤ B ⊔ pCoreOf 2 (Y ⊔ U) := sup_le_sup_left hcov _
        · exact fun h0 => hYmem.2.2.1 (le_bot_iff.mp (h0 ▸ (le_sup_left.trans hcov)))
      have hUY : U ≤ Y := le_sup_right.trans (hY.2 _ hmem le_sup_left).le
      have hQ₀NS : Q₀ ⊓ N ≤ S := hSdef ▸ CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (inf_le_inf_right _ hQ₀M |>.trans (by rw [inf_comm])) ?_ (hQ₀2.to_le inf_le_left)
      · have hSQ₀ : S ≤ normalizer (Q₀ : Set G) := (hSle.trans inf_le_right).trans hMQ₀
        have hUS : U ≤ S :=
          le_inf (le_inf inf_le_left (hUY.trans hYN)) le_rfl |>.trans (inf_le_left.trans hQ₀NS)
        refine hOI (sup_eq_left.mp (le_antisymm ?_ le_sup_left))
        by_contra hlt
        have h := CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup
          (hS2.to_sup_of_normal_right' hQ₀2 hSQ₀) (lt_of_le_of_ne le_sup_left fun he => hlt he.ge)
        rw [inf_comm, CFSG.GroupTheory.inf_sup_eq_sup_inf_of_le_normalizer le_normalizer hSQ₀,
          inf_comm] at h
        exact lt_irrefl S (h.trans_le (sup_le le_rfl hUS))
      · exact (le_inf (inf_le_right.trans hMQ₀) (inf_le_left.trans le_normalizer)).trans
          inf_normalizer_le_normalizer_inf
  obtain ⟨Z, hZS, hZU⟩ := hZ
  have hCM : ∀ C : Subgroup G, C ≤ S → C ≠ ⊥ → (C.subgroupOf S).Characteristic →
      normalizer (C : Set G) ≤ D.M := fun C hCS hC1 hchar =>
    uc22p22p_le_of_uniqueMax hZU ⟨C, hC1, hS2.to_le hCS, rfl⟩
      (hZS.trans (F09.normalizer_le_normalizer_of_char hCS hchar))
  have hcharS : (S.subgroupOf S).Characteristic := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  have hNSM : normalizer (S : Set G) ≤ D.M := hCM S le_rfl hSne hcharS
  have hNN : N ⊓ normalizer (S : Set G) = N ⊓ D.M :=
    le_antisymm (inf_le_inf_left _ hNSM) (le_inf inf_le_left hNMS)
  have hAsc : CFSG.AGLEmbedding.Asc81bHyp N S :=
    { twoRadical := ⟨hSle.trans inf_le_left, hSne, by rw [hNN, hSdef]⟩
      charTwo := D.standing.charTwo N hNmax.1
      cgs := by
        refine le_antisymm (iSup_le fun C => iSup_le fun hCS => iSup_le fun hC1 =>
          iSup_le fun hchar => ?_) ?_
        · exact le_inf inf_le_left ((le_inf inf_le_left
            (inf_le_right.trans (hCM C hCS hC1 hchar))).trans hNMS)
        · exact le_iSup_of_le S (le_iSup_of_le le_rfl (le_iSup_of_le hSne
            (le_iSup_of_le hcharS le_rfl))) }
  have hK : CFSG.Open.IsKGroup ↥N := D.standing.kProper.isKGroup N hNtop
  rcases h84 G N S hK hAsc with hO | ⟨Y', hY'N, hY'sub, ⟨e⟩⟩
  · have hSQ : ¬ S.subgroupOf N ≤ CFSG.pCore 2 ↥N := by
      intro hle
      have hSQ' : S ≤ pCoreOf 2 N := by
        rw [← Subgroup.map_subgroupOf_eq_of_le (hSle.trans inf_le_left)]
        exact Subgroup.map_mono hle
      have hSeq : S = pCoreOf 2 N := le_antisymm hSQ' hQS
      exact hNM ((hSeq ▸ CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N).trans hNSM)
    rcases CFSG.AGLEmbedding.exists_component_not_le_normalizer_or_not_le_centralizer
        hS2.comap_subtype hSQ with ⟨Lb, hLb, hLbn⟩ | hOb
    · obtain ⟨Dsub, hDsub, hbar⟩ :=
        uc22p21c_exists_calC_of_component N ((CFSG.isComponent_iff_open Lb).2 hLb)
      refine ⟨Dsub, hDsub, fun hDM => hLbn ?_,
        (CFSG.CGT.Foote82.pCoreOf_le_pCoreOf_of_isSubnormal hDsub.1).trans hQM⟩
      rw [← hbar]
      have hD : Dsub.subgroupOf N ≤ normalizer ((S.subgroupOf N : Subgroup ↥N) : Set ↥N) :=
        (Subgroup.comap_mono ((le_inf hDsub.1.le hDM).trans hNMS)).trans
          (Subgroup.le_normalizer_comap _)
      exact (Subgroup.map_mono hD).trans (Subgroup.le_normalizer_map _)
    · exact absurd hO hOb
  · exact absurd ⟨CFSG.Open.IsSubnormal.subgroupOf hY'sub,
      CFSG.CGT.PushingUpLit.InClassX.of_mulEquiv ((Subgroup.subgroupOfEquivOfLe hY'N).trans e).symm
        CFSG.CGT.PushingUp.inClassX_alternatingGroup_four⟩ (h640 N hNmax (Y'.subgroupOf N))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
