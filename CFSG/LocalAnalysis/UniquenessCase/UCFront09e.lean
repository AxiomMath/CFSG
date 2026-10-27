module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09c
import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.Section8.NormalizerEscapeRankReduction
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)
open CFSG.AGLEmbedding (KFactCatalogSchreier)
open CFSG.LocalAnalysis.RankThreeUC.ProofSupport.Section8.NormalizerEscapeRankReduction
  (one_le_pRank_of_dvd)

variable {G : Type} [Group G] [Finite G]

theorem surjective_bar2 {L X : Subgroup G} (hXL : X ≤ L) (hcov : L = X ⊔ pCoreOf 2 L) :
    Function.Surjective
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hXL)) := by
  rw [← MonoidHom.range_eq_top, ← MonoidHom.map_range, Subgroup.inclusion_range]
  have h1 : X.subgroupOf L ⊔ CFSG.pCore 2 ↥L = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_of_le_left hXL,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hcov.symm
  have h2 := congrArg (Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) h1
  rwa [Subgroup.map_sup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
    (Subgroup.map_eq_bot_iff _).2 (QuotientGroup.ker_mk' _).ge, sup_bot_eq] at h2

theorem card_bar2_of_isAlt {L : Subgroup G} (hA5 : IsAlt (Bar2 L) 5) : Nat.card (Bar2 L) = 60 := by
  obtain ⟨e⟩ := hA5
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  rfl

theorem not_isSolvable_of_isAlt_bar2 {L X : Subgroup G} (hXL : X ≤ L)
    (hcov : L = X ⊔ pCoreOf 2 L) (hA5 : IsAlt (Bar2 L) 5) : ¬ Group.IsSolvable ↥X := by
  intro hX
  obtain ⟨e⟩ := hA5
  have h1 : Group.IsSolvable (Bar2 L) := Group.isSolvable_of_surjective (surjective_bar2 hXL hcov)
  have h2 : Group.IsSolvable (alternatingGroup (Fin 5)) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  have hcomm : IsMulCommutative (alternatingGroup (Fin 5)) :=
    ⟨⟨(IsSimpleGroup.comm_iff_isSolvable (G := alternatingGroup (Fin 5))).mpr h2⟩⟩
  have hcard := alternatingGroup.isMulCommutative_iff_card_le_three.mp hcomm
  simp at hcard

theorem three_dvd_card_of_isAlt_bar2 {L X : Subgroup G} (hXL : X ≤ L)
    (hcov : L = X ⊔ pCoreOf 2 L) (hA5 : IsAlt (Bar2 L) 5) : 3 ∣ Nat.card ↥X := by
  have h := Subgroup.card_dvd_of_surjective (surjective_bar2 hXL hcov)
  rw [card_bar2_of_isAlt hA5] at h
  exact (show (3 : ℕ) ∣ 60 by norm_num).trans h

theorem inf_I9_le_pCoreOf {L X H : Subgroup G} (hXL : X ≤ L) (hcov : L = X ⊔ pCoreOf 2 L)
    (hA5 : IsAlt (Bar2 L) 5) (hXH : X ≤ H) : X ⊓ I9 H ≤ pCoreOf 2 L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h60 := card_bar2_of_isAlt hA5
  obtain ⟨e⟩ := hA5
  haveI : IsSimpleGroup (Bar2 L) := e.isSimpleGroup
  have hφ := surjective_bar2 hXL hcov
  have hJ : ((I9 H).subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf, I9] at hn ⊢
    obtain ⟨j, hj, hjn⟩ := Subgroup.mem_map.1 hn
    refine Subgroup.mem_map.2 ⟨⟨g, hXH g.2⟩ * j * ⟨g, hXH g.2⟩⁻¹,
      CFSG.pPrimeCore_normal.conj_mem j hj _, ?_⟩
    rw [Subgroup.coe_subtype] at hjn
    simp [hjn]
  rcases (hJ.map _ hφ).eq_bot_or_eq_top with h | h
  · intro y hy
    have h1 := Subgroup.mem_map_of_mem
      ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hXL))
      (Subgroup.mem_subgroupOf.2 hy.2 : (⟨y, hy.1⟩ : ↥X) ∈ (I9 H).subgroupOf X)
    rw [h, Subgroup.mem_bot, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      QuotientGroup.ker_mk'] at h1
    exact (CFSG.mem_openPCoreOf_iff _).2 h1
  · exfalso
    have h1 : Nat.card (Bar2 L) ∣ Nat.card ((I9 H).subgroupOf X) := by
      rw [← Subgroup.card_top (G := Bar2 L), ← h]
      exact Subgroup.card_map_dvd _ _
    have h2 : Nat.card ((I9 H).subgroupOf X) ∣ Nat.card (I9 H) := by
      rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype]
      exact Subgroup.card_dvd_of_le inf_le_left
    have h3 : Nat.card (I9 H) = Nat.card (CFSG.pPrimeCore 3 ↥H) :=
      Subgroup.card_map_of_injective H.subtype_injective
    have hcop := CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥H)
    rw [← h3] at hcop
    rw [h60] at h1
    exact absurd (Nat.Coprime.coprime_dvd_right
      (((show (3 : ℕ) ∣ 60 by norm_num).trans h1).trans h2) hcop) (by decide)

theorem isSolvable_inf_I9 {L X H : Subgroup G} (hXL : X ≤ L) (hcov : L = X ⊔ pCoreOf 2 L)
    (hA5 : IsAlt (Bar2 L) 5) (hXH : X ≤ H) : Group.IsSolvable ↥(X ⊓ I9 H) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : IsPGroup 2 ↥(pCoreOf 2 L) := by
    rw [CFSG.openPCoreOf_eq_map_pCore]
    exact CFSG.pCore_isPGroup.map _
  haveI := (hO.to_le (inf_I9_le_pCoreOf hXL hcov hA5 hXH)).isNilpotent
  infer_instance

theorem L9_le {X H : Subgroup G} (hX : Opp 3 X = X) (hXH : X ≤ H) : L9 X H ≤ H := by
  rw [L9]
  refine iSup_le fun h => Subgroup.map_le_iff_le_comap.2 fun y hy => ?_
  rw [hX] at hy
  simpa using H.mul_mem (H.mul_mem h.2 (hXH hy)) (H.inv_mem h.2)

theorem le_L9 {X H : Subgroup G} (hX : Opp 3 X = X) : X ≤ L9 X H := by
  intro y hy
  rw [L9]
  exact Subgroup.mem_iSup_of_mem (1 : ↥H) ⟨y, by rw [hX]; exact hy, by simp⟩

theorem mem_calH9_of_strong3 (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hSch : KFactCatalogSchreier) (D : Data G) (hM : IsStronglyPEmbedded 3 D.M)
    {L X H : Subgroup G} (hLM : L ≤ D.M) (hXL : X ≤ L) (hcov : L = X ⊔ pCoreOf 2 L)
    (hA5 : IsAlt (Bar2 L) 5) (hX : Opp 3 X = X) (hH : H ≠ ⊤) (hXH : X ≤ H)
    (hHM : ¬ H ≤ D.M) : H ∈ calH9 D X := by
  have h3X := three_dvd_card_of_isAlt_bar2 hXL hcov hA5
  have hXHM : X ≤ H ⊓ D.M := le_inf hXH (hXL.trans hLM)
  have h1 : CFSG.Open.pRank 3 H ≤ 1 :=
    pRank_le_one_of_strong3 hG3 hSch D.standing.kProper hM hH hHM
      (h3X.trans (Subgroup.card_dvd_of_le hXHM)) hXHM
      (not_isSolvable_of_isAlt_bar2 hXL hcov hA5) (isSolvable_inf_I9 hXL hcov hA5 hXH)
  refine ⟨hXH, hHM, ?_⟩
  show CFSG.Open.pRank 3 (L9 X H) = 1
  exact le_antisymm ((CFSG.SectionRank.pRank_mono (by norm_num) (L9_le hX hXH)).trans h1)
    (one_le_pRank_of_dvd Nat.prime_three _ (h3X.trans (Subgroup.card_dvd_of_le (le_L9 hX))))

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
