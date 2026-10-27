module

public import CFSG.Quasithin.H13.U5ParPointQuot
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieLab
public import CFSG.Foundations.SteinbergCADefinitionNodes

public section

namespace CFSG.Quasithin.H13.U5Par

open Matrix Subgroup CFSG.Open CFSG.Quasithin CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.Quasithin.H13.Sec53F.Unit
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.Stroth

variable {f : ℕ} {K : Type} [Field K]

theorem map_u5PtP_of_map_hypProjUnitriangular (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    {θ : MulAut (hypPSU h 2 1)}
    (hθ : (hypProjUnitriangular h 2 1).map θ.toMonoidHom = hypProjUnitriangular h 2 1) :
    (u5PtP h).map θ.toMonoidHom = u5PtP h := by
  refine (CFSG.Quasithin.H13.F431.AG.mem_autStab_iff_map_eq θ (u5PtP h)).1 ?_
  exact CFSG.Quasithin.H13.F431.Un.OL5.autStab_U_le_Pt h hf
    ((CFSG.Quasithin.H13.F431.AG.mem_autStab_iff_map_eq θ
      (hypProjUnitriangular h 2 1)).2 hθ)

theorem two_dvd_card_modO2_perfectCore_u5PtP (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f) :
    2 ∣ Nat.card (ModO2 (perfectCore (u5PtP h))) := by
  obtain ⟨e⟩ := nonempty_modO2_perfectCore_u5PtP_equiv h hf
  have hcard : Nat.card (ModO2 (perfectCore (u5PtP h))) = Nat.card ↥(hypSU h 1 1) :=
    (Nat.card_congr e.toEquiv).trans (Nat.card_congr (N₂equiv h).toEquiv).symm
  rw [hcard]
  have hdvd := Subgroup.card_subgroup_dvd_card (hypUnitriangular h 1 1)
  rw [card_hypUnitriangular h (r := 1) (ε := 1) (by norm_num)] at hdvd
  have h2 : 2 ∣ (2 ^ f) ^ 3 := by
    rw [← pow_mul]
    simpa using Nat.pow_dvd_pow 2 (m := 1) (n := f * 3) (by omega)
  exact dvd_trans h2 hdvd

theorem lieModel_modO2_perfectCore_u5PtP (h : UnitaryFieldData 2 2 K) :
    CFSG.Blueprint.LieModel (ModO2 (perfectCore (u5PtP h))) .PSU 3 2 2 := by
  haveI := h.finite
  have hcardZ : Nat.card ↥(hypScalars h 1 1) = 1 := by
    rw [card_hypScalars h (r := 1) (ε := 1) (by norm_num)]
    norm_num
  have hbot : hypScalars h 1 1 = ⊥ := Subgroup.eq_bot_of_card_eq _ hcardZ
  let eC : hypSU h 1 1 ≃* hypPSU h 1 1 :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hbot.symm)
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := 1) (ε := 1) h
  let eP : hypPSU h 1 1 ≃* StatedProj (StatedSU 3 (2 ^ 2) K) :=
    hypPSUEquivStatedProj (r := 1) (ε := 1) h hR (by norm_num)
  obtain ⟨e1⟩ := nonempty_modO2_perfectCore_u5PtP_equiv h (by norm_num)
  let e : ModO2 (perfectCore (u5PtP h)) ≃* StatedProj (StatedSU 3 (2 ^ 2) K) :=
    e1.trans ((N₂equiv h).symm.trans (eC.trans eP))
  have hKcard : Nat.card K = (2 ^ 2) ^ 2 := by
    rw [h.card]
    norm_num
  refine Or.inl ⟨by decide, ⟨Nat.prime_two, by norm_num, le_rfl, by norm_num⟩,
    K, inferInstance, h.finite, hKcard, ⟨e⟩⟩

theorem isQuasisimple_modO2_perfectCore_u5PtP (h : UnitaryFieldData 2 2 K) :
    IsQuasisimple (ModO2 (perfectCore (u5PtP h))) := by
  obtain ⟨hq, -⟩ := CFSG.AGLEmbedding.LeviBlock.hypSU_facts_of_three_le
    (s := 1) (ε := 1) h (by norm_num) (by norm_num)
  have hq' : CFSG.IsQuasisimple ↥(hypSU h 1 1) :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff _).2.2.1.mpr hq
  obtain ⟨e⟩ := nonempty_modO2_perfectCore_u5PtP_equiv h (by norm_num)
  exact CFSG.IsQuasisimple.of_mulEquiv (e.trans (N₂equiv h).symm) hq'

end CFSG.Quasithin.H13.U5Par
