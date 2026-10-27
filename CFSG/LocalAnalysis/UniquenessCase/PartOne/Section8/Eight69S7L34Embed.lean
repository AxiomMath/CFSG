module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFactsNineteen
public import CFSG.LocalAnalysis.UniquenessCase.UC6K591Defs
import CFSG.Adapters.GeneralizedFitting
import CFSG.GroupTheory.ConjNormalFaithful
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.Blueprint (LieModel)

theorem genFittingFStar_eq_and_centralizer_eq_bot {Q : Type} [Group Q] [Finite Q]
    {Y : Subgroup Q} (hY : genFittingFStar Q ≤ Y) [IsSimpleGroup ↥Y]
    (hnab : ∃ a b : ↥Y, a * b ≠ b * a) :
    genFittingFStar Q = Y ∧ Subgroup.centralizer (Y : Set Q) = ⊥ := by
  let F : Subgroup Q := genFittingFStar Q
  have hFn : F.Normal := CFSG.ComponentClassification.GeneralizedFitting.normal Q
  have hsc : Subgroup.centralizer (F : Set Q) ≤ F :=
    CFSG.Adapters.generalized_fitting_self_centralizing Q
  have hFne : F ≠ ⊥ := by
    intro hbot
    have htop : (⊤ : Subgroup Q) ≤ ⊥ := by
      have hcent : Subgroup.centralizer ((⊥ : Subgroup Q) : Set Q) = ⊤ :=
        Subgroup.centralizer_eq_top_iff_subset.mpr (by simp)
      have h := hsc
      rw [hbot, hcent] at h
      exact h
    obtain ⟨a, b, hab⟩ := exists_pair_ne ↥Y
    refine hab (Subtype.ext ?_)
    exact (Subgroup.mem_bot.mp (htop (Subgroup.mem_top (a : Q)))).trans
      (Subgroup.mem_bot.mp (htop (Subgroup.mem_top (b : Q)))).symm
  have hFY : F = Y := by
    have hnorm : (F.subgroupOf Y).Normal := hFn.subgroupOf Y
    rcases CFSG.eq_bot_or_eq_top_of_normal (F.subgroupOf Y) hnorm with h | h
    · refine absurd ?_ hFne
      refine le_antisymm ?_ bot_le
      intro f hf
      have hmem : (⟨f, hY hf⟩ : ↥Y) ∈ F.subgroupOf Y := Subgroup.mem_subgroupOf.mpr hf
      rw [h] at hmem
      exact Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hmem))
    · exact le_antisymm hY (Subgroup.subgroupOf_eq_top.mp h)
  refine ⟨hFY, ?_⟩
  have hscY : Subgroup.centralizer (Y : Set Q) ≤ Y := by
    rwa [hFY] at hsc
  have hcenter : Subgroup.center ↥Y = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥Y) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  refine le_antisymm ?_ bot_le
  intro x hx
  have hxY : x ∈ Y := hscY hx
  have hxZ : (⟨x, hxY⟩ : ↥Y) ∈ Subgroup.center ↥Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hx) (y : Q) y.2)
  have hx1 : (⟨x, hxY⟩ : ↥Y) = 1 := by
    rw [hcenter] at hxZ
    exact Subgroup.mem_bot.mp hxZ
  exact Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val hx1)

theorem exists_injective_mulAut_of_genFittingFStar_le {Q : Type} [Group Q] [Finite Q]
    {Y : Subgroup Q} (hY : genFittingFStar Q ≤ Y) [IsSimpleGroup ↥Y]
    (hnab : ∃ a b : ↥Y, a * b ≠ b * a) : ∃ φ : Q →* MulAut ↥Y, Function.Injective φ := by
  obtain ⟨hFY, hC⟩ := genFittingFStar_eq_and_centralizer_eq_bot hY hnab
  have hYn : Y.Normal := hFY ▸ CFSG.ComponentClassification.GeneralizedFitting.normal Q
  exact ⟨@MulAut.conjNormal Q _ Y hYn,
    @Subgroup.conjNormal_injective_of_centralizer_eq_bot Q _ Y hYn hC⟩

theorem not_seven_dvd_card_of_lieModel_tits (hK : UCK.KTits) (hT : PartTwo.S19.K_TitsOddPrimes)
    {Q : Type} [Group Q] [Finite Q] {Y : Subgroup Q} (hY : genFittingFStar Q ≤ Y)
    (h : LieModel ↥Y .Tits 0 2 1) : ¬ 7 ∣ Nat.card Q := by
  obtain ⟨hYs, hnab⟩ := hK ↥Y h
  obtain ⟨hFY, hC⟩ := @genFittingFStar_eq_and_centralizer_eq_bot Q _ _ Y hY hYs hnab
  intro h7
  have hTits : CFSG.LocalAnalysis.UniquenessCase.UC22.F10.IsTits10 ↥(genFittingFStar Q) := by
    show LieModel ↥(genFittingFStar Q) .Tits 0 2 1
    rw [hFY]
    exact h
  have hcen : Subgroup.centralizer (genFittingFStar Q : Set Q) = ⊥ := by
    rw [hFY]
    exact hC
  have hq := hT Q hTits hcen 7 Nat.prime_seven (by norm_num) h7
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

end
