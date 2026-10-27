module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20o
public import Certificates.Certificate19954
public import Certificates.Certificate9415
import CFSG.LargeExtraspecial.S63CD4Iso
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.D4TwoSylow
import CFSG.LocalAnalysis.UniquenessCase.Lie.ExcShared
import CFSG.Quasithin.Recognition.CertPermAction
import CFSG.Quasithin.Recognition.CertTriality
import CFSG.Quasithin.Recognition.CertTrialityCheckInputs
import CFSG.Quasithin.Recognition.CertTrialityFaithful

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.AGLEmbedding.D4Two CFSG.Quasithin Subgroup
open CFSG.Blueprint (LieModel)

theorem uc22pwex_d4two_generators_not_commute : commutes genA genB = false := by decide +kernel

theorem uc22pwex_d4two_plane :
    ∃ E : Subgroup trialityGroup8, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 := by
  obtain ⟨hle, hcard, -⟩ := sylowGroup_facts
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI hP : Fact (IsPGroup 3 sylowGroup) := ⟨IsPGroup.of_card hcard⟩
  have hnc : ¬ IsCyclic sylowGroup := by
    intro hcyc
    have ha : wordGL wordA ∈ sylowGroup := Subgroup.subset_closure (by simp)
    have hb : wordGL wordB ∈ sylowGroup := Subgroup.subset_closure (by simp)
    haveI : IsMulCommutative sylowGroup :=
      (MonoidHom.id ↥sylowGroup).isMulCommutative_of_isCyclic_of_ker_le_center (by simp)
    have hab : (⟨wordGL wordA, ha⟩ : ↥sylowGroup) * ⟨wordGL wordB, hb⟩ =
        ⟨wordGL wordB, hb⟩ * ⟨wordGL wordA, ha⟩ := IsMulCommutative.is_comm.comm _ _
    have hab' := congrArg Subtype.val hab
    have hc : commutes genA genB = true := commutes_of _ _ coe_wordGL_A coe_wordGL_B hab'
    rw [uc22pwex_d4two_generators_not_commute] at hc
    exact Bool.false_ne_true hc
  obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hnc
  have hSel' := (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 S).1 hSel
  have hinj : Function.Injective
      (Subgroup.inclusion sylowGroup_le : ↥sylowGroup →* ↥trialityGroup8) :=
    Subgroup.inclusion_injective _
  refine ⟨S.map (Subgroup.inclusion sylowGroup_le), ?_, ?_⟩
  · exact uc22p20d_isElemAbelian_map _ hinj hSel'
  · rw [Subgroup.card_map_of_injective hinj, hScard]

section Witness


theorem uc22pwex_d4two_rankWit {G : Type} [Group G] (hG : LieModel G .trialityD4 0 2 1) :
    uc22p20oRankWit G 3 2 := by
  obtain ⟨e⟩ := CFSG.LargeExtraspecial.S63.nonempty_equiv_trialityGroup8 G hG
  obtain ⟨E, hE, hc⟩ := uc22pwex_d4two_plane
  exact uc22pwex_rankWit_of_equiv e E hE hc

end Witness

end CFSG.LocalAnalysis.UniquenessCase.UC22
