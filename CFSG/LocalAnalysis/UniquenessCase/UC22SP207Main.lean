module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2014h
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207L2
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207U3
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Sp6
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Omega8
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Central
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Sz
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207RankTwoCl
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207RankTwoExc
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Prod
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207Linear
import CFSG.LocalAnalysis.UniquenessCase.Lie.SL3Cover
import CFSG.Adapters.LieModelSimple

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.Blueprint (LieModel)

private theorem uc22sp207_linear_of_lieModel {X : Type} [Group X] [Finite X] {m n : ℕ}
    (hm : m = 3 ∨ m = 4) (hn : 2 < n) (h : LieModel X .PSL m 2 n) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {Y : Subgroup X} (hY : IsParabolicTwo X Y) (hYp : IsStronglyPEmbedded p Y) :
    ¬ 2 ^ n ≡ 1 [MOD p] ∧
      Nonempty (↥(Opp p (⊤ : Subgroup (Bar2 Y))) ≃*
        CFSG.Open.StatedSL (m - 1) (GaloisField 2 n)) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := LinearCover.exists_mulEquiv_projectiveSL_of_lieModel h
  have : CharP K 2 := uc22pwlie_charP_two hK
  refine uc22sp207_linear hm hn hK (e.symm.toMonoidHom.comp (LinearFlag.proj m K))
    (e.symm.surjective.comp (LinearFlag.proj_surjective m K)) (fun A hA => ?_) hp hp2 hY hYp
  exact LinearFlag.scalars_le_center m K (by simpa using hA)


theorem uc22sp207_strongParab207 :
    StrongParab207 := by
  intro X _ _ hs hX p hp hp2 Y hY hYp
  have hns : NoStrongParabolic X → False := fun h => h p hp hp2 Y hY hYp
  have hcl : HasCentralLongest X → False := fun h => hns (uc22sp207_noStrongParabolic h)
  have hnab : ∃ a b : X, a * b ≠ b * a := by
    by_contra hab
    push Not at hab
    have : Y.Normal := ⟨fun y hy g => by rwa [hab g y, mul_inv_cancel_right]⟩
    exact hYp.not_dvd_card_of_normal_le le_rfl hYp.2.1
  have hodd : ¬ 2 ∣ Nat.card (center X) :=
    uc22p20l_not_two_dvd_card_center hX (MonoidHom.id _) Function.injective_id fun _ hz => hz
  rcases hs with ⟨n, hn, h | h | h | h | h | h | h | h | h | h | h | h | h | h⟩ |
      h | h | h | h | h | ⟨n, hn, h⟩ | h
  · exact (hcl (uc22sp207_hasCentralLongest_Sz h)).elim
  · exact (hcl (uc22sp207_hasCentralLongest_L2 h)).elim
  · obtain ⟨hq, -⟩ := uc22p20g_qs_L3 hnab hn h
    have hZ := uc22p20g_center_bot_of_simple hq
      (LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h)
    exact ⟨3, n, by norm_num, by norm_num, hn, hq, LieModel.quotient_center hZ h,
      uc22sp207_linear_of_lieModel (Or.inl rfl) hn h hp hp2 hY hYp⟩
  · exact (hcl (uc22sp207_hasCentralLongest_U3 h)).elim
  · obtain ⟨hq, -⟩ := uc22p20g_qs_L4 hnab hn h
    have hZ := uc22p20g_center_bot_of_simple hq
      (LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h)
    exact ⟨4, n, by norm_num, le_rfl, hn, hq, LieModel.quotient_center hZ h,
      uc22sp207_linear_of_lieModel (Or.inr rfl) hn h hp hp2 hY hYp⟩
  · exact (hns (uc22sp207_noStrongParabolic_U4 h)).elim
  · exact (hns (uc22sp207_noStrongParabolic_G2 h)).elim
  · exact (hns (uc22sp207_noStrongParabolic_3D4 h)).elim
  · exact (hns (uc22sp207_noStrongParabolic_2F4 h)).elim
  · exact (hns (uc22sp207_noStrongParabolic_Sp4 h)).elim
  · obtain ⟨K, _, _, _, α, hK, hα, hαc⟩ := uc22pwI3_exists_cover h.1 hn h.2
    exact ⟨3, n, by norm_num, by norm_num, hn, h.1, h.2,
      uc22sp207_linear (Or.inl rfl) hn hK α hα hαc hp hp2 hY hYp⟩
  · exact (hcl (uc22sp207_hasCentralLongest_SU3 hodd h)).elim
  · exact (hcl (uc22sp207_hasCentralLongest_Sp6 h)).elim
  · exact (hcl (uc22sp207_hasCentralLongest_Omega8m h)).elim
  · exact (hns (uc22sp207_noStrongParabolic_U4 h)).elim
  · exact (hns (uc22sp207_noStrongParabolic_U5 h)).elim
  · exact (hcl (uc22sp207_hasCentralLongest_Omega8m h)).elim
  · exact (hns (uc22sp207_noStrongParabolic_3D4 h)).elim
  · exact (hns (uc22sp207_noStrongParabolic_3D4 h)).elim
  · exact (hcl (uc22sp207_hasCentralLongest_szL2Product h)).elim
  · exact (hcl (uc22sp207_hasCentralLongest_centralSquare hX h)).elim

end CFSG.LocalAnalysis.UniquenessCase.UC22
