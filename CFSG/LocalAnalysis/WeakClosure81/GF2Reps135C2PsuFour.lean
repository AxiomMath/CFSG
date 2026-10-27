module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFDefs
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2NatB
import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSUCover
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallU4Rank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallU4Nat
import CFSG.GroupTheory.E3Params
import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KS.ExactSU
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.RankThreeUC (IsU4Group)
open CFSG.HardMathSupport.U4FF (disp u4RankDichotomySix_holds)
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSExact
  (exists_twistedA_of_statedClassicalModel_PSU)

theorem w135c2_psu_four_center_eq_bot
    {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}
    (hctx : Is135Context Y L) {f : ℕ}
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 4 2 f) : Subgroup.center ↥L = ⊥ := by
  classical
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun g : MulAut W => (g : W → W)) DFunLike.coe_injective
  haveI : Group.IsPerfect ↥L := (hctx.2.2.2.2.1 : CFSG.IsQuasisimple ↥L).1
  have hodd : Odd (Nat.card (Subgroup.center ↥L)) := w135_odd_card_center hctx
  obtain ⟨⟨-, hf, hm, hq⟩, K, hKf, hKfin, hK, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel hlie (by decide)
  letI := hKf
  letI := hKfin
  obtain ⟨φ, -, -, hφmap⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.S15.GN15.exists_su_cover hodd hK hf hm hq e
  have hcard : Nat.card ((StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (2 ^ f) K)) = 1 := by
    rw [(CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hK (by norm_num)).2.2]
    have hodd1 : Odd (2 ^ f + 1) := (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
    have h2 : Nat.Coprime 2 (2 ^ f + 1) := Nat.coprime_two_left.2 hodd1
    simpa using Nat.Coprime.pow_left 2 h2
  rw [← hφmap, Subgroup.eq_bot_of_card_eq _ hcard, Subgroup.map_bot]

theorem w135c2_psu_four_isU4Group {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {f : ℕ}
    (hL : LieModel ↥L .PSU 4 2 f) : IsU4Group f L := by
  have hC := CFSG.Blueprint.LieModel.statedClassicalModel hL (by decide)
  obtain ⟨q, hv, hp, hqe, ⟨φ⟩⟩ := exists_twistedA_of_statedClassicalModel_PSU (m := 3) hC
  exact ⟨⟨_, hv⟩, ⟨q, hp, hqe, rfl⟩, ⟨φ⟩⟩

theorem w135c2_psu_four_inner
    {W : Type} [CommGroup W]
    [Finite W] {Y L : Subgroup (MulAut W)} {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (htL : t ∈ L) (ht2 : orderOf t = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {f : ℕ}
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 4 2 f) : W4Lem13_5Concl W Y L t := by
  classical
  have htY : t ∈ Y := hctx.2.2.1 htL
  have hZ := w135c2_psu_four_center_eq_bot hctx hlie
  have hL' : LieModel ↥L .PSU 4 2 f := CFSG.Blueprint.LieModel.of_quotient_center hZ hlie
  have hU4 : IsU4Group f L := w135c2_psu_four_isU4Group hL'
  have hf : 1 ≤ f := hlie.admissible.2.1
  have hI := hctx.2.2.2.2.2
  have hirr : CFSG.LocalAnalysis.RankThreeUC.IsIrrOn L := fun J hJ => hI.2.2.2 J hJ bot_le le_top
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun g : MulAut W => (g : W → W)) DFunLike.coe_injective
  haveI : Fact (∀ s : W, s * s = 1) := ⟨fun s => by rw [← pow_two]; exact hW s⟩
  have htt : t * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rwa [ht2, pow_two] at h1
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  have hdisp : disp t ≤ 3 := by
    rw [CFSG.GroupTheory.mQuot_top_eq_rkIdx, Thm14_5.rkIdx_fixV_zpowers_eq_disp t] at hm
    exact hm
  rcases u4RankDichotomySix_holds W f L hf hU4 hirr with hnat | hbig
  · rcases hnat with hSU | hO6
    · have h2 := Thm14_5.two_mul_le_disp_of_naturalSU4 hI hSU htt ht1
        (Subgroup.le_normalizer htL)
      obtain rfl : f = 1 := by omega
      exact w135c2_natural hctx htY ht2 hW
        (Or.inr ⟨4, Thm14_5.isSUn_natSUn_of_naturalSU4 hSU⟩)
    · exact w135c2_natural hctx htY ht2 hW
        (Or.inl ⟨6, f, Or.inr (Or.inr (Or.inr
          (Thm14_5.isOmegaMinus_natOmegaMinus_of_naturalOmega6 hO6)))⟩)
  · exfalso
    have h6 : 6 * f ≤ disp t := by simpa [disp] using hbig t htL ht1 htt
    omega

end CFSG.LocalAnalysis.WeakClosure81
