module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuFour
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2PsuFourOne
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2NatB
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinU4Two14
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallU4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallU4Nat
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallOuter
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.MBound
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rk
import CFSG.GroupTheory.E3Params

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.QuasithinUnique.Setup.Family (binaryLin)
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.RankThreeUC (IsU4Group)
open CFSG.HardMathSupport.U4FF (disp u4RankDichotomySix_holds)

theorem w135c2_psu_four_all
    {W : Type} [CommGroup W] [Finite W]
    {Y L : Subgroup (MulAut W)} {t : MulAut W} (hW : ∀ w : W, w ^ 2 = 1)
    (hctx : Is135Context Y L) (htY : t ∈ Y) (ht2 : orderOf t = 2)
    (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {f : ℕ}
    (hlie : LieModel (↥L ⧸ Subgroup.center ↥L) .PSU 4 2 f) : W4Lem13_5Concl W Y L t := by
  classical
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
  have hLY : L ≤ Y := hctx.2.2.1
  have hYN : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).mp (w135_normal_of_ctx hctx)
  have hdisp : disp t ≤ 3 := by
    rw [CFSG.GroupTheory.mQuot_top_eq_rkIdx, Thm14_5.rkIdx_fixV_zpowers_eq_disp t] at hm
    exact hm
  have hsmall : ∀ B : ℕ, 7 ≤ B → (∀ y ∈ L, y ≠ 1 → y * y = 1 → B ≤ disp y) → False := by
    intro B hB hbig
    by_cases htL : t ∈ L
    · have := hbig t htL ht1 htt
      omega
    · have hsimpL : IsSimpleGroup ↥L :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_lieModel_isSimple_classical
          (Or.inr (Or.inl rfl)) hL'
      have hevL : Even (Nat.card ↥L) := Thm14_5.even_card_of_isU4 hL'
      have hLodd : ∀ N : Subgroup ↥L, N.Normal → Odd (Nat.card N) → N = ⊥ :=
        fun N hN hodd => Thm14_5.eq_bot_of_odd_of_isSimpleGroup hevL N hN hodd
      have htc : ∃ x ∈ L, t * x ≠ x * t := by
        by_contra hcon
        push Not at hcon
        exact ht1 (Thm14_5.eq_one_of_commute_of_isIrrOn hW hI (by rw [pow_two]; exact htt) hcon)
      obtain ⟨l, hl, k, hyL, hy1, hy2⟩ :=
        Thm14_5.exists_involution_pow_mul_conj hLodd (hYN htY) htt htc
      have hy : B ≤ disp ((t * (l⁻¹ * t * l)) ^ k) := hbig _ hyL hy1 hy2
      have : Module.Finite (ZMod 2) (Additive W) := Module.Finite.of_finite
      have hrky : disp ((t * (l⁻¹ * t * l)) ^ k) ≤ 2 * disp t :=
        Thm14_5.finrank_range_pow_mul_conj_le
          (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp binaryLin) t l k
      omega
  by_cases hf1 : f = 1
  · subst hf1
    rcases w135c2_psu_four_one_refined hU4 hirr with hnat | hcard | hbig
    · rcases hnat with hSU | hO6
      · exact w135c2_natural hctx htY ht2 hW
          (Or.inr ⟨4, Thm14_5.isSUn_natSUn_of_naturalSU4 hSU⟩)
      · exact w135c2_natural hctx htY ht2 hW
          (Or.inl ⟨6, 1, Or.inr (Or.inr (Or.inr
            (Thm14_5.isOmegaMinus_natOmegaMinus_of_naturalOmega6 hO6)))⟩)
    · exfalso
      have h4 := finU4Two14_holds W hW Y L t hctx htY ht2 hlie hcard
      omega
    · exact (hsmall 7 le_rfl hbig).elim
  · have hf2 : 2 ≤ f := by omega
    rcases u4RankDichotomySix_holds W f L hf hU4 hirr with hnat | hbig
    · rcases hnat with hSU | hO6
      · exfalso
        have h2 := Thm14_5.two_mul_le_disp_of_naturalSU4 hI hSU htt ht1 (hYN htY)
        omega
      · exact w135c2_natural hctx htY ht2 hW
          (Or.inl ⟨6, f, Or.inr (Or.inr (Or.inr
            (Thm14_5.isOmegaMinus_natOmegaMinus_of_naturalOmega6 hO6)))⟩)
    · have h6 : ∀ y ∈ L, y ≠ 1 → y * y = 1 → 6 * f ≤ disp y := fun y hy hy1 hyy => by
        simpa [disp] using hbig y hy hy1 hyy
      exact (hsmall (6 * f) (by omega) h6).elim

end CFSG.LocalAnalysis.WeakClosure81
