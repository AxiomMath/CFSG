module

public import CFSG.LocalAnalysis.StandardType.GGQ2TableBI1Frame
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameCenter
import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameTorus
import CFSG.LocalAnalysis.StandardType.GGTBRowSignedFrameSC
import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalSpLift
import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalSpSC
import CFSG.LocalAnalysis.StandardType.GGKGARank
import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosWeylSys
import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallE8
import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


theorem ggSp_recipe_frameW {m n p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hm : 4 ≤ m)
    {Q : LargeEvenRawCont} (hQ : LargeEvenRecipeSymplectic m (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic m (2 ^ n) false fun R _ I F => Q R I F ∧ GGCenterPrime p R ∧
      ∃ r, GGTorusLift p r R ∧ GGTorusWeylFrameW p r R I (CoxeterMatrix.B m) ∧
        ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
          GGTorusTBGroup p r R I L' ψ A → Nat.card ↥A = p ^ m := by
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  have : CharP K 2 := LayerCC.charP_two_of_natCard hK
  have : NeZero m := ⟨by omega⟩
  have hpq' : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
  have hp2 : p ≠ 2 := SpNS.ne_two_of_dvd_card_add_one hpq'
  have hT := ggSpNonsplitTorusInput_holds K m p (by omega) hp hpq'
  have hcp : GGCenterPrime p (LargeEvenProj (LargeEvenSpGroup K m)) := hT.2
  have hsc : GGTorusSCRank p m (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGSpSet K m)) :=
    ggTorusSCRank_sp (by omega) hp hpq'
  have hfr : GGTorusSignedFrameW p 3 (LargeEvenProj (LargeEvenSpGroup K m))
      (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGSpSet K m)) :=
    ggTorusSignedFrameW_of_signedEltSC (r := 3) hp hp2 TableBSymp.sp_I_subset_inn
      TableBSymp.center_spProj_eq_bot hcp hT.1
  have key : ∀ (L' : Type) [Group L'] [Finite L']
      (ψ : L' →* LargeEvenProj (LargeEvenSpGroup K m)) (A : Subgroup (MulAut L')),
      GGTorusTBGroup p 3 (LargeEvenProj (LargeEvenSpGroup K m))
        (LargeEvenMatConjImage (LargeEvenProjMk _) (LargeEvenGSpSet K m)) L' ψ A →
      GGWeylFrame p A (CoxeterMatrix.B m) ∧ Nat.card ↥A = p ^ m := by
    intro L' _ _ ψ A hA
    obtain ⟨k, -, hcard, hW⟩ := hfr L' ψ A hA
    obtain ⟨hψ, hker, hperf, hAe, hAI, -, -, hself⟩ := hA
    have hlow : p ^ m ≤ Nat.card ↥A := hsc L' ψ hψ hker hperf A hAe hAI hself
    have hup : Nat.card ↥A ≤ p ^ m := KGA.kga_card_le_sp hp hp2 hψ hker hperf hAe hAI
    have hpow : p ^ k = p ^ m := hcard.symm.trans (le_antisymm hup hlow)
    have hkm : k = m := Nat.pow_right_injective hp.two_le hpow
    rw [hkm] at hcard hW
    exact ⟨hW, hcard⟩
  refine ⟨K, inferInstance, inferInstance, hK, hQ, hcp, 3, ?_, ?_, ?_⟩
  · exact TableBSymp.ggTorusLift_symplecticNs_of_lt hp hp2 hpq' (by omega)
  · intro L' _ _ ψ A hA
    exact (key L' ψ A hA).1
  · intro L' _ _ ψ A hA
    exact (key L' ψ A hA).2

private theorem ggQ2_spLabelAll {t : LargeEvenLieTag} (ht : t = .B ∨ t = .C) {m : ℕ}
    (hm : 4 ≤ m) :
    LargeEvenLabelAll ⟨t, m, 1⟩ fun R _ I _ => GGCenterPrime 3 R ∧
      ∃ r, GGTorusLift 3 r R ∧ GGTorusWeylFrameW 3 r R I (CoxeterMatrix.B m) ∧
        ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
          GGTorusTBGroup 3 r R I L' ψ A → Nat.card ↥A = 3 ^ Fintype.card (Fin m) := by
  intro Q hQ
  rcases ht with rfl | rfl <;> dsimp only [LargeEvenRawDatum] at hQ ⊢
  · simpa only [Fintype.card_fin] using
      ggSp_recipe_frameW (m := m) (n := 1) (p := 3) (by norm_num) (by norm_num) hm hQ
  · simpa only [Fintype.card_fin] using
      ggSp_recipe_frameW (m := m) (n := 1) (p := 3) (by norm_num) (by norm_num) hm hQ

theorem ggQ2TableBI1FailOn_sp : GGQ2TableBI1FailOn GGQ2TBSpLabel := by
  refine ggQ2TableBI1FailOn_of_frames (fun lab hlab => Or.inr (Or.inl hlab)) ?_
  intro lab hlab hq2 hsp
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl4⟩ := hsp
  dsimp only at ht hl4
  have hn1 : 1 ≤ n := hlab.1
  have hn : n = 1 := by
    have h2 : n < 2 := hq2
    omega
  subst hn
  have hW : GGQ2LabelWeyl ⟨t, l, 1⟩ (CoxeterMatrix.B l) := by
    rcases ht with ht | ht <;> simp only [GGQ2LabelWeyl, ht] <;>
      exact ⟨Equiv.refl _, rfl⟩
  have hAll : LargeEvenLabelAll ⟨t, l, 1⟩ fun R _ I _ => GGCenterPrime 3 R ∧
      ∃ r, GGTorusLift 3 r R ∧ GGTorusWeylFrameW 3 r R I (CoxeterMatrix.B l) ∧
        ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
          GGTorusTBGroup 3 r R I L' ψ A → Nat.card ↥A = 3 ^ Fintype.card (Fin l) := by
    rcases ht with ht | ht
    · subst ht
      exact ggQ2_spLabelAll (t := .B) (Or.inl rfl) (by omega)
    · subst ht
      exact ggQ2_spLabelAll (t := .C) (Or.inr rfl) (by omega)
  exact ⟨Fin l, inferInstance, inferInstance, CoxeterMatrix.B l, CartanMatrix.B l, hW,
    CFSG.TwoNodeSmall.pws_ggIsWeylMatrix_B l (by omega), ggIntCartan_B l,
    SecFiveRootRefl.entries_B l, SecFiveRootRefl.cartanTree_B l (by omega),
    by rw [CartanMatrix.B_det (by omega)]; decide,
    hAll.mono fun _ _ _ _ ⟨hcp, r, hl, hf, hc⟩ => ⟨hcp, r, r, Nat.le_succ r, hl, hf, hc⟩⟩

end CFSG.StandardType

end
