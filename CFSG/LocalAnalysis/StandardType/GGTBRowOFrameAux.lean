module

public import CFSG.LocalAnalysis.StandardType.GGTBRowSignedFrameSC
public import CFSG.LocalAnalysis.StandardType.GGTBRowR5Defs
public import CFSG.LocalAnalysis.StandardType.GGStdPosC13OrthSigned
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitClassical
public import CFSG.LocalAnalysis.StandardType.GGKGForkOrthRow

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly OrthExc

theorem ggO1Row_recipe_signedFrame
    {m n p : ℕ} (hp : p.Prime) (hn : 1 ≤ n)
    (hpn : p ∣ 2 ^ n - 1 ∨ (Odd m ∧ p ∣ 2 ^ n + 1)) (hm : 3 ≤ m) {Q : LargeEvenRawCont}
    (hQ : LargeEvenRecipeOmegaMinus m (2 ^ n) Q) :
    LargeEvenRecipeOmegaMinus m (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusSignedFrameW p r R I := by
  obtain ⟨K, _, _, hK, b, c, hbc, hQ'⟩ := hQ
  have := charP_two_of_card hK
  have hp2 : p ≠ 2 := by
    rcases hpn with h | ⟨-, h⟩
    · exact ne_two_of_dvd_two_pow_sub_one hn h
    · exact TableBU.ne_two_of_dvd_two_pow_add_one hn h
  obtain ⟨hZ, hcp⟩ := center_data_omegaMinus (K := K) hp hp2 hm hbc
  refine ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ', 0,
    TypeA.ggTorusLift_zero (ggKGOrth_two_dvd_card_minus hm b c hbc),
    ggTorusSignedFrameW_of_signedEltSC hp hp2 (fun _ h => h) hZ hcp ?_⟩
  rcases hpn with h | ⟨ho, h⟩
  · exact ggOrthSignedTorusInput_holds.2 K m p b c hm hbc hp (Or.inl (by rw [hK]; exact h))
  · exact ggOrthSignedTorusInput_holds.2 K m p b c hm hbc hp (Or.inr ⟨ho, by rw [hK]; exact h⟩)

theorem ggO1Row_labelAll_frame
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGTBRowR5O1 p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusSignedFrameW p r R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, h4, hpn⟩ := h
  subst htag
  dsimp only at h4 hpn hlab
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h2 h3
  · omega
  · omega
  · refine ggO1Row_recipe_signedFrame hp hlab.1 ?_ (by omega) hQ
    rcases hpn with h | ⟨he, h⟩
    · exact Or.inl h
    · obtain ⟨j, hj⟩ := he
      exact Or.inr ⟨⟨j - 1, by omega⟩, h⟩

theorem ggO1Row_labelAllGuard_frame
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGTBRowR5O1 p lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTorusSignedFrameW p r R I) :=
  nbrC_labelAll_guard (ggO1Row_labelAll_frame hp hlab h)

end CFSG.StandardType

end
