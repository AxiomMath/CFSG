module

public import CFSG.LocalAnalysis.StandardType.GGTBRowPermFrame
public import CFSG.LocalAnalysis.StandardType.GGTBRowR5Defs
public import CFSG.LocalAnalysis.StandardType.GGStdPosC13Unitary
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUModel
public import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitClassical

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggURow_recipe_permFrame
    {d n p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hn : 1 ≤ n) (hd : 4 ≤ d)
    (hpd : ¬ p ∣ d) {Q : LargeEvenRawCont} (hQ : LargeEvenRecipeUnitary d (2 ^ n) Q) :
    LargeEvenRecipeUnitary d (2 ^ n) fun R _ I F =>
      Q R I F ∧ ∃ r, GGTorusLift p r R ∧ GGTorusPermFrameW p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have := (TableBU.unitaryFieldData_of_card hK hn).charP
  have hdq : (d, 2 ^ n) ≠ (3, 2) := by
    rintro h
    have h1 : d = 3 := congrArg Prod.fst h
    omega
  refine ⟨ggUnitaryTorusRank p d, ggTorusLift_unitary hK hn (by omega) hdq hp hpq, ?_⟩
  exact ggTorusPermFrameW_of_permEltSC hp hp2 (TableBUE.center_proj_eq_bot hK (by omega) hdq)
    (fun φ hφ hφp =>
      InndiagSU.ggOutdiagPrime_unitary hK hn (by omega) hdq hp hpq hpd φ hφ hφp)
    (StdSubRestU.ggCenterPrime_unitary hK hn (by omega) hdq hp hp2 hpd) hpd
    (UModel.ggTorusPermEltSC_unitary hK hn (by omega) hp hp2 hpq hpd)

theorem ggURow_labelAll_frame
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGTBRowR5U p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusPermFrameW p r R I := by
  obtain ⟨t, l, n⟩ := lab
  intro Q hQ
  obtain ⟨htag, hpq⟩ := h
  rcases htag with ⟨ht, hl, hpd⟩ | ⟨ht, hl⟩
  · subst ht
    exact ggURow_recipe_permFrame hp hpq hlab.1 (by omega) hpd hQ
  · subst ht
    subst hl
    exact ggURow_recipe_permFrame hp hpq hlab.1 (by norm_num)
      (nbrC_not_dvd_four hp (TableBU.ne_two_of_dvd_two_pow_add_one hlab.1 hpq)) hQ

theorem ggURow_labelAllGuard_frame
    {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGTBRowR5U p lab) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
      ∃ r, GGTorusLift p r R ∧ GGTorusPermFrameW p r R I) :=
  nbrC_labelAll_guard (ggURow_labelAll_frame hp hlab h)

end CFSG.StandardType

end
