module

public import CFSG.LocalAnalysis.StandardType.GGWPlusD4CardPos
public import CFSG.LocalAnalysis.StandardType.GGWPlusD4CardOrth
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMoreOrth
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBBridge

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem largeEvenLabelAll_irredTableB_D4_split {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGD4Three p lab) (hpn : p ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGIrredTableB p R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hrk, _⟩ := h
  dsimp only at htag hrk
  subst htag
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  split_ifs at hQ ⊢ with h3
  · omega
  · subst hrk
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    haveI : CharP K 2 := charP_two_of_card hK
    have hp2 : p ≠ 2 := ne_two_of_dvd_two_pow_sub_one' hlab.1 hpn
    have hpq : p ∣ Nat.card K - 1 := by rw [hK]; exact hpn
    have hL : GGTorusLift p 4 (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))) :=
      TableBSymp.ggTorusLift_omegaPlus (K := K) hp hp2 hpq (by omega)
    have hI : GGTorusIrred p 4 (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)))
        (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)))) :=
      CorFourTwoMore.ggTorusIrred_omegaPlus (K := K) hp hp2 hpq (by omega)
    have hIrr : GGIrredModTableB p (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)))
        (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4)))) :=
      ggIrredModTableB_of_torusIrred hp hL hI
    have hZ : Subgroup.center (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))) = ⊥ :=
      TableBOrth.center_omegaPlus_eq_bot (K := K) hp hp2 hpq (by omega)
    refine ⟨K, inferInstance, inferInstance, hK, hQ', ?_⟩
    intro M _ _ L' E θ hE hP
    refine ⟨card_eq_pow_mul_card_of_lift_and_bound hp hL ?_ hP, hIrr M L' E θ hE hP⟩
    intro L'' _ _ ψ hψ hker hperf A hA hI'
    exact card_le_pow_orthPlus_cover (by omega : 1 ≤ 4) hp hp2 hZ L'' ψ hψ hker hperf hA hI'

end CFSG.StandardType
