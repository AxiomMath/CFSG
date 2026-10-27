module

public import CFSG.LocalAnalysis.StandardType.GGNSJoinBranch
public import CFSG.LocalAnalysis.StandardType.GGFixedRealizedConfig
import CFSG.LocalAnalysis.StandardType.GGNSJoinOrthExclAux
import CFSG.LocalAnalysis.StandardType.GGNSJoinOrthExclAux2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open TauCeti

namespace NSJoin


theorem nsOrthExclInputOf_holds {T : ∀ {ι : Type}, CoxeterMatrix ι → Prop}
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hBase : NSBaseFrameInputOf T)
    (hRootGenL : NSRootGenLInputOf T) (hRQ : NSRealNbrInputOf T) (hNbrQ4 : NSNbrQFourInputOf T)
    (hPumpNbr : NSPumpNbrInputOf T) :
    NSOrthExclInputOf T := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hC hp3 V _ _ Q hQ _ ι hdim himage
  subst hp3
  exfalso
  haveI : Finite V := Finite.of_injective (⇑ι.toEquiv.symm) ι.toEquiv.symm.injective
  have hcfgR : GGSecFiveRouteCfg' 3 B Bs x L D J 𝒦 := ggSecFiveRouteCfg'_of_routeCfg hcfg.1
  have hconf : GGConfig 3 B Bs x L D J := hcfgR.1.1
  have hInn : GGInnerDiagOn Bs L := hcfgR.1.2.2.1.1
  obtain ⟨c, hc, a, b, haA, hbA, haRe, hbRe, haReal, hbReal, haFx, hbFx, haON, hbON⟩ :=
    nsOrth_fixed_refl_classes hL hP hBase hRootGenL hRQ hNbrQ4 hPumpNbr hcfg hC Q hQ ι hdim himage
  have hP3 : GGFixedRealizedInL 3 Bs L x := ggFixedRealizedInL_of_config hL hP hconf hInn
  have haL : a ∈ ggAutomizer L Bs := hP3 a haRe haReal.mem_ggInduced_top haFx haReal
  have hbL : b ∈ ggAutomizer L Bs := hP3 b hbRe hbReal.mem_ggInduced_top hbFx hbReal
  obtain ⟨ιL, instL, ML, hML, hWeylL, hcardBs, hrank⟩ := hBase G 3 B Bs x L D J 𝒦 hcfg
  have hWM : GGIsWeylMatrix ML := hML.elim (fun h => h.isWeylMatrix) (fun h => h.isWeylMatrix)
  have hle3 : ∀ i j : ιL, i ≠ j → ML.M i j ≤ 3 :=
    hML.elim (fun h => h.le_three) (fun h => h.le_three)
  obtain ⟨f, hf⟩ := hWeylL
  obtain ⟨-, hconjL⟩ := nsOrth_reflConj_of_base hcfgR ML hWM hle3 f hf
  obtain ⟨g, hgL, hb_eq⟩ := hconjL a haL b hbL haRe hbRe
  have hgAInf : g ∈ ggAInf 3 B Bs x L D J := nsOrth_le_ainf_left hgL
  have hgO : ggLin (p := 3) ι g ∈ QuadraticMap.orthogonalGroup Q :=
    QuadraticMap.mem_orthogonalGroup_iff.mpr
      ((himage (ggLin (p := 3) ι g)).mp ⟨g, hgAInf, rfl⟩)
  have hb_eq' : ggLin (p := 3) ι b =
      ggLin (p := 3) ι g * ggLin (p := 3) ι a * (ggLin (p := 3) ι g)⁻¹ := by
    rw [hb_eq, map_mul, map_mul, map_inv]
  have hconjON : CFSG.StandardType.OrthF3.OrthReflOfNorm Q c (ggLin (p := 3) ι b) := by
    rw [hb_eq']
    exact nsOrth_class_conj haON (ggLin (p := 3) ι g) hgO
  have huniq : c = -c := nsOrth_refl_class_unique hconjON hbON
  have hc0 : c = 0 := by
    have h2 : (2 : ZMod 3) * c = 0 := by
      rw [two_mul]
      nth_rewrite 2 [huniq]
      exact add_neg_cancel c
    have h2ne : (2 : ZMod 3) ≠ 0 := by
      intro h
      have hdvd : (3 : ℕ) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 3).mp h
      obtain ⟨k, hk⟩ := hdvd
      omega
    exact (mul_eq_zero.mp h2).resolve_left h2ne
  exact hc hc0

theorem nsOrthExclInput_holds
    (hL : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hBase : NSBaseFrameInput)
    (hRootGenL : NSRootGenLInputOf NSTypeAD) (hRQ : NSRealNbrInputOf NSTypeAD) (hNbrQ4 : NSNbrQFourInput)
    (hPumpNbr : NSPumpNbrInput) :
    NSOrthExclInput :=
  nsOrthExclInputOf_holds (T := NSTypeAD) hL hP hBase hRootGenL hRQ hNbrQ4 hPumpNbr

end NSJoin

end CFSG.StandardType

end
