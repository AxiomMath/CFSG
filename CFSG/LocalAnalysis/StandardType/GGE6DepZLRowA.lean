module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelEFrame
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift

public section

namespace CFSG.StandardType.E6Dep.ZL

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.E6ThreeModel
  CFSG.StandardType.TableBExc.E6Three
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K]

theorem zl_nb_eq (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (i : Fin 6) :
    (eFrame K ζ hζ).nb i = e6Isogeny K (e6Data_valid.nm K i) :=
  Subtype.ext (e6Isogeny_nt_eq i 1).symm

theorem zl_comm_nm_hm (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (i : Fin 6) :
    ⁅e6Data_valid.nm K i, e6Data_valid.hm K i ζ⁆ = e6Data_valid.hm K i ζ := by
  have h := e6Data_valid.nm_conj_hm K i i ζ
  have hc : Tag.cartan Tag.E6 i i = 2 := by fin_cases i <;> rfl
  have hz : ζ ^ (-(2 : ℤ)) = ζ := by
    have h3 : ζ * ζ * ζ = 1 := by rw [← hζ, pow_succ, pow_two]
    rw [zpow_neg, zpow_two]
    exact inv_eq_of_mul_eq_one_right h3
  rw [commutatorElement_def, h, hc, hz]
  have e1 : e6Data_valid.hm K i ζ * e6Data_valid.hm K i ζ * (e6Data_valid.hm K i ζ)⁻¹ =
      e6Data_valid.hm K i ζ := by group
  exact e1

end CFSG.StandardType.E6Dep.ZL

end
