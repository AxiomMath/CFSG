module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelEFrame
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift
import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelClassify

public section

namespace CFSG.StandardType.E6Dep.ZL

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.E6ThreeModel
  CFSG.StandardType.TableBExc.E6Three
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K]

theorem zl_hm_mem_V0 (ζ : Kˣ) (hζ : ζ ^ 3 = 1) (i : Fin 6) :
    e6Isogeny K (e6Data_valid.hm K i ζ) ∈ (eFrame K ζ hζ).V0 := by
  set r := e6Isogeny K (e6Data_valid.hm K i ζ)
  let v : Fin Tag.E6.rank → ZMod 3 := fun j => ((Tag.cartan Tag.E6 i j : ℤ) : ZMod 3)
  have hzeta : TableBExc.E6Three.zetaVec (τ := Tag.E6) ζ hζ v =
      fun j => ζ ^ Tag.cartan Tag.E6 i j := by
    funext j
    show CFSG.RankThree.CentralCover.zmodPowHom ζ hζ
        (Multiplicative.ofAdd (↑(Tag.cartan Tag.E6 i j) : ZMod 3)) =
      ζ ^ Tag.cartan Tag.E6 i j
    rw [show (↑(Tag.cartan Tag.E6 i j) : ZMod 3) =
        Tag.cartan Tag.E6 i j • (1 : ZMod 3) from by rw [zsmul_eq_mul, mul_one],
      ofAdd_zsmul, map_zpow]
    congr 1
    rw [CFSG.RankThree.CentralCover.zmodPowHom_apply,
      show (1 : ZMod 3).val = 1 from by decide, pow_one]
  have heq := e6Isogeny_hm_eq (k := K) i ζ
  have htel : (r : ModGL Tag.E6 K) = torusElt Tag.E6 K i ζ :=
    heq.trans (torusElt_eq_rootDiagUnit (τ := Tag.E6) (K := K) i ζ).symm
  refine (FrameData.mem_V0 (eFrame K ζ hζ)).2 ⟨?_, v, ?_, ?_⟩
  · change r ∈ (torusGroup .E6 K).subgroupOf (adjointGroup .E6 K)
    rw [Subgroup.mem_subgroupOf, htel]
    exact Subgroup.subset_closure ⟨(i, ζ), rfl⟩
  · exact NoOffRest.mem_hypE6.mpr (NoOffRest.kDot_cartan i)
  · refine MulEquiv.ext fun h => Subtype.ext ?_
    rw [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, heq,
      show ((eFrame K ζ hζ).ad v h : ModGL Tag.E6 K) =
          ↑(NoOffE6Three.diag3 ζ hζ (Multiplicative.ofAdd v) h) from rfl,
      NoOffE6Three.diag3_apply ζ hζ v h, hzeta]

end CFSG.StandardType.E6Dep.ZL

end
