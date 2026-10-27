module

public import CFSG.LocalAnalysis.StandardType.GGE6DepZLFinite
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelCoord

public section

namespace CFSG.StandardType

namespace E6Dep

namespace ZL

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three NoOffRest

theorem kDotP_eq_kappa_dotProduct (y : Vec6) : kDotP 3 y = kappa ⬝ᵥ y := by
  have h : ∀ i : Fin 6, ((kE6 i : ℤ) : ZMod 3) = kappa i := by decide +kernel
  unfold kDotP dotProduct
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

theorem adRefl_E6_eq (i : Fin 6) (y : Vec6) : adRefl .E6 3 i y = y - y i • cartanE6 i := by
  have h : ∀ i : Fin 6, (fun j : Fin 6 => ((Tag.E6.cartan i j : ℤ) : ZMod 3)) = cartanE6 i := by
    decide +kernel
  exact congrArg (fun c => y - y i • c) (h i)

theorem adRefl_E6_invol (i : Fin 6) (y : Vec6) : adRefl .E6 3 i (adRefl .E6 3 i y) = y := by
  have h2 : ∀ i : Fin 6, cartanE6 i i = 2 := by decide +kernel
  rw [adRefl_E6_eq, adRefl_E6_eq]
  funext j
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h2 i]
  ring

theorem cartanM_mulVec_indepGens (i : Fin 6) (v : Vec6) :
    cartanM.mulVec ((indepGens i).mulVec v) = adRefl .E6 3 i (cartanM.mulVec v) := by
  have hcol : ∀ i : Fin 6, cartanM.mulVec ((1 : Mat6) i) = cartanE6 i := by decide +kernel
  have h1 : (indepGens i).mulVec v = v - (cartanE6 i ⬝ᵥ v) • (1 : Mat6) i := by
    unfold indepGens reflMat
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec]
    simp
  rw [adRefl_E6_eq, h1, Matrix.mulVec_sub, Matrix.mulVec_smul, hcol]
  rfl

theorem exists_closureU_adWord (ω : List (Fin 6)) :
    ∃ g ∈ closureU, ∀ v : Vec6,
      cartanM.mulVec (g.mulVec v) = adWord .E6 3 ω (cartanM.mulVec v) := by
  induction ω with
  | nil => exact ⟨1, one_mem _, fun v => by rw [Matrix.one_mulVec]; rfl⟩
  | cons i ω ih =>
    obtain ⟨g, hg, hgv⟩ := ih
    refine ⟨indepGens i * g, mul_mem (Submonoid.subset_closure ⟨i, rfl⟩) hg, fun v => ?_⟩
    show cartanM.mulVec ((indepGens i * g).mulVec v) =
      adRefl .E6 3 i (adWord .E6 3 ω (cartanM.mulVec v))
    rw [← Matrix.mulVec_mulVec, cartanM_mulVec_indepGens, hgv v]

theorem exists_closureU_of_weyl (u : WeylGroup .E6) :
    ∃ g ∈ closureU, ∀ v : Vec6,
      cartanM.mulVec (g.mulVec v) = adAct .E6 3 u (cartanM.mulVec v) := by
  obtain ⟨ω, rfl⟩ := (coxeterSystem .E6).wordProd_surjective u
  obtain ⟨g, hg, hgv⟩ := exists_closureU_adWord ω
  exact ⟨g, hg, fun v => (hgv v).trans (adWord_eq_adAct ω _)⟩

end ZL

end E6Dep

end CFSG.StandardType

end
