module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelTFrame
import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelClassify

public section

namespace CFSG.StandardType.E6Dep.ZL

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.E6ThreeModel
  CFSG.StandardType.NoOffTwE6Three CFSG.StandardType.TableBExc.E6Three


theorem tFrame_mem_V0_of_baseChange {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω]
    [Algebra K Ω] [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    {g : ModGL Tag.E6 Ω} {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    {D : FrameData ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (hD : TSpec hn hK σ hσ Fr hFr g hζ D) (i : Fin 6)
    (r : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hr : baseChangeGL (algebraMap K Ω) (r : ModGL TwistTag.E6.tag K) =
      g * torusElt Tag.E6 Ω i ζ * g⁻¹) :
    r ∈ D.V0 := by
  let v : Fin Tag.E6.rank → ZMod 3 := fun j => ((Tag.cartan Tag.E6 i j : ℤ) : ZMod 3)
  have hv : v ∈ NoOffRest.hypE6 := NoOffRest.mem_hypE6.mpr (NoOffRest.kDot_cartan i)
  have hzeta : zetaVec ζ hζ v = fun j => ζ ^ Tag.cartan Tag.E6 i j := by
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
  have htel : torusElt Tag.E6 Ω i ζ = rootDiagUnit Tag.E6 (zetaVec ζ hζ v) := by
    calc torusElt Tag.E6 Ω i ζ
        = rootDiagUnit Tag.E6 (fun j => ζ ^ Tag.cartan Tag.E6 i j) :=
          torusElt_eq_rootDiagUnit (τ := Tag.E6) (K := Ω) i ζ
      _ = rootDiagUnit Tag.E6 (zetaVec ζ hζ v) := by rw [hzeta]
  have hr' : baseChangeGL (algebraMap K Ω) (r : ModGL TwistTag.E6.tag K) =
      g * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * g⁻¹ := by
    rw [hr, htel]
  refine (FrameData.mem_V0 D).2 ⟨?_, v, hv, ?_⟩
  · refine (hD.tor_eq r).2 ⟨torusElt Tag.E6 Ω i ζ,
      Subgroup.subset_closure ⟨(i, ζ), rfl⟩, ?_⟩
    exact (MulAut.conj_apply g (torusElt Tag.E6 Ω i ζ)).trans hr.symm
  · obtain ⟨hx, hxeq⟩ := hD.diag_eq v
    have hrconj : rgrpConjAut hn hK σ hσ Fr hFr
        ⟨g * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * g⁻¹, hx⟩ = MulAut.conj r := by
      have hcΓ : (r : ModGL TwistTag.E6.tag K) ∈ RecipeExcLang.twInndiagGroup K σ :=
        RecipeExcLang.graphFixedRootGroup_le_twInndiag σ r.2
      have h1 : twInndiagEquivRgrp hn hK σ hσ Fr hFr ⟨r, hcΓ⟩ =
          ⟨g * rootDiagUnit Tag.E6 (zetaVec ζ hζ v) * g⁻¹, hx⟩ := by
        refine Subtype.ext ?_
        rw [twInndiagEquivRgrp_apply]
        exact hr'
      rw [← h1, rgrpConjAut_apply_baseChange]
      exact RecipeExcLang.twConj_of_mem_C0 σ r
    rw [hxeq]
    exact hrconj.symm

end CFSG.StandardType.E6Dep.ZL

end
