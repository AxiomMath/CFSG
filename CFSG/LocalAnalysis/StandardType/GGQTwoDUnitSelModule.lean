module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBase
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxEven
import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameModule
import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameCfg
import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameMain

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo

open scoped Matrix

variable {G : Type} [Group G] [Finite G]


theorem ggQTwoD_selectedModule (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hcfg : GGQTwoDCfg 3 B Bs x L D J 𝒦 M e) {m : ℕ} (e' : Fin m ≃ ι) (hm : 4 ≤ m)
    (hM : M = (ggCoxeterMatrixD m).reindex e') :
    ∃ β : Additive ↥Bs ≃+ DVec m, ∀ (t : Fin m) (s : ↥Bs),
      β (Additive.ofMul ((((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs))
        s)) = dTau m (decide (t.val + 1 = m)) (OrthTorus.simpleLo t) (OrthTorus.simpleHi t)
          (β (Additive.ofMul s)) := by
  subst hM
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hrc : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦 := hcfg.1
  obtain ⟨V, iA, iM, ⟨ι'⟩⟩ := exists_ggLinData (ggRouteCfg_isElemAbelian hrc)
  haveI : Finite V := Finite.of_equiv _ ι'.toEquiv
  obtain ⟨Θ, ϑ, hϑ, hact⟩ :=
    ggQTwoDFrame_module hrc hm e' hcfg.2.2.2.1 ι' (ggQTwoD_fix hTBF hWI hrc)
  refine ⟨ι'.trans Θ.symm.toAddEquiv, fun t s => ?_⟩
  have h1 := hact ((ggCoxeterMatrixD m).simple t) (Θ.symm (ι' (Additive.ofMul s)))
  rw [qtwoE0_simple, hϑ t, LinearEquiv.apply_symm_apply, ggLin_apply_ofMul] at h1
  simp only [AddEquiv.trans_apply, LinearEquiv.coe_toAddEquiv]
  rw [h1]
  exact Θ.symm_apply_apply _

end CFSG.StandardType.QTwo

end
