module

public import CFSG.LocalAnalysis.StandardType.GGKG3K3cT
public import CFSG.LocalAnalysis.StandardType.GGKG3K3cA
public import CFSG.LocalAnalysis.StandardType.GGKG3K3cB
public import CFSG.LocalAnalysis.StandardType.GGKG3K3cC
public import CFSG.LocalAnalysis.StandardType.GGKG3ZE
public import CFSG.LocalAnalysis.StandardType.GGKG3K3dWeyl

public section

namespace CFSG.StandardType.GGKG3

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.RankThree.E6 CFSG.StandardType
open CFSG.StandardType.GGKG3.K3dCheck CFSG.StandardType.GGKG3.K3dWeyl

theorem k3c
    {L : Type} [Field L] [IsAlgClosed L] (S : LangSetup .E6 L 7) (hS : IsK3Setup S)
    (φ : MulAut ↥(S.E.subgroupOf S.Γ)) (hr : GGIsReflection 7 φ)
    (c : WeylGroup .E6) (hcw : c * w3 = w3 * c)
    (hc : ∀ x : ↥(S.E.subgroupOf S.Γ),
      (((φ x : ↥(S.E.subgroupOf S.Γ)) : S.Γ) : ModGL .E6 L) =
        canonicalRep (coxeterSystem .E6) L c * ((x : S.Γ) : ModGL .E6 L) *
          (canonicalRep (coxeterSystem .E6) L c)⁻¹) :
    c * c = 1 ∧ (weylMatrix c).trace = 2 := by
  obtain ⟨-, hinv, hfix⟩ := k3c_transport S hS φ hr c hc
  have hc2 : c * c = 1 :=
    k3_ZE (c * c) fun y hy => by rw [k3Star_mul]; exact hinv y hy
  have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hc2
  have hM2 : weylMat6 c * weylMat6 c = 1 := by rw [← weylMat6_mul, hc2, weylMat6_one]
  have hMW : weylMat6 c * Matrix.of kMw = Matrix.of kMw * weylMat6 c := by
    rw [← weylMat6_w3, ← weylMat6_mul, ← weylMat6_mul, hcw]
  have hCo : (weylMat6 c).transpose * Matrix.of kC * weylMat6 c = Matrix.of kC :=
    k3_weylMat6_orth c
  have hfix' : {y : Fin 6 → ZMod 7 | y ∈ k3Ex ∧ k3ActT (weylMat6 c) y = y}.ncard = 49 := by
    simpa [k3Star, hcinv] using hfix
  have tB := k3_trace_ex (weylMat6 c) hM2 hMW hfix'
  have tA := k3_trace_double (weylMat6 c) hCo hM2
  have h7 : (((weylMat6 c).trace : ℤ) : ZMod 7) = 2 := by
    rw [tA, tB]
    norm_num
  exact ⟨hc2, by rw [← weylMat6_trace]; exact k3_trace_wrap (weylMat6 c) hM2 h7⟩

end CFSG.StandardType.GGKG3
