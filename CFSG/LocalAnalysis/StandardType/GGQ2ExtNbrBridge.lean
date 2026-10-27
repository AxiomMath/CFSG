module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExtCoverFrame
public import CFSG.LocalAnalysis.StandardType.GGQTwoD6Frame
public import CFSG.LocalAnalysis.StandardType.GGQTwoK1OfI1

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module
open CFSG.StandardType.QTwoD6

private theorem extNbrBr_reindex_refl {B : Type*} (M : CoxeterMatrix B) :
    M.reindex (Equiv.refl B) = M :=
  CoxeterMatrix.ext (Matrix.ext fun _ _ => rfl)

theorem extNbrBridge (R : RawFrameData) : ExtNbrBridge R := by
  intro hLB hP G _ _ B Bs x L D J hS hI1 y K hnb real hyBs k hkadm hkcomp _ W hW
  have hK1 : GGQTwoK1 3 B Bs x D J := ggQ2_K1_of_I1 hLB hP hS.1 hI1
  have hnrm := real.normalizer_eq k hkadm
  rw [hkcomp] at hnrm
  have hweyl : (ggAutomizer K Bs).map (ggLin (p := 3) real.coord) =
      W.toLin.parab Set.univ := by
    show (ggAutomizer K Bs).map (ggLin (p := 3) real.coord) = W.toLin.weyl
    rw [hnrm, ← hW.1]
  have hauto : ggAutomizer K Bs =
      Subgroup.closure (Set.range (W.toLin.simpleAut real.coord)) := by
    have h := W.toLin.closure_simpleAut_eq real.coord hweyl
    rwa [Set.image_univ] at h
  have hspan : ggFixedSubmodule (p := 3) real.coord (ggAutomizer K Bs) =
      Submodule.span (ZMod 3)
        {real.coord (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))} :=
    W.toLin.ggFixedSubmodule_eq_span (by norm_num) real.coord hweyl
      (real.coord (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs))) (fun v => by simpa using hW.2 v)
  have hfixed : ∀ b : ↥Bs, real.coord (Additive.ofMul b) ∈
      ggFixedSubmodule (p := 3) real.coord (ggAutomizer K Bs) ↔
      (b : G) ∈ ggBarCentralizer 3 Bs K := by
    intro b
    rw [hspan]
    constructor
    · intro hb
      have hb' := (ggQ2d6_model_span_iff (p := 3) real.coord hyBs b).mp hb
      have hby : (b : G) ∈ Subgroup.zpowers y :=
        (ggQ2d6_zpowers_subtype_iff hyBs b).mpr hb'
      have htr := (hnb.1.2.2.2.2.2 (b : G)).mpr hby
      exact ⟨b.2, htr.2.1, htr.2.2⟩
    · intro hb
      have hby : (b : G) ∈ Subgroup.zpowers y := hK1 y K hnb (b : G) hb.1 hb.2.2
      have hb' : b ∈ Subgroup.zpowers (⟨y, hyBs⟩ : ↥Bs) :=
        (ggQ2d6_zpowers_subtype_iff hyBs b).mp hby
      exact (ggQ2d6_model_span_iff (p := 3) real.coord hyBs b).mpr hb'
  let N : GGQ2NbrDatum 3 Bs K :=
    { Λ := W.ι
      coxeter := W.coxeter
      cartan := W.cartan
      V := R.V
      model := real.coord
      simple := W.toLin.simpleAut real.coord
      coroot := W.coroot
      root := W.root
      isWeyl := W.isWeyl
      isCartan := W.isCartan
      pairing := W.pairing
      simple_apply := W.toLin.ggLin_simpleAut real.coord
      automizer_K := hauto
      fixed_ZK := hfixed }
  refine ⟨N, Equiv.refl W.ι, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    rfl
  · exact (extNbrBr_reindex_refl W.coxeter).symm
  · rfl
  · rfl
  · rfl

end CFSG.StandardType.GGQ2Frame

end
