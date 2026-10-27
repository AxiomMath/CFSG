module

public import CFSG.LocalAnalysis.StandardType.GGE6DepModelDefs
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofE6Ad

public section

namespace CFSG.StandardType

namespace E6Dep

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc.E6Three NoOffRest

@[expose] def nodeOf : Fin 6 → Fin Tag.E6.rank := (![0, 2, 3, 4, 5, 1] : Fin 6 → Fin 6)

@[expose] def genOf : Fin Tag.E6.rank → Fin 6 := (![0, 5, 1, 2, 3, 4] : Fin 6 → Fin 6)

@[expose] def coordE : Matrix (Fin Tag.E6.rank) (Fin 6) (ZMod 3) :=
  !![2, 2, 0, 0, 0, 0; 0, 0, 2, 0, 2, 0; 2, 2, 2, 0, 0, 0; 0, 2, 2, 2, 0, 0; 0, 0, 2, 2, 0, 0;
    0, 0, 0, 2, 0, 0]

@[expose] def coordF : Matrix (Fin 6) (Fin Tag.E6.rank) (ZMod 3) :=
  !![2, 0, 0, 1, 2, 0; 0, 0, 0, 2, 1, 0; 1, 0, 2, 0, 0, 0; 2, 0, 1, 0, 2, 0; 2, 2, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0]

theorem nodeOf_genOf (i : Fin Tag.E6.rank) : nodeOf (genOf i) = i := by
  revert i
  decide +kernel

theorem coordE_kDot (v : Vec6) (hv : v 5 = 0) : kDotP 3 (coordE.mulVec v) = 0 := by
  revert v
  decide +kernel

theorem coordE_mem (v : Vec6) (hv : v 5 = 0) : coordE.mulVec v ∈ hypE6 :=
  mem_hypE6.mpr (coordE_kDot v hv)

theorem coordF_coordE (v : Vec6) (hv : v 5 = 0) : coordF.mulVec (coordE.mulVec v) = v := by
  revert v
  decide +kernel

theorem coordE_injOn (v w : Vec6) (hv : v 5 = 0) (hw : w 5 = 0)
    (h : coordE.mulVec v = coordE.mulVec w) : v = w := by
  rw [← coordF_coordE v hv, ← coordF_coordE w hw, h]

theorem coordF_five (x : Fin Tag.E6.rank → ZMod 3) (hx : kDotP 3 x = 0) : (coordF.mulVec x) 5 = 0 := by
  revert x
  decide +kernel

theorem coordE_coordF (x : Fin Tag.E6.rank → ZMod 3) (hx : kDotP 3 x = 0) : coordE.mulVec (coordF.mulVec x) = x := by
  revert x
  decide +kernel

theorem coordE_gensL (i : Fin 6) (v : Vec6) (hv : v 5 = 0) :
    coordE.mulVec ((gensL i).mulVec v) = adRefl .E6 3 (nodeOf i) (coordE.mulVec v) := by
  revert v
  revert i
  decide +kernel

theorem gensL_apply_five (i : Fin 6) (v : Vec6) : ((gensL i).mulVec v) 5 = v 5 := by
  revert v
  revert i
  decide +kernel

theorem closureL_apply_five {g : Mat6} (hg : g ∈ closureL) (v : Vec6) : (g.mulVec v) 5 = v 5 := by
  induction hg using Submonoid.closure_induction generalizing v with
  | mem g hg =>
    obtain ⟨i, rfl⟩ := hg
    exact gensL_apply_five i v
  | one => simp
  | mul g h _ _ ihg ihh =>
    rw [← Matrix.mulVec_mulVec, ihg, ihh]

theorem exists_closureL_adWord (ω : List (Fin Tag.E6.rank)) :
    ∃ g ∈ closureL, ∀ v : Vec6, v 5 = 0 →
      coordE.mulVec (g.mulVec v) = adWord .E6 3 ω (coordE.mulVec v) := by
  induction ω with
  | nil => exact ⟨1, one_mem _, fun v _ => by rw [Matrix.one_mulVec]; rfl⟩
  | cons i ω ih =>
    obtain ⟨g, hg, hgv⟩ := ih
    refine ⟨gensL (genOf i) * g, mul_mem (Submonoid.subset_closure ⟨genOf i, rfl⟩) hg,
      fun v hv => ?_⟩
    have h5 : (g.mulVec v) 5 = 0 := by rw [closureL_apply_five hg v, hv]
    show coordE.mulVec ((gensL (genOf i) * g).mulVec v) =
      adRefl .E6 3 i (adWord .E6 3 ω (coordE.mulVec v))
    rw [← Matrix.mulVec_mulVec, coordE_gensL (genOf i) (g.mulVec v) h5, nodeOf_genOf, hgv v hv]

theorem exists_closureL_of_weyl (u : WeylGroup .E6) :
    ∃ g ∈ closureL, ∀ v : Vec6, v 5 = 0 →
      coordE.mulVec (g.mulVec v) = adAct .E6 3 u (coordE.mulVec v) := by
  obtain ⟨ω, rfl⟩ := (coxeterSystem .E6).wordProd_surjective u
  obtain ⟨g, hg, hgv⟩ := exists_closureL_adWord ω
  exact ⟨g, hg, fun v hv => by rw [hgv v hv, adWord_eq_adAct]⟩

end E6Dep

end CFSG.StandardType

end
