module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section9Focal
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Theorem6
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Sylow

namespace CFSG
end CFSG
open CFSG

/-!
# Section 9, Lemma 9.2

This is the ambient minimal-supplement adapter for the focal-subgroup squeeze.
The mathematical core lives in `Section9Focal`; this file maps Hall's residual
back from the subgroup `W` to the original ambient group and invokes minimality.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise

universe u

/-- Source Lemma 9.2 in the minimal-normal-supplement setup.

Here `P` is a Sylow subgroup of `W`, `E = W ∩ D` is represented as a subgroup
of `W`, and `ControlsFusionIn E P` is the elementwise fusion-control input.
The conclusion is the source contradiction: these hypotheses cannot coexist
with `p ∣ |E/E'|`. -/
public theorem lemma_9_2_of_controlsFusionIn
    {X : Type u} [Group X] [Finite X]
    {M D W : Subgroup X}
    (hW : IsMinimalNormalSupplement M D W)
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p W)
    (hP : (P : Subgroup W) ≤ (W ⊓ D).subgroupOf W)
    (hfusion : ControlsFusionIn ((W ⊓ D).subgroupOf W) (P : Subgroup W))
    (hp : p ∣ Nat.card (((W ⊓ D).subgroupOf W) ⧸
      derivedSubgroup ((W ⊓ D).subgroupOf W))) :
    False := by
  let E : Subgroup W := (W ⊓ D).subgroupOf W
  let RW : Subgroup W := External.hallPResidual p W
  have hfac : RW < ⊤ ∧ E ⊔ RW = ⊤ := by
    simpa [RW, E] using
      (hallPResidual_factorization_of_dvd_abelianization_of_controlsFusionIn
        E P hP hfusion hp)
  let R : Subgroup X := RW.map W.subtype
  have hRleW : R ≤ W := by
    exact Subgroup.map_subtype_le RW
  have hRltW : R < W := by
    have htopmap : (⊤ : Subgroup W).map W.subtype = W := by
      rw [← MonoidHom.range_eq_map, Subgroup.subtype_range]
    have hmaplt : RW.map W.subtype <
        (⊤ : Subgroup W).map W.subtype :=
      (Subgroup.map_lt_map_iff_of_injective W.subtype_injective).2 hfac.1
    rw [htopmap] at hmaplt
    exact hmaplt
  have hRnormal : (R.subgroupOf M).Normal := by
    apply normal_subgroupOf_map_of_characteristic_of_normal
      W R M hW.prop.le_M hW.prop.normal_in_M RW
      (by infer_instance) rfl
    exact hRleW.trans hW.prop.le_M
  have hRsup : R ⊔ D = M := by
    have hE_map : E.map W.subtype = W ⊓ D := by
      simp [E, Subgroup.subgroupOf_map_subtype, inf_comm]
    have htopmap : (⊤ : Subgroup W).map W.subtype = W := by
      rw [← MonoidHom.range_eq_map, Subgroup.subtype_range]
    have hmapfac : R ⊔ (W ⊓ D) = W := by
      calc
        R ⊔ (W ⊓ D) = RW.map W.subtype ⊔ E.map W.subtype := by
          change RW.map W.subtype ⊔ (W ⊓ D) = _
          rw [hE_map]
        _ = (RW ⊔ E).map W.subtype := (Subgroup.map_sup _ _ _).symm
        _ = (⊤ : Subgroup W).map W.subtype := by
          rw [sup_comm RW E, hfac.2]
        _ = W := htopmap
    have hED : (W ⊓ D) ⊔ D = D := sup_eq_right.mpr inf_le_right
    calc
      R ⊔ D = R ⊔ ((W ⊓ D) ⊔ D) := by rw [hED]
      _ = (R ⊔ (W ⊓ D)) ⊔ D := by rw [sup_assoc]
      _ = W ⊔ D := by rw [hmapfac]
      _ = M := hW.prop.sup_eq
  have hRnormsupp : IsNormalSupplement M D R :=
    { le_M := hRleW.trans hW.prop.le_M
      normal_in_M := hRnormal
      sup_eq := hRsup }
  have hReq : R = W := hW.eq_of_le hRnormsupp hRleW
  exact hRltW.ne hReq

end CFSG.BenderSuzuki
