module

public import CFSG.Quasithin.Background.D2Transport
public import CFSG.Quasithin.Background.FixVTransport
public import CFSG.Quasithin.Background.D2Offenders
public import CFSG.Quasithin.Background.G2L2
public import CFSG.Quasithin.Vol2.Ch3Sec1Aux
public import CFSG.Quasithin.Vol2.Ch5Sec1L34InputsD3
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternatingSix
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B4Dual
public import CFSG.Quasithin.Background.B5Basic
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.B6
public import CFSG.Quasithin.Background.B6Example
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.E2Hyp
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.InternalSecISec
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs2
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs520
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs522
public import CFSG.Quasithin.Vol2.Ch5StatementsDS

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped IsMulCommutative

section CongrHom

variable {V V' : Type*} [Group V] [Group V'] (e : V ≃* V')

noncomputable abbrev congrHom : MulAut V →* MulAut V' := (MulAut.congr e).toMonoidHom

theorem congrHom_apply (x : MulAut V) (v : V') : congrHom e x v = e (x (e.symm v)) := rfl

end CongrHom

section Congr

variable {V V' : Type*} [CommGroup V] [CommGroup V'] (e : V ≃* V')

theorem commSeries_map_congr (A : Subgroup (MulAut V)) (k : ℕ) :
    commSeries (A.map (congrHom e)) k = (commSeries A k).map e.toMonoidHom :=
  commSeries_map_mulAutCongr e A k

private theorem fixV_map_congr (A : Subgroup (MulAut V)) :
    fixV (A.map (congrHom e)) = (fixV A).map e.toMonoidHom :=
  fixV_map_congr_equiv e A

theorem rAV_map_congr (A : Subgroup (MulAut V)) : rAV (A.map (congrHom e)) = rAV A :=
  rAV_map_mulAutCongr e A

theorem IsA2.map_congr {X A : Subgroup (MulAut V)} (h : IsA2 X A) :
    IsA2 (X.map (congrHom e)) (A.map (congrHom e)) :=
  isA2_map_mulAutCongr e h

theorem kq_map_congr_le [Finite V] [Finite V'] (X : Subgroup (MulAut V)) (k : ℕ) :
    kq (X.map (congrHom e)) k ≤ kq X k :=
  kq_map_mulAutCongr_le e X k

end Congr

section D27

variable {V : Type*} [CommGroup V] [Finite V]

theorem qhatOf_autSub_le_of_mem_QhatStar (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ)) (hA : A ∈ QhatStar X) {U : Subgroup V}
    (hU : A ≤ stabSub U) (hUA : commSub U A ≠ ⊥) : qhatOf (autSub X U) ≤ (r : WithTop ℚ) := by
  by_cases h : (r : WithTop ℚ) ≤ qhatOf (autSub X U)
  · exact (D2_8 hV hr hA hU hUA h).1.le
  · exact (not_le.mp h).le

end D27

section Internal

variable {G : Type} [Group G]

theorem isElemAbelian_mono {U W : Subgroup G} (hU : IsElemAbelian 2 U) (hWU : W ≤ U) :
    IsElemAbelian 2 W := CFSG.Open.IsElemAbelian.mono hU hWU

variable [Finite G]

omit [Finite G] in
theorem map_autSub_le_autOn {Y U W : Subgroup G} (hU : IsElemAbelian 2 U) (hWU : W ≤ U)
    (hYW : Y ≤ Subgroup.normalizer (W : Set G)) :
    (@autSub ↥U (commGroupOfElemAbelian hU) (autOn Y U) (W.subgroupOf U)).map
        (congrHom (Subgroup.subgroupOfEquivOfLe hWU)) ≤ autOn Y W := by
  let := commGroupOfElemAbelian hU
  rintro φ ⟨ψ, hψ, rfl⟩
  obtain ⟨g, hgY, rfl⟩ := mem_autSub.mp hψ
  obtain ⟨⟨y, hyN⟩, hyY, hyg⟩ := Subgroup.mem_map.mp hgY
  rw [Subgroup.mem_subgroupOf] at hyY
  refine Subgroup.mem_map.mpr ⟨⟨y, hYW hyY⟩, Subgroup.mem_subgroupOf.mpr hyY, ?_⟩
  ext w
  rw [conjAct_coe_apply, congrHom_apply]
  have h2 : ((g : MulAut ↥U) ((Subgroup.subgroupOfEquivOfLe hWU).symm w : ↥U) : G) =
      y * (w : G) * y⁻¹ := by
    rw [← hyg, conjAct_coe_apply]
    rfl
  exact h2.symm

theorem qhatInt_le_qhatOf_autSub {Y U W : Subgroup G} (hU : IsElemAbelian 2 U) (hWU : W ≤ U)
    (hYW : Y ≤ Subgroup.normalizer (W : Set G)) :
    qhatInt Y W (isElemAbelian_mono hU hWU) ≤
      @qhatOf ↥(W.subgroupOf U) (@Subgroup.toCommGroup ↥U (commGroupOfElemAbelian hU) _) _
        (@autSub ↥U (commGroupOfElemAbelian hU) (autOn Y U) (W.subgroupOf U)) := by
  let := commGroupOfElemAbelian hU
  let := commGroupOfElemAbelian (isElemAbelian_mono hU hWU)
  unfold qhatInt qhatOf
  exact (kq_anti_group (map_autSub_le_autOn hU hWU hYW) 3).trans (kq_map_congr_le _ _ 3)

end Internal

end CFSG.Quasithin.H13
