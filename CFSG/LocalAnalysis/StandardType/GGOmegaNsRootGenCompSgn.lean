module

public import CFSG.LocalAnalysis.StandardType.GGOmegaNsRootGenDefs
public import CFSG.Assembly.Defs
public import CFSG.ClassicalGroups.Orthogonal.Derived
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentComp
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CRankWitt
import CFSG.RankThree.PartOne.KC.OrthogonalEvenMinusFourExtract
import CFSG.RankThree.PartOne.K159.RowFourType
import CFSG.ClassicalInvolution.RouteD.TWYType
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldCentralizer
import CFSG.RankThree.PartOne.S11d.OutClassicalTwo
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.RankThree.PartOne.S11d.OutSymplectic
import CFSG.RankThree.PartOne.S11d.OutUnitary
import CFSG.RankThree.PartOne.S12.Sec15FA
import CFSG.RankThree.PartOne.S12.Sec15Items
import CFSG.RankThree.PartOne.S15K.FixedWitt
import CFSG.RankThree.PartOne.S15K.LayerModel
import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.Walter.Defs
import Certificates.Certificate1
import Certificates.Certificate2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.OmNsRootGen

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.GLTheoremA.S172C.Cent
  CFSG.ClassicalGroups.Orthogonal CFSG.GroupTheory.WeirSylow

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ} {k : ℕ}
  {U : Fin k → Submodule F V} {e : Fin k → ↥(orthDerived Q)} {E : Subgroup ↥(orthDerived Q)}

section FrameCalculus

@[instance_reducible] private def frameCommMonoid (hF : IsPlaneFrame Q p U e E) : CommMonoid ↥E :=
  letI : IsMulCommutative ↥E := hF.isElemAbelian.1
  { (inferInstance : Group ↥E) with mul_comm := fun x y => mul_comm' x y }

noncomputable def frameProj (hF : IsPlaneFrame Q p U e E) (i : Fin k) : V →ₗ[F] V :=
  (U i).projection (polarPerp Q (U i)) (isCompl_polarPerp (hF.nondeg i))

theorem frameProj_mem (hF : IsPlaneFrame Q p U e E) (i : Fin k) (v : V) :
    frameProj hF i v ∈ U i :=
  Submodule.projection_apply_mem (isCompl_polarPerp (hF.nondeg i)) v

theorem frameProj_apply_left (hF : IsPlaneFrame Q p U e E) (i : Fin k) {v : V}
    (hv : v ∈ U i) : frameProj hF i v = v :=
  Submodule.projection_apply_of_mem_left (isCompl_polarPerp (hF.nondeg i)) hv

private theorem frameProj_ker (hF : IsPlaneFrame Q p U e E) (i : Fin k) :
    LinearMap.ker (frameProj hF i) = polarPerp Q (U i) :=
  Submodule.ker_projection (isCompl_polarPerp (hF.nondeg i))

theorem frameProj_apply_right (hF : IsPlaneFrame Q p U e E) (i : Fin k) {v : V}
    (hv : v ∈ polarPerp Q (U i)) : frameProj hF i v = 0 := by
  have h : v ∈ LinearMap.ker (frameProj hF i) := by
    rw [frameProj_ker]
    exact hv
  exact LinearMap.mem_ker.mp h

theorem eq_sum_frameProj (hF : IsPlaneFrame Q p U e E) {s : V}
    (hs : s ∈ ⨆ j, U j) : s = ∑ i, frameProj hF i s := by
  classical
  set r : V := s - ∑ i, frameProj hF i s with hr
  have hrmem : r ∈ ⨆ j, U j := by
    have h1 : s ∈ ⨆ j, U j := hs
    have h2 : (∑ i, frameProj hF i s) ∈ ⨆ j, U j :=
      Submodule.sum_mem (⨆ j, U j) fun i _ =>
        Submodule.mem_iSup_of_mem i (frameProj_mem hF i s)
    rw [hr]
    exact Submodule.sub_mem (⨆ j, U j) h1 h2
  have hrzero : ∀ j, frameProj hF j r = 0 := by
    intro j
    have h1 : frameProj hF j (∑ i, frameProj hF i s) = frameProj hF j s := by
      rw [map_sum,
        Finset.sum_eq_single (s := Finset.univ)
          (f := fun i => frameProj hF j (frameProj hF i s)) j]
      · exact frameProj_apply_left hF j (frameProj_mem hF j s)
      · intro i _ hij
        exact frameProj_apply_right hF j (mem_polarPerp_iff.2 fun u hu => by
          rw [QuadraticMap.polar_comm]
          exact hF.perp i j hij _ (frameProj_mem hF i s) u hu)
      · intro h
        exact absurd (Finset.mem_univ j) h
    rw [hr, map_sub, h1, sub_self]
  have hrW : r ∈ polarPerp Q (⨆ j, U j) := by
    rw [mem_polarPerp_iff]
    intro y hy
    refine Submodule.iSup_induction U (motive := fun y => QuadraticMap.polar Q y r = 0) hy
      (fun i u hu => ?_) (by simp) (fun y z hy hz => by
        rw [QuadraticMap.polar_add_left, hy, hz, add_zero])
    have hker : r ∈ polarPerp Q (U i) := by
      rw [← frameProj_ker hF i, LinearMap.mem_ker]
      exact hrzero i
    exact mem_polarPerp_iff.1 hker u hu
  have h0 : r = 0 :=
    (Submodule.disjoint_def.mp hF.isCompl_iSup.disjoint) r hrmem hrW
  rw [hr] at h0
  exact sub_eq_zero.mp h0

theorem fixedSpace_signElt (hF : IsPlaneFrame Q p U e E) (a : Fin k) {x : ↥(orthDerived Q)}
    (hx : x ∈ E ∧ (∀ v ∈ U a, (x : V ≃ₗ[F] V) v = v) ∧
      ∀ j, j ≠ a → ∀ v ∈ U j, (x : V ≃ₗ[F] V) v = (e j : V ≃ₗ[F] V) v) :
    fixedSpace (x : V ≃ₗ[F] V) = U a ⊔ polarPerp Q (⨆ j, U j) := by
  classical
  refine le_antisymm ?_ ?_
  · intro v hv
    rw [mem_fixedSpace] at hv
    have hxW : ∀ w ∈ polarPerp Q (⨆ j, U j), (x : V ≃ₗ[F] V) w = w := fun w hw =>
      hF.apply_eq_of_mem_polarPerp_iSup hx.1 hw
    have htop : v ∈ (⨆ j, U j) ⊔ polarPerp Q (⨆ j, U j) := by
      rw [hF.isCompl_iSup.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨s, hs, w, hw, rfl⟩ := Submodule.mem_sup.mp htop
    have hxs : (x : V ≃ₗ[F] V) s = s := by
      have h1 : (x : V ≃ₗ[F] V) (s + w) = s + w := hv
      rw [map_add, hxW w hw] at h1
      exact add_right_cancel h1
    have hsa : s ∈ U a := by
      have hsum : s = ∑ i, frameProj hF i s := eq_sum_frameProj hF hs
      have hzmem : ∀ i, (x : V ≃ₗ[F] V) (frameProj hF i s) - frameProj hF i s ∈ U i := by
        intro i
        by_cases hi : i = a
        · subst hi
          rw [hx.2.1 _ (frameProj_mem hF i s)]
          exact Submodule.sub_mem (U i) (frameProj_mem hF i s) (frameProj_mem hF i s)
        · rw [hx.2.2 i hi _ (frameProj_mem hF i s)]
          exact Submodule.sub_mem (U i) (hF.maps_to i _ (frameProj_mem hF i s))
            (frameProj_mem hF i s)
      have hsum0 : ∑ i, ((x : V ≃ₗ[F] V) (frameProj hF i s) - frameProj hF i s) = 0 := by
        rw [Finset.sum_sub_distrib, ← map_sum, ← hsum, hxs, sub_self]
      have hz : ∀ j, j ≠ a → frameProj hF j s = 0 := by
        intro j hj
        have h0 : (x : V ≃ₗ[F] V) (frameProj hF j s) - frameProj hF j s = 0 := by
          have h1 : frameProj hF j
              (∑ i, ((x : V ≃ₗ[F] V) (frameProj hF i s) - frameProj hF i s)) = 0 := by
            rw [hsum0, map_zero]
          rw [map_sum,
            Finset.sum_eq_single (s := Finset.univ)
              (f := fun i => frameProj hF j
                ((x : V ≃ₗ[F] V) (frameProj hF i s) - frameProj hF i s)) j] at h1
          · rwa [frameProj_apply_left hF j (hzmem j)] at h1
          · intro i _ hij
            exact frameProj_apply_right hF j (mem_polarPerp_iff.2 fun u hu => by
              rw [QuadraticMap.polar_comm]
              exact hF.perp i j hij _ (hzmem i) u hu)
          · intro h
            exact absurd (Finset.mem_univ j) h
        have hfixj : (e j : V ≃ₗ[F] V) (frameProj hF j s) = frameProj hF j s := by
          rw [← hx.2.2 j hj _ (frameProj_mem hF j s)]
          exact sub_eq_zero.mp h0
        exact hF.eq_zero_of_apply_eq j _ (frameProj_mem hF j s) hfixj
      rw [hsum, Finset.sum_eq_single a (fun i _ hi => hz i hi)
        (fun h => absurd (Finset.mem_univ a) h)]
      exact frameProj_mem hF a s
    exact Submodule.mem_sup.mpr ⟨s, hsa, w, hw, rfl⟩
  · intro v hv
    rw [mem_fixedSpace]
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
    rw [map_add, hx.2.1 u hu, hF.apply_eq_of_mem_polarPerp_iSup hx.1 hw]

end FrameCalculus

section LinearAlgebra

private theorem oddOrderIsometry_of_mem_frame (hF : IsPlaneFrame Q p U e E)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    {x : ↥(orthDerived Q)} (hxE : x ∈ E) :
    OddOrderIsometry Q p (x : V ≃ₗ[F] V) := by
  have hpl : p ≠ ringChar F := by rw [ringChar.eq F 2]; exact hp2
  have hpF : (p : F) ≠ 0 := by
    intro h0
    have h1 := (ringChar.spec F p).mp h0
    rw [ringChar.eq F 2] at h1
    rcases (Nat.dvd_prime hp).mp h1 with h2 | h2
    · exact absurd h2 (by norm_num)
    · exact hp2 h2.symm
  refine ⟨orthDerived_le_orthogonalGroup x.2, ?_, hpF, fun v hv => hQ.1 v fun w => ?_⟩
  · have hxp : x ^ p = 1 := hF.isElemAbelian.2 x hxE
    simpa [Subgroup.coe_pow] using
      congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V)) hxp
  · simpa using hv w

private theorem polarNondegOn_polarPerp (hF : IsPlaneFrame Q p U e E)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) :
    PolarNondegOn Q (polarPerp Q (⨆ j, U j)) := by
  intro w hw hww
  refine hQ.1 w fun v => ?_
  have hv : v ∈ (⨆ j, U j) ⊔ polarPerp Q (⨆ j, U j) := by
    rw [hF.isCompl_iSup.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨s, hs, r, hr, rfl⟩ := Submodule.mem_sup.mp hv
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_add_right]
  have h1 : QuadraticMap.polar Q w s = 0 := by
    rw [QuadraticMap.polar_comm]
    exact mem_polarPerp_iff.1 hw s hs
  rw [h1, hww r hr, add_zero]

private theorem disjoint_plane_polarPerp (hF : IsPlaneFrame Q p U e E) (a : Fin k) :
    Disjoint (U a) (polarPerp Q (⨆ j, U j)) := by
  rw [disjoint_iff_inf_le]
  intro v hv
  obtain ⟨hvU, hvW⟩ := Submodule.mem_inf.mp hv
  have h : (⟨v, hvU⟩ : U a) = 0 := (hF.nondeg a).1 ⟨v, hvU⟩ fun y => by
    rw [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype_cent, QuadraticMap.polar_comm]
    exact mem_polarPerp_iff.1 hvW (y : V) (le_iSup U a y.2)
  exact (Submodule.mem_bot F).mpr (congrArg Subtype.val h)

private theorem polarNondegOn_fixedSpace (hF : IsPlaneFrame Q p U e E) (a : Fin k)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {x : ↥(orthDerived Q)}
    (hx : x ∈ E ∧ (∀ v ∈ U a, (x : V ≃ₗ[F] V) v = v) ∧
      ∀ j, j ≠ a → ∀ v ∈ U j, (x : V ≃ₗ[F] V) v = (e j : V ≃ₗ[F] V) v) :
    PolarNondegOn Q (fixedSpace (x : V ≃ₗ[F] V)) := by
  intro v hv hvperp
  rw [fixedSpace_signElt hF a hx] at hv hvperp
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  have hu0 : u = 0 := by
    have h : (⟨u, hu⟩ : U a) = 0 := (hF.nondeg a).1 ⟨u, hu⟩ fun y => by
      rw [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype_cent]
      have hy := hvperp (y : V) (Submodule.mem_sup_left y.2)
      rw [QuadraticMap.polar_add_left] at hy
      have hwy : QuadraticMap.polar Q w (y : V) = 0 := by
        rw [QuadraticMap.polar_comm]
        exact mem_polarPerp_iff.1 hw (y : V) (le_iSup U a y.2)
      rw [hwy, add_zero] at hy
      exact hy
    exact congrArg Subtype.val h
  have hw0 : w = 0 := by
    refine polarNondegOn_polarPerp hF hQ w hw fun y hy => ?_
    have hy := hvperp y (Submodule.mem_sup_right hy)
    rwa [hu0, zero_add] at hy
  rw [hu0, hw0, add_zero]

private theorem finrank_fixedSpace (hF : IsPlaneFrame Q p U e E) (a : Fin k)
    (hW : Module.finrank F ↥(polarPerp Q (⨆ j, U j)) = 2) {x : ↥(orthDerived Q)}
    (hx : x ∈ E ∧ (∀ v ∈ U a, (x : V ≃ₗ[F] V) v = v) ∧
      ∀ j, j ≠ a → ∀ v ∈ U j, (x : V ≃ₗ[F] V) v = (e j : V ≃ₗ[F] V) v) :
    Module.finrank F ↥(fixedSpace (x : V ≃ₗ[F] V)) = 4 := by
  rw [fixedSpace_signElt hF a hx]
  have h := Submodule.finrank_sup_add_finrank_inf_eq (U a) (polarPerp Q (⨆ j, U j))
  rw [disjoint_iff.1 (disjoint_plane_polarPerp hF a), finrank_bot, add_zero,
    hF.finrank_eq a, hW] at h
  omega

private theorem polarPerp_fixedSpace_eq_othersSpace (hF : IsPlaneFrame Q p U e E) (a : Fin k)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    {x : ↥(orthDerived Q)}
    (hx : x ∈ E ∧ (∀ v ∈ U a, (x : V ≃ₗ[F] V) v = v) ∧
      ∀ j, j ≠ a → ∀ v ∈ U j, (x : V ≃ₗ[F] V) v = (e j : V ≃ₗ[F] V) v) :
    polarPerp Q (fixedSpace (x : V ≃ₗ[F] V)) =
      othersSpace (x : V ≃ₗ[F] V).toLinearMap (X - 1) := by
  have hxOO : OddOrderIsometry Q p (x : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_mem_frame hF hQ hp hp2 hx.1
  obtain ⟨hc, horth⟩ := hxOO.fixed_others
  refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
  · intro r hr
    rw [mem_polarPerp_iff]
    exact fun w hw => horth w hw r hr
  · rw [finrank_polarPerp hQ (fixedSpace (x : V ≃ₗ[F] V))]
    have h := Submodule.finrank_add_eq_of_isCompl hc
    omega

private theorem not_isPlusType_fixedSpace (hF : IsPlaneFrame Q p U e E) (a : Fin k)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hW : Module.finrank F ↥(polarPerp Q (⨆ j, U j)) = 2)
    {f f' : V} (hf : f ∈ polarPerp Q (⨆ j, U j)) (hQf : Q f = 0)
    (hpolar : polar Q f f' = 1) {x : ↥(orthDerived Q)}
    (hx : x ∈ E ∧ (∀ v ∈ U a, (x : V ≃ₗ[F] V) v = v) ∧
      ∀ j, j ≠ a → ∀ v ∈ U j, (x : V ≃ₗ[F] V) v = (e j : V ≃ₗ[F] V) v) :
    ¬ IsPlusType (Q.comp (fixedSpace (x : V ≃ₗ[F] V)).subtype) := by
  set W : Submodule F V := polarPerp Q (⨆ j, U j) with hWdef
  have hWdim : Module.finrank F ↥W = 2 := by rw [hWdef]; exact hW
  have hWplus : IsPlusType (Q.comp W.subtype) := by
    have hfW : f ∈ W := hf
    have hf0 : f ≠ 0 := by
      rintro rfl
      simpa using hpolar
    have hne : (⟨f, hfW⟩ : W) ≠ 0 := fun h => hf0 (congrArg Subtype.val h)
    refine ⟨Submodule.span F {(⟨f, hfW⟩ : W)}, ?_, ?_⟩
    · rw [finrank_span_singleton hne, hWdim]
    · intro y hy
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      simp [QuadraticMap.map_smul, hQf]
  have hdisj : Disjoint (U a) W := disjoint_plane_polarPerp hF a
  have horth : ∀ u ∈ U a, ∀ w ∈ W, polar Q u w = 0 :=
    fun u hu w hw => mem_polarPerp_iff.1 hw u (le_iSup U a hu)
  have hndW : (QuadraticMap.polarBilin (Q.comp W.subtype)).Nondegenerate :=
    nondegenerate_polarBilin_restrict (polarNondegOn_polarPerp hF hQ)
  have hSfix : U a ⊔ W = fixedSpace (x : V ≃ₗ[F] V) := by
    rw [hWdef]
    exact (fixedSpace_signElt hF a hx).symm
  have e1 : (Q.comp (fixedSpace (x : V ≃ₗ[F] V)).subtype).IsometryEquiv
      ((Q.comp (U a).subtype).prod (Q.comp W.subtype)) := by
    rw [← hSfix]
    exact CFSG.RankThree.PartOne.K159.isometryEquivSup Q (U a) W hdisj horth
  have hnp : ¬ IsPlusType ((Q.comp (U a).subtype).prod (Q.comp W.subtype)) := by
    rw [CFSG.ClassicalInvolution.RouteD.TWY.isPlusType_prod_iff (hF.nondeg a) hndW
      (a := 1) (b := 1) le_rfl le_rfl (by simpa using hF.finrank_eq a)
      (by simpa using hWdim)]
    exact fun h => hF.not_isPlusType a (h.mpr hWplus)
  intro hplus
  exact hnp ((isPlusType_congr e1).mp hplus)

private theorem no_singular_plane_fixedSpace (hF : IsPlaneFrame Q p U e E) (a : Fin k)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hW : Module.finrank F ↥(polarPerp Q (⨆ j, U j)) = 2)
    {f f' : V} (hf : f ∈ polarPerp Q (⨆ j, U j)) (hQf : Q f = 0)
    (hpolar : polar Q f f' = 1) {x : ↥(orthDerived Q)}
    (hx : x ∈ E ∧ (∀ v ∈ U a, (x : V ≃ₗ[F] V) v = v) ∧
      ∀ j, j ≠ a → ∀ v ∈ U j, (x : V ≃ₗ[F] V) v = (e j : V ≃ₗ[F] V) v) :
    ∀ S : Submodule F ↥(fixedSpace (x : V ≃ₗ[F] V)), Module.finrank F S = 2 →
      ∃ u ∈ S, (Q.comp (fixedSpace (x : V ≃ₗ[F] V)).subtype) u ≠ 0 := by
  intro S hS
  by_contra hcon
  push Not at hcon
  exact not_isPlusType_fixedSpace hF a hQ hW hf hQf hpolar hx
    ⟨S, by rw [hS, finrank_fixedSpace hF a hW hx], hcon⟩

end LinearAlgebra

section Components

private theorem isQuasisimple_supportedFixedDerived_signElt (hF : IsPlaneFrame Q p U e E)
    (a : Fin k) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hW : Module.finrank F ↥(polarPerp Q (⨆ j, U j)) = 2)
    {f f' : V} (hf : f ∈ polarPerp Q (⨆ j, U j)) (hQf : Q f = 0)
    (hpolar : polar Q f f' = 1) {x : ↥(orthDerived Q)}
    (hx : x ∈ E ∧ (∀ v ∈ U a, (x : V ≃ₗ[F] V) v = v) ∧
      ∀ j, j ≠ a → ∀ v ∈ U j, (x : V ≃ₗ[F] V) v = (e j : V ≃ₗ[F] V) v) :
    CFSG.IsQuasisimple ↥(supportedFixedDerived Q (x : V ≃ₗ[F] V)) := by
  have hxOO : OddOrderIsometry Q p (x : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_mem_frame hF hQ hp hp2 hx.1
  have hR : (QuadraticMap.polarBilin
      (Q.comp (fixedSpace (x : V ≃ₗ[F] V)).subtype)).Nondegenerate :=
    nondegenerate_polarBilin_restrict (polarNondegOn_fixedSpace hF a hQ hx)
  have hdim : Module.finrank F ↥(fixedSpace (x : V ≃ₗ[F] V)) = 4 :=
    finrank_fixedSpace hF a hW hx
  have hts := no_singular_plane_fixedSpace hF a hQ hW hf hQf hpolar hx
  have hqR : CFSG.IsQuasisimple
      ↥(orthDerived (Q.comp (fixedSpace (x : V ≃ₗ[F] V)).subtype)) := by
    obtain ⟨E', _, _, D, ψ, ρ, -, -, -, -, hder, hsimple, -, hnonab, -, -, -, -⟩ :=
      CFSG.RankThree.PartOne.even_minus_four_actual_derived_extraction
        (Q.comp (fixedSpace (x : V ≃ₗ[F] V)).subtype) hR hdim hts
    haveI : IsSimpleGroup ↥ρ.range := hsimple
    have hqA : CFSG.IsQuasisimple ↥ρ.range :=
      CFSG.RankThree.PartOne.KCOrthogonal.isQuasisimple_of_simple_nonabelian hnonab
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr hder.symm) hqA
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (supportedFixedDerivedEquiv hxOO).symm hqR

theorem isComponentOf_signBlock (hF : IsPlaneFrame Q p U e E) (a : Fin k)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hW : Module.finrank F ↥(polarPerp Q (⨆ j, U j)) = 2)
    {f f' : V} (hf : f ∈ polarPerp Q (⨆ j, U j)) (hQf : Q f = 0)
    (hpolar : polar Q f f' = 1) {x : ↥(orthDerived Q)}
    (hx : x ∈ E ∧ (∀ v ∈ U a, (x : V ≃ₗ[F] V) v = v) ∧
      ∀ j, j ≠ a → ∀ v ∈ U j, (x : V ≃ₗ[F] V) v = (e j : V ≃ₗ[F] V) v)
    {X : Set ↥(orthDerived Q)} (hxX : x ∈ X)
    (hX : X ⊆ Subgroup.closure (e '' {j | j ≠ a})) :
    CFSG.Assembly.IsComponentOf
      ((supportedFixedDerived Q (x : V ≃ₗ[F] V)).subgroupOf (orthDerived Q))
      (Subgroup.centralizer X) := by
  have hxOO : OddOrderIsometry Q p (x : V ≃ₗ[F] V) :=
    oddOrderIsometry_of_mem_frame hF hQ hp hp2 hx.1
  have hfix := fixedSpace_signElt hF a hx
  have hle := hxOO.supportedFixedDerived_le_orthDerived
  have hR : (QuadraticMap.polarBilin
      (Q.comp (fixedSpace (x : V ≃ₗ[F] V)).subtype)).Nondegenerate :=
    nondegenerate_polarBilin_restrict (polarNondegOn_fixedSpace hF a hQ hx)
  have hq : CFSG.IsQuasisimple ↥(supportedFixedDerived Q (x : V ≃ₗ[F] V)) :=
    isQuasisimple_supportedFixedDerived_signElt hF a hQ hp hp2 hW hf hQf hpolar hx
  have hqL : CFSG.Assembly.IsQuasisimple
      ↥((supportedFixedDerived Q (x : V ≃ₗ[F] V)).subgroupOf (orthDerived Q)) := by
    have h1 : CFSG.IsQuasisimple
        ↥((supportedFixedDerived Q (x : V ≃ₗ[F] V)).subgroupOf (orthDerived Q)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle).symm hq
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr h1
  have hLle : (supportedFixedDerived Q (x : V ≃ₗ[F] V)).subgroupOf (orthDerived Q) ≤
      Subgroup.centralizer X := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hgS : (g : V ≃ₗ[F] V) ∈ supportedFixedDerived Q (x : V ≃ₗ[F] V) :=
      Subgroup.mem_subgroupOf.mp hg
    have hblock := supportedFixedDerived_le_supportedBlock hgS
    have hgP : ∀ u ∈ polarPerp Q (fixedSpace (x : V ≃ₗ[F] V)), (g : V ≃ₗ[F] V) u = u := by
      intro u hu
      rw [polarPerp_fixedSpace_eq_othersSpace hF a hQ hp hp2 hx] at hu
      exact (mem_supportedBlock.mp hblock).2 u hu
    have hgU : ∀ u ∈ fixedSpace (x : V ≃ₗ[F] V),
        (g : V ≃ₗ[F] V) u ∈ fixedSpace (x : V ≃ₗ[F] V) := by
      intro u hu
      rw [mem_fixedSpace] at hu ⊢
      have h2 := (mem_isometryCentralizer.mp (Subgroup.mem_inf.mp hblock).1).2
      calc (x : V ≃ₗ[F] V) ((g : V ≃ₗ[F] V) u)
          = (g : V ≃ₗ[F] V) ((x : V ≃ₗ[F] V) u) := (h2 u).symm
        _ = (g : V ≃ₗ[F] V) u := by rw [hu]
    have hyE : y ∈ E := by
      rw [← hF.closure_eq]
      exact Subgroup.closure_mono (Set.image_subset_range e {j | j ≠ a}) (hX hy)
    have hyUa : ∀ u ∈ U a, (y : V ≃ₗ[F] V) u = u := by
      have hsub : Subgroup.closure (e '' {j | j ≠ a}) ≤
          (fixingSubgroup (V ≃ₗ[F] V) (U a : Set V)).comap
            (Subgroup.subtype (orthDerived Q)) := by
        rw [Subgroup.closure_le]
        rintro _ ⟨j, hj, rfl⟩
        refine Subgroup.mem_comap.mpr ?_
        exact (mem_fixingSubgroup_iff (M := V ≃ₗ[F] V)).mpr fun u hu => by
          simpa [LinearEquiv.smul_def] using hF.apply_of_perp j u
            (mem_polarPerp_iff.2 fun z hz => by
              rw [QuadraticMap.polar_comm]
              exact hF.perp a j (fun h => hj h.symm) u hu z hz)
      intro u hu
      exact (mem_fixingSubgroup_iff (M := V ≃ₗ[F] V)).mp
        (Subgroup.mem_comap.mp (hsub (hX hy))) u hu
    have hyW : ∀ u ∈ polarPerp Q (⨆ j, U j), (y : V ≃ₗ[F] V) u = u :=
      fun u hu => hF.apply_eq_of_mem_polarPerp_iSup hyE hu
    have hyfix : ∀ u ∈ fixedSpace (x : V ≃ₗ[F] V), (y : V ≃ₗ[F] V) u = u := by
      rw [hfix]
      intro u hu
      obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Submodule.mem_sup.mp hu
      rw [map_add, hyUa u₁ hu₁, hyW u₂ hu₂]
    have hcomm := commute_of_apply_eq hR (orthDerived_le_orthogonalGroup y.2) hyfix hgU hgP
    exact Subtype.ext (by simpa only [Subgroup.coe_mul] using hcomm)
  refine ⟨hLle, ?_, hqL⟩
  refine CFSG.Assembly.IsSubnormal.step hLle ?_ (CFSG.Assembly.IsSubnormal.refl _)
  · refine ⟨fun n hn m => ?_⟩
    refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr ?_)
    have hmn : (m : V ≃ₗ[F] V) ∈ isometryCentralizer Q (x : V ≃ₗ[F] V) := by
      rw [mem_isometryCentralizer]
      refine ⟨fun u => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
        (orthDerived_le_orthogonalGroup (m : ↥(orthDerived Q)).2) u, fun u => ?_⟩
      have hcomm : (m : ↥(orthDerived Q)) * x = x * (m : ↥(orthDerived Q)) :=
        (Subgroup.mem_centralizer_iff.mp m.2 x hxX).symm
      exact congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V) u) hcomm
    have hconj := hxOO.conj_mem_supportedFixedDerived hmn
      (Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hn))
    simpa [Subgroup.coe_mul] using hconj

theorem e_mem_signBlock (hF : IsPlaneFrame Q p U e E) (a : Fin k)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hW : Module.finrank F ↥(polarPerp Q (⨆ j, U j)) = 2)
    {f f' : V} (hf : f ∈ polarPerp Q (⨆ j, U j)) (hQf : Q f = 0)
    (hpolar : polar Q f f' = 1) {x : ↥(orthDerived Q)}
    (hx : x ∈ E ∧ (∀ v ∈ U a, (x : V ≃ₗ[F] V) v = v) ∧
      ∀ j, j ≠ a → ∀ v ∈ U j, (x : V ≃ₗ[F] V) v = (e j : V ≃ₗ[F] V) v) :
    e a ∈ (supportedFixedDerived Q (x : V ≃ₗ[F] V)).subgroupOf (orthDerived Q) := by
  have hfix := fixedSpace_signElt hF a hx
  have hR : (QuadraticMap.polarBilin
      (Q.comp (fixedSpace (x : V ≃ₗ[F] V)).subtype)).Nondegenerate :=
    nondegenerate_polarBilin_restrict (polarNondegOn_fixedSpace hF a hQ hx)
  have hdim : Module.finrank F ↥(fixedSpace (x : V ≃ₗ[F] V)) = 4 :=
    finrank_fixedSpace hF a hW hx
  have hts := no_singular_plane_fixedSpace hF a hQ hW hf hQf hpolar hx
  have hblock : (e a : V ≃ₗ[F] V) ∈ supportedBlock Q (x : V ≃ₗ[F] V) (X - 1) := by
    refine mem_supportedBlock.mpr ⟨?_, ?_⟩
    · rw [mem_isometryCentralizer]
      refine ⟨fun u => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
        (orthDerived_le_orthogonalGroup (e a).2) u, fun u => ?_⟩
      have hcomm : e a * x = x * e a := by
        haveI : IsMulCommutative ↥E := hF.isElemAbelian.1
        exact Subgroup.mul_comm_of_mem_isMulCommutative (H := E) (hF.mem a) hx.1
      exact congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V) u) hcomm
    · intro u hu
      rw [← polarPerp_fixedSpace_eq_othersSpace hF a hQ hp hp2 hx, hfix] at hu
      exact hF.apply_of_perp a u (mem_polarPerp_iff.2 fun y hy =>
        mem_polarPerp_iff.1 hu y (Submodule.mem_sup_left hy))
  refine Subgroup.mem_subgroupOf.mpr (mem_supportedFixedDerived.mpr ⟨hblock, ?_⟩)
  have hpow : (⟨(e a : V ≃ₗ[F] V), hblock⟩ :
      ↥(supportedBlock Q (x : V ≃ₗ[F] V) (X - 1))) ^ p = 1 := by
    apply Subtype.ext
    show (e a : V ≃ₗ[F] V) ^ p = 1
    have h := congrArg (fun z : ↥(orthDerived Q) => (z : V ≃ₗ[F] V))
      (hF.orderOf_eq a ▸ pow_orderOf_eq_one (e a))
    simpa [Subgroup.coe_pow] using h
  have hodd : Odd (orderOf (restrictFixed Q (x : V ≃ₗ[F] V)
      ⟨(e a : V ≃ₗ[F] V), hblock⟩)) := by
    have h1 : orderOf (restrictFixed Q (x : V ≃ₗ[F] V) ⟨(e a : V ≃ₗ[F] V), hblock⟩) ∣ p :=
      orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hpow, map_one])
    exact (hp.odd_of_ne_two hp2).of_dvd_nat h1
  obtain ⟨E', _, _, D, ψ, ρ, -, -, -, -, hder, -, -, -, -, -, -, hodd'⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_actual_derived_extraction
      (Q.comp (fixedSpace (x : V ≃ₗ[F] V)).subtype) hR hdim hts
  rw [show orthDerived (Q.comp (fixedSpace (x : V ≃ₗ[F] V)).subtype) = ρ.range from hder]
  exact hodd' _ (restrictFixed_mem_orthogonalGroup _) hodd

theorem dvd_card_signBlock (hF : IsPlaneFrame Q p U e E) (a : Fin k)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hW : Module.finrank F ↥(polarPerp Q (⨆ j, U j)) = 2)
    {f f' : V} (hf : f ∈ polarPerp Q (⨆ j, U j)) (hQf : Q f = 0)
    (hpolar : polar Q f f' = 1) {x : ↥(orthDerived Q)}
    (hx : x ∈ E ∧ (∀ v ∈ U a, (x : V ≃ₗ[F] V) v = v) ∧
      ∀ j, j ≠ a → ∀ v ∈ U j, (x : V ≃ₗ[F] V) v = (e j : V ≃ₗ[F] V) v) :
    p ∣ Nat.card ↥((supportedFixedDerived Q (x : V ≃ₗ[F] V)).subgroupOf (orthDerived Q)) := by
  have h := Subgroup.orderOf_dvd_natCard
    ((supportedFixedDerived Q (x : V ≃ₗ[F] V)).subgroupOf (orthDerived Q))
    (e_mem_signBlock hF a hQ hp hp2 hW hf hQf hpolar hx)
  rwa [hF.orderOf_eq a] at h

end Components

section Reflections

theorem reflect_mul_reflect_mem_signBlock (hF : IsPlaneFrame Q p U e E) (a : Fin k)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    {x : ↥(orthDerived Q)}
    (hx : x ∈ E ∧ (∀ v ∈ U a, (x : V ≃ₗ[F] V) v = v) ∧
      ∀ j, j ≠ a → ∀ v ∈ U j, (x : V ≃ₗ[F] V) v = (e j : V ≃ₗ[F] V) v)
    {v w : V} (hv : v ∈ U a ⊔ polarPerp Q (⨆ j, U j))
    (hw : w ∈ U a ⊔ polarPerp Q (⨆ j, U j)) (hQv : Q v ≠ 0) (hQw : Q w ≠ 0) :
    reflect Q v * reflect Q w ∈ supportedFixedDerived Q (x : V ≃ₗ[F] V) := by
  have hfix := fixedSpace_signElt hF a hx
  have hvS : v ∈ fixedSpace (x : V ≃ₗ[F] V) := by rw [hfix]; exact hv
  have hwS : w ∈ fixedSpace (x : V ≃ₗ[F] V) := by rw [hfix]; exact hw
  have hR : (QuadraticMap.polarBilin
      (Q.comp (fixedSpace (x : V ≃ₗ[F] V)).subtype)).Nondegenerate :=
    nondegenerate_polarBilin_restrict (polarNondegOn_fixedSpace hF a hQ hx)
  have hblock : ∀ {y : V}, y ∈ fixedSpace (x : V ≃ₗ[F] V) →
      reflect Q y ∈ supportedBlock Q (x : V ≃ₗ[F] V) (X - 1) := by
    intro y hyS
    have hyx : (x : V ≃ₗ[F] V) y = y := mem_fixedSpace.mp hyS
    have hcomm : (x : V ≃ₗ[F] V) * reflect Q y = reflect Q y * (x : V ≃ₗ[F] V) := by
      have h1 : (x : V ≃ₗ[F] V) * reflect Q y * (x : V ≃ₗ[F] V)⁻¹ = reflect Q y := by
        rw [reflect_conj (orthDerived_le_orthogonalGroup x.2), hyx]
      have h2 := congrArg (fun z => z * (x : V ≃ₗ[F] V)) h1
      simpa [mul_assoc] using h2
    refine mem_supportedBlock.mpr ⟨?_, ?_⟩
    · rw [mem_isometryCentralizer]
      refine ⟨fun u => TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup
        (reflect_mem_orthogonalGroup Q y) u, fun u => ?_⟩
      calc reflect Q y ((x : V ≃ₗ[F] V) u)
          = ((reflect Q y * (x : V ≃ₗ[F] V)) u) := rfl
        _ = (((x : V ≃ₗ[F] V) * reflect Q y) u) := by rw [← hcomm]
        _ = (x : V ≃ₗ[F] V) (reflect Q y u) := rfl
    · intro u hu
      rw [← polarPerp_fixedSpace_eq_othersSpace hF a hQ hp hp2 hx] at hu
      exact reflect_apply_of_polar_eq_zero (mem_polarPerp_iff.1 hu y hyS)
  have hres : ∀ {y : V} (hyS : y ∈ fixedSpace (x : V ≃ₗ[F] V)) (hQy : Q y ≠ 0)
      (hb : reflect Q y ∈ supportedBlock Q (x : V ≃ₗ[F] V) (X - 1)),
      restrictFixed Q (x : V ≃ₗ[F] V) ⟨reflect Q y, hb⟩
        = reflect (Q.comp (fixedSpace (x : V ≃ₗ[F] V)).subtype) ⟨y, hyS⟩ := by
    intro y hyS hQy hb
    ext u
    rw [CFSG.RankThree.PartOne.KCOrthogonal.coe_restrictFixed]
    show reflect Q y (u : V) =
      ((reflect (Q.comp (fixedSpace (x : V ≃ₗ[F] V)).subtype) ⟨y, hyS⟩) u : V)
    rw [reflect_apply hQy, reflect_apply (by simpa using hQy)]
    simp [QuadraticMap.comp_apply, polar_comp_subtype_cent]
  have hvblock : reflect Q v ∈ supportedBlock Q (x : V ≃ₗ[F] V) (X - 1) := hblock hvS
  have hwblock : reflect Q w ∈ supportedBlock Q (x : V ≃ₗ[F] V) (X - 1) := hblock hwS
  have helem : (⟨reflect Q v * reflect Q w, mul_mem hvblock hwblock⟩ :
      ↥(supportedBlock Q (x : V ≃ₗ[F] V) (X - 1)))
      = ⟨reflect Q v, hvblock⟩ * ⟨reflect Q w, hwblock⟩ := rfl
  refine mem_supportedFixedDerived.mpr ⟨mul_mem hvblock hwblock, ?_⟩
  rw [helem, map_mul, hres hvS hQv hvblock, hres hwS hQw hwblock]
  exact CFSG.LocalAnalysis.GLTheoremA.S172C.Rank.reflect_mul_reflect_mem_orthDerived hR
    (by simpa using hQv) (by simpa using hQw)

end Reflections

end CFSG.StandardType.OmNsRootGen

end
