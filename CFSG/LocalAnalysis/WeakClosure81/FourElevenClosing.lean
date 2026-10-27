module

public import CFSG.GH74.GLS.IVK.Statements.Sec4
public import CFSG.Blueprint.Catalog
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthPlane
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44a
public import CFSG.GH74.GLS.IVK.Proofs2.Std44
public import CFSG.GH74.GLS.LU.Local.KStep
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCAdapted
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.Dihedral.GorensteinWalter.GLSemilinearDescent
public import CFSG.GH74.BNPair.Defs
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.IVK.L2.F1
public import CFSG.GH74.GLS.IVK.L2.Hilbert90Core
public import CFSG.GH74.GLS.IVK.L2.Lemma19c
public import CFSG.GH74.GLS.IVK.L2.Torus
public import CFSG.GH74.GLS.IVK.L2.TorusGeneral
public import CFSG.GH74.GLS.IVK.Prod.Basic
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Core
public import CFSG.GH74.GLS.Stage2.Local.Statements
public import CFSG.GH74.Statements
public import CFSG.GroupTheory.Fitting.CoprimeAutomorphisms
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAContainedSource
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSCSemidihedralKernel
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOddCoreUnbalancingTriple
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderGlauberman.ClassFunction
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_19
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CoprimeActionNontrivialTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseComponentData
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character
public import CFSG.Walter.J1
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.LocalAnalysis.WeakClosure81.FourEleven

open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.GH74.GLS.IVK
open CFSG.GH74.GLS.IVK.Proofs2

theorem Ez_le_commutator {K : Type} [Group K] (u : K) :
    CFSG.GH74.GLS.IVK.Ez u ≤ ⁅centralizer ({u} : Set K), centralizer ({u} : Set K)⁆ := by
  let C : Subgroup K := centralizer ({u} : Set K)
  have hlayer : CFSG.layer ↥C ≤ ⁅(⊤ : Subgroup ↥C), ⊤⁆ :=
    CFSG.HardMathSupport.Timmesfeld.CrossChar.layer_le_commutator_top_orth ↥C
  have hmap := Subgroup.map_mono (f := C.subtype) hlayer
  rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype] at hmap
  change (CFSG.layer ↥C).map C.subtype ≤ ⁅C, C⁆
  exact hmap

variable {Q : Type} [Group Q] [Finite Q]

theorem le_of_commutator_le_of_commuting_conj {L : Subgroup Q} [L.Normal] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hL : LieModel ↥L .PSL 3 p 1 ∨ LieModel ↥L .PSU 3 p 1)
    {H : Subgroup Q} {z c : Q} (hzL : z ∈ L) (hz2 : orderOf z = 2)
    (hY : ⁅L ⊓ centralizer ({z} : Set Q), L ⊓ centralizer ({z} : Set Q)⁆ ≤ H)
    (hcH : c ∈ H) (hne : c * z * c⁻¹ ≠ z) (hcomm : c * z * c⁻¹ * z = z * (c * z * c⁻¹)) :
    L ≤ H := by
  classical
  let zl : ↥L := ⟨z, hzL⟩
  let wl : ↥L := MulAut.conjNormal (H := L) c zl
  have hz2' : orderOf zl = 2 := by
    simpa [zl] using (Subgroup.orderOf_mk z hzL).trans hz2
  have hw2' : orderOf wl = 2 := by
    simpa [wl] using
      (MulEquiv.orderOf_eq (MulAut.conjNormal (H := L) c) zl).trans hz2'
  have hzl1 : zl ≠ 1 := by
    intro h
    have := hz2'
    rw [h, orderOf_one] at this
    omega
  have hwl1 : wl ≠ 1 := by
    intro h
    have := hw2'
    rw [h, orderOf_one] at this
    omega
  have hneL : zl ≠ wl := by
    intro h
    apply hne
    have hcoe : (wl : Q) = (zl : Q) := congrArg Subtype.val h.symm
    simpa [zl, wl, MulAut.conjNormal_apply] using hcoe
  have hcommL : zl * wl = wl * zl := by
    apply Subtype.ext
    simpa [zl, wl, MulAut.conjNormal_apply] using hcomm.symm
  let U : Subgroup ↥L := Subgroup.zpowers zl ⊔ Subgroup.zpowers wl
  have hU : IsFourSubgroup U :=
    CFSG.GH74.GLS.LU.Local.isFourSubgroup_zpowers_sup hz2' hw2' hneL hcommL
  have hzlU : zl ∈ U := Subgroup.mem_sup_left (Subgroup.mem_zpowers zl)
  have hwlU : wl ∈ U := Subgroup.mem_sup_right (Subgroup.mem_zpowers wl)
  have hgen : Subgroup.closure ((Ez zl : Set ↥L) ∪ (Ez wl : Set ↥L)) = ⊤ := by
    rcases hL with hL | hL
    · have hst : CFSG.Open.StatedClassicalModel ↥L .PSL 3 p 1 :=
        CFSG.Blueprint.LieModel.statedClassicalModel hL (by decide)
      obtain ⟨F, hF, hFin, hcard, he⟩ := hst.2
      have hE : IsLnEps 3 ↥L 1 (p ^ 1) := Or.inl ⟨rfl, F, hF, hFin, hcard, he⟩
      exact (ivk_4_4a (K := ↥L) (ε := 1) (p := p) (n := 1) hp (by omega) hE U hU
        zl hzlU wl hwlU hz2' hw2' hneL).1 (by rw [pow_one]; omega)
    · have hst : CFSG.Open.StatedClassicalModel ↥L .PSU 3 p 1 :=
        CFSG.Blueprint.LieModel.statedClassicalModel hL (by decide)
      obtain ⟨F, hF, hFin, hcard, he⟩ := hst.2
      have hE : IsLnEps 3 ↥L (-1) (p ^ 1) := Or.inr ⟨rfl, F, hF, hFin, hcard, he⟩
      exact (ivk_4_4a (K := ↥L) (ε := -1) (p := p) (n := 1) hp (by omega) hE U hU
        zl hzlU wl hwlU hz2' hw2' hneL).1 (by rw [pow_one]; omega)
  have hmapC : (Subgroup.centralizer ({zl} : Set ↥L)).map L.subtype =
      L ⊓ Subgroup.centralizer ({z} : Set Q) := by
    simpa [zl] using
      CFSG.ClassicalInvolution.Models.SymplecticPairs.map_subtype_centralizer_singleton L zl
  have hEz_le_H : (Ez zl).map L.subtype ≤ H := by
    have h := Subgroup.map_mono (f := L.subtype) (Ez_le_commutator zl)
    rw [Subgroup.map_commutator, hmapC] at h
    exact h.trans hY
  have hEz_w_eq : (Ez wl).map L.subtype =
      ((Ez zl).map L.subtype).map (MulAut.conj c).toMonoidHom := by
    have hψ : (Ez zl).map (MulAut.conjNormal (H := L) c).toMonoidHom = Ez wl := by
      simpa [wl] using Ez_map (MulAut.conjNormal (H := L) c) zl
    rw [← hψ, Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hHmap : H.map (MulAut.conj c).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hcH)
  have hEz_w_le_H : (Ez wl).map L.subtype ≤ H := by
    rw [hEz_w_eq]
    calc ((Ez zl).map L.subtype).map (MulAut.conj c).toMonoidHom
        ≤ H.map (MulAut.conj c).toMonoidHom := Subgroup.map_mono hEz_le_H
      _ = H := hHmap
  have hsup : (Ez zl).map L.subtype ⊔ (Ez wl).map L.subtype = L := by
    rw [← Subgroup.map_sup, Subgroup.sup_eq_closure, hgen, Subgroup.map_top,
      Subgroup.range_subtype]
  rw [← hsup]
  exact sup_le hEz_le_H hEz_w_le_H

theorem le_of_centralizer_le_of_commuting_conj_three {L : Subgroup Q} [L.Normal]
    (hL : LieModel ↥L .PSL 3 3 1) {H : Subgroup Q} {z c : Q} (hzL : z ∈ L)
    (hz2 : orderOf z = 2) (hC : L ⊓ centralizer ({z} : Set Q) ≤ H) (hcH : c ∈ H)
    (hne : c * z * c⁻¹ ≠ z) (hcomm : c * z * c⁻¹ * z = z * (c * z * c⁻¹)) : L ≤ H := by
  classical
  let zl : ↥L := ⟨z, hzL⟩
  let wl : ↥L := MulAut.conjNormal (H := L) c zl
  have hz2' : orderOf zl = 2 := by
    simpa [zl] using (Subgroup.orderOf_mk z hzL).trans hz2
  have hw2' : orderOf wl = 2 := by
    simpa [wl] using
      (MulEquiv.orderOf_eq (MulAut.conjNormal (H := L) c) zl).trans hz2'
  have hneL : zl ≠ wl := by
    intro h
    apply hne
    have hcoe : (wl : Q) = (zl : Q) := congrArg Subtype.val h.symm
    simpa [zl, wl, MulAut.conjNormal_apply] using hcoe
  have hcommL : zl * wl = wl * zl := by
    apply Subtype.ext
    simpa [zl, wl, MulAut.conjNormal_apply] using hcomm.symm
  let U : Subgroup ↥L := Subgroup.zpowers zl ⊔ Subgroup.zpowers wl
  have hU : IsFourSubgroup U :=
    CFSG.GH74.GLS.LU.Local.isFourSubgroup_zpowers_sup hz2' hw2' hneL hcommL
  have hzlU : zl ∈ U := Subgroup.mem_sup_left (Subgroup.mem_zpowers zl)
  have hwlU : wl ∈ U := Subgroup.mem_sup_right (Subgroup.mem_zpowers wl)
  have hgen : Subgroup.closure ((O2z zl : Set ↥L) ∪ (O2z wl : Set ↥L)) = ⊤ := by
    have hst : CFSG.Open.StatedClassicalModel ↥L .PSL 3 3 1 :=
      CFSG.Blueprint.LieModel.statedClassicalModel hL (by decide)
    obtain ⟨F, hF, hFin, hcard, he⟩ := hst.2
    have hE : IsLnEps 3 ↥L 1 (3 ^ 1) := Or.inl ⟨rfl, F, hF, hFin, hcard, he⟩
    exact (ivk_4_4a (K := ↥L) (ε := 1) (p := 3) (n := 1) (by norm_num) (by norm_num)
      hE U hU zl hzlU wl hwlU hz2' hw2' hneL).2 (by norm_num)
  have hmapC : (Subgroup.centralizer ({zl} : Set ↥L)).map L.subtype =
      L ⊓ Subgroup.centralizer ({z} : Set Q) := by
    simpa [zl] using
      CFSG.ClassicalInvolution.Models.SymplecticPairs.map_subtype_centralizer_singleton L zl
  have hO2z_le_H : (O2z zl).map L.subtype ≤ H := by
    have hcent : O2z zl ≤ Subgroup.centralizer ({zl} : Set ↥L) := by
      unfold O2z
      exact Subgroup.map_subtype_le _
    have h := Subgroup.map_mono (f := L.subtype) hcent
    rw [hmapC] at h
    exact h.trans hC
  have hO2z_w_eq : (O2z wl).map L.subtype =
      ((O2z zl).map L.subtype).map (MulAut.conj c).toMonoidHom := by
    have hψ : (O2z zl).map (MulAut.conjNormal (H := L) c).toMonoidHom = O2z wl := by
      simpa [wl] using O2z_map (MulAut.conjNormal (H := L) c) zl
    rw [← hψ, Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hHmap : H.map (MulAut.conj c).toMonoidHom = H :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hcH)
  have hO2z_w_le_H : (O2z wl).map L.subtype ≤ H := by
    rw [hO2z_w_eq]
    calc ((O2z zl).map L.subtype).map (MulAut.conj c).toMonoidHom
        ≤ H.map (MulAut.conj c).toMonoidHom := Subgroup.map_mono hO2z_le_H
      _ = H := hHmap
  have hsup : (O2z zl).map L.subtype ⊔ (O2z wl).map L.subtype = L := by
    rw [← Subgroup.map_sup, Subgroup.sup_eq_closure, hgen, Subgroup.map_top,
      Subgroup.range_subtype]
  rw [← hsup]
  exact sup_le hO2z_le_H hO2z_w_le_H

end CFSG.LocalAnalysis.WeakClosure81.FourEleven
