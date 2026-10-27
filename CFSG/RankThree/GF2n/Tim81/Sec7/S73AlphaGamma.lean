module

public import CFSG.RankThree.GF2n.Tim81.Sec7.Stmts
public import CFSG.RankThree.GF2n.Tim81.Sec7.S71TI
public import CFSG.RankThree.GF2n.Tim81.Cited.Sec7
import CFSG.RankThree.GF2n.Tim81.Sec7.S73Alpha
import CFSG.RankThree.GF2n.Tim81.Sec7.S73TwoFour
import CFSG.RankThree.GF2n.Tim81.Sec7.S73Irred4
import CFSG.RankThree.GF2n.Tim81.Sec7.S73Five
import CFSG.GroupTheory.Commutator.ThreeSubgroupsModNormal

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n
open CFSG.RankThree.GF2n.Tim81.Sec7 (rOf oOf yOf)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M V A B : Subgroup G} {h : G} {n f : ℕ}

namespace L2Datum

private theorem two_mem_p0Of_of_mem_Op_p'p (hS : Sec7Hyp M V n f)
    (h71 : Sec7.Stmt71 M V) (h72 : Sec7.Stmt72 M V n f) (hLP : UnitaryLinePair)
    (hAut : UnitaryAutCentralizer) (hAut4 : UnitaryFourAutCentralizer)
    (hD : L2Datum M V A B h) :
    ∀ y ∈ inSubgroup (Op_p'p 2) (rOf M h), IsPGroup 2 (Subgroup.zpowers y) →
      y ∈ p0Of M V (A ⊔ B) := by
  intro y hyU hy2
  have hyR : y ∈ rOf M h := Subgroup.map_subtype_le _ hyU
  rcases Nat.eq_or_lt_of_le hS.four_le with h4 | h5
  · refine mem_p0_of_two_four hS h71 h72 hLP hAut4 hD h4.symm hyR hy2 ?_
    exact fun p hp => commutator_mem_V_of_mem_Op_p'p hS h72 hD
      (fun N hVN hNP hKN => irred_four hS h72 hLP hD h4.symm N hVN hNP hKN) hyU hp
  · exact mem_p0_of_two_five hS h71 h72 hAut hD (Nat.succ_le_of_lt h5) hyR hy2
      fun r hr => commutator_U_r0 hS h72 hD (Nat.succ_le_of_lt h5) hyU hr

private theorem two_mem_V_of_mem_centralizer_p0Of (hS : Sec7Hyp M V n f)
    (h71 : Sec7.Stmt71 M V) (h72 : Sec7.Stmt72 M V n f) (hLP : UnitaryLinePair)
    (hAut : UnitaryAutCentralizer) (hAut4 : UnitaryFourAutCentralizer)
    (hD : L2Datum M V A B h) :
    ∀ y ∈ rOf M h ⊓ cenOf (p0Of M V (A ⊔ B)), IsPGroup 2 (Subgroup.zpowers y) → y ∈ V := by
  obtain ⟨hS1, -, -, hS4, -, hS6, -, hS8, -, -⟩ := h72 A B h hD
  intro y hy hy2
  have hyR : y ∈ rOf M h := (Subgroup.mem_inf.mp hy).1
  have hyC : y ∈ cenOf (p0Of M V (A ⊔ B)) := (Subgroup.mem_inf.mp hy).2
  have hzero : ∀ p ∈ p0Of M V (A ⊔ B), ⁅y, p⁆ ∈ V := by
    intro p hp
    have h1 : ⁅y, p⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        ((Subgroup.mem_centralizer_iff.mp hyC) p hp).symm
    rw [h1]
    exact Subgroup.one_mem V
  rcases Nat.eq_or_lt_of_le hS.four_le with h4 | h5
  · have hyP0 := mem_p0_of_two_four hS h71 h72 hLP hAut4 hD h4.symm hyR hy2 hzero
    have hmem : y ∈ p0Of M V (A ⊔ B) ⊓ cenOf (p0Of M V (A ⊔ B)) := ⟨hyP0, hyC⟩
    rwa [hS4] at hmem
  · have hcommV : ∀ r ∈ r0Of M V (A ⊔ B), ⁅y, r⁆ ∈ Pc M V := by
      intro r hr
      have hcommR0 : ⁅y, r⁆ ∈ r0Of M V (A ⊔ B) := by
        have h1 : y * r * y⁻¹ ∈ r0Of M V (A ⊔ B) :=
          (Subgroup.mem_normalizer_iff.mp
            (rOf_le_normalizer_r0 hS.toSec6Hyp hD hS6 hyR) r).mp hr
        have h2 := (r0Of M V (A ⊔ B)).mul_mem h1 ((r0Of M V (A ⊔ B)).inv_mem hr)
        simpa [commutatorElement_def] using h2
      have hcommC : ⁅y, r⁆ ∈ cenOf (p0Of M V (A ⊔ B)) := by
        have hrR : r ∈ rOf M h :=
          (r0_le_inf_cenOf hS.toSec6Hyp hD).trans (inf_cenOf_le_rOf hD) hr
        have h1 : r * y * r⁻¹ ∈ cenOf (p0Of M V (A ⊔ B)) :=
          CFSG.GroupTheory.conj_mem_centralizer_of_le_normalizer
            (A := cenOf (p0Of M V (A ⊔ B))) (B := rOf M h)
            (K := p0Of M V (A ⊔ B))
            (rOf_le_normalizer_p0 hS.toSec6Hyp hD hS1) le_rfl r hrR y hyC
        have h2 := (cenOf (p0Of M V (A ⊔ B))).mul_mem h1
          ((cenOf (p0Of M V (A ⊔ B))).inv_mem hyC)
        have h3 : ⁅r, y⁆ ∈ cenOf (p0Of M V (A ⊔ B)) := by
          simpa [commutatorElement_def] using h2
        simpa [commutatorElement_inv] using (cenOf (p0Of M V (A ⊔ B))).inv_mem h3
      have hmem : ⁅y, r⁆ ∈ r0Of M V (A ⊔ B) ⊓ cenOf (p0Of M V (A ⊔ B)) := ⟨hcommR0, hcommC⟩
      rw [hS8] at hmem
      exact hS.sec5.toRootHyp.toHyp.le_Pc hmem
    have hyP0 := mem_p0_of_two_five hS h71 h72 hAut hD (Nat.succ_le_of_lt h5) hyR hy2 hcommV
    have hmem : y ∈ p0Of M V (A ⊔ B) ⊓ cenOf (p0Of M V (A ⊔ B)) := ⟨hyP0, hyC⟩
    rwa [hS4] at hmem

end L2Datum

theorem Sec7Hyp.stmt73alpha (hS : Sec7Hyp M V n f) (h71 : Sec7.Stmt71 M V)
    (h72 : Sec7.Stmt72 M V n f) (hLP : UnitaryLinePair) (hAut : UnitaryAutCentralizer)
    (hAut4 : UnitaryFourAutCentralizer) : Sec7.Stmt73alpha M V := by
  intro A B h hD
  have hU := L2Datum.two_mem_p0Of_of_mem_Op_p'p hS h71 h72 hLP hAut hAut4 hD
  have hT := L2Datum.two_mem_V_of_mem_centralizer_p0Of hS h71 h72 hLP hAut hAut4 hD
  exact ⟨L2Datum.Op_p'p_rOf_eq_oOf_sup_p0Of hS h72 hD hU, oOf_inf_p0Of M V (A ⊔ B) h,
    L2Datum.commutator_oOf_p0 hS h72 hD, L2Datum.rOf_inf_cenOf_p0Of_eq hS h72 hD hT, hU,
    L2Datum.generalizedFitting_quot_rOf_eq_pCore hS h72 hD hU hT,
    L2Datum.pCore_quot_rOf_eq_map_p0Of hS h72 hD hU⟩

theorem Sec7Hyp.stmt73gamma (hS : Sec7Hyp M V n f) (h71 : Sec7.Stmt71 M V)
    (h72 : Sec7.Stmt72 M V n f) (hLP : UnitaryLinePair) (hAut : UnitaryAutCentralizer)
    (hAut4 : UnitaryFourAutCentralizer) (hSU3 : SU3ModuleBound) (hTI : UnitaryTIModule)
    (h71TI : Sec7.Stmt71TI M V) : Sec7.Stmt73gamma M V := by
  intro A B h hD
  have hU := L2Datum.two_mem_p0Of_of_mem_Op_p'p hS h71 h72 hLP hAut hAut4 hD
  have hirr : ∀ N : Subgroup G, V ≤ N → N ≤ p0Of M V (A ⊔ B) →
      M ⊓ cenOf (A ⊔ B) ≤ Subgroup.normalizer (N : Set G) →
      N = V ∨ N = p0Of M V (A ⊔ B) := by
    intro N hVN hNP hKN
    rcases Nat.eq_or_lt_of_le hS.four_le with h4 | h5
    · exact L2Datum.irred_four hS h72 hLP hD h4.symm N hVN hNP hKN
    · exact L2Datum.irred_five hS h72 hSU3 hTI h71TI hD (Nat.succ_le_of_lt h5) N hVN hNP
        ((L2Datum.r0_le_inf_cenOf hS.toSec6Hyp hD).trans hKN)
  exact ⟨hirr, L2Datum.maximal_V_elemAbelian_rOf hS h72 hD hU hirr⟩

end CFSG.RankThree.GF2n.Tim81
