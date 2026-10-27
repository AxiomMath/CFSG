module

public import CFSG.RankThree.GF2n.Tim81.Sec7.Stmts
public import CFSG.RankThree.GF2n.Tim81.Sec7.S73Images
import CFSG.RankThree.GF2n.Tim81.Sec7.S73Split
import CFSG.RankThree.GF2n.Tim81.Sec7.S73Base
import CFSG.RankThree.GF2n.Tim81.Sec6.M0Setup
import CFSG.RankThree.GF2n.Tim81.Sec7.Images
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n
open CFSG.RankThree.GF2n.Tim81.Sec7 (rOf oOf yOf)
open scoped commutatorElement MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G] {M V A B : Subgroup G} {h : G} {n f : ℕ}

private theorem conj_p0Of_eq (hS : Sec6Hyp M V) {X : Subgroup G} (g : ↥M) :
    conjSubgroup (g : G) (p0Of M V X) = p0Of M V (conjSubgroup (g : G) X) := by
  have hP : conjSubgroup (g : G) (Pc M V) = Pc M V :=
    conjSubgroup_eq_self_iff.mpr (hS.sec5.toRootHyp.toHyp.le_normalizer_Pc g.2)
  rw [p0Of, p0Of, conjSubgroup_inf, hP,
    show cenOf (conjSubgroup (g : G) X) = conjSubgroup (g : G) (cenOf X) from
      centralizer_conjSubgroup_eq (g : G) X]

theorem L2Datum.exists_swap (hS : Sec7Hyp M V n f) (hLP : UnitaryLinePair)
    (hD : L2Datum M V A B h) (h4 : n = 4) :
    ∃ g : ↥M, imgQ M (conjSubgroup (g : G) (A ⊔ B)) = imgQ M (r0Of M V (A ⊔ B)) ∧
      imgQ M (conjSubgroup (g : G) (r0Of M V (A ⊔ B))) = imgQ M (A ⊔ B) ∧
      Nat.card ↥(imgQ M (m0Of M V) ⊓ Subgroup.centralizer
        ((imgQ M (A ⊔ B) ⊔ imgQ M (r0Of M V (A ⊔ B)) : Subgroup (MBar M)) :
          Set (MBar M))) = 2 ^ f + 1 := by
  subst h4
  have hAM : A ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hD.memA).1
  have hBM : B ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hD.memB).1
  have h2f : 2 ≤ f := by
    have h4 : 4 ≤ 2 ^ f := by
      rw [← hS.card_V]
      exact hS.sec5.toRootHyp.four_le_card
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using h4)
  have hLP4 := (hLP (MBar M) (imgQ M (m0Of M V)) (imgQ M '' sigmaSet M V) f 4
    hS.one_le le_rfl h2f hS.m0 (imgQ M A) ⟨A, hD.memA, rfl⟩ (imgQ M B)
    ⟨B, hD.memB, rfl⟩
    (Sec6Hyp.isL2Gen_imgQ hS.toSec6Hyp hD.memA hD.memB hD.l2)).2.2 rfl
  obtain ⟨C, -, D, -, -, hperp, hcard, g', hg'X, hg'₁, hg'₂⟩ := hLP4
  have hperp' : C ⊔ D = imgQ M (r0Of M V (A ⊔ B)) :=
    hperp.symm.trans (L2Datum.perpRoots_eq hS.toSec6Hyp hD)
  obtain ⟨g, -, hgg'⟩ := mem_imgQ_iff.mp hg'X
  refine ⟨g, ?_, ?_, ?_⟩
  · rw [imgQ_conjSubgroup g (A ⊔ B), hgg', imgQ_sup hAM hBM, hg'₁, hperp']
  · rw [imgQ_conjSubgroup g (r0Of M V (A ⊔ B)), hgg', ← hperp', hg'₂, imgQ_sup hAM hBM]
  · rw [imgQ_sup hAM hBM, ← hperp']
    exact hcard

theorem L2Datum.mem_conj_p0_iff (hS : Sec7Hyp M V n f) (h72 : Sec7.Stmt72 M V n f)
    (hD : L2Datum M V A B h) (g : ↥M)
    (hg : imgQ M (conjSubgroup (g : G) (A ⊔ B)) = imgQ M (r0Of M V (A ⊔ B)))
    {p : G} (hp : p ∈ Pc M V) :
    p ∈ conjSubgroup (g : G) (p0Of M V (A ⊔ B)) ↔
      ∀ r ∈ r0Of M V (A ⊔ B), ⁅r, p⁆ ∈ V := by
  have hAM : A ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hD.memA).1
  have hBM : B ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hD.memB).1
  have hXM : A ⊔ B ≤ M := _root_.sup_le hAM hBM
  have hPM : Pc M V ≤ M := hS.sec5.toRootHyp.toHyp.Pc_le_M
  have hR0M : r0Of M V (A ⊔ B) ≤ M :=
    (L2Datum.r0_le_inf_cenOf hS.toSec6Hyp hD).trans inf_le_left
  have hconjM : conjSubgroup (g : G) (A ⊔ B) ≤ M := by
    have h1 : conjSubgroup (g : G) (A ⊔ B) ≤ conjSubgroup (g : G) M := conjSubgroup_mono hXM
    rwa [show conjSubgroup (g : G) M = M from
      conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer g.2)] at h1
  have hR0X : r0Of M V (A ⊔ B) ≤ conjSubgroup (g : G) (A ⊔ B) ⊔ Pc M V :=
    hS.toSec6Hyp.le_sup_Pc_of_imgQ_le hR0M (le_of_eq hg.symm)
  have hXgR : conjSubgroup (g : G) (A ⊔ B) ≤ r0Of M V (A ⊔ B) ⊔ Pc M V :=
    hS.toSec6Hyp.le_sup_Pc_of_imgQ_le hconjM (le_of_eq hg)
  have hconjEq : conjSubgroup (g : G) (p0Of M V (A ⊔ B)) =
      p0Of M V (conjSubgroup (g : G) (A ⊔ B)) := conj_p0Of_eq hS.toSec6Hyp g
  constructor
  · intro hpconj r hr
    have hpP : p ∈ Pc M V := by
      rw [hconjEq] at hpconj
      exact (Subgroup.mem_inf.mp hpconj).1
    have hpC : p ∈ cenOf (conjSubgroup (g : G) (A ⊔ B)) := by
      rw [hconjEq] at hpconj
      exact (Subgroup.mem_inf.mp hpconj).2
    have h1 : ∀ x ∈ conjSubgroup (g : G) (A ⊔ B), ⁅p, x⁆ ∈ V := by
      intro x hx
      have hcomm : p * x = x * p := (Subgroup.mem_centralizer_iff.mp hpC x hx).symm
      rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
      exact V.one_mem
    have h2 : ∀ x ∈ Pc M V, ⁅p, x⁆ ∈ V := by
      intro x hx
      have hmem : ⁅p, x⁆ ∈ ⁅Pc M V, Pc M V⁆ := Subgroup.commutator_mem_commutator hp hx
      rwa [hS.sec5.commutator_Pc_eq_V hS.ne] at hmem
    have h3 : ∀ x ∈ conjSubgroup (g : G) (A ⊔ B) ⊔ Pc M V, ⁅p, x⁆ ∈ V :=
      Sec6Hyp.commutator_mem_of_mem_sup hS.toSec6Hyp hconjM hPM h1 h2
    have hpr : ⁅p, r⁆ ∈ V := h3 r (hR0X hr)
    simpa using V.inv_mem hpr
  · intro hpV
    have h1 : ∀ x ∈ r0Of M V (A ⊔ B), ⁅p, x⁆ ∈ V := by
      intro x hx
      simpa using V.inv_mem (hpV x hx)
    have h2 : ∀ x ∈ Pc M V, ⁅p, x⁆ ∈ V := by
      intro x hx
      have hmem : ⁅p, x⁆ ∈ ⁅Pc M V, Pc M V⁆ := Subgroup.commutator_mem_commutator hp hx
      rwa [hS.sec5.commutator_Pc_eq_V hS.ne] at hmem
    have h3 : ∀ x ∈ r0Of M V (A ⊔ B) ⊔ Pc M V, ⁅p, x⁆ ∈ V :=
      Sec6Hyp.commutator_mem_of_mem_sup hS.toSec6Hyp hR0M hPM h1 h2
    have hhX : g * h * (g : G)⁻¹ ∈ conjSubgroup (g : G) (A ⊔ B) := by
      rw [mem_conjSubgroup]
      have hge : (g : G)⁻¹ * (g * h * (g : G)⁻¹) * g = h := by group
      rw [hge]
      exact hD.mem
    have hhV : ⁅p, g * h * (g : G)⁻¹⁆ ∈ V := h3 _ (hXgR hhX)
    have hhV' : ⁅g * h * (g : G)⁻¹, p⁆ ∈ V := by
      simpa using V.inv_mem hhV
    have hdatum := hD.conj hS.toSec6Hyp g.2
    have hS1' := (h72 (conjSubgroup (g : G) A) (conjSubgroup (g : G) B)
      (g * h * (g : G)⁻¹) hdatum).1
    have hp0 := L2Datum.mem_p0_of_commutator_mem hS hdatum hS1' hp hhV'
    rw [conj_p0Of_eq hS.toSec6Hyp g, conjSubgroup_sup]
    exact hp0

theorem L2Datum.Pc_eq_p0_sup_conj (hS : Sec7Hyp M V n f) (h72 : Sec7.Stmt72 M V n f)
    (hD : L2Datum M V A B h) (g : ↥M)
    (hg : imgQ M (conjSubgroup (g : G) (A ⊔ B)) = imgQ M (r0Of M V (A ⊔ B))) :
    Pc M V = p0Of M V (A ⊔ B) ⊔ conjSubgroup (g : G) (p0Of M V (A ⊔ B)) := by
  have hAM : A ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hD.memA).1
  have hBM : B ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hD.memB).1
  have hS1 := (h72 A B h hD).1
  have hEP : ⁅Pc M V, A ⊔ B⁆ ≤ Pc M V :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((_root_.sup_le hAM hBM).trans hS.sec5.toRootHyp.toHyp.le_normalizer_Pc)
  refine le_antisymm ?_ ?_
  · rw [L2Datum.Pc_eq_p0_sup hS hD hS1]
    refine _root_.sup_le le_sup_left ?_
    intro e he
    refine Subgroup.mem_sup_right ?_
    refine (L2Datum.mem_conj_p0_iff hS h72 hD g hg (hEP he)).mpr ?_
    intro r hr
    have hcen : r ∈ cenOf ⁅Pc M V, A ⊔ B⁆ := L2Datum.r0_le_cenOf_commutator hS.toSec6Hyp hD hr
    have hcomm : e * r = r * e := Subgroup.mem_centralizer_iff.mp hcen e he
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm.symm]
    exact V.one_mem
  · refine _root_.sup_le inf_le_left ?_
    rw [conj_p0Of_eq hS.toSec6Hyp g]
    exact inf_le_left

private theorem Pc_inf_cenOf_le_normalizer (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h) :
    (Pc M V ⊓ cenOf A) ≤ Subgroup.normalizer (Pc M V ⊓ cenOf B) := by
  refine (Subgroup.le_normalizer_iff_commutator_le_right (H := Pc M V ⊓ cenOf A)
    (K := Pc M V ⊓ cenOf B)).mpr ?_
  calc ⁅Pc M V ⊓ cenOf A, Pc M V ⊓ cenOf B⁆ ≤ ⁅Pc M V, Pc M V⁆ :=
        Subgroup.commutator_mono inf_le_left inf_le_left
    _ = V := hS.sec5.commutator_Pc_eq_V hS.ne
    _ ≤ Pc M V ⊓ cenOf B :=
        le_inf hS.sec5.toRootHyp.toHyp.le_Pc
          (((L2Datum.V_le_p0 hS.toSec6Hyp hD).trans inf_le_right).trans
            (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_right)))

private theorem Pc_eq_centralizer_sup (hS : Sec7Hyp M V n f) (h72 : Sec7.Stmt72 M V n f)
    (hD : L2Datum M V A B h) :
    Pc M V = (Pc M V ⊓ cenOf A) ⊔ (Pc M V ⊓ cenOf B) := by
  have hnorm := Pc_inf_cenOf_le_normalizer hS hD
  have hprod :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := Pc M V ⊓ cenOf A) (K := Pc M V ⊓ cenOf B) hnorm
  have hS2 := (h72 A B h hD).2.1
  have hn4 : 4 ≤ n := hS.four_le
  have hHcard : Nat.card ↥(Pc M V ⊓ cenOf A) = Nat.card V ^ (2 * n - 1) := by
    have h1 : Nat.card ↥(Pc M V ⊓ cenOf A) * Nat.card V ^ 2 = Nat.card V ^ (2 * n + 1) := by
      rw [← hS.card_Pc]
      exact hS.sec5.card_Pc_inf_centralizer hD.memA
    have h2 : Nat.card V ^ (2 * n - 1) * Nat.card V ^ 2 = Nat.card V ^ (2 * n + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [← h2] at h1
    exact Nat.mul_right_cancel (pow_pos Nat.card_pos 2) h1
  have hKcard : Nat.card ↥(Pc M V ⊓ cenOf B) = Nat.card V ^ (2 * n - 1) := by
    have h1 : Nat.card ↥(Pc M V ⊓ cenOf B) * Nat.card V ^ 2 = Nat.card V ^ (2 * n + 1) := by
      rw [← hS.card_Pc]
      exact hS.sec5.card_Pc_inf_centralizer hD.memB
    have h2 : Nat.card V ^ (2 * n - 1) * Nat.card V ^ 2 = Nat.card V ^ (2 * n + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [← h2] at h1
    exact Nat.mul_right_cancel (pow_pos Nat.card_pos 2) h1
  have hinter : (Pc M V ⊓ cenOf A) ⊓ (Pc M V ⊓ cenOf B) = p0Of M V (A ⊔ B) := by
    have hsplit : Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) =
        Subgroup.centralizer (A : Set G) ⊓ Subgroup.centralizer (B : Set G) :=
      CFSG.centralizer_sup_eq (G := G) (H := A) (K := B)
    rw [p0Of]
    change (Pc M V ⊓ cenOf A) ⊓ (Pc M V ⊓ cenOf B) =
      Pc M V ⊓ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G)
    rw [hsplit]
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  have hjoin : Nat.card ↥((Pc M V ⊓ cenOf A) ⊔ (Pc M V ⊓ cenOf B)) =
      Nat.card V ^ (2 * n + 1) := by
    have h1 : Nat.card ↥((Pc M V ⊓ cenOf A) ⊔ (Pc M V ⊓ cenOf B)) *
        Nat.card V ^ (2 * n - 3) =
        Nat.card V ^ (2 * n - 1) * Nat.card V ^ (2 * n - 1) := by
      have h := hprod
      rw [hinter, hS2, hHcard, hKcard] at h
      exact h
    have h2 : Nat.card V ^ (2 * n - 1) * Nat.card V ^ (2 * n - 1) =
        Nat.card V ^ (2 * n + 1) * Nat.card V ^ (2 * n - 3) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    rw [h2] at h1
    exact Nat.mul_right_cancel (pow_pos Nat.card_pos (2 * n - 3)) h1
  have hle : (Pc M V ⊓ cenOf A) ⊔ (Pc M V ⊓ cenOf B) ≤ Pc M V :=
    _root_.sup_le inf_le_left inf_le_left
  have hcardle : Nat.card ↥(Pc M V) ≤
      Nat.card ↥((Pc M V ⊓ cenOf A) ⊔ (Pc M V ⊓ cenOf B)) := by
    rw [hjoin, hS.card_Pc]
  exact (Subgroup.eq_of_le_of_card_ge hle hcardle).symm

theorem L2Datum.p0_inf_conj_p0 (hS : Sec7Hyp M V n f) (h72 : Sec7.Stmt72 M V n f)
    (hD : L2Datum M V A B h) (h4 : n = 4) (g : ↥M)
    (hg : imgQ M (conjSubgroup (g : G) (A ⊔ B)) = imgQ M (r0Of M V (A ⊔ B))) :
    p0Of M V (A ⊔ B) ⊓ conjSubgroup (g : G) (p0Of M V (A ⊔ B)) = V := by
  subst h4
  have hVle : V ≤ p0Of M V (A ⊔ B) := L2Datum.V_le_p0 hS.toSec6Hyp hD
  have hVleK : V ≤ conjSubgroup (g : G) (p0Of M V (A ⊔ B)) := by
    have h1 : conjSubgroup (g : G) V ≤ conjSubgroup (g : G) (p0Of M V (A ⊔ B)) :=
      conjSubgroup_mono hVle
    rwa [show conjSubgroup (g : G) V = V from
      conjSubgroup_eq_self_iff.mpr (hS.sec5.toRootHyp.toHyp.le_normalizer g.2)] at h1
  have hKle : conjSubgroup (g : G) (p0Of M V (A ⊔ B)) ≤ Pc M V := by
    have h1 : conjSubgroup (g : G) (p0Of M V (A ⊔ B)) ≤ conjSubgroup (g : G) (Pc M V) :=
      conjSubgroup_mono inf_le_left
    rwa [show conjSubgroup (g : G) (Pc M V) = Pc M V from
      conjSubgroup_eq_self_iff.mpr (hS.sec5.toRootHyp.toHyp.le_normalizer_Pc g.2)] at h1
  have hPK : Pc M V ≤ Subgroup.normalizer
      (conjSubgroup (g : G) (p0Of M V (A ⊔ B))) := by
    refine (Subgroup.le_normalizer_iff_commutator_le_right (H := Pc M V)
      (K := conjSubgroup (g : G) (p0Of M V (A ⊔ B)))).mpr ?_
    calc ⁅Pc M V, conjSubgroup (g : G) (p0Of M V (A ⊔ B))⁆ ≤ ⁅Pc M V, Pc M V⁆ :=
          Subgroup.commutator_mono le_rfl hKle
      _ = V := hS.sec5.commutator_Pc_eq_V hS.ne
      _ ≤ conjSubgroup (g : G) (p0Of M V (A ⊔ B)) := hVleK
  have hprod :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := p0Of M V (A ⊔ B))
      (K := conjSubgroup (g : G) (p0Of M V (A ⊔ B))) (inf_le_left.trans hPK)
  have hS2 := (h72 A B h hD).2.1
  have hcardK : Nat.card ↥(conjSubgroup (g : G) (p0Of M V (A ⊔ B))) =
      Nat.card ↥(p0Of M V (A ⊔ B)) := card_conjSubgroup (g : G) _
  have hprod' : Nat.card V ^ 9 * Nat.card ↥(p0Of M V (A ⊔ B) ⊓
      conjSubgroup (g : G) (p0Of M V (A ⊔ B))) =
      Nat.card V ^ 5 * Nat.card V ^ 5 := by
    have h := hprod
    rw [← L2Datum.Pc_eq_p0_sup_conj hS h72 hD g hg, hcardK, hS2, hS.card_Pc] at h
    simpa using h
  have hmeet : Nat.card ↥(p0Of M V (A ⊔ B) ⊓
      conjSubgroup (g : G) (p0Of M V (A ⊔ B))) = Nat.card V := by
    have h2 : Nat.card V ^ 5 * Nat.card V ^ 5 = Nat.card V ^ 9 * Nat.card V := by
      ring
    rw [h2] at hprod'
    exact Nat.mul_left_cancel (pow_pos Nat.card_pos 9) hprod'
  exact (Subgroup.eq_of_le_of_card_ge (_root_.le_inf hVle hVleK) (le_of_eq hmeet)).symm

theorem L2Datum.rOf_le_normalizer_conj_p0 (hS : Sec7Hyp M V n f)
    (h72 : Sec7.Stmt72 M V n f) (hD : L2Datum M V A B h) (g : ↥M)
    (hg : imgQ M (conjSubgroup (g : G) (A ⊔ B)) = imgQ M (r0Of M V (A ⊔ B))) :
    rOf M h ≤ Subgroup.normalizer
      (conjSubgroup (g : G) (p0Of M V (A ⊔ B)) : Set G) := by
  have hS6 := (h72 A B h hD).2.2.2.2.2.1
  have hPnorm : rOf M h ≤ Subgroup.normalizer (Pc M V : Set G) :=
    inf_le_left.trans hS.sec5.toRootHyp.toHyp.le_normalizer_Pc
  have hR0norm : rOf M h ≤ Subgroup.normalizer (r0Of M V (A ⊔ B) : Set G) :=
    L2Datum.rOf_le_normalizer_r0 hS.toSec6Hyp hD hS6
  have hVnorm : rOf M h ≤ Subgroup.normalizer (V : Set G) :=
    inf_le_left.trans hS.sec5.toRootHyp.toHyp.le_normalizer
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro k
  constructor
  · intro hk
    have hk' : k ∈ p0Of M V (conjSubgroup (g : G) (A ⊔ B)) := by
      rwa [conj_p0Of_eq hS.toSec6Hyp g] at hk
    have hkP : k ∈ Pc M V := (Subgroup.mem_inf.mp hk').1
    have hkP' : y * k * y⁻¹ ∈ Pc M V :=
      (Subgroup.mem_normalizer_iff.mp (hPnorm hy) k).mp hkP
    refine (L2Datum.mem_conj_p0_iff hS h72 hD g hg hkP').mpr ?_
    intro r hr
    have hr' : y⁻¹ * r * y ∈ r0Of M V (A ⊔ B) := by
      have h := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (r0Of M V (A ⊔ B) : Set G)).inv_mem (hR0norm hy)) r).mp hr
      simpa using h
    have h1 : ⁅y⁻¹ * r * y, k⁆ ∈ V :=
      (L2Datum.mem_conj_p0_iff hS h72 hD g hg hkP).mp hk _ hr'
    have h2 : y * ⁅y⁻¹ * r * y, k⁆ * y⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hVnorm hy) _).mp h1
    have h3 : ⁅r, y * k * y⁻¹⁆ = y * ⁅y⁻¹ * r * y, k⁆ * y⁻¹ := by
      rw [conjugate_commutatorElement, show y * (y⁻¹ * r * y) * y⁻¹ = r by group]
    rw [h3]
    exact h2
  · intro hk
    have hk'' : y * k * y⁻¹ ∈ p0Of M V (conjSubgroup (g : G) (A ⊔ B)) := by
      rwa [conj_p0Of_eq hS.toSec6Hyp g] at hk
    have hkP : y * k * y⁻¹ ∈ Pc M V := (Subgroup.mem_inf.mp hk'').1
    have hkP' : k ∈ Pc M V :=
      (Subgroup.mem_normalizer_iff.mp (hPnorm hy) k).mpr hkP
    refine (L2Datum.mem_conj_p0_iff hS h72 hD g hg hkP').mpr ?_
    intro r hr
    have hr'' : y * r * y⁻¹ ∈ r0Of M V (A ⊔ B) :=
      (Subgroup.mem_normalizer_iff.mp (hR0norm hy) r).mp hr
    have h1 : ⁅y * r * y⁻¹, y * k * y⁻¹⁆ ∈ V :=
      (L2Datum.mem_conj_p0_iff hS h72 hD g hg hkP).mp hk _ hr''
    have h2 : ⁅y * r * y⁻¹, y * k * y⁻¹⁆ = y * ⁅r, k⁆ * y⁻¹ := by
      rw [← conjugate_commutatorElement]
    have h3 : y * ⁅r, k⁆ * y⁻¹ ∈ V := by rw [← h2]; exact h1
    exact (Subgroup.mem_normalizer_iff.mp (hVnorm hy) _).mpr h3

private theorem commute_of_conj_eq (hS : Sec7Hyp M V n f) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) {m c : G} (hcm : c * m⁻¹ ∈ Pc M V)
    (hmV : ∀ x ∈ U, ⁅m, x⁆ ∈ Pc M V) (hcU : conjSubgroup c U = U) :
    ∀ x ∈ U, c * x = x * c := by
  intro x hx
  have hUM : U ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hU).1
  have hPM : Pc M V ≤ M := hS.sec5.toRootHyp.toHyp.Pc_le_M
  have hMP : M ≤ Subgroup.normalizer (Pc M V : Set G) := hS.sec5.toRootHyp.toHyp.le_normalizer_Pc
  have hMPc : ⁅Pc M V, M⁆ ≤ Pc M V := Subgroup.le_normalizer_iff_commutator_le_left.mp hMP
  have hxM : x ∈ M := hUM hx
  have hcxU : c * x * c⁻¹ ∈ U := by
    have hmem : c ∈ Subgroup.normalizer (U : Set G) := mem_normalizer_iff_conjSubgroup_eq.mpr hcU
    exact (Subgroup.mem_normalizer_iff.mp hmem x).mp hx
  have hcxP : ⁅c, x⁆ ∈ Pc M V := by
    have hqx : ⁅c * m⁻¹, x⁆ ∈ Pc M V :=
      hMPc (Subgroup.commutator_mem_commutator hcm hxM)
    have hmx : ⁅m, x⁆ ∈ Pc M V := hmV x hx
    have hqN : c * m⁻¹ ∈ Subgroup.normalizer (Pc M V : Set G) := hMP (hPM hcm)
    have hconj : (c * m⁻¹) * ⁅m, x⁆ * (c * m⁻¹)⁻¹ ∈ Pc M V :=
      (Subgroup.mem_normalizer_iff.mp hqN _).mp hmx
    have hsplit : ⁅c, x⁆ = (c * m⁻¹) * ⁅m, x⁆ * (c * m⁻¹)⁻¹ * ⁅c * m⁻¹, x⁆ := by
      conv_lhs => rw [show c = (c * m⁻¹) * m from by group]
      rw [commutatorElement_mul_left_eq_conj_mul]
    rw [hsplit]
    exact (Pc M V).mul_mem hconj hqx
  have hbot : ⁅c, x⁆ ∈ (⊥ : Subgroup G) := by
    rw [← hS.sec5.inf_Pc_eq_bot hU]
    refine Subgroup.mem_inf.mpr ⟨?_, hcxP⟩
    have h := U.mul_mem hcxU (U.inv_mem hx)
    simpa [commutatorElement_def] using h
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hbot)

private theorem exists_mem_Pc_conj_eq (hS : Sec7Hyp M V n f) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) {m : G} (hm : m ∈ M)
    (hle : conjSubgroup m U ≤ U ⊔ Pc M V) :
    ∃ p ∈ Pc M V, conjSubgroup m U = conjSubgroup p U := by
  have hUm : conjSubgroup m U ∈ sigmaSet M V := hS.sec5.conj_mem_sigmaSet hm hU
  have hUcard : Nat.card U = Nat.card V := by
    obtain ⟨a, rfl, -⟩ := hU
    exact card_conjSubgroup a V
  have hne : conjSubgroup m U ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card ↥(conjSubgroup m U) = Nat.card U := card_conjSubgroup m U
    rw [hbot, Subgroup.card_bot] at hcard
    have h4 : 4 ≤ Nat.card U := by rw [hUcard]; exact hS.sec5.toRootHyp.four_le_card
    omega
  exact hS.res.s55 M V hS.sec5 U hU (conjSubgroup m U) hUm
    (by rw [inf_eq_left.mpr hle]; exact hne)

private theorem conj_mk_swap (g : ↥M)
    (hg₁ : imgQ M (conjSubgroup (g : G) (A ⊔ B)) = imgQ M (r0Of M V (A ⊔ B)))
    (hg₂ : imgQ M (conjSubgroup (g : G) (r0Of M V (A ⊔ B))) = imgQ M (A ⊔ B)) :
    conjSubgroup (QuotientGroup.mk' (pCore 2 ↥M) g)
      (imgQ M (A ⊔ B) ⊔ imgQ M (r0Of M V (A ⊔ B))) =
      imgQ M (A ⊔ B) ⊔ imgQ M (r0Of M V (A ⊔ B)) := by
  rw [conjSubgroup_sup, ← imgQ_conjSubgroup g (A ⊔ B),
    ← imgQ_conjSubgroup g (r0Of M V (A ⊔ B)), hg₁, hg₂, sup_comm]


private theorem conjSubgroup_le_sup_Pc {U : Subgroup G}
    {m : G} (hm : ∀ x ∈ U, ⁅m, x⁆ ∈ Pc M V) :
    conjSubgroup m U ≤ U ⊔ Pc M V := by
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  change m * a * m⁻¹ ∈ U ⊔ Pc M V
  have h1 : ⁅m, a⁆ ∈ Pc M V := hm a ha
  have heq : m * a * m⁻¹ = ⁅m, a⁆ * a := by rw [commutatorElement_def]; group
  rw [heq]
  exact (U ⊔ Pc M V).mul_mem (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left ha)


private theorem exists_conj_eq_mul (hS : Sec7Hyp M V n f) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) {m : G} (hm : m ∈ M)
    (hmV : ∀ x ∈ U, ⁅m, x⁆ ∈ Pc M V) :
    ∃ p ∈ Pc M V, ∃ c : G, c = (p : G)⁻¹ * m ∧ conjSubgroup c U = U := by
  obtain ⟨p, hpP, hp⟩ := exists_mem_Pc_conj_eq hS hU hm (conjSubgroup_le_sup_Pc hmV)
  refine ⟨p, hpP, (p : G)⁻¹ * m, rfl, ?_⟩
  rw [← conjSubgroup_conjSubgroup (p : G)⁻¹ m U, hp,
    conjSubgroup_conjSubgroup (p : G)⁻¹ (p : G) U,
    show (p : G)⁻¹ * (p : G) = 1 by group, conjSubgroup_one]

private theorem exists_lift_conj (hS : Sec7Hyp M V n f) (h72 : Sec7.Stmt72 M V n f)
    (hD : L2Datum M V A B h) (m : ↥M)
    (hm : QuotientGroup.mk' (pCore 2 ↥M) m ∈
      Subgroup.centralizer (imgQ M (A ⊔ B) : Set (MBar M))) :
    ∃ c : ↥M, QuotientGroup.mk' (pCore 2 ↥M) c = QuotientGroup.mk' (pCore 2 ↥M) m ∧
      (c : G) * (m : G)⁻¹ ∈ Pc M V ∧ conjSubgroup (c : G) A = A ∧
        conjSubgroup (c : G) B = B := by
  have hAM : A ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hD.memA).1
  have hBM : B ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hD.memB).1
  have hXM : A ⊔ B ≤ M := _root_.sup_le hAM hBM
  have hPM : Pc M V ≤ M := hS.sec5.toRootHyp.toHyp.Pc_le_M
  have hcomm : ∀ y ∈ A ⊔ B, ⁅(m : G), y⁆ ∈ Pc M V :=
    (Sec6Hyp.mk_mem_centralizer_imgQ_iff hS.toSec6Hyp hXM m).mp hm
  obtain ⟨p₁, hp₁P, c₁, hc₁eq, hc₁A⟩ := exists_conj_eq_mul hS hD.memA m.2
    (fun x hx => hcomm x (Subgroup.mem_sup_left hx))
  obtain ⟨p₂, hp₂P, c₂, hc₂eq, hc₂B⟩ := exists_conj_eq_mul hS hD.memB m.2
    (fun x hx => hcomm x (Subgroup.mem_sup_right hx))
  have hmP : conjSubgroup (m : G) (Pc M V) = Pc M V :=
    conjSubgroup_eq_self_iff.mpr (hS.sec5.toRootHyp.toHyp.le_normalizer_Pc m.2)
  have htP : c₁⁻¹ * c₂ ∈ Pc M V := by
    have h1 : (p₁ : G) * (p₂ : G)⁻¹ ∈ Pc M V :=
      (Pc M V).mul_mem hp₁P ((Pc M V).inv_mem hp₂P)
    have h2 : (m : G)⁻¹ * ((p₁ : G) * (p₂ : G)⁻¹) * (m : G) ∈ Pc M V := by
      have h := (mem_conjSubgroup (g := (m : G)) (T := Pc M V)).mp
        (by rw [hmP]; exact h1)
      simpa using h
    have heq : c₁⁻¹ * c₂ = (m : G)⁻¹ * ((p₁ : G) * (p₂ : G)⁻¹) * (m : G) := by
      rw [hc₁eq, hc₂eq]
      group
    rw [heq]; exact h2
  have hnorm := Pc_inf_cenOf_le_normalizer hS hD
  have hcoe : ((Pc M V : Subgroup G) : Set G) =
      ((Pc M V ⊓ cenOf A : Subgroup G) : Set G) *
        ((Pc M V ⊓ cenOf B : Subgroup G) : Set G) := by
    conv_lhs => rw [Pc_eq_centralizer_sup hS h72 hD]
    exact Subgroup.coe_mul_of_left_le_normalizer_right _ _ hnorm
  have hmem : c₁⁻¹ * c₂ ∈ (Pc M V : Set G) := htP
  rw [hcoe] at hmem
  obtain ⟨u, huH, v, hvK, huv⟩ := Set.mem_mul.mp hmem
  have huP : u ∈ Pc M V := (Subgroup.mem_inf.mp huH).1
  have huA : conjSubgroup u A = A := by
    have h := Subgroup.centralizer_le_normalizer (A : Set G) (Subgroup.mem_inf.mp huH).2
    exact mem_normalizer_iff_conjSubgroup_eq.mp h
  have hvB : conjSubgroup ((v : G)⁻¹) B = B := by
    have hN := (Subgroup.normalizer (B : Set G)).inv_mem
      (Subgroup.centralizer_le_normalizer (B : Set G) (Subgroup.mem_inf.mp hvK).2)
    exact mem_normalizer_iff_conjSubgroup_eq.mp hN
  have hcM : c₁ * u ∈ M := by
    rw [hc₁eq]
    exact M.mul_mem (M.mul_mem (hPM ((Pc M V).inv_mem hp₁P)) m.2) (hPM huP)
  have hcmP : (c₁ * u) * (m : G)⁻¹ ∈ Pc M V := by
    have hun : (m : G) * u * (m : G)⁻¹ ∈ Pc M V :=
      (Subgroup.mem_normalizer_iff.mp (hS.sec5.toRootHyp.toHyp.le_normalizer_Pc m.2) u).mp huP
    have heq : (c₁ * u) * (m : G)⁻¹ = (p₁ : G)⁻¹ * ((m : G) * u * (m : G)⁻¹) := by
      rw [hc₁eq]; group
    rw [heq]
    exact (Pc M V).mul_mem ((Pc M V).inv_mem hp₁P) hun
  have hcAu : conjSubgroup (c₁ * u) A = A := by
    rw [← conjSubgroup_conjSubgroup, huA, hc₁A]
  have hcBu : conjSubgroup (c₁ * u) B = B := by
    have heq : c₁ * u = c₂ * (v : G)⁻¹ := by
      calc c₁ * u = c₁ * ((u : G) * (v : G)) * (v : G)⁻¹ := by group
        _ = c₁ * (c₁⁻¹ * c₂) * (v : G)⁻¹ := by rw [huv]
        _ = c₂ * (v : G)⁻¹ := by group
    rw [heq, ← conjSubgroup_conjSubgroup, hvB, hc₂B]
  have hmkc : QuotientGroup.mk' (pCore 2 ↥M) ⟨c₁ * u, hcM⟩ =
      QuotientGroup.mk' (pCore 2 ↥M) m := by
    have h1 : QuotientGroup.mk' (pCore 2 ↥M) ⟨c₁ * u, hcM⟩ *
        QuotientGroup.mk' (pCore 2 ↥M) m⁻¹ = 1 := by
      rw [← map_mul]
      exact (Sec6Hyp.mk_eq_one_iff hS.toSec6Hyp _).mpr (by simpa using hcmP)
    have h2 := congrArg (fun z => z * QuotientGroup.mk' (pCore 2 ↥M) m) h1
    simpa [mul_assoc] using h2
  exact ⟨⟨c₁ * u, hcM⟩, hmkc, hcmP, hcAu, hcBu⟩

theorem L2Datum.exists_lift_centralizer (hS : Sec7Hyp M V n f) (h72 : Sec7.Stmt72 M V n f)
    (hD : L2Datum M V A B h) (m : ↥M)
    (hm : QuotientGroup.mk' (pCore 2 ↥M) m ∈
      Subgroup.centralizer (imgQ M (A ⊔ B) : Set (MBar M))) :
    ∃ c : ↥M, QuotientGroup.mk' (pCore 2 ↥M) c = QuotientGroup.mk' (pCore 2 ↥M) m ∧
      (c : G) ∈ cenOf (A ⊔ B) := by
  obtain ⟨c, hmkc, hcm, hcA, hcB⟩ := exists_lift_conj hS h72 hD m hm
  have hAM : A ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hD.memA).1
  have hBM : B ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hD.memB).1
  have hXM : A ⊔ B ≤ M := _root_.sup_le hAM hBM
  have hcomm : ∀ y ∈ A ⊔ B, ⁅(m : G), y⁆ ∈ Pc M V :=
    (Sec6Hyp.mk_mem_centralizer_imgQ_iff hS.toSec6Hyp hXM m).mp hm
  have hcommA : ∀ a ∈ A, (c : G) * a = a * (c : G) :=
    commute_of_conj_eq hS hD.memA hcm
      (fun x hx => hcomm x (Subgroup.mem_sup_left hx)) hcA
  have hcommB : ∀ b ∈ B, (c : G) * b = b * (c : G) :=
    commute_of_conj_eq hS hD.memB hcm
      (fun x hx => hcomm x (Subgroup.mem_sup_right hx)) hcB
  refine ⟨c, hmkc, ?_⟩
  have hAc : A ≤ Subgroup.centralizer ({(c : G)} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcommA a ha).symm
  have hBc : B ≤ Subgroup.centralizer ({(c : G)} : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hcommB b hb).symm
  have hsup : A ⊔ B ≤ Subgroup.centralizer ({(c : G)} : Set G) := _root_.sup_le hAc hBc
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.mp (hsup hx)

private theorem twist_conj_mem (hS : Sec7Hyp M V n f)
    {g : ↥M} {z : MBar M} (hzX0 : z ∈ imgQ M (m0Of M V))
    (hzK : z ∈ Subgroup.centralizer
      ((imgQ M (A ⊔ B) ⊔ imgQ M (r0Of M V (A ⊔ B)) : Subgroup (MBar M)) : Set (MBar M)))
    (hg₁ : imgQ M (conjSubgroup (g : G) (A ⊔ B)) = imgQ M (r0Of M V (A ⊔ B)))
    (hg₂ : imgQ M (conjSubgroup (g : G) (r0Of M V (A ⊔ B))) = imgQ M (A ⊔ B)) :
    MulAut.conj (QuotientGroup.mk' (pCore 2 ↥M) g)⁻¹ z ∈
      imgQ M (m0Of M V) ⊓ Subgroup.centralizer
        ((imgQ M (A ⊔ B) ⊔ imgQ M (r0Of M V (A ⊔ B)) : Subgroup (MBar M)) : Set (MBar M)) := by
  have hX0 : (imgQ M (m0Of M V)).Normal := hS.sec5.imgQ_m0Of_normal
  have hz'X0 : MulAut.conj (QuotientGroup.mk' (pCore 2 ↥M) g)⁻¹ z ∈ imgQ M (m0Of M V) := by
    have h := hX0.conj_mem z hzX0 (QuotientGroup.mk' (pCore 2 ↥M) g)⁻¹
    simpa [MulAut.conj_apply] using h
  have hgK : conjSubgroup (QuotientGroup.mk' (pCore 2 ↥M) g)
      (imgQ M (A ⊔ B) ⊔ imgQ M (r0Of M V (A ⊔ B))) =
      imgQ M (A ⊔ B) ⊔ imgQ M (r0Of M V (A ⊔ B)) :=
    conj_mk_swap g hg₁ hg₂
  have hg'K : conjSubgroup (QuotientGroup.mk' (pCore 2 ↥M) g)⁻¹
      (imgQ M (A ⊔ B) ⊔ imgQ M (r0Of M V (A ⊔ B))) =
      imgQ M (A ⊔ B) ⊔ imgQ M (r0Of M V (A ⊔ B)) := by
    have h := conjSubgroup_conjSubgroup (QuotientGroup.mk' (pCore 2 ↥M) g)⁻¹
      (QuotientGroup.mk' (pCore 2 ↥M) g)
      (imgQ M (A ⊔ B) ⊔ imgQ M (r0Of M V (A ⊔ B)))
    rw [show (QuotientGroup.mk' (pCore 2 ↥M) g)⁻¹ * QuotientGroup.mk' (pCore 2 ↥M) g = 1 by
      group, conjSubgroup_one, hgK] at h
    exact h
  have hz'K : MulAut.conj (QuotientGroup.mk' (pCore 2 ↥M) g)⁻¹ z ∈
      Subgroup.centralizer
        ((imgQ M (A ⊔ B) ⊔ imgQ M (r0Of M V (A ⊔ B)) : Subgroup (MBar M)) : Set (MBar M)) := by
    have hconj := centralizer_conjSubgroup_eq (QuotientGroup.mk' (pCore 2 ↥M) g)⁻¹
      (imgQ M (A ⊔ B) ⊔ imgQ M (r0Of M V (A ⊔ B)))
    have hmem : MulAut.conj (QuotientGroup.mk' (pCore 2 ↥M) g)⁻¹ z ∈
        conjSubgroup (QuotientGroup.mk' (pCore 2 ↥M) g)⁻¹
          (Subgroup.centralizer
            ((imgQ M (A ⊔ B) ⊔ imgQ M (r0Of M V (A ⊔ B)) : Subgroup (MBar M)) :
              Set (MBar M))) :=
      Subgroup.mem_map_of_mem (MulAut.conj (QuotientGroup.mk' (pCore 2 ↥M) g)⁻¹).toMonoidHom hzK
    rw [← hconj, hg'K] at hmem
    exact hmem
  exact Subgroup.mem_inf.mpr ⟨hz'X0, hz'K⟩

private theorem lift_commutator_mem_p0 (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    {z : MBar M} {c : ↥M}
    (hzK : z ∈ Subgroup.centralizer
      ((imgQ M (A ⊔ B) ⊔ imgQ M (r0Of M V (A ⊔ B)) : Subgroup (MBar M)) : Set (MBar M)))
    (hc : QuotientGroup.mk' (pCore 2 ↥M) c = z) (hcC : (c : G) ∈ cenOf (A ⊔ B)) :
    ∀ r ∈ r0Of M V (A ⊔ B), ⁅(c : G), r⁆ ∈ p0Of M V (A ⊔ B) := by
  intro r hr
  have hrM : r ∈ M := ((L2Datum.r0_le_inf_cenOf hS.toSec6Hyp hD).trans inf_le_left) hr
  have hrC : r ∈ cenOf (A ⊔ B) :=
    (Subgroup.mem_inf.mp (L2Datum.r0_le_inf_cenOf hS.toSec6Hyp hD hr)).2
  have h1 : QuotientGroup.mk' (pCore 2 ↥M) (⁅c, ⟨r, hrM⟩⁆ : ↥M) = 1 := by
    rw [map_commutatorElement, hc]
    exact (Subgroup.mem_centralizer_iff_commutator_eq_one'.mp hzK) _
      (Subgroup.mem_sup_right (mk_mem_imgQ hr))
  have h2 : ⁅(c : G), r⁆ ∈ Pc M V := by
    have := (Sec6Hyp.mk_eq_one_iff hS.toSec6Hyp _).mp h1
    simpa [commutatorElement_def] using this
  have h3 : ⁅(c : G), r⁆ ∈ cenOf (A ⊔ B) := by
    have hmem := (cenOf (A ⊔ B)).mul_mem
      ((cenOf (A ⊔ B)).mul_mem ((cenOf (A ⊔ B)).mul_mem hcC hrC)
        ((cenOf (A ⊔ B)).inv_mem hcC)) ((cenOf (A ⊔ B)).inv_mem hrC)
    simpa [commutatorElement_def] using hmem
  exact Subgroup.mem_inf.mpr ⟨h2, h3⟩

private theorem lift_pow_mem_p0 (hS : Sec7Hyp M V n f)
    {C : Subgroup (MBar M)} {z : ↥C} {c : ↥M}
    (hc : QuotientGroup.mk' (pCore 2 ↥M) c = (z : MBar M))
    (hcard : Nat.card ↥C = 2 ^ f + 1) (hcC : (c : G) ∈ cenOf (A ⊔ B)) :
    (c : G) ^ (2 ^ f + 1) ∈ p0Of M V (A ⊔ B) := by
  have hzpow : (z : MBar M) ^ (2 ^ f + 1) = 1 := by
    have h := pow_card_eq_one' (G := ↥C) (x := z)
    rw [hcard] at h
    simpa using congrArg Subtype.val h
  have h1 : QuotientGroup.mk' (pCore 2 ↥M) (c ^ (2 ^ f + 1) : ↥M) = 1 := by
    rw [map_pow, hc, hzpow]
  have h2 : ((c : ↥M) : G) ^ (2 ^ f + 1) ∈ Pc M V := by
    have := (Sec6Hyp.mk_eq_one_iff hS.toSec6Hyp _).mp h1
    simpa using this
  have h3 : ((c : ↥M) : G) ^ (2 ^ f + 1) ∈ cenOf (A ⊔ B) :=
    (cenOf (A ⊔ B)).pow_mem hcC _
  exact Subgroup.mem_inf.mpr ⟨h2, h3⟩

private theorem twist_lift_data (hS : Sec7Hyp M V n f) (h72 : Sec7.Stmt72 M V n f)
    (hLP : UnitaryLinePair) (hD : L2Datum M V A B h) (h4 : n = 4) :
    ∃ (g c c' : ↥M),
      imgQ M (conjSubgroup (g : G) (A ⊔ B)) = imgQ M (r0Of M V (A ⊔ B)) ∧
      (c : G) ∈ M ⊓ cenOf (A ⊔ B) ∧ (c' : G) ∈ M ⊓ cenOf (A ⊔ B) ∧
      (∀ r ∈ r0Of M V (A ⊔ B), ⁅(c : G), r⁆ ∈ p0Of M V (A ⊔ B)) ∧
      (∀ r ∈ r0Of M V (A ⊔ B), ⁅(c' : G), r⁆ ∈ p0Of M V (A ⊔ B)) ∧
      (c : G) ^ (2 ^ f + 1) ∈ p0Of M V (A ⊔ B) ∧
      (c' : G) ^ (2 ^ f + 1) ∈ p0Of M V (A ⊔ B) ∧
      QuotientGroup.mk' (pCore 2 ↥M) c' =
        (QuotientGroup.mk' (pCore 2 ↥M) g)⁻¹ * QuotientGroup.mk' (pCore 2 ↥M) c *
          QuotientGroup.mk' (pCore 2 ↥M) g ∧
      QuotientGroup.mk' (pCore 2 ↥M) c ≠ 1 := by
  subst h4
  obtain ⟨g, hg₁, hg₂, hcard⟩ := L2Datum.exists_swap hS hLP hD rfl
  have h2f : 2 ≤ f := by
    have h4 : 4 ≤ 2 ^ f := by
      rw [← hS.card_V]
      exact hS.sec5.toRootHyp.four_le_card
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using h4)
  let C : Subgroup (MBar M) := imgQ M (m0Of M V) ⊓ Subgroup.centralizer
    ((imgQ M (A ⊔ B) ⊔ imgQ M (r0Of M V (A ⊔ B)) : Subgroup (MBar M)) : Set (MBar M))
  have hcardC : Nat.card ↥C = 2 ^ f + 1 := hcard
  have hlt : 1 < Nat.card ↥C := by
    rw [hcardC]
    have h4f : 4 ≤ 2 ^ f := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h2f
    omega
  haveI : Nontrivial ↥C := Finite.one_lt_card_iff_nontrivial.mp hlt
  obtain ⟨z, hz1⟩ := exists_ne (1 : ↥C)
  have hzX0 : (z : MBar M) ∈ imgQ M (m0Of M V) := (Subgroup.mem_inf.mp z.2).1
  have hzK : (z : MBar M) ∈ Subgroup.centralizer
      ((imgQ M (A ⊔ B) ⊔ imgQ M (r0Of M V (A ⊔ B)) : Subgroup (MBar M)) : Set (MBar M)) :=
    (Subgroup.mem_inf.mp z.2).2
  have hz'C : MulAut.conj (QuotientGroup.mk' (pCore 2 ↥M) g)⁻¹ (z : MBar M) ∈ C :=
    twist_conj_mem hS hzX0 hzK hg₁ hg₂
  have hz'X0 : MulAut.conj (QuotientGroup.mk' (pCore 2 ↥M) g)⁻¹ (z : MBar M) ∈
      imgQ M (m0Of M V) := (Subgroup.mem_inf.mp hz'C).1
  obtain ⟨m, -, hm⟩ := mem_imgQ_iff.mp hzX0
  have hzA : (z : MBar M) ∈ Subgroup.centralizer (imgQ M (A ⊔ B) : Set (MBar M)) :=
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left)) hzK
  obtain ⟨c, hc_m, hcC⟩ := L2Datum.exists_lift_centralizer hS h72 hD m (by rw [hm]; exact hzA)
  have hc : QuotientGroup.mk' (pCore 2 ↥M) c = (z : MBar M) := hc_m.trans hm
  obtain ⟨m', -, hm'⟩ := mem_imgQ_iff.mp hz'X0
  have hz'A : MulAut.conj (QuotientGroup.mk' (pCore 2 ↥M) g)⁻¹ (z : MBar M) ∈
      Subgroup.centralizer (imgQ M (A ⊔ B) : Set (MBar M)) :=
    (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
      (Subgroup.mem_inf.mp hz'C).2
  obtain ⟨c', hc'_m, hc'C⟩ :=
    L2Datum.exists_lift_centralizer hS h72 hD m' (by rw [hm']; exact hz'A)
  have hc' : QuotientGroup.mk' (pCore 2 ↥M) c' =
      MulAut.conj (QuotientGroup.mk' (pCore 2 ↥M) g)⁻¹ (z : MBar M) := hc'_m.trans hm'
  have hrel : QuotientGroup.mk' (pCore 2 ↥M) c' =
      (QuotientGroup.mk' (pCore 2 ↥M) g)⁻¹ * QuotientGroup.mk' (pCore 2 ↥M) c *
        QuotientGroup.mk' (pCore 2 ↥M) g := by
    rw [hc', hc, MulAut.conj_apply]
    group
  have hcne : QuotientGroup.mk' (pCore 2 ↥M) c ≠ 1 := by
    rw [hc]
    exact fun h => hz1 (Subtype.ext h)
  have hca := lift_commutator_mem_p0 hS hD hzK hc hcC
  have hca' := lift_commutator_mem_p0 hS hD (Subgroup.mem_inf.mp hz'C).2 hc' hc'C
  have hcb := lift_pow_mem_p0 hS (C := C) (z := z) hc hcardC hcC
  have hcb' := lift_pow_mem_p0 hS (C := C) (z := ⟨_, hz'C⟩) hc' hcardC hc'C
  exact ⟨g, c, c', hg₁, ⟨c.2, hcC⟩, ⟨c'.2, hc'C⟩, hca, hca', hcb, hcb', hrel, hcne⟩

private theorem twist_contradiction (hS : Sec7Hyp M V n f) (h72 : Sec7.Stmt72 M V n f)
    (hD : L2Datum M V A B h) {g c c' : ↥M}
    (hg₁ : imgQ M (conjSubgroup (g : G) (A ⊔ B)) = imgQ M (r0Of M V (A ⊔ B)))
    (hcM : (c : G) ∈ M) (hc'M : (c' : G) ∈ M)
    (hrel : QuotientGroup.mk' (pCore 2 ↥M) c' =
      (QuotientGroup.mk' (pCore 2 ↥M) g)⁻¹ * QuotientGroup.mk' (pCore 2 ↥M) c *
        QuotientGroup.mk' (pCore 2 ↥M) g)
    (hcne : QuotientGroup.mk' (pCore 2 ↥M) c ≠ 1)
    (hcV : ∀ x ∈ p0Of M V (A ⊔ B), ⁅(c : G), x⁆ ∈ V)
    (hc'V : ∀ x ∈ p0Of M V (A ⊔ B), ⁅(c' : G), x⁆ ∈ V) : False := by
  have hP0M : p0Of M V (A ⊔ B) ≤ M :=
    inf_le_left.trans hS.sec5.toRootHyp.toHyp.Pc_le_M
  have hPg : conjSubgroup (g : G) (p0Of M V (A ⊔ B)) ≤ Pc M V := by
    have h1 : conjSubgroup (g : G) (p0Of M V (A ⊔ B)) ≤ conjSubgroup (g : G) (Pc M V) :=
      conjSubgroup_mono inf_le_left
    rwa [show conjSubgroup (g : G) (Pc M V) = Pc M V from
      conjSubgroup_eq_self_iff.mpr (hS.sec5.toRootHyp.toHyp.le_normalizer_Pc g.2)] at h1
  let d : G := (g : G) * (c' : G) * (g : G)⁻¹
  have hdM : d ∈ M := M.mul_mem (M.mul_mem g.2 hc'M) (M.inv_mem g.2)
  have hd_eq : QuotientGroup.mk' (pCore 2 ↥M) ⟨d, hdM⟩ = QuotientGroup.mk' (pCore 2 ↥M) c := by
    have h1 : QuotientGroup.mk' (pCore 2 ↥M) ⟨d, hdM⟩ =
        (QuotientGroup.mk' (pCore 2 ↥M) g) * QuotientGroup.mk' (pCore 2 ↥M) c' *
          (QuotientGroup.mk' (pCore 2 ↥M) g)⁻¹ := by
      rw [show (⟨d, hdM⟩ : ↥M) = g * c' * g⁻¹ from Subtype.ext rfl, map_mul, map_mul, map_inv]
    rw [h1, hrel]
    group
  have hpP : (c : G) * d⁻¹ ∈ Pc M V := by
    have h1 : QuotientGroup.mk' (pCore 2 ↥M) (c * (⟨d, hdM⟩ : ↥M)⁻¹) = 1 := by
      rw [map_mul, map_inv, hd_eq, mul_inv_cancel]
    have := (Sec6Hyp.mk_eq_one_iff hS.toSec6Hyp _).mp h1
    simpa using this
  have hc_eq : (c : G) = ((c : G) * d⁻¹) * d := by group
  have hcPV : ∀ y ∈ conjSubgroup (g : G) (p0Of M V (A ⊔ B)), ⁅(c : G), y⁆ ∈ V := by
    intro y hy
    have hyP : y ∈ Pc M V := hPg hy
    have h1 : ((c : G) * d⁻¹) ∈ Subgroup.normalizer (V : Set G) :=
      hS.sec5.toRootHyp.toHyp.le_normalizer
        (hS.sec5.toRootHyp.toHyp.Pc_le_M hpP)
    have hdPV : ⁅d, y⁆ ∈ V := by
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      change ⁅d, (g : G) * x * (g : G)⁻¹⁆ ∈ V
      rw [show d = (g : G) * (c' : G) * (g : G)⁻¹ from rfl,
        ← conjugate_commutatorElement (g₁ := (c' : G)) (g₂ := x) (g₃ := (g : G))]
      exact (Subgroup.mem_normalizer_iff.mp (hS.sec5.toRootHyp.toHyp.le_normalizer g.2) _).mp
        (hc'V x hx)
    have h3 : ((c : G) * d⁻¹) * ⁅d, y⁆ * ((c : G) * d⁻¹)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp h1 _).mp hdPV
    have h4 : ⁅(c : G) * d⁻¹, y⁆ ∈ V := by
      have h := Subgroup.commutator_mem_commutator hpP hyP
      rwa [hS.sec5.commutator_Pc_eq_V hS.ne] at h
    have hsplit : ⁅(c : G), y⁆ = ((c : G) * d⁻¹) * ⁅d, y⁆ * ((c : G) * d⁻¹)⁻¹ *
        ⁅(c : G) * d⁻¹, y⁆ := by
      conv_lhs => rw [hc_eq]
      rw [commutatorElement_mul_left_eq_conj_mul]
    rw [hsplit]
    exact V.mul_mem h3 h4
  have hPgM : conjSubgroup (g : G) (p0Of M V (A ⊔ B)) ≤ M :=
    hPg.trans hS.sec5.toRootHyp.toHyp.Pc_le_M
  have hmem : ∀ x ∈ p0Of M V (A ⊔ B) ⊔ conjSubgroup (g : G) (p0Of M V (A ⊔ B)),
      ⁅(c : G), x⁆ ∈ V :=
    Sec6Hyp.commutator_mem_of_mem_sup hS.toSec6Hyp hP0M hPgM hcV hcPV
  have hcP : (c : G) ∈ Pc M V := by
    refine Sec6Hyp.mem_Pc_of_commutator_mem hS.toSec6Hyp hcM ?_
    intro p hp
    rw [L2Datum.Pc_eq_p0_sup_conj hS h72 hD g hg₁] at hp
    exact hmem p hp
  exact hcne ((Sec6Hyp.mk_eq_one_iff hS.toSec6Hyp c).mpr hcP)

theorem L2Datum.exists_twist (hS : Sec7Hyp M V n f) (h72 : Sec7.Stmt72 M V n f)
    (hLP : UnitaryLinePair) (hD : L2Datum M V A B h) (h4 : n = 4) :
    ∃ c ∈ M ⊓ cenOf (A ⊔ B), (∀ r ∈ r0Of M V (A ⊔ B), ⁅c, r⁆ ∈ p0Of M V (A ⊔ B)) ∧
      c ^ (2 ^ f + 1) ∈ p0Of M V (A ⊔ B) ∧
      ∃ x ∈ p0Of M V (A ⊔ B), ⁅c, x⁆ ∉ V := by
  obtain ⟨g, c, c', hg₁, hcM, hc'M, hca, hca', hcb, hcb', hrel, hcne⟩ :=
    twist_lift_data hS h72 hLP hD h4
  by_cases htriv : ∀ x ∈ p0Of M V (A ⊔ B), ⁅(c : G), x⁆ ∈ V
  · have hne' : ¬ ∀ x ∈ p0Of M V (A ⊔ B), ⁅(c' : G), x⁆ ∈ V := by
      intro htriv'
      exact twist_contradiction hS h72 hD hg₁ hcM.1 hc'M.1 hrel hcne htriv htriv'
    push Not at hne'
    exact ⟨(c' : G), hc'M, hca', hcb', hne'⟩
  · push Not at htriv
    exact ⟨(c : G), hcM, hca, hcb, htriv⟩

end CFSG.RankThree.GF2n.Tim81
