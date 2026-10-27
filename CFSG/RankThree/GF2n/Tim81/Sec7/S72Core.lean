module

public import CFSG.RankThree.GF2n.Tim81.Sec7.PBar
public import CFSG.RankThree.GF2n.Tim81.Cited.Sec7
import CFSG.RankThree.GF2n.Tim81.Sec7.S73Split
import CFSG.RankThree.GF2n.Tim81.Sec7.S73Images
import CFSG.RankThree.GF2n.Tim81.Sec7.Images
import CFSG.RankThree.GF2n.Tim81.Sec7.S77Basic
import CFSG.RankThree.GF2n.Tim81.Sec6.M0Setup
import CFSG.RankThree.GF2n.Tim81.Sec5.SigmaPlanes
import CFSG.CGT.Timmesfeld75.L2Real
import CFSG.GroupTheory.InvariantSubgroup
import TauCeti.GroupTheory.SemidirectProduct
public import CFSG.GroupTheory.CentralizerSup
public import CFSG.LocalAnalysis.EvenBN.Common.RadicalRank
public import CFSG.RankThree.GF2n.Tim81.Recog.L2Gen

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.LieType.Universal
open CFSG.Timmesfeld.Transvection
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {M V A B C D : Subgroup G} {h : G} {n f : ℕ}

private theorem L2Datum.exists_sylow_pair (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    {x a b : ↥(A ⊔ B)} (hx : x = a * b) (hodd : Odd (orderOf x)) (hx1 : x ≠ 1)
    (ha2 : a * a = 1) (hb2 : b * b = 1) :
    ∃ T₁ ∈ sigmaSet M V, ∃ T₂ ∈ sigmaSet M V, IsL2Gen T₁ T₂ ∧ T₁ ⊔ T₂ = A ⊔ B ∧
      (a : G) ∈ T₁ ∧ (b : G) ∈ T₂ := by
  have hAM : A ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hD.memA).1
  have hBM : B ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hD.memB).1
  have hXM : A ⊔ B ≤ M := _root_.sup_le hAM hBM
  haveI : IsMulCommutative ↥A := hD.l2.isElemAbelian.1
  obtain ⟨S₁, hS₁⟩ := IsPGroup.exists_le_sylow (isPGroup_two_zpowers_of_mul_self_eq_one ha2)
  obtain ⟨S₂, hS₂⟩ := IsPGroup.exists_le_sylow (isPGroup_two_zpowers_of_mul_self_eq_one hb2)
  have hne : S₁ ≠ S₂ := by
    intro hEq
    have haS : a ∈ (S₁ : Subgroup ↥(A ⊔ B)) := hS₁ (Subgroup.mem_zpowers a)
    have hbS : b ∈ (S₁ : Subgroup ↥(A ⊔ B)) := by
      rw [hEq]; exact hS₂ (Subgroup.mem_zpowers b)
    exact not_exists_isPGroup_two_mem_of_odd_orderOf hx hodd hx1
      ⟨(S₁ : Subgroup ↥(A ⊔ B)), S₁.isPGroup', haS, hbS⟩
  obtain ⟨g₁, hg₁⟩ := hD.l2.isL2Pair.exists_conj_eq_sylow S₁
  obtain ⟨g₂, hg₂⟩ := hD.l2.isL2Pair.exists_conj_eq_sylow S₂
  set T₁ : Subgroup G := (S₁ : Subgroup ↥(A ⊔ B)).map (A ⊔ B).subtype with hT₁
  set T₂ : Subgroup G := (S₂ : Subgroup ↥(A ⊔ B)).map (A ⊔ B).subtype with hT₂
  have hT₁eq : T₁ = conjSubgroup (g₁ : G) A := by
    have hmap := congrArg (Subgroup.map (A ⊔ B).subtype) hg₁
    rw [← CFSG.GroupTheory.map_conjSubgroup,
      Subgroup.map_subgroupOf_eq_of_le (le_sup_left : A ≤ A ⊔ B)] at hmap
    exact hT₁.trans hmap.symm
  have hT₂eq : T₂ = conjSubgroup (g₂ : G) A := by
    have hmap := congrArg (Subgroup.map (A ⊔ B).subtype) hg₂
    rw [← CFSG.GroupTheory.map_conjSubgroup,
      Subgroup.map_subgroupOf_eq_of_le (le_sup_left : A ≤ A ⊔ B)] at hmap
    exact hT₂.trans hmap.symm
  have hT₁sig : T₁ ∈ sigmaSet M V := by
    rw [hT₁eq]; exact hS.sec5.conj_mem_sigmaSet (hXM g₁.2) hD.memA
  have hT₂sig : T₂ ∈ sigmaSet M V := by
    rw [hT₂eq]; exact hS.sec5.conj_mem_sigmaSet (hXM g₂.2) hD.memA
  have hT₁ab : IsMulCommutative ↥T₁ := by
    rw [hT₁eq]
    exact Subgroup.map_isMulCommutative A (MulAut.conj (g₁ : G)).toMonoidHom
  have hT₂ab : IsMulCommutative ↥T₂ := by
    rw [hT₂eq]
    exact Subgroup.map_isMulCommutative A (MulAut.conj (g₂ : G)).toMonoidHom
  have hTsup : T₁ ⊔ T₂ = A ⊔ B := by
    have h := congrArg (Subgroup.map (A ⊔ B).subtype)
      (hD.l2.isL2Pair.sup_sylow_eq_top hne)
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype] at h
    simpa only [← hT₁, ← hT₂] using h
  have hL2 : IsL2Gen T₁ T₂ := by
    rcases hS.res.s513 M V hS.sec5 T₁ hT₁sig T₂ hT₂sig with ⟨hcomm, -⟩ | ⟨hL2, -⟩
    · exfalso
      have hXab : IsMulCommutative ↥(T₁ ⊔ T₂) := by
        rw [Subgroup.sup_eq_closure]
        refine Subgroup.isMulCommutative_closure ?_
        haveI := hT₁ab
        haveI := hT₂ab
        rintro p (hp | hp) q (hq | hq) -
        · exact Subgroup.mul_comm_of_mem_isMulCommutative T₁ hp hq
        · exact (Subgroup.mem_centralizer_iff.mp
            (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hp) q hq).symm
        · exact (Subgroup.mem_centralizer_iff.mp
            (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
              (by rwa [Subgroup.commutator_comm] at hcomm) hp) q hq).symm
        · exact Subgroup.mul_comm_of_mem_isMulCommutative T₂ hp hq
      have hAB : ⁅A, B⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro p hp
        rw [Subgroup.mem_centralizer_iff]
        intro q hq
        haveI := hXab
        exact Subgroup.mul_comm_of_mem_isMulCommutative (T₁ ⊔ T₂)
          (by rw [hTsup]; exact Subgroup.mem_sup_right hq)
          (by rw [hTsup]; exact Subgroup.mem_sup_left hp)
      exact hD.l2.commutator_ne_bot hAB
    · exact hL2
  refine ⟨T₁, hT₁sig, T₂, hT₂sig, hL2, hTsup, ?_, ?_⟩
  · rw [hT₁]
    exact Subgroup.mem_map_of_mem _ (hS₁ (Subgroup.mem_zpowers a))
  · rw [hT₂]
    exact Subgroup.mem_map_of_mem _ (hS₂ (Subgroup.mem_zpowers b))

theorem L2Datum.exists_involution_pair (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h) :
    ∃ T₁ ∈ sigmaSet M V, ∃ T₂ ∈ sigmaSet M V, IsL2Gen T₁ T₂ ∧ T₁ ⊔ T₂ = A ⊔ B ∧
      ∃ t ∈ T₁, ∃ s ∈ T₂, t ≠ 1 ∧ s ≠ 1 ∧ h = t * s := by
  have hodd : Odd (orderOf h) := by
    rw [hD.order, hS.card_V]
    exact ((Nat.even_pow (m := 2) (n := f)).mpr
      ⟨even_two, by have := hS.one_le; omega⟩).add_one
  have hx1 : (⟨h, hD.mem⟩ : ↥(A ⊔ B)) ≠ 1 := by
    intro h1
    have hh1 : h = 1 := congrArg Subtype.val h1
    have h2 : orderOf h = 1 := by rw [hh1, orderOf_one]
    rw [hD.order] at h2
    have h4 := hS.sec5.toRootHyp.four_le_card
    omega
  have hoddx : Odd (orderOf (⟨h, hD.mem⟩ : ↥(A ⊔ B))) := by
    rw [← Subgroup.orderOf_coe (⟨h, hD.mem⟩ : ↥(A ⊔ B))]
    exact hodd
  obtain ⟨a, b, ha2, hb2, ha1, hb1, -, hxab⟩ :=
    hD.l2.isL2Pair.exists_involutions_mul_eq_of_odd_ne_one hoddx hx1
  obtain ⟨T₁, hT₁, T₂, hT₂, hL2, hTsup, haT, hbT⟩ :=
    hD.exists_sylow_pair hS hxab hoddx hx1 ha2 hb2
  refine ⟨T₁, hT₁, T₂, hT₂, hL2, hTsup, (a : G), haT, (b : G), hbT, ?_, ?_, ?_⟩
  · exact fun h1 => ha1 (Subtype.ext (by simpa using h1))
  · exact fun h1 => hb1 (Subtype.ext (by simpa using h1))
  · exact congrArg Subtype.val hxab

theorem Sec6Hyp.mem_cenOf_of_commute_mul (hS : Sec6Hyp M V) {T₁ T₂ : Subgroup G}
    (h₁ : T₁ ∈ sigmaSet M V) (h₂ : T₂ ∈ sigmaSet M V) (hl : IsL2Gen T₁ T₂) {t s p : G}
    (ht : t ∈ T₁) (hs : s ∈ T₂) (ht1 : t ≠ 1) (hs1 : s ≠ 1) (hp : p ∈ Pc M V)
    (hc : t * s * p = p * (t * s)) : p ∈ cenOf (T₁ ⊔ T₂) := by
  have ht2 : t * t = 1 := Sec5Hyp.mul_self_eq_one_of_mem_sup_commutator hS.sec5 h₁ t
    (Subgroup.mem_sup_left ht)
  have hs2 : s * s = 1 := Sec5Hyp.mul_self_eq_one_of_mem_sup_commutator hS.sec5 h₂ s
    (Subgroup.mem_sup_left hs)
  have htinv : t⁻¹ = t := inv_eq_iff_mul_eq_one.mpr ht2
  have hsinv : s⁻¹ = s := inv_eq_iff_mul_eq_one.mpr hs2
  have hcomm : ⁅t, p⁆ = ⁅s, p⁆ := by
    have h1 : s * p * s = t * p * t := by
      calc s * p * s = (t * t) * (s * p) * s := by rw [ht2, one_mul]
        _ = t * (t * s * p) * s := by group
        _ = t * (p * (t * s)) * s := by rw [hc]
        _ = t * p * t * (s * s) := by group
        _ = t * p * t := by rw [hs2, mul_one]
    rw [commutatorElement_def, commutatorElement_def, htinv, hsinv, h1]
  have hp_eq : ⁅p, t⁆ = ⁅p, s⁆ := by
    rw [← commutatorElement_inv t p, ← commutatorElement_inv s p, hcomm]
  have hE₁ : ⁅p, t⁆ ∈ ⁅Pc M V, T₁⁆ := Subgroup.commutator_mem_commutator hp ht
  have hK₂ : ⁅p, s⁆ ∈ Pc M V ⊓ cenOf T₂ := by
    refine Subgroup.mem_inf.mpr ⟨Sec5Hyp.commutator_le_Pc hS.sec5 h₂
      (Subgroup.commutator_mem_commutator hp hs), ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
    exact (Sec5Hyp.mul_comm_of_mem_sup_commutator hS.sec5 h₂
      ⁅p, s⁆ (Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator hp hs))
      x (Subgroup.mem_sup_left hx)).symm
  have hpsV : ⁅p, s⁆ ∈ V := by
    rcases hS.res.s513 M V hS.sec5 T₁ h₁ T₂ h₂ with ⟨hbot, -⟩ | ⟨-, hV⟩
    · exact absurd hbot hl.commutator_ne_bot
    · rw [← hV]
      exact Subgroup.mem_inf.mpr ⟨hK₂, hp_eq ▸ hE₁⟩
  have hpT₁ : p ∈ cenOf T₁ := Sec5Hyp.mem_centralizer_of_commutator_mem hS.sec5 h₁ ht ht1 hp
    (hp_eq ▸ hpsV)
  have hpT₂ : p ∈ cenOf T₂ := Sec5Hyp.mem_centralizer_of_commutator_mem hS.sec5 h₂ hs hs1 hp
    hpsV
  have hsup : cenOf (T₁ ⊔ T₂) = cenOf T₁ ⊓ cenOf T₂ := centralizer_sup_eq T₁ T₂
  rw [hsup]
  exact Subgroup.mem_inf.mpr ⟨hpT₁, hpT₂⟩

theorem L2Datum.p0_zpowers_eq (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h) :
    p0Of M V (Subgroup.zpowers h) = p0Of M V (A ⊔ B) := by
  refine le_antisymm ?_ (inf_le_inf le_rfl
    (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr hD.mem)))
  intro p hp
  obtain ⟨T₁, hT₁, T₂, hT₂, hl, hsup, t, ht, s, hs, ht1, hs1, hts⟩ :=
    hD.exists_involution_pair hS
  have hpP : p ∈ Pc M V := hp.1
  have hcomm : t * s * p = p * (t * s) := by
    have h := Subgroup.mem_centralizer_iff.mp hp.2 h (Subgroup.mem_zpowers h)
    rwa [hts] at h
  have hcen := hS.toSec6Hyp.mem_cenOf_of_commute_mul hT₁ hT₂ hl ht hs ht1 hs1 hpP hcomm
  rw [hsup] at hcen
  exact Subgroup.mem_inf.mpr ⟨hpP, hcen⟩


private theorem Sec7Hyp.finrank_subSec (hS : Sec7Hyp M V n f)
    [Module (ZMod 2) (SecMod hS.pbarHyp)] {E : Subgroup G}
    (hVE : V ≤ E) (hEP : E ≤ Pc M V) {k : ℕ} (hE : Nat.card E = Nat.card V ^ (k + 1)) :
    Module.finrank (ZMod 2) (subSec hS.pbarHyp E) = f * k := by
  have h1 := natCard_subSec hS.pbarHyp hVE hEP
  rw [card_subSec_eq_two_pow, hE, hS.card_V, ← pow_mul, ← pow_add] at h1
  have h2 : Module.finrank (ZMod 2) (subSec hS.pbarHyp E) + f = f * (k + 1) :=
    Nat.pow_right_injective (a := 2) (by norm_num) h1
  rw [Nat.mul_succ] at h2
  omega

private theorem Sec7Hyp.finrank_subSec_commutator (hS : Sec7Hyp M V n f)
    [Module (ZMod 2) (SecMod hS.pbarHyp)] {C : Subgroup G} (hC : C ∈ sigmaSet M V) :
    Module.finrank (ZMod 2) (subSec hS.pbarHyp ⁅Pc M V, C⁆) = f * 2 := by
  refine hS.finrank_subSec (hS.sec5.V_le_commutator hC) (hS.sec5.commutator_le_Pc hC) ?_
  rw [hS.sec5.card_commutator_Pc hC]

private theorem Sec7Hyp.finrank_subSec_inf_cenOf (hS : Sec7Hyp M V n f)
    [Module (ZMod 2) (SecMod hS.pbarHyp)] {C : Subgroup G} (hC : C ∈ sigmaSet M V) :
    Module.finrank (ZMod 2) (subSec hS.pbarHyp (Pc M V ⊓ cenOf C)) = f * (2 * n - 2) := by
  have hcard : Nat.card ↥(Pc M V ⊓ cenOf C) = Nat.card V ^ ((2 * n - 2) + 1) := by
    have h := hS.sec5.card_Pc_inf_centralizer hC
    rw [hS.card_Pc, hS.card_V] at h
    have h2n : 2 * n + 1 = (2 * n - 2) + 1 + 2 := by have := hS.four_le; omega
    rw [h2n, pow_add] at h
    rw [hS.card_V]
    exact Nat.eq_of_mul_eq_mul_right (by positivity) h
  refine hS.finrank_subSec ?_ inf_le_left hcard
  exact le_inf hS.sec5.toRootHyp.toHyp.le_Pc
    ((Subgroup.le_centralizer_iff).mpr (hS.sec5.le_M_of_mem_sigmaSet hC).2)

private theorem Sec7Hyp.finrank_secMod (hS : Sec7Hyp M V n f)
    [Module (ZMod 2) (SecMod hS.pbarHyp)] :
    Module.finrank (ZMod 2) (SecMod hS.pbarHyp) = f * (2 * n) := by
  have h1 : Nat.card (subSec hS.pbarHyp (Pc M V)) =
      2 ^ Module.finrank (ZMod 2) (subSec hS.pbarHyp (Pc M V)) :=
    card_subSec_eq_two_pow hS.pbarHyp (Pc M V)
  rw [subSec_self] at h1
  have h2 : Nat.card ↥(⊤ : Submodule (ZMod 2) (SecMod hS.pbarHyp)) =
      Nat.card (SecMod hS.pbarHyp) :=
    Nat.card_congr (Submodule.topEquiv (R := ZMod 2) (M := SecMod hS.pbarHyp)).toEquiv
  rw [h2, hS.card_pbar, ← pow_mul] at h1
  have h3 : Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) (SecMod hS.pbarHyp)) =
      f * (2 * n) :=
    (Nat.pow_right_injective (a := 2) (by norm_num) h1).symm
  rwa [finrank_top] at h3


private theorem Sec7Hyp.commutator_le_inf_cenOf (hS : Sec7Hyp M V n f)
    {C : Subgroup G} (hC : C ∈ sigmaSet M V) :
    ⁅Pc M V, C⁆ ≤ Pc M V ⊓ cenOf C := by
  refine le_inf (hS.sec5.commutator_le_Pc hC) ?_
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  exact (Sec5Hyp.mul_comm_of_mem_sup_commutator hS.sec5 hC x (Subgroup.mem_sup_right hx)
    c (Subgroup.mem_sup_left hc)).symm

private theorem Sec7Hyp.subSec_commutator_inf_subSec_inf_cenOf (hS : Sec7Hyp M V n f)
    [Module (ZMod 2) (SecMod hS.pbarHyp)]
    {C D : Subgroup G} (hC : C ∈ sigmaSet M V) (hD : D ∈ sigmaSet M V)
    (hl : IsL2Gen C D) :
    subSec hS.pbarHyp ⁅Pc M V, C⁆ ⊓ subSec hS.pbarHyp (Pc M V ⊓ cenOf D) = ⊥ := by
  have hV_eq : Pc M V ⊓ cenOf D ⊓ ⁅Pc M V, C⁆ = V := by
    rcases hS.res.s513 M V hS.sec5 C hC D hD with ⟨hbot, -⟩ | ⟨-, hV⟩
    · exact absurd hbot hl.commutator_ne_bot
    · exact hV
  have h := subSec_inf (hs := hS.pbarHyp) (E := Pc M V ⊓ cenOf D)
    (F := ⁅Pc M V, C⁆) (hS.sec5.V_le_commutator hC)
  rw [hV_eq, subSec_eq_bot_of_le hS.pbarHyp le_rfl] at h
  rw [inf_comm]
  exact h.symm

private theorem Sec7Hyp.subSec_commutator_inf_subSec_commutator (hS : Sec7Hyp M V n f)
    [Module (ZMod 2) (SecMod hS.pbarHyp)]
    {C D : Subgroup G} (hC : C ∈ sigmaSet M V) (hD : D ∈ sigmaSet M V)
    (hl : IsL2Gen C D) :
    subSec hS.pbarHyp ⁅Pc M V, C⁆ ⊓ subSec hS.pbarHyp ⁅Pc M V, D⁆ = ⊥ := by
  have hV_eq : Pc M V ⊓ cenOf D ⊓ ⁅Pc M V, C⁆ = V := by
    rcases hS.res.s513 M V hS.sec5 C hC D hD with ⟨hbot, -⟩ | ⟨-, hV⟩
    · exact absurd hbot hl.commutator_ne_bot
    · exact hV
  have hle : ⁅Pc M V, C⁆ ⊓ ⁅Pc M V, D⁆ = V := by
    refine le_antisymm ?_ (le_inf (hS.sec5.V_le_commutator hC) (hS.sec5.V_le_commutator hD))
    calc ⁅Pc M V, C⁆ ⊓ ⁅Pc M V, D⁆ ≤ ⁅Pc M V, C⁆ ⊓ (Pc M V ⊓ cenOf D) :=
          le_inf inf_le_left (le_trans inf_le_right (hS.commutator_le_inf_cenOf hD))
      _ = Pc M V ⊓ cenOf D ⊓ ⁅Pc M V, C⁆ := by rw [inf_comm]
      _ = V := hV_eq
  have h := subSec_inf (hs := hS.pbarHyp) (E := ⁅Pc M V, C⁆) (F := ⁅Pc M V, D⁆)
    (hS.sec5.V_le_commutator hD)
  rw [hle, subSec_eq_bot_of_le hS.pbarHyp le_rfl] at h
  exact h.symm

private theorem Sec7Hyp.subSec_inf_cenOf_eq (hS : Sec7Hyp M V n f)
    [Module (ZMod 2) (SecMod hS.pbarHyp)] {C D : Subgroup G} (hD : D ∈ sigmaSet M V) :
    subSec hS.pbarHyp (Pc M V ⊓ cenOf (C ⊔ D)) =
      subSec hS.pbarHyp (Pc M V ⊓ cenOf C) ⊓
        subSec hS.pbarHyp (Pc M V ⊓ cenOf D) := by
  have hV_le : V ≤ Pc M V ⊓ cenOf D :=
    le_inf hS.sec5.toRootHyp.toHyp.le_Pc
      ((Subgroup.le_centralizer_iff).mpr (hS.sec5.le_M_of_mem_sigmaSet hD).2)
  have hKsub : Pc M V ⊓ cenOf (C ⊔ D) = (Pc M V ⊓ cenOf C) ⊓ (Pc M V ⊓ cenOf D) := by
    rw [show cenOf (C ⊔ D) = cenOf C ⊓ cenOf D from centralizer_sup_eq C D]
    ext x
    simp only [Subgroup.mem_inf]
    tauto
  rw [hKsub]
  exact subSec_inf (hs := hS.pbarHyp) (E := Pc M V ⊓ cenOf C)
    (F := Pc M V ⊓ cenOf D) hV_le

private theorem Sec7Hyp.Pc_decomp_inf (hS : Sec7Hyp M V n f)
    [Module (ZMod 2) (SecMod hS.pbarHyp)]
    {C D : Subgroup G} (hC : C ∈ sigmaSet M V) (hD : D ∈ sigmaSet M V)
    (hl : IsL2Gen C D) :
    subSec hS.pbarHyp (Pc M V ⊓ cenOf (C ⊔ D)) ⊓
        (subSec hS.pbarHyp ⁅Pc M V, C⁆ ⊔ subSec hS.pbarHyp ⁅Pc M V, D⁆) = ⊥ := by
  classical
  set UC := subSec hS.pbarHyp ⁅Pc M V, C⁆ with hUC
  set UD := subSec hS.pbarHyp ⁅Pc M V, D⁆ with hUD
  set KC := subSec hS.pbarHyp (Pc M V ⊓ cenOf C) with hKC
  set KD := subSec hS.pbarHyp (Pc M V ⊓ cenOf D) with hKD
  set K := subSec hS.pbarHyp (Pc M V ⊓ cenOf (C ⊔ D)) with hK
  have hUC_le_KC : UC ≤ KC := by
    rw [hUC, hKC]
    exact subSec_mono hS.pbarHyp (hS.commutator_le_inf_cenOf hC)
  have hUD_le_KD : UD ≤ KD := by
    rw [hUD, hKD]
    exact subSec_mono hS.pbarHyp (hS.commutator_le_inf_cenOf hD)
  have hUC_inf_KD : UC ⊓ KD = ⊥ := by
    rw [hUC, hKD]
    exact hS.subSec_commutator_inf_subSec_inf_cenOf hC hD hl
  have hUD_inf_KC : UD ⊓ KC = ⊥ := by
    rw [hUD, hKC]
    exact hS.subSec_commutator_inf_subSec_inf_cenOf hD hC hl.symm
  have hK_eq : K = KC ⊓ KD := by
    rw [hK, hKC, hKD]
    exact hS.subSec_inf_cenOf_eq hD
  change K ⊓ (UC ⊔ UD) = ⊥
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨hxK, hxF⟩ := Submodule.mem_inf.mp hx
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hxF
  rw [hK_eq] at hxK
  have huKC : u ∈ KC := hUC_le_KC hu
  have hvKC : v ∈ KC := by
    have hv_eq : v = x - u := by rw [← huv]; abel
    rw [hv_eq]
    exact KC.sub_mem hxK.1 huKC
  have hv0 : v = 0 := by
    have : v ∈ (⊥ : Submodule (ZMod 2) (SecMod hS.pbarHyp)) := by
      rw [← hUD_inf_KC]
      exact Submodule.mem_inf.mpr ⟨hv, hvKC⟩
    simpa using this
  have hx_eq_u : x = u := by rw [← huv, hv0, add_zero]
  have huKD : u ∈ KD := by
    rw [hx_eq_u] at hxK
    exact hxK.2
  have : u ∈ (⊥ : Submodule (ZMod 2) (SecMod hS.pbarHyp)) := by
    rw [← hUC_inf_KD]
    exact Submodule.mem_inf.mpr ⟨hu, huKD⟩
  rw [hx_eq_u]
  simpa using this

private theorem Sec7Hyp.finrank_subSec_inf_cenOf_sup (hS : Sec7Hyp M V n f)
    [Module (ZMod 2) (SecMod hS.pbarHyp)]
    {C D : Subgroup G} (hC : C ∈ sigmaSet M V) (hD : D ∈ sigmaSet M V)
    (hl : IsL2Gen C D) :
    Module.finrank (ZMod 2) (subSec hS.pbarHyp (Pc M V ⊓ cenOf (C ⊔ D))) =
      f * (2 * n - 4) := by
  classical
  haveI : FiniteDimensional (ZMod 2) (SecMod hS.pbarHyp) := Module.Finite.of_finite
  set UC := subSec hS.pbarHyp ⁅Pc M V, C⁆ with hUC
  set KD := subSec hS.pbarHyp (Pc M V ⊓ cenOf D) with hKD
  set KC := subSec hS.pbarHyp (Pc M V ⊓ cenOf C) with hKC
  have hUC_dim : Module.finrank (ZMod 2) UC = f * 2 := by
    rw [hUC]; exact hS.finrank_subSec_commutator hC
  have hKD_dim : Module.finrank (ZMod 2) KD = f * (2 * n - 2) := by
    rw [hKD]; exact hS.finrank_subSec_inf_cenOf hD
  have hKC_dim : Module.finrank (ZMod 2) KC = f * (2 * n - 2) := by
    rw [hKC]; exact hS.finrank_subSec_inf_cenOf hC
  have hUC_inf_KD : UC ⊓ KD = ⊥ := by
    rw [hUC, hKD]; exact hS.subSec_commutator_inf_subSec_inf_cenOf hC hD hl
  have hUC_le_KC : UC ≤ KC := by
    rw [hUC, hKC]
    exact subSec_mono hS.pbarHyp (hS.commutator_le_inf_cenOf hC)
  have hUC_sup_KD : UC ⊔ KD = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    have h := Submodule.finrank_sup_add_finrank_inf_eq UC KD
    rw [hUC_inf_KD, hUC_dim, hKD_dim, finrank_bot (ZMod 2) (SecMod hS.pbarHyp),
      add_zero] at h
    rw [h, hS.finrank_secMod, ← Nat.mul_add]
    congr 1
    have := hS.four_le
    omega
  have hKC_sup_KD : KC ⊔ KD = ⊤ := by
    rw [eq_top_iff]
    calc ⊤ = UC ⊔ KD := hUC_sup_KD.symm
      _ ≤ KC ⊔ KD := sup_le_sup_right hUC_le_KC KD
  have h := Submodule.finrank_sup_add_finrank_inf_eq KC KD
  rw [hKC_sup_KD, hKC_dim, hKD_dim, finrank_top, hS.finrank_secMod] at h
  have h1 : f * (2 * n) = f * (2 * n - 2) + f * 2 := by
    rw [← Nat.mul_add]; congr 1; have := hS.four_le; omega
  have h2 : f * (2 * n - 2) = f * (2 * n - 4) + f * 2 := by
    rw [← Nat.mul_add]; congr 1; have := hS.four_le; omega
  rw [h1, h2] at h
  rw [hS.subSec_inf_cenOf_eq hD, ← hKC, ← hKD]
  omega

private theorem Sec7Hyp.finrank_subSec_commutator_sup (hS : Sec7Hyp M V n f)
    [Module (ZMod 2) (SecMod hS.pbarHyp)]
    {C D : Subgroup G} (hC : C ∈ sigmaSet M V) (hD : D ∈ sigmaSet M V)
    (hl : IsL2Gen C D) :
    Module.finrank (ZMod 2)
      ↥((subSec hS.pbarHyp ⁅Pc M V, C⁆) ⊔ (subSec hS.pbarHyp ⁅Pc M V, D⁆)) = f * 4 := by
  haveI : FiniteDimensional (ZMod 2) (SecMod hS.pbarHyp) := Module.Finite.of_finite
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (subSec hS.pbarHyp ⁅Pc M V, C⁆) (subSec hS.pbarHyp ⁅Pc M V, D⁆)
  rw [hS.subSec_commutator_inf_subSec_commutator hC hD hl,
    hS.finrank_subSec_commutator hC, hS.finrank_subSec_commutator hD,
    finrank_bot (ZMod 2) (SecMod hS.pbarHyp), add_zero] at h
  rw [h, ← Nat.mul_add]

private theorem Sec7Hyp.Pc_decomp_sup (hS : Sec7Hyp M V n f)
    [Module (ZMod 2) (SecMod hS.pbarHyp)]
    {C D : Subgroup G} (hC : C ∈ sigmaSet M V) (hD : D ∈ sigmaSet M V)
    (hl : IsL2Gen C D) :
    subSec hS.pbarHyp (Pc M V) =
        subSec hS.pbarHyp (Pc M V ⊓ cenOf (C ⊔ D)) ⊔
          (subSec hS.pbarHyp ⁅Pc M V, C⁆ ⊔ subSec hS.pbarHyp ⁅Pc M V, D⁆) := by
  haveI : FiniteDimensional (ZMod 2) (SecMod hS.pbarHyp) := Module.Finite.of_finite
  have hinf := hS.Pc_decomp_inf hC hD hl
  have hsup : subSec hS.pbarHyp (Pc M V ⊓ cenOf (C ⊔ D)) ⊔
      (subSec hS.pbarHyp ⁅Pc M V, C⁆ ⊔ subSec hS.pbarHyp ⁅Pc M V, D⁆) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    have h := Submodule.finrank_sup_add_finrank_inf_eq
      (subSec hS.pbarHyp (Pc M V ⊓ cenOf (C ⊔ D)))
      (subSec hS.pbarHyp ⁅Pc M V, C⁆ ⊔ subSec hS.pbarHyp ⁅Pc M V, D⁆)
    rw [hinf, hS.finrank_subSec_inf_cenOf_sup hC hD hl,
      hS.finrank_subSec_commutator_sup hC hD hl,
      finrank_bot (ZMod 2) (SecMod hS.pbarHyp), add_zero] at h
    rw [h, hS.finrank_secMod, ← Nat.mul_add]
    congr 1
    have := hS.four_le
    omega
  rw [subSec_self]
  exact hsup.symm


theorem Sec7Hyp.Pc_decomp (hS : Sec7Hyp M V n f) {C D : Subgroup G}
    (hC : C ∈ sigmaSet M V) (hD : D ∈ sigmaSet M V) (hl : IsL2Gen C D) :
    Pc M V = (Pc M V ⊓ cenOf (C ⊔ D)) ⊔ (⁅Pc M V, C⁆ ⊔ ⁅Pc M V, D⁆) ∧
    (Pc M V ⊓ cenOf (C ⊔ D)) ⊓ (⁅Pc M V, C⁆ ⊔ ⁅Pc M V, D⁆) = V ∧
    Nat.card ↥(Pc M V ⊓ cenOf (C ⊔ D)) = Nat.card V ^ (2 * n - 3) ∧
    Nat.card ↥(⁅Pc M V, C⁆ ⊔ ⁅Pc M V, D⁆) = Nat.card V ^ 5 := by
  letI := Sec6Hyp.pbarModule hS.toSec6Hyp
  have hmod := hS.Pc_decomp_sup hC hD hl
  have hinf := hS.Pc_decomp_inf hC hD hl
  have hV_le_Pc : V ≤ Pc M V := hS.sec5.toRootHyp.toHyp.le_Pc
  have hV_le_C : V ≤ cenOf C :=
    (Subgroup.le_centralizer_iff).mpr (hS.sec5.le_M_of_mem_sigmaSet hC).2
  have hV_le_D : V ≤ cenOf D :=
    (Subgroup.le_centralizer_iff).mpr (hS.sec5.le_M_of_mem_sigmaSet hD).2
  have hV_le_K : V ≤ Pc M V ⊓ cenOf (C ⊔ D) := by
    rw [show cenOf (C ⊔ D) = cenOf C ⊓ cenOf D from centralizer_sup_eq C D]
    exact le_inf hV_le_Pc (le_inf hV_le_C hV_le_D)
  have hV_le_F : V ≤ ⁅Pc M V, C⁆ ⊔ ⁅Pc M V, D⁆ :=
    le_trans (hS.sec5.V_le_commutator hC) le_sup_left
  have hV_le_KF : V ≤ (Pc M V ⊓ cenOf (C ⊔ D)) ⊔ (⁅Pc M V, C⁆ ⊔ ⁅Pc M V, D⁆) :=
    le_trans hV_le_K le_sup_left
  have hK_le : Pc M V ⊓ cenOf (C ⊔ D) ≤ Pc M V := inf_le_left
  have hF_le : ⁅Pc M V, C⁆ ⊔ ⁅Pc M V, D⁆ ≤ Pc M V :=
    sup_le (hS.sec5.commutator_le_Pc hC) (hS.sec5.commutator_le_Pc hD)
  have h1 : Pc M V = (Pc M V ⊓ cenOf (C ⊔ D)) ⊔ (⁅Pc M V, C⁆ ⊔ ⁅Pc M V, D⁆) := by
    have hsub : subSec hS.pbarHyp (Pc M V) = subSec hS.pbarHyp
        ((Pc M V ⊓ cenOf (C ⊔ D)) ⊔ (⁅Pc M V, C⁆ ⊔ ⁅Pc M V, D⁆)) := by
      rw [subSec_sup hS.pbarHyp hK_le hF_le,
        subSec_sup hS.pbarHyp (hS.sec5.commutator_le_Pc hC)
          (hS.sec5.commutator_le_Pc hD)]
      exact hmod
    exact (subSec_inj hS.pbarHyp le_rfl hV_le_Pc (sup_le hK_le hF_le) hV_le_KF).mp hsub
  have h2 : (Pc M V ⊓ cenOf (C ⊔ D)) ⊓ (⁅Pc M V, C⁆ ⊔ ⁅Pc M V, D⁆) = V := by
    have hsub : subSec hS.pbarHyp ((Pc M V ⊓ cenOf (C ⊔ D)) ⊓
        (⁅Pc M V, C⁆ ⊔ ⁅Pc M V, D⁆)) = subSec hS.pbarHyp V := by
      rw [subSec_inf hS.pbarHyp hV_le_F,
        subSec_sup hS.pbarHyp (hS.sec5.commutator_le_Pc hC)
          (hS.sec5.commutator_le_Pc hD),
        hinf, subSec_eq_bot_of_le hS.pbarHyp le_rfl]
    exact (subSec_inj hS.pbarHyp (le_trans inf_le_left hK_le)
      (le_inf hV_le_K hV_le_F) hV_le_Pc (le_refl V)).mp hsub
  have h3 : Nat.card ↥(Pc M V ⊓ cenOf (C ⊔ D)) = Nat.card V ^ (2 * n - 3) := by
    have h := natCard_subSec hS.pbarHyp hV_le_K hK_le
    rw [card_subSec_eq_two_pow, hS.finrank_subSec_inf_cenOf_sup hC hD hl] at h
    rw [hS.card_V, ← pow_add] at h
    have harith : f * (2 * n - 4) + f = f * (2 * n - 3) := by
      calc f * (2 * n - 4) + f = f * (2 * n - 4) + f * 1 := by rw [Nat.mul_one]
        _ = f * ((2 * n - 4) + 1) := by rw [Nat.mul_add]
        _ = f * (2 * n - 3) := by congr 1; have := hS.four_le; omega
    rw [harith, pow_mul, ← hS.card_V] at h
    exact h.symm
  have h4 : Nat.card ↥(⁅Pc M V, C⁆ ⊔ ⁅Pc M V, D⁆) = Nat.card V ^ 5 := by
    have h := natCard_subSec hS.pbarHyp hV_le_F hF_le
    rw [card_subSec_eq_two_pow,
      subSec_sup hS.pbarHyp (hS.sec5.commutator_le_Pc hC)
        (hS.sec5.commutator_le_Pc hD),
      hS.finrank_subSec_commutator_sup hC hD hl] at h
    rw [hS.card_V, ← pow_add] at h
    have harith : f * 4 + f = f * 5 := by
      calc f * 4 + f = f * 4 + f * 1 := by rw [Nat.mul_one]
        _ = f * (4 + 1) := by rw [Nat.mul_add]
        _ = f * 5 := by norm_num
    rw [harith, pow_mul, ← hS.card_V] at h
    exact h.symm
  exact ⟨h1, h2, h3, h4⟩

theorem L2Datum.card_p0 (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h) :
    Nat.card ↥(p0Of M V (A ⊔ B)) = Nat.card V ^ (2 * n - 3) :=
  (hS.Pc_decomp hD.memA hD.memB hD.l2).2.2.1

theorem L2Datum.imgQ_sigma_cenOf (hS : Sec6Hyp M V) (hD : L2Datum M V A B h) :
    imgQ M '' {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)} =
      {E | E ∈ imgQ M '' sigmaSet M V ∧
        E ≤ Subgroup.centralizer ((imgQ M A ⊔ imgQ M B : Subgroup (MBar M)) : Set (MBar M))} := by
  have hAM : A ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hD.memA).1
  have hBM : B ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hD.memB).1
  ext E
  constructor
  · rintro ⟨C, ⟨hC, hCX⟩, rfl⟩
    refine ⟨⟨C, hC, rfl⟩, ?_⟩
    rw [← imgQ_sup hAM hBM]
    exact imgQ_le_centralizer_of_le_cenOf hCX
  · rintro ⟨⟨C, hC, rfl⟩, hE⟩
    exact ⟨C, ⟨hC, hD.le_cenOf_of_imgQ_le hS hC hE⟩, rfl⟩

theorem L2Datum.sigma_cenOf_zpowers_eq (hS : Sec7Hyp M V n f) (hLP : UnitaryLinePair)
    (hD : L2Datum M V A B h) :
    {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (Subgroup.zpowers h)} =
      {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)} := by
  have hAM : A ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hD.memA).1
  have hBM : B ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hD.memB).1
  have hXM : A ⊔ B ≤ M := _root_.sup_le hAM hBM
  have hM : h ∈ M := hXM hD.mem
  ext C
  constructor
  · rintro ⟨hC, hCz⟩
    have hCM : C ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hC).1
    have hmem : QuotientGroup.mk' (pCore 2 ↥M) (⟨h, hM⟩ : ↥M) ∈
        Subgroup.normalizer (imgQ M C : Set (MBar M)) := by
      refine Subgroup.centralizer_le_normalizer _ ?_
      refine (hS.toSec6Hyp.mk_mem_centralizer_imgQ_iff hCM ⟨h, hM⟩).mpr ?_
      intro y hy
      have hcomm : h * y = y * h :=
        Subgroup.mem_centralizer_iff.mp (hCz hy) h (Subgroup.mem_zpowers h)
      rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
      exact (Pc M V).one_mem
    have hord : orderOf (QuotientGroup.mk' (pCore 2 ↥M) (⟨h, hM⟩ : ↥M)) = 2 ^ f + 1 := by
      rw [hD.orderOf_mk hS.toSec6Hyp hM, hS.card_V]
    have hmemA : QuotientGroup.mk' (pCore 2 ↥M) (⟨h, hM⟩ : ↥M) ∈
        imgQ M A ⊔ imgQ M B := by
      rw [← imgQ_sup hAM hBM]
      exact mk_mem_imgQ hD.mem
    have hcomm := (hLP (MBar M) (imgQ M (m0Of M V)) (imgQ M '' sigmaSet M V) f n
      hS.one_le hS.four_le hS.two_le hS.m0 (imgQ M A) ⟨A, hD.memA, rfl⟩
      (imgQ M B) ⟨B, hD.memB, rfl⟩
      (Sec6Hyp.isL2Gen_imgQ hS.toSec6Hyp hD.memA hD.memB hD.l2)).1
      _ hmemA hord (imgQ M C) ⟨C, hC, rfl⟩ hmem
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
    exact ⟨hC, hD.le_cenOf_of_imgQ_le hS.toSec6Hyp hC hcomm⟩
  · rintro ⟨hC, hCX⟩
    refine ⟨hC, hCX.trans (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr hD.mem))⟩

theorem L2Datum.isSUImage_r0 (hS : Sec7Hyp M V n f) (hLP : UnitaryLinePair)
    (hD : L2Datum M V A B h) (hf : 1 ≤ f) (h5 : 5 ≤ n) :
    IsSUImage (imgQ M (r0Of M V (A ⊔ B)))
      (imgQ M '' {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)}) f (n - 2) hf
      (Nat.le_sub_of_add_le (Nat.le_trans (Nat.le_succ 4) h5)) := by
  have h := (hLP (MBar M) (imgQ M (m0Of M V)) (imgQ M '' sigmaSet M V) f n
    hS.one_le hS.four_le hS.two_le hS.m0 (imgQ M A) ⟨A, hD.memA, rfl⟩
    (imgQ M B) ⟨B, hD.memB, rfl⟩
    (Sec6Hyp.isL2Gen_imgQ hS.toSec6Hyp hD.memA hD.memB hD.l2)).2.1 h5
  rw [hD.perpRoots_eq hS.toSec6Hyp] at h
  rw [hD.imgQ_sigma_cenOf hS.toSec6Hyp]
  exact h


theorem L2Datum.exists_pair_four (hS : Sec7Hyp M V n f) (hLP : UnitaryLinePair)
    (hD : L2Datum M V A B h) (h4 : n = 4) :
    ∃ C ∈ sigmaSet M V, ∃ D ∈ sigmaSet M V, C ⊔ D ≤ cenOf (A ⊔ B) ∧ IsL2Gen C D ∧
      imgQ M (r0Of M V (A ⊔ B)) = imgQ M C ⊔ imgQ M D := by
  have hAM : A ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hD.memA).1
  have hBM : B ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hD.memB).1
  set Xbar : Subgroup (MBar M) := imgQ M A ⊔ imgQ M B with hXbar
  set Δ : Set (Subgroup (MBar M)) := imgQ M '' sigmaSet M V with hΔ
  obtain ⟨Cb, hCb, Db, hDb, hL2b, hperp, -⟩ :=
    (hLP (MBar M) (imgQ M (m0Of M V)) Δ f n hS.one_le hS.four_le hS.two_le hS.m0
      (imgQ M A) ⟨A, hD.memA, rfl⟩ (imgQ M B) ⟨B, hD.memB, rfl⟩
      (Sec6Hyp.isL2Gen_imgQ hS.toSec6Hyp hD.memA hD.memB hD.l2)).2.2 h4
  have hperp_le : perpRoots Δ Xbar ≤ Subgroup.centralizer (Xbar : Set (MBar M)) :=
    iSup₂_le fun _ hE => hE.2
  have hCb_cen : Cb ≤ Subgroup.centralizer (Xbar : Set (MBar M)) :=
    (le_sup_left.trans (le_of_eq hperp.symm)).trans hperp_le
  have hDb_cen : Db ≤ Subgroup.centralizer (Xbar : Set (MBar M)) :=
    (le_sup_right.trans (le_of_eq hperp.symm)).trans hperp_le
  obtain ⟨C, hC, hCeq⟩ := hCb
  obtain ⟨D, hD', hDeq⟩ := hDb
  have hCX : C ≤ cenOf (A ⊔ B) := by
    refine hD.le_cenOf_of_imgQ_le hS.toSec6Hyp hC ?_
    rwa [hCeq, ← hXbar]
  have hDX : D ≤ cenOf (A ⊔ B) := by
    refine hD.le_cenOf_of_imgQ_le hS.toSec6Hyp hD' ?_
    rwa [hDeq, ← hXbar]
  have hL2 : IsL2Gen C D := by
    rcases hS.res.s513 M V hS.sec5 C hC D hD' with ⟨hCD, -⟩ | ⟨hL2, -⟩
    · exfalso
      have hcomm : ⁅Cb, Db⁆ = ⊥ := by
        rw [← hCeq, ← hDeq, Subgroup.commutator_eq_bot_iff_le_centralizer]
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hCD
        intro z hz
        obtain ⟨c, hc, rfl⟩ := mem_imgQ_iff.mp hz
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        obtain ⟨d, hd, rfl⟩ := mem_imgQ_iff.mp hw
        have hcd : (c : G) * (d : G) = (d : G) * (c : G) :=
          (Subgroup.mem_centralizer_iff.mp (hCD hc) (d : G) hd).symm
        have hcd' : c * d = d * c := Subtype.ext hcd
        have := congrArg (QuotientGroup.mk' (pCore 2 ↥M)) hcd'
        simpa only [map_mul] using this.symm
      exact hL2b.commutator_ne_bot hcomm
    · exact hL2
  refine ⟨C, hC, D, hD', _root_.sup_le hCX hDX, hL2, ?_⟩
  rw [← hD.perpRoots_eq hS.toSec6Hyp, hperp, hCeq, hDeq]

theorem L2Datum.exists_sigma_cenOf (hS : Sec7Hyp M V n f) (hLP : UnitaryLinePair)
    (hD : L2Datum M V A B h) : ∃ C ∈ sigmaSet M V, C ≤ cenOf (A ⊔ B) := by
  rcases Nat.lt_or_ge n 5 with h5 | h5
  · have h4 : n = 4 := by have := hS.four_le; omega
    obtain ⟨C, hC, D, hD', hCDcen, -, -⟩ := hD.exists_pair_four hS hLP h4
    exact ⟨C, hC, le_trans le_sup_left hCDcen⟩
  · obtain ⟨Φ, -, hrange, hΔ⟩ := hD.isSUImage_r0 hS hLP hS.one_le h5
    have hn2 : 2 ≤ n - 2 := by omega
    let U : Subgroup (MBar M) :=
      (CFSG.Timmesfeld.ARS.conjSub
        ((Unitary.rootDatum (card_galoisField_two_mul hS.one_le) (n - 2)).rootGroup
          (unitaryLongRoot (n - 2) hn2)) 1).map Φ
    have hU : U ∈ imgQ M '' {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)} :=
      (hΔ U).2 ⟨1, rfl⟩
    obtain ⟨C, hCS, -⟩ := hU
    exact ⟨C, hCS.1, hCS.2⟩

theorem L2Datum.commutator_Pc_le_r0 (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    {C : Subgroup G} (hC : C ∈ sigmaSet M V) (hCX : C ≤ cenOf (A ⊔ B)) :
    ⁅Pc M V, C⁆ ≤ r0Of M V (A ⊔ B) := by
  rw [hD.commutator_Pc_eq_p0 hS (hD.p0_zpowers_eq hS) hC hCX, Subgroup.commutator_le]
  intro p hp c hc
  have hpM : p ∈ M := hS.sec5.toRootHyp.toHyp.Pc_le_M hp.1
  have hpX : p ∈ cenOf (A ⊔ B) := hp.2
  have hpXnorm : p ∈ Subgroup.normalizer (cenOf (A ⊔ B) : Set G) :=
    Subgroup.le_normalizer hpX
  have hCX' : conjSubgroup p C ≤ cenOf (A ⊔ B) :=
    (conjSubgroup_mono hCX).trans
      (le_of_eq (mem_normalizer_iff_conjSubgroup_eq.mp hpXnorm))
  have hconjR : conjSubgroup p C ≤ r0Of M V (A ⊔ B) :=
    le_iSup₂ (f := fun D (_ : D ∈ {D : Subgroup G | D ∈ sigmaSet M V ∧ D ≤ cenOf (A ⊔ B)}) => D)
      (conjSubgroup p C) ⟨hS.sec5.conj_mem_sigmaSet hpM hC, hCX'⟩
  have hCR : C ≤ r0Of M V (A ⊔ B) :=
    le_iSup₂ (f := fun D (_ : D ∈ {D : Subgroup G | D ∈ sigmaSet M V ∧ D ≤ cenOf (A ⊔ B)}) => D)
      C ⟨hC, hCX⟩
  have hmem : (p * c * p⁻¹) * c⁻¹ ∈ r0Of M V (A ⊔ B) :=
    (r0Of M V (A ⊔ B)).mul_mem (hconjR (Subgroup.mem_map_of_mem _ hc))
      ((r0Of M V (A ⊔ B)).inv_mem (hCR hc))
  have heq : ⁅p, c⁆ = (p * c * p⁻¹) * c⁻¹ := by rw [commutatorElement_def]
  rwa [heq]

theorem L2Datum.V_le_r0 (hS : Sec7Hyp M V n f) (hLP : UnitaryLinePair)
    (hD : L2Datum M V A B h) : V ≤ r0Of M V (A ⊔ B) := by
  obtain ⟨C, hC, hCX⟩ := hD.exists_sigma_cenOf hS hLP
  exact (hS.sec5.V_le_commutator hC).trans (L2Datum.commutator_Pc_le_r0 hS hD hC hCX)

theorem L2Datum.p0_le_r0_four (hS : Sec7Hyp M V n f) (hLP : UnitaryLinePair)
    (hD : L2Datum M V A B h) (h4 : n = 4) : p0Of M V (A ⊔ B) ≤ r0Of M V (A ⊔ B) := by
  obtain ⟨C, hC, D, hD', hCDcen, hL2, -⟩ := hD.exists_pair_four hS hLP h4
  have hCX : C ≤ cenOf (A ⊔ B) := le_trans le_sup_left hCDcen
  have hDX : D ≤ cenOf (A ⊔ B) := le_trans le_sup_right hCDcen
  have hE_le : ⁅Pc M V, C⁆ ⊔ ⁅Pc M V, D⁆ ≤ p0Of M V (A ⊔ B) :=
    _root_.sup_le (L2Datum.commutator_Pc_le_p0 hS.toSec6Hyp hD hC hCX)
      (L2Datum.commutator_Pc_le_p0 hS.toSec6Hyp hD hD' hDX)
  have hcardE : Nat.card ↥(⁅Pc M V, C⁆ ⊔ ⁅Pc M V, D⁆) = Nat.card V ^ 5 :=
    (hS.Pc_decomp hC hD' hL2).2.2.2
  have hcardP0 : Nat.card ↥(p0Of M V (A ⊔ B)) = Nat.card V ^ 5 := by
    rw [L2Datum.card_p0 hS hD, h4]
  have hEq : ⁅Pc M V, C⁆ ⊔ ⁅Pc M V, D⁆ = p0Of M V (A ⊔ B) :=
    Subgroup.eq_of_le_of_card_ge hE_le (by rw [hcardP0, hcardE])
  rw [← hEq]
  exact _root_.sup_le (L2Datum.commutator_Pc_le_r0 hS hD hC hCX)
    (L2Datum.commutator_Pc_le_r0 hS hD hD' hDX)

theorem L2Datum.r0_eq_four (hS : Sec7Hyp M V n f) (hLP : UnitaryLinePair)
    (hD : L2Datum M V A B h) (h4 : n = 4) :
    ∃ C ∈ sigmaSet M V, ∃ D ∈ sigmaSet M V, C ⊔ D ≤ cenOf (A ⊔ B) ∧ IsL2Gen C D ∧
      r0Of M V (A ⊔ B) = C ⊔ D ⊔ p0Of M V (A ⊔ B) := by
  obtain ⟨C, hC, D, hD', hCDcen, hL2, himg⟩ := hD.exists_pair_four hS hLP h4
  have hCX : C ≤ cenOf (A ⊔ B) := le_trans le_sup_left hCDcen
  have hDX : D ≤ cenOf (A ⊔ B) := le_trans le_sup_right hCDcen
  refine ⟨C, hC, D, hD', hCDcen, hL2, le_antisymm ?_ ?_⟩
  · unfold r0Of
    refine iSup₂_le fun E hE => ?_
    have hEM : E ≤ M := (hS.sec5.le_M_of_mem_sigmaSet hE.1).1
    have hER : E ≤ r0Of M V (A ⊔ B) :=
      le_iSup₂ (f := fun D (_ : D ∈ {D : Subgroup G | D ∈ sigmaSet M V ∧
        D ≤ cenOf (A ⊔ B)}) => D) E hE
    have himgE : imgQ M E ≤ imgQ M C ⊔ imgQ M D := by
      rw [← himg]
      exact imgQ_mono hER
    have hEsup : E ≤ (C ⊔ D) ⊔ Pc M V := by
      refine hS.toSec6Hyp.le_sup_Pc_of_imgQ_le hEM ?_
      rwa [imgQ_sup (hS.sec5.le_M_of_mem_sigmaSet hC).1
        (hS.sec5.le_M_of_mem_sigmaSet hD').1]
    have hnorm : C ⊔ D ≤ Subgroup.normalizer (Pc M V : Set G) :=
      (_root_.sup_le (hS.sec5.le_M_of_mem_sigmaSet hC).1
        (hS.sec5.le_M_of_mem_sigmaSet hD').1).trans hS.sec5.toRootHyp.toHyp.le_normalizer_Pc
    intro e he
    have he' : e ∈ ((C ⊔ D) ⊔ Pc M V : Subgroup G) := hEsup he
    rw [sup_comm] at he'
    obtain ⟨p, hp, d, hd, hpd⟩ :=
      (TauCeti.Subgroup.mem_sup_of_right_le_normalizer_left (H := Pc M V) hnorm).mp he'
    have hdX : d ∈ cenOf (A ⊔ B) := hCDcen hd
    have heX : e ∈ cenOf (A ⊔ B) := hE.2 he
    have hpX : p ∈ cenOf (A ⊔ B) := by
      have hp_eq : p = e * d⁻¹ := by rw [hpd]; group
      rw [hp_eq]
      exact (cenOf (A ⊔ B)).mul_mem heX ((cenOf (A ⊔ B)).inv_mem hdX)
    have hthis : (p0Of M V (A ⊔ B) ⊔ (C ⊔ D) : Subgroup G) =
        (C ⊔ D) ⊔ p0Of M V (A ⊔ B) := sup_comm _ _
    rw [← hthis, hpd]
    exact (p0Of M V (A ⊔ B) ⊔ (C ⊔ D)).mul_mem
      (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hp, hpX⟩))
      (Subgroup.mem_sup_right hd)
  · refine _root_.sup_le ?_ (L2Datum.p0_le_r0_four hS hLP hD h4)
    exact _root_.sup_le
      (le_iSup₂ (f := fun E (_ : E ∈ {E : Subgroup G | E ∈ sigmaSet M V ∧
        E ≤ cenOf (A ⊔ B)}) => E) C ⟨hC, hCX⟩)
      (le_iSup₂ (f := fun E (_ : E ∈ {E : Subgroup G | E ∈ sigmaSet M V ∧
        E ≤ cenOf (A ⊔ B)}) => E) D ⟨hD', hDX⟩)


private theorem Sec5Hyp.card_inf_centralizer_commutator_le (hS : Sec5Hyp M V) {C : Subgroup G}
    (hC : C ∈ sigmaSet M V) {y : G} (hy : y ∈ Pc M V) (hyC : y ∉ cenOf C) :
    Nat.card ↥((⁅Pc M V, C⁆) ⊓ Subgroup.centralizer ({y} : Set G)) ≤ Nat.card V ^ 2 := by
  have hset : ∀ z ∈ (⁅Pc M V, C⁆) ⊓ Subgroup.centralizer ({y} : Set G),
      ∃ v ∈ V, ∃ t ∈ C, z = v * ⁅y, (t : G)⁆ := by
    rintro w ⟨hwA, hwC⟩
    have hwy : w * y = y * w := Subgroup.mem_centralizer_singleton_iff.mp hwC
    obtain ⟨v, hv, t, ht, hvt⟩ := Sec5Hyp.exists_eq_mul_commutator hS hC hy hyC hwA hwy
    exact ⟨v, hv, t, ht, hvt⟩
  have hcardK : Nat.card ↥((⁅Pc M V, C⁆) ⊓ Subgroup.centralizer ({y} : Set G)) ≤
      Nat.card {z : G // ∃ v ∈ V, ∃ t ∈ C, z = v * ⁅y, (t : G)⁆} := by
    refine Nat.card_le_card_of_injective
      (fun x : ↥((⁅Pc M V, C⁆) ⊓ Subgroup.centralizer ({y} : Set G)) =>
        (⟨(x : G), hset (x : G) x.2⟩ : {z : G // ∃ v ∈ V, ∃ t ∈ C, z = v * ⁅y, (t : G)⁆})) ?_
    intro x x' hxx
    exact Subtype.ext (congrArg (fun z : {z : G // ∃ v ∈ V, ∃ t ∈ C, z = v * ⁅y, (t : G)⁆} =>
      (z : G)) hxx)
  have hcardSet : Nat.card {z : G // ∃ v ∈ V, ∃ t ∈ C, z = v * ⁅y, (t : G)⁆} ≤
      Nat.card V * Nat.card C := by
    have h := Nat.card_le_card_of_surjective
      (fun p : ↥V × ↥C => (⟨p.1 * ⁅y, (p.2 : G)⁆,
        ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩⟩ : {z : G // ∃ v ∈ V, ∃ t ∈ C, z = v * ⁅y, (t : G)⁆})) ?_
    · rwa [Nat.card_prod] at h
    · rintro ⟨z, v, hv, t, ht, rfl⟩
      exact ⟨(⟨v, hv⟩, ⟨t, ht⟩), rfl⟩
  calc Nat.card ↥((⁅Pc M V, C⁆) ⊓ Subgroup.centralizer ({y} : Set G))
      ≤ Nat.card {z : G // ∃ v ∈ V, ∃ t ∈ C, z = v * ⁅y, (t : G)⁆} := hcardK
    _ ≤ Nat.card V * Nat.card C := hcardSet
    _ = Nat.card V ^ 2 := by
        obtain ⟨g, rfl, -⟩ := hC
        rw [card_conjSubgroup, pow_two]

private theorem Sec5Hyp.exists_commutator_eq (hS : Sec5Hyp M V) {C : Subgroup G}
    (hC : C ∈ sigmaSet M V) {y : G} (hy : y ∈ Pc M V) (hyC : y ∉ cenOf C) {v : G}
    (hv : v ∈ V) : ∃ w ∈ ⁅Pc M V, C⁆, ⁅w, y⁆ = v := by
  classical
  set A : Subgroup G := ⁅Pc M V, C⁆ with hA
  have hne : (sigmaSet M V).Nonempty := ⟨C, hC⟩
  have hZA : V ≤ Subgroup.centralizer (A : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwP : w ∈ Pc M V := hS.commutator_le_Pc hC (hA ▸ hw)
    have hPCV : Pc M V ≤ Subgroup.centralizer (V : Set G) := inf_le_right
    exact (Subgroup.mem_centralizer_iff.mp (hPCV hwP) z hz).symm
  have hxA : ∀ a ∈ A, ⁅y, a⁆ ∈ V := by
    intro a ha
    have haP : a ∈ Pc M V := hS.commutator_le_Pc hC (hA ▸ ha)
    have hmem : ⁅y, a⁆ ∈ ⁅Pc M V, Pc M V⁆ := Subgroup.commutator_mem_commutator hy haP
    rwa [hS.commutator_Pc_eq_V hne] at hmem
  let f : ↥A →* ↥V := CFSG.LocalAnalysis.EvenBN.Common.commutatorElementHom y hZA hxA
  have hker : f.ker = (A ⊓ Subgroup.centralizer ({y} : Set G)).subgroupOf A :=
    CFSG.LocalAnalysis.EvenBN.Common.ker_commutatorElementHom y hZA hxA
  have hcardker : Nat.card ↥f.ker ≤ Nat.card V ^ 2 := by
    rw [hker]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    rw [hA]
    exact hS.card_inf_centralizer_commutator_le hC hy hyC
  have hcardA : Nat.card ↥A = Nat.card V ^ 3 := hS.card_commutator_Pc hC
  have hcard : Nat.card ↥f.ker * Nat.card ↥f.range = Nat.card V ^ 3 := by
    rw [Subgroup.card_ker_mul_card_range f, hcardA]
  have hVpos : 0 < Nat.card V := by
    have := hS.toRootHyp.four_le_card
    omega
  have hq2pos : 0 < Nat.card V ^ 2 := pow_pos hVpos 2
  have hrange_ge : Nat.card V ≤ Nat.card ↥f.range := by
    have h1 : Nat.card V ^ 3 ≤ Nat.card V ^ 2 * Nat.card ↥f.range := by
      rw [← hcard]
      exact Nat.mul_le_mul_right _ hcardker
    have h2 : Nat.card V ^ 3 = Nat.card V ^ 2 * Nat.card V := by ring
    rw [h2] at h1
    exact Nat.le_of_mul_le_mul_left h1 hq2pos
  have hrange_le : Nat.card ↥f.range ≤ Nat.card V := by
    refine Nat.card_le_card_of_injective (fun x : ↥f.range => (x.1 : ↥V)) ?_
    intro x y hxy
    exact Subtype.ext (show (x : ↥V) = (y : ↥V) from hxy)
  have hrange : Nat.card ↥f.range = Nat.card V := le_antisymm hrange_le hrange_ge
  have htop : f.range = ⊤ := by
    refine Subgroup.eq_of_le_of_card_ge le_top ?_
    rw [hrange, Subgroup.card_top]
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp (htop ▸ Subgroup.mem_top
    (⟨v⁻¹, V.inv_mem hv⟩ : ↥V))
  refine ⟨(w : G), w.2, ?_⟩
  have h1 : ⁅y, (w : G)⁆ = v⁻¹ := by
    have := congrArg Subtype.val hw
    simpa [f, CFSG.LocalAnalysis.EvenBN.Common.commutatorElementHom_apply] using this
  rw [← inv_inv v, ← h1, commutatorElement_inv]

theorem L2Datum.commutator_p0_eq (hS : Sec7Hyp M V n f) (hLP : UnitaryLinePair)
    (hD : L2Datum M V A B h) : ⁅p0Of M V (A ⊔ B), p0Of M V (A ⊔ B)⁆ = V := by
  refine le_antisymm ?_ ?_
  · calc ⁅p0Of M V (A ⊔ B), p0Of M V (A ⊔ B)⁆ ≤ ⁅Pc M V, Pc M V⁆ :=
        Subgroup.commutator_mono inf_le_left inf_le_left
      _ = V := hS.sec5.commutator_Pc_eq_V hS.ne
  · obtain ⟨C, hC, hCX⟩ := hD.exists_sigma_cenOf hS hLP
    have hy_exists : ∃ y ∈ p0Of M V (A ⊔ B), y ∉ cenOf C := by
      by_contra h
      push Not at h
      have hbot : ⁅p0Of M V (A ⊔ B), C⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        exact h
      have hE : ⁅Pc M V, C⁆ = ⊥ := by
        rw [L2Datum.commutator_Pc_eq_p0 hS hD (hD.p0_zpowers_eq hS) hC hCX]
        exact hbot
      have hcard := hS.sec5.card_commutator_Pc hC
      rw [hE, Subgroup.card_bot] at hcard
      have h4 := hS.sec5.toRootHyp.four_le_card
      have h43 : 4 ^ 3 ≤ Nat.card V ^ 3 := Nat.pow_le_pow_left h4 3
      norm_num at h43
      omega
    obtain ⟨y, hyP0, hyC⟩ := hy_exists
    intro v hv
    obtain ⟨w, hw, hwy⟩ := hS.sec5.exists_commutator_eq hC hyP0.1 hyC hv
    have hwP0 : w ∈ p0Of M V (A ⊔ B) :=
      L2Datum.commutator_Pc_le_p0 hS.toSec6Hyp hD hC hCX hw
    rw [← hwy]
    exact Subgroup.commutator_mem_commutator hwP0 hyP0

theorem L2Datum.p0_inf_cenOf_p0 (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h) :
    p0Of M V (A ⊔ B) ⊓ cenOf (p0Of M V (A ⊔ B)) = V := by
  refine le_antisymm ?_ ?_
  · intro z hz
    obtain ⟨hzP0, hzCen⟩ := Subgroup.mem_inf.mp hz
    have hzPc : z ∈ Pc M V := hzP0.1
    have hzA : z ∈ cenOf A :=
      Subgroup.centralizer_le (le_sup_left : A ≤ A ⊔ B) hzP0.2
    have hzB : z ∈ cenOf B :=
      Subgroup.centralizer_le (le_sup_right : B ≤ A ⊔ B) hzP0.2
    have hzEA : z ∈ cenOf ⁅Pc M V, A⁆ := by
      have h := hS.sec5.Pc_inf_centralizer_eq_commutator hD.memA
      have hz : z ∈ Pc M V ⊓ cenOf A := Subgroup.mem_inf.mpr ⟨hzPc, hzA⟩
      rw [h] at hz
      exact hz.2
    have hzEB : z ∈ cenOf ⁅Pc M V, B⁆ := by
      have h := hS.sec5.Pc_inf_centralizer_eq_commutator hD.memB
      have hz : z ∈ Pc M V ⊓ cenOf B := Subgroup.mem_inf.mpr ⟨hzPc, hzB⟩
      rw [h] at hz
      exact hz.2
    have hzPcCen : z ∈ cenOf (Pc M V) := by
      have hdec := hS.Pc_decomp hD.memA hD.memB hD.l2
      have hsup : Pc M V = p0Of M V (A ⊔ B) ⊔ (⁅Pc M V, A⁆ ⊔ ⁅Pc M V, B⁆) :=
        hdec.1
      rw [hsup]
      rw [show cenOf (p0Of M V (A ⊔ B) ⊔ (⁅Pc M V, A⁆ ⊔ ⁅Pc M V, B⁆)) =
        cenOf (p0Of M V (A ⊔ B)) ⊓ cenOf (⁅Pc M V, A⁆ ⊔ ⁅Pc M V, B⁆) from
        centralizer_sup_eq _ _]
      refine Subgroup.mem_inf.mpr ⟨hzCen, ?_⟩
      rw [show cenOf (⁅Pc M V, A⁆ ⊔ ⁅Pc M V, B⁆) =
        cenOf ⁅Pc M V, A⁆ ⊓ cenOf ⁅Pc M V, B⁆ from centralizer_sup_eq _ _]
      exact Subgroup.mem_inf.mpr ⟨hzEA, hzEB⟩
    have hcenter := hS.sec5.toRootHyp.toHyp.center_Pc
    rw [← hcenter]
    exact Subgroup.mem_inf.mpr ⟨hzPc, hzPcCen⟩
  · intro v hv
    have hVPc : V ≤ Pc M V := hS.sec5.toRootHyp.toHyp.le_Pc
    have hPcV : Pc M V ≤ cenOf V := inf_le_right
    refine Subgroup.mem_inf.mpr ⟨L2Datum.V_le_p0 hS.toSec6Hyp hD hv, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact (Subgroup.mem_centralizer_iff.mp (hPcV hp.1) v hv).symm

end CFSG.RankThree.GF2n.Tim81
