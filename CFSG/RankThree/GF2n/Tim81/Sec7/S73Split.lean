module

public import CFSG.RankThree.GF2n.Tim81.Sec7.Stmts
import CFSG.RankThree.GF2n.Tim81.Sec7.S73Base
import CFSG.GroupTheory.CoprimeCovering
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.GroupTheory.ABGLocalTools.Constraint
public import CFSG.GroupTheory.CentralizerSup
public import CFSG.RankThree.GF2n.Tim81.Recog.L2Gen

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n
open CFSG.RankThree.GF2n.Tim81.Sec7 (rOf oOf yOf)
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G] {M V A B : Subgroup G} {h : G} {n f : ℕ}

namespace Sec7

theorem odd_card_oOf (M : Subgroup G) (h : G) : Odd (Nat.card (oOf M h)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [oOf, inSubgroup,
    Subgroup.card_map_of_injective (rOf M h).subtype_injective]
  exact Nat.coprime_two_left.mp
    (pPrimeCore_coprime_card (p := 2) (G := ↥(rOf M h)))

theorem rOf_le_normalizer_oOf (M : Subgroup G) (h : G) :
    rOf M h ≤ Subgroup.normalizer (oOf M h : Set G) :=
  CFSG.ABGLocalTools.le_normalizer_map_subtype (rOf M h) (pPrimeCore 2 ↥(rOf M h))

theorem rOf_le_normalizer_Op_p'p (M : Subgroup G) (h : G) :
    rOf M h ≤ Subgroup.normalizer (inSubgroup (Op_p'p 2) (rOf M h) : Set G) :=
  CFSG.ABGLocalTools.le_normalizer_map_subtype (rOf M h) (Op_p'p 2 ↥(rOf M h))

theorem oOf_le_Op_p'p (M : Subgroup G) (h : G) :
    oOf M h ≤ inSubgroup (Op_p'p 2) (rOf M h) := by
  simpa [oOf, inSubgroup] using
    (Subgroup.map_mono (f := (rOf M h).subtype)
      (CFSG.ABGLocalTools.pPrimeCore_le_Op_p'p (p := 2) (H := ↥(rOf M h))))

theorem exists_pow_mem_oOf {M : Subgroup G} {h : G} {u : G}
    (hu : u ∈ inSubgroup (Op_p'p 2) (rOf M h)) :
    ∃ k : ℕ, u ^ 2 ^ k ∈ oOf M h := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hu
  obtain ⟨k, hk⟩ :=
    CFSG.ABGLocalTools.exists_pow_mem_pPrimeCore_of_mem_Op_p'p hx
  refine ⟨k, ?_⟩
  have hmem := Subgroup.mem_map_of_mem (f := (rOf M h).subtype)
    (K := pPrimeCore 2 ↥(rOf M h)) hk
  simpa [oOf, inSubgroup, Subgroup.coe_pow] using hmem

theorem le_Op_p'p_rOf_of_normal {M : Subgroup G} {h : G} {N : Subgroup G} (hNR : N ≤ rOf M h)
    (hN : rOf M h ≤ Subgroup.normalizer (N : Set G)) (h2 : IsPGroup 2 N) :
    N ≤ inSubgroup (Op_p'p 2) (rOf M h) := by
  have hNsub : (N.subgroupOf (rOf M h)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNR).mpr hN
  have hpow : ∀ x ∈ N.subgroupOf (rOf M h),
      ∃ k : ℕ, x ^ 2 ^ k ∈ pPrimeCore 2 ↥(rOf M h) := by
    intro x hx
    obtain ⟨k, hk⟩ := h2.exists_pow_pow_eq_one ⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩
    refine ⟨k, ?_⟩
    have hx1 : x ^ 2 ^ k = 1 := by
      apply Subtype.ext
      have := congrArg (fun z : ↥N => (z : G)) hk
      simpa [Subgroup.coe_pow] using this
    rw [hx1]
    exact (pPrimeCore 2 ↥(rOf M h)).one_mem
  have hle : N.subgroupOf (rOf M h) ≤ Op_p'p 2 ↥(rOf M h) :=
    CFSG.ABGLocalTools.le_Op_p'p_of_normal hNsub hpow
  have hmap := Subgroup.map_mono (f := (rOf M h).subtype) hle
  simpa [inSubgroup, Subgroup.map_subgroupOf_eq_of_le hNR] using hmap

end Sec7

namespace L2Datum

theorem sup_le (hS : Sec6Hyp M V) (hD : L2Datum M V A B h) :
    A ⊔ B ≤ M ⊓ cenOf V := by
  refine _root_.sup_le ?_ ?_
  · exact le_inf (hS.sec5.le_M_of_mem_sigmaSet hD.memA).1
      (hS.sec5.le_M_of_mem_sigmaSet hD.memA).2
  · exact le_inf (hS.sec5.le_M_of_mem_sigmaSet hD.memB).1
      (hS.sec5.le_M_of_mem_sigmaSet hD.memB).2

theorem V_le_p0 (hS : Sec6Hyp M V) (hD : L2Datum M V A B h) :
    V ≤ p0Of M V (A ⊔ B) := by
  have hVc : V ≤ cenOf (A ⊔ B) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxAB : x ∈ cenOf V := (_root_.sup_le (hS.sec5.le_M_of_mem_sigmaSet hD.memA).2
      (hS.sec5.le_M_of_mem_sigmaSet hD.memB).2) hx
    exact (Subgroup.mem_centralizer_iff.mp hxAB v hv).symm
  exact le_inf hS.sec5.toRootHyp.toHyp.le_Pc hVc

theorem inf_cenOf_le_rOf (hD : L2Datum M V A B h) :
    M ⊓ cenOf (A ⊔ B) ≤ rOf M h :=
  le_inf inf_le_left (inf_le_right.trans
    (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr hD.mem)))

theorem p0_le_rOf (hS : Sec6Hyp M V) (hD : L2Datum M V A B h) :
    p0Of M V (A ⊔ B) ≤ rOf M h :=
  le_inf (inf_le_left.trans hS.sec5.toRootHyp.toHyp.Pc_le_M)
    (inf_le_right.trans (Subgroup.centralizer_le (Subgroup.zpowers_le.mpr hD.mem)))

theorem r0_le_inf_cenOf (hS : Sec6Hyp M V) (hD : L2Datum M V A B h) :
    r0Of M V (A ⊔ B) ≤ M ⊓ cenOf (A ⊔ B) := by
  unfold r0Of
  exact iSup₂_le fun C hC => le_inf (hS.sec5.le_M_of_mem_sigmaSet hC.1).1 hC.2

private theorem r0_le_rOf (hS : Sec6Hyp M V) (hD : L2Datum M V A B h) :
    r0Of M V (A ⊔ B) ≤ rOf M h :=
  (r0_le_inf_cenOf hS hD).trans (inf_cenOf_le_rOf hD)

theorem rOf_le_normalizer_p0 (hS : Sec6Hyp M V) (hD : L2Datum M V A B h)
    (hS1 : p0Of M V (Subgroup.zpowers h) = p0Of M V (A ⊔ B)) :
    rOf M h ≤ Subgroup.normalizer (p0Of M V (A ⊔ B) : Set G) := by
  intro y hy
  obtain ⟨hyM, hyC⟩ := Subgroup.mem_inf.mp hy
  have h1 : y ∈ Subgroup.normalizer (Pc M V : Set G) :=
    hS.sec5.toRootHyp.toHyp.le_normalizer_Pc hyM
  have h2 : y ∈ Subgroup.normalizer (cenOf (Subgroup.zpowers h) : Set G) :=
    mem_normalizer_centralizer
      (Subgroup.centralizer_le_normalizer _ hyC)
  rw [← hS1, p0Of]
  exact mem_normalizer_inf h1 h2

theorem rOf_le_normalizer_r0 (hS : Sec6Hyp M V) (hD : L2Datum M V A B h)
    (hS6 : {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (Subgroup.zpowers h)} =
      {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)}) :
    rOf M h ≤ Subgroup.normalizer (r0Of M V (A ⊔ B) : Set G) := by
  intro y hy
  obtain ⟨hyM, hyC⟩ := Subgroup.mem_inf.mp hy
  have hyC' : y⁻¹ ∈ cenOf (Subgroup.zpowers h) := (yOf h).inv_mem hyC
  have hCz : ∀ C : Subgroup G, C ∈ sigmaSet M V → C ≤ cenOf (A ⊔ B) →
      C ≤ cenOf (Subgroup.zpowers h) := by
    intro C hC hCcen
    have hmem : C ∈ {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (Subgroup.zpowers h)} := by
      rw [hS6]
      exact ⟨hC, hCcen⟩
    exact hmem.2
  have hconj : ∀ C : Subgroup G, C ∈ sigmaSet M V → C ≤ cenOf (A ⊔ B) →
      conjSubgroup y C ≤ r0Of M V (A ⊔ B) := by
    intro C hC hCcen
    have hconjC : conjSubgroup y C ≤ cenOf (Subgroup.zpowers h) := by
      intro x hx
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
      have hyN : y ∈ Subgroup.normalizer (cenOf (Subgroup.zpowers h) : Set G) :=
        mem_normalizer_centralizer (Subgroup.centralizer_le_normalizer _ hyC)
      simpa [MulAut.conj_apply] using
        (Subgroup.mem_normalizer_iff.mp hyN c).mp (hCz C hC hCcen hc)
    have hconjSig := hS.sec5.conj_mem_sigmaSet hyM hC
    refine le_iSup₂_of_le
      (f := fun D (_ : D ∈ {D | D ∈ sigmaSet M V ∧ D ≤ cenOf (A ⊔ B)}) => D)
      (conjSubgroup y C) ⟨hconjSig, ?_⟩ le_rfl
    have hmem : conjSubgroup y C ∈
        {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (Subgroup.zpowers h)} :=
      ⟨hconjSig, hconjC⟩
    rw [hS6] at hmem
    exact hmem.2
  have hconj' : ∀ C : Subgroup G, C ∈ sigmaSet M V → C ≤ cenOf (A ⊔ B) →
      conjSubgroup y⁻¹ C ≤ r0Of M V (A ⊔ B) := by
    intro C hC hCcen
    have hconjC : conjSubgroup y⁻¹ C ≤ cenOf (Subgroup.zpowers h) := by
      intro x hx
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
      have hyN : y⁻¹ ∈ Subgroup.normalizer (cenOf (Subgroup.zpowers h) : Set G) :=
        mem_normalizer_centralizer (Subgroup.centralizer_le_normalizer _ hyC')
      simpa [MulAut.conj_apply] using
        (Subgroup.mem_normalizer_iff.mp hyN c).mp (hCz C hC hCcen hc)
    have hconjSig := hS.sec5.conj_mem_sigmaSet ((rOf M h).inv_mem hy).1 hC
    refine le_iSup₂_of_le
      (f := fun D (_ : D ∈ {D | D ∈ sigmaSet M V ∧ D ≤ cenOf (A ⊔ B)}) => D)
      (conjSubgroup y⁻¹ C) ⟨hconjSig, ?_⟩ le_rfl
    have hmem : conjSubgroup y⁻¹ C ∈
        {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (Subgroup.zpowers h)} :=
      ⟨hconjSig, hconjC⟩
    rw [hS6] at hmem
    exact hmem.2
  have hmap : conjSubgroup y (r0Of M V (A ⊔ B)) ≤ r0Of M V (A ⊔ B) := by
    simp only [r0Of, conjSubgroup, Subgroup.map_iSup]
    exact iSup₂_le fun C hC => hconj C hC.1 hC.2
  have hmap' : conjSubgroup y⁻¹ (r0Of M V (A ⊔ B)) ≤ r0Of M V (A ⊔ B) := by
    simp only [r0Of, conjSubgroup, Subgroup.map_iSup]
    exact iSup₂_le fun C hC => hconj' C hC.1 hC.2
  have heq : conjSubgroup y (r0Of M V (A ⊔ B)) = r0Of M V (A ⊔ B) := by
    refine le_antisymm hmap ?_
    calc r0Of M V (A ⊔ B) = conjSubgroup y (conjSubgroup y⁻¹ (r0Of M V (A ⊔ B))) := by
          rw [conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
      _ ≤ conjSubgroup y (r0Of M V (A ⊔ B)) := conjSubgroup_mono hmap'
  exact mem_normalizer_iff_conjSubgroup_eq.mpr heq

theorem r0_inf_Pc (hD : L2Datum M V A B h)
    (hS7 : p0Of M V (A ⊔ B) ≤ r0Of M V (A ⊔ B)) :
    r0Of M V (A ⊔ B) ⊓ Pc M V = p0Of M V (A ⊔ B) := by
  refine le_antisymm ?_ (le_inf hS7 inf_le_left)
  intro x hx
  obtain ⟨hxR0, hxP⟩ := Subgroup.mem_inf.mp hx
  have hxC : x ∈ cenOf (A ⊔ B) := by
    have hR0 : r0Of M V (A ⊔ B) ≤ cenOf (A ⊔ B) := by
      unfold r0Of
      exact iSup₂_le fun C hC => hC.2
    exact hR0 hxR0
  exact Subgroup.mem_inf.mpr ⟨hxP, hxC⟩

theorem conj (hS : Sec6Hyp M V) (hD : L2Datum M V A B h) {g : G} (hg : g ∈ M) :
    L2Datum M V (conjSubgroup g A) (conjSubgroup g B) (g * h * g⁻¹) where
  memA := hS.sec5.conj_mem_sigmaSet hg hD.memA
  memB := hS.sec5.conj_mem_sigmaSet hg hD.memB
  l2 := hD.l2.conj g
  mem := by
    rw [← conjSubgroup_sup]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hD.mem
  order := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hD.order]

end L2Datum

theorem Sec6Hyp.commutator_mem_of_mem_sup (hS : Sec6Hyp M V) {x : G}
    {H₁ H₂ : Subgroup G} (h₁ : H₁ ≤ M) (h₂ : H₂ ≤ M)
    (hx₁ : ∀ p ∈ H₁, ⁅x, p⁆ ∈ V) (hx₂ : ∀ p ∈ H₂, ⁅x, p⁆ ∈ V) :
    ∀ p ∈ H₁ ⊔ H₂, ⁅x, p⁆ ∈ V := by
  have hnorm : M ≤ Subgroup.normalizer (V : Set G) :=
    hS.sec5.toRootHyp.toHyp.le_normalizer
  have hH₁ : H₁ ≤ CFSG.GroupTheory.commMemSubgroup M V hnorm x := by
    intro p hp
    rw [CFSG.GroupTheory.mem_commMemSubgroup]
    exact ⟨h₁ hp, by rw [← commutatorElement_inv]; exact V.inv_mem (hx₁ p hp)⟩
  have hH₂ : H₂ ≤ CFSG.GroupTheory.commMemSubgroup M V hnorm x := by
    intro p hp
    rw [CFSG.GroupTheory.mem_commMemSubgroup]
    exact ⟨h₂ hp, by rw [← commutatorElement_inv]; exact V.inv_mem (hx₂ p hp)⟩
  intro p hp
  have hpK := _root_.sup_le hH₁ hH₂ hp
  rw [CFSG.GroupTheory.mem_commMemSubgroup] at hpK
  rw [← commutatorElement_inv]
  exact V.inv_mem hpK.2

namespace L2Datum

theorem commutator_Pc_le_p0 (hS : Sec6Hyp M V) (hD : L2Datum M V A B h)
    {C : Subgroup G} (hC : C ∈ sigmaSet M V) (hCX : C ≤ cenOf (A ⊔ B)) :
    ⁅Pc M V, C⁆ ≤ p0Of M V (A ⊔ B) := by
  have hA : ⁅Pc M V, C⁆ ≤ Pc M V ⊓ cenOf A := by
    rcases hS.res.s513 M V hS.sec5 C hC A hD.memA with ⟨-, hle⟩ | ⟨hL2, -⟩
    · exact hle
    · exfalso
      have hCA : C ≤ cenOf A :=
        hCX.trans (Subgroup.centralizer_le (le_sup_left : A ≤ A ⊔ B))
      exact hL2.commutator_ne_bot
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hCA)
  have hB : ⁅Pc M V, C⁆ ≤ Pc M V ⊓ cenOf B := by
    rcases hS.res.s513 M V hS.sec5 C hC B hD.memB with ⟨-, hle⟩ | ⟨hL2, -⟩
    · exact hle
    · exfalso
      have hCB : C ≤ cenOf B :=
        hCX.trans (Subgroup.centralizer_le (le_sup_right : B ≤ A ⊔ B))
      exact hL2.commutator_ne_bot
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hCB)
  change ⁅Pc M V, C⁆ ≤ Pc M V ⊓ cenOf (A ⊔ B)
  refine le_inf (hA.trans inf_le_left) ?_
  calc ⁅Pc M V, C⁆ ≤ cenOf A ⊓ cenOf B :=
        le_inf (hA.trans inf_le_right) (hB.trans inf_le_right)
    _ = cenOf (A ⊔ B) := (centralizer_sup_eq A B).symm

theorem mem_p0_of_commutator_mem (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    (hS1 : p0Of M V (Subgroup.zpowers h) = p0Of M V (A ⊔ B))
    {p : G} (hp : p ∈ Pc M V) (hpV : ⁅h, p⁆ ∈ V) : p ∈ p0Of M V (A ⊔ B) := by
  have hhyp : Hyp M V := hS.sec5.toRootHyp.toHyp
  have hXM : A ⊔ B ≤ M := _root_.sup_le
    (hS.sec5.le_M_of_mem_sigmaSet hD.memA).1
    (hS.sec5.le_M_of_mem_sigmaSet hD.memB).1
  have hmem : h ∈ M := hXM hD.mem
  have hRnorm : Subgroup.zpowers h ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.zpowers_le.mpr (hhyp.le_normalizer hmem)
  have hh : h ∈ CFSG.GroupTheory.commMemSubgroup
      (Subgroup.zpowers h) V hRnorm p := by
    rw [CFSG.GroupTheory.mem_commMemSubgroup]
    exact ⟨Subgroup.mem_zpowers h, hpV⟩
  have hzple : Subgroup.zpowers h ≤ CFSG.GroupTheory.commMemSubgroup
      (Subgroup.zpowers h) V hRnorm p := Subgroup.zpowers_le.mpr hh
  have hxR : ∀ r ∈ Subgroup.zpowers h, ⁅p, r⁆ ∈ V := by
    intro r hr
    have hpr : ⁅r, p⁆ ∈ V :=
      (CFSG.GroupTheory.mem_commMemSubgroup hRnorm p r).mp (hzple hr) |>.2
    rw [← commutatorElement_inv]
    exact V.inv_mem hpr
  have hNX : V ≤ Pc M V := hhyp.le_Pc
  have hN : (V.subgroupOf (Pc M V)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).mpr
      (hhyp.Pc_le_M.trans hhyp.le_normalizer)
  have hVsolv : Group.IsSolvable ↥V :=
    Group.isSolvable_of_comm fun a b => hhyp.maxAb.prop.2.2.is_comm.comm a b
  have hcop : Nat.Coprime (Nat.card V) (Nat.card ↥(Subgroup.zpowers h)) := by
    rw [Nat.card_zpowers, hD.order]
    exact (Nat.coprime_self_add_right (m := Nat.card V) (n := 1)).mpr
      (Nat.coprime_one_right _)
  obtain ⟨y, hyP, hyC, hxyV⟩ :=
    CFSG.GroupTheory.exists_mem_centralizer_of_commutator_mem hNX hN hRnorm hVsolv hcop
      hp hxR
  have hyC' : y ∈ cenOf (Subgroup.zpowers h) :=
    Subgroup.mem_centralizer_iff.mpr fun r hr => (hyC r hr).symm
  have hyP0 : y ∈ p0Of M V (A ⊔ B) := by
    rw [← hS1]
    exact Subgroup.mem_inf.mpr ⟨hyP, hyC'⟩
  have hp_eq : p = y * (p⁻¹ * y)⁻¹ := by group
  rw [hp_eq]
  exact (p0Of M V (A ⊔ B)).mul_mem hyP0
    ((p0Of M V (A ⊔ B)).inv_mem (V_le_p0 hS.toSec6Hyp hD hxyV))

theorem Pc_eq_p0_sup (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    (hS1 : p0Of M V (Subgroup.zpowers h) = p0Of M V (A ⊔ B)) :
    Pc M V = p0Of M V (A ⊔ B) ⊔ ⁅Pc M V, A ⊔ B⁆ := by
  set X : Subgroup G := A ⊔ B with hX
  set E : Subgroup G := ⁅Pc M V, X⁆ with hE
  have hXM : X ≤ M := _root_.sup_le (hS.sec5.le_M_of_mem_sigmaSet hD.memA).1
    (hS.sec5.le_M_of_mem_sigmaSet hD.memB).1
  have hXn : X ≤ Subgroup.normalizer (Pc M V : Set G) :=
    hXM.trans hS.sec5.toRootHyp.toHyp.le_normalizer_Pc
  have hEP : E ≤ Pc M V := Subgroup.le_normalizer_iff_commutator_le_left.mp hXn
  have hEN : (E.subgroupOf (Pc M V)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEP).mpr
      (Subgroup.normalizer_commutator_ge_left (Pc M V) X)
  have hRnorm : Subgroup.zpowers h ≤ Subgroup.normalizer (E : Set G) :=
    Subgroup.zpowers_le.mpr ((Subgroup.normalizer_commutator_ge_right (Pc M V) X) hD.mem)
  have hE2 : IsPGroup 2 E :=
    (inSubgroup_pCore_two M).1.to_le (hEP.trans inf_le_left)
  have hEsolv : Group.IsSolvable ↥E := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Group.IsNilpotent ↥E := IsPGroup.isNilpotent (p := 2) hE2
    exact IsNilpotent.to_isSolvable
  have hcop : Nat.Coprime (Nat.card ↥E) (Nat.card ↥(Subgroup.zpowers h)) := by
    obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq (p := 2) hE2
    rw [hk, Nat.card_zpowers, hD.order, hS.card_V]
    have hf : f ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hS.one_le)
    have hodd : Odd (2 ^ f + 1) :=
      ((Nat.even_pow (m := 2) (n := f)).mpr ⟨even_two, hf⟩).add_one
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  refine le_antisymm ?_ (_root_.sup_le inf_le_left hEP)
  intro p hp
  have hxR : ∀ r ∈ Subgroup.zpowers h, ⁅p, r⁆ ∈ E := fun r hr =>
    Subgroup.commutator_mem_commutator hp (Subgroup.zpowers_le.mpr hD.mem hr)
  obtain ⟨y, hyP, hyC, hyE⟩ :=
    CFSG.GroupTheory.exists_mem_centralizer_of_commutator_mem hEP hEN hRnorm hEsolv hcop
      hp hxR
  have hyC' : y ∈ cenOf (Subgroup.zpowers h) :=
    Subgroup.mem_centralizer_iff.mpr fun r hr => (hyC r hr).symm
  have hyP0 : y ∈ p0Of M V (A ⊔ B) := by
    rw [← hS1]
    exact Subgroup.mem_inf.mpr ⟨hyP, hyC'⟩
  have hp_eq : p = y * (p⁻¹ * y)⁻¹ := by group
  rw [hp_eq]
  exact (p0Of M V (A ⊔ B) ⊔ E).mul_mem (Subgroup.mem_sup_left hyP0)
    (Subgroup.mem_sup_right (E.inv_mem hyE))

theorem r0_le_cenOf_commutator (hS : Sec6Hyp M V) (hD : L2Datum M V A B h) :
    r0Of M V (A ⊔ B) ≤ cenOf ⁅Pc M V, A ⊔ B⁆ := by
  unfold r0Of
  refine iSup₂_le fun C hC => ?_
  have hCP : ⁅C, Pc M V⁆ ≤ p0Of M V (A ⊔ B) := by
    rw [Subgroup.commutator_comm]
    exact commutator_Pc_le_p0 hS hD hC.1 hC.2
  have hXC : ⁅A ⊔ B, C⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact (Subgroup.mem_centralizer_iff.mp (hC.2 hc) x hx).symm
  have h1 : ⁅⁅A ⊔ B, C⁆, Pc M V⁆ = ⊥ := by
    rw [hXC, Subgroup.commutator_bot_left]
  have h2 : ⁅⁅C, Pc M V⁆, A ⊔ B⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hCP.trans (inf_le_right : p0Of M V (A ⊔ B) ≤ cenOf (A ⊔ B))
  have hrot := Subgroup.commutator_commutator_eq_bot_of_rotate
    (H₁ := Pc M V) (H₂ := A ⊔ B) (H₃ := C) h1 h2
  rw [Subgroup.commutator_comm] at hrot
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hrot

theorem mem_Pc_of_trivial_p0 (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    (hS1 : p0Of M V (Subgroup.zpowers h) = p0Of M V (A ⊔ B)) {x : G} (hxM : x ∈ M)
    (hxE : x ∈ cenOf ⁅Pc M V, A ⊔ B⁆)
    (hx : ∀ p ∈ p0Of M V (A ⊔ B), ⁅x, p⁆ ∈ V) : x ∈ Pc M V := by
  have hEP : ⁅Pc M V, A ⊔ B⁆ ≤ Pc M V :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((_root_.sup_le (hS.sec5.le_M_of_mem_sigmaSet hD.memA).1
        (hS.sec5.le_M_of_mem_sigmaSet hD.memB).1).trans
        hS.sec5.toRootHyp.toHyp.le_normalizer_Pc)
  have hEM : ⁅Pc M V, A ⊔ B⁆ ≤ M :=
    hEP.trans hS.sec5.toRootHyp.toHyp.Pc_le_M
  have hP0M : p0Of M V (A ⊔ B) ≤ M :=
    inf_le_left.trans hS.sec5.toRootHyp.toHyp.Pc_le_M
  have hx' : ∀ p ∈ p0Of M V (A ⊔ B) ⊔ ⁅Pc M V, A ⊔ B⁆, ⁅x, p⁆ ∈ V := by
    refine Sec6Hyp.commutator_mem_of_mem_sup hS.toSec6Hyp hP0M hEM hx ?_
    intro e he
    have h1 : e * x = x * e := Subgroup.mem_centralizer_iff.mp hxE e he
    rw [commutatorElement_eq_one_iff_mul_comm.mpr h1.symm]
    exact V.one_mem
  have hxPc : ∀ p ∈ Pc M V, ⁅x, p⁆ ∈ V := by
    intro p hp
    rw [Pc_eq_p0_sup hS hD hS1] at hp
    exact hx' p hp
  exact Sec6Hyp.mem_Pc_of_commutator_mem hS.toSec6Hyp hxM hxPc

private theorem commutator_terms_setup (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    (hS1 : p0Of M V (Subgroup.zpowers h) = p0Of M V (A ⊔ B))
    {y r : G} (hyR : y ∈ rOf M h)
    (hy : ∀ q ∈ p0Of M V (A ⊔ B), ⁅y, q⁆ ∈ V)
    (hr : r ∈ r0Of M V (A ⊔ B)) {p : G} (hp : p ∈ p0Of M V (A ⊔ B)) :
    ⁅r, r⁻¹ * p * r⁆ ∈ p0Of M V (A ⊔ B) ∧
      ∀ x ∈ p0Of M V (A ⊔ B),
        ⁅(r⁻¹ * p * r) * y * (r⁻¹ * p * r)⁻¹, x⁆ ∈ V := by
  have hhyp : Hyp M V := hS.sec5.toRootHyp.toHyp
  obtain ⟨hyM, hyC⟩ := Subgroup.mem_inf.mp hyR
  have hrR : r ∈ rOf M h := r0_le_rOf hS.toSec6Hyp hD hr
  have hrP0 : r ∈ Subgroup.normalizer (p0Of M V (A ⊔ B) : Set G) :=
    rOf_le_normalizer_p0 hS.toSec6Hyp hD hS1 hrR
  have hp' : r⁻¹ * p * r ∈ p0Of M V (A ⊔ B) := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer
      (p0Of M V (A ⊔ B) : Set G)).inv_mem hrP0) p).mp hp
    simpa using this
  have hp'N : r⁻¹ * p * r ∈ Subgroup.normalizer
      (p0Of M V (A ⊔ B) : Set G) :=
    rOf_le_normalizer_p0 hS.toSec6Hyp hD hS1
      (p0_le_rOf hS.toSec6Hyp hD hp')
  have hp'M : r⁻¹ * p * r ∈ M := (p0_le_rOf hS.toSec6Hyp hD hp').1
  have hPr : ⁅r, r⁻¹ * p * r⁆ ∈ p0Of M V (A ⊔ B) := by
    have hPc : ⁅r, r⁻¹ * p * r⁆ ∈ Pc M V := by
      have h1 : r * (r⁻¹ * p * r) * r⁻¹ ∈ Pc M V :=
        (Subgroup.mem_normalizer_iff.mp
          (hhyp.le_normalizer_Pc hrR.1) (r⁻¹ * p * r)).mp hp'.1
      have h2 : (r * (r⁻¹ * p * r) * r⁻¹) * (r⁻¹ * p * r)⁻¹ ∈ Pc M V :=
        (Pc M V).mul_mem h1 ((Pc M V).inv_mem hp'.1)
      simpa [commutatorElement_def] using h2
    have hC : ⁅r, r⁻¹ * p * r⁆ ∈ cenOf (A ⊔ B) := by
      have hrCen : r ∈ cenOf (A ⊔ B) := by
        have hR0 : r0Of M V (A ⊔ B) ≤ cenOf (A ⊔ B) := by
          unfold r0Of
          exact iSup₂_le fun C hC => hC.2
        exact hR0 hr
      have hrN : r ∈ Subgroup.normalizer (cenOf (A ⊔ B) : Set G) :=
        mem_normalizer_centralizer (Subgroup.centralizer_le_normalizer _ hrCen)
      have hconj : r * (r⁻¹ * p * r) * r⁻¹ ∈ cenOf (A ⊔ B) := by
        have heq : r * (r⁻¹ * p * r) * r⁻¹ = p := by group
        rw [heq]
        exact hp.2
      have hmem := (cenOf (A ⊔ B)).mul_mem hconj
        ((cenOf (A ⊔ B)).inv_mem hp'.2)
      simpa [commutatorElement_def] using hmem
    exact Subgroup.mem_inf.mpr ⟨hPc, hC⟩
  refine ⟨hPr, fun x hx => ?_⟩
  have hx' : (r⁻¹ * p * r)⁻¹ * x * (r⁻¹ * p * r) ∈
      p0Of M V (A ⊔ B) := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer
      (p0Of M V (A ⊔ B) : Set G)).inv_mem hp'N) x).mp hx
    simpa using this
  have hyx : ⁅y, (r⁻¹ * p * r)⁻¹ * x * (r⁻¹ * p * r)⁆ ∈ V := hy _ hx'
  have hconj : (r⁻¹ * p * r) *
      ⁅y, (r⁻¹ * p * r)⁻¹ * x * (r⁻¹ * p * r)⁆ *
        (r⁻¹ * p * r)⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (hhyp.le_normalizer hp'M) _).mp hyx
  have hid : ⁅(r⁻¹ * p * r) * y * (r⁻¹ * p * r)⁻¹, x⁆ =
      (r⁻¹ * p * r) * ⁅y, (r⁻¹ * p * r)⁻¹ * x * (r⁻¹ * p * r)⁆ *
        (r⁻¹ * p * r)⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [hid]
  exact hconj

private theorem hallWitt_terms_mem_V (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    (hS1 : p0Of M V (Subgroup.zpowers h) = p0Of M V (A ⊔ B))
    (hS6 : {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (Subgroup.zpowers h)} =
      {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)})
    {y r : G} (hyR : y ∈ rOf M h)
    (hy : ∀ q ∈ p0Of M V (A ⊔ B), ⁅y, q⁆ ∈ V)
    (hr : r ∈ r0Of M V (A ⊔ B)) {p : G} (hp : p ∈ p0Of M V (A ⊔ B)) :
    ⁅⁅r, r⁻¹ * p * r⁆, (r⁻¹ * p * r) * y * (r⁻¹ * p * r)⁻¹⁆ ∈ V ∧
      ⁅⁅r⁻¹ * p * r, y⁆, y * r * y⁻¹⁆ ∈ V := by
  obtain ⟨hPr, hz⟩ := commutator_terms_setup hS hD hS1 hyR hy hr hp
  have hp' : r⁻¹ * p * r ∈ p0Of M V (A ⊔ B) := by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer
      (p0Of M V (A ⊔ B) : Set G)).inv_mem
        (rOf_le_normalizer_p0 hS.toSec6Hyp hD hS1
          (r0_le_rOf hS.toSec6Hyp hD hr))) p).mp hp
    simpa using this
  have hhyp : Hyp M V := hS.sec5.toRootHyp.toHyp
  have h2 : ⁅⁅r, r⁻¹ * p * r⁆,
      (r⁻¹ * p * r) * y * (r⁻¹ * p * r)⁻¹⁆ ∈ V := by
    have h' := V.inv_mem (hz ⁅r, r⁻¹ * p * r⁆ hPr)
    rwa [commutatorElement_inv] at h'
  have h3 : ⁅⁅r⁻¹ * p * r, y⁆, y * r * y⁻¹⁆ ∈ V := by
    have hyv : ⁅r⁻¹ * p * r, y⁆ ∈ V := by
      have h1 := V.inv_mem (hy _ hp')
      rwa [commutatorElement_inv] at h1
    have hconvR0 : y * r * y⁻¹ ∈ r0Of M V (A ⊔ B) :=
      (Subgroup.mem_normalizer_iff.mp
        (rOf_le_normalizer_r0 hS.toSec6Hyp hD hS6 hyR) r).mp hr
    have hconv : y * r * y⁻¹ ∈ rOf M h := r0_le_rOf hS.toSec6Hyp hD hconvR0
    have hVn : y * r * y⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      hhyp.le_normalizer hconv.1
    have hgx : y * r * y⁻¹ * ⁅r⁻¹ * p * r, y⁆ * (y * r * y⁻¹)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp hVn _).mp hyv
    have hmem := V.mul_mem hyv (V.inv_mem hgx)
    have heq : ⁅⁅r⁻¹ * p * r, y⁆, y * r * y⁻¹⁆ =
        ⁅r⁻¹ * p * r, y⁆ *
          (y * r * y⁻¹ * ⁅r⁻¹ * p * r, y⁆ * (y * r * y⁻¹)⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rwa [heq]
  exact ⟨h2, h3⟩

private theorem commutator_commutator_mem_V (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    (hS1 : p0Of M V (Subgroup.zpowers h) = p0Of M V (A ⊔ B))
    (hS6 : {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (Subgroup.zpowers h)} =
      {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)})
    {y r : G} (hyR : y ∈ rOf M h)
    (hy : ∀ q ∈ p0Of M V (A ⊔ B), ⁅y, q⁆ ∈ V)
    (hr : r ∈ r0Of M V (A ⊔ B)) :
    ∀ p ∈ p0Of M V (A ⊔ B), ⁅⁅y, r⁆, p⁆ ∈ V := by
  intro p hp
  obtain ⟨h2, h3⟩ := hallWitt_terms_mem_V hS hD hS1 hS6 hyR hy hr hp
  have hHW := commutatorElement_commutatorElement_conj_mul y r (r⁻¹ * p * r)
  have hprod : ⁅⁅y, r⁆, r * (r⁻¹ * p * r) * r⁻¹⁆ *
      (⁅⁅r, r⁻¹ * p * r⁆, (r⁻¹ * p * r) * y * (r⁻¹ * p * r)⁻¹⁆ *
        ⁅⁅r⁻¹ * p * r, y⁆, y * r * y⁻¹⁆) = 1 := by
    rw [mul_assoc] at hHW
    exact hHW
  have hfirst : ⁅⁅y, r⁆, r * (r⁻¹ * p * r) * r⁻¹⁆ ∈ V := by
    rw [eq_inv_of_mul_eq_one_left hprod]
    exact V.inv_mem (V.mul_mem h2 h3)
  have hrp : r * (r⁻¹ * p * r) * r⁻¹ = p := by group
  rwa [hrp] at hfirst

theorem commutator_r0_mem_p0 (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    (hS1 : p0Of M V (Subgroup.zpowers h) = p0Of M V (A ⊔ B))
    (hS6 : {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (Subgroup.zpowers h)} =
      {C | C ∈ sigmaSet M V ∧ C ≤ cenOf (A ⊔ B)})
    {y : G} (hyR : y ∈ rOf M h) (hy : ∀ p ∈ p0Of M V (A ⊔ B), ⁅y, p⁆ ∈ V)
    {r : G} (hr : r ∈ r0Of M V (A ⊔ B)) : ⁅y, r⁆ ∈ p0Of M V (A ⊔ B) := by
  obtain ⟨hyM, hyC⟩ := Subgroup.mem_inf.mp hyR
  have hrR : r ∈ rOf M h := r0_le_rOf hS.toSec6Hyp hD hr
  have hxR0 : ⁅y, r⁆ ∈ r0Of M V (A ⊔ B) := by
    have h1 : y * r * y⁻¹ ∈ r0Of M V (A ⊔ B) :=
      (Subgroup.mem_normalizer_iff.mp
        (rOf_le_normalizer_r0 hS.toSec6Hyp hD hS6 hyR) r).mp hr
    have h2 : (y * r * y⁻¹) * r⁻¹ ∈ r0Of M V (A ⊔ B) :=
      (r0Of M V (A ⊔ B)).mul_mem h1 ((r0Of M V (A ⊔ B)).inv_mem hr)
    simpa [commutatorElement_def] using h2
  have hxE : ⁅y, r⁆ ∈ cenOf ⁅Pc M V, A ⊔ B⁆ :=
    r0_le_cenOf_commutator hS.toSec6Hyp hD hxR0
  have hxV : ∀ p ∈ p0Of M V (A ⊔ B), ⁅⁅y, r⁆, p⁆ ∈ V :=
    commutator_commutator_mem_V hS hD hS1 hS6 hyR hy hr
  have hxPc : ⁅y, r⁆ ∈ Pc M V :=
    mem_Pc_of_trivial_p0 hS hD hS1 (r0_le_rOf hS.toSec6Hyp hD hxR0).1 hxE hxV
  have hxC : ⁅y, r⁆ ∈ cenOf (Subgroup.zpowers h) := by
    have hyN : y ∈ Subgroup.normalizer (cenOf (Subgroup.zpowers h) : Set G) :=
      mem_normalizer_centralizer (Subgroup.centralizer_le_normalizer _ hyC)
    have hconj : y * r * y⁻¹ ∈ cenOf (Subgroup.zpowers h) :=
      (Subgroup.mem_normalizer_iff.mp hyN r).mp hrR.2
    have hmem := (cenOf (Subgroup.zpowers h)).mul_mem hconj
      ((cenOf (Subgroup.zpowers h)).inv_mem hrR.2)
    simpa [commutatorElement_def] using hmem
  exact hS1 ▸ Subgroup.mem_inf.mpr ⟨hxPc, hxC⟩

theorem commutator_Pc_eq_p0 (hS : Sec7Hyp M V n f) (hD : L2Datum M V A B h)
    (hS1 : p0Of M V (Subgroup.zpowers h) = p0Of M V (A ⊔ B))
    {C : Subgroup G} (hC : C ∈ sigmaSet M V) (hCX : C ≤ cenOf (A ⊔ B)) :
    ⁅Pc M V, C⁆ = ⁅p0Of M V (A ⊔ B), C⁆ := by
  refine le_antisymm ?_ (Subgroup.commutator_mono inf_le_left le_rfl)
  have hEP : ⁅Pc M V, A ⊔ B⁆ ≤ Pc M V :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((_root_.sup_le (hS.sec5.le_M_of_mem_sigmaSet hD.memA).1
        (hS.sec5.le_M_of_mem_sigmaSet hD.memB).1).trans
        hS.sec5.toRootHyp.toHyp.le_normalizer_Pc)
  have hP0E : p0Of M V (A ⊔ B) ≤
      Subgroup.normalizer ((⁅Pc M V, A ⊔ B⁆ : Subgroup G) : Set G) :=
    inf_le_left.trans (Subgroup.normalizer_commutator_ge_left (Pc M V) (A ⊔ B))
  have hCR0 : C ≤ r0Of M V (A ⊔ B) :=
    le_iSup₂ (f := fun D (_ : D ∈ {D | D ∈ sigmaSet M V ∧ D ≤ cenOf (A ⊔ B)}) => D)
      C ⟨hC, hCX⟩
  have hCE : C ≤ cenOf ⁅Pc M V, A ⊔ B⁆ :=
    hCR0.trans (r0_le_cenOf_commutator hS.toSec6Hyp hD)
  rw [Subgroup.commutator_le]
  intro p hp c hc
  have hset : ((Pc M V : Subgroup G) : Set G) =
      ((p0Of M V (A ⊔ B) ⊔ ⁅Pc M V, A ⊔ B⁆ : Subgroup G) : Set G) := by
    conv_lhs => rw [Pc_eq_p0_sup hS hD hS1]
  have hp'' : p ∈ ((p0Of M V (A ⊔ B) ⊔ ⁅Pc M V, A ⊔ B⁆ : Subgroup G) : Set G) := by
    rwa [← hset]
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right (p0Of M V (A ⊔ B))
    ⁅Pc M V, A ⊔ B⁆ hP0E
  rw [hcoe] at hp''
  obtain ⟨p₀, hp₀, e, he, rfl⟩ := Set.mem_mul.mp hp''
  have hec : e * c = c * e :=
    Subgroup.mem_centralizer_iff.mp (hCE hc) e he
  have hcomm : ⁅p₀ * e, c⁆ = ⁅p₀, c⁆ := by
    calc ⁅p₀ * e, c⁆ = p₀ * (e * c * e⁻¹) * p₀⁻¹ * c⁻¹ := by
          rw [commutatorElement_def]
          group
      _ = p₀ * c * p₀⁻¹ * c⁻¹ := by
          rw [show e * c * e⁻¹ = c by rw [hec]; group]
      _ = ⁅p₀, c⁆ := by rw [commutatorElement_def]
  rw [hcomm]
  exact Subgroup.commutator_mem_commutator hp₀ hc

end L2Datum

end CFSG.RankThree.GF2n.Tim81
