module

public import CFSG.RankThree.PartTwo.KFacts.BlackburnScalar
import CFSG.RankThree.PartTwo.Sec11.SimsR1Blackburn
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank
import CFSG.GroupTheory.SectionLemmas
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Lemmas
public import Mathlib.Algebra.Group.Action.End
public import Mathlib.Algebra.Group.Commute.Defs
public import Mathlib.GroupTheory.Commutator.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Quotient
import CFSG.GH74.GLS.Stage2.Bender.Thm1.IG109
public import CFSG.Assembly.InCatalog
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.Defs
import CFSG.CharacterTheory.Blocks.Defs
import CFSG.GH74.GLS.Defs
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der62
import CFSG.GH74.GLS.Stage2.Bender.Thm1.ExtraInv
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7
import CFSG.GH74.GLS.Stage2.Final.Named
import CFSG.GH74.GLS.Stage2.Local.Concl
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.theorem_3_6
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

open Subgroup
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec16.Kcd166

open CFSG.RankThree.PartTwo.Sec11.SimsR1.Blackburn

private lemma generatorRank_frattini_quotient_le_card
    {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P] [Fact (IsPGroup p P)]
    {s : Finset P} (hs : Subgroup.closure (s : Set P) ⊔ frattini P = ⊤) :
    CFSG.generatorRank (P ⧸ frattini P) ≤ s.card := by
  classical
  let q : P →* P ⧸ frattini P := QuotientGroup.mk' (frattini P)
  have hmapΦ : (frattini P).map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hmap : (Subgroup.closure (s : Set P)).map q = ⊤ := by
    have h := congrArg (Subgroup.map q) hs
    rw [Subgroup.map_sup, hmapΦ, sup_bot_eq,
      Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)] at h
    exact h
  let t : Fin s.card → P := fun i => ((s.equivFin.symm i : s) : P)
  have ht : Set.range t = (s : Set P) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (s.equivFin.symm i).2
    · intro hx
      exact ⟨s.equivFin ⟨x, hx⟩, by simp [t]⟩
  have hgen : Subgroup.closure (Set.range (fun i => q (t i))) = ⊤ := by
    have h := MonoidHom.map_closure q (Set.range t)
    rw [ht, hmap] at h
    have hrange : (q '' (s : Set P)) = Set.range (fun i => q (t i)) := by
      rw [← ht]
      ext y
      constructor
      · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
        exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨t i, ⟨i, rfl⟩, rfl⟩
    rw [← hrange]
    exact h.symm
  let S : Finset (P ⧸ frattini P) := Finset.univ.image (fun i => q (t i))
  have hS : Subgroup.closure (S : Set (P ⧸ frattini P)) = ⊤ := by
    simpa [S, Finset.coe_image, Finset.coe_univ, Set.image_univ] using hgen
  have hS_card : S.card ≤ s.card := by
    simpa [S] using Finset.card_image_le (s := Finset.univ) (f := fun i => q (t i))
  rw [CFSG.generatorRank_eq_group_rank]
  exact (Group.rank_le hS).trans hS_card

private theorem frattini_index_le_pow_card_of_sup_eq_top
    {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P] [Fact (IsPGroup p P)]
    {s : Finset P} (hs : Subgroup.closure (s : Set P) ⊔ frattini P = ⊤) :
    (frattini P).index ≤ p ^ s.card := by
  have hrank : CFSG.generatorRank (P ⧸ frattini P) ≤ s.card :=
    generatorRank_frattini_quotient_le_card (p := p) (P := P) hs
  haveI : Fact (IsPGroup p (P ⧸ frattini P)) :=
    ⟨(Fact.out : IsPGroup p P).to_quotient (frattini P)⟩
  haveI : IsElementaryAbelian p (P ⧸ frattini P) :=
    CFSG.isElementaryAbelian_quotient_frattini
  have hcard : Nat.card (P ⧸ frattini P) = p ^ CFSG.generatorRank (P ⧸ frattini P) :=
    CFSG.elementaryAbelian_card_eq_pow_generatorRank (p := p) (P ⧸ frattini P)
  calc (frattini P).index = Nat.card (P ⧸ frattini P) := Subgroup.index_eq_card _
    _ = p ^ CFSG.generatorRank (P ⧸ frattini P) := hcard
    _ ≤ p ^ s.card := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hrank

private lemma commutator_pow_mul_pow_of_central
    {P : Type*} [Group P] {E Z : Subgroup P}
    (hZE : ∀ z ∈ Z, ∀ x ∈ E, z * x = x * z)
    (hder : ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ Z)
    {u c a z : P} (hu : u ∈ E) (hc : c ∈ E) (ha : a ∈ E)
    (hz : z ∈ Z) (hac : a * c = c * a) (m n : ℕ) :
    ⁅u ^ m * a, c ^ n * z⁆ = ⁅u, c⁆ ^ (m * n) := by
  have hleft : ⁅a, c ^ n * z⁆ = 1 := by
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    have h1 : a * c ^ n = c ^ n * a := ((show Commute a c from hac).pow_right n).eq
    have h2 : a * z = z * a := (hZE z hz a ha).symm
    calc a * (c ^ n * z) = (a * c ^ n) * z := by group
      _ = (c ^ n * a) * z := by rw [h1]
      _ = c ^ n * (a * z) := by group
      _ = c ^ n * (z * a) := by rw [h2]
      _ = (c ^ n * z) * a := by group
  have hright : ⁅u ^ m, z⁆ = 1 := by
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    have hzu : Commute z u := hZE z hz u hu
    exact (hzu.pow_right m).eq.symm
  have huc : ⁅u, c⁆ ∈ Z := hder u hu c hc
  have hucomm : Commute u ⁅u, c⁆ := (hZE _ huc u hu).symm
  have hccomm : Commute c ⁅u, c⁆ := (hZE _ huc c hc).symm
  have hcn : Commute u ⁅u, c ^ n⁆ := by
    rw [← Commute.commutatorElement_pow_right hccomm n]
    exact hucomm.pow_right n
  calc ⁅u ^ m * a, c ^ n * z⁆
      = u ^ m * ⁅a, c ^ n * z⁆ * (u ^ m)⁻¹ * ⁅u ^ m, c ^ n * z⁆ := by
          rw [commutatorElement_mul_left_eq_conj_mul]
    _ = ⁅u ^ m, c ^ n * z⁆ := by rw [hleft]; group
    _ = ⁅u ^ m, c ^ n⁆ * (c ^ n) * ⁅u ^ m, z⁆ * (c ^ n)⁻¹ := by
          rw [commutatorElement_mul_right_eq_mul_conj]
    _ = ⁅u ^ m, c ^ n⁆ := by rw [hright]; group
    _ = ⁅u, c ^ n⁆ ^ m := (Commute.commutatorElement_pow_left hcn m).symm
    _ = (⁅u, c⁆ ^ n) ^ m := by rw [Commute.commutatorElement_pow_right hccomm n]
    _ = ⁅u, c⁆ ^ (n * m) := by rw [pow_mul]
    _ = ⁅u, c⁆ ^ (m * n) := by rw [Nat.mul_comm]

private lemma index_eq_prime_of_le_prime {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) {K : Subgroup P} (hle : K.index ≤ p) (hne : K.index ≠ 1) :
    K.index = p := by
  obtain ⟨n, hn⟩ := hP.index K
  have hn_le : n ≤ 1 :=
    (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 (by simpa [hn] using hle)
  have hn_ne : n ≠ 0 := by
    intro h0
    exact hne (by rw [hn, h0, pow_zero])
  have hn1 : n = 1 := by omega
  rw [hn, hn1, pow_one]

private lemma index_le_sq_of_sup_frattini_eq_top
    {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    {E Z : Subgroup P} (hsup : E ⊔ frattini P = ⊤)
    (hZE : Z ≤ E) (hZΦ : Z ≤ frattini P)
    (hEcard : Nat.card E = p ^ 3) (hZcard : Nat.card Z = p) :
    (frattini P).index ≤ p ^ 2 := by
  have hZle : Z ≤ E ⊓ frattini P := le_inf hZE hZΦ
  have hrel : (E ⊓ frattini P).relIndex E ∣ Z.relIndex E :=
    Subgroup.relIndex_dvd_of_le_left (L := E) hZle
  have hZrel : Z.relIndex E = p ^ 2 := by
    have h := Subgroup.relIndex_mul_card (H := Z) (K := E)
    rw [inf_of_le_left hZE, hZcard, hEcard] at h
    have h' : Z.relIndex E * p = p ^ 2 * p := by
      rw [h]
      ring
    exact Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos h'
  have hErel : (E ⊓ frattini P).relIndex E ≤ p ^ 2 :=
    Nat.le_of_dvd (pow_pos (Fact.out : p.Prime).pos 2) (hZrel ▸ hrel)
  have hidx : (frattini P).index = (E ⊓ frattini P).relIndex E := by
    calc (frattini P).index = (frattini P).relIndex ⊤ :=
          (Subgroup.relIndex_top_right (H := frattini P)).symm
      _ = (frattini P).relIndex (E ⊔ frattini P) := by rw [hsup]
      _ = (frattini P).relIndex E := Subgroup.relIndex_sup_right E (frattini P)
      _ = (E ⊓ frattini P).relIndex E := by
            rw [inf_comm, Subgroup.inf_relIndex_right]
  rw [hidx]
  exact hErel


private lemma not_isMulCommutative_of_isExtraspecial {p : ℕ} {E : Type*} [Group E]
    [IsExtraspecial p E] : ¬ IsMulCommutative E := by
  intro hcomm
  have hcenter : Subgroup.center E = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_center_iff]
    intro y
    exact (hcomm.is_comm.comm x y).symm
  haveI : Subsingleton (E ⧸ Subgroup.center E) :=
    (QuotientGroup.subsingleton_iff (N := Subgroup.center E)).2 hcenter
  haveI := IsExtraspecial.quotient_nontrivial p E
  obtain ⟨x, y, hxy⟩ := exists_pair_ne (E ⧸ Subgroup.center E)
  exact hxy (Subsingleton.elim x y)

private lemma conj_mem_characteristic_iff
    {P : Type*} [Group P] {Z : Subgroup P} (hZchar : Z.Characteristic) :
    ∀ (g : P) (x : P), x ∈ Z ↔ g * x * g⁻¹ ∈ Z := by
  intro g x
  rw [show g * x * g⁻¹ = MulAut.conj g x from (MulAut.conj_apply g x).symm]
  have hfix := hZchar.fixed (MulAut.conj g)
  have hcomap : x ∈ Z.comap (MulAut.conj g).toMonoidHom ↔ (MulAut.conj g x) ∈ Z :=
    Subgroup.mem_comap
  rwa [hfix] at hcomap

private lemma quotient_center_card_eq_prime
    {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    {A Z : Subgroup P} (hAZ : Z ≤ A) (hAcard : Nat.card A = p ^ 2)
    (hZcard : Nat.card Z = p) :
    Nat.card (↥A ⧸ Z.subgroupOf A) = p := by
  haveI : IsMulCommutative ↥A := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hAcard
  haveI : (Z.subgroupOf A).Normal := Subgroup.normal_of_isMulCommutative _
  have hZsubcard : Nat.card (Z.subgroupOf A) = p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAZ).toEquiv, hZcard]
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (Z.subgroupOf A)
  rw [hAcard, hZsubcard] at hmul
  have h2 : Nat.card (↥A ⧸ Z.subgroupOf A) * p = p * p := by
    rw [← hmul, pow_two]
  exact Nat.eq_of_mul_eq_mul_right (Fact.out : p.Prime).pos h2

private lemma commutator_mem_of_mem_of_card_eq_prime_sq
    {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) {A Z : Subgroup P}
    (hAZ : Z ≤ A) (hAcard : Nat.card A = p ^ 2) (hZcard : Nat.card Z = p)
    (hAnorm : A.Normal) (hZchar : Z.Characteristic)
    {a g : P} (ha : a ∈ A) :
    ⁅a, g⁆ ∈ Z := by
  classical
  have hp : p.Prime := Fact.out
  haveI : IsMulCommutative ↥A := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) hAcard
  haveI : (Z.subgroupOf A).Normal := Subgroup.normal_of_isMulCommutative _
  haveI hZcharI : Z.Characteristic := hZchar
  have hZnormal : Z.Normal := inferInstance
  have hquotcard : Nat.card (↥A ⧸ Z.subgroupOf A) = p :=
    quotient_center_card_eq_prime hAZ hAcard hZcard
  let act : P →* MulAut ↥A := MulAut.conjNormal (H := A)
  let : MulDistribMulAction P ↥A := MulDistribMulAction.compHom ↥A act
  have hZinv : IsInvariant P ↥A (Z.subgroupOf A) := by
    refine ⟨fun g x => ?_⟩
    change (x : P) ∈ Z ↔ (((act g) x : ↥A) : P) ∈ Z
    rw [show (((act g) x : ↥A) : P) = g * (x : P) * g⁻¹ from MulAut.conjNormal_apply g x]
    exact conj_mem_characteristic_iff hZchar g (x : P)
  let : MulAction.QuotientAction P (Z.subgroupOf A) :=
    quotientAction_of_isInvariant (A := P) (Z.subgroupOf A) hZinv
  let : MulDistribMulAction P (↥A ⧸ Z.subgroupOf A) :=
    quotientMulDistribMulAction (A := P) (G := ↥A) (Z.subgroupOf A) hZinv
  haveI : IsCyclic (↥A ⧸ Z.subgroupOf A) := isCyclic_of_prime_card hquotcard
  have htriv : ActsTrivially P (↥A ⧸ Z.subgroupOf A) :=
    actsTrivially_of_isPGroup_on_cyclic_prime_order hp hP (inferInstance) hquotcard
  let x : ↥A := ⟨a, ha⟩
  have hq := htriv g (QuotientGroup.mk x)
  rw [MulAction.Quotient.smul_mk] at hq
  have hmem : (x⁻¹ * (g • x) : ↥A) ∈ Z.subgroupOf A := QuotientGroup.eq.mp hq.symm
  have hmemZ : (((x⁻¹ * (g • x) : ↥A) : P)) ∈ Z := Subgroup.mem_subgroupOf.mp hmem
  have hsmul : (((g • x : ↥A) : P)) = g * a * g⁻¹ := by
    change (((act g) x : ↥A) : P) = g * a * g⁻¹
    rw [MulAut.conjNormal_apply]
  have hcoe : (((x⁻¹ * (g • x) : ↥A) : P)) = ⁅a⁻¹, g⁆ := by
    simp only [x, Subgroup.coe_inv, Subgroup.coe_mul]
    rw [hsmul]
    rw [commutatorElement_def]
    group
  rw [hcoe] at hmemZ
  have hconj : a * ⁅a⁻¹, g⁆ * a⁻¹ ∈ Z := hZnormal.conj_mem _ hmemZ a
  have hform : a * ⁅a⁻¹, g⁆ * a⁻¹ = ⁅a, g⁆⁻¹ := by
    rw [commutatorElement_inv_left, commutatorElement_inv]
    group
  rw [hform] at hconj
  simpa using Z.inv_mem hconj

private lemma frattini_index_le_pow_two_of_relIndex_le
    {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    {Y : Subgroup P} (hY : (Y ⊔ frattini P).index ≤ p)
    (hrel : (frattini P).relIndex (Y ⊔ frattini P) ≤ p) :
    (frattini P).index ≤ p ^ 2 := by
  have h := Subgroup.relIndex_mul_index (H := frattini P) (K := Y ⊔ frattini P) le_sup_right
  calc (frattini P).index = (frattini P).relIndex (Y ⊔ frattini P) * (Y ⊔ frattini P).index :=
        h.symm
    _ ≤ p * p := Nat.mul_le_mul hrel hY
    _ = p ^ 2 := by ring

private lemma commutator_mem_of_mem_sup_centralizer
    {P : Type*} [Group P] {E C Z : Subgroup P}
    (hCE : C ≤ Subgroup.centralizer (E : Set P))
    (hder : ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ Z)
    (hEnorm : E.Normal) {e x : P} (he : e ∈ E) (hx : x ∈ E ⊔ C) :
    ⁅e, x⁆ ∈ Z := by
  obtain ⟨e', he', c, hc, rfl⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := E) (t := C)).mp hx
  have h1 : ⁅e, e' * c⁆ = ⁅e, e'⁆ * e' * ⁅e, c⁆ * e'⁻¹ :=
    commutatorElement_mul_right_eq_mul_conj e e' c
  have h2 : ⁅e, c⁆ = 1 := by
    refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
    exact Subgroup.mem_centralizer_iff.mp (hCE hc) e he
  rw [h1, h2]
  have h4 : ⁅e, e'⁆ * e' * 1 * e'⁻¹ = ⁅e, e'⁆ := by group
  rw [h4]
  exact hder e he e' he'

private lemma zpowers_sup_eq_of_card {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    {A E : Subgroup P} (hAE : A ≤ E) (hA : Nat.card A = p ^ 2) (hE : Nat.card E = p ^ 3)
    {u : P} (huE : u ∈ E) (huA : u ∉ A) :
    Subgroup.zpowers u ⊔ A = E := by
  let B : Subgroup P := Subgroup.zpowers u ⊔ A
  have hBle : B ≤ E := sup_le (Subgroup.zpowers_le.mpr huE) hAE
  have hAlt : A < B := lt_of_le_of_ne le_sup_right (by
    intro hAB
    apply huA
    rw [hAB]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers u))
  have hBcard_gt : p ^ 2 < Nat.card B := by
    rw [← hA]
    exact Subgroup.card_lt_of_lt hAlt
  have hBdvd : Nat.card B ∣ p ^ 3 := by
    rw [← hE]
    exact Subgroup.card_dvd_of_le hBle
  obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hBdvd
  have hkgt : 2 < k := by
    have : p ^ 2 < p ^ k := by rw [← hk]; exact hBcard_gt
    exact (Nat.pow_lt_pow_iff_right (Fact.out : p.Prime).one_lt).mp this
  have hk3 : k = 3 := by omega
  refine Subgroup.eq_of_le_of_card_ge hBle ?_
  rw [hk, hk3, ← hE]



private structure Setting (p : ℕ) [Fact p.Prime] (P : Type*) [Group P] [Finite P] where
  E : Subgroup P
  C : Subgroup P
  Ceq : C = Subgroup.centralizer (E : Set P)
  Z : Subgroup P
  Echar : E.Characteristic
  Cchar : C.Characteristic
  Eextra : IsExtraspecial p E
  Ecard : Nat.card E = p ^ 3
  Eexp : Monoid.exponent E = p
  Epow : ∀ x ∈ E, x ^ p = 1
  Zcard : Nat.card Z = p
  Zchar : Z.Characteristic
  ZleE : Z ≤ E
  ZleC : Z ≤ C
  EC : E ⊓ C = Z
  Zcentral : ∀ z ∈ Z, ∀ x ∈ E, z * x = x * z
  derE : ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ Z
  Ccyclic : IsCyclic C
  ZleΦ : Z ≤ frattini P
  Enoncomm : ¬ IsMulCommutative E
  Ccentral : C ≤ Subgroup.centralizer (E : Set P)

private lemma omega_extraspecial
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (hp : 5 ≤ p) (hP : IsPGroup p P)
    (hE : ∀ E : Subgroup P, CFSG.Assembly.IsElemAbelian p E → Nat.card E ≤ p ^ 2)
    (hsmall : ¬ Nat.card (CFSG.omega₁ (G := P) (p := p)) ≤ p ^ 2) :
    IsExtraspecial p (CFSG.omega₁ (G := P) (p := p)) ∧
      Nat.card (CFSG.omega₁ (G := P) (p := p)) = p ^ 3 ∧
      Monoid.exponent (CFSG.omega₁ (G := P) (p := p)) = p := by
  haveI : Fact (IsPGroup p P) := ⟨hP⟩
  have h3 : 3 < p := by omega
  have hrank : CFSG.groupRank P ≤ 2 := groupRank_le_two (P := P) hP hE
  have hlarge := omega_large h3 hrank hsmall
  exact ⟨isExtraspecial_omega h3 hrank hsmall, hlarge.2, hlarge.1⟩

private lemma omega_pow_eq_one
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (hexp : Monoid.exponent (CFSG.omega₁ (G := P) (p := p)) = p) :
    ∀ x ∈ CFSG.omega₁ (G := P) (p := p), x ^ p = 1 := by
  intro x hx
  have h := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : CFSG.omega₁ (G := P) (p := p))
  rw [hexp] at h
  simpa using congrArg (CFSG.omega₁ (G := P) (p := p)).subtype h

private lemma omega_noncomm
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P]
    (hextra : IsExtraspecial p (CFSG.omega₁ (G := P) (p := p))) :
    ¬ IsMulCommutative (CFSG.omega₁ (G := P) (p := p)) := by
  haveI : IsExtraspecial p (CFSG.omega₁ (G := P) (p := p)) := hextra
  exact not_isMulCommutative_of_isExtraspecial (p := p)
    (E := ↥(CFSG.omega₁ (G := P) (p := p)))

private lemma center_facts
    {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    {E C Z : Subgroup P}
    (hC : C = Subgroup.centralizer (E : Set P))
    (hZ : Z = (Subgroup.center E).map E.subtype)
    (hEchar : E.Characteristic) (hEextra : IsExtraspecial p E) :
    Z.Characteristic ∧ Nat.card Z = p ∧ Z ≤ E ∧ Z ≤ C ∧ E ⊓ C = Z ∧
      (∀ z ∈ Z, ∀ x ∈ E, z * x = x * z) := by
  subst hC
  subst hZ
  haveI : E.Characteristic := hEchar
  haveI : IsExtraspecial p E := hEextra
  have hZchar : ((Subgroup.center E).map E.subtype).Characteristic :=
    Subgroup.characteristic_of_characteristic_of_characteristic
      (H := E) (K := Subgroup.center E)
  have hZcard : Nat.card ((Subgroup.center E).map E.subtype) = p := by
    rw [Subgroup.card_map_of_injective E.subtype_injective]
    exact IsExtraspecial.center_order_p p ↥E
  have hZleE : (Subgroup.center E).map E.subtype ≤ E := Subgroup.map_subtype_le _
  have hZleC : (Subgroup.center E).map E.subtype ≤ Subgroup.centralizer (E : Set P) := by
    rintro x ⟨z, hz, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    simpa using congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)
  have hEC : E ⊓ Subgroup.centralizer (E : Set P) = (Subgroup.center E).map E.subtype := by
    apply le_antisymm
    · rintro x ⟨hxE, hxC⟩
      refine Subgroup.mem_map.mpr ⟨⟨x, hxE⟩, ?_, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC (y : P) y.2)
    · rintro x ⟨z, hz, rfl⟩
      refine ⟨z.2, ?_⟩
      change (z : P) ∈ Subgroup.centralizer (E : Set P)
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      simpa using congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)
  have hZcentral : ∀ z ∈ (Subgroup.center E).map E.subtype, ∀ x ∈ E, z * x = x * z := by
    rintro z ⟨z', hz', rfl⟩ x hx
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz' ⟨x, hx⟩).symm
  exact ⟨hZchar, hZcard, hZleE, hZleC, hEC, hZcentral⟩

private lemma commutator_center_eq
    {p : ℕ} [Fact p.Prime] {E : Type*} [Group E] [Finite E] [IsExtraspecial p E] :
    _root_.commutator E = Subgroup.center E := by
  have hcenter : _root_.commutator E ≤ Subgroup.center E := by
    haveI : IsElementaryAbelian p (E ⧸ Subgroup.center E) :=
      IsExtraspecial.quotient_elementary_abelian p E
    exact Subgroup.Normal.quotient_commutative_iff_commutator_le.1 inferInstance
  refine Subgroup.eq_of_le_of_card_ge hcenter ?_
  have hne : _root_.commutator E ≠ ⊥ := by
    intro hbot
    apply not_isMulCommutative_of_isExtraspecial (p := p) (E := E)
    refine ⟨⟨fun a b => ?_⟩⟩
    have hmem : ⁅a, b⁆ ∈ _root_.commutator E := by
      rw [_root_.commutator_def]
      exact commutator_mem_commutator (H₁ := ⊤) (H₂ := ⊤) (mem_top _) (mem_top _)
    rw [hbot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp (by simpa using hmem)
  have hgt : 1 < Nat.card (_root_.commutator E) := by
    rw [← Subgroup.card_bot (G := E)]
    exact Subgroup.card_lt_of_lt (bot_lt_iff_ne_bot.mpr hne)
  have hdvd : Nat.card (_root_.commutator E) ∣ p := by
    rw [← IsExtraspecial.center_order_p p E]
    exact Subgroup.card_dvd_of_le hcenter
  have hcard : Nat.card (_root_.commutator E) = p := by
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hdvd with h1 | hp_eq
    · omega
    · exact hp_eq
  rw [IsExtraspecial.center_order_p p E, hcard]

private lemma center_le_frattini
    {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    {E Z : Subgroup P} (hP : IsPGroup p P) (hEextra : IsExtraspecial p E)
    (hZ : Z = (Subgroup.center E).map E.subtype) :
    Z ≤ frattini P := by
  subst hZ
  haveI : Fact (IsPGroup p P) := ⟨hP⟩
  haveI : IsExtraspecial p E := hEextra
  have hcommZ : _root_.commutator ↥E = Subgroup.center ↥E :=
    commutator_center_eq (p := p) (E := ↥E)
  have hZeq : (Subgroup.center E).map E.subtype = (_root_.commutator ↥E).map E.subtype := by
    rw [hcommZ]
  have hmap : (_root_.commutator ↥E).map E.subtype = ⁅E, E⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator]
    congr 1 <;> rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hZeq, hmap]
  refine (Subgroup.commutator_mono le_top le_top).trans ?_
  rw [← _root_.commutator_def]
  exact CFSG.commutator_le_frattini_of_isPGroup (p := p) (R := P)

private lemma commutator_mem_center
    {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    {E Z : Subgroup P} (hEextra : IsExtraspecial p E)
    (hZ : Z = (Subgroup.center E).map E.subtype) :
    ∀ x ∈ E, ∀ y ∈ E, ⁅x, y⁆ ∈ Z := by
  subst hZ
  haveI : IsExtraspecial p E := hEextra
  have hcenter : _root_.commutator ↥E ≤ Subgroup.center ↥E :=
    le_of_eq (commutator_center_eq (p := p) (E := ↥E))
  intro x hx y hy
  have hc : ⁅(⟨x, hx⟩ : ↥E), (⟨y, hy⟩ : ↥E)⁆ ∈ Subgroup.center ↥E :=
    hcenter (by
      rw [_root_.commutator_def]
      exact commutator_mem_commutator (H₁ := ⊤) (H₂ := ⊤) (mem_top _) (mem_top _))
  exact Subgroup.mem_map.mpr
    ⟨⁅(⟨x, hx⟩ : ↥E), (⟨y, hy⟩ : ↥E)⁆, hc,
      (map_commutatorElement E.subtype ⟨x, hx⟩ ⟨y, hy⟩).symm⟩

private noncomputable def settingOfLarge
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (hp : 5 ≤ p) (hP : IsPGroup p P)
    (hE : ∀ E : Subgroup P, CFSG.Assembly.IsElemAbelian p E → Nat.card E ≤ p ^ 2)
    (hsmall : ¬ Nat.card (CFSG.omega₁ (G := P) (p := p)) ≤ p ^ 2) :
    Setting p P := by
  classical
  haveI : Fact (IsPGroup p P) := ⟨hP⟩
  have h3 : 3 < p := by omega
  have hrank : CFSG.groupRank P ≤ 2 := groupRank_le_two (P := P) hP hE
  obtain ⟨hEextra, hEcard, hEexp⟩ := omega_extraspecial hp hP hE hsmall
  have hpow : ∀ x ∈ CFSG.omega₁ (G := P) (p := p), x ^ p = 1 :=
    omega_pow_eq_one hEexp
  have hnoncomm : ¬ IsMulCommutative (CFSG.omega₁ (G := P) (p := p)) :=
    omega_noncomm hEextra
  have hchar : (CFSG.omega₁ (G := P) (p := p)).Characteristic :=
    CFSG.omega₁_characteristic P
  let C : Subgroup P := Subgroup.centralizer ((CFSG.omega₁ (G := P) (p := p)) : Set P)
  let Z : Subgroup P := (Subgroup.center (CFSG.omega₁ (G := P) (p := p))).map
    (CFSG.omega₁ (G := P) (p := p)).subtype
  have hCchar : C.Characteristic := by
    haveI : (CFSG.omega₁ (G := P) (p := p)).Characteristic := hchar
    exact Subgroup.characteristic_centralizer
  obtain ⟨hZchar, hZcard, hZleE, hZleC, hEC, hZcentral⟩ :=
    center_facts (C := C) (Z := Z) rfl rfl hchar hEextra
  have hZleΦ : Z ≤ frattini P := center_le_frattini (Z := Z) hP hEextra rfl
  have hderE : ∀ x ∈ CFSG.omega₁ (G := P) (p := p),
      ∀ y ∈ CFSG.omega₁ (G := P) (p := p), ⁅x, y⁆ ∈ Z :=
    commutator_mem_center (Z := Z) hEextra rfl
  exact {
    E := CFSG.omega₁ (G := P) (p := p)
    C := C
    Ceq := rfl
    Z := Z
    Echar := hchar
    Cchar := hCchar
    Eextra := hEextra
    Ecard := hEcard
    Eexp := hEexp
    Epow := hpow
    Zcard := hZcard
    Zchar := hZchar
    ZleE := hZleE
    ZleC := hZleC
    EC := hEC
    Zcentral := hZcentral
    derE := hderE
    Ccyclic := isCyclic_centralizer_omega h3 hrank hsmall
    ZleΦ := hZleΦ
    Enoncomm := hnoncomm
    Ccentral := fun _ hx => hx }


private lemma case_small
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (hp : 5 ≤ p) (hP : IsPGroup p P)
    (hsmall : Nat.card (CFSG.omega₁ (G := P) (p := p)) ≤ p ^ 2) :
    (frattini P).index ≤ p ^ 2 := by
  haveI : Fact (IsPGroup p P) := ⟨hP⟩
  obtain ⟨s, hs, hcl⟩ := blackburn_small hp hP hsmall
  have hsup : Subgroup.closure (s : Set P) ⊔ frattini P = ⊤ := by rw [hcl, top_sup_eq]
  exact (frattini_index_le_pow_card_of_sup_eq_top (p := p) (P := P) hsup).trans
    (Nat.pow_le_pow_right (Fact.out : p.Prime).pos hs)

private lemma case_C_le_frattini_sup
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (S : Setting p P) (hCΦ : S.C ≤ frattini P) (hPEC : S.E ⊔ S.C = ⊤) :
    (frattini P).index ≤ p ^ 2 := by
  refine index_le_sq_of_sup_frattini_eq_top ?_ S.ZleE (S.ZleC.trans hCΦ) S.Ecard S.Zcard
  refine top_unique ?_
  rw [← hPEC]
  exact sup_le_sup_left hCΦ S.E

private lemma case_C_le_frattini_not_sup
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (hp2 : p ≠ 2) (hP : IsPGroup p P) (S : Setting p P)
    (hCΦ : S.C ≤ frattini P) (hne : S.E ⊔ S.C ≠ ⊤) :
    (frattini P).index ≤ p ^ 2 := by
  haveI : Fact (IsPGroup p P) := ⟨hP⟩
  haveI : S.E.Characteristic := S.Echar
  haveI : S.E.Normal := inferInstance
  haveI : IsExtraspecial p S.E := S.Eextra
  obtain ⟨x, hx⟩ : ∃ x : P, x ∉ S.E ⊔ S.C := by
    by_contra h
    push Not at h
    exact hne (top_unique fun y _ => h y)
  have hx' : x ∉ S.E ⊔ Subgroup.centralizer (S.E : Set P) := by
    rwa [S.Ceq] at hx
  obtain ⟨A₁, hA₁E, hA₁card, hA₁Φ⟩ :=
    exists_le_frattini_of_not_mem_sup_centralizer hp2 hP S.E S.Ecard S.Eexp hx'
  have hidxE : (S.E ⊔ S.C).index ≤ p := by
    rw [S.Ceq]
    exact index_sup_centralizer_le_of_extraspecial hp2 hP S.E S.Ecard S.Eexp
  have hsupIndex : (S.E ⊔ frattini P).index ≤ p :=
    (Subgroup.index_antitone (sup_le_sup_left hCΦ S.E)).trans hidxE
  have hA₁rel : A₁.relIndex S.E = p := by
    have h := Subgroup.relIndex_mul_card (H := A₁) (K := S.E)
    rw [inf_of_le_left hA₁E, hA₁card, S.Ecard] at h
    have h' : A₁.relIndex S.E * p ^ 2 = p * p ^ 2 := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_right (pow_pos (Fact.out : p.Prime).pos 2) h'
  have hrel : (frattini P).relIndex (S.E ⊔ frattini P) ≤ p := by
    rw [Subgroup.relIndex_sup_right S.E (frattini P)]
    have hdvd : (frattini P).relIndex S.E ∣ A₁.relIndex S.E :=
      Subgroup.relIndex_dvd_of_le_left (L := S.E) hA₁Φ
    have hdvd' : (frattini P).relIndex S.E ∣ p := by rwa [hA₁rel] at hdvd
    exact Nat.le_of_dvd (Fact.out : p.Prime).pos hdvd'
  exact frattini_index_le_pow_two_of_relIndex_le hsupIndex hrel

private lemma sigma_power_mod
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (hP : IsPGroup p P) {w : ℕ} {σ : P ≃* P}
    (hσ : ∀ x : P, (σ x)⁻¹ * x ^ w ∈ frattini P)
    {c : P} {C : Subgroup P} (hcC : C = Subgroup.zpowers c) (hcΦ : c ∉ frattini P)
    {v : ℕ} (hv : σ c = c ^ v) :
    v ≡ w [MOD p] := by
  haveI : Fact (IsPGroup p P) := ⟨hP⟩
  have hφ : (σ c)⁻¹ * c ^ w ∈ frattini P := hσ c
  rw [hv] at hφ
  have hzpow : c ^ ((w : ℤ) - (v : ℤ)) ∈ frattini P := by
    have h : (c ^ v)⁻¹ * c ^ w = c ^ ((w : ℤ) - (v : ℤ)) := by
      rw [← zpow_natCast c v, ← zpow_natCast c w, ← zpow_neg, ← zpow_add]
      congr 1
      ring
    rwa [h] at hφ
  let q : P →* P ⧸ frattini P := QuotientGroup.mk' (frattini P)
  have ha_pow : (q c) ^ p = 1 := by
    calc (q c) ^ p = q (c ^ p) := (map_pow q c p).symm
      _ = 1 := (QuotientGroup.eq_one_iff (x := c ^ p)).mpr
          (CFSG.pth_power_mem_frattini_of_isPGroup c)
  have ha_zpow : (q c) ^ ((w : ℤ) - (v : ℤ)) = 1 := by
    have h : q (c ^ ((w : ℤ) - (v : ℤ))) = 1 :=
      (QuotientGroup.eq_one_iff (x := c ^ ((w : ℤ) - (v : ℤ)))).mpr hzpow
    simpa using h
  have hord_z : (orderOf (q c) : ℤ) ∣ ((w : ℤ) - (v : ℤ)) :=
    orderOf_dvd_iff_zpow_eq_one.mpr ha_zpow
  have hord_p : orderOf (q c) ∣ p := orderOf_dvd_of_pow_eq_one ha_pow
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hord_p with h1 | hp_eq
  · have hqc : q c = 1 := orderOf_eq_one_iff.mp h1
    exact absurd ((QuotientGroup.eq_one_iff c).mp hqc) hcΦ
  · have hdvd : (p : ℤ) ∣ (w : ℤ) - (v : ℤ) := by simpa [hp_eq] using hord_z
    exact Nat.modEq_of_dvd hdvd

private lemma sigma_apply_eq_pow_of_mem_center
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (S : Setting p P) {w : ℕ} {σ : P ≃* P}
    {c : P} (hcC : S.C = Subgroup.zpowers c)
    {v : ℕ} (hv : σ c = c ^ v) (hvmod : v ≡ w [MOD p])
    {z : P} (hz : z ∈ S.Z) :
    σ z = z ^ w := by
  have hzC : z ∈ S.C := S.ZleC hz
  rw [hcC] at hzC
  obtain ⟨k, hk⟩ := (isOfFinOrder_of_finite c).mem_powers_iff_mem_zpowers.mpr hzC
  have hkz : z = c ^ k := hk.symm
  have hzp : z ^ p = 1 := S.Epow z (S.ZleE hz)
  have hord : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzp
  calc σ z = σ (c ^ k) := by rw [hkz]
    _ = (σ c) ^ k := map_pow σ c k
    _ = (c ^ v) ^ k := by rw [hv]
    _ = c ^ (v * k) := by rw [pow_mul]
    _ = c ^ (k * v) := by rw [Nat.mul_comm]
    _ = (c ^ k) ^ v := by rw [pow_mul]
    _ = z ^ v := by rw [hkz]
    _ = z ^ w := (pow_eq_pow_iff_modEq (x := z)).mpr (Nat.ModEq.of_dvd hord hvmod)


private lemma commutator_le_centralizer_of_sup
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (S : Setting p P) (hPEC : S.E ⊔ S.C = ⊤) :
    _root_.commutator P ≤ S.C := by
  haveI : S.E.Characteristic := S.Echar
  haveI : S.E.Normal := inferInstance
  haveI : S.C.Characteristic := S.Cchar
  haveI : S.C.Normal := inferInstance
  haveI : (S.E ⊔ S.C).Normal := Subgroup.sup_normal S.E S.C
  have hEEZ : ⁅S.E, S.E⁆ ≤ S.Z :=
    Subgroup.commutator_le.mpr fun x hx y hy => S.derE x hx y hy
  have hEC1 : ⁅S.E, S.C⁆ ≤ S.C := by
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    have h1 : ⁅x, y⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp (S.Ccentral hy) x hx)
    rw [h1]
    exact S.C.one_mem
  have hCE1 : ⁅S.C, S.E⁆ ≤ S.C := by
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    have h1 : ⁅x, y⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_centralizer_iff.mp (S.Ccentral hx) y hy).symm
    rw [h1]
    exact S.C.one_mem
  calc _root_.commutator P = ⁅(⊤ : Subgroup P), ⊤⁆ := (_root_.commutator_def (G := P))
    _ = ⁅S.E ⊔ S.C, S.E ⊔ S.C⁆ := by rw [hPEC]
    _ = ⁅S.E, S.E ⊔ S.C⁆ ⊔ ⁅S.C, S.E ⊔ S.C⁆ :=
          Subgroup.commutator_sup_right S.E S.C (S.E ⊔ S.C)
    _ = (⁅S.E, S.E⁆ ⊔ ⁅S.E, S.C⁆) ⊔ (⁅S.C, S.E⁆ ⊔ ⁅S.C, S.C⁆) := by
          rw [Subgroup.commutator_sup_left S.E S.E S.C,
            Subgroup.commutator_sup_left S.C S.E S.C]
    _ ≤ S.C := by
          refine sup_le (sup_le (hEEZ.trans S.ZleC) hEC1)
            (sup_le hCE1 (Subgroup.commutator_le_self S.C))

private lemma frattini_le_centralizer_of_sup
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (hP : IsPGroup p P) (S : Setting p P) (hPEC : S.E ⊔ S.C = ⊤) :
    frattini P ≤ S.C := by
  haveI : Fact (IsPGroup p P) := ⟨hP⟩
  haveI : S.E.Characteristic := S.Echar
  haveI : S.E.Normal := inferInstance
  haveI : S.C.Characteristic := S.Cchar
  refine CFSG.GroupTheory.frattini_le_of_comm_pow hP S.C ?_ ?_
  · intro x y
    exact commutator_le_centralizer_of_sup S hPEC
      (Subgroup.commutator_mem_commutator (H₁ := ⊤) (H₂ := ⊤) (mem_top x) (mem_top y))
  · intro x
    obtain ⟨e, he, cc, hcc, rfl⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := S.E) (t := S.C)).mp
        (by rw [hPEC]; exact Subgroup.mem_top x)
    have hcomm : Commute e cc := Subgroup.mem_centralizer_iff.mp (S.Ccentral hcc) e he
    rw [hcomm.mul_pow, S.Epow e he, one_mul]
    exact S.C.pow_mem hcc p

private lemma sigma_eq_scalar_mul_of_mem
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (S : Setting p P) {w : ℕ} {σ : P ≃* P}
    (hσ : ∀ x : P, (σ x)⁻¹ * x ^ w ∈ frattini P)
    (hΦC : frattini P ≤ S.C) {e : P} (he : e ∈ S.E) :
    ∃ z ∈ S.Z, σ e = e ^ w * z := by
  haveI : S.E.Characteristic := S.Echar
  have hσeE : σ e ∈ S.E := by
    have hmap : S.E.map (σ : P →* P) = S.E :=
      Subgroup.characteristic_iff_map_eq.mp S.Echar σ
    have hmem : σ e ∈ S.E.map (σ : P →* P) :=
      Subgroup.mem_map.mpr ⟨e, he, rfl⟩
    rwa [hmap] at hmem
  have hz : (σ e)⁻¹ * e ^ w ∈ S.Z :=
    le_of_eq S.EC ⟨S.E.mul_mem (S.E.inv_mem hσeE) (S.E.pow_mem he w), hΦC (hσ e)⟩
  refine ⟨((σ e)⁻¹ * e ^ w)⁻¹, S.Z.inv_mem hz, ?_⟩
  have h : ((σ e)⁻¹ * e ^ w)⁻¹ = (e ^ w)⁻¹ * σ e := by group
  rw [h]
  group

private lemma exists_commutator_scalar_eq
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (S : Setting p P) {w : ℕ} {σ : P ≃* P}
    (hσE : ∀ e ∈ S.E, ∃ z ∈ S.Z, σ e = e ^ w * z)
    (hσZ : ∀ z ∈ S.Z, σ z = z ^ w) :
    ∃ e f : ↥S.E, ⁅e, f⁆ ≠ 1 ∧
      ⁅(e : P), (f : P)⁆ ^ (w * w) = ⁅(e : P), (f : P)⁆ ^ w := by
  obtain ⟨e, f, hef⟩ : ∃ e f : ↥S.E, ⁅e, f⁆ ≠ 1 := by
    by_contra h
    push Not at h
    apply S.Enoncomm
    refine ⟨⟨fun a b => ?_⟩⟩
    exact commutatorElement_eq_one_iff_mul_comm.mp (h a b)
  obtain ⟨ze, hzeZ, hze⟩ := hσE (e : P) e.2
  obtain ⟨zf, hzfZ, hzf⟩ := hσE (f : P) f.2
  have hσcomm : σ ⁅(e : P), (f : P)⁆ = ⁅(e : P), (f : P)⁆ ^ (w * w) := by
    rw [map_commutatorElement, hze, hzf]
    exact commutator_pow_mul_pow_of_central (a := ze) (z := zf) S.Zcentral S.derE
      e.2 f.2 (S.ZleE hzeZ) hzfZ (S.Zcentral ze hzeZ f f.2) w w
  have hσZcomm : σ ⁅(e : P), (f : P)⁆ = ⁅(e : P), (f : P)⁆ ^ w :=
    hσZ _ (S.derE (e : P) e.2 (f : P) f.2)
  exact ⟨e, f, hef, by rw [← hσcomm, hσZcomm]⟩

private lemma false_of_scalar_sup
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (hP : IsPGroup p P) (S : Setting p P) {w : ℕ}
    (hw3 : (w : ZMod p) ^ 3 = 1) (hw1 : (w : ZMod p) ≠ 1)
    {σ : P ≃* P} (hσ : ∀ x : P, (σ x)⁻¹ * x ^ w ∈ frattini P)
    (hσZ : ∀ z ∈ S.Z, σ z = z ^ w) (hPEC : S.E ⊔ S.C = ⊤) :
    False := by
  have hΦC : frattini P ≤ S.C := frattini_le_centralizer_of_sup hP S hPEC
  have hσE : ∀ e ∈ S.E, ∃ z ∈ S.Z, σ e = e ^ w * z :=
    fun e he => sigma_eq_scalar_mul_of_mem S hσ hΦC he
  obtain ⟨e, f, hef, hpow_eq⟩ := exists_commutator_scalar_eq S hσE hσZ
  have hzZ : ⁅(e : P), (f : P)⁆ ∈ S.Z := S.derE (e : P) e.2 (f : P) f.2
  have hzE : ⁅(e : P), (f : P)⁆ ∈ S.E := S.ZleE hzZ
  have hzp : ⁅(e : P), (f : P)⁆ ^ p = 1 := S.Epow _ hzE
  have hz_ne : ⁅(e : P), (f : P)⁆ ≠ 1 := by
    intro h1
    apply hef
    apply Subtype.ext
    show S.E.subtype ⁅e, f⁆ = S.E.subtype (1 : ↥S.E)
    rw [map_commutatorElement, map_one]
    exact h1
  have hord : orderOf ⁅(e : P), (f : P)⁆ = p := orderOf_eq_prime hzp hz_ne
  have hmod : w * w ≡ w [MOD p] := by
    have h := (pow_eq_pow_iff_modEq (x := ⁅(e : P), (f : P)⁆)).mp hpow_eq
    simpa [hord] using h
  have hsq : (w : ZMod p) ^ 2 = (w : ZMod p) := by
    have hcast : ((w * w : ℕ) : ZMod p) = (w : ZMod p) :=
      (ZMod.natCast_eq_natCast_iff (w * w) w p).mpr hmod
    simpa [pow_two] using hcast
  have hfac : (w : ZMod p) * ((w : ZMod p) - 1) = 0 := by
    rw [mul_sub, mul_one]
    have hsq' : (w : ZMod p) * (w : ZMod p) = (w : ZMod p) := by
      simpa [pow_two] using hsq
    rw [hsq', sub_self]
  rcases mul_eq_zero.mp hfac with h0 | h1
  · have h3 : (w : ZMod p) ^ 3 = 0 := by rw [h0]; ring
    rw [hw3] at h3
    exact one_ne_zero h3
  · exact hw1 (sub_eq_zero.mp h1)


private lemma exists_A1_of_not_mem_sup
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (hp2 : p ≠ 2) (hP : IsPGroup p P) (S : Setting p P) {x : P}
    (hx : x ∉ S.E ⊔ S.C) :
    ∃ A₁ : Subgroup P, A₁ ≤ S.E ∧ Nat.card A₁ = p ^ 2 ∧ A₁ ≤ frattini P := by
  haveI : S.E.Characteristic := S.Echar
  haveI : S.E.Normal := inferInstance
  haveI : IsExtraspecial p S.E := S.Eextra
  have hx' : x ∉ S.E ⊔ Subgroup.centralizer (S.E : Set P) := by
    rwa [S.Ceq] at hx
  exact exists_le_frattini_of_not_mem_sup_centralizer hp2 hP S.E S.Ecard S.Eexp hx'

private lemma inf_frattini_eq_of_not_le
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (S : Setting p P) (hEΦ : ¬ S.E ≤ frattini P) {A₁ : Subgroup P}
    (hA₁E : A₁ ≤ S.E) (hA₁card : Nat.card A₁ = p ^ 2)
    (hA₁Φ : A₁ ≤ frattini P) :
    S.E ⊓ frattini P = A₁ := by
  have hAnti : A₁ ≤ S.E ⊓ frattini P := le_inf hA₁E hA₁Φ
  have hLE : S.E ⊓ frattini P ≤ A₁ := by
    intro y hy
    have hcarddvd : Nat.card ↥(S.E ⊓ frattini P) ∣ p ^ 3 := by
      rw [← S.Ecard]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp hcarddvd
    have hge : p ^ 2 ≤ Nat.card ↥(S.E ⊓ frattini P) := by
      rw [← hA₁card]
      exact Subgroup.card_le_of_le hAnti
    have hkgt : 2 ≤ k :=
      (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp (by rw [← hk]; exact hge)
    rcases (show k = 2 ∨ k = 3 by omega) with h2 | h3
    · have hcard : Nat.card ↥(S.E ⊓ frattini P) = Nat.card A₁ := by
        rw [hk, h2, hA₁card]
      have hEq : A₁ = S.E ⊓ frattini P :=
        Subgroup.eq_of_le_of_card_ge hAnti (le_of_eq hcard)
      rw [hEq]
      exact hy
    · exfalso
      apply hEΦ
      have htop : S.E ⊓ frattini P = S.E := by
        refine Subgroup.eq_of_le_of_card_ge inf_le_left ?_
        rw [hk, h3, S.Ecard]
      rw [← htop]
      exact inf_le_right
  exact le_antisymm hLE hAnti

private lemma index_sup_centralizer_eq_prime
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (hp2 : p ≠ 2) (hP : IsPGroup p P) (S : Setting p P) {x : P}
    (hx : x ∉ S.E ⊔ S.C) :
    (S.E ⊔ S.C).index = p ∧ frattini P ≤ S.E ⊔ S.C := by
  haveI : S.E.Characteristic := S.Echar
  haveI : S.E.Normal := inferInstance
  haveI : IsExtraspecial p S.E := S.Eextra
  have hidxE : (S.E ⊔ S.C).index ≤ p := by
    rw [S.Ceq]
    exact index_sup_centralizer_le_of_extraspecial hp2 hP S.E S.Ecard S.Eexp
  have hidxK : (S.E ⊔ S.C).index = p :=
    index_eq_prime_of_le_prime hP hidxE (by
      intro h1
      exact hx (by rw [Subgroup.index_eq_one.mp h1]; exact Subgroup.mem_top x))
  have hKmax : IsCoatom (S.E ⊔ S.C) :=
    Subgroup.isCoatom_of_index_prime (by rw [hidxK]; exact Fact.out)
  exact ⟨hidxK, frattini_le_coatom hKmax⟩

private lemma isExtraspecialPGroup_of_setting
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (hP : IsPGroup p P) (S : Setting p P) :
    CFSG.IsExtraspecialPGroup p S.E := by
  haveI : IsExtraspecial p S.E := S.Eextra
  have hcomm := commutator_center_eq (p := p) (E := ↥S.E)
  have hexp : ∀ y : ↥S.E, y ^ p = 1 := fun y => Subtype.ext (S.Epow y y.2)
  exact ⟨hP.to_subgroup S.E, hcomm,
    (CFSG.GH74.GLS.Stage2.Bender.Thm1.frattini_eq_commutator_of_exp
      (Fact.out : p.Prime) (hP.to_subgroup S.E) hexp).trans hcomm,
    IsExtraspecial.center_order_p p ↥S.E⟩

private lemma exists_commutator_not_mem_center
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (hP : IsPGroup p P) (S : Setting p P) {x : P} (hx : x ∉ S.E ⊔ S.C) :
    ∃ u ∈ S.E, ⁅u, x⁆ ∉ S.Z := by
  haveI : S.E.Characteristic := S.Echar
  haveI : S.E.Normal := inferInstance
  have hEextraPG : CFSG.IsExtraspecialPGroup p S.E := isExtraspecialPGroup_of_setting hP S
  have hEC' : S.E ⊓ Subgroup.centralizer (S.E : Set P) = S.Z := by
    rw [← S.Ceq]
    exact S.EC
  have hinner : (∀ y ∈ S.E, ⁅y⁻¹, x⁆ ∈ S.Z) → x ∈ S.E ⊔ S.C := by
    intro htriv
    have hQg : ∀ y ∈ S.E, ⁅y⁻¹, x⁆ ∈ CFSG.GH74.GLS.Bg.zOf S.E := by
      intro y hy
      change ⁅y⁻¹, x⁆ ∈ S.E ⊓ Subgroup.centralizer (S.E : Set P)
      rw [hEC']
      exact htriv y hy
    have hxN : x ∈ Subgroup.normalizer (S.E : Set P) := by
      rw [Subgroup.normalizer_eq_top (H := S.E)]
      exact Subgroup.mem_top x
    obtain ⟨u, huE, hux⟩ :=
      CFSG.GH74.GLS.Stage2.Bender.Thm1.exists_inner_of_extraspecial_gen
        (Fact.out : p.Prime) hEextraPG S.Epow hxN hQg
    have hx' : x = u * (u⁻¹ * x) := by group
    have huxC : u⁻¹ * x ∈ S.C := by rwa [S.Ceq]
    rw [hx']
    exact Subgroup.mul_mem_sup huE huxC
  by_contra h
  push Not at h
  exact hx (hinner fun y hy => h y⁻¹ (S.E.inv_mem hy))


private lemma sigma_eq_scalar_mul_of_mem_A
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (S : Setting p P) {w : ℕ} {σ : P ≃* P}
    (hσ : ∀ x : P, (σ x)⁻¹ * x ^ w ∈ frattini P)
    {A₁ : Subgroup P} (hA₁E : A₁ ≤ S.E) (hA₁Φ : A₁ ≤ frattini P)
    (hEΦeq : S.E ⊓ frattini P = A₁) {e : P} (he : e ∈ S.E) :
    ∃ z ∈ A₁, σ e = e ^ w * z := by
  haveI : S.E.Characteristic := S.Echar
  have hσeE : σ e ∈ S.E := by
    have hmap : S.E.map (σ : P →* P) = S.E :=
      Subgroup.characteristic_iff_map_eq.mp S.Echar σ
    have hmem : σ e ∈ S.E.map (σ : P →* P) := Subgroup.mem_map.mpr ⟨e, he, rfl⟩
    rwa [hmap] at hmem
  have hz : (σ e)⁻¹ * e ^ w ∈ A₁ := by
    rw [← hEΦeq]
    exact ⟨S.E.mul_mem (S.E.inv_mem hσeE) (S.E.pow_mem he w), hσ e⟩
  refine ⟨((σ e)⁻¹ * e ^ w)⁻¹, A₁.inv_mem hz, ?_⟩
  have h : ((σ e)⁻¹ * e ^ w)⁻¹ = (e ^ w)⁻¹ * σ e := by group
  rw [h]
  group

private lemma sigma_eq_scalar_mul_of_mem_Phi
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (S : Setting p P) {w : ℕ} {σ : P ≃* P}
    (hσ : ∀ x : P, (σ x)⁻¹ * x ^ w ∈ frattini P)
    {x : P} (hΦK : frattini P ≤ S.E ⊔ S.C) :
    ∃ y ∈ S.E ⊔ S.C, σ x = x ^ w * y := by
  refine ⟨((σ x)⁻¹ * x ^ w)⁻¹, hΦK ((frattini P).inv_mem (hσ x)), ?_⟩
  have h : ((σ x)⁻¹ * x ^ w)⁻¹ = (x ^ w)⁻¹ * σ x := by group
  rw [h]
  group

private lemma quotient_sigma_commutator_eq
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (S : Setting p P) [S.Z.Normal] {w : ℕ} {σ : P ≃* P} {x u a a₁ y : P}
    (ha : a = ⁅u, x⁆) (hσu : σ u = u ^ w * a₁) (hσx : σ x = x ^ w * y)
    (ha₁x : Commute ((QuotientGroup.mk' S.Z) a₁) ((QuotientGroup.mk' S.Z) x))
    (ha₁y : Commute ((QuotientGroup.mk' S.Z) a₁) ((QuotientGroup.mk' S.Z) y))
    (hu_a : Commute ((QuotientGroup.mk' S.Z) u) ((QuotientGroup.mk' S.Z) a))
    (hx_a : Commute ((QuotientGroup.mk' S.Z) x) ((QuotientGroup.mk' S.Z) a))
    (hu_y : Commute ((QuotientGroup.mk' S.Z) u) ((QuotientGroup.mk' S.Z) y)) :
    (QuotientGroup.mk' S.Z) (σ a) = (QuotientGroup.mk' S.Z) (a ^ (w * w)) := by
  let q : P →* P ⧸ S.Z := QuotientGroup.mk' S.Z
  have haeq : q a = ⁅q u, q x⁆ := by rw [ha, map_commutatorElement]
  have hu_a' : Commute (q u) ⁅q u, q x⁆ := haeq ▸ hu_a
  have hx_a' : Commute (q x) ⁅q u, q x⁆ := haeq ▸ hx_a
  have hleft : ⁅q a₁, (q x) ^ w * q y⁆ = 1 := by
    have h1 : Commute (q a₁) ((q x) ^ w) := ha₁x.pow_right w
    have h2 : Commute (q a₁) (q y) := ha₁y
    exact (h1.mul_right h2).commutator_eq
  have hright : ⁅(q u) ^ w, q y⁆ = 1 := hu_y.pow_left w |>.commutator_eq
  have hstep1 : ⁅q (σ u), q (σ x)⁆ = ⁅(q u) ^ w, (q x) ^ w⁆ := by
    rw [hσu, hσx, map_mul, map_pow, map_mul, map_pow]
    calc ⁅(q u) ^ w * q a₁, (q x) ^ w * q y⁆
        = (q u) ^ w * ⁅q a₁, (q x) ^ w * q y⁆ * ((q u) ^ w)⁻¹ *
            ⁅(q u) ^ w, (q x) ^ w * q y⁆ := by
            rw [commutatorElement_mul_left_eq_conj_mul]
      _ = ⁅(q u) ^ w, (q x) ^ w * q y⁆ := by rw [hleft]; group
      _ = ⁅(q u) ^ w, (q x) ^ w⁆ * (q x) ^ w * ⁅(q u) ^ w, q y⁆ *
            ((q x) ^ w)⁻¹ := by
            rw [commutatorElement_mul_right_eq_mul_conj]
      _ = ⁅(q u) ^ w, (q x) ^ w⁆ := by rw [hright]; group
  have hstep2 : ⁅(q u) ^ w, (q x) ^ w⁆ = ⁅q u, q x⁆ ^ (w * w) := by
    have hu' : Commute (q u) ⁅q u, (q x) ^ w⁆ := by
      rw [← Commute.commutatorElement_pow_right hx_a' w]
      exact hu_a'.pow_right w
    calc ⁅(q u) ^ w, (q x) ^ w⁆ = ⁅q u, (q x) ^ w⁆ ^ w :=
          (Commute.commutatorElement_pow_left hu' w).symm
      _ = (⁅q u, q x⁆ ^ w) ^ w := by
          rw [Commute.commutatorElement_pow_right hx_a' w]
      _ = ⁅q u, q x⁆ ^ (w * w) := by rw [pow_mul]
  have h1 : σ a = ⁅σ u, σ x⁆ := by rw [ha, map_commutatorElement]
  rw [h1, map_commutatorElement q (σ u) (σ x), hstep1, hstep2, map_pow, haeq]

private lemma exists_z_of_quotient_eq
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (S : Setting p P) [S.Z.Normal] {a : P} {w : ℕ} {σ : P ≃* P}
    (hq : (QuotientGroup.mk' S.Z) (σ a) = (QuotientGroup.mk' S.Z) (a ^ (w * w)))
    (haE : a ∈ S.E) :
    ∃ z ∈ S.Z, σ a = a ^ (w * w) * z := by
  set z : P := σ a * (a ^ (w * w))⁻¹ with hz_def
  have hzker : (QuotientGroup.mk' S.Z) z = 1 := by
    rw [hz_def, map_mul, map_inv, hq, mul_inv_cancel]
  have hzZ : z ∈ S.Z := (QuotientGroup.eq_one_iff (x := z)).mp hzker
  refine ⟨z, hzZ, ?_⟩
  calc σ a = z * (a ^ (w * w)) := by rw [hz_def]; group
    _ = (a ^ (w * w)) * z := S.Zcentral z hzZ _ (S.E.pow_mem haE (w * w))


private lemma quotient_comm_of_mem_E
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (S : Setting p P) [S.Z.Normal] {e f : P} (he : e ∈ S.E) (hf : f ∈ S.E) :
    Commute ((QuotientGroup.mk' S.Z) e) ((QuotientGroup.mk' S.Z) f) := by
  have hz : ⁅e, f⁆ ∈ S.Z := S.derE e he f hf
  have hq1 : ⁅(QuotientGroup.mk' S.Z) e, (QuotientGroup.mk' S.Z) f⁆ = 1 := by
    rw [← map_commutatorElement (QuotientGroup.mk' S.Z) e f]
    exact (QuotientGroup.eq_one_iff (x := ⁅e, f⁆)).mpr hz
  exact commutatorElement_eq_one_iff_commute.mp hq1

private lemma quotient_comm_of_mem_A
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (hP : IsPGroup p P) (S : Setting p P) [S.Z.Normal]
    {A₁ : Subgroup P} (hA₁Z : S.Z ≤ A₁) (hA₁card : Nat.card A₁ = p ^ 2)
    (hA₁normal : A₁.Normal) {α x : P} (hα : α ∈ A₁) :
    Commute ((QuotientGroup.mk' S.Z) α) ((QuotientGroup.mk' S.Z) x) := by
  have hz : ⁅α, x⁆ ∈ S.Z :=
    commutator_mem_of_mem_of_card_eq_prime_sq hP hA₁Z hA₁card S.Zcard
      hA₁normal S.Zchar hα
  have hq1 : ⁅(QuotientGroup.mk' S.Z) α, (QuotientGroup.mk' S.Z) x⁆ = 1 := by
    rw [← map_commutatorElement (QuotientGroup.mk' S.Z) α x]
    exact (QuotientGroup.eq_one_iff (x := ⁅α, x⁆)).mpr hz
  exact commutatorElement_eq_one_iff_commute.mp hq1

private lemma quotient_comm_of_mem_sup
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (S : Setting p P) [S.Z.Normal] {e y : P} (he : e ∈ S.E)
    (hy : y ∈ S.E ⊔ S.C) :
    Commute ((QuotientGroup.mk' S.Z) e) ((QuotientGroup.mk' S.Z) y) := by
  haveI : S.E.Characteristic := S.Echar
  have hz : ⁅e, y⁆ ∈ S.Z :=
    commutator_mem_of_mem_sup_centralizer S.Ccentral S.derE
      (by infer_instance) he hy
  have hq1 : ⁅(QuotientGroup.mk' S.Z) e, (QuotientGroup.mk' S.Z) y⁆ = 1 := by
    rw [← map_commutatorElement (QuotientGroup.mk' S.Z) e y]
    exact (QuotientGroup.eq_one_iff (x := ⁅e, y⁆)).mpr hz
  exact commutatorElement_eq_one_iff_commute.mp hq1

private lemma commutator_u_a_ne_one
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (S : Setting p P) {A₁ : Subgroup P} {u a : P}
    (hA₁E : A₁ ≤ S.E) (hA₁card : Nat.card A₁ = p ^ 2)
    (huE : u ∈ S.E) (haA : a ∈ A₁) (haE : a ∈ S.E)
    (huA : u ∉ A₁) (haZ : a ∉ S.Z)
    (hE_eq : S.E = Subgroup.zpowers u ⊔ A₁) :
    ⁅u, a⁆ ≠ 1 := by
  haveI : IsMulCommutative ↥A₁ := IsPGroup.isMulCommutative_of_card_eq_prime_sq hA₁card
  intro h1
  have hua_comm : Commute u a := commutatorElement_eq_one_iff_commute.mp h1
  have hcent : S.E ≤ Subgroup.centralizer ({a} : Set P) := by
    rw [hE_eq]
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hua_comm.eq
    · intro α hα
      exact Subgroup.mem_centralizer_singleton_iff.mpr (by
        have h := (IsMulCommutative.is_comm (M := ↥A₁)).comm ⟨α, hα⟩ ⟨a, haA⟩
        exact congrArg Subtype.val h)
  have haC : a ∈ S.C := by
    rw [S.Ceq]
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcent hy)
  exact haZ (by rw [← S.EC]; exact ⟨haE, haC⟩)

private lemma false_of_sigma_commutator
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (S : Setting p P) {u a a₁ z : P} {w : ℕ} {σ : P ≃* P}
    (huE : u ∈ S.E) (haE : a ∈ S.E) (ha₁E : a₁ ∈ S.E) (hzZ : z ∈ S.Z)
    (hac : a₁ * a = a * a₁) (hσu_eq : σ u = u ^ w * a₁)
    (hσa_eq : σ a = a ^ (w * w) * z)
    (hσZ : ∀ y ∈ S.Z, σ y = y ^ w) (hcomm_ua : ⁅u, a⁆ ≠ 1)
    (hw3 : (w : ZMod p) ^ 3 = 1) (hw1 : (w : ZMod p) ≠ 1) :
    False := by
  have hcomp : σ ⁅u, a⁆ = ⁅u, a⁆ ^ (w * (w * w)) := by
    rw [map_commutatorElement, hσu_eq, hσa_eq]
    exact commutator_pow_mul_pow_of_central (a := a₁) (z := z) S.Zcentral S.derE
      huE haE ha₁E hzZ hac w (w * w)
  have hσZua : σ ⁅u, a⁆ = ⁅u, a⁆ ^ w := hσZ _ (S.derE u huE a haE)
  have hw3mod : w * (w * w) ≡ 1 [MOD p] := by
    have hcast : ((w * (w * w) : ℕ) : ZMod p) = ((1 : ℕ) : ZMod p) := by
      have h : ((w * (w * w) : ℕ) : ZMod p) = (w : ZMod p) ^ 3 := by
        push_cast
        ring
      rw [h, hw3]
      norm_num
    exact (ZMod.natCast_eq_natCast_iff (w * (w * w)) 1 p).mp hcast
  have hua_order : orderOf ⁅u, a⁆ = p :=
    orderOf_eq_prime (S.Epow _ (S.ZleE (S.derE u huE a haE))) hcomm_ua
  have hpow_one : ⁅u, a⁆ ^ (w * (w * w)) = ⁅u, a⁆ := by
    have hmod : w * (w * w) ≡ 1 [MOD orderOf ⁅u, a⁆] := by rwa [hua_order]
    simpa using (pow_eq_pow_iff_modEq (x := ⁅u, a⁆)).mpr hmod
  have hsigma_one : σ ⁅u, a⁆ = ⁅u, a⁆ := by rw [hcomp, hpow_one]
  have hw1mod : w ≡ 1 [MOD p] := by
    have htmp : ⁅u, a⁆ ^ w = ⁅u, a⁆ ^ 1 := by
      simpa using hσZua.symm.trans hsigma_one
    have h := (pow_eq_pow_iff_modEq (x := ⁅u, a⁆)).mp htmp
    simpa [hua_order] using h
  exact hw1 (by simpa using (ZMod.natCast_eq_natCast_iff w 1 p).mpr hw1mod)



private structure B3Data
    (p : ℕ) [Fact p.Prime] (P : Type*) [Group P] [Finite P]
    (S : Setting p P) (x : P) where
  A₁ : Subgroup P
  u : P
  a : P
  A₁E : A₁ ≤ S.E
  A₁card : Nat.card A₁ = p ^ 2
  A₁Φ : A₁ ≤ frattini P
  EΦeq : S.E ⊓ frattini P = A₁
  A₁Z : S.Z ≤ A₁
  A₁normal : A₁.Normal
  uE : u ∈ S.E
  aE : a ∈ S.E
  aA : a ∈ A₁
  uA : u ∉ A₁
  aZ : a ∉ S.Z
  E_eq : S.E = Subgroup.zpowers u ⊔ A₁
  a_def : a = ⁅u, x⁆

private lemma exists_A1_data
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (hp2 : p ≠ 2) (hP : IsPGroup p P) (S : Setting p P) {x : P}
    (hx : x ∉ S.E ⊔ S.C) (hEΦ : ¬ S.E ≤ frattini P) :
    ∃ A₁ : Subgroup P, A₁ ≤ S.E ∧ Nat.card A₁ = p ^ 2 ∧ A₁ ≤ frattini P ∧
      S.E ⊓ frattini P = A₁ ∧ S.Z ≤ A₁ ∧ A₁.Normal := by
  haveI : S.E.Characteristic := S.Echar
  haveI : S.E.Normal := inferInstance
  obtain ⟨A₁, hA₁E, hA₁card, hA₁Φ⟩ := exists_A1_of_not_mem_sup hp2 hP S hx
  have hEΦeq : S.E ⊓ frattini P = A₁ :=
    inf_frattini_eq_of_not_le S hEΦ hA₁E hA₁card hA₁Φ
  have hA₁normal : A₁.Normal := by
    rw [← hEΦeq]
    infer_instance
  have hA₁Z : S.Z ≤ A₁ := by
    rw [← hEΦeq]
    exact le_inf S.ZleE S.ZleΦ
  exact ⟨A₁, hA₁E, hA₁card, hA₁Φ, hEΦeq, hA₁Z, hA₁normal⟩

private lemma exists_u_a_data
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (hP : IsPGroup p P) (S : Setting p P) {x : P} (hx : x ∉ S.E ⊔ S.C)
    {A₁ : Subgroup P} (hA₁E : A₁ ≤ S.E) (hA₁card : Nat.card A₁ = p ^ 2)
    (hA₁Φ : A₁ ≤ frattini P) (hEΦeq : S.E ⊓ frattini P = A₁)
    (hA₁Z : S.Z ≤ A₁) (hA₁normal : A₁.Normal) :
    ∃ u a : P, u ∈ S.E ∧ a ∈ S.E ∧ a ∈ A₁ ∧ u ∉ A₁ ∧ a ∉ S.Z ∧
      S.E = Subgroup.zpowers u ⊔ A₁ ∧ a = ⁅u, x⁆ := by
  haveI : Fact (IsPGroup p P) := ⟨hP⟩
  haveI : S.E.Characteristic := S.Echar
  haveI : S.E.Normal := inferInstance
  have hAtriv : ∀ α ∈ A₁, ∀ g : P, ⁅α, g⁆ ∈ S.Z :=
    fun α hα g => commutator_mem_of_mem_of_card_eq_prime_sq hP hA₁Z hA₁card S.Zcard
      hA₁normal S.Zchar hα
  obtain ⟨u, huE, huZ⟩ := exists_commutator_not_mem_center hP S hx
  set a : P := ⁅u, x⁆ with ha_def
  have haE : a ∈ S.E := by
    have hxu : x * u⁻¹ * x⁻¹ ∈ S.E := (inferInstance : S.E.Normal).conj_mem u⁻¹
      (S.E.inv_mem huE) x
    have hform : ⁅u, x⁆ = u * (x * u⁻¹ * x⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [ha_def, hform]
    exact S.E.mul_mem huE hxu
  have haΦ : a ∈ frattini P := by
    rw [ha_def]
    exact CFSG.commutator_le_frattini_of_isPGroup (p := p) (R := P)
      (Subgroup.commutator_mem_commutator (H₁ := ⊤) (H₂ := ⊤) (mem_top u) (mem_top x))
  have haA : a ∈ A₁ := by
    rw [← hEΦeq]
    exact ⟨haE, haΦ⟩
  have huA : u ∉ A₁ := by
    intro huA
    exact huZ (by rw [ha_def]; exact hAtriv u huA x)
  have hE_eq : S.E = Subgroup.zpowers u ⊔ A₁ :=
    (zpowers_sup_eq_of_card hA₁E hA₁card S.Ecard huE huA).symm
  exact ⟨u, a, huE, haE, haA, huA, huZ, hE_eq, ha_def⟩

private lemma exists_B3Data
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (hp2 : p ≠ 2) (hP : IsPGroup p P) (S : Setting p P) {x : P}
    (hx : x ∉ S.E ⊔ S.C) (hEΦ : ¬ S.E ≤ frattini P) :
    Nonempty (B3Data p P S x) := by
  obtain ⟨A₁, hA₁E, hA₁card, hA₁Φ, hEΦeq, hA₁Z, hA₁normal⟩ :=
    exists_A1_data hp2 hP S hx hEΦ
  obtain ⟨u, a, huE, haE, haA, huA, haZ, hE_eq, ha_def⟩ :=
    exists_u_a_data hP S hx hA₁E hA₁card hA₁Φ hEΦeq hA₁Z hA₁normal
  exact ⟨{
    A₁ := A₁
    u := u
    a := a
    A₁E := hA₁E
    A₁card := hA₁card
    A₁Φ := hA₁Φ
    EΦeq := hEΦeq
    A₁Z := hA₁Z
    A₁normal := hA₁normal
    uE := huE
    aE := haE
    aA := haA
    uA := huA
    aZ := haZ
    E_eq := hE_eq
    a_def := ha_def }⟩

private lemma false_of_scalar_not_mem_sup
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (hp2 : p ≠ 2) (hP : IsPGroup p P) (S : Setting p P) {x : P}
    (hx : x ∉ S.E ⊔ S.C) (hEΦ : ¬ S.E ≤ frattini P) {w : ℕ}
    (hw3 : (w : ZMod p) ^ 3 = 1) (hw1 : (w : ZMod p) ≠ 1)
    {σ : P ≃* P} (hσ : ∀ y : P, (σ y)⁻¹ * y ^ w ∈ frattini P)
    (hσZ : ∀ y ∈ S.Z, σ y = y ^ w) :
    False := by
  classical
  haveI : Fact (IsPGroup p P) := ⟨hP⟩
  haveI hEc : S.E.Characteristic := S.Echar
  haveI hEn : S.E.Normal := inferInstance
  haveI hZc : S.Z.Characteristic := S.Zchar
  haveI hZn : S.Z.Normal := inferInstance
  let D : B3Data p P S x := Classical.choice (exists_B3Data hp2 hP S hx hEΦ)
  haveI hA₁comm : IsMulCommutative ↥D.A₁ :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq D.A₁card
  obtain ⟨a₁, ha₁, hσu_eq⟩ :=
    sigma_eq_scalar_mul_of_mem_A S hσ D.A₁E D.A₁Φ D.EΦeq D.uE
  have hΦK : frattini P ≤ S.E ⊔ S.C := (index_sup_centralizer_eq_prime hp2 hP S hx).2
  obtain ⟨y, hyK, hσx_eq⟩ := sigma_eq_scalar_mul_of_mem_Phi S hσ hΦK
  have ha₁x : Commute ((QuotientGroup.mk' S.Z) a₁) ((QuotientGroup.mk' S.Z) x) :=
    quotient_comm_of_mem_A hP S D.A₁Z D.A₁card D.A₁normal ha₁
  have ha₁y : Commute ((QuotientGroup.mk' S.Z) a₁) ((QuotientGroup.mk' S.Z) y) :=
    quotient_comm_of_mem_sup S (D.A₁E ha₁) hyK
  have hu_a : Commute ((QuotientGroup.mk' S.Z) D.u) ((QuotientGroup.mk' S.Z) D.a) :=
    quotient_comm_of_mem_E S D.uE D.aE
  have hx_a : Commute ((QuotientGroup.mk' S.Z) x) ((QuotientGroup.mk' S.Z) D.a) :=
    (quotient_comm_of_mem_A hP S D.A₁Z D.A₁card D.A₁normal D.aA).symm
  have hu_y : Commute ((QuotientGroup.mk' S.Z) D.u) ((QuotientGroup.mk' S.Z) y) :=
    quotient_comm_of_mem_sup S D.uE hyK
  have hq := quotient_sigma_commutator_eq S D.a_def hσu_eq hσx_eq ha₁x ha₁y hu_a hx_a hu_y
  obtain ⟨z, hzZ, hσa_eq⟩ := exists_z_of_quotient_eq S hq D.aE
  have hcomm_ua : ⁅D.u, D.a⁆ ≠ 1 :=
    commutator_u_a_ne_one S D.A₁E D.A₁card D.uE D.aA D.aE D.uA D.aZ D.E_eq
  have hac : a₁ * D.a = D.a * a₁ := by
    have h := (IsMulCommutative.is_comm (M := ↥D.A₁)).comm ⟨a₁, ha₁⟩ ⟨D.a, D.aA⟩
    exact congrArg Subtype.val h
  exact false_of_sigma_commutator S D.uE D.aE (D.A₁E ha₁) hzZ hac hσu_eq hσa_eq hσZ
    hcomm_ua hw3 hw1

private lemma case_E_le_frattini_of_not_sup
    {p : ℕ} [Fact p.Prime] {P : Type} [Group P] [Finite P]
    (hp2 : p ≠ 2) (hP : IsPGroup p P) (S : Setting p P) {x : P}
    (hx : x ∉ S.E ⊔ S.C) (hEΦ : S.E ≤ frattini P)
    {c : P} (hcC : S.C = Subgroup.zpowers c) :
    (frattini P).index ≤ p ^ 2 := by
  haveI : Fact (IsPGroup p P) := ⟨hP⟩
  haveI : S.C.Characteristic := S.Cchar
  have hidxK : (S.E ⊔ S.C).index = p := (index_sup_centralizer_eq_prime hp2 hP S hx).1
  have hsupIndex : (S.C ⊔ frattini P).index ≤ p := by
    refine (Subgroup.index_antitone ?_).trans (le_of_eq hidxK)
    exact sup_le (hEΦ.trans le_sup_right) le_sup_left
  have hrel : (frattini P).relIndex (S.C ⊔ frattini P) ≤ p := by
    rw [Subgroup.relIndex_sup_right S.C (frattini P), hcC]
    exact Nat.le_of_dvd (Fact.out : p.Prime).pos
      (CFSG.GroupTheory.relIndex_zpowers_dvd (frattini P) c
        (CFSG.pth_power_mem_frattini_of_isPGroup c))
  exact frattini_index_le_pow_two_of_relIndex_le hsupIndex hrel

theorem blackburnScalarAut_holds : CFSG.RankThree.PartTwo.KFacts.BlackburnScalarAut := by
  intro p _ hp P _ _ hP hE w hw3 hw1 σ hσ
  classical
  haveI : Fact (IsPGroup p P) := ⟨hP⟩
  have hp2 : p ≠ 2 := by omega
  by_cases hsmall : Nat.card (CFSG.omega₁ (G := P) (p := p)) ≤ p ^ 2
  · exact case_small hp hP hsmall
  · let S : Setting p P := settingOfLarge hp hP hE hsmall
    by_cases hCΦ : S.C ≤ frattini P
    · by_cases hPEC : S.E ⊔ S.C = ⊤
      · exact case_C_le_frattini_sup S hCΦ hPEC
      · exact case_C_le_frattini_not_sup hp2 hP S hCΦ hPEC
    · obtain ⟨c, hcC⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top S.C).mp S.Ccyclic
      have hcC' : S.C = Subgroup.zpowers c := hcC.symm
      have hcΦ : c ∉ frattini P := by
        intro hc
        exact hCΦ (by rw [hcC']; exact Subgroup.zpowers_le.mpr hc)
      have hσcC : σ c ∈ S.C := by
        have hmap : S.C.map (σ : P →* P) = S.C :=
          Subgroup.characteristic_iff_map_eq.mp S.Cchar σ
        have hmem : σ c ∈ S.C.map (σ : P →* P) :=
          Subgroup.mem_map.mpr ⟨c, by rw [hcC']; exact Subgroup.mem_zpowers c, rfl⟩
        rwa [hmap] at hmem
      obtain ⟨v, hv⟩ :=
        (isOfFinOrder_of_finite c).mem_powers_iff_mem_zpowers.mpr (by rwa [hcC'] at hσcC)
      have hv' : σ c = c ^ v := hv.symm
      have hvmod : v ≡ w [MOD p] := sigma_power_mod hP hσ hcC' hcΦ hv'
      have hσZ : ∀ z ∈ S.Z, σ z = z ^ w :=
        fun z hz => sigma_apply_eq_pow_of_mem_center S hcC' hv' hvmod hz
      by_cases hPEC : S.E ⊔ S.C = ⊤
      · exact (false_of_scalar_sup hP S hw3 hw1 hσ hσZ hPEC).elim
      · obtain ⟨x, hx⟩ : ∃ x : P, x ∉ S.E ⊔ S.C := by
          by_contra h
          push Not at h
          exact hPEC (top_unique fun y _ => h y)
        by_cases hEΦ : S.E ≤ frattini P
        · exact case_E_le_frattini_of_not_sup hp2 hP S hx hEΦ hcC'
        · exact (false_of_scalar_not_mem_sup hp2 hP S hx hEΦ hw3 hw1 hσ hσZ).elim

end CFSG.RankThree.PartTwo.Sec16.Kcd166

