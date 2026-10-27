module

import CFSG.RankThree.PartOne.S9.Planes.Basic
import CFSG.RankThree.PGroups.MaximalNormalElementaryCentralizer
import CFSG.GroupTheory.SteinbergBKOddNoncyclicRankTwo
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.RankThree.PartOne.Planes

open Subgroup
open scoped commutatorElement

theorem exists_normal_plane {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Type*} [Group Q]
    [Finite Q] (hQ : IsPGroup p Q) (hnc : ¬ IsCyclic Q) :
    ∃ U V : Subgroup Q, U ≤ V ∧ Nat.card U = p ∧ U ≤ center Q ∧ IsElementaryAbelian p V ∧
      Nat.card V = p ^ 2 ∧ V.Normal ∧ ∀ v ∈ V, ∀ g : Q, ⁅v, g⁆ ∈ U := by
  have hpF : Fact p.Prime := ⟨hp⟩
  let S : Set (Subgroup Q) := {B | B.Normal ∧ IsElementaryAbelian p B}
  have hbot : (⊥ : Subgroup Q) ∈ S := ⟨inferInstance, (isElementaryAbelian_iff p _).2
    ⟨fun x hx y hy => by rw [mem_bot.1 hx, mem_bot.1 hy], fun x hx => by
      rw [mem_bot.1 hx, one_pow]⟩⟩
  obtain ⟨E, hEmax⟩ := S.toFinite.exists_maximal ⟨⊥, hbot⟩
  obtain ⟨hEn, hEe⟩ := hEmax.prop
  have hmax : ∀ B : Subgroup Q, B.Normal → IsElementaryAbelian p B → E ≤ B → B = E :=
    fun B hBn hBe hEB => le_antisymm (hEmax.2 ⟨hBn, hBe⟩ hEB) hEB
  have htors := (CFSG.RankThree.PGroups.maximal_normal_elementary_centralizer_torsion hp hp2 hQ
    (E := E) hEe hmax).2
  have hcardE : p ^ 2 ≤ Nat.card E := by
    by_contra hlt
    push Not at hlt
    have hEc : E ≤ center Q := by
      obtain ⟨k, hk⟩ := (IsElementaryAbelian.isPGroup p E).exists_card_eq
      have hk2 : k < 2 := by
        rw [hk] at hlt
        exact (Nat.pow_lt_pow_iff_right hp.one_lt).1 hlt
      by_cases hE0 : E = ⊥
      · rw [hE0]
        exact bot_le
      · have h1 := (CFSG.SectionRank.Ccomm.normal_inf_center_card hQ hE0).2
        have h2 : Nat.card E ≤ p := by
          calc Nat.card E = p ^ k := hk
            _ ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
            _ = p := pow_one p
        exact inf_eq_left.1 (Subgroup.eq_of_le_of_card_ge (inf_le_left : E ⊓ center Q ≤ E)
          (h2.trans h1))
    have hall : ∀ x : Q, x ^ p = 1 → x ∈ E := fun x hx =>
      htors x (mem_centralizer_iff.2 fun h hh => (mem_center_iff.1 (hEc hh) x).symm) hx
    obtain ⟨B, hBe, hBc⟩ := CFSG.GroupTheory.SteinbergBK.odd_noncyclic_pgroup_rank_two
      (p := p) (hp.odd_of_ne_two hp2) hQ hnc
    have hBE : B ≤ E := fun x hx => hall x (((isElementaryAbelian_iff p B).1 hBe).2 x hx)
    have := Subgroup.card_le_of_le hBE
    omega
  have hE0 : E ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hcardE
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  have hpdvd := (CFSG.SectionRank.Ccomm.normal_inf_center_card hQ hE0).1
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := (E ⊓ center Q : Subgroup Q)) p hpdvd
  have hzE : (y : Q) ∈ E := y.2.1
  have hzZ : (y : Q) ∈ center Q := y.2.2
  have hzord : orderOf (y : Q) = p := by rw [Subgroup.orderOf_coe]; exact hy
  have hUcard : Nat.card (zpowers (y : Q)) = p := by rw [Nat.card_zpowers, hzord]
  have hUle : zpowers (y : Q) ≤ center Q := zpowers_le.2 hzZ
  have hUE : zpowers (y : Q) ≤ E := zpowers_le.2 hzE
  have hUn : (zpowers (y : Q)).Normal := normal_of_le_center hUle
  have hUlt : zpowers (y : Q) < E := by
    refine lt_of_le_of_ne hUE ?_
    intro h
    rw [h] at hUcard
    have : p < p ^ 2 := by nlinarith [hp.one_lt]
    omega
  obtain ⟨b, hbE, hbU, -, B, hBn, hUB, hBE, hbB, hform, hcomm⟩ :=
    CFSG.SectionRank.Ccomm.exists_central_extension hQ hUlt
  have hbp : b ^ p = 1 := ((isElementaryAbelian_iff p E).1 hEe).2 b hbE
  have hBeq : B = zpowers (y : Q) ⊔ zpowers b := by
    apply le_antisymm
    · intro x hx
      obtain ⟨k, a, ha, rfl⟩ := hform x hx
      exact mul_mem (mem_sup_right ((zpowers b).zpow_mem (mem_zpowers b) k)) (mem_sup_left ha)
    · exact sup_le hUB.le (zpowers_le.2 hbB)
  have hBcard : Nat.card B = p ^ 2 := by
    rw [hBeq, card_sup_zpowers hp _ hbp hbU
      (fun e he => (mem_center_iff.1 (hUle he) b).symm), hUcard]
    ring
  exact ⟨zpowers (y : Q), B, hUB.le, hUcard, hUle, isElementaryAbelian_of_le hBE hEe, hBcard,
    hBn, hcomm⟩

end CFSG.RankThree.PartOne.Planes

namespace CFSG.RankThree.PartOne

open Subgroup
open scoped commutatorElement

theorem pgOddNoncyclicSecondCenterNormalPlane :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → p ≠ 2 → ∀ P : Subgroup G,
      IsPGroup p P → ¬ IsCyclic P →
      ∃ U V : Subgroup G, U ≤ V ∧ V ≤ P ∧ Nat.card U = p ∧
        U ≤ P ⊓ Subgroup.centralizer (P : Set G) ∧ IsElementaryAbelian p V ∧ Nat.card V = p ^ 2 ∧
        P ≤ Subgroup.normalizer (V : Set G) ∧ ⁅V, P⁆ ≤ U := by
  intro G _ _ p hp hp2 P hP hnc
  have hpF : Fact p.Prime := ⟨hp⟩
  obtain ⟨U, V, hUV, hU, hUZ, hV, hVc, hVn, hcomm⟩ :=
    Planes.exists_normal_plane hp hp2 hP hnc
  have hinj : Function.Injective P.subtype := Subtype.val_injective
  refine ⟨U.map P.subtype, V.map P.subtype, Subgroup.map_mono hUV, Subgroup.map_subtype_le V,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective hinj, hU]
  · rintro _ ⟨u, hu, rfl⟩
    refine ⟨u.2, mem_centralizer_iff.2 fun h hh => ?_⟩
    exact congrArg Subtype.val (mem_center_iff.1 (hUZ hu) ⟨h, hh⟩)
  · have := hV
    exact IsElementaryAbelian.map_subtype
  · rw [Subgroup.card_map_of_injective hinj, hVc]
  · have h : (V.map P.subtype).subgroupOf P = V :=
      Subgroup.comap_map_eq_self_of_injective hinj V
    exact (normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le V)).1 (by rw [h]; exact hVn)
  · rw [Subgroup.commutator_le]
    rintro _ ⟨v, hv, rfl⟩ g hg
    exact ⟨⁅v, ⟨g, hg⟩⁆, hcomm v hv ⟨g, hg⟩, rfl⟩

end CFSG.RankThree.PartOne
