module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res8ProofKMd
public import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.RankThree.PartTwo.Sec17.Item17Res9ProofComp
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec4.T444.Lift
import CFSG.RankThree.PartTwo.Sec4.Census.Lift46
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec14.Item145Bot

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

namespace Proof17Res9

variable {G : Type} [Group G] [Finite G]

theorem lB_le_ld {A L : Subgroup G} {c d : G} (hΩ : omegaA A = {Subgroup.zpowers c})
    (hc3 : orderOf c = 3) (hcL : c ∉ L) (hLc : L ∈ lA A c) (hdL : d ∈ L) (hcA : c ∈ A)
    (hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {D : Subgroup G} (hDA : D ≤ A)
    (hdD : d ∈ D) :
    lB A D ≤ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) := by
  refine iSup_le fun b => iSup_le fun d' => iSup_le fun Lb => iSup_le fun hcfg => ?_
  obtain ⟨hD, hbΩ, hLb, -, hd'Lb, -⟩ := hcfg
  have hbc : Subgroup.zpowers b = Subgroup.zpowers c := by
    rw [hΩ] at hbΩ
    exact hbΩ
  have hLLb : L = Lb := by
    have hL' : L ∈ lA A b := (lA_eq_of_zpowers_eq hbc) ▸ hLc
    rw [hLb] at hL'
    exact hL'
  subst hLLb
  have hd'D : d' ∈ D := by
    rw [hD]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton d'))
  have hd'A : d' ∈ A := hDA hd'D
  have hDeq : D = Subgroup.zpowers c ⊔ Subgroup.zpowers d' := by
    rw [hD, Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure, hbc]
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (Subgroup.zpowers d' : Set G) :=
    Subgroup.zpowers_le.mpr (centralizer_singleton_le_normalizer_zpowers d'
      (Subgroup.mem_centralizer_singleton_iff.mpr (hAcomm c hcA d' hd'A)))
  have hdD' : d ∈ ((Subgroup.zpowers c ⊔ Subgroup.zpowers d' : Subgroup G) : Set G) := by
    rw [← hDeq]
    exact hdD
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hcN] at hdD'
  obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.mp hdD'
  have hyL : y ∈ L := (Subgroup.zpowers_le.mpr hd'Lb) hy
  have hxL : x ∈ L := by
    have : x = d * y⁻¹ := by rw [← hxy]; group
    rw [this]
    exact mul_mem hdL (inv_mem hyL)
  have hx1 : x = 1 := by
    have h := Sec4.Census.inf_zpowers_eq_bot_of_not_mem Nat.prime_three hc3 hcL
    have hxmem : x ∈ L ⊓ Subgroup.zpowers c := ⟨hxL, hx⟩
    rw [h, Subgroup.mem_bot] at hxmem
    exact hxmem
  have hdy : d ∈ Subgroup.zpowers d' := by
    rw [← hxy, hx1, one_mul]
    exact hy
  have hCC : Subgroup.centralizer ({d'} : Set G) ≤ Subgroup.centralizer ({d} : Set G) := by
    intro g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hdy
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    exact ((Commute.zpow_left (Commute.symm hg) n).symm).eq
  exact Sec6.inSubgroup_perfectResidual_mono (inf_le_inf_left _ hCC)

theorem delta_le_sup_of_lB_le {A L : Subgroup G} {c : G} (hbal : Step143Balance)
    (h : Sec14Std G A c L) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    (hΩ : Subgroup.zpowers a ∉ omegaA A) {X : Subgroup G}
    (hLD : ∀ D : Subgroup G, IsHyperplane A D → a ∈ D →
      lB A D ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X) :
    delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ≤
      pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
        pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊔ X := by
  have hA := h.isE27'
  have hAmax := h.maximal_isElemAbelian
  refine sSup_le fun P hP => ?_
  obtain ⟨hPq, hPa⟩ := hP
  have hP3 : ¬ 3 ∣ Nat.card P := (isPiSubgroup_piCompl_iff Nat.prime_three P).mp hPq.1.2.1
  refine Sec5.le_of_forall_inf_centralizer_sub_le (k := 2) Nat.prime_three hA.1
    (by rw [hA.2]; norm_num) hPq.1.2.2
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hP3) fun H hHA hH9 => ?_
  have hH : IsHyperplane A H := ⟨hHA, by rw [hA.2, hH9]; norm_num⟩
  by_cases haH : a ∈ H
  · have hK := pPrimeCoreOf_centralizer_le_sup hA hAmax hH.1
      (commutator_pPrimeCoreOf_le hbal h ha ha1 hΩ hH haH)
    refine (hPq.2 H hH).trans ?_
    rw [qBound]
    exact sup_le (sup_le (hK.trans le_sup_left) (le_sup_right.trans le_sup_left))
      ((hLD H hH haH).trans (sup_le (le_sup_left.trans le_sup_left) le_sup_right))
  · have hAle := le_sup_zpowers_of_not_mem hA hH ha haH
    have hCA : P ⊓ Subgroup.centralizer (H : Set G) ≤
        P ⊓ Subgroup.centralizer (A : Set G) := fun x hx =>
      ⟨hx.1, mem_centralizer_of_le_sup hAle hx.2 (hPa hx.1)⟩
    exact hCA.trans ((inf_centralizer_le_xA hAmax hP3).trans (le_sup_right.trans le_sup_left))

end Proof17Res9

open Proof17Res9 in
theorem claim143LdThree_of
    (hbal : Step143Balance)
    (h48 : Sec4.Item4_8) : Claim143LdThree := by
  intro G _ _ A c L Y₀ hs hΩ hJ d hdA hd1 hdc K hK hKΔ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h14 : Sec14Std G A c L := hs.toSec14Std
  have hD13 : Sec13Data G A c L := hs.toSec13Data
  have hA : Late.IsE27 A := h14.isE27'
  have hcA : c ∈ A := hD13.mem_A
  have hc3 : orderOf c = 3 := hD13.orderOf_eq
  have hc1 : c ≠ 1 := hD13.ne_one
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  set C := Subgroup.centralizer ({d} : Set G) with hCdef
  set O := pPrimeCoreOf 3 C with hOdef
  set O' := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hO'def
  set Ld := inSubgroup perfectResidual (L ⊓ C) with hLddef
  obtain ⟨K', hK', rfl⟩ := hK
  have hcardK : Nat.card (K'.map C.subtype) = Nat.card K' :=
    Subgroup.card_map_of_injective C.subtype_injective
  by_cases hK3 : ¬ 3 ∣ Nat.card (K'.map C.subtype)
  · left
    rw [hcardK] at hK3
    exact Subgroup.map_mono (Sec4.le_pPrimeCore_of_isSubnormal hK'.2.1 hK3)
  push Not at hK3
  right
  obtain ⟨hcL, h9, -⟩ := Sec14.j2_point_facts hD13 hJ
  have h3L : 3 ∣ Nat.card L := by
    have h9L := Subgroup.card_dvd_of_le (inf_le_right : A ⊓ L ≤ L)
    rw [h9] at h9L
    exact (show 3 ∣ 9 by norm_num).trans h9L
  obtain ⟨hdL, S, hdS, hSd⟩ := hdc
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three
  have hG4 : SectionFourHyp ↥C := hD13.toTheoremFourHyp.sectionFourHyp
    (centralizer_singleton_ne_top h14.isSimpleGroup h14.nonabelian hd1)
  have hJq := residual_inf_centralizer_quasisimple_of_quot Sec4.Sporadic.rank3II_4_15 hθ3 hθs
    hJ hdL hd1 ⟨S, hdS, hSd⟩
  obtain ⟨X, hX, hLdX⟩ :=
    exists_mem_thetaComponentsAt_le_residual h48 hG4 hA hcA hdA hc1 hD13.mem_lA.1 hJq
  by_contra hLdK
  have hdΩ : Subgroup.zpowers d ∉ omegaA A := by
    rw [hΩ, Set.mem_singleton_iff]
    intro hdc
    exact hcL ((Subgroup.zpowers_le.mpr hdL) (hdc ▸ Subgroup.mem_zpowers c))
  have hΔ : delta A (lB A) C ≤ O ⊔ O' ⊔ Ld :=
    delta_le_sup_of_lB_le hbal h14 hdA hd1 hdΩ fun D hD hdD =>
      (lB_le_ld hΩ hc3 hcL hD13.mem_lA hdL hcA hAcomm hD.1 hdD).trans le_sup_right
  obtain ⟨X', hX', rfl⟩ := hX
  have hKX : K' ≠ X' := fun h => hLdK (h ▸ hLdX)
  have hLdC : Ld ≤ C := (Subgroup.map_subtype_le _).trans inf_le_right
  have hO'C : O' ≤ C := (pPrimeCoreOf_le 3 _).trans
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hdA))
  have hLd : (Ld.subgroupOf C).map C.subtype = Ld := Subgroup.map_subgroupOf_eq_of_le hLdC
  have hO' : (O'.subgroupOf C).map C.subtype = O' := Subgroup.map_subgroupOf_eq_of_le hO'C
  have hLdX' : Ld.subgroupOf C ≤ X' := by
    rw [← Subgroup.map_le_map_iff_of_injective C.subtype_injective, hLd]
    exact hLdX
  have hO'N : O' ≤ Subgroup.normalizer (Ld : Set G) := by
    have hCAc : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({c} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcA)
    have hO'L : O' ≤ Subgroup.normalizer (L : Set G) :=
      ((pPrimeCoreOf_le 3 _).trans hCAc).trans (centralizer_le_normalizer_of_three_dvd h14 h3L)
    have hO'CN : O' ≤ Subgroup.normalizer (C : Set G) := hO'C.trans Subgroup.le_normalizer
    exact (Late.le_normalizer_inf hO'L hO'CN).trans
      (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
        _)
  have hJN : O'.subgroupOf C ≤ Subgroup.normalizer ((Ld.subgroupOf C : Subgroup ↥C) : Set ↥C) := by
    intro j hj
    rw [Subgroup.mem_subgroupOf] at hj
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    simpa using Subgroup.mem_normalizer_iff.mp (hO'N hj) (x : G)
  have hKle : K' ≤ CFSG.pPrimeCore 3 ↥C ⊔ O'.subgroupOf C ⊔ Ld.subgroupOf C := by
    rw [← Subgroup.map_le_map_iff_of_injective C.subtype_injective, Subgroup.map_sup,
      Subgroup.map_sup, hO', hLd]
    exact hKΔ.trans hΔ
  have hO'3 : ¬ 3 ∣ Nat.card (O'.subgroupOf C) := fun h3 =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
      (h3.trans (Proof17Res8.card_subgroupOf_dvd O' C))
  have hO3 : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥C) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  rw [hcardK] at hK3
  exact false_of_le_sup_of_ne hK' hX' hKX hLdX' CFSG.pPrimeCore_normal hO3 hO'3 hJN hKle hK3

end CFSG.RankThree.PartTwo.Sec17
