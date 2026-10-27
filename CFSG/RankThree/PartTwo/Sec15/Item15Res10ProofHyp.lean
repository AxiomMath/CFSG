module

public import CFSG.RankThree.PartTwo.Sec15.Item15Res10ProofEnd
import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofPassage
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullCommutator
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CentralizerZpowers

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

namespace Proof15Res10

open Proof15Res4

theorem le_normalizer_commutatorR (h : Conf1515HJ A c L L) :
    A ≤ Subgroup.normalizer
      ((⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ :
        Subgroup G) : Set G) := by
  have hD := h.sec13Data
  intro a ha
  refine mem_normalizer_commutator ((hD.le_normalizer.trans
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)) ha) ?_
  refine CFSG.GorensteinWalter.centralizer_singleton_le_normalizer_zpowers c ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hD.commute ha hD.mem_A

theorem commutatorR_le (h : Conf1515HJ A c L L) :
    ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ ≤
      CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)) :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((Subgroup.zpowers_le.mpr (h.sec13Data.le_normalizer h.sec13Data.mem_A)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))

theorem commutator_eq_commutator_A (h : Conf1515HJ A c L L) :
    ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ =
      ⁅⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆, A⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.sec13Data
  set N := Subgroup.normalizer (L : Set G) with hNdef
  set Q := CFSG.Open.pCoreOf 2 N with hQdef
  set R := ⁅Q, Subgroup.zpowers c⁆ with hRdef
  have hZQ : Subgroup.zpowers c ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.zpowers_le.mpr (hD.le_normalizer hD.mem_A)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N)
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers c)) (Nat.card Q) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
    rw [Nat.card_zpowers, hD.orderOf_eq, hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hcc : ⁅R, Subgroup.zpowers c⁆ = R :=
    CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull.properHull_coprime_double_commutator
      Q (Subgroup.zpowers c) hZQ hcop
  refine le_antisymm ?_ (Subgroup.le_normalizer_iff_commutator_le_left.mp
    (le_normalizer_commutatorR h))
  calc R = ⁅R, Subgroup.zpowers c⁆ := hcc.symm
    _ ≤ ⁅R, A⁆ := Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hD.mem_A)

theorem commutator_mem_scriptQ
    (h : Conf1515HJ A c L L)
    (hB0 : ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ ≤
      qBound A (lB A) (A ⊓ L)) :
    ⁅CFSG.Open.pCoreOf 2 (Subgroup.normalizer (L : Set G)), Subgroup.zpowers c⁆ ∈
      scriptQ A (lB A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD := h.sec13Data
  have hS := h.sec15R.toSec14Std
  have hA : Late.IsE27 A := Late.isE27_of_mem_partTwoE hD.mem_partTwoE
  obtain ⟨hcL, hAL9, hAc⟩ := j2_point_facts hD h.j2
  set N := Subgroup.normalizer (L : Set G) with hNdef
  set Q := CFSG.Open.pCoreOf 2 N with hQdef
  set R := ⁅Q, Subgroup.zpowers c⁆ with hRdef
  have hR2 : IsPGroup 2 R := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N).to_le (commutatorR_le h)
  have h3 : ∀ H : Subgroup G, IsPGroup 2 H → IsPiSubgroup (piCompl 3) H := by
    intro H hH
    refine (isPiSubgroup_piCompl_iff Nat.prime_three H).mpr fun h3 => ?_
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hH
    rw [hn] at h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hAR := le_normalizer_commutatorR h
  have hRL : R ≤ Subgroup.centralizer (L : Set G) := commutator_le_centralizer hD.le_centralizer
  set Rc := R ⊓ Subgroup.centralizer ({c} : Set G) with hRcdef
  have hARc : A ≤ Subgroup.normalizer (Rc : Set G) := by
    refine Late.le_normalizer_inf hAR ?_
    intro a ha
    exact Subgroup.le_normalizer
      (Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute ha hD.mem_A))
  have hRcQ : Rc ∈ scriptQ A (lB A) :=
    (mem_scriptQ_of_hj_point hS h.j2 ⟨inf_le_right.trans
      (CFSG.GorensteinWalter.centralizer_singleton_le_normalizer_zpowers c),
      h3 Rc (hR2.to_le inf_le_left), hARc⟩).1
  refine mem_scriptQ_iff.mpr ⟨h3 R hR2, hAR, fun B hB => ?_⟩
  by_cases hBL : B ≤ L
  ·
    have hBeq : B = A ⊓ L := by
      refine Subgroup.eq_of_le_of_card_ge (le_inf hB.1 hBL) ?_
      have h27 : Nat.card A = 27 := hA.2
      have hB2 := hB.2
      omega
    rw [hBeq]
    exact inf_le_left.trans hB0
  ·
    obtain ⟨x, hxB, hxL⟩ := Set.not_subset.mp hBL
    have hxA : x ∈ A := hB.1 hxB
    have hcAL : Subgroup.zpowers c ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) :=
      Subgroup.zpowers_le.mpr (Late.le_normalizer_inf Subgroup.le_normalizer hD.le_normalizer
        hD.mem_A)
    obtain ⟨m, hm, o, ho, hxmo⟩ := exists_mul_of_mem_sup hcAL (hAc ▸ hxA)
    have hmL : m ∉ L := by
      intro hmL'
      exact hxL (hxmo ▸ L.mul_mem hmL' ho.2)
    have hmA : m ∈ A := (Subgroup.zpowers_le.mpr hD.mem_A) hm
    have hm1 : m ≠ 1 := fun h1 => hmL (h1 ▸ L.one_mem)
    have hm3 : orderOf m = 3 := orderOf_eq_prime (hA.1.2 m hmA) hm1
    have hcm : c ∈ Subgroup.zpowers m := by
      have heq : Subgroup.zpowers m = Subgroup.zpowers c :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hm)
          (by rw [Nat.card_zpowers, Nat.card_zpowers, hm3, hD.orderOf_eq])
      exact heq ▸ Subgroup.mem_zpowers c
    have hle : R ⊓ Subgroup.centralizer (B : Set G) ≤ Rc := by
      rintro r ⟨hr, hrB⟩
      refine Subgroup.mem_inf.mpr ⟨hr, ?_⟩
      have hrx : Commute r x := (Subgroup.mem_centralizer_iff.mp hrB x hxB).symm
      have hro : Commute r o := (Subgroup.mem_centralizer_iff.mp (hRL hr) o ho.2).symm
      have hrm : Commute r m := by
        have e : m = x * o⁻¹ := by rw [hxmo]; group
        rw [e]
        exact hrx.mul_right hro.inv_right
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hcm
      rw [Subgroup.mem_centralizer_singleton_iff, ← hj]
      exact (hrm.zpow_right j).eq
    calc R ⊓ Subgroup.centralizer (B : Set G) ≤ Rc ⊓ Subgroup.centralizer (B : Set G) :=
          le_inf hle inf_le_right
      _ ≤ qBound A (lB A) B := hRcQ.2 B hB

end Proof15Res10

open Proof15Res4 Proof15Res10

end CFSG.RankThree.PartTwo.Sec15
