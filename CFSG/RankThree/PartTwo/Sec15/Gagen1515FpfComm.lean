module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1515FpfCtx
public import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.RankThree.PartTwo.Sec15.Item15Res11ProofTools
import CFSG.RankThree.PartTwo.Sec15.Item1518Res2ProofDelta
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullCommutator
import CFSG.GroupTheory.CommutingConjugatePair
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.RankThree.PartTwo.Sec13.Item13Prod
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ

public section

namespace CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {A L : Subgroup G} {c d : G}

theorem eq_bot_of_le_centralizer
    (hbal : Step143Balance)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h : Ctx A c L d) {U : Subgroup G}
    (hU : U ∈ scriptQ A (lB A)) (hU2 : IsPGroup 2 ↥U)
    (hUL : U ≤ Subgroup.centralizer (L : Set G)) (hUc : U = ⁅U, Subgroup.zpowers c⁆) :
    U = ⊥ := by
  have hD := h.sec13Data
  have hS := h.conf.sec15R.toSec14Std
  have hA : Late.IsE27 A := h.isE27
  have hcA : c ∈ A := hD.mem_A
  have hdA : d ∈ A := h.mem_d
  have hdL : d ∈ L := h.mem_L
  have hmd1 : d ≠ 1 := h.ne_d
  obtain ⟨-, hAL9, -⟩ := j2_point_facts hD h.conf.j2
  have hB0 : IsHyperplane A (A ⊓ L) := by
    refine ⟨inf_le_left, ?_⟩
    have h27 : Nat.card A = 27 := hA.2
    omega
  have hlB : lB A (A ⊓ L) = ⊥ := Proof1518R2.lB_eq_bot_of_forall_not_le1523 h.off
  have hbound := (mem_scriptQ_iff.mp hU).2.2 (A ⊓ L) hB0
  have hUB0 : U ≤ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) :=
    hUL.trans (Subgroup.centralizer_le inf_le_right)
  set NB : Subgroup G :=
    pPrimeCoreOf 3 (Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G)) with hNB
  set OA : Subgroup G := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hOA
  have hUle : U ≤ NB ⊔ OA := by
    have h := hbound
    rw [inf_eq_left.mpr hUB0, qBound, hlB, sup_bot_eq] at h
    simpa [hNB, hOA] using h
  have hcB0 : c ∈ Subgroup.centralizer ((A ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hx.2)
  have hcNB : c ∈ Subgroup.normalizer (NB : Set G) := by
    rw [hNB]
    exact le_normalizer_pPrimeCoreOf 3 _ hcB0
  have hYNB : OA ≤ Subgroup.normalizer (NB : Set G) := by
    rw [hOA, hNB]
    exact (pPrimeCoreOf_le 3 _).trans
      ((Subgroup.centralizer_le inf_le_left).trans (le_normalizer_pPrimeCoreOf 3 _))
  have hYc : OA ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [hOA]
    exact (pPrimeCoreOf_le 3 _).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hcA))
  have hUNB : U ≤ NB :=
    Proof15Res11.le_of_le_sup_of_le_centralizer hUc hcNB hYNB hYc hUle
  have hAU : A ≤ Subgroup.normalizer (U : Set G) := (mem_scriptQ_iff.mp hU).2.1
  have hUA : U = ⁅U, A⁆ := by
    refine le_antisymm ?_ (Subgroup.le_normalizer_iff_commutator_le_left.mp hAU)
    calc U = ⁅U, Subgroup.zpowers c⁆ := hUc
      _ ≤ ⁅U, A⁆ := Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr hcA)
  have hΩd : Subgroup.zpowers d ∉ omegaA A := (h.omega_facts h134 h48).1
  have hcomm : ⁅NB, A⁆ ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) := by
    rw [hNB]
    exact commutator_pPrimeCoreOf_le hbal hS hdA hmd1 hΩd hB0 ⟨hdA, hdL⟩
  have hUM : U ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) := by
    calc U = ⁅U, A⁆ := hUA
      _ ≤ ⁅NB, A⁆ := Subgroup.commutator_mono hUNB le_rfl
      _ ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) := hcomm
  have hUNL : U ≤ Subgroup.normalizer (L : Set G) :=
    hUL.trans (Subgroup.centralizer_le_normalizer (L : Set G))
  have hUinf : U ≤ Subgroup.normalizer (L : Set G) ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) := le_inf hUNL hUM
  have hbot : U ⊓ (Subgroup.normalizer (L : Set G) ⊓
      pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))) = ⊥ :=
    CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd hU2 h.odd
  calc U = U ⊓ (Subgroup.normalizer (L : Set G) ⊓
        pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G))) :=
        (inf_eq_left.mpr hUinf).symm
    _ = ⊥ := hbot

theorem le_centralizer_of_le_normalizer
    (hbal : Step143Balance) (h134 : Item134) (h48 : Sec4.Item4_8) (h : Ctx A c L d)
    {Q : Subgroup G} (hQ : Q ∈ scriptQ A (lB A)) (hQ2 : IsPGroup 2 ↥Q)
    (hQL : Q ≤ Subgroup.normalizer (L : Set G)) :
    Q ≤ Subgroup.centralizer ({c} : Set G) := by
  have hD := h.sec13Data
  have hcA : c ∈ A := hD.mem_A
  have hAU : A ≤ Subgroup.normalizer (Q : Set G) := (mem_scriptQ_iff.mp hQ).2.1
  set U : Subgroup G := ⁅Q, Subgroup.zpowers c⁆ with hUdef
  have hcQ : Subgroup.zpowers c ≤ Subgroup.normalizer (Q : Set G) :=
    Subgroup.zpowers_le.mpr (hAU hcA)
  have hUQ : U ≤ Q := by
    rw [hUdef]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hcQ
  have hU2 : IsPGroup 2 ↥U := hQ2.to_le hUQ
  have hAU' : A ≤ Subgroup.normalizer (U : Set G) := by
    rw [hUdef]
    exact le_normalizer_commutator hAU hD.A_le_normalizer_zpowers
  have hUscript : U ∈ scriptQ A (lB A) := mem_scriptQ_of_le hQ hUQ hAU'
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers c)) (Nat.card Q) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ2
    rw [Nat.card_zpowers, hD.orderOf_eq, hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hUc : U = ⁅U, Subgroup.zpowers c⁆ := by
    rw [hUdef]
    exact (CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull.properHull_coprime_double_commutator
      Q (Subgroup.zpowers c) hcQ hcop).symm
  have hccL : ⁅Subgroup.zpowers c, L⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x hx l hl
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact (Commute.zpow_right
      (show Commute l c from Subgroup.mem_centralizer_singleton_iff.mp
        (hD.le_centralizer hl)) k).eq
  have hLc : ⁅L, Subgroup.zpowers c⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hccL
  have hLQ : ⁅L, Q⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_left.mp hQL
  have h1 : ⁅⁅Subgroup.zpowers c, L⁆, Q⁆ = ⊥ := by
    rw [hccL]
    exact Subgroup.commutator_bot_left Q
  have h2 : ⁅⁅L, Q⁆, Subgroup.zpowers c⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono hLQ le_rfl).trans hLc.le)
  have hcomm : ⁅⁅Q, Subgroup.zpowers c⁆, L⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := Q) (H₂ := Subgroup.zpowers c)
      (H₃ := L) h1 h2
  have hUL : U ≤ Subgroup.centralizer (L : Set G) := by
    have hUcomm : ⁅U, L⁆ = ⊥ := by
      rw [hUdef]
      exact hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hUcomm
  have hUbot : U = ⊥ := eq_bot_of_le_centralizer hbal h134 h48 h hUscript hU2 hUL hUc
  have hQZ : Q ≤ Subgroup.centralizer (Subgroup.zpowers c : Set G) := by
    have hcomm' : ⁅Q, Subgroup.zpowers c⁆ = ⊥ := by
      rw [← hUdef]
      exact hUbot
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm'
  intro q hq
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp (hQZ hq) c (Subgroup.mem_zpowers c)).symm

end Ctx

end CFSG.RankThree.PartTwo.Sec15.Gagen1515Fpf
