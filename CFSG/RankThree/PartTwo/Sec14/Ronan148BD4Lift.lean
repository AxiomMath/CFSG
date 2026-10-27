module

public import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Item148ProofYB
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec14.Ronan148NFive
import CFSG.RankThree.PartTwo.Sec14.Item148Res7ProofPoint
import CFSG.RankThree.PartTwo.Sec12.Item128Bar
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartOne.K1214.Basic
public import CFSG.RankThree.PartTwo.Sec15.HypS

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Res148BD4

omit [Finite G] in
theorem commutator_le_of_le_normalizer {W X N : Subgroup G} (hWN : W ≤ N)
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) : ⁅W, X⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro w hw x hx
  rw [commutatorElement_def]
  have h1 : x * w⁻¹ * x⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hXN hx) _).mp (N.inv_mem (hWN hw))
  have h2 : w * x * w⁻¹ * x⁻¹ = w * (x * w⁻¹ * x⁻¹) := by group
  rw [h2]
  exact N.mul_mem (hWN hw) h1

theorem not_mem_of_coprime {N : Subgroup G} (hN : Nat.Coprime 3 (Nat.card N)) {b : G}
    (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) : b ∉ N := by
  intro hbN
  have h1 : orderOf (⟨b, hbN⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
  have h2 : orderOf (⟨b, hbN⟩ : N) ∣ 3 := by
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext (by simpa using hb3)
  have h3 : orderOf (⟨b, hbN⟩ : N) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hN) h1
  rw [orderOf_eq_one_iff] at h3
  exact hb1 (congrArg Subtype.val h3)

theorem coprime_card_sup_of_le_normalizer {N R : Subgroup G} (hN : Nat.Coprime 3 (Nat.card N))
    (hR : Nat.Coprime 3 (Nat.card R)) (hRN : R ≤ Subgroup.normalizer (N : Set G)) :
    Nat.Coprime 3 (Nat.card (N ⊔ R : Subgroup G)) := by
  have h := PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hRN
  have hdvd : Nat.card (N ⊔ R : Subgroup G) ∣ Nat.card N * Nat.card R := by
    rw [← h]
    exact Dvd.intro _ rfl
  exact Nat.Coprime.coprime_dvd_right hdvd (Nat.Coprime.mul_right hN hR)

section Certs


theorem false_of_mem_commutator148 (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5)
    (h142 : Item142AllS14) (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15)
    {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) (h143 : Item143N A (lB A))
    (hnHJ : ¬ AllPointsHJ A) {B : Subgroup G} (hB : IsHyperplane A B) {W : Subgroup G}
    (hW : W ∈ scriptQZero A (lB A)) (hWB : W ≤ Subgroup.centralizer (B : Set G)) {b : G}
    (hb : b ∈ B) (hb1 : b ≠ 1) {R : Subgroup G} (hRb : R ≤ Subgroup.centralizer ({b} : Set G))
    (hR3 : Nat.Coprime 3 (Nat.card R))
    (hbW : b ∈ ⁅W, Subgroup.centralizer ({b} : Set G)⁆ ⊔ R) : False := by
  have hD := h.toSec13Data
  have hAc : IsMulCommutative A := hD.isElemAbelian.1
  have hbA : b ∈ A := hB.1 hb
  have hb3 : b ^ 3 = 1 := hD.isElemAbelian.2 b hbA
  have hWb : W ≤ Subgroup.centralizer ({b} : Set G) :=
    hWB.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))
  have hWA : W = ⁅W, A⁆ := hW.2
  have hWinv : W ∈ invariantPiSubgroups ⊤ A (piCompl 3) := hW.1.1
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hD.commute hx hbA)
  have hcomm : ∀ N : Subgroup G, W ≤ N →
      Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (N : Set G) → b ∈ N ⊔ R :=
    fun N hWN hCN => sup_le_sup_right (commutator_le_of_le_normalizer hWN hCN) R hbW
  have hcopN : ∀ N : Subgroup G, Nat.Coprime 3 (Nat.card N) →
      Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (N : Set G) → b ∉ N ⊔ R :=
    fun N hN hCN => not_mem_of_coprime (coprime_card_sup_of_le_normalizer hN hR3 (hRb.trans hCN))
      hb3 hb1
  by_cases hbΩ : Subgroup.zpowers b ∈ omegaA A
  ·
    obtain ⟨Lb, hLb⟩ := Sec12.exists_mem_lA422 h422 h45 hD.toPartTwoStanding hD.mem_partTwoF
      hD.card_eq hbΩ
    have hLbA : Lb ∈ lA A b := Sec12.mem_lA_of_mem_lA422 hAb hLb
    have hS : Sec14Std G A b Lb := { h with zpowers_mem_omegaA := hbΩ, mem_lA := hLbA }
    have hDb : Sec13Data G A b Lb := hS.toSec13Data
    have hT := (h.chosen136.2 b hbΩ Lb hLbA).1
    have hbL : b ∉ Lb :=
      not_mem_of_center_eq_bot hDb (Sec15.center_eq_bot_of_types hDb.mem_thetaComponentsAt hT)
    set H := Subgroup.normalizer (Subgroup.zpowers b : Set G) with hHdef
    have hCH : Subgroup.centralizer ({b} : Set G) ≤ H := by
      rw [← centralizer_zpowers148]
      exact Subgroup.centralizer_le_normalizer _
    have hWH : W ∈ invariantPiSubgroups H A (piCompl 3) :=
      ⟨hWb.trans hCH, hWinv.2.1, hWinv.2.2⟩
    obtain ⟨Qs, hQs, hWQs⟩ := exists_le_mem_maxInvariantPiSubgroups hWH
    obtain ⟨hQsmem, halt⟩ := h142 G A b Lb hS Qs hQs
    have hAH : A ≤ Subgroup.normalizer (pPrimeCoreOf 3 H : Set G) :=
      (hAb.trans hCH).trans (le_normalizer_pPrimeCoreOf 3 H)
    have hCO : Subgroup.centralizer ({b} : Set G) ≤
        Subgroup.normalizer (pPrimeCoreOf 3 H : Set G) :=
      hCH.trans (le_normalizer_pPrimeCoreOf 3 H)
    rcases halt with ⟨-, hQsK, hOK, hcard⟩ | ⟨hK, -⟩
    ·
      rw [← hHdef] at hOK hcard
      set K := k142 A (lB A) b with hKdef
      have hidx : ((pPrimeCoreOf 3 H).subgroupOf K).index = 2 := by
        have h1 := Subgroup.card_mul_index ((pPrimeCoreOf 3 H).subgroupOf K)
        have h2 : Nat.card ↥((pPrimeCoreOf 3 H).subgroupOf K) = Nat.card (pPrimeCoreOf 3 H) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOK).toEquiv
        rw [h2, hcard] at h1
        have hpos : 0 < Nat.card (pPrimeCoreOf 3 H) := Nat.card_pos
        have h3 : Nat.card (pPrimeCoreOf 3 H) * ((pPrimeCoreOf 3 H).subgroupOf K).index =
            Nat.card (pPrimeCoreOf 3 H) * 2 := by rw [h1, mul_comm]
        exact Nat.eq_of_mul_eq_mul_left hpos h3
      have hAK : A ≤ Subgroup.normalizer (K : Set G) := le_normalizer_sSup fun Q' hQ' =>
        hQ'.1.1.2.2
      have hWK : W ≤ K := hWQs.trans (hQsK ▸ le_rfl)
      have hWO : W ≤ pPrimeCoreOf 3 H := by
        rw [hWA, Subgroup.commutator_le]
        intro x hx a ha
        have hxK : x ∈ K := hWK hx
        have hax : a * x⁻¹ * a⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp (hAK ha) _).mp (K.inv_mem hxK)
        have hmem := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨x, hxK⟩)
          (b := ⟨a * x⁻¹ * a⁻¹, hax⟩)).mpr ?_
        · rw [Subgroup.mem_subgroupOf] at hmem
          rw [commutatorElement_def]
          simpa [mul_assoc] using hmem
        · rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
          constructor
          · intro hx'
            exact (Subgroup.mem_normalizer_iff.mp (hAH ha) _).mp ((pPrimeCoreOf 3 H).inv_mem hx')
          · intro hax'
            have := (Subgroup.mem_normalizer_iff.mp (hAH (A.inv_mem ha)) _).mp hax'
            simpa [mul_assoc] using this
      exact hcopN _ (coprime_card_pPrimeCoreOf 3 H) hCO (hcomm _ hWO hCO)
    ·
      have hQsK : Qs ≤ k142 A (lB A) b := le_delta hQsmem.1 (hQsmem.2.trans hCH)
      have hLbN : A ≤ Subgroup.normalizer (Lb : Set G) := hLbA.2.1
      have h3 : 3 ∣ Nat.card Lb := three_dvd_card_of_types148 hT
      have hCLb : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer (Lb : Set G) :=
        centralizer_le_normalizer_of_three_dvd hS h3
      have hCA : Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer ({b} : Set G) :=
        Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbA)
      have hM : A ≤ Subgroup.normalizer ((Lb ⊔ pPrimeCoreOf 3 H : Subgroup G) : Set G) :=
        le_normalizer_sup (A := A) hLbN hAH
      have hCM : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤ Subgroup.normalizer
          ((Lb ⊔ pPrimeCoreOf 3 H : Subgroup G) : Set G) := by
        have h1 : pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ≤
            Subgroup.centralizer ({b} : Set G) := (pPrimeCoreOf_le 3 _).trans hCA
        exact le_normalizer_sup (A := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)))
          (h1.trans hCLb) ((h1.trans hCH).trans (le_normalizer_pPrimeCoreOf 3 H))
      have hWLb : W ≤ Lb ⊔ pPrimeCoreOf 3 H := by
        rw [hWA]
        refine (Subgroup.commutator_mono (hWQs.trans (hQsK.trans hK.le)) le_rfl).trans ?_
        exact commutator_sup_le148 hM hCM (pPrimeCoreOf_le 3 _)
      have hCLbR : Subgroup.centralizer ({b} : Set G) ≤
          Subgroup.normalizer ((Lb ⊔ pPrimeCoreOf 3 H : Subgroup G) : Set G) :=
        le_normalizer_sup (A := Subgroup.centralizer ({b} : Set G)) hCLb hCO
      have hbM : b ∈ Lb ⊔ (pPrimeCoreOf 3 H ⊔ R) := by
        rw [← sup_assoc]
        exact hcomm _ hWLb hCLbR
      set R' := pPrimeCoreOf 3 H ⊔ R with hR'def
      have hRH : R ≤ Subgroup.normalizer (pPrimeCoreOf 3 H : Set G) := hRb.trans hCO
      have hR'3 : Nat.Coprime 3 (Nat.card R') :=
        coprime_card_sup_of_le_normalizer (coprime_card_pPrimeCoreOf 3 H) hR3 hRH
      have hRLb : R' ≤ Subgroup.normalizer (Lb : Set G) :=
        sup_le ((pPrimeCoreOf_le 3 H).trans (Res7Point.normalizer_zpowers_le148 h hbΩ hLbA h3))
          (hRb.trans hCLb)
      have hbM' : b ∈ ((Lb : Set G) * (R' : Set G)) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left Lb R' hRLb]
        exact hbM
      obtain ⟨j, hj, r, hr, hjr⟩ := hbM'
      have hjb : j⁻¹ * b ∈ R' := by
        rw [← hjr]
        simpa using hr
      exact hbL (Ronan148N.mem_of_pow_three_pow_eq_one148 hRLb hR'3 hj hjb (k := 1)
        (by simpa using hb3))
  ·
    obtain ⟨Qs, hQs⟩ := maxInvariantPiSubgroups_nonempty
      (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) A (piCompl 3)
    obtain ⟨-, halt⟩ := h143 b hbA hb1 hbΩ Qs hQs
    rcases halt with h1 | h2
    ·
      have hWΔ : W ≤ delta A (lB A) (Subgroup.centralizer ({b} : Set G)) := le_delta hW.1 hWb
      have hcom := commutator_sup_le_pPrimeCoreOf hAc (Subgroup.zpowers_le.mpr hbA)
      rw [centralizer_zpowers148] at hcom
      have hWO : W ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
        rw [hWA]
        exact (Subgroup.commutator_mono (hWΔ.trans h1.le) le_rfl).trans hcom
      exact hcopN _ (coprime_card_pPrimeCoreOf 3 _) (le_normalizer_pPrimeCoreOf 3 _)
        (hcomm _ hWO (le_normalizer_pPrimeCoreOf 3 _))
    ·
      obtain ⟨b', d, Lb', hb', hLb', hJ, hdA, hd1, hdc, -⟩ := h2
      exact hnHJ fun e he => exists_hj_of_hj_point h134 h48 h415 h hb' hLb' hJ hdA hd1 hdc he

end Certs

end Res148BD4

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
