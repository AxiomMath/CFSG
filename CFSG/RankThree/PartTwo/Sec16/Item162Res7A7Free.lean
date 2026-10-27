module

import CFSG.RankThree.PartTwo.Sec16.Item162ResProofConf
import CFSG.RankThree.PartTwo.Sec16.Item162Res7PushA7
import CFSG.RankThree.PartTwo.Sec17.Item17Q0Proof
import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.RankThree.PartTwo.Sec16.Item162Res2ProofSeven

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open CFSG.RankThreeEvenClassification.Helpers
open scoped Pointwise commutatorElement

namespace Res162Seven

variable {G : Type} [Group G] [Finite G]

structure Conf683 (A : Subgroup G) (c : G) (L Y₁ Y₂ S : Subgroup G) (b : G)
    (Lb : Subgroup G) : Prop where
  sec15R : Sec15R G A c L
  maxCE : MaxCE162 A (lB A) Y₁ Y₂ S S
  le_y₁ : L ≤ Y₁
  meets₁ : MeetsY4 A (lB A) L Y₁
  a7₁ : Nonempty (↥Y₁ ⧸ CFSG.pCore 2 ↥Y₁ ≃* alternatingGroup (Fin 7))
  ne : Y₂ ≠ Y₁
  omega_b : Subgroup.zpowers b ∈ omegaA A
  lA_b : Lb ∈ lA A b
  ne_c : Subgroup.zpowers b ≠ Subgroup.zpowers c
  meets₂ : MeetsY4 A (lB A) Lb Y₂
  a7₂ : Nonempty (↥Y₂ ⧸ CFSG.pCore 2 ↥Y₂ ≃* alternatingGroup (Fin 7))
  sc₂ : Late.sectionCentralizer A Y₂ (CFSG.Open.pCoreOf 2 Y₂) = (Subgroup.zpowers b : Set G)
  free : CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) ⊓ Subgroup.normalizer (Subgroup.zpowers b : Set G) = ⊥
  centralizer_le : S ⊓ Subgroup.centralizer ({b} : Set G) ≤ Y₂ ⊓ Lb
  item153 : Item153Main A (lB A)
  claim153Normal : Claim153Normal A (lB A)
  item1444 : Item1444 A (lB A)
  item146 : Item146 A (lB A)
  bot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥
  concl142 : Concl142 A (lB A)

theorem pCoreOf_le_of_cover {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    (h1444 : Item1444 A (lB A)) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (h142 : Concl142 A (lB A)) {K S : Subgroup G}
    (hK : K ∈ scriptY4 A (lB A))
    (hS : S ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (K : Set G)) (piOf 2))
    (hcov : K = (K ⊓ L) ⊔ CFSG.Open.pCoreOf 2 K) : CFSG.Open.pCoreOf 2 K ≤ S :=
  Proof162.pCoreOf_le_of_mem_scriptQ h.isE27 h146 hS
    (Sec17.Proof17Q0.pCoreOf_mem_scriptQ_of_cover h h1444 h146 hbot h142 hK (Or.inl hcov))

namespace Conf683

variable {A : Subgroup G} {c : G} {L Y₁ Y₂ S : Subgroup G} {b : G} {Lb : Subgroup G}

theorem sec15R_b (h : Conf683 A c L Y₁ Y₂ S b Lb) : Sec15R G A b Lb :=
  sec15R_of_point h.sec15R h.omega_b h.lA_b

theorem cover₁ (h : Conf683 A c L Y₁ Y₂ S b Lb) : Y₁ = (Y₁ ⊓ L) ⊔ CFSG.Open.pCoreOf 2 Y₁ := by
  have hcov := Res162b.eq_top_of_seven h.sec15R h.maxCE.1.mem₁ h.meets₁ h.a7₁.some
  exact Res162.eq_sup_of_forall_mem fun y hy => by
    obtain ⟨d, hd, hdy⟩ := hcov y hy
    exact ⟨d, ⟨hd.2, hd.1⟩, hdy⟩

theorem cover₂ (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    Y₂ = (Y₂ ⊓ Lb) ⊔ CFSG.Open.pCoreOf 2 Y₂ := by
  have hcov := Res162b.eq_top_of_seven h.sec15R_b h.maxCE.1.mem₂ h.meets₂ h.a7₂.some
  exact Res162.eq_sup_of_forall_mem fun y hy => by
    obtain ⟨d, hd, hdy⟩ := hcov y hy
    exact ⟨d, ⟨hd.2, hd.1⟩, hdy⟩

theorem sc₁ (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    Late.sectionCentralizer A Y₁ (CFSG.Open.pCoreOf 2 Y₁) = (Subgroup.zpowers c : Set G) :=
  Res162.sectionCentralizer_eq_zpowers_of_meetsY4 h.sec15R h.maxCE.1.mem₁ h.meets₁ h.a7₁.some

theorem pCoreOf_le₁ (h : Conf683 A c L Y₁ Y₂ S b Lb) : CFSG.Open.pCoreOf 2 Y₁ ≤ S :=
  pCoreOf_le_of_cover h.sec15R.toSec14Std h.item1444 h.item146 h.bot h.concl142
    h.maxCE.1.mem₁.prop.1 h.maxCE.1.s₁ (cover₁ h)

theorem pCoreOf_le₂ (h : Conf683 A c L Y₁ Y₂ S b Lb) : CFSG.Open.pCoreOf 2 Y₂ ≤ S :=
  pCoreOf_le_of_cover h.sec15R_b.toSec14Std h.item1444 h.item146 h.bot h.concl142
    h.maxCE.1.mem₂.prop.1 h.maxCE.1.s₂ (cover₂ h)

theorem inf_inf_R_eq_bot (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    (Y₂ ⊓ Lb) ⊓ CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) = ⊥ := by
  rw [eq_bot_iff, ← h.free]
  exact le_inf inf_le_right ((inf_le_left.trans inf_le_right).trans
    (h.sec15R_b.toSec13Data.le_centralizer.trans
      (centralizer_singleton_le_normalizer_zpowers b)))

theorem commutator_b_mem (h : Conf683 A c L Y₁ Y₂ S b Lb) {x : G} (hx : x ∈ Y₂ ⊔ S) :
    b * x * b⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) := by
  have hZ : Subgroup.center (↥Y₂ ⧸ CFSG.pCore 2 ↥Y₂) = ⊥ := by
    obtain ⟨φ⟩ := h.a7₂
    exact (CFSG.RankThree.PartTwo.KFacts.KS14.a7_facts _ ⟨φ⟩).2.1
  have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp h.omega_b).1
  refine commutator_mem_pCoreOf_sup (isPGroup_of_mem_scriptQPi Nat.prime_two h.maxCE.1.s₂.prop)
    h.maxCE.1.s₂.prop.1.2 hZ ?_ ?_ ?_ hx
  · exact h.maxCE.1.mem₂.prop.1.1.2 hbA
  · exact h.maxCE.1.s₂.prop.1.1.1.2.2 hbA
  · intro y hy
    have hmem : b ∈ Late.sectionCentralizer A Y₂ (CFSG.Open.pCoreOf 2 Y₂) := by
      rw [h.sc₂]
      exact Subgroup.mem_zpowers b
    exact hmem.2 y hy

private theorem sup_inf_R_V_eq (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    S = (S ⊓ CFSG.Open.pCoreOf 2 (Y₂ ⊔ S)) ⊔
      (S ⊓ Subgroup.centralizer ({b} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp h.omega_b).1
  have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two h.maxCE.1.s₂.prop
  have hb3 : IsPGroup 3 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [(zpowers_mem_omegaA_iff.mp h.omega_b).2.1]; norm_num)
  have hS3 : ¬ 3 ∣ Nat.card S := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS2
    rw [hn]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hbS : Subgroup.zpowers b ≤ Subgroup.normalizer (S : Set G) :=
    (Subgroup.zpowers_le.mpr hbA).trans h.maxCE.1.s₂.prop.1.1.1.2.2
  have hCz : Subgroup.centralizer ((Subgroup.zpowers b : Subgroup G) : Set G) =
      Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hfactor : S = ⁅S, Subgroup.zpowers b⁆ ⊔ (S ⊓ Subgroup.centralizer ({b} : Set G)) := by
    have h := coprime_commutator_centralizer_factorization 3 Nat.prime_three
      (Subgroup.zpowers b) S hb3 hS3 hbS
    rwa [hCz] at h
  have hcommS : ⁅S, Subgroup.zpowers b⁆ ≤ S := by
    rw [Subgroup.commutator_comm]
    refine Subgroup.commutator_le.mpr fun k hk s hs => ?_
    exact S.mul_mem ((Subgroup.mem_normalizer_iff.mp (hbS hk) s).mp hs) (S.inv_mem hs)
  have hcommR : ⁅S, Subgroup.zpowers b⁆ ≤ CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) := by
    have hAR : A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) : Set G) :=
      (le_normalizer_sup h.maxCE.1.mem₂.prop.1.1.2 h.maxCE.1.s₂.prop.1.1.1.2.2).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (Y₂ ⊔ S))
    have hbCS : b ∈ commutatorInSubgroup S (CFSG.Open.pCoreOf 2 (Y₂ ⊔ S)) := by
      refine ⟨hAR hbA, fun q hq => ?_⟩
      have h1 : b * q * b⁻¹ * q⁻¹ ∈ CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) :=
        commutator_b_mem h (Subgroup.mem_sup_right hq)
      have e : ⁅q, b⁆ = (b * q * b⁻¹ * q⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact (CFSG.Open.pCoreOf 2 (Y₂ ⊔ S)).inv_mem h1
    have hle : Subgroup.zpowers b ≤ commutatorInSubgroup S (CFSG.Open.pCoreOf 2 (Y₂ ⊔ S)) :=
      Subgroup.zpowers_le.mpr hbCS
    exact Subgroup.commutator_le.mpr fun s hs k hk => (hle hk).2 s hs
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  calc S = ⁅S, Subgroup.zpowers b⁆ ⊔ (S ⊓ Subgroup.centralizer ({b} : Set G)) := hfactor
    _ ≤ (S ⊓ CFSG.Open.pCoreOf 2 (Y₂ ⊔ S)) ⊔
        (S ⊓ Subgroup.centralizer ({b} : Set G)) :=
        sup_le ((le_inf hcommS hcommR).trans le_sup_left) le_sup_right

theorem R_le (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) ≤ S := by
  have hSsup : S = (S ⊓ CFSG.Open.pCoreOf 2 (Y₂ ⊔ S)) ⊔
      (S ⊓ Subgroup.centralizer ({b} : Set G)) := sup_inf_R_V_eq h
  have hnorm : ((S ⊓ CFSG.Open.pCoreOf 2 (Y₂ ⊔ S)).subgroupOf S).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    exact Late.le_normalizer_inf Subgroup.le_normalizer
      (le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y₂ ⊔ S)))
  have hDN : Y₂ ⊓ Lb ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y₂ : Set G) :=
    inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₂)
  intro r hr
  have hdec : r ∈ (Y₂ : Set G) * (S : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left Y₂ S h.maxCE.1.s₂.prop.1.2]
    simpa using (CFSG.LieType.BorelTits.pCoreOf_le 2 (Y₂ ⊔ S)) hr
  obtain ⟨y, hy, s, hs, hys⟩ := hdec
  have hydec : y ∈ ((Y₂ ⊓ Lb : Subgroup G) : Set G) * (CFSG.Open.pCoreOf 2 Y₂ : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (Y₂ ⊓ Lb) _ hDN, ← cover₂ h]
    exact hy
  obtain ⟨d, hd, o, ho, hdo⟩ := hydec
  obtain ⟨t, ht, v, hv, htv⟩ := normal_subgroup_sup_factorization S
    (S ⊓ CFSG.Open.pCoreOf 2 (Y₂ ⊔ S)) (S ⊓ Subgroup.centralizer ({b} : Set G))
    inf_le_left inf_le_left hnorm hSsup (o * s) (S.mul_mem (pCoreOf_le₂ h ho) hs)
  have hrv : r = (d * v) * (v⁻¹ * t * v) := by
    have h1 : r = d * (o * s) := by
      rw [← hys, ← hdo]
      exact mul_assoc d o s
    rw [h1, ← htv]
    group
  have hdvD : d * v ∈ Y₂ ⊓ Lb := (Y₂ ⊓ Lb).mul_mem hd (h.centralizer_le hv)
  have hvR : v⁻¹ * t * v ∈ CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) := by
    have hvN : v ∈ Y₂ ⊔ S := Subgroup.mem_sup_right hv.1
    have h1 := (Subgroup.mem_normalizer_iff.mp
      ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y₂ ⊔ S)) (inv_mem hvN)) t).mp ht.2
    simpa using h1
  have hdvR : d * v ∈ CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) := by
    have h1 : d * v = r * (v⁻¹ * t * v)⁻¹ := by rw [hrv]; group
    rw [h1]
    exact (CFSG.Open.pCoreOf 2 (Y₂ ⊔ S)).mul_mem hr
      ((CFSG.Open.pCoreOf 2 (Y₂ ⊔ S)).inv_mem hvR)
  have hdv1 : d * v = 1 := by
    have hmem : d * v ∈ (Y₂ ⊓ Lb) ⊓ CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) := ⟨hdvD, hdvR⟩
    rw [inf_inf_R_eq_bot h, Subgroup.mem_bot] at hmem
    exact hmem
  rw [hrv, hdv1, one_mul]
  exact S.mul_mem (S.mul_mem (S.inv_mem hv.1) ht.1) hv.1

theorem sup_V_eq (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    (S ⊓ Subgroup.centralizer ({b} : Set G)) ⊔ CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) = S := by
  have hSsup := sup_inf_R_V_eq h
  refine le_antisymm (sup_le inf_le_left (R_le h)) ?_
  calc S = (S ⊓ CFSG.Open.pCoreOf 2 (Y₂ ⊔ S)) ⊔
        (S ⊓ Subgroup.centralizer ({b} : Set G)) := hSsup
    _ ≤ (S ⊓ Subgroup.centralizer ({b} : Set G)) ⊔ CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) :=
        sup_le ((inf_le_right : S ⊓ CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) ≤
          CFSG.Open.pCoreOf 2 (Y₂ ⊔ S)).trans le_sup_right) le_sup_left

theorem V_inf_R (h : Conf683 A c L Y₁ Y₂ S b Lb) :
    (S ⊓ Subgroup.centralizer ({b} : Set G)) ⊓ CFSG.Open.pCoreOf 2 (Y₂ ⊔ S) = ⊥ := by
  rw [eq_bot_iff, ← h.free]
  exact le_inf inf_le_right (inf_le_left.trans (inf_le_right.trans
    (centralizer_singleton_le_normalizer_zpowers b)))

end Conf683

end Res162Seven

end CFSG.RankThree.PartTwo.Sec16
