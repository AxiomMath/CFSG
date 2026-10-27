module

import CFSG.RankThree.PartTwo.Sec17.Item17Q0ProofTools
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec14.Concrete
public import CFSG.RankThree.PartTwo.Sec14.Item1446
public import CFSG.RankThree.PartTwo.Sec15.HypR

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

namespace Proof1518R2

variable {G : Type} [Group G] [Finite G]

theorem le_sup_zpowers_of_isHyperplane {A B : Subgroup G} (hB : IsHyperplane A B) {d : G}
    (hdA : d ∈ A) (hdB : d ∉ B) : A ≤ B ⊔ Subgroup.zpowers d := by
  set H := B ⊔ Subgroup.zpowers d with hH
  have hHA : H ≤ A := sup_le hB.1 (Subgroup.zpowers_le.mpr hdA)
  have hBH : B ≤ H := le_sup_left
  have hdH : d ∈ H := Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hBH
  obtain ⟨j, hj⟩ := Subgroup.card_dvd_of_le hHA
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hkj : k * j = 3 := by
    have h1 : Nat.card B * (k * j) = Nat.card B * 3 := by
      rw [← mul_assoc, ← hk, ← hj, hB.2, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hBpos h1
  have hk1 : k ≠ 1 := by
    rintro rfl
    have hBeq : B = H := Subgroup.eq_of_le_of_card_ge hBH (by rw [hk, mul_one])
    exact hdB (hBeq ▸ hdH)
  have hj1 : j = 1 := by
    have hk3 : k ∣ 3 := ⟨j, hkj.symm⟩
    rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with h1 | h3
    · exact absurd h1 hk1
    · subst h3
      omega
  exact (Subgroup.eq_of_le_of_card_ge hHA (by rw [hj, hj1, mul_one])).ge

theorem mem_centralizer_of_isHyperplane {A B : Subgroup G} (hB : IsHyperplane A B) {d : G}
    (hdA : d ∈ A) (hdB : d ∉ B) {x : G} (hxB : x ∈ Subgroup.centralizer (B : Set G))
    (hxd : x ∈ Subgroup.centralizer ({d} : Set G)) {a : G} (ha : a ∈ A) :
    x ∈ Subgroup.centralizer ({a} : Set G) := by
  have hle : B ⊔ Subgroup.zpowers d ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sup_le (fun b hb => ?_) (Subgroup.zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hxB b hb
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hxd).symm
  have haC := hle (le_sup_zpowers_of_isHyperplane hB hdA hdB ha)
  rw [Subgroup.mem_centralizer_singleton_iff] at haC ⊢
  exact haC.symm

theorem lB_eq_bot_of_forall_not_le1523 {A B : Subgroup G} (hΩ : ∀ F ∈ omegaA A, ¬ F ≤ B) :
    lB A B = ⊥ :=
  lB_eq_bot fun b d L' hc => by
    obtain ⟨hBbd, hb, -⟩ := hc
    refine hΩ _ hb (Subgroup.zpowers_le.mpr ?_)
    rw [hBbd]
    exact Subgroup.subset_closure (Set.mem_insert b _)

theorem inf_centralizer_mem_scriptQ1523 {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec15R G A c L) (h142 : Concl142 A (lB A)) {Y : Subgroup G}
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {d : G} (hdA : d ∈ A)
    (hB : ∀ B : Subgroup G, IsHyperplane A B → d ∈ B → (∀ F ∈ omegaA A, ¬ F ≤ B) →
      CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer (B : Set G) ≤
        pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) :
    CFSG.Open.pCoreOf 2 Y ⊓ Subgroup.centralizer ({d} : Set G) ∈ scriptQ A (lB A) := by
  set Q := CFSG.Open.pCoreOf 2 Y with hQ
  have hA : Late.IsE27 A := h.toSec14Std.isE27
  have hAab : IsMulCommutative A := h.toSec13Data.isElemAbelian.1
  have hcA : c ∈ A := h.toSec13Data.mem_A
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) :=
    hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hAd : A ≤ Subgroup.centralizer ({d} : Set G) := fun a ha => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (congrArg Subtype.val (hAab.is_comm.comm ⟨d, hdA⟩ ⟨a, ha⟩)).symm
  have hQ3 : IsPiSubgroup (piCompl 3) Q := Sec17.Proof17Q0.isPiSubgroup_piCompl_pCoreOf Y
  have hQb : ∀ b : G, Subgroup.zpowers b ∈ omegaA A →
      Q ⊓ Subgroup.centralizer ({b} : Set G) ∈ scriptQ A (lB A) := fun b hb =>
    Sec17.Proof17Q0.inf_centralizer_mem_scriptQ_of_concl142 hA h142 hb hQ3 hAQ
  refine mem_scriptQ_iff.mpr ⟨isPiSubgroup_piCompl_of_le hQ3 inf_le_left,
    Late.le_normalizer_inf hAQ (hAd.trans Subgroup.le_normalizer), fun B hBh => ?_⟩
  by_cases hΩB : ∃ F ∈ omegaA A, F ≤ B
  ·
    obtain ⟨F, hF, hFB⟩ := hΩB
    obtain ⟨-, -, b, hFb, -⟩ := id hF
    subst hFb
    have hbB : b ∈ B := hFB (Subgroup.mem_zpowers b)
    refine le_trans (fun x hx => ?_) ((hQb b hF).2 B hBh)
    have hxB : x ∈ Subgroup.centralizer (B : Set G) := (Subgroup.mem_inf.mp hx).2
    have hxQ : x ∈ Q := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).1
    have hxb : x ∈ Subgroup.centralizer ({b} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hxB b hbB).symm
    exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxQ, hxb⟩, hxB⟩
  · simp only [not_exists, not_and] at hΩB
    by_cases hdB : d ∈ B
    · refine (inf_le_inf_right _ inf_le_left).trans ((hB B hBh hdB hΩB).trans ?_)
      exact le_sup_left
    ·
      refine le_trans (fun x hx => ?_) ((hQb c h.toSec13Data.zpowers_mem_omegaA).2 B hBh)
      have hxB : x ∈ Subgroup.centralizer (B : Set G) := (Subgroup.mem_inf.mp hx).2
      have hxQd := Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr
        ⟨hxQd.1, mem_centralizer_of_isHyperplane hBh hdA hdB hxB hxQd.2 hcA⟩, hxB⟩

end Proof1518R2

open Proof1518R2

end CFSG.RankThree.PartTwo.Sec15
