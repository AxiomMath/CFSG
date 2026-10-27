module

import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec14.Item1446
public import CFSG.RankThree.PartTwo.Sec15.Notation
public import CFSG.RankThree.PartTwo.Sec16.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

namespace Proof176

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {LB : Subgroup G → Subgroup G}

theorem mem_scriptQ_of_forall_centralizer (hA : IsE27 A) {B₀ Y : Subgroup G}
    (hB₀ : IsHyperplane A B₀) (hY : Y ∈ invariantPiSubgroups ⊤ A (piCompl 3))
    (h : ∀ e ∈ B₀, e ≠ 1 → Y ⊓ Subgroup.centralizer ({e} : Set G) ∈ scriptQ A LB) :
    Y ∈ scriptQ A LB := by
  refine mem_scriptQ_iff.mpr ⟨hY.2.1, hY.2.2, fun B hB => ?_⟩
  have hcomm : ∀ x ∈ B, ∀ y ∈ B₀, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨x, hB.1 hx⟩ ⟨y, hB₀.1 hy⟩)
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute B B₀ hcomm
  have hB9 : Nat.card B = 9 := by have := hB.2; rw [hA.2] at this; omega
  have hB₀9 : Nat.card B₀ = 9 := by have := hB₀.2; rw [hA.2] at this; omega
  have hsup : Nat.card (B ⊔ B₀ : Subgroup G) ≤ 27 :=
    hA.2 ▸ Subgroup.card_le_of_le (sup_le hB.1 hB₀.1)
  have hinf : B ⊓ B₀ ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot, mul_one, hB9, hB₀9] at hcard
    omega
  obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hinf
  have he1' : e ≠ 1 := fun h1 => he1 (Subtype.ext h1)
  have hCB : Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer ({e} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr he.1)
  have hle : Y ⊓ Subgroup.centralizer (B : Set G) ≤
      (Y ⊓ Subgroup.centralizer ({e} : Set G)) ⊓ Subgroup.centralizer (B : Set G) :=
    le_inf (le_inf inf_le_left (inf_le_right.trans hCB)) inf_le_right
  exact hle.trans ((h e he.2 he1').2 B hB)

theorem mem_scriptQ_of_le_centralizer (h142 : Concl142 A LB) {a : G}
    (ha : Subgroup.zpowers a ∈ omegaA A) {X : Subgroup G} (hX3 : ¬ 3 ∣ Nat.card X)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) (hXa : X ≤ Subgroup.centralizer ({a} : Set G)) :
    X ∈ scriptQ A LB := by
  have hXN : X ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers a : Set G)) A
      (piCompl 3) :=
    ⟨hXa.trans (centralizer_singleton_le_normalizer_zpowers a),
      (isPiSubgroup_piCompl_iff Nat.prime_three X).mpr hX3, hAX⟩
  obtain ⟨Q', hQ', hXQ'⟩ := exists_le_mem_maxInvariantPiSubgroups hXN
  exact mem_scriptQ_of_le (h142 a ha Q' hQ').1 hXQ' hAX

omit [Finite G] in
theorem sup_mem_scriptQ (h1443 : Item1443 A LB) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1)
    {P₁ P₂ : Subgroup G} (hP₁ : P₁ ∈ scriptQ A LB) (hP₂ : P₂ ∈ scriptQ A LB)
    (hP₁a : P₁ ≤ Subgroup.centralizer ({a} : Set G))
    (hP₂a : P₂ ≤ Subgroup.centralizer ({a} : Set G))
    (hP : P₁ ⊔ P₂ ∈ invariantPiSubgroups ⊤ A (piCompl 3)) : P₁ ⊔ P₂ ∈ scriptQ A LB := by
  have hS : ({P₁, P₂} : Set (Subgroup G)) ⊆
      collectionIn (scriptQ A LB) (Subgroup.centralizer {a}) := by
    rintro X (rfl | rfl)
    · exact ⟨hP₁, hP₁a⟩
    · exact ⟨hP₂, hP₂a⟩
  have h := h1443 a ha ha1 _ hS (by rw [sSup_pair]; exact hP)
  rw [sSup_pair] at h
  exact h.1

theorem eq_commutator_sup (hA : IsE27 A) {b : G} (hb : b ∈ A) {X : Subgroup G}
    (hX3 : ¬ 3 ∣ Nat.card X) (hAX : A ≤ Subgroup.normalizer (X : Set G)) :
    X = ⁅X, Subgroup.zpowers b⁆ ⊔ (X ⊓ Subgroup.centralizer ({b} : Set G)) := by
  have h := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
    3 Nat.prime_three (Subgroup.zpowers b) X (hA.isPGroup.to_le (Subgroup.zpowers_le.mpr hb)) hX3
    (Subgroup.zpowers_le.mpr (hAX hb))
  rwa [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
    ← Subgroup.zpowers_eq_closure] at h

omit [Finite G] in
theorem commutator_le_left {b : G} (hb : b ∈ A) {X : Subgroup G}
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) : ⁅X, Subgroup.zpowers b⁆ ≤ X :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr (hAX hb))

omit [Finite G] in
theorem le_normalizer_zpowers (hA : IsE27 A) {b : G} (hb : b ∈ A) :
    A ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := fun a ha =>
  centralizer_singleton_le_normalizer_zpowers b (Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)))

omit [Finite G] in
theorem le_normalizer_centralizer (hA : IsE27 A) {b : G} (hb : b ∈ A) :
    A ≤ Subgroup.normalizer (Subgroup.centralizer ({b} : Set G) : Set G) := fun a ha =>
  Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hA.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)))

omit [Finite G] in
theorem mem_invariantPiSubgroups_of_le {X Y : Subgroup G} (hY3 : ¬ 3 ∣ Nat.card Y) (hXY : X ≤ Y)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) :
    X ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
  ⟨le_top, (isPiSubgroup_piCompl_iff Nat.prime_three X).mpr fun h3 =>
    hY3 (h3.trans (Subgroup.card_dvd_of_le hXY)), hAX⟩

omit [Finite G] in
theorem bot_mem_scriptQ : (⊥ : Subgroup G) ∈ scriptQ A LB := by
  refine mem_scriptQ_iff.mpr ⟨fun q hq => ?_, fun a _ => ?_, fun B _ => inf_le_left.trans bot_le⟩
  · rw [Subgroup.card_bot] at hq
    exact absurd (Nat.le_of_dvd one_pos hq) (by have := q.2.two_le; omega)
  · rw [Subgroup.normalizer_eq_top ⊥]
    exact Subgroup.mem_top a

end Proof176

end CFSG.RankThree.PartTwo.Sec17
