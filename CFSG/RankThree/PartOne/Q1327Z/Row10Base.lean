module

public import CFSG.RankThree.PartOne.Q1327Z.Block
public import CFSG.RankThree.PartOne.S13K.Sp6Reps

public section

namespace CFSG.RankThree.PartOne.Q1327Z

open CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.KFQ

section Abstract

variable {Γ : Type*} [Group Γ]

theorem exists_noncomm_of_quasisimple {B : Subgroup Γ} (hq : CFSG.IsQuasisimple ↥B)
    (hZ : Subgroup.center ↥B = ⊥) {l : Γ} (hl : l ∈ B) (hl1 : l ≠ 1) :
    ∃ y ∈ B, ¬ Commute l (y * l * y⁻¹) := by
  have : IsSimpleGroup (↥B ⧸ Subgroup.center ↥B) := hq.2.1
  have hS : IsSimpleGroup ↥B :=
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.isSimpleGroup
  have hperf : ⁅B, B⁆ = B := Subgroup.isPerfect_iff.mp hq.1
  have hne : B ≠ ⊥ := fun h => hl1 (by simpa [h] using hl)
  refine exists_noncomm_of_simple (fun N hNB hN => ?_) hperf hne hl hl1
  have : (N.subgroupOf B).Normal := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf B) with h | h
  · left
    rw [Subgroup.subgroupOf_eq_bot] at h
    have h1 : N ⊓ B = ⊥ := disjoint_iff.mp h
    rwa [inf_eq_left.mpr hNB] at h1
  · right
    rw [Subgroup.subgroupOf_eq_top] at h
    exact le_antisymm hNB h

end Abstract

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

theorem exists_card_eq_pow (hK : 4 ≤ Nat.card K) : ∃ f : ℕ, Nat.card K = 2 ^ f ∧ 2 ≤ f := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  refine ⟨n, by rw [Nat.card_eq_fintype_card]; exact hn, ?_⟩
  by_contra hlt
  push Not at hlt
  have : (n : ℕ) = 1 := by have := n.pos; omega
  rw [Nat.card_eq_fintype_card, hn, this] at hK
  omega

theorem sBlk_noncomm (hK : 4 ≤ Nat.card K) {l : ↥(M10 K)} (hl : l ∈ sBlk K) (hl1 : l ≠ 1) :
    ∃ y ∈ sBlk K, ¬ Commute l (y * l * y⁻¹) := by
  obtain ⟨f, hf, hf2⟩ := exists_card_eq_pow hK
  obtain ⟨hq, hZ, -⟩ := sBlk_model hf hf2
  exact exists_noncomm_of_quasisimple hq hZ hl hl1

theorem dBlk_noncomm (hK : 4 ≤ Nat.card K) {l : ↥(M10 K)} (hl : l ∈ dBlk K) (hl1 : l ≠ 1) :
    ∃ y ∈ dBlk K, ¬ Commute l (y * l * y⁻¹) := by
  obtain ⟨f, hf, hf2⟩ := exists_card_eq_pow hK
  obtain ⟨hq, hZ, -⟩ := dBlk_model hf hf2
  exact exists_noncomm_of_quasisimple hq hZ hl hl1

theorem tor10_mem_sBlk (hpq : p ∣ Nat.card K + 1) {x : Fin 3 → (Qext K)ˣ}
    (hx : ∀ i, x i ^ p = 1) (h1 : x 1 = 1) (h2 : x 2 = 1) : tor10 hpq x hx ∈ sBlk K := by
  intro a
  refine ⟨?_, ?_⟩
  · change torusEquiv x (sg 1 a) = sg 1 a
    rw [torusEquiv_sg, h1, Units.val_one, one_mul]
  · change torusEquiv x (sg 2 a) = sg 2 a
    rw [torusEquiv_sg, h2, Units.val_one, one_mul]

theorem tor10_mem_dBlk (hpq : p ∣ Nat.card K + 1) {x : Fin 3 → (Qext K)ˣ}
    (hx : ∀ i, x i ^ p = 1) (h2 : x 2 = 1) (h01 : x 0 * x 1 = 1) : tor10 hpq x hx ∈ dBlk K := by
  refine ⟨fun a => ?_, ⟨fun u hu => ?_, fun c u _ => ?_⟩, ?_⟩
  · change torusEquiv x (sg 2 a) = sg 2 a
    rw [torusEquiv_sg, h2, Units.val_one, one_mul]
  · change torusEquiv x u 2 = 0
    rw [torusEquiv_apply, hu, mul_zero]
  · change torusEquiv x (c • u) = c • torusEquiv x u
    funext i
    simp only [torusEquiv_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · change (dMat (torusEquiv x)).det = 1
    have h01' : ((x 0 : (Qext K)ˣ) : Qext K) * ((x 1 : (Qext K)ˣ) : Qext K) = 1 := by
      rw [← Units.val_mul, h01, Units.val_one]
    simp only [dMat, torusEquiv_apply, Matrix.det_fin_two_of]
    simp [sg, h01']

end CFSG.RankThree.PartOne.Q1327Z
