module

public import CFSG.LocalAnalysis.OddStandard.AltStdSmall4FusP42Data
import Mathlib.GroupTheory.Perm.DomMulAct
import Mathlib.Tactic.FinCases

public section

namespace CertificateChecks.Batch36404

open Equiv CFSG.OddStandard.AltStdSmall4.Fus.P42

private def blk (x : Fin 9) : Fin 3 := ⟨x.val / 4, by have := x.2; omega⟩

private def sw : Fin 3 → Fin 3 := ![1, 0, 2]

private def τ : Perm (Fin 9) := swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7

private def pt (j : Fin 4) (u : Fin 4) : Fin 9 := ⟨4 * (j.val / 2) + u.val, by omega⟩

private def pi (j : Fin 4) : Fin 4 → Fin 4 := ![![1, 0, 3, 2], ![2, 3, 0, 1], ![1, 0, 3, 2], ![2, 3, 0, 1]] j

private theorem fin9 : ∀ x : Fin 9, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨
    x = 7 ∨ x = 8 := by decide

private theorem bFun_blk : ∀ (k : Fin 16) (x : Fin 9), blk (bFun k x) = blk x := by decide

private theorem eq_eight_of_blk : ∀ y : Fin 9, blk y = 2 → y = 8 := by decide

private theorem blk_tau : ∀ y : Fin 9, blk (τ y) = sw (blk y) := by decide

private theorem blk_swap01 : ∀ y : Fin 9, blk (swap 0 1 y) = blk y := by decide

private theorem sw_sw : ∀ c : Fin 3, sw (sw c) = c := by decide

private theorem sw_inj : ∀ c d : Fin 3, sw c = sw d → c = d := by decide

private theorem tau_mul_tau : τ * τ = 1 := by decide

private theorem sign_tau : Perm.sign τ = 1 := by
  simp only [τ, Perm.sign_mul, Perm.sign_swap']
  decide

private theorem bIdx_bEl' : ∀ k : Fin 16, bIdx (bEl k) = k := by decide

private theorem bEl_injective' : Function.Injective bEl := fun k l h => by
  rw [← bIdx_bEl' k, ← bIdx_bEl' l, h]

private theorem gen_pt : ∀ (j u : Fin 4), bGen j (pt j u) = pt j (pi j u) := by decide

private theorem gen_off : ∀ (j : Fin 4) (y : Fin 9),
    (∃ u, y = pt j u) ∨ (bGen j y = y ∧ blk y ≠ blk (pt j 0)) := by decide

private theorem pt_ne : ∀ j : Fin 4, pt j 0 ≠ pt j 1 ∧ pt j 0 ≠ pt j 2 ∧ pt j 0 ≠ pt j 3 ∧
    pt j 1 ≠ pt j 2 ∧ pt j 1 ≠ pt j 3 ∧ pt j 2 ≠ pt j 3 := by decide

private theorem pt_blk : ∀ (j u : Fin 4), blk (pt j u) = blk (pt j 0) := by decide

private theorem pt_blk_ne : ∀ j : Fin 4, blk (pt j 0) ≠ 2 ∧ sw (blk (pt j 0)) ≠ 2 := by decide

private theorem vec4 (f : Fin 4 → Fin 9) : ∀ u : Fin 4, ![f 0, f 1, f 2, f 3] u = f u := by
  intro u; fin_cases u <;> rfl

private theorem core : ∀ a0 a1 a2 a3 : Fin 9, a0 ≠ a1 → a0 ≠ a2 → a0 ≠ a3 → a1 ≠ a2 →
    a1 ≠ a3 → a2 ≠ a3 → blk a1 = blk a0 → blk a2 = blk a0 → blk a3 = blk a0 → blk a0 ≠ 2 →
    ∀ j : Fin 4, ∃ l : Fin 16, (∀ u : Fin 4, ![a0, a1, a2, a3] (pi j u) =
      bFun l (![a0, a1, a2, a3] u)) ∧ ∀ z : Fin 9, blk z ≠ blk a0 → bFun l z = z := by
  decide +kernel

private def Q (σ : Perm (Fin 9)) : Prop :=
  (∀ x, blk (σ x) = blk x) ∨ (∀ x, blk (σ x) = sw (blk x))

private theorem blocks_of (a b : Fin 3) (ha : a ≠ 2) (hb : b ≠ 2) (hab : a ≠ b) :
    (∀ x, ![a, a, a, a, b, b, b, b, 2] x = blk x) ∨
      (∀ x, ![a, a, a, a, b, b, b, b, 2] x = sw (blk x)) := by
  revert a b; decide

private theorem card_block_le : ∀ c : Fin 3,
    (Finset.univ.filter fun y : Fin 9 => blk y = c).card ≤ 4 := by decide

private theorem Q_of_normB {σ : Perm (Fin 9)} (h : normB σ = true) : Q σ ∧ Perm.sign σ = 1 := by
  simp only [normB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h8, hc⟩, hs⟩ := h
  refine ⟨?_, hs⟩
  have rel : ∀ j y, blk (σ (bGen j y)) = blk (σ y) := by
    intro j y
    have := DFunLike.congr_fun (hc j) (σ y)
    simp only [Perm.mul_apply, Perm.inv_def, Equiv.symm_apply_apply] at this
    rw [this]
    exact bFun_blk _ _
  have h1 := rel 0 0
  have h2 := rel 1 0
  have h3 := rel 0 2
  have h5 := rel 2 4
  have h6 := rel 3 4
  have h7 := rel 2 6
  rw [show bGen 0 0 = 1 by decide] at h1
  rw [show bGen 1 0 = 2 by decide] at h2
  rw [show bGen 0 2 = 3 by decide] at h3
  rw [show bGen 2 4 = 5 by decide] at h5
  rw [show bGen 3 4 = 6 by decide] at h6
  rw [show bGen 2 6 = 7 by decide] at h7
  have hv : ∀ x, blk (σ x) = ![blk (σ 0), blk (σ 0), blk (σ 0), blk (σ 0), blk (σ 4), blk (σ 4),
      blk (σ 4), blk (σ 4), 2] x := by
    intro x
    rcases fin9 x with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rfl
    · exact h1
    · exact h2
    · exact h3.trans h2
    · rfl
    · exact h5
    · exact h6
    · exact h7.trans h6
    · change blk (σ 8) = 2
      rw [h8]; rfl
  have hne : ∀ x : Fin 9, x ≠ 8 → blk (σ x) ≠ 2 := by
    intro x hx h
    exact hx (σ.injective ((eq_eight_of_blk _ h).trans h8.symm))
  have hab : blk (σ 0) ≠ blk (σ 4) := by
    intro hab
    have hsub : (({0, 1, 2, 3, 4} : Finset (Fin 9)).image σ) ⊆
        Finset.univ.filter fun y : Fin 9 => blk y = blk (σ 0) := by
      intro y hy
      simp only [Finset.mem_image, Finset.mem_insert, Finset.mem_singleton] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · rfl
      · exact h1
      · exact h2
      · exact h3.trans h2
      · exact hab.symm
    have hc5 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ σ.injective] at hc5
    have := card_block_le (blk (σ 0))
    have h5' : ({0, 1, 2, 3, 4} : Finset (Fin 9)).card = 5 := by decide
    omega
  rcases blocks_of _ _ (hne 0 (by decide)) (hne 4 (by decide)) hab with h | h
  · exact Or.inl fun x => (hv x).trans (h x)
  · exact Or.inr fun x => (hv x).trans (h x)

private theorem conj_of_Q {σ : Perm (Fin 9)} (hQ : Q σ) (j : Fin 4) :
    ∃ l, σ * bGen j * σ⁻¹ = bEl l := by
  have hb : ∀ u, blk (σ (pt j u)) = blk (σ (pt j 0)) := by
    intro u
    rcases hQ with h | h
    · rw [h, h, pt_blk]
    · rw [h, h, pt_blk]
  have hb2 : blk (σ (pt j 0)) ≠ 2 := by
    rcases hQ with h | h
    · rw [h]; exact (pt_blk_ne j).1
    · rw [h]; exact (pt_blk_ne j).2
  obtain ⟨n01, n02, n03, n12, n13, n23⟩ := pt_ne j
  obtain ⟨l, hl1, hl2⟩ := core _ _ _ _ (σ.injective.ne n01) (σ.injective.ne n02)
    (σ.injective.ne n03) (σ.injective.ne n12) (σ.injective.ne n13) (σ.injective.ne n23)
    (hb 1) (hb 2) (hb 3) hb2 j
  simp only [vec4 (fun u => σ (pt j u))] at hl1
  refine ⟨l, Equiv.ext fun z => ?_⟩
  obtain ⟨y, rfl⟩ := σ.surjective z
  simp only [Perm.mul_apply, Perm.inv_def, Equiv.symm_apply_apply]
  change σ (bGen j y) = bFun l (σ y)
  rcases gen_off j y with ⟨u, rfl⟩ | ⟨hg, hy⟩
  · rw [gen_pt, hl1]
  · rw [hg, hl2]
    intro h
    apply hy
    rcases hQ with hQ | hQ
    · rwa [hQ, hQ] at h
    · rw [hQ, hQ] at h
      exact sw_inj _ _ h

private theorem normB_of_Q {σ : Perm (Fin 9)} (hQ : Q σ) (hs : Perm.sign σ = 1) :
    normB σ = true := by
  simp only [normB, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨?_, fun j => ?_⟩, hs⟩
  · apply eq_eight_of_blk
    rcases hQ with h | h
    · rw [h]; rfl
    · rw [h]; rfl
  · obtain ⟨l, hl⟩ := conj_of_Q hQ j
    rw [hl, bIdx_bEl']

private theorem normB_iff (σ : Perm (Fin 9)) :
    normB σ = true ↔ ((∀ x, blk (σ x) = blk x) ∧ Perm.sign σ = 1) ∨
      ((∀ x, blk (σ x) = sw (blk x)) ∧ Perm.sign σ = 1) := by
  rw [← or_and_right]
  exact ⟨Q_of_normB, fun h => normB_of_Q h.1 h.2⟩

private theorem card_block :
    (Finset.univ.filter fun σ : Perm (Fin 9) => ∀ x, blk (σ x) = blk x).card = 576 := by
  have h := DomMulAct.stabilizer_card blk
  rw [Fintype.card_subtype] at h
  have e : ∏ i : Fin 3, (Fintype.card {a // blk a = i}).factorial = 576 := by decide
  rw [e] at h
  rw [← h]
  exact congrArg Finset.card (Finset.filter_congr fun σ _ => funext_iff.symm)

private theorem sign_swap01_mul (σ : Perm (Fin 9)) :
    Perm.sign (swap 0 1 * σ) = -Perm.sign σ := by
  rw [Perm.sign_mul, Perm.sign_swap (by decide), neg_one_mul]

private def s0 : Finset (Perm (Fin 9)) := Finset.univ.filter fun σ => ∀ x, blk (σ x) = blk x

private def s1 : Finset (Perm (Fin 9)) := Finset.univ.filter fun σ => ∀ x, blk (σ x) = sw (blk x)

private theorem units_neg_one_ne_one : (-1 : ℤˣ) ≠ 1 := by decide

private theorem card_split_gen (A : Finset (Perm (Fin 9))) :
    (A.filter fun σ => Perm.sign σ = 1).card + (A.filter fun σ => ¬Perm.sign σ = 1).card =
      A.card :=
  Finset.card_filter_add_card_filter_not _

private theorem card_split : (s0.filter fun σ => Perm.sign σ = 1).card +
    (s0.filter fun σ => ¬Perm.sign σ = 1).card = 576 :=
  (card_split_gen s0).trans card_block

private theorem mapsTo_even : ∀ σ ∈ s0.filter (fun σ => Perm.sign σ = 1),
    swap 0 1 * σ ∈ s0.filter (fun σ => ¬Perm.sign σ = 1) := by
  intro σ hσ
  simp only [s0, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
  refine ⟨fun x => ?_, ?_⟩
  · rw [Perm.mul_apply, blk_swap01, hσ.1]
  · rw [sign_swap01_mul, hσ.2]
    exact units_neg_one_ne_one

private theorem mapsTo_odd : ∀ σ ∈ s0.filter (fun σ => ¬Perm.sign σ = 1),
    swap 0 1 * σ ∈ s0.filter (fun σ => Perm.sign σ = 1) := by
  intro σ hσ
  simp only [s0, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
  refine ⟨fun x => ?_, ?_⟩
  · rw [Perm.mul_apply, blk_swap01, hσ.1]
  · rw [sign_swap01_mul]
    rcases Int.units_eq_one_or (Perm.sign σ) with h | h
    · exact absurd h hσ.2
    · rw [h, neg_neg]

private theorem card_even_odd : (s0.filter fun σ => Perm.sign σ = 1).card =
    (s0.filter fun σ => ¬Perm.sign σ = 1).card :=
  Finset.card_nbij' (fun σ => swap 0 1 * σ) (fun σ => swap 0 1 * σ) mapsTo_even mapsTo_odd
    (fun σ _ => by simp only [← mul_assoc, swap_mul_self, one_mul])
    (fun σ _ => by simp only [← mul_assoc, swap_mul_self, one_mul])

private theorem card_block_even : (s0.filter fun σ => Perm.sign σ = 1).card = 288 := by
  have h1 := card_split
  have h2 := card_even_odd
  omega

private theorem card_swap_even : (s1.filter fun σ => Perm.sign σ = 1).card = 288 := by
  rw [← card_block_even]
  refine Finset.card_nbij' (fun σ => τ * σ) (fun σ => τ * σ) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [s0, s1, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    refine ⟨fun x => ?_, ?_⟩
    · rw [Perm.mul_apply, blk_tau, hσ.1, sw_sw]
    · rw [Perm.sign_mul, sign_tau, hσ.2, one_mul]
  · intro σ hσ
    simp only [s0, s1, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
    refine ⟨fun x => ?_, ?_⟩
    · rw [Perm.mul_apply, blk_tau, hσ.1]
    · rw [Perm.sign_mul, sign_tau, hσ.2, one_mul]
  · intro σ _
    simp only [← mul_assoc, tau_mul_tau, one_mul]
  · intro σ _
    simp only [← mul_assoc, tau_mul_tau, one_mul]

private theorem card_normB :
    (Finset.univ.filter fun σ : Perm (Fin 9) => normB σ = true).card = 576 := by
  have e : (Finset.univ.filter fun σ : Perm (Fin 9) => normB σ = true) =
      (s0.filter fun σ => Perm.sign σ = 1) ∪ (s1.filter fun σ => Perm.sign σ = 1) := by
    ext σ
    simp only [s0, s1, Finset.mem_filter, Finset.mem_union, Finset.mem_univ, true_and,
      normB_iff]
  rw [e, Finset.card_union_of_disjoint, card_block_even, card_swap_even]
  rw [Finset.disjoint_left]
  intro σ h1 h2
  simp only [s0, s1, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
  have := (h1.1 0).symm.trans (h2.1 0)
  exact absurd this (by decide)

private theorem det : ∀ a b : Fin 9, (∀ x y : Fin 9, ![a, bGen 0 a, bGen 1 a, bGen 0 (bGen 1 a),
    b, bGen 2 b, bGen 3 b, bGen 2 (bGen 3 b), 8] x = ![a, bGen 0 a, bGen 1 a,
      bGen 0 (bGen 1 a), b, bGen 2 b, bGen 3 b, bGen 2 (bGen 3 b), 8] y → x = y) →
    ∀ x, ![a, bGen 0 a, bGen 1 a, bGen 0 (bGen 1 a), b, bGen 2 b, bGen 3 b,
      bGen 2 (bGen 3 b), 8] x = bFun ⟨a.val % 4 + 4 * (b.val % 4), by omega⟩ x := by
  decide +kernel

private theorem sign_bEl : ∀ k : Fin 16, Perm.sign (bEl k) = 1 := by decide +kernel

private theorem centB_iff (σ : Perm (Fin 9)) : centB σ = true ↔ ∃ k, bEl k = σ := by
  constructor
  · intro h
    simp only [centB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h8, hc⟩, -⟩ := h
    have rel : ∀ j y, σ (bGen j y) = bGen j (σ y) := fun j y => by
      simpa only [Perm.mul_apply] using DFunLike.congr_fun (hc j) y
    have hv : ∀ x, σ x = ![σ 0, bGen 0 (σ 0), bGen 1 (σ 0), bGen 0 (bGen 1 (σ 0)), σ 4,
        bGen 2 (σ 4), bGen 3 (σ 4), bGen 2 (bGen 3 (σ 4)), 8] x := by
      intro x
      rcases fin9 x with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rfl
      · exact (congrArg σ (show (1 : Fin 9) = bGen 0 0 by decide)).trans (rel 0 0)
      · exact (congrArg σ (show (2 : Fin 9) = bGen 1 0 by decide)).trans (rel 1 0)
      · exact ((congrArg σ (show (3 : Fin 9) = bGen 0 (bGen 1 0) by decide)).trans
          (rel 0 _)).trans (congrArg (bGen 0) (rel 1 0))
      · rfl
      · exact (congrArg σ (show (5 : Fin 9) = bGen 2 4 by decide)).trans (rel 2 4)
      · exact (congrArg σ (show (6 : Fin 9) = bGen 3 4 by decide)).trans (rel 3 4)
      · exact ((congrArg σ (show (7 : Fin 9) = bGen 2 (bGen 3 4) by decide)).trans
          (rel 2 _)).trans (congrArg (bGen 2) (rel 3 4))
      · exact h8
    refine ⟨⟨(σ 0).val % 4 + 4 * ((σ 4).val % 4), by omega⟩, Equiv.ext fun x => ?_⟩
    rw [hv x]
    refine (det _ _ (fun x y hxy => σ.injective ?_) x).symm
    rw [hv x, hv y]
    exact hxy
  · rintro ⟨k, rfl⟩
    have h8 : ∀ k : Fin 16, bEl k 8 = 8 := by decide
    have hc : ∀ (k : Fin 16) (j : Fin 4), bEl k * bGen j = bGen j * bEl k := by decide
    simp only [centB, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨h8 k, hc k⟩, sign_bEl k⟩

private theorem card_centB :
    (Finset.univ.filter fun σ : Perm (Fin 9) => centB σ = true).card = 16 := by
  have : (Finset.univ.filter fun σ : Perm (Fin 9) => centB σ = true) =
      Finset.univ.image bEl := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, centB_iff]
  rw [this, Finset.card_image_of_injective _ bEl_injective']
  rfl

private theorem p42Check_36404 : p42Check () = true := by
  unfold p42Check
  rw [card_normB, card_centB]
  rfl

end CertificateChecks.Batch36404

namespace Certificates

open CertificateChecks

theorem certificate36404 : CFSG.OddStandard.AltStdSmall4.Fus.P42.p42Check () = true :=
  CertificateChecks.Batch36404.p42Check_36404

end Certificates
