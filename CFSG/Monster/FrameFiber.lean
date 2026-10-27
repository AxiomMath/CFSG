module

public import CFSG.Monster.CodeLatticeUnimodular
public import CFSG.Monster.Code.Weights

public section

namespace CFSG.Monster

open Code

theorem mogCode_allOnes_mem : allOnes ∈ Code.C := Code.Ω_mem_C

private theorem sum_bitLift_eq (d : Fin 24 → ZMod 2) :
    ∑ i, bitLift (d i) = (hammingNorm d : ℤ) := by
  rw [hammingNorm_eq_sum_val]
  push_cast
  rfl

theorem mogCode_weight_emod_four : ∀ d ∈ Code.C, weight d % 4 = 0 := by
  intro d hd
  rw [weight, sum_bitLift_eq]
  obtain ⟨k, hk⟩ := four_dvd_wt hd
  rw [hk]
  push_cast
  omega

theorem two_allOnes_mem_codeLattice : (fun _ => (2 : ℤ)) ∈ codeLattice Code.C := by
  refine ⟨0, .inl rfl, Code.Ω, Code.Ω_mem_C, fun i => ?_, ?_⟩
  · rfl
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, mul_zero]
    decide

@[expose] noncomputable def frameClass : codeLatticeModTwo Code.C mogCode_allOnes_mem :=
  Submodule.Quotient.mk (⟨fun _ => 2, two_allOnes_mem_codeLattice⟩ :
    codeLatticeSubgroup mogCode_allOnes_mem)

theorem mk_eq_frameClass_iff (u : codeLatticeSubgroup mogCode_allOnes_mem) :
    (Submodule.Quotient.mk u : codeLatticeModTwo Code.C mogCode_allOnes_mem) = frameClass ↔
      ∃ l ∈ codeLattice Code.C, ∀ i, (u : Fin 24 → ℤ) i = 2 + 2 * l i := by
  rw [frameClass, Submodule.Quotient.eq, mem_two_range_iff]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨w, w.2, fun i => ?_⟩
    have := congrFun hw i
    simp only [Pi.smul_apply, smul_eq_mul, AddSubgroup.coe_sub, Pi.sub_apply] at this
    linarith
  · rintro ⟨l, hl, hu⟩
    refine ⟨⟨l, hl⟩, funext fun i => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, AddSubgroup.coe_sub, Pi.sub_apply, hu i]
    ring

theorem frameClass_ne_zero : frameClass ≠ 0 := by
  intro h
  rw [frameClass, ← Submodule.Quotient.mk_zero, Submodule.Quotient.eq, mem_two_range_iff] at h
  obtain ⟨w, hw⟩ := h
  have hw1 : ∀ i, (w : Fin 24 → ℤ) i = 1 := by
    intro i
    have := congrFun hw i
    simp only [Pi.smul_apply, smul_eq_mul, sub_zero] at this
    linarith
  obtain ⟨m, hm, d, -, hmod, hsum⟩ := w.2
  have h0 := hmod 0
  rw [hw1] at h0
  unfold Int.ModEq at h0 hsum
  rw [Finset.sum_congr rfl fun i _ => hw1 i] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat,
    mul_one] at hsum
  have hb := bitLift_zero_or_one (d 0)
  rcases hm with rfl | rfl <;> omega

theorem codeQuadForm_frameClass :
    codeQuadForm Code.C mogCode_allOnes_mem mogCode_weight_emod_four frameClass = 0 := by
  rw [frameClass, codeQuadForm_mk]
  have : hInt (fun _ => (2 : ℤ)) (fun _ => 2) = 12 := by
    simp only [hInt, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    norm_num
  rw [show ((⟨fun _ => 2, two_allOnes_mem_codeLattice⟩ : codeLatticeSubgroup mogCode_allOnes_mem) :
    Fin 24 → ℤ) = fun _ => 2 from rfl, this]
  decide

private theorem rep_cases {l : Fin 24 → ℤ} (hl : l ∈ codeLattice Code.C) :
    96 ≤ ∑ i, (2 + 2 * l i) * (2 + 2 * l i) ∨ ∀ i, (2 + 2 * l i) % 8 = 0 := by
  obtain ⟨m, hm, d, hd, hld, -⟩ := hl
  rcases hm with rfl | rfl
  · left
    have hi : ∀ i, (4 : ℤ) ≤ (2 + 2 * l i) * (2 + 2 * l i) := by
      intro i
      have h := hld i
      unfold Int.ModEq at h
      have hb := bitLift_zero_or_one (d i)
      obtain ⟨k, hk⟩ : ∃ k, l i = 2 * k := ⟨l i / 2, by omega⟩
      rw [hk]
      have : 0 ≤ k * (k + 1) := by rcases le_or_gt 0 k with h | h <;> nlinarith
      nlinarith
    calc (96 : ℤ) = ∑ _i : Fin 24, (4 : ℤ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun i _ => hi i
  · by_cases h24 : hammingNorm d = 24
    · right
      intro i
      have hfull : (Finset.univ.filter fun j => d j ≠ 0) = Finset.univ :=
        Finset.eq_univ_of_card _ (by rw [Fintype.card_fin]; exact h24)
      have hdi : d i ≠ 0 := by
        have hi : i ∈ Finset.univ.filter fun j => d j ≠ 0 := by
          rw [hfull]
          exact Finset.mem_univ i
        exact (Finset.mem_filter.1 hi).2
      have hb : bitLift (d i) = 1 := by
        rcases bitLift_zero_or_one (d i) with h | h
        · exfalso
          apply hdi
          have h' : ((d i).val : ℤ) = 0 := h
          have : (d i).val = 0 := by exact_mod_cast h'
          exact (ZMod.val_eq_zero (d i)).1 this
        · exact h
      have h := hld i
      unfold Int.ModEq at h
      rw [hb] at h
      omega
    · left
      have hw := wt_mem hd
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      have hle' : hammingNorm d ≤ 16 := by omega
      have hle : (hammingNorm d : ℤ) ≤ 16 := by exact_mod_cast hle'
      have hi : ∀ i, 16 * (1 - bitLift (d i)) ≤ (2 + 2 * l i) * (2 + 2 * l i) := by
        intro i
        have h := hld i
        unfold Int.ModEq at h
        rcases bitLift_zero_or_one (d i) with hb | hb <;> rw [hb] at h ⊢
        · obtain ⟨k, hk⟩ : ∃ k, l i = 4 * k + 1 := ⟨(l i - 1) / 4, by omega⟩
          rw [hk]
          have : 0 ≤ k * (k + 1) := by rcases le_or_gt 0 k with h | h <;> nlinarith
          nlinarith
        · nlinarith [sq_nonneg (2 + 2 * l i)]
      have hsum : ∑ i, 16 * (1 - bitLift (d i)) = 16 * (24 - (hammingNorm d : ℤ)) := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_bitLift_eq]
        simp
      have := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hi i
      rw [hsum] at this
      linarith

private theorem eight_dvd_cases {u : Fin 24 → ℤ} (h8 : ∀ i, u i % 8 = 0) (h0 : u ≠ 0) :
    64 ≤ ∑ i, u i * u i ∧ (∑ i, u i * u i = 64 →
      ∃ j, u = (8 : ℤ) • Pi.single j 1 ∨ u = -((8 : ℤ) • Pi.single j 1)) := by
  obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (funext h)
  have hsq : ∀ i, 0 ≤ u i * u i := fun i => mul_self_nonneg _
  have hj64 : 64 ≤ u j * u j := by
    obtain ⟨k, hk⟩ : ∃ k, u j = 8 * k := ⟨u j / 8, by have := h8 j; omega⟩
    have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hj hk
    rw [hk]
    have : 1 ≤ k * k := by
      rcases lt_or_gt_of_ne hk0 with h | h <;> nlinarith
    nlinarith
  have hsplit := Finset.add_sum_erase Finset.univ (fun i => u i * u i) (Finset.mem_univ j)
  have hrest : 0 ≤ ∑ i ∈ Finset.univ.erase j, u i * u i :=
    Finset.sum_nonneg fun i _ => hsq i
  refine ⟨by linarith, fun h64 => ⟨j, ?_⟩⟩
  have hj' : u j * u j = 64 := by linarith
  have hz : ∀ i ∈ Finset.univ.erase j, u i * u i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hsq i).1 (by linarith)
  have hoff : ∀ i, i ≠ j → u i = 0 := fun i hi =>
    mul_self_eq_zero.1 (hz i (Finset.mem_erase.2 ⟨hi, Finset.mem_univ _⟩))
  have hpm : u j = 8 ∨ u j = -8 := by
    have : (u j - 8) * (u j + 8) = 0 := by ring_nf; linarith
    rcases mul_eq_zero.1 this with h | h
    · exact .inl (by linarith)
    · exact .inr (by linarith)
  rcases hpm with h | h
  · refine .inl (funext fun i => ?_)
    by_cases hi : i = j
    · subst hi; simp [h]
    · simp [hi, hoff i hi]
  · refine .inr (funext fun i => ?_)
    by_cases hi : i = j
    · subst hi; simp [h]
    · simp [hi, hoff i hi]

private theorem codeForm_cast (u : Fin 24 → ℤ) :
    codeForm (fun i => (u i : ℚ)) (fun i => (u i : ℚ)) = ((∑ i, u i * u i : ℤ) : ℚ) / 8 := by
  unfold codeForm
  push_cast
  rfl

private theorem normSq_rep (u : codeLatticeSubgroup mogCode_allOnes_mem)
    (hu : (Submodule.Quotient.mk u : codeLatticeModTwo Code.C mogCode_allOnes_mem) = frameClass) :
    64 ≤ ∑ i, (u : Fin 24 → ℤ) i * (u : Fin 24 → ℤ) i ∧
      (∑ i, (u : Fin 24 → ℤ) i * (u : Fin 24 → ℤ) i = 64 →
        ∃ j, (u : Fin 24 → ℤ) = (8 : ℤ) • Pi.single j 1 ∨
          (u : Fin 24 → ℤ) = -((8 : ℤ) • Pi.single j 1)) := by
  obtain ⟨l, hl, hul⟩ := (mk_eq_frameClass_iff u).1 hu
  have he : ∑ i, (u : Fin 24 → ℤ) i * (u : Fin 24 → ℤ) i =
      ∑ i, (2 + 2 * l i) * (2 + 2 * l i) := Finset.sum_congr rfl fun i _ => by rw [hul i]
  rcases rep_cases hl with h | h
  · rw [he]
    exact ⟨by linarith, fun h' => by linarith⟩
  · have h8 : ∀ i, (u : Fin 24 → ℤ) i % 8 = 0 := fun i => by rw [hul i]; exact h i
    have h0 : (u : Fin 24 → ℤ) ≠ 0 := by
      intro h0
      apply frameClass_ne_zero
      rw [← hu, Submodule.Quotient.mk_eq_zero, mem_two_range_iff]
      exact ⟨0, by rw [h0]; simp⟩
    exact eight_dvd_cases h8 h0

theorem coordinate_frame_mod_two_fiber :
    frameClass ≠ 0 ∧
    codeQuadForm Code.C mogCode_allOnes_mem mogCode_weight_emod_four frameClass = 0 ∧
    (∀ u : codeLatticeSubgroup mogCode_allOnes_mem,
      (Submodule.Quotient.mk u : codeLatticeModTwo Code.C mogCode_allOnes_mem) = frameClass →
      codeForm (fun i => ((u : Fin 24 → ℤ) i : ℚ)) (fun i => ((u : Fin 24 → ℤ) i : ℚ)) ≠ 4) ∧
    (∀ v : Fin 24 → ℤ,
      (∃ hv : v ∈ codeLatticeSubgroup mogCode_allOnes_mem,
        (Submodule.Quotient.mk ⟨v, hv⟩ : codeLatticeModTwo Code.C mogCode_allOnes_mem) =
          frameClass ∧ codeForm (fun i => (v i : ℚ)) (fun i => (v i : ℚ)) = 8) ↔
      ∃ i : Fin 24, v = (8 : ℤ) • Pi.single i 1 ∨ v = -((8 : ℤ) • Pi.single i 1)) ∧
    (∀ u : codeLatticeSubgroup mogCode_allOnes_mem,
      (Submodule.Quotient.mk u : codeLatticeModTwo Code.C mogCode_allOnes_mem) = frameClass →
      8 ≤ codeForm (fun i => ((u : Fin 24 → ℤ) i : ℚ)) (fun i => ((u : Fin 24 → ℤ) i : ℚ))) := by
  refine ⟨frameClass_ne_zero, codeQuadForm_frameClass, fun u hu => ?_, fun v => ?_, fun u hu => ?_⟩
  · have := (normSq_rep u hu).1
    rw [codeForm_cast]
    intro h
    have h' : ((∑ i, (u : Fin 24 → ℤ) i * (u : Fin 24 → ℤ) i : ℤ) : ℚ) = 32 := by linarith
    have : (∑ i, (u : Fin 24 → ℤ) i * (u : Fin 24 → ℤ) i : ℤ) = 32 := by exact_mod_cast h'
    omega
  · constructor
    · rintro ⟨hv, hmk, hn⟩
      rw [codeForm_cast] at hn
      have h' : ((∑ i, v i * v i : ℤ) : ℚ) = 64 := by linarith
      have h64 : (∑ i, v i * v i : ℤ) = 64 := by exact_mod_cast h'
      exact (normSq_rep ⟨v, hv⟩ hmk).2 h64
    · rintro ⟨j, hj⟩
      have hmem : v ∈ codeLatticeSubgroup mogCode_allOnes_mem := by
        rcases hj with rfl | rfl
        · exact smul_eight_mem_codeLattice _
        · exact (codeLatticeSubgroup mogCode_allOnes_mem).neg_mem (smul_eight_mem_codeLattice _)
      refine ⟨hmem, (mk_eq_frameClass_iff ⟨v, hmem⟩).2 ?_, ?_⟩
      · have hΩb : ∀ i, bitLift (Code.Ω i) = 1 := fun _ => rfl
        have hsum : ∀ a : ℤ, ∑ i, (if i = j then a else -1) = a - 23 := by
          intro a
          have e : (fun i => if i = j then a else -1) = fun i => -1 + if i = j then a + 1 else 0 :=
            funext fun i => by split_ifs <;> ring
          rw [e, Finset.sum_add_distrib, Finset.sum_ite_eq']
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, Finset.mem_univ,
            ite_true]
          norm_num
          ring
        rcases hj with rfl | rfl
        · refine ⟨fun i => if i = j then 3 else -1, ⟨1, .inr rfl, Code.Ω, Code.Ω_mem_C,
            fun i => ?_, ?_⟩, fun i => ?_⟩
          · rw [hΩb]
            by_cases hi : i = j <;> simp only [hi, ite_true, ite_false] <;> decide
          · rw [hsum]
            decide
          · by_cases hi : i = j
            · subst hi; simp
            · simp [hi]
        · refine ⟨fun i => if i = j then -5 else -1, ⟨1, .inr rfl, Code.Ω, Code.Ω_mem_C,
            fun i => ?_, ?_⟩, fun i => ?_⟩
          · rw [hΩb]
            by_cases hi : i = j <;> simp only [hi, ite_true, ite_false] <;> decide
          · rw [hsum]
            decide
          · by_cases hi : i = j
            · subst hi; simp
            · simp [hi]
      · rw [codeForm_cast]
        have : (∑ i, v i * v i : ℤ) = 64 := by
          rcases hj with rfl | rfl <;>
          · rw [Fintype.sum_eq_single j fun i hi => by simp [hi]]
            simp
        rw [this]
        norm_num
  · have := (normSq_rep u hu).1
    rw [codeForm_cast]
    have h' : (64 : ℚ) ≤ ((∑ i, (u : Fin 24 → ℤ) i * (u : Fin 24 → ℤ) i : ℤ) : ℚ) := by
      exact_mod_cast this
    linarith

end CFSG.Monster
