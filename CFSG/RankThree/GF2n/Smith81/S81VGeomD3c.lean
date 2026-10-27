module

public import CFSG.RankThree.GF2n.Smith81.S81VGeomD3b

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module

variable {F : Type} [Field F] {σ : F ≃+* F} {a b : Fin 3 → Fin 6 → F} {θ : F}

@[expose] def P4 (a b : Fin 3 → Fin 6 → F) : Submodule F (Fin 6 → F) :=
  Submodule.span F {a 0, b 0, a 1, b 1}

@[expose] def P3 (a b : Fin 3 → Fin 6 → F) (θ : F) : Submodule F (Fin 6 → F) :=
  Submodule.span F {a 0, b 0, a 1 + θ • b 1}

@[expose] def P2 (a b : Fin 3 → Fin 6 → F) : Submodule F (Fin 6 → F) :=
  Submodule.span F {a 0, b 0}

@[expose] def PU (a b : Fin 3 → Fin 6 → F) (θ : F) : Submodule F (Fin 6 → F) :=
  Submodule.span F {a 0, b 0, rr a b θ}

private theorem herm_ba_of_frame (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) (i j : Fin 3) :
    herm σ (b i) (a j) = if i = j then 1 else 0 := by
  rw [herm_conj σ hσ (a j) (b i), hf.ab j i]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

private theorem range_v2 (x y : Fin 6 → F) : Set.range ![x, y] = ({x, y} : Set (Fin 6 → F)) :=
  Matrix.range_cons_cons_empty x y ![]

private theorem range_v3 (x y z : Fin 6 → F) :
    Set.range ![x, y, z] = ({x, y, z} : Set (Fin 6 → F)) := by
  rw [Matrix.range_cons, Matrix.range_cons_cons_empty, Set.singleton_union]

private theorem range_v4 (x y z w : Fin 6 → F) :
    Set.range ![x, y, z, w] = ({x, y, z, w} : Set (Fin 6 → F)) := by
  rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_cons_cons_empty, Set.singleton_union,
    Set.singleton_union]

private theorem mem_span_three {x y z u : Fin 6 → F}
    (h : u ∈ Submodule.span F ({x, y, z} : Set (Fin 6 → F))) :
    ∃ α β γ : F, u = α • x + β • y + γ • z := by
  rw [Submodule.mem_span_insert] at h
  obtain ⟨α, t, ht, rfl⟩ := h
  rw [Submodule.mem_span_insert] at ht
  obtain ⟨β, s, hs, rfl⟩ := ht
  rw [Submodule.mem_span_singleton] at hs
  obtain ⟨γ, rfl⟩ := hs
  exact ⟨α, β, γ, by rw [add_assoc]⟩

private theorem mem_P3 {x : Fin 6 → F} (h : x ∈ P3 a b θ) :
    ∃ α β γ : F, x = α • a 0 + β • b 0 + γ • (a 1 + θ • b 1) :=
  mem_span_three h

private theorem gram_three_det (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) {x : Fin 6 → F}
    (h1 : herm σ (a 0) x = θ) (h2 : herm σ (b 0) x = 1) (h3 : herm σ x x = 0) :
    (Matrix.of fun i j => herm σ (![a 0, b 0, x] i) (![a 0, b 0, x] j)).det = θ + σ θ := by
  have h4 : herm σ x (a 0) = σ θ := by rw [herm_conj σ hσ, h1]
  have h5 : herm σ x (b 0) = 1 := by rw [herm_conj σ hσ, h2, map_one]
  rw [Matrix.det_fin_three]
  simp [hf.aa, hf.bb, hf.ab, herm_ba_of_frame hσ hf, h1, h2, h3, h4, h5] <;> ring

private theorem gram_three_ne (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) (hθ : θ + σ θ ≠ 0)
    {x : Fin 6 → F} (h1 : herm σ (a 0) x = θ) (h2 : herm σ (b 0) x = 1)
    (h3 : herm σ x x = 0) :
    (Matrix.of fun i j => herm σ (![a 0, b 0, x] i) (![a 0, b 0, x] j)).det ≠ 0 := by
  rw [gram_three_det hσ hf h1 h2 h3]
  exact hθ

private theorem li_three (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) (hθ : θ + σ θ ≠ 0)
    {x : Fin 6 → F} (h1 : herm σ (a 0) x = θ) (h2 : herm σ (b 0) x = 1)
    (h3 : herm σ x x = 0) : LinearIndependent F ![a 0, b 0, x] :=
  linearIndependent_of_gram ![a 0, b 0, x] (gram_three_ne hσ hf hθ h1 h2 h3)

private theorem herm_a0_rr (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) :
    herm σ (a 0) (rr a b θ) = θ := by
  unfold rr
  simp [hf.aa, hf.bb, hf.ab, herm_ba_of_frame hσ hf]

private theorem herm_b0_rr (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) :
    herm σ (b 0) (rr a b θ) = 1 := by
  unfold rr
  simp [hf.aa, hf.bb, hf.ab, herm_ba_of_frame hσ hf]

private theorem herm_rr_rr [CharP F 2] (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) :
    herm σ (rr a b θ) (rr a b θ) = 0 := by
  have key : herm σ (rr a b θ) (rr a b θ) = 2 * (θ + σ θ) := by
    unfold rr
    simp [hf.aa, hf.bb, hf.ab, herm_ba_of_frame hσ hf]
    ring
  rw [key, CharTwo.two_eq_zero, zero_mul]

private theorem herm_a0_v3 (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) :
    herm σ (a 0) (v3 a b θ) = θ := by
  unfold v3
  simp [hf.aa, hf.bb, hf.ab, herm_ba_of_frame hσ hf]

private theorem herm_b0_v3 (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) :
    herm σ (b 0) (v3 a b θ) = 1 := by
  unfold v3
  simp [hf.aa, hf.bb, hf.ab, herm_ba_of_frame hσ hf]

private theorem herm_v3_v3 [CharP F 2] (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) :
    herm σ (v3 a b θ) (v3 a b θ) = 0 := by
  have key : herm σ (v3 a b θ) (v3 a b θ) = 2 * (θ + σ θ) := by
    unfold v3
    simp [hf.aa, hf.bb, hf.ab, herm_ba_of_frame hσ hf]
    ring
  rw [key, CharTwo.two_eq_zero, zero_mul]

private theorem P_data_gram (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) :
    (Matrix.of fun i j => herm σ (![a 0, b 0, a 1, b 1] i) (![a 0, b 0, a 1, b 1] j)).det ≠ 0 := by
  have hG : (Matrix.of fun i j => herm σ (![a 0, b 0, a 1, b 1] i)
      (![a 0, b 0, a 1, b 1] j)) = !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hf.aa, hf.bb, hf.ab, herm_ba_of_frame hσ hf]
  rw [hG]
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem P_data [CharP F 2] (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) (hθ : θ + σ θ ≠ 0) :
    finrank F (P4 a b) = 4 ∧ NonDeg σ (P4 a b) ∧ finrank F (P3 a b θ) = 3 ∧
      NonDeg σ (P3 a b θ) ∧ finrank F (P2 a b) = 2 ∧ NonDeg σ (P2 a b) ∧
      finrank F (PU a b θ) = 3 ∧ NonDeg σ (PU a b θ) := by
  have hdet4 := P_data_gram hσ hf
  have hdet3 : (Matrix.of fun i j => herm σ (![a 0, b 0, a 1 + θ • b 1] i)
      (![a 0, b 0, a 1 + θ • b 1] j)).det ≠ 0 := by
    rw [Matrix.det_fin_three]
    simp [hf.aa, hf.bb, hf.ab, herm_ba_of_frame hσ hf]
    intro h
    apply hθ
    linear_combination -h
  have hdet2 : (Matrix.of fun i j => herm σ (![a 0, b 0] i) (![a 0, b 0] j)).det ≠ 0 := by
    rw [Matrix.det_fin_two]
    simp [hf.aa, hf.bb, hf.ab, herm_ba_of_frame hσ hf]
  have hdetU := gram_three_ne hσ hf hθ (herm_a0_rr hσ hf) (herm_b0_rr hσ hf)
    (herm_rr_rr hσ hf)
  have e4 : P4 a b = Submodule.span F (Set.range ![a 0, b 0, a 1, b 1]) := by
    unfold P4
    rw [range_v4]
  have e3 : P3 a b θ = Submodule.span F (Set.range ![a 0, b 0, a 1 + θ • b 1]) := by
    unfold P3
    rw [range_v3]
  have e2 : P2 a b = Submodule.span F (Set.range ![a 0, b 0]) := by
    unfold P2
    rw [range_v2]
  have eU : PU a b θ = Submodule.span F (Set.range ![a 0, b 0, rr a b θ]) := by
    unfold PU
    rw [range_v3]
  rw [e4, e3, e2, eU]
  exact ⟨finrank_span_of_gram _ hdet4, nonDeg_span_of_gram hσ _ hdet4,
    finrank_span_of_gram _ hdet3, nonDeg_span_of_gram hσ _ hdet3,
    finrank_span_of_gram _ hdet2, nonDeg_span_of_gram hσ _ hdet2,
    finrank_span_of_gram _ hdetU, nonDeg_span_of_gram hσ _ hdetU⟩

private theorem P2_le_P3 : P2 a b ≤ P3 a b θ := by
  unfold P2 P3
  apply Submodule.span_mono
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  rcases hx with rfl | rfl <;> simp

private theorem P3_le_P4 : P3 a b θ ≤ P4 a b := by
  unfold P3 P4
  rw [Submodule.span_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact Submodule.subset_span (by simp)
  · exact Submodule.subset_span (by simp)
  · exact Submodule.add_mem _ (Submodule.subset_span (by simp))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

private theorem b1_mem_P4 : b 1 ∈ P4 a b := by
  unfold P4
  exact Submodule.subset_span (by simp)

private theorem a0_mem_P3 : a 0 ∈ P3 a b θ := by
  unfold P3
  exact Submodule.subset_span (by simp)

private theorem b0_mem_P3 : b 0 ∈ P3 a b θ := by
  unfold P3
  exact Submodule.subset_span (by simp)

private theorem v3_mem_P3 : v3 a b θ ∈ P3 a b θ := by
  have e : v3 a b θ = a 0 + θ • b 0 + (a 1 + θ • b 1) := by
    unfold v3
    simp only [add_assoc]
  rw [e]
  unfold P3
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.subset_span (by simp))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))
    (Submodule.subset_span (by simp))

private theorem b1_not_mem_P3 (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) :
    b 1 ∉ P3 a b θ := by
  intro hmem
  obtain ⟨α, β, γ, h⟩ := mem_P3 hmem
  have e1 : herm σ (b 1) (α • a 0 + β • b 0 + γ • (a 1 + θ • b 1)) = γ := by
    simp [hf.bb, herm_ba_of_frame hσ hf]
  have e2 : herm σ (a 1) (α • a 0 + β • b 0 + γ • (a 1 + θ • b 1)) = γ * θ := by
    simp [hf.aa, hf.ab]
  have hγ : γ = 0 := by
    have h1 := congrArg (herm σ (b 1)) h
    rw [e1, hf.bb] at h1
    exact h1.symm
  have h2 := congrArg (herm σ (a 1)) h
  rw [e2, hγ, zero_mul, hf.ab] at h2
  simp at h2

theorem P_incl [CharP F 2] (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) (hθ : θ + σ θ ≠ 0) :
    P2 a b ≤ P3 a b θ ∧ P3 a b θ ≤ P4 a b ∧ b 1 ∈ P4 a b ∧ b 1 ∉ P3 a b θ ∧
      a 0 ∈ P3 a b θ ∧ b 0 ∈ P3 a b θ ∧ v3 a b θ ∈ P3 a b θ ∧
      LinearIndependent F ![a 0, b 0, v3 a b θ] :=
  ⟨P2_le_P3, P3_le_P4, b1_mem_P4, b1_not_mem_P3 hσ hf, a0_mem_P3, b0_mem_P3, v3_mem_P3,
    li_three hσ hf hθ (herm_a0_v3 hσ hf) (herm_b0_v3 hσ hf) (herm_v3_v3 hσ hf)⟩

private theorem orth_of_b1 {x : Fin 6 → F} (h : herm σ (b 1) x = 0) :
    x ∈ orth σ (Submodule.span F {b 1}) := by
  rw [mem_orth]
  intro w hw
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [herm_smul_left, h, mul_zero]

private theorem P2_le_orth (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) :
    P2 a b ≤ orth σ (Submodule.span F {b 1}) := by
  unfold P2
  rw [Submodule.span_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · rw [SetLike.mem_coe]
    apply orth_of_b1
    simp [hf.bb, herm_ba_of_frame hσ hf]
  · rw [SetLike.mem_coe]
    apply orth_of_b1
    simp [hf.bb, herm_ba_of_frame hσ hf]

theorem P_perp [CharP F 2] (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) (hθ : θ + σ θ ≠ 0) :
    P3 a b θ ⊓ orth σ (Submodule.span F {b 1}) = P2 a b := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hx3, hxo⟩ := Submodule.mem_inf.mp hx
    have hbx : herm σ (b 1) x = 0 :=
      (mem_orth (σ := σ)).mp hxo (b 1) (Submodule.mem_span_singleton_self (b 1))
    obtain ⟨α, β, γ, hxe⟩ := mem_P3 hx3
    have e1 : herm σ (b 1) (α • a 0 + β • b 0 + γ • (a 1 + θ • b 1)) = γ := by
      simp [hf.bb, herm_ba_of_frame hσ hf]
    rw [hxe, e1] at hbx
    rw [hxe, hbx, zero_smul, add_zero]
    unfold P2
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · exact le_inf P2_le_P3 (P2_le_orth hσ hf)

end CFSG.RankThree.GF2n.Smith81.S81V
