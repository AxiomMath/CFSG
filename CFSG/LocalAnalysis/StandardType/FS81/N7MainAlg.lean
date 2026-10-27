module

public import CFSG.LocalAnalysis.StandardType.FS81.HMCore
public import CFSG.LocalAnalysis.StandardType.FS81.SpMatAlg

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

@[expose] def nmE0 : Coords 8 := Pi.single 0 1

@[expose] def nmFK : Set (Matrix (Fin 8) (Fin 8) (ZMod 3)) :=
  spSet fun _ s => ∏ i, s i = 1

@[expose] def nmF : Set (Matrix (Fin 8) (Fin 8) (ZMod 3)) :=
  spSet fun σ s => σ = 1 ∧ ∏ i, s i = 1

@[expose] def nmSgn (A : Finset (Fin 8)) : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  Matrix.diagonal fun i => if i ∈ A then -1 else 1

theorem IsSign.ne_zero {k : ℕ} {s : Fin k → ZMod 3} (hs : IsSign s) (i : Fin k) : s i ≠ 0 := by
  rcases hs i with h | h <;> rw [h] <;> decide

theorem IsSign.mul {k : ℕ} {s t : Fin k → ZMod 3} (hs : IsSign s) (ht : IsSign t) :
    IsSign fun j => s j * t j := by
  intro j
  rcases hs j with h | h <;> rcases ht j with h' | h' <;> simp only [h, h'] <;> decide

theorem IsSign.mul_self {k : ℕ} {s : Fin k → ZMod 3} (hs : IsSign s) (i : Fin k) :
    s i * s i = 1 := by
  rcases hs i with h | h <;> rw [h] <;> decide

private theorem nmh_diagonal_eq_spMat {k : ℕ} (d : Fin k → ZMod 3) :
    Matrix.diagonal d = spMat (1 : Equiv.Perm (Fin k)) d := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [spMat_apply]
  · simp [spMat_apply, Matrix.diagonal, h]

private theorem nmh_spMat_congr {k : ℕ} {σ τ : Equiv.Perm (Fin k)} {s t : Fin k → ZMod 3}
    (h1 : σ = τ) (h2 : s = t) : spMat σ s = spMat τ t := by
  rw [h1, h2]

theorem nm_spMat_inj {k : ℕ} {σ τ : Equiv.Perm (Fin k)} {s t : Fin k → ZMod 3} (hs : IsSign s)
    (ht : IsSign t) (h : spMat σ s = spMat τ t) : σ = τ ∧ s = t := by
  have hval : ∀ j, σ j = τ j ∧ t j = s j := by
    intro j
    have hentry := congrFun (congrFun h (σ j)) j
    rw [spMat_apply, spMat_apply] at hentry
    by_cases hστ : σ j = τ j
    · simp [hστ] at hentry
      exact ⟨hστ, hentry.symm⟩
    · simp [hστ] at hentry
      exact absurd hentry (IsSign.ne_zero hs j)
  exact ⟨Equiv.ext fun j => (hval j).1, funext fun j => (hval j).2.symm⟩

theorem nmFK_one : (1 : Matrix (Fin 8) (Fin 8) (ZMod 3)) ∈ nmFK :=
  ⟨1, fun _ => 1, fun _ => Or.inl rfl, by simp, spMat_one.symm⟩

theorem nmFK_mul {A B : Matrix (Fin 8) (Fin 8) (ZMod 3)} (hA : A ∈ nmFK) (hB : B ∈ nmFK) :
    A * B ∈ nmFK := by
  obtain ⟨σ, s, hs, hps, rfl⟩ := hA
  obtain ⟨τ, t, ht, hpt, rfl⟩ := hB
  refine ⟨σ * τ, fun j => s (τ j) * t j, IsSign.mul (fun j => hs (τ j)) ht, ?_,
    spMat_mul σ τ s t⟩
  show ∏ j : Fin 8, s (τ j) * t j = 1
  rw [Finset.prod_mul_distrib, hpt, mul_one, Equiv.prod_comp τ s, hps]

theorem nmFK_of_mul_eq_one {A B : Matrix (Fin 8) (Fin 8) (ZMod 3)} (hA : A ∈ nmFK)
    (h : A * B = 1) : B ∈ nmFK := by
  obtain ⟨σ, s, hs, hps, rfl⟩ := hA
  have hA'A : spMat σ⁻¹ (fun j => s (σ⁻¹ j)) * spMat σ s = 1 := by
    rw [spMat_mul, inv_mul_cancel]
    conv_rhs => rw [← spMat_one]
    apply nmh_spMat_congr rfl
    funext j
    show s (σ.symm (σ j)) * s j = 1
    rw [Equiv.symm_apply_apply]
    exact IsSign.mul_self hs j
  have hB_eq : B = spMat σ⁻¹ (fun j => s (σ⁻¹ j)) := by
    calc B = (spMat σ⁻¹ (fun j => s (σ⁻¹ j)) * spMat σ s) * B := by rw [hA'A, one_mul]
      _ = spMat σ⁻¹ (fun j => s (σ⁻¹ j)) * (spMat σ s * B) := by rw [mul_assoc]
      _ = spMat σ⁻¹ (fun j => s (σ⁻¹ j)) := by rw [h, mul_one]
  rw [hB_eq]
  refine ⟨σ⁻¹, fun j => s (σ⁻¹ j), fun j => hs (σ⁻¹ j), ?_, rfl⟩
  show ∏ j : Fin 8, s (σ⁻¹ j) = 1
  rw [Equiv.prod_comp σ⁻¹ s, hps]

theorem nmF_one : (1 : Matrix (Fin 8) (Fin 8) (ZMod 3)) ∈ nmF :=
  ⟨1, fun _ => 1, fun _ => Or.inl rfl, ⟨rfl, by simp⟩, spMat_one.symm⟩

theorem nmF_mul {a b : Matrix (Fin 8) (Fin 8) (ZMod 3)} (ha : a ∈ nmF) (hb : b ∈ nmF) :
    a * b ∈ nmF := by
  obtain ⟨σ, s, hs, ⟨hσ, hps⟩, rfl⟩ := ha
  obtain ⟨τ, t, ht, ⟨hτ, hpt⟩, rfl⟩ := hb
  refine ⟨σ * τ, fun j => s (τ j) * t j, IsSign.mul (fun j => hs (τ j)) ht, ⟨?_, ?_⟩,
    spMat_mul σ τ s t⟩
  · rw [hσ, hτ, one_mul]
  · show ∏ j : Fin 8, s (τ j) * t j = 1
    rw [Finset.prod_mul_distrib, hpt, mul_one, Equiv.prod_comp τ s, hps]

theorem nmF_sq {a : Matrix (Fin 8) (Fin 8) (ZMod 3)} (ha : a ∈ nmF) : a * a = 1 := by
  obtain ⟨σ, s, hs, ⟨hσ, hps⟩, rfl⟩ := ha
  exact spMat_mul_self σ s (by rw [hσ, one_mul]) (fun j => by
    rw [hσ]
    simpa using IsSign.mul_self hs j)

theorem nmF_comm {a b : Matrix (Fin 8) (Fin 8) (ZMod 3)} (ha : a ∈ nmF) (hb : b ∈ nmF) :
    a * b = b * a := by
  obtain ⟨σ, s, hs, ⟨hσ, hps⟩, rfl⟩ := ha
  obtain ⟨τ, t, ht, ⟨hτ, hpt⟩, rfl⟩ := hb
  rw [spMat_mul, spMat_mul, hσ, hτ]
  exact nmh_spMat_congr rfl (funext fun j => mul_comm (s j) (t j))

theorem nmSgn_mul_self (A : Finset (Fin 8)) : nmSgn A * nmSgn A = 1 := by
  rw [nmSgn, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  by_cases h : i ∈ A <;> simp [h] <;> decide

theorem nmSgn_mulVec (A : Finset (Fin 8)) (v : Coords 8) :
    nmSgn A *ᵥ v = fun i => if i ∈ A then -v i else v i := by
  funext i
  rw [nmSgn, Matrix.mulVec_diagonal]
  by_cases h : i ∈ A
  · rw [if_pos h, if_pos h]
    exact neg_one_mul (v i)
  · rw [if_neg h, if_neg h, one_mul]

theorem nmSgn_mulVec_single_of_mem {C : Finset (Fin 8)} {i : Fin 8} (hi : i ∈ C) :
    nmSgn C *ᵥ Pi.single i 1 = -Pi.single i 1 := by
  funext j
  rw [nmSgn_mulVec]
  change (if j ∈ C then -Pi.single i 1 j else Pi.single i 1 j) = -Pi.single i 1 j
  by_cases hj : j = i
  · subst hj
    rw [if_pos hi]
  · rw [Pi.single_eq_of_ne hj]
    by_cases hjC : j ∈ C
    · rw [if_pos hjC]
    · rw [if_neg hjC]
      exact neg_zero.symm

theorem nmSgn_mulVec_single_of_notMem {C : Finset (Fin 8)} {i : Fin 8} (hi : i ∉ C) :
    nmSgn C *ᵥ Pi.single i 1 = Pi.single i 1 := by
  funext j
  rw [nmSgn_mulVec]
  change (if j ∈ C then -Pi.single i 1 j else Pi.single i 1 j) = Pi.single i 1 j
  by_cases hj : j ∈ C
  · rw [if_pos hj]
    have hji : j ≠ i := fun h => hi (h ▸ hj)
    rw [Pi.single_eq_of_ne hji]
    exact neg_zero
  · rw [if_neg hj]

theorem nmSgn_mem_nmF {A : Finset (Fin 8)} (h : Even A.card) : nmSgn A ∈ nmF := by
  have hs : IsSign (fun i : Fin 8 => if i ∈ A then (-1 : ZMod 3) else 1) := by
    intro i
    dsimp only
    split_ifs <;> simp
  refine ⟨1, fun i => if i ∈ A then -1 else 1, hs, ⟨rfl, ?_⟩, ?_⟩
  · show ∏ i : Fin 8, (if i ∈ A then (-1 : ZMod 3) else 1) = 1
    rw [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.prod_const,
      Finset.prod_const_one, mul_one]
    exact Even.neg_one_pow h
  · rw [nmSgn, nmh_diagonal_eq_spMat]

theorem exists_nmSgn_of_mem_nmF {a : Matrix (Fin 8) (Fin 8) (ZMod 3)} (ha : a ∈ nmF) :
    ∃ A : Finset (Fin 8), Even A.card ∧ a = nmSgn A := by
  obtain ⟨τ, t, ht, ⟨hτ, hpt⟩, rfl⟩ := ha
  subst hτ
  refine ⟨Finset.univ.filter fun i => t i = -1, ?_, ?_⟩
  · have h1 : (∏ i : Fin 8, t i) =
        ∏ i : Fin 8, (if t i = -1 then (-1 : ZMod 3) else 1) := by
      apply Finset.prod_congr rfl
      intro i _
      rcases ht i with h | h <;> simp [h]
    have hprod : (∏ i : Fin 8, t i) =
        (-1 : ZMod 3) ^ (Finset.univ.filter fun i => t i = -1).card := by
      rw [h1, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
    rw [hpt] at hprod
    exact (neg_one_pow_eq_one_iff_even (by decide : (-1 : ZMod 3) ≠ 1)).mp hprod.symm
  · rw [← nmh_diagonal_eq_spMat, nmSgn]
    congr 1
    funext i
    by_cases hi : t i = -1
    · have hmem : i ∈ Finset.univ.filter (fun i => t i = -1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
      simp [hmem, hi]
    · have hmem : i ∉ Finset.univ.filter (fun i => t i = -1) :=
        fun h => hi (Finset.mem_filter.mp h).2
      rcases ht i with h | h
      · simp [hmem, h]
      · exact absurd h hi

theorem nmSgn_mul {A B : Finset (Fin 8)} :
    nmSgn A * nmSgn B = nmSgn (symmDiff A B) := by
  rw [nmSgn, nmSgn, nmSgn, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hA : i ∈ A <;> by_cases hB : i ∈ B <;>
    simp [hA, hB, Finset.mem_symmDiff] <;> decide

theorem evenAll0_subset_nmFK : evenAll0 7 ⊆ nmFK := by
  rintro A ⟨σ, s, hs, ⟨hσ, hps⟩, rfl⟩
  exact ⟨σ, s, hs, hps, rfl⟩

end CFSG.StandardType.FrameRoute.FS81

end
