module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open

open scoped Matrix

private def s1614_ls_g (K : Type) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

private def s1614_ls_h (K : Type) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1]

private def s1614_ls_tag (K : Type) [Field K] : Fin 3 → K × K := ![(1, 0), (0, 1), (1, 1)]

private lemma s1614_ls_tag_inj (K : Type) [Field K] {i k : Fin 3}
    (h : s1614_ls_tag K i = s1614_ls_tag K k) : i = k := by
  fin_cases i <;> fin_cases k <;> simp_all [s1614_ls_tag]

private lemma s1614_ls_entry_i (K : Type) [Field K] (h2 : (1 : K) + 1 = 0) (i j : Fin 3) :
    ((s1614_ls_g K ^ (i : ℕ) * s1614_ls_h K ^ (j : ℕ)) 0 0,
      (s1614_ls_g K ^ (i : ℕ) * s1614_ls_h K ^ (j : ℕ)) 0 1) = s1614_ls_tag K i := by
  fin_cases i <;> fin_cases j <;>
    simp [s1614_ls_tag, s1614_ls_g, s1614_ls_h, Matrix.mul_apply, Fin.sum_univ_four,
      pow_two, pow_one, h2]

private lemma s1614_ls_entry_j (K : Type) [Field K] (h2 : (1 : K) + 1 = 0) (i j : Fin 3) :
    ((s1614_ls_g K ^ (i : ℕ) * s1614_ls_h K ^ (j : ℕ)) 2 2,
      (s1614_ls_g K ^ (i : ℕ) * s1614_ls_h K ^ (j : ℕ)) 2 3) = s1614_ls_tag K j := by
  fin_cases i <;> fin_cases j <;>
    simp [s1614_ls_tag, s1614_ls_g, s1614_ls_h, Matrix.mul_apply, Fin.sum_univ_four,
      pow_two, pow_one, h2]

private lemma s1614_ls_pair_inj (K : Type) [Field K] (h2 : (1 : K) + 1 = 0)
    (i j k l : Fin 3)
    (h : s1614_ls_g K ^ (i : ℕ) * s1614_ls_h K ^ (j : ℕ) =
      s1614_ls_g K ^ (k : ℕ) * s1614_ls_h K ^ (l : ℕ)) :
    i = k ∧ j = l := by
  have h00 : (s1614_ls_g K ^ (i : ℕ) * s1614_ls_h K ^ (j : ℕ)) 0 0 =
      (s1614_ls_g K ^ (k : ℕ) * s1614_ls_h K ^ (l : ℕ)) 0 0 := by rw [h]
  have h01 : (s1614_ls_g K ^ (i : ℕ) * s1614_ls_h K ^ (j : ℕ)) 0 1 =
      (s1614_ls_g K ^ (k : ℕ) * s1614_ls_h K ^ (l : ℕ)) 0 1 := by rw [h]
  have h22 : (s1614_ls_g K ^ (i : ℕ) * s1614_ls_h K ^ (j : ℕ)) 2 2 =
      (s1614_ls_g K ^ (k : ℕ) * s1614_ls_h K ^ (l : ℕ)) 2 2 := by rw [h]
  have h23 : (s1614_ls_g K ^ (i : ℕ) * s1614_ls_h K ^ (j : ℕ)) 2 3 =
      (s1614_ls_g K ^ (k : ℕ) * s1614_ls_h K ^ (l : ℕ)) 2 3 := by rw [h]
  have hi : s1614_ls_tag K i = s1614_ls_tag K k := by
    rw [← s1614_ls_entry_i K h2 i j, ← s1614_ls_entry_i K h2 k l]
    exact Prod.ext h00 h01
  have hj : s1614_ls_tag K j = s1614_ls_tag K l := by
    rw [← s1614_ls_entry_j K h2 i j, ← s1614_ls_entry_j K h2 k l]
    exact Prod.ext h22 h23
  exact ⟨s1614_ls_tag_inj K hi, s1614_ls_tag_inj K hj⟩

private lemma s1614_ls_g_mul_sq (K : Type) [Field K] (h2 : (1 : K) + 1 = 0) :
    s1614_ls_g K * (s1614_ls_g K * s1614_ls_g K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s1614_ls_g, Matrix.mul_apply, Fin.sum_univ_four, h2]

private lemma s1614_ls_sq_mul_g (K : Type) [Field K] (h2 : (1 : K) + 1 = 0) :
    (s1614_ls_g K * s1614_ls_g K) * s1614_ls_g K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s1614_ls_g, Matrix.mul_apply, Fin.sum_univ_four, h2]

private lemma s1614_ls_h_mul_sq (K : Type) [Field K] (h2 : (1 : K) + 1 = 0) :
    s1614_ls_h K * (s1614_ls_h K * s1614_ls_h K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s1614_ls_h, Matrix.mul_apply, Fin.sum_univ_four, h2]

private lemma s1614_ls_sq_mul_h (K : Type) [Field K] (h2 : (1 : K) + 1 = 0) :
    (s1614_ls_h K * s1614_ls_h K) * s1614_ls_h K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s1614_ls_h, Matrix.mul_apply, Fin.sum_univ_four, h2]

private lemma s1614_ls_comm (K : Type) [Field K] (h2 : (1 : K) + 1 = 0) :
    s1614_ls_g K * s1614_ls_h K = s1614_ls_h K * s1614_ls_g K := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [s1614_ls_g, s1614_ls_h, Matrix.mul_apply, Fin.sum_univ_four, h2]

private lemma s1614_ls_g_act (K : Type) [Field K] (v : Fin 4 → K)
    (hv2 : v 2 = 0) (hv3 : v 3 = 0) :
    (s1614_ls_g K *ᵥ v) 2 = 0 ∧ (s1614_ls_g K *ᵥ v) 3 = 0 := by
  constructor <;>
    · rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four]
      simp [s1614_ls_g, hv2, hv3]

private lemma s1614_ls_h_act (K : Type) [Field K] (v : Fin 4 → K)
    (hv2 : v 2 = 0) (hv3 : v 3 = 0) :
    (s1614_ls_h K *ᵥ v) 2 = 0 ∧ (s1614_ls_h K *ᵥ v) 3 = 0 := by
  constructor <;>
    · rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four]
      simp [s1614_ls_h, hv2, hv3]

private lemma s1614_ls_g2_act (K : Type) [Field K] (h2 : (1 : K) + 1 = 0) (v : Fin 4 → K)
    (hv2 : v 2 = 0) (hv3 : v 3 = 0) :
    ((s1614_ls_g K * s1614_ls_g K) *ᵥ v) 2 = 0 ∧
      ((s1614_ls_g K * s1614_ls_g K) *ᵥ v) 3 = 0 := by
  constructor <;>
    · rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four]
      simp [s1614_ls_g, Matrix.mul_apply, Fin.sum_univ_four, hv2, hv3, h2]

private lemma s1614_ls_h2_act (K : Type) [Field K] (h2 : (1 : K) + 1 = 0) (v : Fin 4 → K)
    (hv2 : v 2 = 0) (hv3 : v 3 = 0) :
    ((s1614_ls_h K * s1614_ls_h K) *ᵥ v) 2 = 0 ∧
      ((s1614_ls_h K * s1614_ls_h K) *ᵥ v) 3 = 0 := by
  constructor <;>
    · rw [Matrix.mulVec_apply_eq_sum, Fin.sum_univ_four]
      simp [s1614_ls_h, Matrix.mul_apply, Fin.sum_univ_four, hv2, hv3, h2]

theorem s1614_ln_std (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2) :
    ∃ X₀ : Subgroup (Multiplicative (Fin 4 → K)),
      (∀ x ∈ X₀, Multiplicative.toAdd x 3 = 0) ∧ Nat.card ↥X₀ = 4 ∧
      ∃ E₀ : Subgroup (Matrix.GeneralLinearGroup (Fin 4) K), IsElemAbelian 3 E₀ ∧
        9 ≤ Nat.card ↥E₀ ∧ ∀ e ∈ E₀, ∀ x ∈ X₀,
          Multiplicative.ofAdd (((e : Matrix.GeneralLinearGroup (Fin 4) K) :
            Matrix (Fin 4) (Fin 4) K).mulVec (Multiplicative.toAdd x)) ∈ X₀ := by
  have h01 : ∀ x : K, x = 0 ∨ x = 1 := by
    intro x
    by_cases hx : x = 0
    · exact Or.inl hx
    · right
      obtain ⟨y, _, hy⟩ := (Nat.card_eq_two_iff' (0 : K)).1 hK
      exact (hy x hx).trans (hy 1 one_ne_zero).symm
  have h2 : (1 : K) + 1 = 0 := by
    rcases h01 ((1 : K) + 1) with h | h
    · exact h
    · exfalso
      exact one_ne_zero (add_right_cancel (show (1 : K) + 1 = 0 + 1 by simpa using h))
  have hGmm : s1614_ls_g K * (s1614_ls_g K * s1614_ls_g K) = 1 := s1614_ls_g_mul_sq K h2
  have hGmm' : (s1614_ls_g K * s1614_ls_g K) * s1614_ls_g K = 1 := s1614_ls_sq_mul_g K h2
  have hHmm : s1614_ls_h K * (s1614_ls_h K * s1614_ls_h K) = 1 := s1614_ls_h_mul_sq K h2
  have hHmm' : (s1614_ls_h K * s1614_ls_h K) * s1614_ls_h K = 1 := s1614_ls_sq_mul_h K h2
  let G₀ : Matrix.GeneralLinearGroup (Fin 4) K :=
    ⟨s1614_ls_g K, s1614_ls_g K * s1614_ls_g K, hGmm, hGmm'⟩
  let H₀ : Matrix.GeneralLinearGroup (Fin 4) K :=
    ⟨s1614_ls_h K, s1614_ls_h K * s1614_ls_h K, hHmm, hHmm'⟩
  have hg3 : s1614_ls_g K ^ 3 = 1 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ', pow_two]
    exact hGmm
  have hh3 : s1614_ls_h K ^ 3 = 1 := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ', pow_two]
    exact hHmm
  have hG3 : G₀ ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact hg3
  have hH3 : H₀ ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    exact hh3
  have hGH : G₀ * H₀ = H₀ * G₀ := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact s1614_ls_comm K h2
  let E₀ : Subgroup (Matrix.GeneralLinearGroup (Fin 4) K) :=
    Subgroup.closure ({G₀, H₀} : Set (Matrix.GeneralLinearGroup (Fin 4) K))
  have hGmem : G₀ ∈ E₀ := Subgroup.subset_closure (by simp)
  have hHmem : H₀ ∈ E₀ := Subgroup.subset_closure (by simp)
  have hcommAll : ∀ a ∈ E₀, ∀ b ∈ E₀, a * b = b * a := by
    intro a ha b hb
    refine Subgroup.closure_induction₂
      (k := ({G₀, H₀} : Set (Matrix.GeneralLinearGroup (Fin 4) K))) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ha hb
    · intro x y hx hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
      rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;>
        first | rfl | exact hGH | exact hGH.symm
    · intro x hx
      simp
    · intro x hx
      simp
    · intro x y z hx hy hz hxz hyz
      exact (Commute.mul_left (show Commute x z from hxz) (show Commute y z from hyz)).eq
    · intro y z x hy hz hx hxy hxz
      exact (Commute.mul_right (show Commute x y from hxy) (show Commute x z from hxz)).eq
    · intro x y hx hy hxy
      exact (show Commute x y from hxy).inv_left.eq
    · intro x y hx hy hxy
      exact (show Commute x y from hxy).inv_right.eq
  have hpow : ∀ x ∈ E₀, x ^ 3 = 1 := by
    intro x hx
    refine Subgroup.closure_induction
      (k := ({G₀, H₀} : Set (Matrix.GeneralLinearGroup (Fin 4) K))) ?_ ?_ ?_ ?_ hx
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact hG3
      · exact hH3
    · simp
    · intro a b ha hb ha3 hb3
      rw [Commute.mul_pow (show Commute a b from hcommAll a ha b hb) 3, ha3, hb3, one_mul]
    · intro a ha ha3
      rw [inv_pow, ha3, inv_one]
  have hEA : IsElemAbelian 3 E₀ := by
    refine ⟨IsMulCommutative.of_comm (fun a b : ↥E₀ => ?_), ?_⟩
    · exact Subtype.ext (hcommAll a.1 a.2 b.1 b.2)
    · intro x hx
      exact hpow x hx
  let X₀ : Subgroup (Multiplicative (Fin 4 → K)) :=
    { carrier := {x | Multiplicative.toAdd x 2 = 0 ∧ Multiplicative.toAdd x 3 = 0}
      one_mem' := by
        simp
      mul_mem' := by
        intro x y hx hy
        refine ⟨?_, ?_⟩
        · simp [hx.1, hy.1]
        · simp [hx.2, hy.2]
      inv_mem' := by
        intro x hx
        refine ⟨?_, ?_⟩
        · simp [hx.1]
        · simp [hx.2] }
  have hXmem : ∀ x : Multiplicative (Fin 4 → K),
      x ∈ X₀ ↔ Multiplicative.toAdd x 2 = 0 ∧ Multiplicative.toAdd x 3 = 0 :=
    fun _ => Iff.rfl
  have hstab : ∀ e ∈ E₀, ∀ x ∈ X₀,
      Multiplicative.ofAdd (((e : Matrix.GeneralLinearGroup (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K).mulVec (Multiplicative.toAdd x)) ∈ X₀ := by
    intro e he
    refine Subgroup.closure_induction''
      (s := ({G₀, H₀} : Set (Matrix.GeneralLinearGroup (Fin 4) K)))
      (p := fun y _ => ∀ x ∈ X₀, Multiplicative.ofAdd
        (((y : Matrix.GeneralLinearGroup (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K).mulVec (Multiplicative.toAdd x)) ∈ X₀)
      ?_ ?_ ?_ ?_ he
    · intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · intro x hx
        have hx' : Multiplicative.toAdd x 2 = 0 ∧ Multiplicative.toAdd x 3 = 0 := hx
        simpa [hXmem] using s1614_ls_g_act K (Multiplicative.toAdd x) hx'.1 hx'.2
      · intro x hx
        have hx' : Multiplicative.toAdd x 2 = 0 ∧ Multiplicative.toAdd x 3 = 0 := hx
        simpa [hXmem] using s1614_ls_h_act K (Multiplicative.toAdd x) hx'.1 hx'.2
    · intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl
      · intro x hx
        have hx' : Multiplicative.toAdd x 2 = 0 ∧ Multiplicative.toAdd x 3 = 0 := hx
        rw [show (((G₀⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K)) :
            Matrix (Fin 4) (Fin 4) K) = s1614_ls_g K * s1614_ls_g K from rfl]
        simpa [hXmem] using s1614_ls_g2_act K h2 (Multiplicative.toAdd x) hx'.1 hx'.2
      · intro x hx
        have hx' : Multiplicative.toAdd x 2 = 0 ∧ Multiplicative.toAdd x 3 = 0 := hx
        rw [show (((H₀⁻¹ : Matrix.GeneralLinearGroup (Fin 4) K)) :
            Matrix (Fin 4) (Fin 4) K) = s1614_ls_h K * s1614_ls_h K from rfl]
        simpa [hXmem] using s1614_ls_h2_act K h2 (Multiplicative.toAdd x) hx'.1 hx'.2
    · intro x hx
      simpa [Matrix.one_mulVec] using hx
    · intro a b ha hb pa pb x hx
      have h1 : (((a * b : Matrix.GeneralLinearGroup (Fin 4) K)) :
          Matrix (Fin 4) (Fin 4) K).mulVec (Multiplicative.toAdd x) =
          (a : Matrix (Fin 4) (Fin 4) K).mulVec
            ((b : Matrix (Fin 4) (Fin 4) K).mulVec (Multiplicative.toAdd x)) := by
        rw [Units.val_mul, Matrix.mulVec_mulVec]
      rw [h1]
      simpa using pa (Multiplicative.ofAdd ((b : Matrix (Fin 4) (Fin 4) K).mulVec
        (Multiplicative.toAdd x))) (pb x hx)
  have hXcard : Nat.card ↥X₀ = 4 := by
    have e : ↥X₀ ≃ K × K :=
      { toFun := fun x => (Multiplicative.toAdd x.1 0, Multiplicative.toAdd x.1 1)
        invFun := fun p => ⟨Multiplicative.ofAdd ![p.1, p.2, 0, 0], by
          constructor <;> simp⟩
        left_inv := by
          intro x
          apply Subtype.ext
          apply_fun Multiplicative.toAdd
          funext i
          fin_cases i <;> simp [x.2.1, x.2.2]
        right_inv := by
          intro p
          ext <;> simp }
    rw [Nat.card_congr e, Nat.card_prod, hK]
  have h9 : 9 ≤ Nat.card ↥E₀ := by
    let F : Fin 3 × Fin 3 → ↥E₀ := fun p =>
      ⟨G₀ ^ (p.1 : ℕ) * H₀ ^ (p.2 : ℕ),
        Subgroup.mul_mem E₀ (Subgroup.pow_mem E₀ hGmem (p.1 : ℕ))
          (Subgroup.pow_mem E₀ hHmem (p.2 : ℕ))⟩
    have hFinj : Function.Injective F := by
      rintro ⟨i, j⟩ ⟨k, l⟩ heq
      have hgl : G₀ ^ (i : ℕ) * H₀ ^ (j : ℕ) = G₀ ^ (k : ℕ) * H₀ ^ (l : ℕ) :=
        congrArg Subtype.val heq
      have hmat : (G₀ : Matrix (Fin 4) (Fin 4) K) ^ (i : ℕ) *
            (H₀ : Matrix (Fin 4) (Fin 4) K) ^ (j : ℕ) =
          (G₀ : Matrix (Fin 4) (Fin 4) K) ^ (k : ℕ) *
            (H₀ : Matrix (Fin 4) (Fin 4) K) ^ (l : ℕ) := by
        simpa only [Units.val_mul, Units.val_pow_eq_pow_val] using
          congrArg (fun u : Matrix.GeneralLinearGroup (Fin 4) K =>
            (u : Matrix (Fin 4) (Fin 4) K)) hgl
      obtain ⟨hik, hjl⟩ := s1614_ls_pair_inj K h2 i j k l hmat
      exact Prod.ext hik hjl
    have hle := Nat.card_le_card_of_injective F hFinj
    simpa using hle
  refine ⟨X₀, ?_, hXcard, E₀, hEA, h9, ?_⟩
  · intro x hx
    exact hx.2
  · intro e he x hx
    exact hstab e he x hx

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
