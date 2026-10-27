module

public import CFSG.LieType.Universal.Spin.Generation.Datum

public section

namespace CFSG.RankThree.PartTwo.Census.Carrier.SpinD

open CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal QuadraticMap
open scoped commutatorElement

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {n : ℕ} (F : HypFrame Q n) (G : Subgroup (V ≃ₗ[K] V))

@[expose] def RootMem (i : Fin n) (s : Bool) (j : Fin n) (t : Bool) : Prop :=
  ∀ c : K, eichler Q (F.vec j t) (c • F.vec i s) ∈ G

theorem polar_vec_smul_vec_of_ne {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K) :
    polar Q (F.vec j t) (c • F.vec i s) = 0 := by
  rw [polar_smul_right, F.polar_vec_of_ne (Ne.symm hij), smul_zero]

theorem eichler_vec_swap {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : K) :
    eichler Q (F.vec i s) (c • F.vec j t) = eichler Q (F.vec j t) ((-c) • F.vec i s) := by
  refine LinearEquiv.ext fun x => ?_
  rw [eichler_apply (F.map_vec i s) (polar_vec_smul_vec_of_ne F (Ne.symm hij) t s c),
    eichler_apply (F.map_vec j t) (polar_vec_smul_vec_of_ne F hij s t (-c))]
  simp only [polar_smul_right, QuadraticMap.map_smul, F.map_vec, smul_eq_mul, mul_zero]
  module

variable {F G}

theorem rootMem_symm {i j : Fin n} (hij : i ≠ j) {s t : Bool} (h : RootMem F G i s j t) :
    RootMem F G j t i s := fun c => by
  rw [eichler_vec_swap F hij s t c]
  exact h (-c)

theorem rootMem_comm {i j k : Fin n} (hik : i ≠ k) (hjk : j ≠ k) (hij : i ≠ j) {s r t : Bool}
    (h1 : RootMem F G i s k r) (h2 : RootMem F G k (!r) j t) : RootMem F G i s j t := by
  intro c
  set a := eichler Q (F.vec k r) ((1 : K) • F.vec i s)
  have ha : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q := eichler_mem_orthogonalGroup Q _ _
  have hfix : a (F.vec j t) = F.vec j t := by
    rw [eichler_apply (F.map_vec k r) (polar_vec_smul_vec_of_ne F hik s r 1)]
    simp only [F.polar_vec_of_ne hjk, polar_smul_right, F.polar_vec_of_ne (Ne.symm hij),
      smul_eq_mul, mul_zero, zero_smul, add_zero, sub_zero, QuadraticMap.map_smul, F.map_vec]
  have hpol : polar Q (F.vec j t) (c • F.vec k (!r)) = 0 := by
    rw [polar_smul_right, F.polar_vec_of_ne hjk, smul_zero]
  have hcomm := commutatorElement_eichler ha hfix hpol
  have hav : a (c • F.vec k (!r)) - c • F.vec k (!r) = c • F.vec i s := by
    rw [eichler_apply (F.map_vec k r) (polar_vec_smul_vec_of_ne F hik s r 1)]
    have hpv : polar Q (F.vec k (!r)) (F.vec k r) = 1 := by
      have := F.polar_vec_not k (!r)
      rwa [Bool.not_not] at this
    have h1' : polar Q (c • F.vec k (!r)) (F.vec k r) = c := by
      rw [polar_smul_left, hpv, smul_eq_mul, mul_one]
    simp only [h1', polar_smul_left, F.polar_vec_of_ne (Ne.symm hik), smul_eq_mul, mul_zero,
      F.map_vec, zero_add, one_smul]
    module
  rw [hav] at hcomm
  rw [← hcomm, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem (h1 1) (h2 c)) (inv_mem (h1 1))) (inv_mem (h2 c))

variable (F G)

@[expose] def SimpleMem (hn : 3 ≤ n) : Prop :=
  (∀ (k : Fin n) (hk : k.val + 1 < n),
    RootMem F G k true ⟨k.val + 1, hk⟩ false ∧ RootMem F G ⟨k.val + 1, hk⟩ true k false) ∧
  RootMem F G ⟨n - 2, by omega⟩ true ⟨n - 1, by omega⟩ true ∧
  RootMem F G ⟨n - 1, by omega⟩ false ⟨n - 2, by omega⟩ false

variable {F G}

theorem rootMem_diff_up {hn : 3 ≤ n} (h : SimpleMem F G hn) :
    ∀ (d : ℕ) (i j : Fin n), i.val + d + 1 = j.val → RootMem F G i true j false := by
  intro d
  induction d with
  | zero =>
    intro i j hij
    have hk : i.val + 1 < n := by omega
    have e : j = ⟨i.val + 1, hk⟩ := Fin.ext (by simp only; omega)
    subst e
    exact (h.1 i hk).1
  | succ d ih =>
    intro i j hij
    have hk : j.val - 1 < n := by omega
    set k : Fin n := ⟨j.val - 1, hk⟩
    have h1 : RootMem F G i true k false := ih i k (by simp only [k]; omega)
    have hk1 : k.val + 1 < n := by simp only [k]; omega
    have e : j = ⟨k.val + 1, hk1⟩ := Fin.ext (by simp only [k]; omega)
    have h2 : RootMem F G k true j false := by
      rw [e]
      exact (h.1 k hk1).1
    exact rootMem_comm (r := false) (Fin.ne_of_val_ne (by simp only [k]; omega))
      (Fin.ne_of_val_ne (by simp only [k]; omega)) (Fin.ne_of_val_ne (by omega)) h1 h2

theorem rootMem_diff_down {hn : 3 ≤ n} (h : SimpleMem F G hn) :
    ∀ (d : ℕ) (i j : Fin n), j.val + d + 1 = i.val → RootMem F G i true j false := by
  intro d
  induction d with
  | zero =>
    intro i j hij
    have hk : j.val + 1 < n := by omega
    have e : i = ⟨j.val + 1, hk⟩ := Fin.ext (by simp only; omega)
    subst e
    exact (h.1 j hk).2
  | succ d ih =>
    intro i j hij
    have hk : j.val + 1 < n := by omega
    set k : Fin n := ⟨j.val + 1, hk⟩
    have h1 : RootMem F G i true k false := ih i k (by simp only [k]; omega)
    have h2 : RootMem F G k true j false := (h.1 j hk).2
    exact rootMem_comm (r := false) (Fin.ne_of_val_ne (by simp only [k]; omega))
      (Fin.ne_of_val_ne (by simp only [k]; omega)) (Fin.ne_of_val_ne (by omega)) h1 h2

theorem rootMem_diff {hn : 3 ≤ n} (h : SimpleMem F G hn) {i j : Fin n} (hij : i ≠ j) :
    RootMem F G i true j false ∧ RootMem F G i false j true := by
  have key : ∀ {i j : Fin n}, i ≠ j → RootMem F G i true j false := by
    intro i j hij
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hlt | hgt
    · exact rootMem_diff_up h (j.val - i.val - 1) i j (by omega)
    · exact rootMem_diff_down h (i.val - j.val - 1) i j (by omega)
  exact ⟨key hij, rootMem_symm (Ne.symm hij) (key (Ne.symm hij))⟩

theorem rootMem_sum {hn : 3 ≤ n} (h : SimpleMem F G hn) {i j : Fin n} (hij : i ≠ j) :
    RootMem F G i true j true := by
  set a : Fin n := ⟨n - 2, by omega⟩
  set b : Fin n := ⟨n - 1, by omega⟩
  have hab : a ≠ b := Fin.ne_of_val_ne (by simp only [a, b]; omega)
  have hb : ∀ {i : Fin n}, i ≠ b → RootMem F G i true b true := by
    intro i hib
    by_cases hia : i = a
    · rw [hia]
      exact h.2.1
    · exact rootMem_comm (r := false) hia (Ne.symm hab) hib (rootMem_diff h hia).1 h.2.1
  by_cases hjb : j = b
  · rw [hjb] at hij ⊢
    exact hb hij
  · by_cases hib : i = b
    · rw [hib] at hij ⊢
      exact rootMem_symm (Ne.symm hij) (hb (Ne.symm hij))
    · exact rootMem_comm (r := true) hib hjb hij (hb hib) (rootMem_diff h (Ne.symm hjb)).2

theorem rootMem_negSum {hn : 3 ≤ n} (h : SimpleMem F G hn) {i j : Fin n} (hij : i ≠ j) :
    RootMem F G i false j false := by
  set a : Fin n := ⟨n - 2, by omega⟩
  set b : Fin n := ⟨n - 1, by omega⟩
  have hab : a ≠ b := Fin.ne_of_val_ne (by simp only [a, b]; omega)
  have hab' : RootMem F G a false b false := rootMem_symm (Ne.symm hab) h.2.2
  have hb : ∀ {i : Fin n}, i ≠ b → RootMem F G i false b false := by
    intro i hib
    by_cases hia : i = a
    · rw [hia]
      exact hab'
    · exact rootMem_comm (r := true) hia (Ne.symm hab) hib (rootMem_diff h hia).2 hab'
  by_cases hjb : j = b
  · rw [hjb] at hij ⊢
    exact hb hij
  · by_cases hib : i = b
    · rw [hib] at hij ⊢
      exact rootMem_symm (Ne.symm hij) (hb (Ne.symm hij))
    · exact rootMem_comm (r := false) hib hjb hij (hb hib) (rootMem_diff h (Ne.symm hjb)).1

theorem rootMem_of_simple {hn : 3 ≤ n} (h : SimpleMem F G hn) {i j : Fin n} (hij : i ≠ j)
    (s t : Bool) : RootMem F G i s j t := by
  cases s <;> cases t
  · exact rootMem_negSum h hij
  · exact (rootMem_diff h hij).2
  · exact (rootMem_diff h hij).1
  · exact rootMem_sum h hij

theorem elementaryGroup_le_of_simple {K : Type} [Field K] {n : ℕ} (hn : 3 ≤ n)
    {G : Subgroup ((Fin n ⊕ Fin n → K) ≃ₗ[K] (Fin n ⊕ Fin n → K))}
    (h : SimpleMem (plusFrame n K hn) G hn) : elementaryGroup (quadPlus n K) ≤ G := by
  refine (plusFrame n K hn).elementaryGroup_le
    (fun hij s t c => rootMem_of_simple h hij s t c) (fun i s v hv => ?_) (fun v hv _ =>
      eq_zero_of_polar_plusFrame_vec hn hv)
  rw [eq_zero_of_polar_plusFrame_vec hn hv, eichler_zero_right]
  exact one_mem G

end CFSG.RankThree.PartTwo.Census.Carrier.SpinD
