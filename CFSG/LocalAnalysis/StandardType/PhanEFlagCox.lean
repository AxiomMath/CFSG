module

public import CFSG.LocalAnalysis.StandardType.PhanEFlagInv
public import CFSG.Monster.B.Geometry.Coxeter
public import CFSG.Permutation.SymmetricCoxeter
import CFSG.LocalAnalysis.ComponentInitial.LinearHigherDescents

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Flag

open CFSG.Monster.B.Geometry
open CFSG.Permutation
open CFSG.LocalAnalysis.ComponentInitial

variable {m : ℕ}

private lemma q2cFC_A_apply (i j : Fin m) :
    (CoxeterMatrix.A m) i j =
      if i = j then 1
      else if (j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ) then 3 else 2 :=
  rfl

private lemma q2cFC_A_apply_of_ne {i j : Fin m} (hij : i ≠ j) :
    (CoxeterMatrix.A m) i j =
      if (j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ) then 3 else 2 := by
  rw [q2cFC_A_apply, if_neg hij]

private lemma q2cFC_fin_ne {n : ℕ} {a b : Fin n} (h : (a : ℕ) ≠ (b : ℕ)) : a ≠ b :=
  fun hh => h (congrArg Fin.val hh)

private lemma q2cFC_adjSwap_braid (i j : Fin m) (h : (i : ℕ) + 1 = (j : ℕ)) :
    adjSwap i * adjSwap j * adjSwap i = adjSwap j * adjSwap i * adjSwap j := by
  have hji : j.castSucc = i.succ :=
    Fin.ext (by simp only [Fin.val_castSucc, Fin.val_succ]; omega)
  simp only [adjSwap, hji]
  exact SymmetricCoxeter.swap_braid
    (q2cFC_fin_ne (by simp only [Fin.val_castSucc, Fin.val_succ]; omega))
    (q2cFC_fin_ne (by simp only [Fin.val_castSucc, Fin.val_succ]; omega))
    (q2cFC_fin_ne (by simp only [Fin.val_castSucc, Fin.val_succ]; omega))

private lemma q2cFC_adjSwap_comm (i j : Fin m) (hij : (i : ℕ) ≠ (j : ℕ))
    (hna : ¬ ((j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ))) :
    adjSwap i * adjSwap j = adjSwap j * adjSwap i := by
  have h1 : (j : ℕ) + 1 ≠ (i : ℕ) := fun hh => hna (Or.inl hh)
  have h2 : (i : ℕ) + 1 ≠ (j : ℕ) := fun hh => hna (Or.inr hh)
  simp only [adjSwap]
  exact SymmetricCoxeter.swap_mul_swap_comm
    (q2cFC_fin_ne (by simp only [Fin.val_castSucc, Fin.val_succ]; omega))
    (q2cFC_fin_ne (by simp only [Fin.val_castSucc, Fin.val_succ]; omega))
    (q2cFC_fin_ne (by simp only [Fin.val_castSucc, Fin.val_succ]; omega))
    (q2cFC_fin_ne (by simp only [Fin.val_castSucc, Fin.val_succ]; omega))

private lemma q2cFC_pow_three_of_braid {G : Type*} [Group G] {x y : G} (hx : x * x = 1)
    (hy : y * y = 1) (hb : x * y * x = y * x * y) : (x * y) ^ 3 = 1 := by
  have h2 : (y * x) ^ 2 = x * y := by
    calc (y * x) ^ 2 = y * x * y * x := by rw [pow_two]; group
      _ = (y * x * y) * x := by group
      _ = (x * y * x) * x := by rw [hb]
      _ = x * y * (x * x) := by group
      _ = x * y := by rw [hx, mul_one]
  calc (x * y) ^ 3 = x * (y * x) ^ 2 * y := by rw [pow_three', pow_two]; group
    _ = x * (x * y) * y := by rw [h2]
    _ = (x * x) * (y * y) := by group
    _ = 1 := by rw [hx, hy, one_mul]

private lemma q2cFC_braid_of_pow_three {G : Type*} [Group G] {x y : G} (hx : x * x = 1)
    (hy : y * y = 1) (h3 : (x * y) ^ 3 = 1) : x * y * x = y * x * y := by
  have h1 : (x * y * x) * (y * x * y) = 1 := by
    calc (x * y * x) * (y * x * y) = (x * y) ^ 3 := by rw [pow_three']; group
      _ = 1 := h3
  have h2 : x * y * x = (y * x * y)⁻¹ := eq_inv_of_mul_eq_one_left h1
  have h3' : (y * x * y)⁻¹ = y * x * y := by
    rw [mul_inv_rev, mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy]
    group
  rw [h2, h3']

private lemma q2cFC_pow_two_of_comm {G : Type*} [Group G] {x y : G} (hx : x * x = 1)
    (hy : y * y = 1) (hc : x * y = y * x) : (x * y) ^ 2 = 1 := by
  calc (x * y) ^ 2 = x * (y * x) * y := by rw [pow_two]; group
    _ = x * (x * y) * y := by rw [← hc]
    _ = (x * x) * (y * y) := by group
    _ = 1 := by rw [hx, hy, one_mul]

private lemma q2cFC_comm_of_pow_two {G : Type*} [Group G] {x y : G} (hx : x * x = 1)
    (hy : y * y = 1) (h2 : (x * y) ^ 2 = 1) : x * y = y * x := by
  have hxy : (x * y)⁻¹ = x * y :=
    inv_eq_of_mul_eq_one_right (by simpa [pow_two] using h2)
  rw [← hxy, mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy]

private lemma q2cFC_adjSwap_pow_three (i j : Fin m)
    (h : (j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ)) :
    (adjSwap i * adjSwap j) ^ 3 = 1 := by
  rcases h with h | h
  · exact q2cFC_pow_three_of_braid (adjSwap_mul_self i) (adjSwap_mul_self j)
      (q2cFC_adjSwap_braid j i h).symm
  · exact q2cFC_pow_three_of_braid (adjSwap_mul_self i) (adjSwap_mul_self j)
      (q2cFC_adjSwap_braid i j h)

private lemma q2cFC_isLiftable_adjSwap (m : ℕ) :
    (CoxeterMatrix.A m).IsLiftable (fun i : Fin m => (adjSwap i : Equiv.Perm (Fin (m + 1)))) := by
  intro i j
  rcases eq_or_ne i j with rfl | hij
  · rw [(CoxeterMatrix.A m).diagonal i, pow_one, adjSwap_mul_self]
  · rw [q2cFC_A_apply_of_ne hij]
    by_cases hadj : (j : ℕ) + 1 = (i : ℕ) ∨ (i : ℕ) + 1 = (j : ℕ)
    · rw [if_pos hadj]
      exact q2cFC_adjSwap_pow_three i j hadj
    · rw [if_neg hadj]
      exact q2cFC_pow_two_of_comm (adjSwap_mul_self i) (adjSwap_mul_self j)
        (q2cFC_adjSwap_comm i j (fun hh => hij (Fin.ext hh)) hadj)

private noncomputable def q2cFC_x (m : ℕ) : ℕ → (CoxeterMatrix.A m).Group :=
  fun i => if h : i < m then (CoxeterMatrix.A m).toCoxeterSystem.simple ⟨i, h⟩ else 1

private lemma q2cFC_x_of_lt {i : ℕ} (hi : i < m) :
    q2cFC_x m i = (CoxeterMatrix.A m).toCoxeterSystem.simple ⟨i, hi⟩ := by
  rw [q2cFC_x, dif_pos hi]

private theorem q2cFC_isCoxeterA_x (m : ℕ) :
    SymmetricCoxeter.IsCoxeterA m (q2cFC_x m) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [q2cFC_x_of_lt hi]
    exact (CoxeterMatrix.A m).toCoxeterSystem.simple_mul_simple_self ⟨i, hi⟩
  · intro i hi
    have hi' : i < m := by omega
    rw [q2cFC_x_of_lt hi', q2cFC_x_of_lt hi]
    have h3 : ((CoxeterMatrix.A m).toCoxeterSystem.simple ⟨i, hi'⟩ *
        (CoxeterMatrix.A m).toCoxeterSystem.simple ⟨i + 1, hi⟩) ^ 3 = 1 := by
      have hM : (CoxeterMatrix.A m) ⟨i, hi'⟩ ⟨i + 1, hi⟩ = 3 := by
        rw [q2cFC_A_apply, if_neg (by simp [Fin.ext_iff]), if_pos]
        exact Or.inr (by simp)
      rw [← hM]
      exact (CoxeterMatrix.A m).toCoxeterSystem.simple_mul_simple_pow ⟨i, hi'⟩ ⟨i + 1, hi⟩
    exact q2cFC_braid_of_pow_three
      ((CoxeterMatrix.A m).toCoxeterSystem.simple_mul_simple_self ⟨i, hi'⟩)
      ((CoxeterMatrix.A m).toCoxeterSystem.simple_mul_simple_self ⟨i + 1, hi⟩) h3
  · intro i j hij hj
    have hi : i < m := by omega
    have hj' : j < m := by omega
    rw [q2cFC_x_of_lt hi, q2cFC_x_of_lt hj']
    have h2 : ((CoxeterMatrix.A m).toCoxeterSystem.simple ⟨i, hi⟩ *
        (CoxeterMatrix.A m).toCoxeterSystem.simple ⟨j, hj'⟩) ^ 2 = 1 := by
      have hM : (CoxeterMatrix.A m) ⟨i, hi⟩ ⟨j, hj'⟩ = 2 := by
        rw [q2cFC_A_apply_of_ne (by simp [Fin.ext_iff]; omega)]
        rw [if_neg]
        simp only [Fin.val_mk, not_or]
        omega
      rw [← hM]
      exact (CoxeterMatrix.A m).toCoxeterSystem.simple_mul_simple_pow ⟨i, hi⟩ ⟨j, hj'⟩
    exact q2cFC_comm_of_pow_two
      ((CoxeterMatrix.A m).toCoxeterSystem.simple_mul_simple_self ⟨i, hi⟩)
      ((CoxeterMatrix.A m).toCoxeterSystem.simple_mul_simple_self ⟨j, hj'⟩) h2

private noncomputable def q2cFC_φ (m : ℕ) :
    (CoxeterMatrix.A m).Group →* Equiv.Perm (Fin (m + 1)) :=
  (CoxeterMatrix.A m).toCoxeterSystem.lift
    ⟨fun i : Fin m => (adjSwap i : Equiv.Perm (Fin (m + 1))), q2cFC_isLiftable_adjSwap m⟩

private theorem q2cFC_φ_simple (m : ℕ) (i : Fin m) :
    q2cFC_φ m ((CoxeterMatrix.A m).toCoxeterSystem.simple i) = adjSwap i :=
  (CoxeterMatrix.A m).toCoxeterSystem.lift_apply_simple (q2cFC_isLiftable_adjSwap m) i

private noncomputable def q2cFC_ψ (m : ℕ) :
    Equiv.Perm (Fin (m + 1)) →* (CoxeterMatrix.A m).Group :=
  (SymmetricCoxeter.exists_hom_perm m (q2cFC_x m) (q2cFC_isCoxeterA_x m)).choose

private theorem q2cFC_ψ_adjSwap (m : ℕ) (i : ℕ) (hi : i < m) :
    q2cFC_ψ m (SymmetricCoxeter.adjSwap m i) = q2cFC_x m i :=
  (SymmetricCoxeter.exists_hom_perm m (q2cFC_x m) (q2cFC_isCoxeterA_x m)).choose_spec i hi

private lemma q2cFC_adjSwap_eq (i : Fin m) :
    adjSwap i = SymmetricCoxeter.adjSwap m i.val := by
  rw [SymmetricCoxeter.adjSwap_of_lt i.isLt]
  rfl

private theorem q2cFC_φψ (m : ℕ) :
    (q2cFC_ψ m).comp (q2cFC_φ m) = MonoidHom.id (CoxeterMatrix.A m).Group := by
  apply (CoxeterMatrix.A m).toCoxeterSystem.ext_simple
  intro i
  simp only [MonoidHom.comp_apply, MonoidHom.id_apply, q2cFC_φ_simple m i, q2cFC_adjSwap_eq i,
    q2cFC_ψ_adjSwap m i.val i.isLt, q2cFC_x_of_lt i.isLt]

private theorem q2cFC_ψφ (m : ℕ) :
    (q2cFC_φ m).comp (q2cFC_ψ m) = MonoidHom.id (Equiv.Perm (Fin (m + 1))) := by
  apply MonoidHom.ext
  intro σ
  have hσ : σ ∈ Subgroup.closure (SymmetricCoxeter.adjSwap m '' Set.Iio m) := by
    rw [SymmetricCoxeter.closure_adjSwap]
    exact Subgroup.mem_top σ
  induction hσ using Subgroup.closure_induction with
  | mem x hx =>
      obtain ⟨i, hi, rfl⟩ := hx
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply, q2cFC_ψ_adjSwap m i hi,
        q2cFC_x_of_lt hi, q2cFC_φ_simple m ⟨i, hi⟩, q2cFC_adjSwap_eq ⟨i, hi⟩]
  | one => simp
  | mul x y hx hy ihx ihy => simp only [map_mul, ihx, ihy]
  | inv x hx ih => simp only [map_inv, ih]

noncomputable def symCoxEquiv (m : ℕ) :
    (CoxeterMatrix.A m).Group ≃* Equiv.Perm (Fin (m + 1)) :=
  MonoidHom.toMulEquiv (q2cFC_φ m) (q2cFC_ψ m) (q2cFC_φψ m) (q2cFC_ψφ m)

theorem symCoxEquiv_simple (i : Fin m) :
    symCoxEquiv m ((CoxeterMatrix.A m).toCoxeterSystem.simple i) = adjSwap i :=
  q2cFC_φ_simple m i

@[expose] noncomputable def symCox (m : ℕ) :
    CoxeterSystem (CoxeterMatrix.A m) (Equiv.Perm (Fin (m + 1))) :=
  (CoxeterMatrix.A m).toCoxeterSystem.map (symCoxEquiv m)

theorem symCox_simple (i : Fin m) : (symCox m).simple i = adjSwap i := by
  simp only [symCox, CoxeterSystem.map_simple, symCoxEquiv_simple]

private lemma q2cFC_invCount_one (n : ℕ) : invCount (1 : Equiv.Perm (Fin n)) = 0 := by
  rw [invCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  rintro ⟨a, b⟩ - ⟨hab, hba⟩
  exact absurd hab (not_lt.mpr hba.le)

private lemma q2cFC_exists_adjacent_descent {σ : Equiv.Perm (Fin (m + 1))} (hσ : σ ≠ 1) :
    ∃ i : Fin m, σ i.succ < σ i.castSucc := by
  obtain ⟨i, hi, hin, hdesc⟩ :=
    LinearFlag.exists_descent (n := m + 1) (w := σ⁻¹) (by simpa [inv_eq_one] using hσ)
  refine ⟨⟨i - 1, by omega⟩, ?_⟩
  have h1 : (⟨i - 1, by omega⟩ : Fin m).succ = ⟨i, hin⟩ := Fin.ext (by simp; omega)
  rw [h1]
  simp only [inv_inv] at hdesc
  exact hdesc

private lemma q2cFC_invCount_le_length (σ : Equiv.Perm (Fin (m + 1))) :
    invCount σ ≤ (symCox m).length σ := by
  obtain ⟨ω, hω, rfl⟩ := (symCox m).exists_isReduced σ
  rw [hω.eq]
  clear hω
  induction ω with
  | nil => simp [q2cFC_invCount_one]
  | cons i ω ih =>
    rw [CoxeterSystem.wordProd_cons, List.length_cons, symCox_simple]
    have hne : ((symCox m).wordProd ω)⁻¹ i.castSucc ≠ ((symCox m).wordProd ω)⁻¹ i.succ :=
      fun hh => (Fin.castSucc_lt_succ (i := i)).ne (((symCox m).wordProd ω)⁻¹.injective hh)
    rcases lt_or_gt_of_ne hne with h | h
    · have hcount := invCount_adjSwap_mul_of_lt ((symCox m).wordProd ω) i h
      omega
    · have hcount := invCount_adjSwap_mul_of_gt ((symCox m).wordProd ω) i h
      omega

private lemma q2cFC_length_le_invCount (σ : Equiv.Perm (Fin (m + 1))) :
    (symCox m).length σ ≤ invCount σ := by
  induction hn : invCount σ using Nat.strong_induction_on generalizing σ with
  | _ n ih =>
    rcases eq_or_ne σ 1 with rfl | hσ
    · rw [← hn, q2cFC_invCount_one]
      simp
    · obtain ⟨i, hdesc⟩ := q2cFC_exists_adjacent_descent hσ
      have hcount : invCount (σ * adjSwap i) + 1 = invCount σ :=
        invCount_mul_adjSwap_of_gt σ i hdesc
      have hlt : invCount (σ * adjSwap i) < n := by omega
      have ih' : (symCox m).length (σ * adjSwap i) ≤ invCount (σ * adjSwap i) :=
        ih _ hlt (σ * adjSwap i) rfl
      have hle : (symCox m).length σ ≤ (symCox m).length (σ * adjSwap i) + 1 := by
        have h := (symCox m).length_mul_le (σ * adjSwap i) (adjSwap i)
        have hmul : (σ * adjSwap i) * adjSwap i = σ := by
          rw [mul_assoc, adjSwap_mul_self, mul_one]
        rw [hmul] at h
        have hlen : (symCox m).length (adjSwap i) = 1 := by
          rw [← symCox_simple i, CoxeterSystem.length_simple]
        omega
      omega

theorem symCox_length (σ : Equiv.Perm (Fin (m + 1))) : (symCox m).length σ = invCount σ :=
  le_antisymm (q2cFC_length_le_invCount σ) (q2cFC_invCount_le_length σ)

theorem longest_symCox_univ (m : ℕ) :
    longest (symCox m) Set.univ = (Fin.revPerm : Equiv.Perm (Fin (m + 1))) := by
  have hlong : IsLongest (symCox m) Set.univ (Fin.revPerm : Equiv.Perm (Fin (m + 1))) := by
    refine ⟨?_, ?_⟩
    · rw [CoxeterSystem.parabolic_univ]
      exact Subgroup.mem_top _
    · intro v _
      rw [symCox_length, symCox_length, invCount_revPerm (m + 1)]
      simpa using invCount_le v
  exact hlong.eq_longest.symm

theorem length_longest_symCox_univ (m : ℕ) :
    (symCox m).length (longest (symCox m) Set.univ) = (m + 1) * m / 2 := by
  rw [longest_symCox_univ, symCox_length, invCount_revPerm]
  simp

end CFSG.ClassicalInvolution.Phan.PhanE.Flag
