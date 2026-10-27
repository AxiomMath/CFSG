module

public import CFSG.Open.MonsterDefs

public section

namespace CFSG.Monster.Existence.Compat

open CFSG.Open Matrix

abbrev F4 : Type := GaloisField 2 2

theorem card_F4 : Nat.card F4 = 4 := by
  simpa using GaloisField.card 2 2 (by norm_num)

theorem exists_omega : ∃ ω : F4, ω ^ 3 = 1 ∧ ω ^ 2 ≠ ω := by
  classical
  have : Fintype F4 := Fintype.ofFinite F4
  have hcard : Fintype.card F4ˣ = 3 := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, card_F4]
  have : Nontrivial F4ˣ := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨u, hu⟩ := exists_ne (1 : F4ˣ)
  refine ⟨u, ?_, fun h => hu ?_⟩
  · have := pow_card_eq_one (x := u)
    rw [hcard] at this
    simpa using congrArg Units.val this
  · apply Units.ext
    have h1 : (u : F4) * ((u : F4) - 1) = 0 := by rw [mul_sub, mul_one, ← sq, h, sub_self]
    rcases mul_eq_zero.1 h1 with h2 | h2
    · exact absurd h2 u.ne_zero
    · rw [Units.val_one]; exact sub_eq_zero.1 h2

@[expose] def IsHermSU (A : GL (Fin 6) F4) : Prop :=
  (A : Matrix (Fin 6) (Fin 6) F4).det = 1 ∧
    ∀ x y, monsterHerm ((A : Matrix (Fin 6) (Fin 6) F4) *ᵥ x)
      ((A : Matrix (Fin 6) (Fin 6) F4) *ᵥ y) = monsterHerm x y

theorem mem_monsterSU62_of_isHermSU {A : GL (Fin 6) F4} (h : IsHermSU A) : A ∈ monsterSU62 :=
  Subgroup.subset_closure h

@[expose] noncomputable def diagOmega (ω : F4) (i j : Fin 6) : Matrix (Fin 6) (Fin 6) F4 :=
  diagonal fun k => if k = i then ω else if k = j then ω ^ 2 else 1

theorem det_diagOmega {ω : F4} (hω : ω ^ 3 = 1) {i j : Fin 6} (hij : i ≠ j) :
    (diagOmega ω i j).det = 1 := by
  rw [diagOmega, det_diagonal]
  have : ∀ k : Fin 6, (if k = i then ω else if k = j then ω ^ 2 else 1) =
      (if k = i then ω else 1) * (if k = j then ω ^ 2 else 1) := by
    intro k
    rcases eq_or_ne k i with rfl | h1
    · simp [hij]
    · rcases eq_or_ne k j with rfl | h2
      · simp [h1]
      · simp [h1, h2]
  simp_rw [this]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.prod_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  rw [← pow_succ', hω]

theorem diagOmega_cube {ω : F4} (hω : ω ^ 3 = 1) (i j k : Fin 6) :
    (if k = i then ω else if k = j then ω ^ 2 else 1) ^ 3 = 1 := by
  rcases eq_or_ne k i with rfl | h1
  · simp [hω]
  · rcases eq_or_ne k j with rfl | h2
    · simp only [h1, ite_true, ite_false]
      rw [← pow_mul, mul_comm, pow_mul, hω, one_pow]
    · simp [h1, h2]

theorem isHermSU_diagOmega {ω : F4} (hω : ω ^ 3 = 1) {i j : Fin 6} (hij : i ≠ j)
    (hu : IsUnit (diagOmega ω i j).det) :
    IsHermSU (Matrix.GeneralLinearGroup.mk'' (diagOmega ω i j) hu) := by
  refine ⟨det_diagOmega hω hij, fun x y => ?_⟩
  show monsterHerm (diagOmega ω i j *ᵥ x) (diagOmega ω i j *ᵥ y) = monsterHerm x y
  simp only [monsterHerm, diagOmega, mulVec_diagonal]
  refine Finset.sum_congr rfl fun k _ => ?_
  set d := (if k = i then ω else if k = j then ω ^ 2 else 1) with hd
  have h3 : d ^ 3 = 1 := diagOmega_cube hω i j k
  calc d * x k * (d * y k) ^ 2 = d ^ 3 * (x k * y k ^ 2) := by ring
    _ = x k * y k ^ 2 := by rw [h3, one_mul]

theorem isHermSU_swap {i j : Fin 6} (hij : i ≠ j)
    (hu : IsUnit ((Equiv.swap i j).permMatrix F4).det) :
    IsHermSU (Matrix.GeneralLinearGroup.mk'' ((Equiv.swap i j).permMatrix F4) hu) := by
  refine ⟨?_, fun x y => ?_⟩
  · show ((Equiv.swap i j).permMatrix F4).det = 1
    rw [det_permutation, Equiv.Perm.sign_swap hij]
    simp [CharTwo.neg_eq]
  · show monsterHerm ((Equiv.swap i j).permMatrix F4 *ᵥ x)
      ((Equiv.swap i j).permMatrix F4 *ᵥ y) = monsterHerm x y
    simp only [monsterHerm, permMatrix_mulVec, Function.comp_apply]
    exact Equiv.sum_comp (Equiv.swap i j) fun k => x k * y k ^ 2

theorem center_monsterSU62_scalar (g : monsterSU62) (hg : g ∈ Subgroup.center monsterSU62) :
    ∃ c : F4ˣ, (g : GL (Fin 6) F4) = Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
  obtain ⟨ω, hω3, hω2⟩ := exists_omega
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 6) (Fin 6) F4,
      M = ((g : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) := ⟨_, rfl⟩
  have hcomm : ∀ A : GL (Fin 6) F4, A ∈ monsterSU62 →
      (A : Matrix (Fin 6) (Fin 6) F4) * M = M * (A : Matrix (Fin 6) (Fin 6) F4) := by
    intro A hA
    have h := Subgroup.mem_center_iff.1 hg ⟨A, hA⟩
    have h' := congrArg (fun u : monsterSU62 => ((u : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4)) h
    rw [hM]
    simpa using h'
  have hoff : ∀ i j, i ≠ j → M i j = 0 := by
    intro i j hij
    have hdet : IsUnit (diagOmega ω i j).det := by rw [det_diagOmega hω3 hij]; exact isUnit_one
    have hc := hcomm _ (mem_monsterSU62_of_isHermSU (isHermSU_diagOmega hω3 hij hdet))
    have h1 := congrFun (congrFun hc i) j
    change (diagOmega ω i j * M) i j = (M * diagOmega ω i j) i j at h1
    simp only [diagOmega, diagonal_mul, mul_diagonal, ite_true] at h1
    have hji : j ≠ i := Ne.symm hij
    simp only [hji, ite_false] at h1
    have h2 : M i j * (ω ^ 2 - ω) = 0 := by rw [mul_sub]; linear_combination -h1
    rcases mul_eq_zero.1 h2 with h3 | h3
    · exact h3
    · exact absurd (sub_eq_zero.1 h3) hω2
  obtain ⟨m, hm⟩ : ∃ m : Fin 6 → F4, M = diagonal m := by
    refine ⟨fun k => M k k, Matrix.ext fun i j => ?_⟩
    by_cases h : i = j
    · subst h; simp
    · rw [hoff i j h, diagonal_apply_ne _ h]
  have hdeq : ∀ i j, m i = m j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    have hu : IsUnit ((Equiv.swap i j).permMatrix F4).det := by
      rw [det_permutation, Equiv.Perm.sign_swap hij]
      simp [CharTwo.neg_eq]
    have hc := hcomm _ (mem_monsterSU62_of_isHermSU (isHermSU_swap hij hu))
    change (Equiv.swap i j).permMatrix F4 * M = M * (Equiv.swap i j).permMatrix F4 at hc
    have h1 : (Equiv.swap i j).permMatrix F4 *ᵥ (M *ᵥ Pi.single i (1 : F4)) =
        M *ᵥ ((Equiv.swap i j).permMatrix F4 *ᵥ Pi.single i (1 : F4)) := by
      rw [mulVec_mulVec, mulVec_mulVec, hc]
    have h2 := congrFun h1 j
    rw [permMatrix_mulVec, Function.comp_apply, hm, mulVec_diagonal, mulVec_diagonal,
      permMatrix_mulVec, Function.comp_apply, Equiv.swap_apply_right] at h2
    simpa using h2
  have hm0 : m = fun _ => m 0 := funext fun k => hdeq k 0
  have hunit : IsUnit (m 0) := by
    have h1 : IsUnit M.det := Matrix.isUnit_iff_isUnit_det _ |>.1 (hM ▸ (g : GL (Fin 6) F4).isUnit)
    rw [hm, det_diagonal, hm0] at h1
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
    exact (isUnit_pow_iff (by norm_num)).1 h1
  refine ⟨hunit.unit, Units.ext ?_⟩
  rw [Matrix.GeneralLinearGroup.coe_scalar, ← hM, hm, Matrix.scalar_apply]
  refine congrArg diagonal (funext fun k => ?_)
  rw [hdeq k 0, IsUnit.unit_spec]

end CFSG.Monster.Existence.Compat
