module

public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

variable {n : ℕ}

@[expose] def IsUniTri (M : Matrix (Fin n) (Fin n) (ZMod 2)) : Prop :=
  M.IsUpperTriangular ∧ ∀ i, M i i = 1

theorem isUniTri_one : IsUniTri (1 : Matrix (Fin n) (Fin n) (ZMod 2)) :=
  ⟨blockTriangular_one, fun i => one_apply_eq i⟩

theorem IsUniTri.mul {A B : Matrix (Fin n) (Fin n) (ZMod 2)} (hA : IsUniTri A)
    (hB : IsUniTri B) : IsUniTri (A * B) := by
  refine ⟨hA.1.mul hB.1, fun i => ?_⟩
  rw [mul_apply, Finset.sum_eq_single i, hA.2 i, hB.2 i, mul_one]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hA.1 h, zero_mul]
    · rw [hB.1 h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem inv_mem_of_mul_closed {G : Type*} [Group G] [Finite G] {S : Set G} (h1 : (1 : G) ∈ S)
    (hmul : ∀ a b, a ∈ S → b ∈ S → a * b ∈ S) {x : G} (hx : x ∈ S) : x⁻¹ ∈ S := by
  have hpow : ∀ k : ℕ, x ^ k ∈ S := fun k => by
    induction k with
    | zero => simpa using h1
    | succ k ih => rw [pow_succ]; exact hmul _ _ ih hx
  have hx' : x⁻¹ = x ^ (orderOf x - 1) := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
  rw [hx']
  exact hpow _

@[expose] def uniSL (n : ℕ) : Subgroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) where
  carrier := {A | IsUniTri (A : Matrix (Fin n) (Fin n) (ZMod 2))}
  one_mem' := isUniTri_one
  mul_mem' := fun ha hb => IsUniTri.mul ha hb
  inv_mem' := fun hx => inv_mem_of_mul_closed
    (S := {A : Matrix.SpecialLinearGroup (Fin n) (ZMod 2) |
      IsUniTri (A : Matrix (Fin n) (Fin n) (ZMod 2))}) isUniTri_one
    (fun _ _ ha hb => IsUniTri.mul ha hb) hx

@[expose] def par4 (v : Fin 6 → ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, v 0, v 1, v 2; 0, 1, v 3, v 4; 0, 0, 1, v 5; 0, 0, 0, 1]

theorem isUniTri_par4 (v : Fin 6 → ZMod 2) : IsUniTri (par4 v) := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> simp_all [par4]
  · fin_cases i <;> simp [par4]

theorem det_par4 (v : Fin 6 → ZMod 2) : (par4 v).det = 1 := by
  rw [det_of_isUpperTriangular (isUniTri_par4 v).1]
  exact Finset.prod_eq_one fun i _ => (isUniTri_par4 v).2 i

@[expose] def par4SL (v : Fin 6 → ZMod 2) : ↥(uniSL 4) :=
  ⟨⟨par4 v, det_par4 v⟩, isUniTri_par4 v⟩

theorem par4_injective : Function.Injective par4 := by
  intro v w h
  funext k
  fin_cases k
  · exact congrFun (congrFun h 0) 1
  · exact congrFun (congrFun h 0) 2
  · exact congrFun (congrFun h 0) 3
  · exact congrFun (congrFun h 1) 2
  · exact congrFun (congrFun h 1) 3
  · exact congrFun (congrFun h 2) 3

theorem exists_par4 {M : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hM : IsUniTri M) :
    M = par4 ![M 0 1, M 0 2, M 0 3, M 1 2, M 1 3, M 2 3] := by
  obtain ⟨hT, hD⟩ := hM
  have h10 : M 1 0 = 0 := hT (by decide)
  have h20 : M 2 0 = 0 := hT (by decide)
  have h21 : M 2 1 = 0 := hT (by decide)
  have h30 : M 3 0 = 0 := hT (by decide)
  have h31 : M 3 1 = 0 := hT (by decide)
  have h32 : M 3 2 = 0 := hT (by decide)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [par4, hD, h10, h20, h21, h30, h31, h32]

theorem par4SL_bijective : Function.Bijective par4SL := by
  constructor
  · intro v w h
    exact par4_injective (congrArg (fun A : ↥(uniSL 4) =>
      ((A : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))) h)
  · intro A
    set M := ((A : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2))
      with hM
    refine ⟨![M 0 1, M 0 2, M 0 3, M 1 2, M 1 3, M 2 3],
      Subtype.ext (Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_)⟩
    exact (congrFun (congrFun (exists_par4 A.2) i) j).symm

theorem card_uniSL_four : Nat.card (uniSL 4) = 64 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ par4SL_bijective), Nat.card_eq_fintype_card]
  simp

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
