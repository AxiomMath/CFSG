module

public import CFSG.Quasithin.H13.U3SixNorm

public section

namespace CFSG.Quasithin.H13.U3

open CFSG.Quasithin Matrix

@[expose] def dotB (x y : ℕ) : Bool :=
  (List.range 6).foldr (fun i acc => (x.testBit i && y.testBit i) ^^ acc) false

theorem bit2_and (a b : Bool) : bit2 (a && b) = bit2 a * bit2 b := by
  cases a <;> cases b <;> decide

theorem bit2_dot_foldr (x y : ℕ) (l : List ℕ) :
    bit2 (l.foldr (fun i acc => (x.testBit i && y.testBit i) ^^ acc) false) =
      (l.map fun i => bit2 (x.testBit i) * bit2 (y.testBit i)).sum := by
  induction l with
  | nil => simp [bit2]
  | cons i l ih => rw [List.foldr_cons, List.map_cons, List.sum_cons, bit2_xor, ih, bit2_and]

theorem vecOf_dotProduct (x y : ℕ) : vecOf x ⬝ᵥ vecOf y = bit2 (dotB x y) := by
  rw [dotB, bit2_dot_foldr, list_sum_map_range,
    ← Fin.sum_univ_eq_sum_range (fun i => bit2 (x.testBit i) * bit2 (y.testBit i)) 6]
  rfl

@[expose] def b0c : List ℕ := [46, 33, 57, 37, 36, 31]

noncomputable def b0 : LinearMap.BilinForm (ZMod 2) W6 :=
  Matrix.toBilin' (colMat b0c)

theorem b0_apply (v w : W6) : b0 v w = v ⬝ᵥ (colMat b0c *ᵥ w) :=
  Matrix.toBilin'_apply' _ _ _

theorem b0_vecOf (x y : ℕ) : b0 (vecOf x) (vecOf y) = bit2 (dotB x (vapp b0c y)) := by
  rw [b0_apply, colMat_mulVec_vecOf, vecOf_dotProduct]

theorem b0c_alt : ∀ c < 64, dotB c (vapp b0c c) = false := by
  decide +kernel

theorem b0c_nondeg : ∀ c < 64, c ≠ 0 → ∃ n < 64, dotB c (vapp b0c n) = true := by
  decide +kernel

theorem b0_isAlt : b0.IsAlt := by
  intro v
  obtain ⟨c, hc, rfl⟩ := exists_vecOf v
  rw [b0_vecOf, b0c_alt c hc]
  rfl

theorem b0c_nondeg_right : ∀ c < 64, c ≠ 0 → ∃ n < 64, dotB n (vapp b0c c) = true := by
  decide +kernel

theorem b0_nondegenerate : b0.Nondegenerate := by
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · obtain ⟨c, hc, rfl⟩ := exists_vecOf v
    by_contra hne
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hne vecOf_zero
    obtain ⟨n, -, hn⟩ := b0c_nondeg c hc hc0
    have h := hv (vecOf n)
    rw [b0_vecOf, hn] at h
    exact absurd h (by decide)
  · obtain ⟨c, hc, rfl⟩ := exists_vecOf v
    by_contra hne
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact hne vecOf_zero
    obtain ⟨n, -, hn⟩ := b0c_nondeg_right c hc hc0
    have h := hv (vecOf n)
    rw [b0_vecOf, hn] at h
    exact absurd h (by decide)

@[expose] def n6Gens : List (List ℕ) :=
  [u6c 0, u6c 1, u6c 2, u6c 3, u6c 4, dc]

theorem b0c_invariant : ∀ m ∈ n6Gens, ∀ x < 64, ∀ y < 64,
    dotB (vapp m x) (vapp b0c (vapp m y)) = dotB x (vapp b0c y) := by
  decide +kernel

noncomputable def b0Stab : Subgroup (GL (Fin 6) (ZMod 2)) where
  carrier := {g | ∀ v w : W6, b0 ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v)
    ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ w) = b0 v w}
  one_mem' := fun v w => by simp
  mul_mem' := fun {g h} hg hh v w => by
    simp only [Set.mem_ofPred_eq] at hg hh ⊢
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hg, hh]
  inv_mem' := fun {g} hg v w => by
    simp only [Set.mem_ofPred_eq] at hg ⊢
    rw [← hg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mulVec, Matrix.one_mulVec]

theorem mem_b0Stab_of_code {g : GL (Fin 6) (ZMod 2)} {m : List ℕ} (hm : m ∈ n6Gens)
    (hg : (g : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat m) : g ∈ b0Stab := by
  intro v w
  obtain ⟨x, hx, rfl⟩ := exists_vecOf v
  obtain ⟨y, hy, rfl⟩ := exists_vecOf w
  rw [hg, colMat_mulVec_vecOf, colMat_mulVec_vecOf, b0_vecOf, b0_vecOf,
    b0c_invariant m hm x hx y hy]

theorem J6_le_b0Stab
    : J6 ≤ b0Stab := by
  show rho6.range ≤ b0Stab
  rw [MonoidHom.range_eq_map, ← u33Data.gen, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact mem_b0Stab_of_code (m := u6c 0) (by simp [n6Gens]) (by rw [rho6_abs.1]; rfl)
  · exact mem_b0Stab_of_code (m := u6c 1) (by simp [n6Gens]) (by rw [rho6_abs.2.1]; rfl)
  · exact mem_b0Stab_of_code (m := u6c 2) (by simp [n6Gens]) (by rw [rho6_abs.2.2.1]; rfl)
  · exact mem_b0Stab_of_code (m := u6c 3) (by simp [n6Gens]) (by rw [rho6_abs.2.2.2.1]; rfl)
  · exact mem_b0Stab_of_code (m := u6c 4) (by simp [n6Gens]) (by rw [rho6_abs.2.2.2.2]; rfl)

theorem b0_mulVec_of_mem_b0Stab {g : GL (Fin 6) (ZMod 2)} (hg : g ∈ b0Stab) (v w : W6) :
    b0 ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ v)
      ((g : Matrix (Fin 6) (Fin 6) (ZMod 2)) *ᵥ w) = b0 v w :=
  hg v w

theorem N6_le_b0Stab :
    N6 ≤ b0Stab :=
  sup_le (Subgroup.zpowers_le.2 (mem_b0Stab_of_code (m := dc) (by simp [n6Gens]) rfl))
    J6_le_b0Stab

end CFSG.Quasithin.H13.U3
