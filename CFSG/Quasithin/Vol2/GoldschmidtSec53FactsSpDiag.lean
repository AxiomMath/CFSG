module

public import CFSG.Quasithin.SteinbergBSSymplecticRoots
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinSp4

public section

namespace CFSG.Quasithin.H13.Sec53F

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.Quasithin.SteinbergBS
  CFSG.QuasithinUnique.Fin257.Sp4 CFSG.Open

section Diag

variable {F : Type} [Field F] [CharP F 2]

abbrev bor (F : Type) [Field F] [CharP F 2] : Subgroup (antiSp F) :=
  Subgroup.normalizer (antiUnipotent F : Set (antiSp F))

omit [CharP F 2] in
theorem glMat_mul_diag {x y : antiSp F}
    (hx : ∀ i j : Fin 4, j < i → glMat (x : GL (Fin 4) F) i j = 0)
    (hy : ∀ i j : Fin 4, j < i → glMat (y : GL (Fin 4) F) i j = 0) (i : Fin 4) :
    glMat ((x * y : antiSp F) : GL (Fin 4) F) i i =
      glMat (x : GL (Fin 4) F) i i * glMat (y : GL (Fin 4) F) i i := by
  rw [glMat_mul, Matrix.mul_apply, Finset.sum_eq_single i]
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [hx i k h, zero_mul]
    · rw [hy k i h, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ i) h

@[expose] noncomputable def dgHom (F : Type) [Field F] [CharP F 2] (i : Fin 4) : ↥(bor F) →* F where
  toFun x := glMat ((x : antiSp F) : GL (Fin 4) F) i i
  map_one' := by simp
  map_mul' x y := glMat_mul_diag (upper_of_mem_normalizer x.2) (upper_of_mem_normalizer y.2) i

theorem dgHom_apply (i : Fin 4) (x : ↥(bor F)) :
    dgHom F i x = glMat ((x : antiSp F) : GL (Fin 4) F) i i := rfl

theorem mem_U_of_dg_eq_one {x : antiSp F} (hx : x ∈ bor F)
    (h0 : glMat (x : GL (Fin 4) F) 0 0 = 1) (h1 : glMat (x : GL (Fin 4) F) 1 1 = 1) :
    x ∈ antiUnipotent F := by
  have hU := upper_of_mem_normalizer hx
  obtain ⟨r1, r2, -⟩ := upper_relations hU
  refine (mem_antiUnipotent_iff_upper x).mpr ⟨hU, fun i => ?_⟩
  fin_cases i
  · exact h0
  · exact h1
  · simpa [h1] using r2
  · simpa [h0] using r1

theorem glMat_diag_of_mem_U {x : antiSp F} (hx : x ∈ antiUnipotent F) (i : Fin 4) :
    glMat (x : GL (Fin 4) F) i i = 1 :=
  ((mem_antiUnipotent_iff_upper x).mp hx).2 i

theorem eq_one_of_pow_two_pow_eq_one {y : F} {a : ℕ} (h : y ^ 2 ^ a = 1) : y = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : (y - 1) ^ 2 ^ a = 0 := by
    rw [sub_pow_char_pow, h, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero a two_ne_zero) |>.mp h1)

theorem mem_U_of_pow_eq_one {x : antiSp F} (hx : x ∈ bor F) {a : ℕ} (h : x ^ 2 ^ a = 1) :
    x ∈ antiUnipotent F := by
  have hpow : (⟨x, hx⟩ : ↥(bor F)) ^ 2 ^ a = 1 := Subtype.ext (by simpa using h)
  have key : ∀ i : Fin 4, glMat (x : GL (Fin 4) F) i i = 1 := fun i => by
    refine eq_one_of_pow_two_pow_eq_one (a := a) ?_
    have := congrArg (dgHom F i) hpow
    rwa [map_pow, map_one] at this
  exact mem_U_of_dg_eq_one hx (key 0) (key 1)

omit [CharP F 2] in
theorem glMat_dSp_diag (s t : Fˣ) :
    glMat ((dSp s t : antiSp F) : GL (Fin 4) F) 0 0 = s ∧
      glMat ((dSp s t : antiSp F) : GL (Fin 4) F) 1 1 = t := by
  simp [glMat_dSp, dSpMat]

theorem isSolvable_bor [Finite F] (hU : IsPGroup 2 (antiUnipotent F)) :
    Group.IsSolvable ↥(bor F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent (antiUnipotent F) := hU.isNilpotent
  have : Group.IsSolvable (antiUnipotent F) := inferInstance
  have : Group.IsSolvable (Fˣ × Fˣ) := Group.isSolvable_of_comm fun a b => mul_comm a b
  let g : ↥(bor F) →* Fˣ × Fˣ :=
    (MonoidHom.toHomUnits (dgHom F 0)).prod (MonoidHom.toHomUnits (dgHom F 1))
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion
    (Subgroup.le_normalizer : antiUnipotent F ≤ bor F)) g ?_
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have h0 : dgHom F 0 x = 1 := by
    have := congrArg (fun p : Fˣ × Fˣ => (p.1 : F)) hx
    simpa [g] using this
  have h1 : dgHom F 1 x = 1 := by
    have := congrArg (fun p : Fˣ × Fˣ => (p.2 : F)) hx
    simpa [g] using this
  have hxU : (x : antiSp F) ∈ antiUnipotent F := mem_U_of_dg_eq_one x.2 h0 h1
  exact ⟨⟨x, hxU⟩, rfl⟩

end Diag

end CFSG.Quasithin.H13.Sec53F
