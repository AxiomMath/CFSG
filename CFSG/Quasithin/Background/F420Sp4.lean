module

public import CFSG.Quasithin.Background.F420Basic
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin.F420

open CFSG.Open (quasithinIsSylowTwo)
open CFSG.Assembly.LowTwoRank Matrix

section Matrices

variable {F : Type} [Field F]

abbrev spJ (F : Type) [Field F] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks 0 1 (-1) 0

@[expose] def spU (F : Type) [Field F] : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
  Matrix.fromBlocks !![1, 1; 0, 1] !![0, 1; 0, 1] 0 !![1, 0; 1, 1]

variable [CharP F 2]

theorem spU_symplectic : (spU F)ᵀ * spJ F * spU F = spJ F := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hneg : (-1 : F) = 1 := CharTwo.neg_eq 1
  simp only [spU, spJ, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hneg] <;> (try rw [← two_mul, h2]) <;> simp

theorem spU_mul_spU :
    spU F * spU F = Matrix.fromBlocks 1 !![1, 1; 1, 0] 0 1 := by
  simp only [spU, Matrix.fromBlocks_multiply]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp
  all_goals exact CharTwo.add_self_eq_zero 1

theorem spU_pow_four : spU F * spU F * (spU F * spU F) = 1 := by
  rw [spU_mul_spU, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]
  congr 1 <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp
  all_goals exact CharTwo.add_self_eq_zero 1

omit [CharP F 2] in
theorem spU_mulVec_eq {v : Fin 2 ⊕ Fin 2 → F} (hv : (spU F).mulVec v = v) :
    v (.inl 1) = 0 ∧ v (.inr 0) = 0 ∧ v (.inr 1) = 0 := by
  have e0 := congrFun hv (.inl 0)
  have e1 := congrFun hv (.inl 1)
  have e3 := congrFun hv (.inr 1)
  simp [spU, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Fin.sum_univ_two] at e0 e1 e3
  have h3 : v (.inr 1) = 0 := by linear_combination e1
  have h2 : v (.inr 0) = 0 := by linear_combination e3
  refine ⟨?_, h2, h3⟩
  linear_combination e0 - h3

end Matrices

section Diagonal

variable {F : Type} [Field F]

@[expose] def spDv (ω : F) : Fin 2 ⊕ Fin 2 → F := Sum.elim ![1, ω] ![1, ω ^ 2]

theorem spD_symplectic {ω : F} (hω : ω ^ 3 = 1) :
    (diagonal (spDv ω))ᵀ * spJ F * diagonal (spDv ω) = spJ F := by
  have h1 : ω * ω ^ 2 = 1 := by rw [← pow_succ', hω]
  have h2 : ω ^ 2 * ω = 1 := by rw [← pow_succ, hω]
  rw [diagonal_transpose]
  ext i j
  rw [mul_diagonal, diagonal_mul]
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [spDv, h1, h2]

theorem spD_pow_three {ω : F} (hω : ω ^ 3 = 1) : diagonal (spDv ω) ^ 3 = 1 := by
  rw [diagonal_pow, ← diagonal_one]
  congr 1
  ext i
  rcases i with i | i <;> fin_cases i <;> simp [spDv, ← pow_mul, hω]
  rw [show 6 = 3 * 2 by norm_num, pow_mul, hω, one_pow]

theorem spD_mulVec_eq {ω : F} {v : Fin 2 ⊕ Fin 2 → F} (h1 : v (.inl 1) = 0) (h2 : v (.inr 0) = 0)
    (h3 : v (.inr 1) = 0) : (diagonal (spDv ω)).mulVec v = v := by
  ext i
  rw [mulVec_diagonal]
  rcases i with i | i <;> fin_cases i <;> simp [spDv, h1, h2, h3]

end Diagonal

section Group

variable {F : Type} [Field F] [CharP F 2]

@[expose] def spUGL (F : Type) [Field F] [CharP F 2] : GL (Fin 2 ⊕ Fin 2) F where
  val := spU F
  inv := spU F * spU F * spU F
  val_inv := by
    rw [← spU_pow_four]
    simp only [Matrix.mul_assoc]
  inv_val := by
    rw [← spU_pow_four]
    simp only [Matrix.mul_assoc]

theorem spUGL_mem : spUGL F ∈ StatedSp 2 F :=
  Subgroup.subset_closure (spU_symplectic (F := F))

theorem spUGL_pow_four : spUGL F ^ 4 = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, show (4 : ℕ) = 2 + 2 from rfl, pow_add,
    sq]
  exact spU_pow_four

end Group

variable {F : Type} [Field F] [Fintype F]

theorem exists_cube_root_of_card_four (hF : Fintype.card F = 4) :
    ∃ ω : F, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  classical
  have hu : Nat.card Fˣ = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hF]
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 (by rw [hu])
  refine ⟨w, ?_, ?_⟩
  · have := pow_orderOf_eq_one w
    rw [hw] at this
    rw [← Units.val_pow_eq_pow_val, this, Units.val_one]
  · intro h1
    have : w = 1 := Units.ext h1
    rw [this, orderOf_one] at hw
    omega

theorem exists_orderOf_eq_three_fix_of_sylow_statedSp (hF : Fintype.card F = 4)
    (S : Subgroup ↥(StatedSp 2 F)) (hS : quasithinIsSylowTwo S) :
    ∃ g : ↥(StatedSp 2 F), orderOf g = 3 ∧ ∀ v : Fin 2 ⊕ Fin 2 → F,
      (∀ s ∈ S,
        ((s : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).mulVec v = v) →
        ((g : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F).mulVec v = v := by
  classical
  have : CharP F 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (f := 2) (by rw [hF]; norm_num)
  obtain ⟨ω, hω3, hω1⟩ := exists_cube_root_of_card_four hF
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω3
  let dGL : GL (Fin 2 ⊕ Fin 2) F :=
    { val := diagonal (spDv ω)
      inv := diagonal (spDv ω) ^ 2
      val_inv := by rw [← pow_succ', spD_pow_three hω3]
      inv_val := by rw [← pow_succ, spD_pow_three hω3] }
  have hdmem : dGL ∈ StatedSp 2 F := Subgroup.subset_closure (spD_symplectic hω3)
  let d : ↥(StatedSp 2 F) := ⟨dGL, hdmem⟩
  have hd3 : d ^ 3 = 1 := by
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one]
    exact spD_pow_three hω3
  have hd1 : d ≠ 1 := by
    intro h1
    have h2 := congrArg (fun x : ↥(StatedSp 2 F) =>
      ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) (.inl 1) (.inl 1)) h1
    simp [d, dGL, spDv] at h2
    exact hω1 h2
  have hdo : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  let u : ↥(StatedSp 2 F) := ⟨spUGL F, spUGL_mem⟩
  have hu4 : u ^ 4 = 1 := Subtype.ext (by simpa using spUGL_pow_four (F := F))
  have hT : IsPGroup 2 (Subgroup.zpowers u) := by
    rintro ⟨x, hx⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine ⟨2, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul,
      show ((2 ^ 2 : ℕ) : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast, hu4, _root_.one_zpow]
  obtain ⟨h, hh⟩ := exists_conj_mem_of_isPGroup hT hS
  refine ⟨h * d * h⁻¹, ?_, fun v hv => ?_⟩
  · rw [show h * d * h⁻¹ = MulAut.conj h d from rfl, MulEquiv.orderOf_eq, hdo]
  · let M : ↥(StatedSp 2 F) → Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F :=
      fun x => ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)
    have hM : ∀ x y : ↥(StatedSp 2 F), M (x * y) = M x * M y := fun _ _ => rfl
    have hMinv : ∀ x : ↥(StatedSp 2 F), M x⁻¹ * M x = 1 := by
      intro x
      rw [← hM, inv_mul_cancel]
      rfl
    have hMinv' : ∀ x : ↥(StatedSp 2 F), M x * M x⁻¹ = 1 := by
      intro x
      rw [← hM, mul_inv_cancel]
      rfl
    have huv : (spU F).mulVec ((M h⁻¹).mulVec v) = (M h⁻¹).mulVec v := by
      have h1 := hv _ (hh u (Subgroup.mem_zpowers u))
      change (M (h * u * h⁻¹)).mulVec v = v at h1
      rw [hM, hM] at h1
      have h2 := congrArg (M h⁻¹).mulVec h1
      have h3 : M h⁻¹ * (M h * M u * M h⁻¹) = M u * M h⁻¹ := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hMinv, Matrix.one_mul]
      rw [mulVec_mulVec, h3, ← mulVec_mulVec] at h2
      exact h2
    obtain ⟨e1, e2, e3⟩ := spU_mulVec_eq huv
    have hdv := spD_mulVec_eq (ω := ω) e1 e2 e3
    change (M (h * d * h⁻¹)).mulVec v = v
    rw [hM, hM, ← mulVec_mulVec, ← mulVec_mulVec]
    change (M h).mulVec ((diagonal (spDv ω)).mulVec ((M h⁻¹).mulVec v)) = v
    rw [hdv, mulVec_mulVec, hMinv', one_mulVec]

end CFSG.Quasithin.F420
