module

public import CFSG.RankThree.PartOne.S13K.ReflAlg
public import CFSG.RankThree.PartOne.S13K.Sp6Refl
public import CFSG.RankThree.PartOne.S13K.Sp6Reps

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartOne.S13K

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.RankThree.PartOne.KFQ ReflAlg Matrix

section Coord

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} [Fact p.Prime]

@[expose] noncomputable def expv (ζ : (Qext K)ˣ) (a : Fin 3 → ZMod p) : Fin 3 → (Qext K)ˣ :=
  fun i => ζ ^ (a i).val

theorem expv_pow {ζ : (Qext K)ˣ} (hζ : ζ ^ p = 1) (a : Fin 3 → ZMod p) (i : Fin 3) :
    expv ζ a i ^ p = 1 := by
  simp only [expv]
  rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]

theorem expv_add {ζ : (Qext K)ˣ} (hζ : ζ ^ p = 1) (a b : Fin 3 → ZMod p) :
    expv ζ (a + b) = expv ζ a * expv ζ b := by
  funext i
  simp only [expv, Pi.add_apply, Pi.mul_apply]
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hζ, pow_add]

theorem expv_neg {ζ : (Qext K)ˣ} (hζ : ζ ^ p = 1) (a : Fin 3 → ZMod p) :
    expv ζ (-a) = (expv ζ a)⁻¹ := by
  funext i
  simp only [expv, Pi.neg_apply, Pi.inv_apply]
  by_cases h : a i = 0
  · have h0 : -a i = 0 := by rw [h]; exact neg_zero
    rw [h0, h, ZMod.val_zero]
    simp
  · have hneg : (-a i).val = p - (a i).val := by
      have := ZMod.neg_val (a i)
      simp only [h, ite_false] at this
      exact this
    rw [hneg]
    have hv : (a i).val ≤ p := (ZMod.val_lt (a i)).le
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_add, Nat.sub_add_cancel hv, hζ]

theorem expv_injective {ζ : (Qext K)ˣ} (hζ : IsPrimitiveRoot ζ p) :
    Function.Injective (expv (p := p) ζ) := by
  intro a b h
  funext i
  have h1 : ζ ^ (a i).val = ζ ^ (b i).val := congrFun h i
  exact ZMod.val_injective p (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h1)

theorem expv_surj {ζ : (Qext K)ˣ} (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    {x : Fin 3 → (Qext K)ˣ} (hx : ∀ i, x i ^ p = 1) : ∃ a : Fin 3 → ZMod p, expv ζ a = x := by
  choose k hk using fun i => exists_pow_eq hp hζ (hx i)
  refine ⟨fun i => (k i : ZMod p), ?_⟩
  funext i
  simp only [expv, ZMod.val_natCast]
  rw [← pow_eq_pow_mod _ hζ.pow_eq_one]
  exact hk i

@[expose] def sgnVec (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) (a : Fin 3 → ZMod p) :
    Fin 3 → ZMod p :=
  fun j => if ε (π.symm j) then -a (π.symm j) else a (π.symm j)

theorem sact_expv {ζ : (Qext K)ˣ} (hζ : ζ ^ p = 1) (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool)
    (a : Fin 3 → ZMod p) : sact π ε (expv ζ a) = expv ζ (sgnVec π ε a) := by
  funext j
  by_cases h : ε (π.symm j) = true
  · have h1 : sgnVec π ε a j = -a (π.symm j) := by simp [sgnVec, h]
    have h2 := congrFun (expv_neg hζ a) (π.symm j)
    simp only [expv, Pi.neg_apply, Pi.inv_apply] at h2
    simp only [sact_apply, h, ite_true]
    show (ζ ^ (a (π.symm j)).val)⁻¹ = ζ ^ (sgnVec π ε a j).val
    rw [h1]
    exact h2.symm
  · have h1 : sgnVec π ε a j = a (π.symm j) := by simp [sgnVec, h]
    simp only [sact_apply, h]
    show ζ ^ (a (π.symm j)).val = ζ ^ (sgnVec π ε a j).val
    rw [h1]

@[expose] def sgnMat (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) :
    Matrix (Fin 3) (Fin 3) (ZMod p) :=
  fun j i => if π.symm j = i then (if ε i then -1 else 1) else 0

theorem sgnMat_mulVec (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) (a : Fin 3 → ZMod p) :
    sgnMat π ε *ᵥ a = sgnVec π ε a := by
  funext j
  simp only [Matrix.mulVec, dotProduct, sgnMat, sgnVec]
  rw [Finset.sum_eq_single (π.symm j)]
  · by_cases h : ε (π.symm j) = true
    · simp only [h, ite_true]; exact neg_one_mul _
    · simp [h]
  · intro i _ hi
    simp [Ne.symm hi]
  · intro h
    exact absurd (Finset.mem_univ _) h

@[expose] def shapeP : Fin 9 → Equiv.Perm (Fin 3) :=
  ![1, 1, 1, Equiv.swap 0 1, Equiv.swap 0 1, Equiv.swap 1 2, Equiv.swap 1 2, Equiv.swap 0 2,
    Equiv.swap 0 2]

@[expose] def shapeE : Fin 9 → Fin 3 → Bool :=
  ![![true, false, false], ![false, true, false], ![false, false, true], ![false, false, false],
    ![true, true, false], ![false, false, false], ![false, true, true], ![false, false, false],
    ![true, false, true]]

@[expose] def rootV : Fin 9 → Fin 3 → ZMod p :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, -1, 0], ![1, 1, 0], ![0, 1, -1], ![0, 1, 1],
    ![1, 0, -1], ![1, 0, 1]]

theorem shape_reflShape (k : Fin 9) : ReflShape (shapeP k) (shapeE k) := by
  have : ∀ k : Fin 9, (shapeP k = 1 ∧ ∃ i, shapeE k i = true ∧ ∀ j, j ≠ i → shapeE k j = false) ∨
      (∃ a b c : Fin 3, a ≠ b ∧ c ≠ a ∧ c ≠ b ∧ shapeP k = Equiv.swap a b ∧
        shapeE k a = shapeE k b ∧ shapeE k c = false) := by
    unfold shapeP shapeE
    decide +kernel
  exact this k

theorem reflShape_cases {π : Equiv.Perm (Fin 3)} {ε : Fin 3 → Bool} (h : ReflShape π ε) :
    ∃ k : Fin 9, π = shapeP k ∧ ε = shapeE k := by
  have : ∀ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool),
      ((π = 1 ∧ ∃ i, ε i = true ∧ ∀ j, j ≠ i → ε j = false) ∨
        (∃ a b c : Fin 3, a ≠ b ∧ c ≠ a ∧ c ≠ b ∧ π = Equiv.swap a b ∧ ε a = ε b ∧ ε c = false)) →
      ∃ k : Fin 9, π = shapeP k ∧ ε = shapeE k := by
    unfold shapeP shapeE
    decide +kernel
  exact this π ε h

theorem isRoot_rootV (k : Fin 9) : IsRoot (rootV (p := p) k) := by
  fin_cases k
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))

theorem exists_rootV_of_isRoot {α : Fin 3 → ZMod p} (hα : IsRoot α) : ∃ k, α = rootV k := by
  rcases hα with h | h | h | h | h | h | h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩
  · exact ⟨4, h⟩
  · exact ⟨3, h⟩
  · exact ⟨6, h⟩
  · exact ⟨5, h⟩
  · exact ⟨8, h⟩
  · exact ⟨7, h⟩

theorem sgnMat_shape (hp5 : 5 ≤ p) (k : Fin 9) :
    sgnMat (shapeP k) (shapeE k) = reflMat (rootV (p := p) k) := by
  have h2 := two_ne_zero_of_five_le (p := p) hp5
  have h11 : (1 : ZMod p) + 1 = 2 := one_add_one_eq_two
  ext j i
  fin_cases k <;> fin_cases j <;> fin_cases i <;>
    simp [sgnMat, reflMat_apply, shapeP, shapeE, rootV, dotProduct, Fin.sum_univ_three,
      Equiv.swap_apply_def, h11, h2] <;> ring

theorem exists_root_of_shape (hp5 : 5 ≤ p) {π : Equiv.Perm (Fin 3)} {ε : Fin 3 → Bool}
    (h : ReflShape π ε) : ∃ β : Fin 3 → ZMod p, IsRoot β ∧ sgnMat π ε = reflMat β := by
  obtain ⟨k, rfl, rfl⟩ := reflShape_cases h
  exact ⟨rootV k, isRoot_rootV k, sgnMat_shape hp5 k⟩

theorem exists_shape_of_root (hp5 : 5 ≤ p) {α : Fin 3 → ZMod p} (hα : IsRoot α) :
    ∃ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool), ReflShape π ε ∧ sgnMat π ε = reflMat α := by
  obtain ⟨k, rfl⟩ := exists_rootV_of_isRoot hα
  exact ⟨shapeP k, shapeE k, shape_reflShape k, sgnMat_shape hp5 k⟩

theorem exists_line_of_card_ker (N : (Fin 3 → ZMod p) →+ (Fin 3 → ZMod p))
    (hker : Nat.card N.ker = p ^ 2) :
    ∃ u : Fin 3 → ZMod p, u ≠ 0 ∧ (∃ a, N a ≠ 0) ∧ ∀ a, ∃ k : ZMod p, N a = k • u := by
  have hp : p.Prime := Fact.out
  have hcard : Nat.card (Fin 3 → ZMod p) = p ^ 3 := by
    rw [Nat.card_eq_fintype_card]
    simp [ZMod.card]
  have h1 : Nat.card (Fin 3 → ZMod p) = Nat.card ((Fin 3 → ZMod p) ⧸ N.ker) * Nat.card N.ker :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.ker
  have h2 : Nat.card ((Fin 3 → ZMod p) ⧸ N.ker) = Nat.card N.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange N).toEquiv
  have hr : Nat.card N.range = p := by
    have h3 : p * p ^ 2 = Nat.card N.range * p ^ 2 := by
      calc p * p ^ 2 = p ^ 3 := by ring
        _ = Nat.card N.range * p ^ 2 := by rw [← hcard, h1, h2, hker]
    exact (Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos 2) h3).symm
  have hcyc : IsAddCyclic N.range := isAddCyclic_of_prime_card hr
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hne : ∃ a, N a ≠ 0 := by
    by_contra hall
    push Not at hall
    have : Nat.card N.range = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun x y => ?_⟩, ⟨0⟩⟩
      obtain ⟨a, ha⟩ := x.2
      obtain ⟨b, hb⟩ := y.2
      exact Subtype.ext (by rw [← ha, ← hb, hall a, hall b])
    rw [hr] at this
    exact hp.one_lt.ne' this
  obtain ⟨a₀, ha₀⟩ := hne
  have hg0 : (g : Fin 3 → ZMod p) ≠ 0 := by
    intro h0
    have := hg ⟨N a₀, ⟨a₀, rfl⟩⟩
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 this
    apply ha₀
    have := congrArg Subtype.val hn
    simp only [AddSubgroup.coe_zsmul, h0, smul_zero] at this
    exact this.symm
  refine ⟨g, hg0, ⟨a₀, ha₀⟩, fun a => ?_⟩
  have := hg ⟨N a, ⟨a, rfl⟩⟩
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 this
  refine ⟨(n : ZMod p), ?_⟩
  have h5 := congrArg Subtype.val hn
  simp only [AddSubgroup.coe_zsmul] at h5
  rw [← h5, Int.cast_smul_eq_zsmul]

theorem exists_phi_of_line {M : Matrix (Fin 3) (Fin 3) (ZMod p)} {u : Fin 3 → ZMod p}
    (h : ∀ a, ∃ k : ZMod p, M *ᵥ a - a = k • u) :
    ∃ φ : Fin 3 → ZMod p, M = 1 + Matrix.vecMulVec u φ := by
  choose φ hφ using fun i : Fin 3 => h (Pi.single i 1)
  refine ⟨φ, ?_⟩
  ext j i
  have := congrFun (hφ i) j
  simp only [Matrix.mulVec_single_one, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.col_apply] at this
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.vecMulVec_apply]
  have h2 : M j i = (Pi.single i (1 : ZMod p) : Fin 3 → ZMod p) j + φ i * u j := by
    linear_combination this
  rw [h2, Pi.single_apply]
  by_cases hij : j = i <;> simp [hij, mul_comm]

end Coord

end CFSG.RankThree.PartOne.S13K
