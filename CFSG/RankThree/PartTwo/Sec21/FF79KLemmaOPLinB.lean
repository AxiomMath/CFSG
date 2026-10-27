module

public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

namespace LemmaOPLinB

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {k : Type} [Field k]

@[expose] def dg (p q : Fin n) (x y : k) : Fin n → k := fun i =>
  (if i = p then x else 1) * (if i = q then y else 1)

theorem prod_dg (p q : Fin n) (x y : k) : ∏ i, dg p q x y i = x * y := by
  unfold dg
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq', Finset.mem_univ, if_true]

@[expose] def dgSL (p q : Fin n) (x y : k) (h : x * y = 1) : SpecialLinearGroup (Fin n) k :=
  ⟨diagonal (dg p q x y), by rw [det_diagonal, prod_dg, h]⟩

@[expose] def tv (i j : Fin n) (h : i ≠ j) (c : k) : SpecialLinearGroup (Fin n) k :=
  ⟨transvection i j c, det_transvection_of_ne i j h c⟩

theorem tv_mul_tv (i j : Fin n) (h : i ≠ j) (c d : k) :
    tv i j h c * tv i j h d = tv i j h (c + d) :=
  Subtype.ext (transvection_mul_transvection_same i j h c d)

theorem tv_comm_dgSL (i j : Fin n) (h : i ≠ j) (c : k) (p q : Fin n) (x y : k) (hxy : x * y = 1)
    (hij : dg p q x y i = dg p q x y j) :
    tv i j h c * dgSL p q x y hxy = dgSL p q x y hxy * tv i j h c := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  show transvection i j c * diagonal (dg p q x y) = diagonal (dg p q x y) * transvection i j c
  rw [transvection, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
  congr 1
  ext a b
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hab : a = i ∧ b = j
  · obtain ⟨rfl, rfl⟩ := hab
    simp [hij, mul_comm]
  · have hab' : ¬(i = a ∧ j = b) := fun h => hab ⟨h.1.symm, h.2.symm⟩
    simp [Matrix.single_apply, hab']

theorem dgSL_comm (p q p' q' : Fin n) (x y x' y' : k) (h : x * y = 1) (h' : x' * y' = 1) :
    dgSL p q x y h * dgSL p' q' x' y' h' = dgSL p' q' x' y' h' * dgSL p q x y h := by
  refine Subtype.ext ?_
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  show diagonal (dg p q x y) * diagonal (dg p' q' x' y') =
    diagonal (dg p' q' x' y') * diagonal (dg p q x y)
  rw [diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem coe_dgSL_pow (p q : Fin n) (x y : k) (h : x * y = 1) (m : ℕ) :
    ((dgSL p q x y h ^ m : SpecialLinearGroup (Fin n) k) : Matrix (Fin n) (Fin n) k) =
      diagonal (dg p q x y ^ m) := by
  rw [Matrix.SpecialLinearGroup.coe_pow]
  show diagonal (dg p q x y) ^ m = _
  rw [diagonal_pow]

theorem dgSL_pow_three (p q : Fin n) (x y : k) (h : x * y = 1) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) :
    dgSL p q x y h ^ 3 = 1 := by
  refine Subtype.ext ?_
  rw [coe_dgSL_pow]
  show _ = (1 : Matrix (Fin n) (Fin n) k)
  rw [← diagonal_one]
  congr 1
  funext i
  simp only [Pi.pow_apply, dg, mul_pow, Pi.one_apply]
  split_ifs <;> simp [hx, hy]

theorem exists_cube_root (hk : Nat.card k = 4) [Finite k] : ∃ W : k, W ^ 3 = 1 ∧ W ≠ 1 := by
  haveI := Fintype.ofFinite k
  classical
  have hc : Fintype.card k = 4 := by rw [← Nat.card_eq_fintype_card, hk]
  by_contra hno
  push Not at hno
  have hsub : (Finset.univ : Finset k) ⊆ {0, 1} := by
    intro a _
    by_cases ha : a = 0
    · simp [ha]
    · have := FiniteField.pow_card_sub_one_eq_one a ha
      rw [hc] at this
      have := hno a this
      simp [this]
  have := Finset.card_le_card hsub
  rw [Finset.card_univ, hc] at this
  have h2 := Finset.card_le_two (a := (0 : k)) (b := 1)
  omega

theorem not_mem_scalars_diag (A : SpecialLinearGroup (Fin n) k) (i j : Fin n)
    (h : (A : Matrix (Fin n) (Fin n) k) i i ≠ (A : Matrix (Fin n) (Fin n) k) j j) :
    A ∉ scalars n k := by
  rintro ⟨c, -, hA⟩
  apply h
  rw [hA]
  have hij : i ≠ j := by
    rintro rfl
    exact h rfl
  simp [scalar_apply]

theorem not_mem_scalars_offdiag (A : SpecialLinearGroup (Fin n) k) (i j : Fin n) (hij : i ≠ j)
    (h : (A : Matrix (Fin n) (Fin n) k) i j ≠ 0) : A ∉ scalars n k := by
  rintro ⟨c, -, hA⟩
  apply h
  rw [hA]
  simp [scalar_apply, diagonal_apply, hij]

theorem coe_dgSL_apply (p q : Fin n) (x y : k) (h : x * y = 1) (i : Fin n) :
    (dgSL p q x y h : Matrix (Fin n) (Fin n) k) i i = dg p q x y i := by
  simp [dgSL]

theorem exists_proj (hn : 5 ≤ n) [Finite k] [CharP k 2] (hk : Nat.card k = 4) :
    ∃ t u v : projectiveSL n k, orderOf t = 2 ∧ t * u = u * t ∧ t * v = v * t ∧ u * v = v * u ∧
      orderOf u = 3 ∧ orderOf v = 3 ∧ v ∉ Subgroup.zpowers u := by
  obtain ⟨W, hW3, hW1⟩ := exists_cube_root hk
  have hW0 : W * W ^ 2 = 1 := by rw [← pow_succ']; exact hW3
  have hW2 : (W ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hW3, one_pow]
  let i0 : Fin n := ⟨0, by omega⟩
  let i1 : Fin n := ⟨1, by omega⟩
  let i2 : Fin n := ⟨2, by omega⟩
  let i3 : Fin n := ⟨3, by omega⟩
  let i4 : Fin n := ⟨4, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h03 : i0 ≠ i3 := by simp [i0, i3, Fin.ext_iff]
  have h23 : i2 ≠ i3 := by simp [i2, i3, Fin.ext_iff]
  have h24 : i2 ≠ i4 := by simp [i2, i4, Fin.ext_iff]
  have h34 : i3 ≠ i4 := by simp [i3, i4, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  have h13 : i1 ≠ i3 := by simp [i1, i3, Fin.ext_iff]
  have h14 : i1 ≠ i4 := by simp [i1, i4, Fin.ext_iff]
  have h04 : i0 ≠ i4 := by simp [i0, i4, Fin.ext_iff]
  let T := tv i0 i1 h01 (1 : k)
  let U := dgSL i2 i3 W (W ^ 2) hW0
  let V := dgSL i3 i4 W (W ^ 2) hW0
  have hTU : T * U = U * T := tv_comm_dgSL _ _ h01 _ _ _ _ _ hW0 (by
    simp [dg, h02, h12, h03, h13])
  have hTV : T * V = V * T := tv_comm_dgSL _ _ h01 _ _ _ _ _ hW0 (by
    simp [dg, h03, h13, h04, h14])
  have hUV : U * V = V * U := dgSL_comm _ _ _ _ _ _ _ _ hW0 hW0
  have hT2 : T ^ 2 = 1 := by
    rw [pow_two, tv_mul_tv, CharTwo.add_self_eq_zero]
    exact Subtype.ext (transvection_zero i0 i1)
  have hU3 : U ^ 3 = 1 := dgSL_pow_three _ _ _ _ hW0 hW3 hW2
  have hV3 : V ^ 3 = 1 := dgSL_pow_three _ _ _ _ hW0 hW3 hW2
  have hTn : T ∉ scalars n k := not_mem_scalars_offdiag T i0 i1 h01 (by
    show (1 + Matrix.single i0 i1 (1 : k)) i0 i1 ≠ 0
    simp [Matrix.add_apply, Matrix.one_apply_ne h01])
  have hUn : U ∉ scalars n k := not_mem_scalars_diag U i0 i2 (by
    rw [coe_dgSL_apply, coe_dgSL_apply]
    simp [dg, h02, h03, h23, hW1.symm])
  have hVn : V ∉ scalars n k := not_mem_scalars_diag V i0 i3 (by
    rw [coe_dgSL_apply, coe_dgSL_apply]
    simp [dg, h03, h04, h34, hW1.symm])
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨proj n k T, proj n k U, proj n k V, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine orderOf_eq_prime (by rw [← map_pow, hT2, map_one]) ?_
    rwa [Ne, proj_eq_one_iff]
  · rw [← map_mul, ← map_mul, hTU]
  · rw [← map_mul, ← map_mul, hTV]
  · rw [← map_mul, ← map_mul, hUV]
  · refine orderOf_eq_prime (by rw [← map_pow, hU3, map_one]) ?_
    rwa [Ne, proj_eq_one_iff]
  · refine orderOf_eq_prime (by rw [← map_pow, hV3, map_one]) ?_
    rwa [Ne, proj_eq_one_iff]
  · intro hmem
    obtain ⟨m, hm⟩ := mem_powers_iff_mem_zpowers.2 hmem
    simp only [← map_pow] at hm
    rw [proj_eq_proj_iff] at hm
    obtain ⟨c, hc, hmat⟩ := hm
    have e : (U ^ m)⁻¹ * V = scalarElement c hc := Subtype.ext hmat
    have hV : V = U ^ m * scalarElement c hc := by rw [← e]; simp
    have key : ∀ i, dg i3 i4 W (W ^ 2) i = (dg i2 i3 W (W ^ 2) i) ^ m * (c : k) := by
      intro i
      have := congrArg (fun A : SpecialLinearGroup (Fin n) k =>
        (A : Matrix (Fin n) (Fin n) k) i i) hV
      simp only [V, U, coe_dgSL_apply, Matrix.SpecialLinearGroup.coe_mul, coe_dgSL_pow,
        coe_scalarElement, scalar_apply, diagonal_mul_diagonal, diagonal_apply_eq,
        Pi.pow_apply] at this
      exact this
    have k0 := key i0
    have k2 := key i2
    have k3 := key i3
    simp [dg, h01, h02, h03, h04, h23, h24, h34, h02.symm, h03.symm, h04.symm, h23.symm,
      h24.symm, h34.symm] at k0 k2 k3
    rw [← k0, mul_one] at k2 k3
    apply hW1
    rw [k3, ← pow_mul, mul_comm, pow_mul, ← k2, one_pow]

end LemmaOPLinB

open CFSG.LocalAnalysis.ComponentInitial

theorem exists_three_rank_two_linear {S : Type} [Group S] {n : ℕ} (hn : 5 ≤ n)
    {k : Type} [Field k] [Finite k] [CharP k 2] (hk : Nat.card k = 4)
    (e : S ≃* LinearFlag.projectiveSL n k) :
    ∃ t u v : S, orderOf t = 2 ∧ t * u = u * t ∧ t * v = v * t ∧ u * v = v * u ∧
      orderOf u = 3 ∧ orderOf v = 3 ∧ v ∉ Subgroup.zpowers u := by
  obtain ⟨t, u, v, ht, htu, htv, huv, hu, hv, hnm⟩ := LemmaOPLinB.exists_proj hn hk
  have hord : ∀ x : LinearFlag.projectiveSL n k, orderOf (e.symm x) = orderOf x := fun x =>
    orderOf_injective e.symm.toMonoidHom e.symm.injective x
  refine ⟨e.symm t, e.symm u, e.symm v, by rw [hord, ht], ?_, ?_, ?_, by rw [hord, hu],
    by rw [hord, hv], ?_⟩
  · rw [← map_mul, ← map_mul, htu]
  · rw [← map_mul, ← map_mul, htv]
  · rw [← map_mul, ← map_mul, huv]
  · intro hmem
    apply hnm
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hmem
    refine Subgroup.mem_zpowers_iff.2 ⟨m, ?_⟩
    have := congrArg e hm
    simpa [← map_zpow] using this

end CFSG.RankThree.PartTwo.Sec21.FF79
