module

public import CFSG.RankThree.PartOne.SLB4B.RankFourSp
public import CFSG.RankThree.PartOne.SLB4B.CommPair

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.SLB4B

open Matrix Subgroup CFSG CFSG.RankThree.PartTwo.Census CFSG.RankThree.Classical
  CFSG.Assembly.LowTwoRank

section Levi

variable {K : Type} [Field K]

@[expose] def leviGL (A Ai : Matrix (Fin 2) (Fin 2) K) (h1 : A * Ai = 1) (h2 : Ai * A = 1) :
    GL (Fin 2 ⊕ Fin 2) K :=
  ⟨Matrix.fromBlocks A 0 0 Aiᵀ, Matrix.fromBlocks Ai 0 0 Aᵀ,
    by
      rw [Matrix.fromBlocks_multiply]
      simp [h1, ← Matrix.transpose_mul, ← Matrix.fromBlocks_one],
    by
      rw [Matrix.fromBlocks_multiply]
      simp [h2, ← Matrix.transpose_mul, ← Matrix.fromBlocks_one]⟩

theorem leviGL_mem_statedSp (A Ai : Matrix (Fin 2) (Fin 2) K) (h1 : A * Ai = 1)
    (h2 : Ai * A = 1) : leviGL A Ai h1 h2 ∈ StatedSp 2 K := by
  refine Subgroup.subset_closure ?_
  change (Matrix.fromBlocks A 0 0 Aiᵀ)ᵀ * Matrix.fromBlocks 0 1 (-1) 0 *
    Matrix.fromBlocks A 0 0 Aiᵀ = Matrix.fromBlocks 0 1 (-1) 0
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [h2, ← Matrix.transpose_mul]

@[expose] def leviSp (A Ai : Matrix (Fin 2) (Fin 2) K) (h1 : A * Ai = 1) (h2 : Ai * A = 1) :
    StatedSp 2 K :=
  ⟨leviGL A Ai h1 h2, leviGL_mem_statedSp A Ai h1 h2⟩

theorem leviGL_conj_siegelGL (A Ai : Matrix (Fin 2) (Fin 2) K) (h1 : A * Ai = 1)
    (h2 : Ai * A = 1) (B : Matrix (Fin 2) (Fin 2) K) :
    leviGL A Ai h1 h2 * siegelGL B * (leviGL A Ai h1 h2)⁻¹ = siegelGL (A * B * Aᵀ) := by
  refine Units.ext ?_
  have hinv : ((leviGL A Ai h1 h2)⁻¹ : GL (Fin 2 ⊕ Fin 2) K).val =
      Matrix.fromBlocks Ai 0 0 Aᵀ := rfl
  rw [Units.val_mul, Units.val_mul, hinv]
  change Matrix.fromBlocks A 0 0 Aiᵀ * siegelMat B * Matrix.fromBlocks Ai 0 0 Aᵀ =
    siegelMat (A * B * Aᵀ)
  rw [siegelMat, siegelMat, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp [h1, ← Matrix.transpose_mul, Matrix.mul_assoc]

theorem leviSp_conj_siegelSp [Finite K] (A Ai : Matrix (Fin 2) (Fin 2) K) (h1 : A * Ai = 1)
    (h2 : Ai * A = 1) (w w' : K × K × K) (hw : A * symMap w * Aᵀ = symMap w') :
    leviSp A Ai h1 h2 * siegelSp (Multiplicative.ofAdd w) * (leviSp A Ai h1 h2)⁻¹ =
      siegelSp (Multiplicative.ofAdd w') := by
  apply Subtype.ext
  change leviGL A Ai h1 h2 * siegelGL (symMap w) * (leviGL A Ai h1 h2)⁻¹ =
    siegelGL (symMap w')
  rw [leviGL_conj_siegelGL, hw]

end Levi

section Radical

variable {K : Type} [Field K] [Finite K]

@[expose] def eigCoord : K × K × K →+ K × K × K where
  toFun v := (v.1 + v.2.1 + v.2.2, v.1 - v.2.1 - v.2.2, -v.2.1 + v.2.2)
  map_zero' := by simp
  map_add' a b := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp <;> ring

theorem eigCoord_injective (h2 : (2 : K) ≠ 0) : Function.Injective (eigCoord (K := K)) := by
  intro a b h
  have h1 := congrArg Prod.fst h
  have h2' := congrArg (fun x => x.2.1) h
  have h3 := congrArg (fun x => x.2.2) h
  simp only [eigCoord, AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h1 h2' h3
  have s : a.2.1 + a.2.2 = b.2.1 + b.2.2 :=
    mul_left_cancel₀ h2 (by linear_combination h1 - h2')
  have e3 : a.2.2 = b.2.2 := mul_left_cancel₀ h2 (by linear_combination s + h3)
  have e2 : a.2.1 = b.2.1 := by linear_combination s - e3
  have e1 : a.1 = b.1 := mul_left_cancel₀ h2 (by linear_combination h1 + h2')
  exact Prod.ext e1 (Prod.ext e2 e3)

@[expose] noncomputable def siegelEig : Multiplicative (K × K × K) →* StatedSp 2 K :=
  siegelSp.comp (AddMonoidHom.toMultiplicative eigCoord)

theorem siegelEig_injective (h2 : (2 : K) ≠ 0) : Function.Injective (siegelEig (K := K)) := by
  intro a b hab
  have h1 : siegelSp (Multiplicative.ofAdd (eigCoord a.toAdd)) =
      siegelSp (Multiplicative.ofAdd (eigCoord b.toAdd)) := hab
  have h2' := siegelSp_injective h1
  have h3 : eigCoord a.toAdd = eigCoord b.toAdd := Multiplicative.ofAdd.injective h2'
  exact Multiplicative.toAdd.injective (eigCoord_injective h2 h3)

@[expose] def mI : Matrix (Fin 2) (Fin 2) K := !![0, 1; -1, 0]

@[expose] def mIinv : Matrix (Fin 2) (Fin 2) K := !![0, -1; 1, 0]

@[expose] def mJ : Matrix (Fin 2) (Fin 2) K := !![1, 1; 1, -1]

@[expose] def mJinv : Matrix (Fin 2) (Fin 2) K := !![-1, -1; -1, 1]

theorem mI_mul : (mI : Matrix (Fin 2) (Fin 2) K) * mIinv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mI, mIinv, Matrix.mul_apply, Fin.sum_univ_two]

theorem mIinv_mul : (mIinv : Matrix (Fin 2) (Fin 2) K) * mI = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mI, mIinv, Matrix.mul_apply, Fin.sum_univ_two]

theorem mJ_mul (h3 : (3 : K) = 0) : (mJ : Matrix (Fin 2) (Fin 2) K) * mJinv = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mJ, mJinv, Matrix.mul_apply, Fin.sum_univ_two] <;>
    linear_combination (-1 : K) * h3

theorem mJinv_mul (h3 : (3 : K) = 0) : (mJinv : Matrix (Fin 2) (Fin 2) K) * mJ = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mJ, mJinv, Matrix.mul_apply, Fin.sum_univ_two] <;>
    linear_combination (-1 : K) * h3

theorem symMap_eig1 : symMap (eigCoord ((1 : K), (0 : K), (0 : K))) = !![1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symMap, eigCoord]

theorem symMap_eig2 : symMap (eigCoord ((0 : K), (1 : K), (0 : K))) = !![1, -1; -1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symMap, eigCoord]

theorem symMap_eig3 : symMap (eigCoord ((0 : K), (0 : K), (1 : K))) = !![1, 1; 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [symMap, eigCoord]

theorem conjI_1 : (mI : Matrix (Fin 2) (Fin 2) K) * !![1, 0; 0, 1] * mIᵀ = !![1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mI, Matrix.mul_apply, Fin.sum_univ_two]

theorem conjI_2 :
    (mI : Matrix (Fin 2) (Fin 2) K) * !![1, -1; -1, -1] * mIᵀ = -!![1, -1; -1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mI, Matrix.mul_apply, Fin.sum_univ_two]

theorem conjI_3 :
    (mI : Matrix (Fin 2) (Fin 2) K) * !![1, 1; 1, -1] * mIᵀ = -!![1, 1; 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mI, Matrix.mul_apply, Fin.sum_univ_two]

theorem conjJ_1 (h3 : (3 : K) = 0) :
    (mJ : Matrix (Fin 2) (Fin 2) K) * !![1, 0; 0, 1] * mJᵀ = -!![1, 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mJ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    linear_combination h3

theorem conjJ_2 (h3 : (3 : K) = 0) :
    (mJ : Matrix (Fin 2) (Fin 2) K) * !![1, -1; -1, -1] * mJᵀ = !![1, -1; -1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mJ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination h3 | linear_combination (-1 : K) * h3

theorem conjJ_3 (h3 : (3 : K) = 0) :
    (mJ : Matrix (Fin 2) (Fin 2) K) * !![1, 1; 1, -1] * mJᵀ = -!![1, 1; 1, -1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mJ, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination h3 | linear_combination (-1 : K) * h3

theorem siegelEig_inv (v : K × K × K) :
    (siegelEig (Multiplicative.ofAdd v))⁻¹ = siegelEig (Multiplicative.ofAdd (-v)) := by
  rw [ofAdd_neg, map_inv]

theorem eigCoord_neg (v : K × K × K) : eigCoord (-v) = -eigCoord v := map_neg eigCoord v

theorem leviSp_conj_siegelEig (A Ai : Matrix (Fin 2) (Fin 2) K) (h1 : A * Ai = 1)
    (h2 : Ai * A = 1) (v v' : K × K × K) (hw : A * symMap (eigCoord v) * Aᵀ = symMap (eigCoord v')) :
    leviSp A Ai h1 h2 * siegelEig (Multiplicative.ofAdd v) * (leviSp A Ai h1 h2)⁻¹ =
      siegelEig (Multiplicative.ofAdd v') :=
  leviSp_conj_siegelSp A Ai h1 h2 _ _ hw

theorem leviSp_inv_siegelEig (A Ai : Matrix (Fin 2) (Fin 2) K) (h1 : A * Ai = 1)
    (h2 : Ai * A = 1) (v : K × K × K)
    (hw : A * symMap (eigCoord v) * Aᵀ = -symMap (eigCoord v)) :
    leviSp A Ai h1 h2 * siegelEig (Multiplicative.ofAdd v) * (leviSp A Ai h1 h2)⁻¹ =
      (siegelEig (Multiplicative.ofAdd v))⁻¹ := by
  rw [siegelEig_inv]
  exact leviSp_conj_siegelEig A Ai h1 h2 v (-v) (by rw [eigCoord_neg, map_neg]; exact hw)

end Radical

section Main

variable {K : Type} [Field K] [Finite K]

@[expose] def leviI : StatedSp 2 K := leviSp mI mIinv mI_mul mIinv_mul

@[expose] def leviJ (h3 : (3 : K) = 0) : StatedSp 2 K :=
  leviSp mJ mJinv (mJ_mul h3) (mJinv_mul h3)

theorem leviI_e1 : leviI * siegelEig (Multiplicative.ofAdd ((1 : K), (0 : K), (0 : K))) *
    leviI⁻¹ = siegelEig (Multiplicative.ofAdd ((1 : K), (0 : K), (0 : K))) :=
  leviSp_conj_siegelEig _ _ _ _ _ _ (by rw [symMap_eig1]; exact conjI_1)

theorem leviI_e2 : leviI * siegelEig (Multiplicative.ofAdd ((0 : K), (1 : K), (0 : K))) *
    leviI⁻¹ = (siegelEig (Multiplicative.ofAdd ((0 : K), (1 : K), (0 : K))))⁻¹ :=
  leviSp_inv_siegelEig _ _ _ _ _ (by rw [symMap_eig2]; exact conjI_2)

theorem leviI_e3 : leviI * siegelEig (Multiplicative.ofAdd ((0 : K), (0 : K), (1 : K))) *
    leviI⁻¹ = (siegelEig (Multiplicative.ofAdd ((0 : K), (0 : K), (1 : K))))⁻¹ :=
  leviSp_inv_siegelEig _ _ _ _ _ (by rw [symMap_eig3]; exact conjI_3)

theorem leviJ_e1 (h3 : (3 : K) = 0) :
    leviJ h3 * siegelEig (Multiplicative.ofAdd ((1 : K), (0 : K), (0 : K))) * (leviJ h3)⁻¹ =
      (siegelEig (Multiplicative.ofAdd ((1 : K), (0 : K), (0 : K))))⁻¹ :=
  leviSp_inv_siegelEig _ _ _ _ _ (by rw [symMap_eig1]; exact conjJ_1 h3)

theorem leviJ_e2 (h3 : (3 : K) = 0) :
    leviJ h3 * siegelEig (Multiplicative.ofAdd ((0 : K), (1 : K), (0 : K))) * (leviJ h3)⁻¹ =
      siegelEig (Multiplicative.ofAdd ((0 : K), (1 : K), (0 : K))) :=
  leviSp_conj_siegelEig _ _ _ _ _ _ (by rw [symMap_eig2]; exact conjJ_2 h3)

theorem leviJ_e3 (h3 : (3 : K) = 0) :
    leviJ h3 * siegelEig (Multiplicative.ofAdd ((0 : K), (0 : K), (1 : K))) * (leviJ h3)⁻¹ =
      (siegelEig (Multiplicative.ofAdd ((0 : K), (0 : K), (1 : K))))⁻¹ :=
  leviSp_inv_siegelEig _ _ _ _ _ (by rw [symMap_eig3]; exact conjJ_3 h3)

theorem exists_natCast_eq_of_card_three [CharP K 3] (hK : Nat.card K = 3) :
    ∀ a : K, ∃ n : ℕ, (n : K) = a := by
  have hinj : Function.Injective (ZMod.castHom (dvd_refl 3) K) :=
    (ZMod.castHom (dvd_refl 3) K).injective
  have hbij := hinj.bijective_of_nat_card_le (by rw [hK, Nat.card_zmod])
  intro a
  obtain ⟨z, rfl⟩ := hbij.2 a
  exact ⟨z.val, by simp⟩

theorem closure_basis_eq_top (hnat : ∀ a : K, ∃ n : ℕ, (n : K) = a) :
    AddSubgroup.closure ({((1 : K), (0 : K), (0 : K)), ((0 : K), (1 : K), (0 : K)),
      ((0 : K), (0 : K), (1 : K))} : Set (K × K × K)) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  obtain ⟨n₁, h₁⟩ := hnat v.1
  obtain ⟨n₂, h₂⟩ := hnat v.2.1
  obtain ⟨n₃, h₃⟩ := hnat v.2.2
  have hv : v = n₁ • ((1 : K), (0 : K), (0 : K)) + n₂ • ((0 : K), (1 : K), (0 : K)) +
      n₃ • ((0 : K), (0 : K), (1 : K)) := by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [← h₁, ← h₂, ← h₃]
  rw [hv]
  refine add_mem (add_mem ?_ ?_) ?_ <;>
    exact nsmul_mem (AddSubgroup.subset_closure (by simp)) _

theorem siegelEig_liftPair_eq_one [CharP K 3] (hK : Nat.card K = 3) {Y : Type} [Group Y]
    {φ : Y →* StatedSp 2 K} (hφ : Function.Surjective φ) (hZ : φ.ker ≤ Subgroup.center Y)
    (v w : K × K × K) : liftPair hφ siegelEig v w = 1 := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have hpV : ∀ v : K × K × K, 3 • v = 0 := fun v => by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [← Nat.cast_smul_eq_nsmul K, h3]
  have hS := closure_basis_eq_top (exists_natCast_eq_of_card_three hK)
  refine liftPair_eq_one_of_gen hφ siegelEig hZ _ hS ?_ v w
  intro a ha b hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact liftPair_self hφ siegelEig _
  · exact liftPair_eq_one_of_opposite_signs hφ siegelEig hZ hp hp2 (hpV _) (hpV _) _
      leviI_e1 leviI_e2
  · exact liftPair_eq_one_of_opposite_signs hφ siegelEig hZ hp hp2 (hpV _) (hpV _) _
      leviI_e1 leviI_e3
  · exact liftPair_eq_one_of_opposite_signs' hφ siegelEig hZ hp hp2 (hpV _) (hpV _) _
      leviI_e2 leviI_e1
  · exact liftPair_self hφ siegelEig _
  · exact liftPair_eq_one_of_opposite_signs hφ siegelEig hZ hp hp2 (hpV _) (hpV _) _
      (leviJ_e2 h3) (leviJ_e3 h3)
  · exact liftPair_eq_one_of_opposite_signs' hφ siegelEig hZ hp hp2 (hpV _) (hpV _) _
      leviI_e3 leviI_e1
  · exact liftPair_eq_one_of_opposite_signs' hφ siegelEig hZ hp hp2 (hpV _) (hpV _) _
      (leviJ_e3 h3) (leviJ_e2 h3)
  · exact liftPair_self hφ siegelEig _

theorem siegelEig_preimage_comm [CharP K 3] (hK : Nat.card K = 3) {Y : Type} [Group Y]
    {φ : Y →* StatedSp 2 K} (hφ : Function.Surjective φ) (hZ : φ.ker ≤ Subgroup.center Y) :
    ∀ x ∈ (siegelEig (K := K)).range.comap φ, ∀ y ∈ (siegelEig (K := K)).range.comap φ,
      x * y = y * x := fun _ hx _ hy =>
  mul_comm_of_liftPair_eq_one hφ siegelEig hZ (siegelEig_liftPair_eq_one hK hφ hZ) hx hy

theorem siegelEig_exists_lift [CharP K 3] (hK : Nat.card K = 3) {Y : Type} [Group Y]
    {φ : Y →* StatedSp 2 K} (hφ : Function.Surjective φ) (hZ : φ.ker ≤ Subgroup.center Y) :
    ∀ e ∈ (siegelEig (K := K)).range, ∃ x : Y, φ x = e ∧ x ^ 3 = 1 := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have hpV : ∀ v : K × K × K, 3 • v = 0 := fun v => by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [← Nat.cast_smul_eq_nsmul K, h3]
  have hS := closure_basis_eq_top (exists_natCast_eq_of_card_three hK)
  refine exists_lift_pow_eq_one_of_gen (φ := φ) siegelEig _ hS
    (siegelEig_preimage_comm hK hφ hZ) ?_
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl
  · exact exists_lift_pow_eq_one_of_inverted hφ siegelEig hZ hp hp2 (hpV _) _ (leviJ_e1 h3)
  · exact exists_lift_pow_eq_one_of_inverted hφ siegelEig hZ hp hp2 (hpV _) _ leviI_e2
  · exact exists_lift_pow_eq_one_of_inverted hφ siegelEig hZ hp hp2 (hpV _) _ leviI_e3

theorem exists_sp4_three_radical {p : ℕ} [Fact p.Prime] [CharP K p] (hp3 : p = 3)
    (hK : Nat.card K = p) :
    ∃ E₀ : Subgroup (StatedSp 2 K), IsElementaryAbelian p E₀ ∧ Nat.card E₀ = p ^ 3 ∧
      (∀ (Y : Type) [Group Y] (φ : Y →* StatedSp 2 K), Function.Surjective φ →
        φ.ker ≤ Subgroup.center Y → ∀ x ∈ E₀.comap φ, ∀ y ∈ E₀.comap φ, x * y = y * x) ∧
      (∀ (Y : Type) [Group Y] (φ : Y →* StatedSp 2 K), Function.Surjective φ →
        φ.ker ≤ Subgroup.center Y → ∀ e ∈ E₀, ∃ x : Y, φ x = e ∧ x ^ p = 1) := by
  subst hp3
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have h2 : (2 : K) ≠ 0 := fun h0 => one_ne_zero (by linear_combination h3 - h0 : (1 : K) = 0)
  have hpV : ∀ v : K × K × K, 3 • v = 0 := fun v => by
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [← Nat.cast_smul_eq_nsmul K, h3]
  have hinj := siegelEig_injective (K := K) h2
  have hEA : IsElementaryAbelian 3 (siegelEig (K := K)).range := by
    have hpow : ∀ a : Multiplicative (K × K × K), a ^ 3 = 1 := fun a =>
      Multiplicative.toAdd.injective (by rw [toAdd_pow, toAdd_one]; exact hpV _)
    exact CFSG.RankThree.PartOne.SRC.isElementaryAbelian_range
      (A := Multiplicative (K × K × K)) (siegelEig (K := K)) hpow
  have hcard : Nat.card (siegelEig (K := K)).range = 3 ^ 3 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
      Nat.card_congr Multiplicative.toAdd, Nat.card_prod, Nat.card_prod, hK]
    ring
  exact ⟨(siegelEig (K := K)).range, hEA, hcard,
    fun Y _ φ hφ hZ => siegelEig_preimage_comm hK hφ hZ,
    fun Y _ φ hφ hZ => siegelEig_exists_lift hK hφ hZ⟩

end Main

end CFSG.RankThree.PartOne.SLB4B
