module

public import CFSG.RankThree.PartOne.KF.U4Calc
public import CFSG.RankThree.PartOne.KF.U4Blk
public import CFSG.RankThree.PartOne.KF.UnitaryTorus

public section

namespace CFSG.RankThree.PartOne.KFU

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCUnitaryCoord

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem blk_comm_diagU {i j : Fin n} (hij : i ≠ j) {v : Fin n → Kˣ} (hv : v i = v j)
    {g : GL (Fin n) K} (hg : g ∈ blk h hij) : g * diagU v = diagU v * g := by
  obtain ⟨X, -, hX⟩ := (mem_blk_iff hij).mp hg
  apply Units.ext
  simp only [Units.val_mul, diagU_val, hX]
  exact (diagonal_mul_coordEmbed (fun k => (v k : K)) (congrArg (fun u : Kˣ => (u : K)) hv)
    _).symm

theorem diagU_torusElt_mem_blk {i j : Fin n} (hij : i ≠ j) {ζ : Kˣ} (hζ : h.bar ζ * ζ = 1) :
    diagU (torusElt i j ζ) ∈ blk h hij := by
  rw [mem_blk_iff hij]
  refine ⟨diag2 ζ, diag2_mem h ζ ?_, ?_⟩
  · rw [UnitaryFieldData.norm, mul_comm]
    exact hζ
  · have h2 : ((diag2 ζ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
        diagonal ![(ζ : K), ((ζ⁻¹ : Kˣ) : K)] := rfl
    rw [diagU_val, h2, coordEmbed_diagonal i j hij]
    congr 1
    funext k
    by_cases hki : k = i
    · subst hki
      simp [torusElt_apply_left hij]
    · by_cases hkj : k = j
      · subst hkj
        simp [torusElt_apply_right hij, hki]
      · simp [torusElt_apply_other hki hkj, hki, hkj]

theorem exists_swap {i j : Fin n} (hij : i ≠ j) :
    ∃ k ∈ blk h hij, ∀ v : Fin n → Kˣ, k * diagU v = diagU (v ∘ Equiv.swap i j) * k := by
  refine ⟨((swapCoord h hij : primeFormUnitary h (idGram K n)) : GL (Fin n) K),
    ⟨_, swapCoord_mem_coordSU h hij, rfl⟩, fun v => ?_⟩
  apply Units.ext
  simp only [Units.val_mul, diagU_val]
  have hk : (((swapCoord h hij : primeFormUnitary h (idGram K n)) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = coordEmbed K i j !![0, 1; -1, 0] := rfl
  rw [hk]
  ext k l
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hki : k = i
  · subst hki
    by_cases hli : l = k
    · subst hli
      simp [coordEmbed_apply_ii hij]
    · by_cases hlj : l = j
      · subst hlj
        simp [coordEmbed_apply_ij hij]
      · rw [coordEmbed_apply_of_not_mem_right hli hlj]
        simp [Ne.symm hli]
  · by_cases hkj : k = j
    · subst hkj
      by_cases hli : l = i
      · subst hli
        simp [coordEmbed_apply_ji hij, Equiv.swap_apply_right]
      · by_cases hlj : l = k
        · subst hlj
          simp [coordEmbed_apply_jj hij]
        · rw [coordEmbed_apply_of_not_mem_right hli hlj]
          simp [Ne.symm hlj]
    · rw [coordEmbed_apply_of_not_mem_left hki hkj]
      simp only [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hki hkj]
      by_cases hkl : k = l
      · subst hkl
        simp
      · simp [hkl]

theorem exists_vec_decomp {p : ℕ} (hp2 : Odd p) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p) {i j : Fin n}
    (hij : i ≠ j) {v : Fin n → Kˣ} (hv : v ∈ torusVec p n K) :
    ∃ (u : Fin n → Kˣ) (m : ℕ), u ∈ torusVec p n K ∧ u i = u j ∧
      v = u * (torusElt i j ζ) ^ m := by
  have hp0 : p ≠ 0 := by
    obtain ⟨k, hk⟩ := hp2
    omega
  have : NeZero p := ⟨hp0⟩
  have hζK : IsPrimitiveRoot (ζ : K) p := IsPrimitiveRoot.coe_units_iff.mpr hζ
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hξ : ((v i * (v j)⁻¹ : Kˣ) : K) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, mul_pow, inv_pow, hv.1 i, hv.1 j]
    simp
  obtain ⟨s, -, hs⟩ := hζK.eq_pow_of_pow_eq_one hξ
  have hsU : ζ ^ s = v i * (v j)⁻¹ := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    exact hs
  obtain ⟨k, hk⟩ := hp2
  set m : ℕ := s * (k + 1) with hm
  have hmm : m + m = s + p * s := by
    rw [hm, hk]
    ring
  have hζm : ζ ^ m * ζ ^ m = ζ ^ s := by
    rw [← pow_add, hmm, pow_add, pow_mul, hζp, one_pow, mul_one]
  set w : Fin n → Kˣ := torusElt i j ζ with hw
  have hwmem : w ∈ torusVec p n K := torusElt_mem hij hζp
  refine ⟨v * (w ^ m)⁻¹, m, ?_, ?_, ?_⟩
  · exact Subgroup.mul_mem _ hv (Subgroup.inv_mem _ (Subgroup.pow_mem _ hwmem m))
  · have hwi : (w ^ m) i = ζ ^ m := by
      rw [Pi.pow_apply, hw, torusElt_apply_left hij]
    have hwj : (w ^ m) j = (ζ ^ m)⁻¹ := by
      rw [Pi.pow_apply, hw, torusElt_apply_right hij, inv_pow]
    simp only [Pi.mul_apply, Pi.inv_apply, hwi, hwj, inv_inv]
    have h1 : v i = v j * ζ ^ s := by
      rw [hsU, mul_comm (v i), ← mul_assoc, mul_inv_cancel, one_mul]
    rw [h1, ← hζm]
    group
  · simp

@[expose] def IsBlockDiag (i j : Fin n) (M : Matrix (Fin n) (Fin n) K) : Prop :=
  ∀ k l : Fin n, ((k = i ∨ k = j) ↔ ¬ (l = i ∨ l = j)) → M k l = 0

theorem coordIncl_mul_coordProj_mul_apply {i j : Fin n} (hij : i ≠ j) {m : Type}
    [Fintype m] (N : Matrix (Fin n) m K) (k : Fin n) (b : m) :
    ((coordIncl K i j * coordProj K i j) * N) k b = if (k = i ∨ k = j) then N k b else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · rw [coordIncl_mul_coordProj_apply hij]
    by_cases hk : k = i ∨ k = j
    · simp [hk]
    · simp [hk]
  · intro m' _ hm'
    rw [coordIncl_mul_coordProj_apply hij]
    simp [Ne.symm hm']
  · intro hk
    exact absurd (Finset.mem_univ k) hk

theorem mul_coordIncl_mul_coordProj_apply {i j : Fin n} (hij : i ≠ j) {m : Type}
    [Fintype m] (N : Matrix m (Fin n) K) (a : m) (l : Fin n) :
    (N * (coordIncl K i j * coordProj K i j)) a l = if (l = i ∨ l = j) then N a l else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single l]
  · rw [coordIncl_mul_coordProj_apply hij]
    by_cases hl : l = i ∨ l = j
    · simp [hl]
    · simp [hl]
  · intro m' _ hm'
    rw [coordIncl_mul_coordProj_apply hij]
    simp [hm']
  · intro hl
    exact absurd (Finset.mem_univ l) hl

theorem mul_coordIncl_apply (i j : Fin n) (Y : Matrix (Fin n) (Fin n) K) (k : Fin n) (a : Fin 2) :
    (Y * coordIncl K i j) k a = Y k (![i, j] a) := by
  simp [Matrix.mul_apply, coordIncl_apply]

theorem coordProj_mul_apply (i j : Fin n) (Y : Matrix (Fin n) (Fin n) K) (a : Fin 2)
    (l : Fin n) : (coordProj K i j * Y) a l = Y (![i, j] a) l := by
  simp [Matrix.mul_apply, coordProj_apply]

theorem blockDiag_mul_coordIncl {i j : Fin n} (hij : i ≠ j) {Y : Matrix (Fin n) (Fin n) K}
    (hY : IsBlockDiag i j Y) :
    Y * coordIncl K i j = coordIncl K i j * (coordProj K i j * Y * coordIncl K i j) := by
  have h1 : Y * coordIncl K i j = (coordIncl K i j * coordProj K i j) * (Y * coordIncl K i j) := by
    ext k a
    rw [coordIncl_mul_coordProj_mul_apply hij]
    by_cases hk : k = i ∨ k = j
    · simp [hk]
    · have h0 : (Y * coordIncl K i j) k a = 0 := by
        rw [mul_coordIncl_apply]
        refine hY k _ ?_
        have : (![i, j] a = i ∨ ![i, j] a = j) := by fin_cases a <;> simp
        simp [hk, this]
      simp [hk, h0]
  calc Y * coordIncl K i j = (coordIncl K i j * coordProj K i j) * (Y * coordIncl K i j) := h1
    _ = coordIncl K i j * (coordProj K i j * Y * coordIncl K i j) := by
      simp only [Matrix.mul_assoc]

theorem coordProj_mul_blockDiag {i j : Fin n} (hij : i ≠ j) {Y : Matrix (Fin n) (Fin n) K}
    (hY : IsBlockDiag i j Y) :
    coordProj K i j * Y = (coordProj K i j * Y * coordIncl K i j) * coordProj K i j := by
  have h1 : coordProj K i j * Y = (coordProj K i j * Y) * (coordIncl K i j * coordProj K i j) := by
    ext a l
    rw [mul_coordIncl_mul_coordProj_apply hij]
    by_cases hl : l = i ∨ l = j
    · simp [hl]
    · have h0 : (coordProj K i j * Y) a l = 0 := by
        rw [coordProj_mul_apply]
        refine hY _ l ?_
        have : (![i, j] a = i ∨ ![i, j] a = j) := by fin_cases a <;> simp
        simp [hl, this]
      simp [hl, h0]
  calc coordProj K i j * Y = (coordProj K i j * Y) * (coordIncl K i j * coordProj K i j) := h1
    _ = (coordProj K i j * Y * coordIncl K i j) * coordProj K i j := by
      simp only [Matrix.mul_assoc]

theorem coordIncl_map_transpose (σ : K →+* K) (i j : Fin n) :
    ((coordIncl K i j).map σ)ᵀ = coordProj K i j := by
  have h1 : (coordIncl K i j).map σ = coordIncl K i j := by
    ext k a
    simp only [coordIncl_apply, Matrix.map_apply]
    split_ifs <;> simp
  rw [h1]
  rfl

theorem coordProj_map_transpose (σ : K →+* K) (i j : Fin n) :
    ((coordProj K i j).map σ)ᵀ = coordIncl K i j := by
  have h1 : (coordProj K i j).map σ = coordProj K i j := by
    ext a k
    simp only [coordProj_apply, Matrix.map_apply]
    split_ifs <;> simp
  rw [h1]
  exact Matrix.transpose_transpose _

theorem conj_mem_blk {i j : Fin n} (hij : i ≠ j) {y : GL (Fin n) K}
    (hyU : y ∈ primeFormUnitary h (idGram K n))
    (hy : IsBlockDiag i j (y : Matrix (Fin n) (Fin n) K))
    (hy' : IsBlockDiag i j ((y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    {g : GL (Fin n) K} (hg : g ∈ blk h hij) : y * g * y⁻¹ ∈ blk h hij := by
  obtain ⟨X, hX, hgX⟩ := (mem_blk_iff hij).mp hg
  have hYY : (y : Matrix (Fin n) (Fin n) K) * ((y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hY'Y : ((y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (y : Matrix (Fin n) (Fin n) K) =
      1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨h22, hconj⟩ := coordEmbed_conj hij hYY
    (blockDiag_mul_coordIncl hij hy) (blockDiag_mul_coordIncl hij hy')
    (coordProj_mul_blockDiag hij hy') (X : Matrix (Fin 2) (Fin 2) K)
  obtain ⟨h22', -⟩ := coordEmbed_conj hij hY'Y (blockDiag_mul_coordIncl hij hy')
    (blockDiag_mul_coordIncl hij hy) (coordProj_mul_blockDiag hij hy) (X : Matrix (Fin 2) (Fin 2) K)
  have hYuni : (((y : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (y : Matrix (Fin n) (Fin n) K)) =
      1 := by
    have := mem_primeFormUnitary.mp hyU
    simpa [idGram] using this
  have hY₂uni : ((coordProj K i j * (y : Matrix (Fin n) (Fin n) K) * coordIncl K i j).map
      h.bar)ᵀ * (coordProj K i j * (y : Matrix (Fin n) (Fin n) K) * coordIncl K i j) = 1 := by
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_mul, Matrix.transpose_mul,
      coordIncl_map_transpose, coordProj_map_transpose]
    have h1 := blockDiag_mul_coordIncl hij hy
    calc coordProj K i j * (((y : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * coordIncl K i j) *
          (coordProj K i j * (y : Matrix (Fin n) (Fin n) K) * coordIncl K i j)
        = coordProj K i j * ((y : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
            ((coordIncl K i j * (coordProj K i j * (y : Matrix (Fin n) (Fin n) K) *
              coordIncl K i j))) := by simp only [Matrix.mul_assoc]
      _ = coordProj K i j * ((y : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
            ((y : Matrix (Fin n) (Fin n) K) * coordIncl K i j) := by rw [← h1]
      _ = coordProj K i j * (((y : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ *
            (y : Matrix (Fin n) (Fin n) K)) * coordIncl K i j := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hYuni, Matrix.mul_one, coordProj_mul_coordIncl hij]
  let Y₂u : GL (Fin 2) K := ⟨coordProj K i j * (y : Matrix (Fin n) (Fin n) K) * coordIncl K i j,
    coordProj K i j * ((y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * coordIncl K i j,
    h22, h22'⟩
  have hY₂U : Y₂u ∈ primeFormUnitary h (idGram K 2) := by
    rw [mem_primeFormUnitary]
    show ((coordProj K i j * (y : Matrix (Fin n) (Fin n) K) * coordIncl K i j).map h.bar)ᵀ *
      (1 : Matrix (Fin 2) (Fin 2) K) *
      (coordProj K i j * (y : Matrix (Fin n) (Fin n) K) * coordIncl K i j) =
        (1 : Matrix (Fin 2) (Fin 2) K)
    rw [Matrix.mul_one]
    exact hY₂uni
  have hXU : X ∈ primeFormUnitary h (idGram K 2) := ((mem_gramSU_iff_unitary h).mp hX).1
  have hval : ((Y₂u * X * Y₂u⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (coordProj K i j * (y : Matrix (Fin n) (Fin n) K) * coordIncl K i j) *
        (X : Matrix (Fin 2) (Fin 2) K) *
        (coordProj K i j * ((y⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * coordIncl K i j) :=
    rfl
  refine (mem_blk_iff hij).mpr ⟨Y₂u * X * Y₂u⁻¹, ?_, ?_⟩
  · refine (mem_gramSU_iff_unitary h).mpr ⟨?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hY₂U hXU) (Subgroup.inv_mem _ hY₂U)
    · have hdetX := ((mem_gramSU_iff_unitary h).mp hX).2
      have hd : (Y₂u : Matrix (Fin 2) (Fin 2) K).det * ((Y₂u⁻¹ : GL (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K).det = 1 := by
        rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hdetX]
      calc (Y₂u : Matrix (Fin 2) (Fin 2) K).det * 1 * ((Y₂u⁻¹ : GL (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K).det = _ := by ring
        _ = 1 := hd
  · rw [Units.val_mul, Units.val_mul, hgX, hval]
    exact hconj

theorem blk_comm_of_disjoint {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) {x y : GL (Fin n) K} (hx : x ∈ blk h hij)
    (hy : y ∈ blk h hkl) : x * y = y * x := by
  obtain ⟨X, -, hX⟩ := (mem_blk_iff hij).mp hx
  obtain ⟨Y, -, hY⟩ := (mem_blk_iff hkl).mp hy
  apply Units.ext
  simp only [Units.val_mul, hX, hY]
  exact coordEmbed_comm_of_disjoint hik hil hjk hjl _ _

theorem blk_inf_eq_bot_of_disjoint {i j k l : Fin n} (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) : blk h hij ⊓ blk h hkl = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hy⟩
  obtain ⟨X, -, hX⟩ := (mem_blk_iff hij).mp hx
  obtain ⟨Y, -, hY⟩ := (mem_blk_iff hkl).mp hy
  have h1 := coordEmbed_eq_one_of_disjoint hik hil hjk hjl (hX.symm.trans hY)
  rw [Subgroup.mem_bot]
  apply Units.ext
  rw [hX, h1, Units.val_one]

theorem isBlockDiag_of_comm {i j : Fin n} {ζ : Kˣ} (hζ : ζ ≠ ζ⁻¹) {y : GL (Fin n) K}
    (hy : y * diagU (fun k => if k = i ∨ k = j then ζ else ζ⁻¹) =
      diagU (fun k => if k = i ∨ k = j then ζ else ζ⁻¹) * y) :
    IsBlockDiag i j (y : Matrix (Fin n) (Fin n) K) := by
  intro k l hkl
  have h1 := congrArg (fun z : GL (Fin n) K => (z : Matrix (Fin n) (Fin n) K) k l) hy
  simp only [Units.val_mul, diagU_val, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  have hne : (if k = i ∨ k = j then (ζ : K) else (ζ⁻¹ : Kˣ)) ≠
      (if l = i ∨ l = j then (ζ : K) else (ζ⁻¹ : Kˣ)) := by
    have hζK : (ζ : K) ≠ ((ζ⁻¹ : Kˣ) : K) := fun h' => hζ (Units.ext h')
    by_cases hk : k = i ∨ k = j
    · have hl : ¬ (l = i ∨ l = j) := hkl.mp hk
      simp only [hk, hl, ↓reduceIte]
      exact hζK
    · have hl : l = i ∨ l = j := by
        by_contra hl
        exact hk (hkl.mpr hl)
      simp only [hk, hl, ↓reduceIte]
      exact fun h' => hζK h'.symm
  have h2 : (y : Matrix (Fin n) (Fin n) K) k l * ((if l = i ∨ l = j then (ζ : K) else
      ((ζ⁻¹ : Kˣ) : K)) - (if k = i ∨ k = j then (ζ : K) else ((ζ⁻¹ : Kˣ) : K))) = 0 := by
    have : (y : Matrix (Fin n) (Fin n) K) k l * (if l = i ∨ l = j then (ζ : K) else
        ((ζ⁻¹ : Kˣ) : K)) = (if k = i ∨ k = j then (ζ : K) else ((ζ⁻¹ : Kˣ) : K)) *
          (y : Matrix (Fin n) (Fin n) K) k l := by
      simpa [apply_ite (fun u : Kˣ => (u : K))] using h1
    linear_combination this
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact h3
  · exact absurd (sub_eq_zero.mp h3).symm hne

theorem prod_ite_blk {i j : Fin 4} (hij : i ≠ j) (ζ : Kˣ) :
    ∏ k : Fin 4, (if k = i ∨ k = j then ζ else ζ⁻¹) = 1 := by
  classical
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const]
  have h1 : (Finset.univ.filter fun k : Fin 4 => k = i ∨ k = j) = {i, j} := by
    ext k
    simp
  have h2 : (Finset.univ.filter fun k : Fin 4 => k = i ∨ k = j).card = 2 := by
    rw [h1, Finset.card_pair hij]
  have h3 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 4)))
    (fun k : Fin 4 => k = i ∨ k = j)
  rw [Finset.card_univ, Fintype.card_fin, h2] at h3
  have h4 : (Finset.univ.filter fun k : Fin 4 => ¬ (k = i ∨ k = j)).card = 2 := by omega
  rw [h2, h4, inv_pow, mul_inv_cancel]

theorem conj_mem_blk_of_centralizes {p : ℕ} (hp2 : 2 < p) {ζ : Kˣ} (hζ : IsPrimitiveRoot ζ p)
    {i j : Fin 4} (hij : i ≠ j) {y : GL (Fin 4) K} (hyU : y ∈ primeFormUnitary h (idGram K 4))
    (hyc : ∀ x ∈ torusSU p 4 K, ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i i =
      ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) j j → y * x = x * y)
    {g : GL (Fin 4) K} (hg : g ∈ blk h hij) : y * g * y⁻¹ ∈ blk h hij := by
  have hζne : ζ ≠ ζ⁻¹ := by
    intro h'
    have h2 : ζ ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 1 [h']
      exact inv_mul_cancel ζ
    exact hζ.pow_ne_one_of_pos_of_lt (by norm_num) hp2 h2
  set v₀ : Fin 4 → Kˣ := fun k => if k = i ∨ k = j then ζ else ζ⁻¹ with hv₀
  have hx₀ : diagU v₀ ∈ torusSU p 4 K := by
    refine mem_torusSU_iff.mpr ⟨v₀, fun k => ?_, prod_ite_blk hij ζ, rfl⟩
    by_cases hk : k = i ∨ k = j
    · simp [hv₀, hk, hζ.pow_eq_one]
    · simp [hv₀, hk, inv_pow, hζ.pow_eq_one]
  have hx₀i : ((diagU v₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i i =
      ((diagU v₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) j j := by
    simp [diagU_apply_same, hv₀]
  have hc := hyc _ hx₀ hx₀i
  refine conj_mem_blk hij hyU (isBlockDiag_of_comm hζne hc) ?_ hg
  refine isBlockDiag_of_comm hζne ?_
  have := Commute.inv_left (show Commute y (diagU v₀) from hc)
  exact this.eq

@[expose] def swapMat (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

theorem swapMat_mul_self : swapMat K * swapMat K = 1 := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [swapMat, Matrix.mul_apply, Fin.sum_univ_two]

theorem swapMat_transpose : (swapMat K)ᵀ = swapMat K := by
  ext a b
  fin_cases a <;> fin_cases b <;> simp [swapMat]

theorem coordIncl_swap (i j : Fin n) : coordIncl K j i = coordIncl K i j * swapMat K := by
  ext k a
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  by_cases hk : k = i <;> by_cases hk' : k = j <;> fin_cases a <;>
    simp [coordIncl, swapMat, hk, hk'] <;> rfl

theorem coordEmbed_swap_indices (i j : Fin n) (X : Matrix (Fin 2) (Fin 2) K) :
    coordEmbed K j i X = coordEmbed K i j (swapMat K * X * swapMat K) := by
  have hπ : coordProj K j i = swapMat K * coordProj K i j := by
    unfold coordProj
    rw [coordIncl_swap, Matrix.transpose_mul, swapMat_transpose]
  have hX : swapMat K * (X - 1) * swapMat K = swapMat K * X * swapMat K - 1 := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, swapMat_mul_self]
  unfold coordEmbed
  rw [coordIncl_swap, hπ, ← hX]
  simp only [Matrix.mul_assoc]

theorem blk_symm_le {i j : Fin n} (hij : i ≠ j) : blk h hij.symm ≤ blk h hij := by
  intro g hg
  obtain ⟨X, hX, hgX⟩ := (mem_blk_iff hij.symm).mp hg
  let Pu : GL (Fin 2) K := ⟨swapMat K, swapMat K, swapMat_mul_self, swapMat_mul_self⟩
  have hPU : Pu ∈ primeFormUnitary h (idGram K 2) := by
    rw [mem_primeFormUnitary]
    show ((swapMat K).map h.bar)ᵀ * (1 : Matrix (Fin 2) (Fin 2) K) * swapMat K = 1
    have hm : (swapMat K).map h.bar = swapMat K := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [swapMat]
    rw [hm, swapMat_transpose, Matrix.mul_one, swapMat_mul_self]
  have hXU : X ∈ primeFormUnitary h (idGram K 2) := ((mem_gramSU_iff_unitary h).mp hX).1
  refine (mem_blk_iff hij).mpr ⟨Pu * X * Pu⁻¹, ?_, ?_⟩
  · refine (mem_gramSU_iff_unitary h).mpr ⟨?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hPU hXU) (Subgroup.inv_mem _ hPU)
    · have hdetX := ((mem_gramSU_iff_unitary h).mp hX).2
      have hd : (Pu : Matrix (Fin 2) (Fin 2) K).det * ((Pu⁻¹ : GL (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K).det = 1 := by
        rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hdetX]
      calc (Pu : Matrix (Fin 2) (Fin 2) K).det * 1 * ((Pu⁻¹ : GL (Fin 2) K) :
          Matrix (Fin 2) (Fin 2) K).det = _ := by ring
        _ = 1 := hd
  · rw [hgX, coordEmbed_swap_indices]
    rfl

theorem blk_symm {i j : Fin n} (hij : i ≠ j) : blk h hij.symm = blk h hij :=
  le_antisymm (blk_symm_le hij) (blk_symm_le hij.symm)

end CFSG.RankThree.PartOne.KFU
