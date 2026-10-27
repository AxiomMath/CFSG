module

public import CFSG.Quasithin.EmptyFaithful.S1565L16

public section

namespace CFSG.Quasithin.S146zU.UD1

open CFSG.Assembly.LowTwoRank
open Matrix

section Matrices

theorem exists_line_of_sq_zero {K : Type} [Field K] {N : Matrix (Fin 2) (Fin 2) K}
    (hN0 : N ≠ 0) (hN2 : N * N = 0) :
    ∃ u : Fin 2 → K, u ≠ 0 ∧
      ∀ x : Fin 2 → K, N *ᵥ x = 0 → ∀ a b : Fin 2, x a * u b = x b * u a := by
  obtain ⟨i, j, hij⟩ : ∃ i j, N i j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hN0 (Matrix.ext fun i j => hcon i j)
  have hu : ∀ k, N k 0 * N 0 j + N k 1 * N 1 j = 0 := by
    intro k
    have := congrFun (congrFun hN2 k) j
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  refine ⟨fun k => N k j, fun h => hij (congrFun h i), fun x hx a b => ?_⟩
  have hx' : ∀ k, N k 0 * x 0 + N k 1 * x 1 = 0 := by
    intro k
    have := congrFun hx k
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using this
  have e0 : (x 0 * N 1 j - x 1 * N 0 j) * N i 0 = 0 := by
    linear_combination (N 1 j) * hx' i - (x 1) * hu i
  have e1 : (x 0 * N 1 j - x 1 * N 0 j) * N i 1 = 0 := by
    linear_combination (x 0) * hu i - (N 0 j) * hx' i
  have key : x 0 * N 1 j = x 1 * N 0 j := by
    have : x 0 * N 1 j - x 1 * N 0 j = 0 := by
      fin_cases j
      · rcases mul_eq_zero.mp e0 with h | h
        · exact h
        · exact absurd h hij
      · rcases mul_eq_zero.mp e1 with h | h
        · exact h
        · exact absurd h hij
    exact sub_eq_zero.mp this
  fin_cases a <;> fin_cases b
  · rfl
  · exact key
  · exact key.symm
  · rfl

theorem exists_entry_of_sq_zero {K : Type} [Field K] {N N' : Matrix (Fin 2) (Fin 2) K}
    (hN0 : N ≠ 0) (hN2 : N * N = 0) (hN'0 : N' ≠ 0) (hN'2 : N' * N' = 0) :
    ∃ i j : Fin 2, ∀ X : Matrix (Fin 2) (Fin 2) K, N * X = 0 → N' * Xᵀ = 0 → X i j = 0 →
      X = 0 := by
  obtain ⟨u, hu0, hu⟩ := exists_line_of_sq_zero hN0 hN2
  obtain ⟨v, hv0, hv⟩ := exists_line_of_sq_zero hN'0 hN'2
  obtain ⟨i, hi⟩ : ∃ i, u i ≠ 0 := by
    by_contra h
    push Not at h
    exact hu0 (funext h)
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  refine ⟨i, j, fun X hX hX' hXij => ?_⟩
  have hrow : N' *ᵥ (fun m => X i m) = 0 := by
    funext m
    have := congrFun (congrFun hX' m) i
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  ext k l
  have hcol : N *ᵥ (fun m => X m l) = 0 := by
    funext m
    have := congrFun (congrFun hX m) l
    simpa [Matrix.mulVec, dotProduct, Matrix.mul_apply] using this
  have h1 := hu _ hcol k i
  have h2 := hv _ hrow l j
  have h3 : X i l = 0 := by
    have : X i l * v j = 0 := by rw [h2, hXij, zero_mul]
    exact (mul_eq_zero.mp this).resolve_right hj
  have h4 : X k l * u i = 0 := by rw [h1, h3, zero_mul]
  simpa using (mul_eq_zero.mp h4).resolve_right hi

theorem sub_one_mul_self_eq_zero {K : Type} [Field K] [CharP K 2]
    {G : Matrix (Fin 2) (Fin 2) K} (h : G * G = 1) : (G - 1) * (G - 1) = 0 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have e00 : G 0 0 * G 0 0 + G 0 1 * G 1 0 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun h 0) 0
  have e01 : G 0 0 * G 0 1 + G 0 1 * G 1 1 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun h 0) 1
  have e10 : G 1 0 * G 0 0 + G 1 1 * G 1 0 = 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun h 1) 0
  have e11 : G 1 0 * G 0 1 + G 1 1 * G 1 1 = 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun h 1) 1
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply, Matrix.one_apply]
  · linear_combination e00 + (1 - G 0 0) * h2
  · linear_combination e01 - (G 0 1) * h2
  · linear_combination e10 - (G 1 0) * h2
  · linear_combination e11 + (1 - G 1 1) * h2

end Matrices

section SL2

theorem statedSL2_eq_one_of_central {K : Type} [Field K] [CharP K 2] {g : ↥(StatedSL 2 K)}
    (h : ∀ k : ↥(StatedSL 2 K), k * g = g * k) : g = 1 := by
  set e := specialLinearGroupEquivStatedSL 2 K
  have hc : e.symm g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Subgroup.mem_center_iff]
    intro B
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h (e B)
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have hr1 : r = 1 := by
    rw [Fintype.card_fin] at hr
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have h3 : (r + 1) ^ 2 = 0 := by linear_combination hr + (r + 1) * h2
    have h5 : r + 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp h3
    have h6 : r = -1 := eq_neg_of_add_eq_zero_left h5
    rw [h6]
    exact (CharTwo.neg_eq (1 : K))
  have h1 : e.symm g = 1 := by
    apply Subtype.ext
    rw [← hrA, hr1]
    simp
  simpa using congrArg e h1

theorem matrix_ne_one {K : Type} [Field K] {g : ↥(StatedSL 2 K)} (h : g ≠ 1) :
    ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ≠ 1 :=
  fun h1 => h (Subtype.ext (Units.ext h1))

theorem matrix_pow_eq_one {K : Type} [Field K] {g : ↥(StatedSL 2 K)} {m : ℕ} (h : g ^ m = 1) :
    ((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ^ m = 1 := by
  have := congrArg (fun x : ↥(StatedSL 2 K) => ((x : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) h
  simpa [Subgroup.coe_pow, Units.val_pow_eq_pow_val] using this

end SL2

section Factors

variable {W : Type} [CommGroup W] {K : Type} [Field K]

@[expose] def tensorTranspose2 : TensorE2 K ≃* TensorE2 K :=
  AddEquiv.toMultiplicative (Matrix.transposeAddEquiv (Fin 2) (Fin 2) K)

@[expose] def tensorSwap2 (K : Type) [Field K] : TensorG2 K →* TensorG2 K :=
  (MulEquiv.prodComm (M := ↥(StatedSL 2 K)) (N := ↥(StatedSL 2 K))).toMonoidHom

theorem tensorData2_swap {Mp : Subgroup (MulAut W)} {π : TensorG2 K →* ↥Mp}
    {β : W ≃* TensorE2 K} (hd : IsTensorData2 Mp π β) :
    IsTensorData2 Mp (π.comp (tensorSwap2 K)) (β.trans tensorTranspose2) := by
  intro γ w
  obtain ⟨g, h⟩ := γ
  show tensorTranspose2 (β (((π (h, g) : ↥Mp) : MulAut W) w)) =
    tensorAct 2 K (g, h) (tensorTranspose2 (β w))
  rw [hd (h, g) w]
  apply Multiplicative.toAdd.injective
  simp [tensorTranspose2, tensorAct, Matrix.transpose_mul, mul_assoc]

theorem factorL2_swap {Mp : Subgroup (MulAut W)} (π : TensorG2 K →* ↥Mp) :
    factorL2 Mp (π.comp (tensorSwap2 K)) = factorR2 Mp π := by
  ext x
  simp only [mem_factorL2, mem_factorR2]
  rfl

theorem le_factorR2_of_commute [CharP K 2] {Mp L' : Subgroup (MulAut W)} {π : TensorG2 K →* ↥Mp}
    (hinj : Function.Injective π) (hπs : Function.Surjective π) (hL'Mp : L' ≤ Mp)
    (hcomm : ∀ x ∈ factorL2 Mp π, ∀ y ∈ L', x * y = y * x) : L' ≤ factorR2 Mp π := by
  intro y hy
  obtain ⟨⟨g, h⟩, hγ⟩ := hπs ⟨y, hL'Mp hy⟩
  have hγ' : ((π (g, h) : ↥Mp) : MulAut W) = y := congrArg Subtype.val hγ
  have hg : g = 1 := by
    refine statedSL2_eq_one_of_central fun k => ?_
    have h1 := hcomm _ (mem_factorL2.mpr ⟨k, rfl⟩) y hy
    have h2 : π (k, 1) * π (g, h) = π (g, h) * π (k, 1) := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hγ']
      exact h1
    rw [← map_mul, ← map_mul] at h2
    have h3 := hinj h2
    simpa using congrArg Prod.fst h3
  subst hg
  exact mem_factorR2.mpr ⟨h, hγ'⟩

theorem factorR2_le_of_sup [CharP K 2] {Mp L L' : Subgroup (MulAut W)} {π : TensorG2 K →* ↥Mp}
    (hinj : Function.Injective π) (hMp : Mp = L ⊔ L')
    (hcomm : ∀ x ∈ L, ∀ y ∈ L', x * y = y * x) (hL : L = factorL2 Mp π)
    (hL' : L' ≤ factorR2 Mp π) : factorR2 Mp π ≤ L' := by
  intro y hy
  obtain ⟨h, rfl⟩ := mem_factorR2.mp hy
  have hmem : ((π (1, h) : ↥Mp) : MulAut W) ∈ L ⊔ L' := hMp ▸ (π (1, h)).2
  obtain ⟨f, hf, a, ha, hfa⟩ :=
    (B19Aux.mem_sup_iff_of_le_normalizer (InternalSec.le_normalizer_of_commute hcomm)).1 hmem
  obtain ⟨k, rfl⟩ := mem_factorL2.mp (hL ▸ hf)
  obtain ⟨h', rfl⟩ := mem_factorR2.mp (hL' ha)
  have h1 : π (1, h) = π (k, 1) * π (1, h') := by
    apply Subtype.ext
    rw [Subgroup.coe_mul]
    exact hfa
  rw [← map_mul] at h1
  have h2 := hinj h1
  have h3 : h = h' := by simpa using congrArg Prod.snd h2
  rw [h3]
  exact ha

end Factors

section Fixed

variable {W : Type} [CommGroup W] {K : Type} [Field K]

theorem sub_one_mul_eq_zero_of_fix_left {Mp : Subgroup (MulAut W)} {π : TensorG2 K →* ↥Mp}
    {β : W ≃* TensorE2 K} (hd : IsTensorData2 Mp π β) (g : ↥(StatedSL 2 K)) {w : W}
    (hw : ((π (g, 1) : ↥Mp) : MulAut W) w = w) :
    (((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) - 1) * Multiplicative.toAdd (β w) = 0 := by
  have h1 := hd (g, 1) w
  rw [hw] at h1
  have h2 := congrArg Multiplicative.toAdd h1
  simp only [tensorAct, toAdd_ofAdd, Subgroup.coe_one, Units.val_one, Matrix.transpose_one,
    mul_one] at h2
  rw [sub_mul, one_mul, ← h2, sub_self]

theorem sub_one_mul_transpose_eq_zero_of_fix_right {Mp : Subgroup (MulAut W)}
    {π : TensorG2 K →* ↥Mp} {β : W ≃* TensorE2 K} (hd : IsTensorData2 Mp π β)
    (h : ↥(StatedSL 2 K)) {w : W} (hw : ((π (1, h) : ↥Mp) : MulAut W) w = w) :
    (((h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) - 1) * (Multiplicative.toAdd (β w))ᵀ = 0 := by
  have h1 := hd (1, h) w
  rw [hw] at h1
  have h2 := congrArg Multiplicative.toAdd h1
  simp only [tensorAct, toAdd_ofAdd, Subgroup.coe_one, Units.val_one, Matrix.one_mul] at h2
  have h3 := congrArg Matrix.transpose h2
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose] at h3
  rw [sub_mul, one_mul, ← h3, sub_self]

theorem card_fixV_pair_le [Finite K] [CharP K 2] {Mp : Subgroup (MulAut W)}
    {π : TensorG2 K →* ↥Mp} {β : W ≃* TensorE2 K} (hd : IsTensorData2 Mp π β)
    {g h : ↥(StatedSL 2 K)} (hg1 : g ≠ 1) (hg2 : g ^ 2 = 1) (hh1 : h ≠ 1) (hh2 : h ^ 2 = 1) :
    Nat.card ↥(fixV (Subgroup.zpowers ((π (g, 1) : ↥Mp) : MulAut W) ⊔
      Subgroup.zpowers ((π (1, h) : ↥Mp) : MulAut W))) ≤ Nat.card K := by
  obtain ⟨i, j, hij⟩ := exists_entry_of_sq_zero
    (sub_ne_zero.mpr (matrix_ne_one hg1))
    (sub_one_mul_self_eq_zero (by simpa [sq] using matrix_pow_eq_one hg2))
    (sub_ne_zero.mpr (matrix_ne_one hh1))
    (sub_one_mul_self_eq_zero (by simpa [sq] using matrix_pow_eq_one hh2))
  have hfix : ∀ w ∈ fixV (Subgroup.zpowers ((π (g, 1) : ↥Mp) : MulAut W) ⊔
      Subgroup.zpowers ((π (1, h) : ↥Mp) : MulAut W)),
      (((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) - 1) * Multiplicative.toAdd (β w) = 0 ∧
      (((h : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) - 1) *
        (Multiplicative.toAdd (β w))ᵀ = 0 := by
    intro w hw
    exact ⟨sub_one_mul_eq_zero_of_fix_left hd g
        (hw _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))),
      sub_one_mul_transpose_eq_zero_of_fix_right hd h
        (hw _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)))⟩
  refine (Nat.card_le_card_of_injective
    (fun w => Multiplicative.toAdd (β (w : W)) i j) fun w₁ w₂ hw => ?_)
  have hmem : (w₁ : W) * (w₂ : W)⁻¹ ∈ fixV (Subgroup.zpowers ((π (g, 1) : ↥Mp) : MulAut W) ⊔
      Subgroup.zpowers ((π (1, h) : ↥Mp) : MulAut W)) :=
    Subgroup.mul_mem _ w₁.2 (Subgroup.inv_mem _ w₂.2)
  obtain ⟨h1, h2⟩ := hfix _ hmem
  have h0 : Multiplicative.toAdd (β ((w₁ : W) * (w₂ : W)⁻¹)) = 0 := by
    apply hij _ h1 h2
    have : Multiplicative.toAdd (β ((w₁ : W) * (w₂ : W)⁻¹)) i j =
        Multiplicative.toAdd (β (w₁ : W)) i j - Multiplicative.toAdd (β (w₂ : W)) i j := by
      simp [map_mul, map_inv, sub_eq_add_neg]
    rw [this]
    exact sub_eq_zero.mpr hw
  have h3 : β ((w₁ : W) * (w₂ : W)⁻¹) = 1 := by
    apply Multiplicative.toAdd.injective
    rw [h0]
    rfl
  have h4 : (w₁ : W) * (w₂ : W)⁻¹ = 1 := β.injective (h3.trans (map_one β).symm)
  exact Subtype.ext (mul_inv_eq_one.mp h4)

theorem card_fixV_le_of_factorL2 [Finite K] [CharP K 2] {Mp L L' : Subgroup (MulAut W)}
    {π : TensorG2 K →* ↥Mp} {β : W ≃* TensorE2 K} (hd : IsTensorData2 Mp π β)
    (hπs : Function.Surjective π) (hMp : Mp = L ⊔ L')
    (hcomm : ∀ x ∈ L, ∀ y ∈ L', x * y = y * x) (hL : L = factorL2 Mp π)
    {a b : MulAut W} (ha : a ∈ L) (hb : b ∈ L') (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) :
    Nat.card ↥(fixV (Subgroup.zpowers a ⊔ Subgroup.zpowers b)) ≤ Nat.card K := by
  have hinj := hd.injective
  have hL'R : L' ≤ factorR2 Mp π :=
    le_factorR2_of_commute hinj hπs (hMp ▸ le_sup_right) (hL ▸ hcomm)
  obtain ⟨g, rfl⟩ := mem_factorL2.mp (hL ▸ ha)
  obtain ⟨h, rfl⟩ := mem_factorR2.mp (hL'R hb)
  have hg1 : g ≠ 1 := by
    intro h1
    apply ha1
    rw [h1, Prod.mk_one_one, map_one]
    rfl
  have hh1 : h ≠ 1 := by
    intro h1
    apply hb1
    rw [h1, Prod.mk_one_one, map_one]
    rfl
  have hg2 : g ^ 2 = 1 := by
    have hgr : (g, (1 : ↥(StatedSL 2 K))) ^ 2 = 1 := by
      apply hinj
      rw [map_pow, map_one]
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      exact ha2
    simpa using congrArg Prod.fst hgr
  have hh2 : h ^ 2 = 1 := by
    have hhr : ((1 : ↥(StatedSL 2 K)), h) ^ 2 = 1 := by
      apply hinj
      rw [map_pow, map_one]
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      exact hb2
    simpa using congrArg Prod.snd hhr
  exact card_fixV_pair_le hd hg1 hg2 hh1 hh2

theorem fixV_eq_bot_of_factorL2 [CharP K 2] {Mp L L' : Subgroup (MulAut W)}
    {π : TensorG2 K →* ↥Mp} {β : W ≃* TensorE2 K} (hd : IsTensorData2 Mp π β)
    (hπs : Function.Surjective π) (hMp : Mp = L ⊔ L')
    (hcomm : ∀ x ∈ L, ∀ y ∈ L', x * y = y * x) (hL : L = factorL2 Mp π)
    {b₀ : MulAut W} (hb₀ : b₀ ∈ L) (hb₀1 : b₀ ≠ 1) (hodd : Odd (orderOf b₀)) :
    fixV L' = ⊥ := by
  have hinj := hd.injective
  have hL'R : L' ≤ factorR2 Mp π :=
    le_factorR2_of_commute hinj hπs (hMp ▸ le_sup_right) (hL ▸ hcomm)
  have hRL' : factorR2 Mp π ≤ L' := factorR2_le_of_sup hinj hMp hcomm hL hL'R
  obtain ⟨g, hg⟩ := mem_factorL2.mp (hL ▸ hb₀)
  have hg1 : g ≠ 1 := by
    intro h1
    apply hb₀1
    rw [← hg, h1, Prod.mk_one_one, map_one]
    rfl
  have hgr : g ^ (orderOf b₀) = 1 := by
    have hgr' : (g, (1 : ↥(StatedSL 2 K))) ^ (orderOf b₀) = 1 := by
      apply hinj
      rw [map_pow, map_one]
      apply Subtype.ext
      rw [Subgroup.coe_pow, hg]
      exact pow_orderOf_eq_one b₀
    simpa using congrArg Prod.fst hgr'
  have hdet := CFSG.Quasithin.Vol2.Ch10.SecA.det_eq_one_of_mem_statedSL g.2
  have hy : ((π (1, g) : ↥Mp) : MulAut W) ∈ L' := hRL' (mem_factorR2.mpr ⟨g, rfl⟩)
  refine (Subgroup.eq_bot_iff_forall _).mpr fun c hc => ?_
  have h3 := sub_one_mul_transpose_eq_zero_of_fix_right hd g (hc _ hy)
  have h4 : (((g : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)) *
      (Multiplicative.toAdd (β c))ᵀ = (Multiplicative.toAdd (β c))ᵀ :=
    sub_eq_zero.mp (by rwa [sub_mul, one_mul] at h3)
  have h5 : (Multiplicative.toAdd (β c))ᵀ = 0 := by
    by_contra hX
    exact matrix_ne_one hg1 (eq_one_of_mul_fixed hdet hodd (matrix_pow_eq_one hgr) h4 hX)
  have h6 : β c = 1 := by
    apply Multiplicative.toAdd.injective
    rw [Matrix.transpose_eq_zero.mp h5]
    rfl
  exact β.injective (h6.trans (map_one β).symm)

end Fixed

section Reduction

theorem exists_data_of_omega4 {W : Type} [CommGroup W]
    {Mp L L' : Subgroup (MulAut W)} {n : ℕ} (hn3 : 3 ≤ n)
    (hL : IsPSL 2 2 n ↥(autSub L (⊤ : Subgroup W)))
    (hΩ : Omega4PlusModule (autSub Mp (⊤ : Subgroup W)) n) (hMp : Mp = L ⊔ L')
    (hcomm : ∀ x ∈ L, ∀ y ∈ L', x * y = y * x) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ^ n ∧
      ∃ (π : TensorG2 K →* ↥Mp) (β : W ≃* TensorE2 K),
        Function.Surjective π ∧ IsTensorData2 Mp π β ∧ L = factorL2 Mp π := by
  have hLn : IsPSL 2 2 n ↥L := isPSL_of_autSub_top rfl hL
  have hLq := isQuasisimple_of_psl2_or_sz hn3 (Or.inl hLn)
  have h504 := le_card_of_psl2_or_sz hn3 (Or.inl hLn)
  have hL1 : L ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at h504
    omega
  obtain ⟨K, fK, finK, hK, π, β, hπs, hd⟩ := exists_tensorData2 hΩ
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card, hK])
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
  rcases eq_factor_or2 hK4 hd hπs hMp hcomm hLq hL1 with h | h
  · exact ⟨K, fK, finK, hchar, hK, π, β, hπs, hd, h⟩
  · exact ⟨K, fK, finK, hchar, hK, π.comp (tensorSwap2 K), β.trans tensorTranspose2,
      hπs.comp (MulEquiv.surjective _), tensorData2_swap hd, h.trans (factorL2_swap π).symm⟩

end Reduction

end CFSG.Quasithin.S146zU.UD1

namespace CFSG.Quasithin.S146zU

open CFSG.Assembly.LowTwoRank UD1

theorem omega4_fixV_card_le {W : Type} [CommGroup W]
    {Mp L L' : Subgroup (MulAut W)} {n : ℕ} (hn3 : 3 ≤ n)
    (hL : IsPSL 2 2 n ↥(autSub L (⊤ : Subgroup W)))
    (hΩ : Omega4PlusModule (autSub Mp (⊤ : Subgroup W)) n) (hMp : Mp = L ⊔ L')
    (hcomm : ∀ x ∈ L, ∀ y ∈ L', x * y = y * x)
    {a b : MulAut W} (ha : a ∈ L) (hb : b ∈ L') (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) :
    Nat.card ↥(fixV (Subgroup.zpowers a ⊔ Subgroup.zpowers b)) ≤ 2 ^ n := by
  obtain ⟨K, fK, finK, hchar, hK, π, β, hπs, hd, hL'⟩ := exists_data_of_omega4 hn3 hL hΩ hMp hcomm
  rw [← hK]
  exact card_fixV_le_of_factorL2 hd hπs hMp hcomm hL' ha hb ha1 hb1 ha2 hb2

end CFSG.Quasithin.S146zU
