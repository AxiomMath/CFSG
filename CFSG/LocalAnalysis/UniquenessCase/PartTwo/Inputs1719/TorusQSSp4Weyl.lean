module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeylMatrices
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusRegular
public import TauCeti.LinearAlgebra.Eigenspace.DiagonalBasis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS

open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

variable {K : Type} [Field K]

local notation "spMat " g =>
  (((g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)

@[expose] def IsPermSp (n : StatedSp 2 K) (π : Equiv.Perm (Fin 2 ⊕ Fin 2)) : Prop :=
  ∀ i j, (spMat n) i j = if i = π j then 1 else 0

theorem spMat_mul (x y : StatedSp 2 K) : (spMat (x * y)) = (spMat x) * (spMat y) := rfl

theorem spMat_inv_mul (x : StatedSp 2 K) : (spMat x⁻¹) * (spMat x) = 1 := by
  change (spMat (x⁻¹ * x)) = 1
  rw [inv_mul_cancel]
  rfl

theorem IsPermSp.inv {n : StatedSp 2 K} {π : Equiv.Perm (Fin 2 ⊕ Fin 2)} (hn : IsPermSp n π) :
    IsPermSp n⁻¹ π⁻¹ := by
  set Q : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
    Matrix.of fun i j => if i = π⁻¹ j then 1 else 0
  have hQ : (spMat n) * Q = 1 := by
    ext i j
    rw [Matrix.mul_apply, Finset.sum_eq_single (π⁻¹ j)]
    · rw [hn]
      simp only [Q, Matrix.of_apply, if_true, mul_one, Matrix.one_apply, Equiv.Perm.inv_def,
        Equiv.apply_symm_apply]
    · intro b _ hb
      simp only [Q, Matrix.of_apply, if_neg hb, mul_zero]
    · simp
  have h : (spMat n⁻¹) = Q := by
    calc (spMat n⁻¹) = (spMat n⁻¹) * ((spMat n) * Q) := by rw [hQ, Matrix.mul_one]
      _ = ((spMat n⁻¹) * (spMat n)) * Q := (Matrix.mul_assoc _ _ _).symm
      _ = Q := by rw [spMat_inv_mul, Matrix.one_mul]
  intro i j
  exact congrFun (congrFun h i) j

theorem IsPermSp.conj_apply {n : StatedSp 2 K} {π : Equiv.Perm (Fin 2 ⊕ Fin 2)}
    (hn : IsPermSp n π) (g : StatedSp 2 K) (k j : Fin 2 ⊕ Fin 2) :
    (spMat (n * g * n⁻¹)) (π k) (π j) = (spMat g) k j := by
  have hi := hn.inv
  change ((spMat n) * (spMat g) * (spMat n⁻¹)) (π k) (π j) = _
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  · rw [Matrix.mul_apply, Finset.sum_eq_single k, hn, hi]
    · simp [Equiv.Perm.inv_def]
    · intro b _ hb
      rw [hn, if_neg (fun h => hb (π.injective h).symm), zero_mul]
    · simp
  · intro b _ hb
    rw [hi, if_neg (fun h => hb (by rw [h, Equiv.Perm.inv_def, Equiv.symm_apply_apply])),
      mul_zero]
  · simp

theorem isPermSp_one : IsPermSp (1 : StatedSp 2 K) 1 := by
  intro i j
  change (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) i j = _
  rw [Matrix.one_apply, Equiv.Perm.one_apply]

theorem IsPermSp.mul {n m : StatedSp 2 K} {π σ : Equiv.Perm (Fin 2 ⊕ Fin 2)}
    (hn : IsPermSp n π) (hm : IsPermSp m σ) : IsPermSp (n * m) (π * σ) := by
  intro i j
  rw [spMat_mul, Matrix.mul_apply, Finset.sum_eq_single (σ j)]
  · rw [hn, hm, if_pos rfl, mul_one, Equiv.Perm.mul_apply]
  · intro b _ hb
    rw [hm, if_neg hb, mul_zero]
  · simp

section CharTwo

variable [CharP K 2]

theorem isPermSp_lam_sl2W (i : Fin 2) :
    IsPermSp (lam i sl2W : StatedSp 2 K) (Equiv.swap (Sum.inl i) (Sum.inr i)) := by
  intro x y
  show (((lam i sl2W : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) x y = _
  rw [coe_lam, coe_sl2W, CharTwo.neg_eq]
  rcases x with x | x <;> rcases y with y | y <;> fin_cases i <;> fin_cases x <;> fin_cases y <;>
    simp [pairMat, Equiv.swap_apply_def, Matrix.one_apply]

abbrev planeSwap : Equiv.Perm (Fin 2 ⊕ Fin 2) :=
  Equiv.swap (Sum.inl 0) (Sum.inl 1) * Equiv.swap (Sum.inr 0) (Sum.inr 1)

theorem isPermSp_rho_sl2W :
    IsPermSp (rho (0 : Fin 2) 1 (by decide) sl2W : StatedSp 2 K) planeSwap := by
  intro x y
  show (((rho (0 : Fin 2) 1 (by decide) sl2W : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) x y = _
  rw [coe_rho, coe_sl2W, coe_sl2W_inv, CharTwo.neg_eq]
  rcases x with x | x <;> rcases y with y | y <;> fin_cases x <;> fin_cases y <;>
    simp [pairMat, Matrix.fromBlocks, Equiv.swap_apply_def]

omit [CharP K 2] in
theorem IsPermSp.conj_torusHom_mem {n : StatedSp 2 K} {π : Equiv.Perm (Fin 2 ⊕ Fin 2)}
    (hn : IsPermSp n π) (hπ : π ∈ signedPermGroup 2) (t : Fin 2 → Kˣ) :
    n * torusHom t * n⁻¹ ∈ torus 2 K := by
  set u : Fin 2 ⊕ Fin 2 → Kˣ := Sum.elim t (fun i => (t i)⁻¹) with hudef
  have hu : ∀ y : Fin 2 ⊕ Fin 2, u y.swap = (u y)⁻¹ := by
    rintro (y | y) <;> simp [u]
  have hcoe : ∀ s : Fin 2 → Kˣ, ∀ y : Fin 2 ⊕ Fin 2,
      (Sum.elim (fun i => (s i : K)) (fun i => (((s i)⁻¹ : Kˣ) : K)) y) =
        ((Sum.elim s (fun i => (s i)⁻¹) y : Kˣ) : K) := by
    intro s y
    rcases y with y | y <;> rfl
  have hπi : ∀ x : Fin 2 ⊕ Fin 2, π⁻¹ x.swap = (π⁻¹ x).swap :=
    mem_signedPermGroup.mp ((signedPermGroup 2).inv_mem hπ)
  refine ⟨fun i => u (π⁻¹ (Sum.inl i)), ?_⟩
  apply statedSp_ext
  ext x y
  obtain ⟨k, rfl⟩ := π.surjective x
  obtain ⟨j, rfl⟩ := π.surjective y
  rw [hn.conj_apply, coe_torusHom, coe_torusHom, Matrix.diagonal_apply, Matrix.diagonal_apply,
    hcoe, hcoe]
  by_cases hkj : k = j
  · subst hkj
    simp only [if_true]
    congr 1
    rcases hk : π k with i | i
    · simp only [Sum.elim_inl]
      have h1 : π⁻¹ (Sum.inl i) = k := by
        rw [← hk]
        simp
      rw [h1]
    · simp only [Sum.elim_inr]
      have h2 : π⁻¹ (Sum.inr i) = k := by
        rw [← hk]
        simp
      have h1 : π⁻¹ (Sum.inl i) = k.swap := by
        have := hπi (Sum.inr i)
        rw [h2] at this
        exact this
      rw [h1, hu, inv_inv]
  · rw [if_neg (fun h => hkj (π.injective h)), if_neg hkj]

omit [CharP K 2] in
theorem IsPermSp.torus_le_normalizer_map {n : StatedSp 2 K} {π : Equiv.Perm (Fin 2 ⊕ Fin 2)}
    (hn : IsPermSp n π) (hπ : π ∈ signedPermGroup 2) {H : Subgroup (StatedSp 2 K)}
    (hT : torus 2 K ≤ Subgroup.normalizer (H : Set (StatedSp 2 K))) :
    torus 2 K ≤ Subgroup.normalizer
      ((H.map (MulAut.conj n).toMonoidHom : Subgroup (StatedSp 2 K)) : Set (StatedSp 2 K)) := by
  rintro _ ⟨s, rfl⟩
  have h1 : n⁻¹ * torusHom s * n ∈ torus 2 K := by
    simpa using hn.inv.conj_torusHom_mem ((signedPermGroup 2).inv_mem hπ) s
  rw [← Subgroup.map_equiv_normalizer_eq]
  refine ⟨n⁻¹ * torusHom s * n, hT h1, ?_⟩
  simp [MulAut.conj_apply, mul_assoc]

omit [CharP K 2] in
theorem IsPermSp.entry_map {n : StatedSp 2 K} {π : Equiv.Perm (Fin 2 ⊕ Fin 2)}
    (hn : IsPermSp n π) {H : Subgroup (StatedSp 2 K)}
    {P : Fin 2 ⊕ Fin 2 → Fin 2 ⊕ Fin 2 → Prop} (hH : ∀ h ∈ H, ∀ k j, P k j → (spMat h) k j = 0) :
    ∀ h ∈ H.map (MulAut.conj n).toMonoidHom, ∀ k j, P (π⁻¹ k) (π⁻¹ j) → (spMat h) k j = 0 := by
  rintro _ ⟨h₀, hh₀, rfl⟩ k j hP
  have := hn.conj_apply h₀ (π⁻¹ k) (π⁻¹ j)
  have hk : π (π⁻¹ k) = k := by rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  have hj : π (π⁻¹ j) = j := by rw [Equiv.Perm.inv_def, Equiv.apply_symm_apply]
  rw [hk, hj] at this
  change (spMat (n * h₀ * n⁻¹)) k j = 0
  rw [this]
  exact hH h₀ hh₀ _ _ hP

theorem fromBlocks_J_apply (a b : Fin 2 ⊕ Fin 2) :
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) a b =
      if a = b.swap then 1 else 0 := by
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, CharTwo.neg_eq, eq_comm]

theorem spMat_inv_apply (h : StatedSp 2 K) (a b : Fin 2 ⊕ Fin 2) :
    (spMat h⁻¹) a b = (spMat h) b.swap a.swap := by
  set J : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K := fromBlocks 0 1 (-1) 0
  have hsp : (spMat h)ᵀ * J * (spMat h) = J := mem_statedSp_iff.mp h.2
  have hJJ : J * J = 1 := by
    ext a b
    rw [Matrix.mul_apply, Finset.sum_eq_single b.swap]
    · simp only [J, fromBlocks_J_apply, Sum.swap_swap, if_true, mul_one, Matrix.one_apply]
    · intro c _ hc
      simp [J, fromBlocks_J_apply, hc]
    · simp
  have hinv : J * (spMat h)ᵀ * J * (spMat h) = 1 := by
    rw [Matrix.mul_assoc J, Matrix.mul_assoc J, hsp, hJJ]
  have heq : (spMat h⁻¹) = J * (spMat h)ᵀ * J := by
    calc (spMat h⁻¹) = (J * (spMat h)ᵀ * J * (spMat h)) * (spMat h⁻¹) := by
          rw [hinv, Matrix.one_mul]
      _ = J * (spMat h)ᵀ * J * ((spMat h) * (spMat h⁻¹)) := by
          simp only [Matrix.mul_assoc]
      _ = J * (spMat h)ᵀ * J := by
          rw [show (spMat h) * (spMat h⁻¹) = 1 from by
            change (spMat (h * h⁻¹)) = 1
            rw [mul_inv_cancel]
            rfl, Matrix.mul_one]
  rw [show (spMat h⁻¹) a b = (J * (spMat h)ᵀ * J) a b from congrFun (congrFun heq a) b]
  rw [Matrix.mul_apply, Finset.sum_eq_single b.swap]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a.swap]
    · simp [J, fromBlocks_J_apply]
    · intro c _ hc
      have hJ : J a c = 0 := by
        simp only [J, fromBlocks_J_apply]
        exact if_neg fun h' => hc (by rw [h', Sum.swap_swap])
      rw [hJ, zero_mul]
    · simp
  · intro c _ hc
    have hJ : J c b = 0 := by
      simp only [J, fromBlocks_J_apply]
      exact if_neg hc
    rw [hJ, mul_zero]
  · simp

theorem exists_torusHom_diag_injective [Finite K] (hK : 8 ≤ Nat.card K) :
    ∃ t : Fin 2 → Kˣ,
      Function.Injective (Sum.elim (fun i => (t i : K)) fun i => (((t i)⁻¹ : Kˣ) : K)) := by
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf ζ = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, Nat.card_units]
  have hpow : ∀ k : ℕ, 0 < k → k < 7 → ζ ^ k ≠ 1 := fun k hk0 hk7 h => by
    have := orderOf_le_of_pow_eq_one hk0 h
    omega
  refine ⟨![ζ, ζ ^ 2], torusHom_diag_injective_sp4 ?_ ?_ ?_ ?_⟩
  · simpa using hpow 1 (by norm_num) (by norm_num)
  · simpa using hpow 2 (by norm_num) (by norm_num)
  · show ζ ≠ ζ ^ 2
    intro h
    apply hpow 1 (by norm_num) (by norm_num)
    have h' : ζ * 1 = ζ * ζ := by rw [mul_one, ← sq]; exact h
    rw [pow_one]
    exact (mul_left_cancel h').symm
  · show ζ ≠ (ζ ^ 2)⁻¹
    intro h
    apply hpow 3 (by norm_num) (by norm_num)
    calc ζ ^ 3 = ζ * ζ ^ 2 := by group
      _ = (ζ ^ 2)⁻¹ * ζ ^ 2 := by rw [← h]
      _ = 1 := inv_mul_cancel _

theorem single_mem_of_torus_invariant [Finite K] (hK : 8 ≤ Nat.card K)
    {W : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hW : ∀ d ∈ torus 2 K, ∀ w ∈ W, (spMat d) *ᵥ w ∈ W)
    {w : Fin 2 ⊕ Fin 2 → K} (hw : w ∈ W) {j : Fin 2 ⊕ Fin 2} (hj : w j ≠ 0) :
    Pi.single j 1 ∈ W := by
  obtain ⟨t, ht⟩ := exists_torusHom_diag_injective hK
  have hf : ∀ i, (Matrix.mulVecLin (spMat (torusHom t))) (Pi.basisFun K (Fin 2 ⊕ Fin 2) i) =
      (Sum.elim (fun i => (t i : K)) fun i => (((t i)⁻¹ : Kˣ) : K)) i •
        Pi.basisFun K (Fin 2 ⊕ Fin 2) i := by
    intro i
    rw [Matrix.mulVecLin_apply, Pi.basisFun_apply, coe_torusHom, Matrix.mulVec_single_one]
    ext x
    by_cases hx : x = i
    · subst hx
      simp
    · simp [hx]
  have h := (Pi.basisFun K (Fin 2 ⊕ Fin 2)).self_mem_of_repr_ne_zero hf ht
    (fun v hv => hW _ ⟨t, rfl⟩ v hv) hw (by rwa [Pi.basisFun_repr])
  simpa using h

theorem entry_eq_zero_of_invariant [Finite K] (hK : 8 ≤ Nat.card K)
    {W : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hW : ∀ d ∈ torus 2 K, ∀ w ∈ W, (spMat d) *ᵥ w ∈ W)
    {g : StatedSp 2 K} (hg : ∀ w ∈ W, (spMat g) *ᵥ w ∈ W) {j k : Fin 2 ⊕ Fin 2}
    (hj : Pi.single j 1 ∈ W) (hk : Pi.single k 1 ∉ W) : (spMat g) k j = 0 := by
  by_contra hne
  apply hk
  refine single_mem_of_torus_invariant hK hW (hg _ hj) ?_
  rw [Matrix.mulVec_single_one]
  exact hne

theorem exists_isPermSp_apply_eq_inl_zero (x : Fin 2 ⊕ Fin 2) :
    ∃ (n : StatedSp 2 K) (π : Equiv.Perm (Fin 2 ⊕ Fin 2)), IsPermSp n π ∧
      π ∈ signedPermGroup 2 ∧ π x = Sum.inl 0 := by
  rcases x with x | x <;> fin_cases x
  · exact ⟨1, 1, isPermSp_one, one_mem _, rfl⟩
  · exact ⟨_, _, isPermSp_rho_sl2W, mem_signedPermGroup.mpr (by decide), by decide⟩
  · exact ⟨_, _, isPermSp_lam_sl2W 0, mem_signedPermGroup.mpr (by decide), by decide⟩
  · exact ⟨_, _, isPermSp_rho_sl2W.mul (isPermSp_lam_sl2W 1),
      mem_signedPermGroup.mpr (by decide), by decide⟩

theorem line_of_triple {H : Subgroup (StatedSp 2 K)} {y : Fin 2 ⊕ Fin 2}
    (hy : ∀ h ∈ H, ∀ j, j ≠ y → (spMat h) y j = 0) :
    ∀ h ∈ H, ∀ k, k ≠ y.swap → (spMat h) k y.swap = 0 := by
  intro h hh k hk
  have := hy h⁻¹ (H.inv_mem hh) k.swap fun h' => hk (by rw [← h', Sum.swap_swap])
  rwa [spMat_inv_apply, Sum.swap_swap] at this

end CharTwo

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS

end
