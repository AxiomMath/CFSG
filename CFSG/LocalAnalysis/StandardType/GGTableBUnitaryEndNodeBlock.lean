module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.StandardType

namespace TableBUE

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.RankThree.Classical CFSG.RankThree.Classical2

variable {K : Type} [Field K] {d : ℕ}

section Block

@[expose] def IsBlockOn (S : Finset (Fin d)) (M : Matrix (Fin d) (Fin d) K) : Prop :=
  ∀ i j, (i ∉ S ∨ j ∉ S) → M i j = (1 : Matrix (Fin d) (Fin d) K) i j

variable {S : Finset (Fin d)} {M N : Matrix (Fin d) (Fin d) K}

theorem IsBlockOn.one : IsBlockOn S (1 : Matrix (Fin d) (Fin d) K) := fun _ _ _ => rfl

theorem IsBlockOn.mul_apply_left (hM : IsBlockOn S M) {i : Fin d} (hi : i ∉ S) (j : Fin d) :
    (M * N) i j = N i j := by
  have h : (M * N) i j = ((1 : Matrix (Fin d) (Fin d) K) * N) i j := by
    simp only [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [hM i k (Or.inl hi)]
  rw [h, Matrix.one_mul]

theorem IsBlockOn.mul_apply_right (hN : IsBlockOn S N) (i : Fin d) {j : Fin d} (hj : j ∉ S) :
    (M * N) i j = M i j := by
  have h : (M * N) i j = (M * (1 : Matrix (Fin d) (Fin d) K)) i j := by
    simp only [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [hN k j (Or.inr hj)]
  rw [h, Matrix.mul_one]

theorem IsBlockOn.mul (hM : IsBlockOn S M) (hN : IsBlockOn S N) : IsBlockOn S (M * N) := by
  rintro i j (hi | hj)
  · rw [hM.mul_apply_left (N := N) hi, hN i j (Or.inl hi)]
  · rw [hN.mul_apply_right (M := M) i hj, hM i j (Or.inr hj)]

theorem IsBlockOn.of_inv (hM : IsBlockOn S M) (h1 : M * N = 1) (h2 : N * M = 1) :
    IsBlockOn S N := by
  rintro i j (hi | hj)
  · rw [← hM.mul_apply_left (N := N) hi, h1]
  · rw [← hM.mul_apply_right (M := N) i hj, h2]

theorem IsBlockOn.map_transpose (hM : IsBlockOn S M) (f : K →+* K) :
    IsBlockOn S ((M.map f)ᵀ) := by
  intro i j hij
  rw [Matrix.transpose_apply, Matrix.map_apply, hM j i hij.symm, Matrix.one_apply,
    Matrix.one_apply]
  by_cases h : j = i
  · subst h
    simp
  · simp [h, Ne.symm h]

@[expose] noncomputable def blockRes (S : Finset (Fin d)) (M : Matrix (Fin d) (Fin d) K) :
    Matrix (Fin S.card) (Fin S.card) K :=
  fun a b => M (S.equivFin.symm a) (S.equivFin.symm b)

@[expose] noncomputable def blockExt (S : Finset (Fin d)) (N : Matrix (Fin S.card) (Fin S.card) K) :
    Matrix (Fin d) (Fin d) K :=
  fun i j => if hi : i ∈ S then (if hj : j ∈ S then N (S.equivFin ⟨i, hi⟩) (S.equivFin ⟨j, hj⟩)
    else 0) else (1 : Matrix (Fin d) (Fin d) K) i j

theorem isBlockOn_blockExt (N : Matrix (Fin S.card) (Fin S.card) K) :
    IsBlockOn S (blockExt S N) := by
  rintro i j (hi | hj)
  · simp [blockExt, hi]
  · by_cases hi : i ∈ S
    · have hij : i ≠ j := fun h => hj (h ▸ hi)
      simp [blockExt, hi, hj, hij]
    · simp [blockExt, hi]

theorem blockRes_blockExt (N : Matrix (Fin S.card) (Fin S.card) K) :
    blockRes S (blockExt S N) = N := by
  ext a b
  simp [blockRes, blockExt]

theorem blockExt_blockRes (hM : IsBlockOn S M) : blockExt S (blockRes S M) = M := by
  ext i j
  by_cases hi : i ∈ S
  · by_cases hj : j ∈ S
    · simp [blockExt, blockRes, hi, hj]
    · have hij : i ≠ j := fun h => hj (h ▸ hi)
      simp only [blockExt, hi, hj, dite_true, dite_false]
      rw [hM i j (Or.inr hj), Matrix.one_apply_ne hij]
  · simp only [blockExt, hi, dite_false]
    rw [hM i j (Or.inl hi)]

theorem blockRes_mul (hM : IsBlockOn S M) (N : Matrix (Fin d) (Fin d) K) :
    blockRes S (M * N) = blockRes S M * blockRes S N := by
  ext a b
  simp only [blockRes, Matrix.mul_apply]
  set e := S.equivFin.symm with he
  have hz : ∀ k ∉ S, M (e a) k * N k (e b) = 0 := by
    intro k hk
    have hne : ((e a : ↥S) : Fin d) ≠ k := fun h => hk (h ▸ (e a).2)
    rw [hM _ k (Or.inr hk), Matrix.one_apply_ne hne, zero_mul]
  rw [← Finset.sum_subset (Finset.subset_univ S) fun k _ hk => hz k hk,
    ← Finset.sum_coe_sort S]
  exact (Equiv.sum_comp e fun k : ↥S => M (e a) k * N k (e b)).symm

theorem blockRes_one : blockRes S (1 : Matrix (Fin d) (Fin d) K) = 1 := by
  ext a b
  simp only [blockRes, Matrix.one_apply]
  by_cases h : a = b
  · subst h
    simp
  · have hne : ((S.equivFin.symm a : ↥S) : Fin d) ≠ S.equivFin.symm b :=
      fun h' => h (S.equivFin.symm.injective (Subtype.ext h'))
    simp [hne, h]

theorem blockExt_one : blockExt S (1 : Matrix (Fin S.card) (Fin S.card) K) = 1 := by
  rw [← blockRes_one (S := S), blockExt_blockRes IsBlockOn.one]

theorem blockExt_mul (N N' : Matrix (Fin S.card) (Fin S.card) K) :
    blockExt S (N * N') = blockExt S N * blockExt S N' := by
  have hb := (isBlockOn_blockExt (S := S) N).mul (isBlockOn_blockExt N')
  rw [← blockExt_blockRes hb, blockRes_mul (isBlockOn_blockExt N), blockRes_blockExt,
    blockRes_blockExt]

theorem blockRes_map_transpose (f : K →+* K) :
    blockRes S ((M.map f)ᵀ) = ((blockRes S M).map f)ᵀ := rfl

theorem blockExt_map_transpose (f : K →+* K) (N : Matrix (Fin S.card) (Fin S.card) K) :
    blockExt S ((N.map f)ᵀ) = ((blockExt S N).map f)ᵀ := by
  rw [← blockExt_blockRes ((isBlockOn_blockExt (S := S) N).map_transpose f),
    blockRes_map_transpose, blockRes_blockExt]

theorem det_eq_det_blockRes (hM : IsBlockOn S M) : M.det = (blockRes S M).det := by
  rw [Matrix.twoBlockTriangular_det M (· ∈ S) fun i hi j hj => by
    have hne : i ≠ j := fun h => hi (h ▸ hj)
    rw [hM i j (Or.inl hi), Matrix.one_apply_ne hne]]
  have h2 : M.toSquareBlockProp (fun i => ¬ i ∈ S) = 1 := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Matrix.toSquareBlockProp_def, Matrix.of_apply]
    rw [hM i j (Or.inl hi)]
    by_cases h : i = j
    · subst h
      simp
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne fun h' => h (congrArg Subtype.val h')]
  have h1 : blockRes S M =
      (M.toSquareBlockProp (· ∈ S)).submatrix S.equivFin.symm S.equivFin.symm := by
    ext a b
    rfl
  rw [h2, Matrix.det_one, mul_one, h1, Matrix.det_submatrix_equiv_self]
  convert rfl

end Block

section Group

variable {n : ℕ} (S : Finset (Fin d))

@[expose] def blockSU : Subgroup ↥(unitarySU 2 n K d) where
  carrier := {x | IsBlockOn S (((x : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K)}
  mul_mem' {x y} hx hy := by
    change IsBlockOn S (((x * y : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K)
    rw [Units.val_mul]
    exact IsBlockOn.mul hx hy
  one_mem' := IsBlockOn.one
  inv_mem' {x} hx := by
    change IsBlockOn S ((((x : GL (Fin d) K))⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
    refine IsBlockOn.of_inv hx ?_ ?_
    · rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    · rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

variable {S} in
theorem mem_blockSU {x : ↥(unitarySU 2 n K d)} :
    x ∈ blockSU S ↔ IsBlockOn S (((x : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K) :=
  Iff.rfl

@[expose] noncomputable def blockExtHom :
    Matrix (Fin S.card) (Fin S.card) K →* Matrix (Fin d) (Fin d) K where
  toFun := blockExt S
  map_one' := blockExt_one
  map_mul' := blockExt_mul

variable (h : UnitaryFieldData 2 n K)

include h in
theorem blockExt_mem (g : ↥(unitarySU 2 n K S.card)) :
    Units.map (blockExtHom S) (g : GL (Fin S.card) K) ∈ unitarySU 2 n K d := by
  obtain ⟨hdet, hu⟩ := (mem_unitarySU_iff h).mp g.2
  rw [mem_unitarySU_iff h]
  refine ⟨?_, ?_⟩
  · change (blockExt S ((g : GL (Fin S.card) K) : Matrix _ _ K)).det = 1
    rw [det_eq_det_blockRes (isBlockOn_blockExt _), blockRes_blockExt, hdet]
  · change ((blockExt S ((g : GL (Fin S.card) K) : Matrix _ _ K)).map h.bar)ᵀ *
      blockExt S ((g : GL (Fin S.card) K) : Matrix _ _ K) = 1
    rw [← blockExt_map_transpose, ← blockExt_mul, hu, blockExt_one]

@[expose] noncomputable def blockExtSU :
    ↥(unitarySU 2 n K S.card) →* ↥(unitarySU 2 n K d) :=
  ((Units.map (blockExtHom S)).comp (unitarySU 2 n K S.card).subtype).codRestrict _
    (blockExt_mem S h)

theorem coe_blockExtSU (g : ↥(unitarySU 2 n K S.card)) :
    (((blockExtSU S h g : ↥(unitarySU 2 n K d)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      blockExt S ((g : GL (Fin S.card) K) : Matrix _ _ K) :=
  rfl

theorem blockExtSU_injective : Function.Injective (blockExtSU S h) := by
  intro g g' hgg
  have h1 := congrArg (fun x : ↥(unitarySU 2 n K d) =>
    blockRes S (((x : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K)) hgg
  simp only [coe_blockExtSU, blockRes_blockExt] at h1
  exact Subtype.ext (Units.ext h1)

theorem range_blockExtSU : (blockExtSU S h).range = blockSU S := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    exact isBlockOn_blockExt _
  · intro hx
    have hx' : IsBlockOn S ((((x : GL (Fin d) K))⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) :=
      (blockSU S).inv_mem hx
    set X : Matrix (Fin d) (Fin d) K := ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) with hX
    set Y : Matrix (Fin d) (Fin d) K :=
      ((((x : GL (Fin d) K))⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) with hY
    have hXY : X * Y = 1 := by rw [hX, hY, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hYX : Y * X = 1 := by rw [hX, hY, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    let g : GL (Fin S.card) K :=
      ⟨blockRes S X, blockRes S Y, by rw [← blockRes_mul hx, hXY, blockRes_one],
        by rw [← blockRes_mul hx', hYX, blockRes_one]⟩
    obtain ⟨hdet, hu⟩ := (mem_unitarySU_iff h).mp x.2
    have hg : g ∈ unitarySU 2 n K S.card := by
      rw [mem_unitarySU_iff h]
      refine ⟨?_, ?_⟩
      · change (blockRes S X).det = 1
        rw [← det_eq_det_blockRes hx]
        exact hdet
      · change ((blockRes S X).map h.bar)ᵀ * blockRes S X = 1
        rw [← blockRes_map_transpose, ← blockRes_mul (hx.map_transpose h.bar)]
        rw [show (X.map h.bar)ᵀ * X = 1 from hu, blockRes_one]
    refine ⟨⟨g, hg⟩, Subtype.ext (Units.ext ?_)⟩
    change blockExt S (blockRes S X) = X
    exact blockExt_blockRes hx

@[expose] noncomputable def blockSUEquiv :
    ↥(unitarySU 2 n K S.card) ≃* ↥(blockSU (K := K) (n := n) S) :=
  (MonoidHom.ofInjective (blockExtSU_injective S h)).trans
    (MulEquiv.subgroupCongr (range_blockExtSU S h))

include h in
theorem isQuasisimple_blockSU [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hS : 3 ≤ S.card)
    (hSq : (S.card, 2 ^ n) ≠ (3, 2)) : CFSG.IsQuasisimple ↥(blockSU (n := n) (K := K) S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (blockSUEquiv S h)
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hK hS hSq).1

end Group

section Centralizer

@[expose] def IsNodeOn (τ : Fin d → Kˣ) (S : Finset (Fin d)) : Prop :=
  (∀ i ∈ S, ∀ j ∈ S, τ i = τ j) ∧ ∀ i ∉ S, ∀ j, j ≠ i → τ j ≠ τ i

theorem entry_eq_zero_of_commute {g : GL (Fin d) K} {τ : Fin d → Kˣ}
    (hg : g * diagHom d τ = diagHom d τ * g) {i j : Fin d} (hij : τ i ≠ τ j) :
    (g : Matrix (Fin d) (Fin d) K) i j = 0 := by
  have h1 := congrFun (congrFun (congrArg (fun x : GL (Fin d) K => (x : Matrix (Fin d) (Fin d) K))
    hg) i) j
  simp only [Units.val_mul, coe_diagHom, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  have h2 : ((g : Matrix (Fin d) (Fin d) K) i j) * (((τ j : Kˣ) : K) - (τ i : K)) = 0 := by
    rw [mul_sub, h1]
    ring
  rcases mul_eq_zero.mp h2 with h | h
  · exact h
  · exact absurd (Units.ext (sub_eq_zero.mp h)).symm hij

@[expose] def DiagAt (i : Fin d) (A : Matrix (Fin d) (Fin d) K) : Prop :=
  (∀ j, j ≠ i → A i j = 0) ∧ ∀ j, j ≠ i → A j i = 0

theorem DiagAt.mul_apply {i : Fin d} {A B : Matrix (Fin d) (Fin d) K} (hA : DiagAt i A)
    (_hB : DiagAt i B) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by rw [hA.1 k hk, zero_mul])
    (fun h => absurd (Finset.mem_univ i) h)]

theorem DiagAt.mul {i : Fin d} {A B : Matrix (Fin d) (Fin d) K} (hA : DiagAt i A)
    (hB : DiagAt i B) : DiagAt i (A * B) := by
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by rw [hA.1 k hk, zero_mul])
      (fun h => absurd (Finset.mem_univ i) h), hB.1 j hj, mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i (fun k _ hk => by rw [hB.2 k hk, mul_zero])
      (fun h => absurd (Finset.mem_univ i) h), hA.2 j hj, zero_mul]

variable {n : ℕ} {S : Finset (Fin d)} {τ : Fin d → Kˣ}

theorem diagAt_of_mem_centralizer (hτ : IsNodeOn τ S) {t g : ↥(unitarySU 2 n K d)}
    (ht : (t : GL (Fin d) K) = diagHom d τ) (hg : g ∈ Subgroup.centralizer {t}) {i : Fin d}
    (hi : i ∉ S) : DiagAt i (((g : GL (Fin d) K)) : Matrix (Fin d) (Fin d) K) := by
  have hc : (g : GL (Fin d) K) * diagHom d τ = diagHom d τ * g := by
    rw [← ht]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hg)
  exact ⟨fun j hj => entry_eq_zero_of_commute hc (hτ.2 i hi j hj).symm,
    fun j hj => entry_eq_zero_of_commute hc (hτ.2 i hi j hj)⟩

theorem commutator_mem_blockSU (hτ : IsNodeOn τ S) {t : ↥(unitarySU 2 n K d)}
    (ht : (t : GL (Fin d) K) = diagHom d τ) {g g' : ↥(unitarySU 2 n K d)}
    (hg : g ∈ Subgroup.centralizer {t}) (hg' : g' ∈ Subgroup.centralizer {t}) :
    g * g' * g⁻¹ * g'⁻¹ ∈ blockSU S := by
  have key : ∀ i ∉ S, DiagAt i
      ((((g * g' * g⁻¹ * g'⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K)) :
        Matrix (Fin d) (Fin d) K) ∧
      ((((g * g' * g⁻¹ * g'⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K)) :
        Matrix (Fin d) (Fin d) K) i i = 1 := by
    intro i hi
    have d1 := diagAt_of_mem_centralizer hτ ht hg hi
    have d2 := diagAt_of_mem_centralizer hτ ht hg' hi
    have d3 := diagAt_of_mem_centralizer hτ ht ((Subgroup.centralizer {t}).inv_mem hg) hi
    have d4 := diagAt_of_mem_centralizer hτ ht ((Subgroup.centralizer {t}).inv_mem hg') hi
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul] at d3 d4 ⊢
    refine ⟨((d1.mul d2).mul d3).mul d4, ?_⟩
    rw [(((d1.mul d2).mul d3)).mul_apply d4, ((d1.mul d2)).mul_apply d3, d1.mul_apply d2]
    have e1 : ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i *
        ((((g : GL (Fin d) K))⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i = 1 := by
      rw [← d1.mul_apply d3, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    have e2 : ((g' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i *
        ((((g' : GL (Fin d) K))⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i = 1 := by
      rw [← d2.mul_apply d4, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    linear_combination (((g' : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i *
        ((((g' : GL (Fin d) K))⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i i) * e1 + e2
  rintro i j (hi | hj)
  · obtain ⟨hd, h1⟩ := key i hi
    by_cases hij : j = i
    · subst hij
      rw [h1, Matrix.one_apply_eq]
    · rw [hd.1 j hij, Matrix.one_apply_ne (Ne.symm hij)]
  · obtain ⟨hd, h1⟩ := key j hj
    by_cases hij : i = j
    · subst hij
      rw [h1, Matrix.one_apply_eq]
    · rw [hd.2 i hij, Matrix.one_apply_ne hij]

theorem diagHom_mul_comm_of_isBlockOn {σ : Fin d → Kˣ} (hσ : ∀ i ∈ S, ∀ j ∈ S, σ i = σ j)
    {X : GL (Fin d) K} (hX : IsBlockOn S (X : Matrix (Fin d) (Fin d) K)) :
    diagHom d σ * X = X * diagHom d σ := by
  apply Units.ext
  ext i j
  simp only [Units.val_mul, coe_diagHom, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : i ∈ S ∧ j ∈ S
  · rw [hσ i h.1 j h.2, mul_comm]
  · have h' : i ∉ S ∨ j ∉ S := by tauto
    rw [hX i j h']
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, mul_one, one_mul]
    · rw [Matrix.one_apply_ne hij, mul_zero, zero_mul]

theorem blockSU_le_centralizer (hτ : ∀ i ∈ S, ∀ j ∈ S, τ i = τ j) {t : ↥(unitarySU 2 n K d)}
    (ht : (t : GL (Fin d) K) = diagHom d τ) : blockSU S ≤ Subgroup.centralizer {t} := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ht]
  exact (diagHom_mul_comm_of_isBlockOn hτ hx).symm

variable (h : UnitaryFieldData 2 n K)

include h in
theorem permGL_swap_mem (i j : Fin d) :
    (permGL (Equiv.swap i j) : GL (Fin d) K) ∈ unitarySU 2 n K d := by
  have : CharP K 2 := h.charP
  rw [mem_unitarySU_iff h]
  refine ⟨?_, permGL_unitary h _⟩
  rw [det_permGL]
  by_cases hij : i = j
  · subst hij
    simp
  · rw [Equiv.Perm.sign_swap hij]
    have h2K : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one]
    linear_combination -h2K

theorem permGL_apply (σ : Equiv.Perm (Fin d)) (i j : Fin d) :
    ((permGL σ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) i j = if σ⁻¹ i = j then 1 else 0 := by
  show (Equiv.Perm.permMatrix K σ⁻¹) i j = _
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
  simp

theorem isBlockOn_permGL_swap {i j : Fin d} (hi : i ∈ S) (hj : j ∈ S) :
    IsBlockOn S ((permGL (Equiv.swap i j) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
  intro a b hab
  rw [permGL_apply, Equiv.swap_inv]
  rcases hab with ha | hb
  · have hai : a ≠ i := fun h' => ha (h' ▸ hi)
    have haj : a ≠ j := fun h' => ha (h' ▸ hj)
    rw [Equiv.swap_apply_of_ne_of_ne hai haj, Matrix.one_apply]
  · have hbi : b ≠ i := fun h' => hb (h' ▸ hi)
    have hbj : b ≠ j := fun h' => hb (h' ▸ hj)
    have hiff : Equiv.swap i j a = b ↔ a = b := by
      constructor
      · intro h'
        have := congrArg (Equiv.swap i j) h'
        rwa [Equiv.swap_apply_self, Equiv.swap_apply_of_ne_of_ne hbi hbj] at this
      · rintro rfl
        exact Equiv.swap_apply_of_ne_of_ne hbi hbj
    simp only [hiff, Matrix.one_apply]

include h in
theorem commute_blockSU_iff {s : ↥(unitarySU 2 n K d)} {σ : Fin d → Kˣ}
    (hs : (s : GL (Fin d) K) = diagHom d σ) :
    (∀ x ∈ blockSU S, s * x = x * s) ↔ ∀ i ∈ S, ∀ j ∈ S, σ i = σ j := by
  constructor
  · intro hc i hi j hj
    have hw := hc ⟨_, permGL_swap_mem h i j⟩ (isBlockOn_permGL_swap hi hj)
    have hw' : (permGL (Equiv.swap i j) : GL (Fin d) K) * diagHom d σ =
        diagHom d σ * permGL (Equiv.swap i j) := by
      rw [← hs]
      exact (congrArg Subtype.val hw).symm
    have h1 := permGL_mul_diagHom_mul_inv (K := K) (Equiv.swap i j) σ
    rw [hw', mul_inv_cancel_right] at h1
    have h2 := congrFun (diagHom_injective d h1) j
    rw [Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_right] at h2
    exact h2.symm
  · intro hσ x hx
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hs]
    exact diagHom_mul_comm_of_isBlockOn hσ hx

end Centralizer

end TableBUE

end CFSG.StandardType
