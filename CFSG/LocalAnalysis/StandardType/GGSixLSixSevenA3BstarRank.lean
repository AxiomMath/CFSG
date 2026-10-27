module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordContrary
public import CFSG.LocalAnalysis.StandardType.GGTableBRank

public section

open Polynomial Module Matrix

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Multiplicative

namespace CoordSL

section Unipotent

variable {K : Type} [Field K] [CharP K 2] {n e s r : ℕ}

@[expose] def blockEmb (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r) (i j : Fin s)
    (X : Matrix (Fin e) (Fin e) K) : Matrix (Fin n) (Fin n) K :=
  (Matrix.fromBlocks (Matrix.of fun (x y : Fin e × Fin s) =>
    if x.2 = i ∧ y.2 = j then X x.1 y.1 else 0) 0 0 0).submatrix ε ε

section BlockEmb

variable (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r) {i j : Fin s}

theorem blockEmb_add (X Y : Matrix (Fin e) (Fin e) K) :
    blockEmb ε i j (X + Y) = blockEmb ε i j X + blockEmb ε i j Y := by
  have hF : (Matrix.fromBlocks (Matrix.of fun x y : Fin e × Fin s =>
      if x.2 = i ∧ y.2 = j then (X + Y) x.1 y.1 else 0) 0 0 0 :
          Matrix ((Fin e × Fin s) ⊕ Fin r) ((Fin e × Fin s) ⊕ Fin r) K) =
      Matrix.fromBlocks (Matrix.of fun x y : Fin e × Fin s =>
        if x.2 = i ∧ y.2 = j then X x.1 y.1 else 0) 0 0 0 +
      Matrix.fromBlocks (Matrix.of fun x y : Fin e × Fin s =>
        if x.2 = i ∧ y.2 = j then Y x.1 y.1 else 0) 0 0 0 := by
    rw [Matrix.fromBlocks_add]
    congr 1
    · ext x y
      by_cases h : x.2 = i ∧ y.2 = j <;> simp [h, Matrix.add_apply]
    · simp
    · simp
    · simp
  rw [blockEmb, blockEmb, blockEmb, hF, Matrix.submatrix_add]
  simp

theorem blockEmb_zero : blockEmb ε i j (0 : Matrix (Fin e) (Fin e) K) = 0 := by
  have h : (Matrix.of fun x y : Fin e × Fin s =>
      if x.2 = i ∧ y.2 = j then (0 : Matrix (Fin e) (Fin e) K) x.1 y.1 else 0) = 0 := by
    ext x y
    by_cases h : x.2 = i ∧ y.2 = j <;> simp [h]
  rw [blockEmb, h]
  simp

theorem blockEmb_mul_blockEmb (hij : i ≠ j) (X Y : Matrix (Fin e) (Fin e) K) :
    blockEmb ε i j X * blockEmb ε i j Y = 0 := by
  have hAB : (Matrix.of fun x y : Fin e × Fin s => if x.2 = i ∧ y.2 = j then X x.1 y.1 else 0) *
      (Matrix.of fun x y : Fin e × Fin s => if x.2 = i ∧ y.2 = j then Y x.1 y.1 else 0) = 0 := by
    ext ⟨a, l⟩ ⟨b, m⟩
    rw [Matrix.mul_apply, Matrix.zero_apply]
    apply Finset.sum_eq_zero
    rintro ⟨c, w⟩ -
    by_cases hw : w = j
    · subst hw
      simp [Matrix.of_apply, hij.symm]
    · simp [Matrix.of_apply, hw]
  rw [blockEmb, blockEmb, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, hAB]
  simp

theorem nsMat_mul_blockEmb {C : Matrix (Fin e) (Fin e) K} (k : Fin s → ℕ)
    (X : Matrix (Fin e) (Fin e) K) :
    SLNS.nsMat ε C k * blockEmb ε i j X = blockEmb ε i j (C ^ k i * X) := by
  have h : (Matrix.blockDiagonal fun i => C ^ k i) *
      (Matrix.of fun x y : Fin e × Fin s => if x.2 = i ∧ y.2 = j then X x.1 y.1 else 0)
      = Matrix.of fun x y : Fin e × Fin s =>
          if x.2 = i ∧ y.2 = j then (C ^ k i * X) x.1 y.1 else 0 := by
    ext ⟨a, l⟩ ⟨b, m⟩
    rw [Matrix.mul_apply, Fintype.sum_prod_type_right]
    by_cases hlm : l = i ∧ m = j
    · rw [Matrix.of_apply, if_pos hlm]
      have hsum : (∑ w, ∑ c, Matrix.blockDiagonal (fun i => C ^ k i) (a, l) (c, w) *
          (Matrix.of fun x y : Fin e × Fin s =>
            if x.2 = i ∧ y.2 = j then X x.1 y.1 else 0) (c, w) (b, m)) =
          ∑ c, Matrix.blockDiagonal (fun i => C ^ k i) (a, l) (c, l) *
            (Matrix.of fun x y : Fin e × Fin s =>
              if x.2 = i ∧ y.2 = j then X x.1 y.1 else 0) (c, l) (b, m) := by
        apply Fintype.sum_eq_single l
        intro w hw
        apply Finset.sum_eq_zero
        intro c _
        rw [Matrix.blockDiagonal_apply, if_neg hw.symm, zero_mul]
      rw [hsum, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Matrix.blockDiagonal_apply, if_pos rfl, Matrix.of_apply, if_pos hlm, hlm.1]
    · rw [Matrix.of_apply, if_neg hlm]
      apply Finset.sum_eq_zero
      intro w _
      apply Finset.sum_eq_zero
      intro c _
      by_cases hw : l = w
      · rw [Matrix.blockDiagonal_apply, if_pos hw, Matrix.of_apply, ← hw, if_neg hlm, mul_zero]
      · rw [Matrix.blockDiagonal_apply, if_neg hw, zero_mul]
  rw [blockEmb, SLNS.nsMat, SLNS.nsCore, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
    h]
  simp [blockEmb]

theorem blockEmb_mul_nsMat {C : Matrix (Fin e) (Fin e) K} (k : Fin s → ℕ)
    (X : Matrix (Fin e) (Fin e) K) :
    blockEmb ε i j X * SLNS.nsMat ε C k = blockEmb ε i j (X * C ^ k j) := by
  have h : (Matrix.of fun x y : Fin e × Fin s => if x.2 = i ∧ y.2 = j then X x.1 y.1 else 0) *
      (Matrix.blockDiagonal fun i => C ^ k i)
      = Matrix.of fun x y : Fin e × Fin s =>
          if x.2 = i ∧ y.2 = j then (X * C ^ k j) x.1 y.1 else 0 := by
    ext ⟨a, l⟩ ⟨b, m⟩
    rw [Matrix.mul_apply, Fintype.sum_prod_type_right]
    by_cases hlm : l = i ∧ m = j
    · rw [Matrix.of_apply, if_pos hlm]
      have hsum : (∑ w, ∑ c, (Matrix.of fun x y : Fin e × Fin s =>
            if x.2 = i ∧ y.2 = j then X x.1 y.1 else 0) (a, l) (c, w) *
            Matrix.blockDiagonal (fun i => C ^ k i) (c, w) (b, m)) =
          ∑ c, (Matrix.of fun x y : Fin e × Fin s =>
              if x.2 = i ∧ y.2 = j then X x.1 y.1 else 0) (a, l) (c, m) *
              Matrix.blockDiagonal (fun i => C ^ k i) (c, m) (b, m) := by
        apply Fintype.sum_eq_single m
        intro w hw
        apply Finset.sum_eq_zero
        intro c _
        rw [Matrix.blockDiagonal_apply, if_neg hw, mul_zero]
      rw [hsum, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Matrix.of_apply, if_pos hlm, Matrix.blockDiagonal_apply, if_pos rfl, hlm.2]
    · rw [Matrix.of_apply, if_neg hlm]
      apply Finset.sum_eq_zero
      intro w _
      apply Finset.sum_eq_zero
      intro c _
      by_cases hw : m = w
      · rw [Matrix.of_apply, ← hw, if_neg hlm, zero_mul]
      · rw [Matrix.blockDiagonal_apply, if_neg (Ne.symm hw), mul_zero]
  rw [blockEmb, SLNS.nsMat, SLNS.nsCore, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply,
    h]
  simp [blockEmb]

theorem blockEmb_apply (a b : Fin e) (X : Matrix (Fin e) (Fin e) K) :
    blockEmb ε i j X (ε.symm (Sum.inl (a, i))) (ε.symm (Sum.inl (b, j))) = X a b := by
  rw [blockEmb, Matrix.submatrix_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    Matrix.fromBlocks_apply₁₁, Matrix.of_apply, if_pos ⟨rfl, rfl⟩]

theorem det_one_add_blockEmb (hij : i ≠ j) (X : Matrix (Fin e) (Fin e) K) :
    (1 + blockEmb ε i j X).det = 1 := by
  set N := blockEmb ε i j X with hN
  have hNN : N * N = 0 := by rw [hN]; exact blockEmb_mul_blockEmb ε hij X X
  have h2 : N + N = 0 := by
    ext a b
    exact CharTwo.add_self_eq_zero (N a b)
  have hsq : (1 + N) * (1 + N) = 1 := by
    rw [mul_add, mul_one, add_mul, one_mul, hNN, add_zero, add_assoc, h2, add_zero]
  have hdet : (1 + N).det * (1 + N).det = 1 := by
    rw [← Matrix.det_mul, hsq, Matrix.det_one]
  have hsq2 : ((1 + N).det + 1) ^ 2 = 0 := by
    rw [CharTwo.add_sq, one_pow, pow_two, hdet, CharTwo.add_self_eq_zero]
  exact CharTwo.add_eq_zero.mp (sq_eq_zero_iff.mp hsq2)

@[expose] def unipSL (hij : i ≠ j) (X : Matrix (Fin e) (Fin e) K) :
    Matrix.SpecialLinearGroup (Fin n) K :=
  ⟨1 + blockEmb ε i j X, det_one_add_blockEmb ε hij X⟩

theorem unipSL_mul (hij : i ≠ j) (X Y : Matrix (Fin e) (Fin e) K) :
    unipSL ε hij X * unipSL ε hij Y = unipSL ε hij (X + Y) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  change (1 + blockEmb ε i j X) * (1 + blockEmb ε i j Y) = 1 + blockEmb ε i j (X + Y)
  rw [mul_add, mul_one, add_mul, one_mul, blockEmb_mul_blockEmb ε hij X Y, add_zero,
    add_assoc, ← blockEmb_add]

theorem unipSL_zero (hij : i ≠ j) : unipSL ε hij (0 : Matrix (Fin e) (Fin e) K) = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one]
  change 1 + blockEmb ε i j 0 = 1
  rw [blockEmb_zero, add_zero]

variable (K) in
@[expose] def unipHom (hij : i ≠ j) :
    Multiplicative (Matrix (Fin e) (Fin e) K) →* Matrix.SpecialLinearGroup (Fin n) K where
  toFun X := unipSL ε hij (Multiplicative.toAdd X)
  map_one' := unipSL_zero ε hij
  map_mul' X Y := by
    simp only [toAdd_mul]
    exact (unipSL_mul ε hij _ _).symm

variable (K) in
@[expose] def unipGroup (hij : i ≠ j) : Subgroup (Matrix.SpecialLinearGroup (Fin n) K) :=
  (unipHom K ε hij).range

theorem unipSL_mem_unipGroup (hij : i ≠ j) (X : Matrix (Fin e) (Fin e) K) :
    unipSL ε hij X ∈ unipGroup K ε hij :=
  ⟨Multiplicative.ofAdd X, rfl⟩

theorem isPGroup_two_unipGroup (hij : i ≠ j) : IsPGroup 2 (unipGroup K ε hij) := by
  intro g
  obtain ⟨X, hX⟩ := MonoidHom.mem_range.mp g.2
  refine ⟨1, ?_⟩
  change g ^ 2 = 1
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hX, pow_two, ← map_mul]
  have hXX : X * X = 1 := by
    apply Multiplicative.toAdd.injective
    ext a b
    simp [toAdd_mul, CharTwo.add_self_eq_zero]
  rw [hXX, map_one]

theorem unipSL_single_not_mem_center (hij : i ≠ j) (he : 0 < e) :
    unipSL ε hij (Matrix.single ⟨0, he⟩ ⟨0, he⟩ 1) ∉
      Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K) := by
  intro hmem
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hmem
  set u := ε.symm (Sum.inl ((⟨0, he⟩ : Fin e), i)) with hu
  set v := ε.symm (Sum.inl ((⟨0, he⟩ : Fin e), j)) with hv
  have huv : u ≠ v := by
    intro huv
    rw [hu, hv] at huv
    have h1 := ε.symm.injective huv
    simp only [Sum.inl.injEq, Prod.mk.injEq] at h1
    exact hij h1.2
  have hzero : (Matrix.scalar (Fin n) r) u v = 0 := by
    rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ huv]
  have hone : (↑(unipSL ε hij (Matrix.single ⟨0, he⟩ ⟨0, he⟩ (1 : K))) :
      Matrix (Fin n) (Fin n) K) u v = 1 := by
    change (1 + blockEmb ε i j (Matrix.single ⟨0, he⟩ ⟨0, he⟩ (1 : K))) u v = 1
    rw [Matrix.add_apply, Matrix.one_apply_ne huv, zero_add]
    rw [blockEmb_apply, Matrix.single_apply_same]
  have hcon := congrArg (fun A : Matrix (Fin n) (Fin n) K => A u v) hr
  rw [hzero, hone] at hcon
  exact zero_ne_one hcon

theorem nsSL_mul_unipSL (hij : i ≠ j) {C : Matrix (Fin e) (Fin e) K} (hC : C.det = 1)
    (k : Fin s → ℕ) (X Y : Matrix (Fin e) (Fin e) K) (h : Y * C ^ k j = C ^ k i * X) :
    SLNS.nsSL ε hC k * unipSL ε hij X = unipSL ε hij Y * SLNS.nsSL ε hC k := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  change SLNS.nsMat ε C k * (1 + blockEmb ε i j X) =
    (1 + blockEmb ε i j Y) * SLNS.nsMat ε C k
  rw [mul_add, mul_one, add_mul, one_mul, nsMat_mul_blockEmb ε k X, blockEmb_mul_nsMat ε k Y, h]

theorem nsSL_mem_normalizer_unipGroup (hij : i ≠ j) {C : Matrix (Fin e) (Fin e) K}
    (hC : C.det = 1) (k : Fin s → ℕ) :
    SLNS.nsSL ε hC k ∈
      Subgroup.normalizer (unipGroup K ε hij : Set (Matrix.SpecialLinearGroup (Fin n) K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨X, hX⟩ := MonoidHom.mem_range.mp hh
    set Z := Multiplicative.toAdd X with hZ
    set Y := C ^ k i * Z * (C ^ k j)⁻¹ with hY
    have hunitj : IsUnit (C ^ k j).det := by
      rw [Matrix.det_pow, hC, one_pow]; exact isUnit_one
    have hYC : Y * C ^ k j = C ^ k i * Z := by
      rw [hY, mul_assoc, Matrix.nonsing_inv_mul _ hunitj, mul_one]
    have hcomm : SLNS.nsSL ε hC k * unipSL ε hij Z = unipSL ε hij Y * SLNS.nsSL ε hC k :=
      nsSL_mul_unipSL ε hij hC k Z Y hYC
    rw [← hX]
    rw [show unipHom K ε hij X = unipSL ε hij Z from by rw [hZ]; rfl]
    rw [show SLNS.nsSL ε hC k * unipSL ε hij Z * (SLNS.nsSL ε hC k)⁻¹ = unipSL ε hij Y from by
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]]
    exact unipSL_mem_unipGroup ε hij Y
  · intro hh
    obtain ⟨X, hX⟩ := MonoidHom.mem_range.mp hh
    set Z := Multiplicative.toAdd X with hZ
    set W := (C ^ k i)⁻¹ * Z * C ^ k j with hW
    have huniti : IsUnit (C ^ k i).det := by
      rw [Matrix.det_pow, hC, one_pow]; exact isUnit_one
    have hWC : Z * C ^ k j = C ^ k i * W := by
      rw [hW, ← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ huniti, one_mul]
    have hcomm : SLNS.nsSL ε hC k * unipSL ε hij W = unipSL ε hij Z * SLNS.nsSL ε hC k :=
      nsSL_mul_unipSL ε hij hC k W Z hWC
    rw [show h = (SLNS.nsSL ε hC k)⁻¹ * (SLNS.nsSL ε hC k * h * (SLNS.nsSL ε hC k)⁻¹) *
        SLNS.nsSL ε hC k from by group, ← hX,
      show unipHom K ε hij X = unipSL ε hij Z from by rw [hZ]; rfl,
      show (SLNS.nsSL ε hC k)⁻¹ * unipSL ε hij Z * SLNS.nsSL ε hC k = unipSL ε hij W from by
        rw [mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]]
    exact unipSL_mem_unipGroup ε hij W

end BlockEmb

theorem exists_isPGroup_two_normalized_by_nsSL (he : 0 < e) (hs : 2 ≤ s)
    (ε : Fin n ≃ (Fin e × Fin s) ⊕ Fin r) {C : Matrix (Fin e) (Fin e) K} (hC : C.det = 1) :
    ∃ U : Subgroup (Matrix.SpecialLinearGroup (Fin n) K), IsPGroup 2 U ∧
      (∃ u ∈ U, u ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K)) ∧
      ∀ k : Fin s → ℕ, SLNS.nsSL ε hC k ∈
        Subgroup.normalizer (U : Set (Matrix.SpecialLinearGroup (Fin n) K)) := by
  have hij : (⟨0, by omega⟩ : Fin s) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  exact ⟨unipGroup K ε hij, isPGroup_two_unipGroup ε hij,
    ⟨_, unipSL_mem_unipGroup ε hij _, unipSL_single_not_mem_center ε hij he⟩,
    fun k => nsSL_mem_normalizer_unipGroup ε hij hC k⟩

end Unipotent

section Frame

variable {G : Type} [Group G] {K : Type} [Field K] [CharP K 2] {g : K[X]} [Fact (Irreducible g)]
  {n s r p : ℕ} [NeZero p] {ψ : Matrix.SpecialLinearGroup (Fin n) K →* G}

theorem exists_isPGroup_two_le_range_normalized_by_frameHom
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (A₀ : Matrix.SpecialLinearGroup (Fin n) K)
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (hC : (rootMat g).det = 1)
    (hCp : rootMat g ^ p = 1) (hs : 2 ≤ s) :
    ∃ Q : Subgroup G, Q ≤ ψ.range ∧ Q ≠ ⊥ ∧ IsPGroup 2 Q ∧
      (frameHom ψ A₀ ε hC hCp).range ≤ Subgroup.normalizer (Q : Set G) := by
  obtain ⟨U, hU2, ⟨u, huU, hu⟩, hN⟩ := exists_isPGroup_two_normalized_by_nsSL
    (rootPB_dim_pos g) hs ε hC
  refine ⟨U.map (SLRep.ggFrame ψ A₀), ?_, ?_, hU2.map _, ?_⟩
  · rintro _ ⟨v, -, rfl⟩
    rw [← SLRep.range_ggFrame ψ A₀]
    exact ⟨v, rfl⟩
  · intro hbot
    apply hu
    have h1 : SLRep.ggFrame ψ A₀ u ∈ (U.map (SLRep.ggFrame ψ A₀)) := ⟨u, huU, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact SLRep.ker_ggFrame_le hker A₀ h1
  · rintro _ ⟨a, rfl⟩
    exact Subgroup.le_normalizer_map (SLRep.ggFrame ψ A₀)
      ⟨SLNS.nsSL ε hC fun i => (toAdd a i).val, hN _, (frameHom_eq_ggFrame (toAdd a)).symm⟩

theorem exists_isPGroup_two_normalized_by_frameHom
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) K))
    (A₀ : Matrix.SpecialLinearGroup (Fin n) K)
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (hC : (rootMat g).det = 1)
    (hCp : rootMat g ^ p = 1) (hs : 2 ≤ s) :
    ∃ Q : Subgroup G, Q ≠ ⊥ ∧ IsPGroup 2 Q ∧
      (frameHom ψ A₀ ε hC hCp).range ≤ Subgroup.normalizer (Q : Set G) := by
  obtain ⟨Q, -, hQ1, hQ2, hQN⟩ :=
    exists_isPGroup_two_le_range_normalized_by_frameHom hker A₀ ε hC hCp hs
  exact ⟨Q, hQ1, hQ2, hQN⟩

end Frame

end CoordSL

section Config

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
  {ψ : U →* G}

theorem GGSixCtxV2.eq_bstar_of_twoLocal (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) {Q : Subgroup G}
    (hQ1 : Q ≠ ⊥) (hQ2 : IsPGroup 2 Q) (hBs : Bs ≤ Subgroup.normalizer (Q : Set G)) :
    B = Bs := by
  have hB : Nat.card B = p ^ LargeEvenTwoLocalRank p G := h.sstar.1.2.1
  have hle : Nat.card Bs ≤ p ^ LargeEvenTwoLocalRank p G :=
    TableB.card_le_of_twoLocal h.prime ⟨Q, hQ1, hQ2, rfl⟩ hBs h.bstar.2.1
  exact Subgroup.eq_of_le_of_card_ge h.bstar.1 (hB ▸ hle)

end Config

end CFSG.StandardType
