module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality

namespace CFSG
end CFSG
open CFSG

/-!
# The projective-line action and upper root group of `PSL₂`

This file packages the geometric objects used in Dieudonne's proof of the
automorphism theorem for `PSL₂`: the natural action on the projective line,
the standard Borel stabilizer, and its upper-unipotent root subgroup.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix Projectivization
open scoped LinearAlgebra.Projectivization MatrixGroups

universe u

/-- The projective line over `K`. -/
public abbrev PSL2ProjectiveLine
    (K : Type u) [Field K] := ℙ K (Fin 2 → K)

public theorem psl2_e0_ne_zero
    {K : Type u} [Field K] : (![1, 0] : Fin 2 → K) ≠ 0 := by
  intro h
  simpa using congrFun h 0

public theorem psl2_e1_ne_zero
    {K : Type u} [Field K] : (![0, 1] : Fin 2 → K) ≠ 0 := by
  intro h
  simpa using congrFun h 1

/-- The point at infinity `⟨(1,0)⟩`. -/
@[expose]
public def psl2ProjectiveInfinity
    (K : Type u) [Field K] : PSL2ProjectiveLine K :=
  Projectivization.mk K ![1, 0] psl2_e0_ne_zero

/-- The zero point `⟨(0,1)⟩`. -/
@[expose]
public def psl2ProjectiveZero
    (K : Type u) [Field K] : PSL2ProjectiveLine K :=
  Projectivization.mk K ![0, 1] psl2_e1_ne_zero

private theorem sl2_smul_eq_mulVec
    {K : Type u} [Field K]
    (A : SL(2, K)) (v : Fin 2 → K) : A • v = A.val *ᵥ v := rfl

private theorem sl2_smul_e0
    {K : Type u} [Field K] (A : SL(2, K)) :
    A • (![1, 0] : Fin 2 → K) = ![A.val 0 0, A.val 1 0] := by
  ext i
  fin_cases i <;>
    simp [sl2_smul_eq_mulVec, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail]

private theorem sl2_smul_e1
    {K : Type u} [Field K] (A : SL(2, K)) :
    A • (![0, 1] : Fin 2 → K) = ![A.val 0 1, A.val 1 1] := by
  ext i
  fin_cases i <;>
    simp [sl2_smul_eq_mulVec, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail]

/-- An `SL₂` matrix fixes infinity exactly when its lower-left entry is zero. -/
public theorem sl2_mem_stabilizer_infinity_iff
    {K : Type u} [Field K] (A : SL(2, K)) :
    A ∈ MulAction.stabilizer (SL(2, K)) (psl2ProjectiveInfinity K) ↔
      A.val 1 0 = 0 := by
  rw [MulAction.mem_stabilizer_iff, psl2ProjectiveInfinity,
    Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
  constructor
  · rintro ⟨a, ha⟩
    have h1 := congrFun ha 1
    rw [sl2_smul_e0] at h1
    simpa [Units.smul_def] using h1.symm
  · intro h
    have hdet : A.val 0 0 * A.val 1 1 = 1 := by
      have hA := A.property
      rw [Matrix.det_fin_two, h] at hA
      simpa using hA
    have hne : A.val 0 0 ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hdet
      exact zero_ne_one hdet
    refine ⟨Units.mk0 (A.val 0 0) hne, ?_⟩
    rw [sl2_smul_e0]
    ext i
    fin_cases i <;> simp [Units.smul_def, h]

/-- An `SL₂` matrix fixes zero exactly when its upper-right entry is zero. -/
public theorem sl2_mem_stabilizer_zero_iff
    {K : Type u} [Field K] (A : SL(2, K)) :
    A ∈ MulAction.stabilizer (SL(2, K)) (psl2ProjectiveZero K) ↔
      A.val 0 1 = 0 := by
  rw [MulAction.mem_stabilizer_iff, psl2ProjectiveZero,
    Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
  constructor
  · rintro ⟨a, ha⟩
    have h0 := congrFun ha 0
    rw [sl2_smul_e1] at h0
    simpa [Units.smul_def] using h0.symm
  · intro h
    have hdet : A.val 0 0 * A.val 1 1 = 1 := by
      have hA := A.property
      rw [Matrix.det_fin_two, h] at hA
      simpa using hA
    have hne : A.val 1 1 ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hdet
      exact zero_ne_one hdet
    refine ⟨Units.mk0 (A.val 1 1) hne, ?_⟩
    rw [sl2_smul_e1]
    ext i
    fin_cases i <;> simp [Units.smul_def, h]

/-- The upper-triangular Borel subgroup of `SL₂`. -/
@[expose]
public def sl2Borel
    (K : Type u) [Field K] : Subgroup (SL(2, K)) :=
  MulAction.stabilizer (SL(2, K)) (psl2ProjectiveInfinity K)

/-- The upper-unipotent matrix with parameter `x`. -/
@[expose]
public def sl2UpperUnipotent
    {K : Type u} [Field K] (x : K) : SL(2, K) :=
  ⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[simp]
public theorem sl2UpperUnipotent_zero
    {K : Type u} [Field K] : sl2UpperUnipotent (0 : K) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2UpperUnipotent]

set_option backward.isDefEq.respectTransparency false in
@[simp]
public theorem sl2UpperUnipotent_mul
    {K : Type u} [Field K] (x y : K) :
    sl2UpperUnipotent x * sl2UpperUnipotent y =
      sl2UpperUnipotent (x + y) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2UpperUnipotent, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

@[simp]
public theorem sl2UpperUnipotent_inv
    {K : Type u} [Field K] (x : K) :
    (sl2UpperUnipotent x)⁻¹ = sl2UpperUnipotent (-x) := by
  apply inv_eq_of_mul_eq_one_left
  rw [sl2UpperUnipotent_mul]
  simp

/-- The additive field, embedded in the upper-unipotent subgroup of `SL₂`. -/
@[expose]
public def sl2UpperUnipotentHom
    (K : Type u) [Field K] : Multiplicative K →* SL(2, K) where
  toFun x := sl2UpperUnipotent x.toAdd
  map_one' := sl2UpperUnipotent_zero
  map_mul' x y := by
    simp [sl2UpperUnipotent_mul]

public theorem sl2UpperUnipotentHom_injective
    {K : Type u} [Field K] :
    Function.Injective (sl2UpperUnipotentHom K) := by
  intro x y hxy
  have h := congrFun (congrFun (congrArg Subtype.val hxy) 0) 1
  apply Multiplicative.ext
  exact h

/-- The upper-unipotent subgroup of `SL₂`. -/
@[expose]
public def sl2UpperUnipotentSubgroup
    (K : Type u) [Field K] : Subgroup (SL(2, K)) :=
  (sl2UpperUnipotentHom K).range

public theorem mem_sl2UpperUnipotentSubgroup_iff
    {K : Type u} [Field K] (A : SL(2, K)) :
    A ∈ sl2UpperUnipotentSubgroup K ↔
      ∃ x : K, A = sl2UpperUnipotent x := by
  simp [sl2UpperUnipotentSubgroup, MonoidHom.mem_range,
    sl2UpperUnipotentHom]
  exact ⟨fun ⟨x, hx⟩ => ⟨x, hx.symm⟩,
    fun ⟨x, hx⟩ => ⟨x, hx.symm⟩⟩

public theorem sl2UpperUnipotent_le_borel
    {K : Type u} [Field K] :
    sl2UpperUnipotentSubgroup K ≤ sl2Borel K := by
  rintro A hA
  rw [mem_sl2UpperUnipotentSubgroup_iff] at hA
  obtain ⟨x, rfl⟩ := hA
  rw [sl2Borel, sl2_mem_stabilizer_infinity_iff]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Conjugation inside the `SL₂` Borel scales the upper-unipotent parameter
by a square. -/
public theorem sl2Borel_conj_upperUnipotent
    {K : Type u} [Field K]
    {A : SL(2, K)} (hA : A ∈ sl2Borel K) (x : K) :
    A * sl2UpperUnipotent x * A⁻¹ =
      sl2UpperUnipotent (A.val 0 0 ^ 2 * x) := by
  have h10 : A.val 1 0 = 0 :=
    (sl2_mem_stabilizer_infinity_iff A).mp hA
  have hdet : A.val 0 0 * A.val 1 1 = 1 := by
    have h := A.property
    rw [Matrix.det_fin_two, h10] at h
    simpa using h
  have hne : A.val 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
  have h11 : A.val 1 1 = (A.val 0 0)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hdet)
  have key :
      A * sl2UpperUnipotent x =
        sl2UpperUnipotent (A.val 0 0 ^ 2 * x) * A := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sl2UpperUnipotent, Matrix.mul_apply, Fin.sum_univ_two,
        h10, h11, sq, mul_assoc]
    field_simp
    ring
  rw [key, mul_assoc, mul_inv_cancel, mul_one]

/-- The quotient map from `SL₂` to `PSL₂`. -/
@[expose]
public def psl2QuotientMap
    (K : Type u) [Field K] : SL(2, K) →* PSL2 K :=
  QuotientGroup.mk' (Subgroup.center (SL(2, K)))

public theorem psl2QuotientMap_surjective
    {K : Type u} [Field K] : Function.Surjective (psl2QuotientMap K) :=
  QuotientGroup.mk'_surjective _

public theorem psl2QuotientMap_smul
    {K : Type u} [Field K]
    (g : SL(2, K)) (p : PSL2ProjectiveLine K) :
    psl2QuotientMap K g • p = g • p := rfl

/-- Point stabilizers in `PSL₂` are the images of the corresponding
stabilizers in `SL₂`. -/
public theorem psl2_stabilizer_eq_map
    {K : Type u} [Field K] (p : PSL2ProjectiveLine K) :
    MulAction.stabilizer (PSL2 K) p =
      (MulAction.stabilizer (SL(2, K)) p).map (psl2QuotientMap K) := by
  ext x
  obtain ⟨g, rfl⟩ := psl2QuotientMap_surjective (K := K) x
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨g, h, rfl⟩
  · rintro ⟨h, hh, hhg⟩
    rw [← hhg, psl2QuotientMap_smul]
    exact hh

/-- The standard Borel subgroup of `PSL₂`, as the stabilizer of infinity. -/
@[expose]
public def psl2Borel
    (K : Type u) [Field K] : Subgroup (PSL2 K) :=
  MulAction.stabilizer (PSL2 K) (psl2ProjectiveInfinity K)

public theorem psl2Borel_eq_map
    {K : Type u} [Field K] :
    psl2Borel K = (sl2Borel K).map (psl2QuotientMap K) := by
  exact psl2_stabilizer_eq_map (psl2ProjectiveInfinity K)

/-- The upper-unipotent root homomorphism in `PSL₂`. -/
@[expose]
public def psl2UpperUnipotentHom
    (K : Type u) [Field K] : Multiplicative K →* PSL2 K :=
  (psl2QuotientMap K).comp (sl2UpperUnipotentHom K)

public theorem psl2UpperUnipotentHom_injective
    {K : Type u} [Field K] :
    Function.Injective (psl2UpperUnipotentHom K) := by
  intro x y hxy
  have hcenter :
      sl2UpperUnipotent (x.toAdd - y.toAdd) ∈
        Subgroup.center (SL(2, K)) := by
    have hq :
        psl2QuotientMap K
            (sl2UpperUnipotent (x.toAdd - y.toAdd)) = 1 := by
      rw [sub_eq_add_neg, ← sl2UpperUnipotent_mul, map_mul,
        ← sl2UpperUnipotent_inv, map_inv]
      change psl2UpperUnipotentHom K x *
          (psl2UpperUnipotentHom K y)⁻¹ = 1
      rw [hxy, mul_inv_cancel]
    exact (QuotientGroup.eq_one_iff _).mp hq
  have hscalar :=
    Matrix.SpecialLinearGroup.scalar_eq_self_of_mem_center hcenter (0 : Fin 2)
  have h01 := congrFun (congrFun hscalar (0 : Fin 2)) (1 : Fin 2)
  apply Multiplicative.ext
  apply sub_eq_zero.mp
  simpa [sl2UpperUnipotent] using h01.symm

/-- The upper-unipotent root subgroup of `PSL₂`. -/
@[expose]
public def psl2UpperUnipotentSubgroup
    (K : Type u) [Field K] : Subgroup (PSL2 K) :=
  (psl2UpperUnipotentHom K).range

public theorem mem_psl2UpperUnipotentSubgroup_iff
    {K : Type u} [Field K] (g : PSL2 K) :
    g ∈ psl2UpperUnipotentSubgroup K ↔
      ∃ x : K, g = psl2QuotientMap K (sl2UpperUnipotent x) := by
  simp [psl2UpperUnipotentSubgroup, MonoidHom.mem_range,
    psl2UpperUnipotentHom, sl2UpperUnipotentHom]
  exact ⟨fun ⟨x, hx⟩ => ⟨x, hx.symm⟩,
    fun ⟨x, hx⟩ => ⟨x, hx.symm⟩⟩

public theorem psl2UpperUnipotent_le_borel
    {K : Type u} [Field K] :
    psl2UpperUnipotentSubgroup K ≤ psl2Borel K := by
  rw [psl2UpperUnipotentSubgroup, psl2UpperUnipotentHom,
    MonoidHom.range_comp, psl2Borel_eq_map]
  exact Subgroup.map_mono (sl2UpperUnipotent_le_borel (K := K))

/-- The upper-unipotent root subgroup is normal in the standard Borel. -/
public theorem psl2UpperUnipotent_normal_in_borel
    {K : Type u} [Field K] :
    ((psl2UpperUnipotentSubgroup K).subgroupOf (psl2Borel K)).Normal := by
  constructor
  intro x hx g
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨c, hxc⟩ :=
    (mem_psl2UpperUnipotentSubgroup_iff (x : PSL2 K)).mp hx
  have hgmem : (g : PSL2 K) ∈ (sl2Borel K).map (psl2QuotientMap K) := by
    rw [← psl2Borel_eq_map]
    exact g.property
  obtain ⟨b, hb, hbg⟩ := hgmem
  have hval :
      ((g * x * g⁻¹ : psl2Borel K) : PSL2 K) =
        psl2QuotientMap K (b * sl2UpperUnipotent c * b⁻¹) := by
    push_cast
    rw [map_mul, map_mul, map_inv, hxc, hbg]
  rw [hval]
  rw [sl2Borel_conj_upperUnipotent hb]
  exact (mem_psl2UpperUnipotentSubgroup_iff _).2 ⟨_, rfl⟩

/-- `PSL₂(K)` acts two-transitively on its projective line. -/
public instance psl2_projectiveLine_two_pretransitive
    (K : Type u) [Field K] :
    MulAction.IsMultiplyPretransitive
      (PSL2 K) (PSL2ProjectiveLine K) 2 :=
  let f : PSL2ProjectiveLine K →ₑ[psl2QuotientMap K]
      PSL2ProjectiveLine K := {
    toFun := id
    map_smul' := fun _ _ => rfl }
  MulAction.IsPretransitive.of_embedding
    (f := f) Function.surjective_id

/-- The upper-unipotent root subgroup has the same cardinality as the
coefficient field. -/
public theorem psl2UpperUnipotentSubgroup_card
    (K : Type u) [Field K] [Finite K] :
    Nat.card (psl2UpperUnipotentSubgroup K) = Nat.card K := by
  let e : Multiplicative K ≃* psl2UpperUnipotentSubgroup K :=
    MulEquiv.ofBijective (psl2UpperUnipotentHom K).rangeRestrict
      ⟨fun x y h => psl2UpperUnipotentHom_injective
          (congrArg Subtype.val h),
        MonoidHom.rangeRestrict_surjective _⟩
  calc
    Nat.card (psl2UpperUnipotentSubgroup K) =
        Nat.card (Multiplicative K) := Nat.card_congr e.symm.toEquiv
    _ = Nat.card K := Nat.card_congr Multiplicative.toAdd

end CFSG.GorensteinWalter
