module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.PSL2
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.LinearAlgebra.Projectivization.Cardinality
public import Mathlib.FieldTheory.Finite.GaloisField

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace Converse

open PFchapter1section1 PFAppendixIII Matrix Projectivization
open scoped LinearAlgebra.Projectivization MatrixGroups

universe u

variable {F : Type u} [Field F]

/-- `SL(2, F)`. -/
public abbrev SL2 (F : Type u) [Field F] := Matrix.SpecialLinearGroup (Fin 2) F

/-- The projective line over `F`. -/
public abbrev P1 (F : Type u) [Field F] := ℙ F (Fin 2 → F)

/-! ### The two standard points of the projective line -/

public theorem e0_ne_zero : (![1, 0] : Fin 2 → F) ≠ 0 := by
  intro h
  simpa using congrFun h 0

public theorem e1_ne_zero : (![0, 1] : Fin 2 → F) ≠ 0 := by
  intro h
  simpa using congrFun h 1

/-- The point at infinity `⟨(1,0)⟩` of the projective line. -/
@[expose] public def pInf (F : Type u) [Field F] : P1 F := Projectivization.mk F ![1, 0] e0_ne_zero

/-- The zero point `⟨(0,1)⟩` of the projective line. -/
@[expose] public def pZero (F : Type u) [Field F] : P1 F := Projectivization.mk F ![0, 1] e1_ne_zero

public theorem smul_eq_mulVec (A : SL2 F) (v : Fin 2 → F) : A • v = A.val *ᵥ v := rfl

public theorem smul_e0 (A : SL2 F) : A • (![1, 0] : Fin 2 → F) = ![A.val 0 0, A.val 1 0] := by
  ext i
  fin_cases i <;> simp [smul_eq_mulVec, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail]

public theorem smul_e1 (A : SL2 F) : A • (![0, 1] : Fin 2 → F) = ![A.val 0 1, A.val 1 1] := by
  ext i
  fin_cases i <;> simp [smul_eq_mulVec, Matrix.mulVec, Matrix.vecHead, Matrix.vecTail]

/-! ### Stabilizers of the two standard points -/

public theorem mem_stabilizer_pInf_iff (A : SL2 F) :
    A ∈ MulAction.stabilizer (SL2 F) (pInf F) ↔ A.val 1 0 = 0 := by
  rw [MulAction.mem_stabilizer_iff, pInf, Projectivization.smul_mk,
    Projectivization.mk_eq_mk_iff]
  constructor
  · rintro ⟨a, ha⟩
    have h1 := congrFun ha 1
    rw [smul_e0] at h1
    simpa [Units.smul_def] using h1.symm
  · intro h
    have hdet : A.val 0 0 * A.val 1 1 = 1 := by
      have := A.property
      rw [Matrix.det_fin_two] at this
      rw [h] at this
      simpa using this
    have hne : A.val 0 0 ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hdet
      exact zero_ne_one hdet
    refine ⟨Units.mk0 (A.val 0 0) hne, ?_⟩
    rw [smul_e0]
    ext i
    fin_cases i <;> simp [Units.smul_def, h]

public theorem mem_stabilizer_pZero_iff (A : SL2 F) :
    A ∈ MulAction.stabilizer (SL2 F) (pZero F) ↔ A.val 0 1 = 0 := by
  rw [MulAction.mem_stabilizer_iff, pZero, Projectivization.smul_mk,
    Projectivization.mk_eq_mk_iff]
  constructor
  · rintro ⟨a, ha⟩
    have h0 := congrFun ha 0
    rw [smul_e1] at h0
    simpa [Units.smul_def] using h0.symm
  · intro h
    have hdet : A.val 0 0 * A.val 1 1 = 1 := by
      have := A.property
      rw [Matrix.det_fin_two] at this
      rw [h] at this
      simpa using this
    have hne : A.val 1 1 ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hdet
      exact zero_ne_one hdet
    refine ⟨Units.mk0 (A.val 1 1) hne, ?_⟩
    rw [smul_e1]
    ext i
    fin_cases i <;> simp [Units.smul_def, h]

/-- The Borel subgroup: the stabilizer of the point at infinity, i.e. the upper
triangular matrices of determinant one. -/
@[expose] public def Borel (F : Type u) [Field F] : Subgroup (SL2 F) :=
  MulAction.stabilizer (SL2 F) (pInf F)

/-- The maximal torus: the stabilizer of both standard points, i.e. the diagonal
matrices of determinant one. -/
@[expose] public def Torus (F : Type u) [Field F] : Subgroup (SL2 F) :=
  MulAction.stabilizer (SL2 F) (pInf F) ⊓ MulAction.stabilizer (SL2 F) (pZero F)

/-! ### The unipotent radical and the torus, as ranges of injective homomorphisms -/

/-- The unipotent matrix `!![1, b; 0, 1]`. -/
@[expose] public def uni (b : F) : SL2 F := ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two_of]⟩

/-- The diagonal matrix `!![a, 0; 0, a⁻¹]`. -/
@[expose] public def tor (a : Fˣ) : SL2 F := ⟨!![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)], by
  simp [Matrix.det_fin_two_of]⟩

@[simp] public theorem uni_val (b : F) : (uni b).val = !![1, b; 0, 1] := rfl

@[simp] public theorem tor_val (a : Fˣ) :
    (tor a).val = !![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)] := rfl

/-- The unipotent radical of the Borel, as the range of a homomorphism from the
additive group of `F`. -/
@[expose] public def uniHom (F : Type u) [Field F] : Multiplicative F →* SL2 F where
  toFun b := uni b.toAdd
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/-- The torus, as the range of a homomorphism from the unit group of `F`. -/
@[expose] public def torHom (F : Type u) [Field F] : Fˣ →* SL2 F where
  toFun := tor
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' a b := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

@[simp] public theorem uniHom_apply (b : F) : uniHom F (Multiplicative.ofAdd b) = uni b := rfl

@[simp] public theorem torHom_apply (a : Fˣ) : torHom F a = tor a := rfl

public theorem uniHom_injective : Function.Injective (uniHom F) := by
  intro a b hab
  have := congrFun (congrFun (congrArg Subtype.val hab) 0) 1
  simpa [uniHom] using this

public theorem torHom_injective : Function.Injective (torHom F) := by
  intro a b hab
  have := congrFun (congrFun (congrArg Subtype.val hab) 0) 0
  simp [torHom] at this
  exact Units.ext this

/-- The unipotent radical `Q` of the Borel subgroup. -/
@[expose] public def Unip (F : Type u) [Field F] : Subgroup (SL2 F) := (uniHom F).range

public theorem mem_Unip_iff (A : SL2 F) : A ∈ Unip F ↔ ∃ b : F, A = uni b := by
  simp [Unip, MonoidHom.mem_range]
  exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩

public theorem Torus_eq_range : Torus F = (torHom F).range := by
  ext A
  rw [Torus, Subgroup.mem_inf, mem_stabilizer_pInf_iff, mem_stabilizer_pZero_iff,
    MonoidHom.mem_range]
  constructor
  · rintro ⟨h10, h01⟩
    have hdet : A.val 0 0 * A.val 1 1 = 1 := by
      have := A.property
      rw [Matrix.det_fin_two, h10, h01] at this
      simpa using this
    have hne : A.val 0 0 ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hdet
      exact zero_ne_one hdet
    have h11 : A.val 1 1 = (A.val 0 0)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact hdet)
    refine ⟨Units.mk0 (A.val 0 0) hne, ?_⟩
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [torHom, tor, h10, h01, h11]
  · rintro ⟨a, rfl⟩
    simp [torHom, tor]

/-! ### The Borel subgroup is the semidirect product `Unip ⋊ Torus` -/

public theorem mem_Borel_iff (A : SL2 F) : A ∈ Borel F ↔ A.val 1 0 = 0 :=
  mem_stabilizer_pInf_iff A

public theorem Borel_diag_ne_zero {A : SL2 F} (hA : A ∈ Borel F) : A.val 0 0 ≠ 0 := by
  rw [mem_Borel_iff] at hA
  intro h0
  have := A.property
  rw [Matrix.det_fin_two, hA, h0] at this
  simp at this

public theorem Borel_lower_right {A : SL2 F} (hA : A ∈ Borel F) :
    A.val 1 1 = (A.val 0 0)⁻¹ := by
  rw [mem_Borel_iff] at hA
  have := A.property
  rw [Matrix.det_fin_two, hA] at this
  simp only [mul_zero, sub_zero] at this
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact this)

public theorem Unip_le_Borel : Unip F ≤ Borel F := by
  rintro A hA
  rw [mem_Unip_iff] at hA
  obtain ⟨b, rfl⟩ := hA
  rw [mem_Borel_iff]
  simp

public theorem Torus_le_Borel : Torus F ≤ Borel F := inf_le_left

public theorem Unip_sup_Torus : Unip F ⊔ Torus F = Borel F := by
  apply le_antisymm (sup_le Unip_le_Borel Torus_le_Borel)
  intro A hA
  have hne := Borel_diag_ne_zero hA
  have h11 := Borel_lower_right hA
  rw [mem_Borel_iff] at hA
  have hfac : A = uni (A.val 0 1 * A.val 0 0) * tor (Units.mk0 (A.val 0 0) hne) := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hA, h11, mul_assoc,
        mul_inv_cancel₀ hne]
  rw [hfac]
  exact Subgroup.mul_mem_sup ((mem_Unip_iff _).2 ⟨_, rfl⟩)
    (by rw [Torus_eq_range]; exact ⟨_, rfl⟩)

public theorem Unip_disjoint_Torus : Disjoint (Unip F) (Torus F) := by
  rw [Subgroup.disjoint_def]
  intro A hU hT
  rw [mem_Unip_iff] at hU
  obtain ⟨b, rfl⟩ := hU
  rw [Torus_eq_range] at hT
  obtain ⟨a, ha⟩ := hT
  have hb : b = 0 := by
    have := congrFun (congrFun (congrArg Subtype.val ha) 0) 1
    simpa [torHom, tor] using this.symm
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hb]

/-- Conjugation inside the Borel scales the unipotent parameter by a square. -/
public theorem Borel_conj_uni {A : SL2 F} (hA : A ∈ Borel F) (b : F) :
    A * uni b * A⁻¹ = uni (A.val 0 0 ^ 2 * b) := by
  have hne := Borel_diag_ne_zero hA
  have h11 := Borel_lower_right hA
  rw [mem_Borel_iff] at hA
  have key : A * uni b = uni (A.val 0 0 ^ 2 * b) * A := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, hA, h11, sq, mul_assoc]
    field_simp
    ring
  rw [key, mul_assoc, mul_inv_cancel, mul_one]

/-! ### Characteristic two -/

public theorem uni_zero : uni (0 : F) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp

public theorem uni_mul_uni (a b : F) : uni a * uni b = uni (a + b) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

section CharTwo

variable [CharP F 2]

/-- The Weyl involution `!![0, 1; 1, 0]`, which has determinant `-1 = 1` in
characteristic two. -/
@[expose] public def weyl (F : Type u) [Field F] [CharP F 2] : SL2 F :=
  ⟨!![0, 1; 1, 0], by simp [Matrix.det_fin_two_of, CharTwo.neg_eq]⟩

@[simp] public theorem weyl_val : (weyl F).val = !![0, 1; 1, 0] := rfl

public theorem weyl_sq : weyl F * weyl F = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

public theorem weyl_ne_one : weyl F ≠ 1 := by
  intro h
  have := congrFun (congrFun (congrArg Subtype.val h) 0) 0
  simp at this

public theorem weyl_inv : (weyl F)⁻¹ = weyl F :=
  inv_eq_of_mul_eq_one_left weyl_sq

public theorem weyl_smul_pInf : weyl F • pInf F = pZero F := by
  rw [pInf, pZero, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
  refine ⟨1, ?_⟩
  rw [smul_e0]
  ext i
  fin_cases i <;> simp

public theorem weyl_notMem_Borel : weyl F ∉ Borel F := by
  rw [mem_Borel_iff]
  simp

/-- In characteristic two the centre of `SL(2, F)` is trivial, so `PSL(2, F)` is
`SL(2, F)` itself. -/
public theorem center_SL2_eq_bot : Subgroup.center (SL2 F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hA
  obtain ⟨r, hr, hrA⟩ := hA
  simp only [Fintype.card_fin] at hr
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hsq : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
  have hr1 : r = 1 :=
    eq_of_sub_eq_zero (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq)
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1]
  simp

/-! ### A Klein four subgroup inside the unipotent radical -/

/-- The additive `{0, x, y, x + y}`, an `𝔽₂`-plane when `x`, `y` are independent. -/
@[expose] public def kleinCarrier (x y : F) : Set F := {0, x, y, x + y}

omit [CharP F 2] in
public theorem uni_injective : Function.Injective (uni : F → SL2 F) := by
  intro a b hab
  have := congrFun (congrFun (congrArg Subtype.val hab) 0) 1
  simpa using this

public theorem kleinCarrier_add {x y a b : F} (ha : a ∈ kleinCarrier x y)
    (hb : b ∈ kleinCarrier x y) : a + b ∈ kleinCarrier x y := by
  have hxx : x + x = 0 := CharTwo.add_self_eq_zero x
  have hyy : y + y = 0 := CharTwo.add_self_eq_zero y
  have h1 : x + (x + y) = y := by rw [← add_assoc, hxx, zero_add]
  have h2 : y + (x + y) = x := by rw [add_comm x y, ← add_assoc, hyy, zero_add]
  have h3 : x + y + x = y := by rw [add_comm]; exact h1
  have h4 : x + y + y = x := by rw [add_comm]; exact h2
  have h5 : x + y + (x + y) = 0 := CharTwo.add_self_eq_zero _
  have h6 : y + x = x + y := add_comm y x
  simp only [kleinCarrier, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb ⊢
  rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
    simp [hxx, hyy, h1, h2, h3, h4, h5, h6]

/-- The Klein four subgroup of `SL(2, F)` spanned by the unipotent elements with
parameters `x` and `y`. -/
@[expose] public def klein (x y : F) : Subgroup (SL2 F) where
  carrier := uni '' kleinCarrier x y
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a + b, kleinCarrier_add ha hb, (uni_mul_uni a b).symm⟩
  one_mem' := ⟨0, by simp [kleinCarrier], uni_zero⟩
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨a, ha, ?_⟩
    rw [eq_comm, inv_eq_iff_mul_eq_one, uni_mul_uni, CharTwo.add_self_eq_zero, uni_zero]

public theorem klein_sq (x y : F) (g : klein x y) : (g : klein x y) ^ 2 = 1 := by
  obtain ⟨_, a, _, rfl⟩ := g
  apply Subtype.ext
  rw [Subgroup.coe_pow, sq]
  simpa using (uni_mul_uni a a).trans (by rw [CharTwo.add_self_eq_zero, uni_zero])

public theorem kleinCarrier_ncard {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    (kleinCarrier x y).ncard = 4 := by
  have hsum : x + y ≠ 0 := fun h =>
    hxy (by rw [eq_neg_of_add_eq_zero_left h, CharTwo.neg_eq])
  have hxs : x ≠ x + y := fun h => hy (by simpa using h.symm)
  have hys : y ≠ x + y := fun h => hx (by simpa using h.symm)
  rw [kleinCarrier]
  rw [Set.ncard_insert_of_notMem (by simp [hx.symm, hy.symm, hsum.symm]),
    Set.ncard_insert_of_notMem (by simp [hxy, hxs]),
    Set.ncard_insert_of_notMem (by simp [hys]), Set.ncard_singleton]

public theorem klein_card {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x ≠ y) :
    Nat.card (klein x y) = 4 := by
  show (uni '' kleinCarrier x y).ncard = 4
  rw [Set.ncard_image_of_injective _ uni_injective]
  exact kleinCarrier_ncard hx hy hxy

end CharTwo

/-! ### Passage to `PSL(2, F)` -/

/-- `PSL(2, F)`. -/
public abbrev PSL2 (F : Type u) [Field F] := Matrix.ProjectiveSpecialLinearGroup (Fin 2) F

/-- The quotient map `SL(2, F) → PSL(2, F)`. -/
@[expose] public def pi (F : Type u) [Field F] : SL2 F →* PSL2 F :=
  QuotientGroup.mk' (Subgroup.center (SL2 F))

public theorem pi_surjective : Function.Surjective (pi F) :=
  QuotientGroup.mk'_surjective _

public theorem pi_injective [CharP F 2] : Function.Injective (pi F) := by
  rw [← MonoidHom.ker_eq_bot_iff, pi, QuotientGroup.ker_mk']
  exact center_SL2_eq_bot

public theorem pi_smul (g : SL2 F) (p : P1 F) : pi F g • p = g • p := rfl

public theorem stabilizer_map (ω : P1 F) :
    MulAction.stabilizer (PSL2 F) ω = (MulAction.stabilizer (SL2 F) ω).map (pi F) := by
  ext x
  obtain ⟨g, rfl⟩ := pi_surjective (F := F) x
  simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨g, h, rfl⟩
  · rintro ⟨h, hh, hhg⟩
    rw [← hhg, pi_smul]
    exact hh

public instance psl2_two_pretransitive :
    MulAction.IsMultiplyPretransitive (PSL2 F) (P1 F) 2 :=
  let f : P1 F →ₑ[pi F] P1 F := { toFun := id, map_smul' := fun _ _ => rfl }
  MulAction.IsPretransitive.of_embedding (f := f) Function.surjective_id

section CharTwoPSL

variable [CharP F 2]

/-- The Borel subgroup of `PSL(2, F)`: the stabilizer of the point at infinity. -/
@[expose] public def PBorel (F : Type u) [Field F] : Subgroup (PSL2 F) :=
  MulAction.stabilizer (PSL2 F) (pInf F)

/-- The unipotent radical of `PBorel`. -/
@[expose] public def PUnip (F : Type u) [Field F] [CharP F 2] : Subgroup (PSL2 F) := (Unip F).map (pi F)

/-- The maximal torus of `PBorel`. -/
@[expose] public def PTorus (F : Type u) [Field F] [CharP F 2] : Subgroup (PSL2 F) := (Torus F).map (pi F)

/-- The Weyl involution in `PSL(2, F)`. -/
@[expose] public def PWeyl (F : Type u) [Field F] [CharP F 2] : PSL2 F := pi F (weyl F)

omit [CharP F 2] in
public theorem PBorel_eq_map : PBorel F = (Borel F).map (pi F) :=
  stabilizer_map _

public theorem PWeyl_isInvolution : IsInvolution (PWeyl F) := by
  refine ⟨?_, ?_⟩
  · intro h
    have hw : PWeyl F = pi F 1 := by rw [h, map_one]
    exact weyl_ne_one (F := F) (pi_injective hw)
  · rw [PWeyl, sq, ← map_mul, weyl_sq, map_one]

public theorem PWeyl_inv : (PWeyl F)⁻¹ = PWeyl F := by
  rw [PWeyl, ← map_inv, weyl_inv]

public theorem PWeyl_smul_pInf : PWeyl F • pInf F = pZero F := by
  rw [PWeyl, pi_smul, weyl_smul_pInf]

public theorem PWeyl_notMem_PBorel : PWeyl F ∉ PBorel F := by
  rw [PBorel_eq_map]
  rintro ⟨g, hg, hgw⟩
  exact weyl_notMem_Borel (pi_injective hgw ▸ hg)

public theorem PTorus_eq : PTorus F = PBorel F ⊓ MulAction.stabilizer (PSL2 F) (pZero F) := by
  rw [PTorus, Torus, Subgroup.map_inf_eq _ _ _ (pi_injective (F := F)), PBorel,
    stabilizer_map, stabilizer_map]

omit [CharP F 2] in
public theorem Unip_conj_mem {b : SL2 F} (hb : b ∈ Borel F) {u : SL2 F} (hu : u ∈ Unip F) :
    b * u * b⁻¹ ∈ Unip F := by
  obtain ⟨c, rfl⟩ := (mem_Unip_iff _).1 hu
  rw [Borel_conj_uni hb]
  exact (mem_Unip_iff _).2 ⟨_, rfl⟩

public theorem PUnip_le_PBorel : PUnip F ≤ PBorel F := by
  rw [PUnip, PBorel_eq_map]
  exact Subgroup.map_mono Unip_le_Borel

public theorem PTorus_le_PBorel : PTorus F ≤ PBorel F := by
  rw [PTorus, PBorel_eq_map]
  exact Subgroup.map_mono Torus_le_Borel

public theorem PUnip_sup_PTorus : PUnip F ⊔ PTorus F = PBorel F := by
  rw [PUnip, PTorus, ← Subgroup.map_sup, Unip_sup_Torus, PBorel_eq_map]

public theorem PUnip_disjoint_PTorus : Disjoint (PUnip F) (PTorus F) := by
  rw [disjoint_iff, PUnip, PTorus, ← Subgroup.map_inf_eq _ _ _ (pi_injective (F := F)),
    disjoint_iff.1 Unip_disjoint_Torus, Subgroup.map_bot]

public theorem PUnip_normal_in_PBorel : ((PUnip F).subgroupOf (PBorel F)).Normal := by
  constructor
  intro x hx g
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨u, hu, hux⟩ := hx
  have hgmem : (g : PSL2 F) ∈ (Borel F).map (pi F) := by
    rw [← PBorel_eq_map]; exact g.property
  obtain ⟨b, hb, hbg⟩ := hgmem
  have hval : ((g * x * g⁻¹ : PBorel F) : PSL2 F) = pi F (b * u * b⁻¹) := by
    push_cast
    rw [map_mul, map_mul, map_inv, hux, hbg]
  rw [hval]
  exact ⟨_, Unip_conj_mem hb hu, rfl⟩

/-! ### Cardinalities -/

public theorem card_map_pi (S : Subgroup (SL2 F)) :
    Nat.card (S.map (pi F)) = Nat.card S :=
  (Nat.card_congr (Subgroup.equivMapOfInjective S (pi F) (pi_injective)).toEquiv).symm

public theorem PUnip_card : Nat.card (PUnip F) = Nat.card F := by
  rw [PUnip, card_map_pi, Unip]
  exact (Nat.card_congr (MonoidHom.ofInjective (uniHom_injective (F := F))).toEquiv).symm

public theorem PTorus_card : Nat.card (PTorus F) = Nat.card Fˣ := by
  rw [PTorus, card_map_pi, Torus_eq_range]
  exact (Nat.card_congr (MonoidHom.ofInjective (torHom_injective (F := F))).toEquiv).symm

/-! ### Two-rank at least two -/

public theorem twoRank [Finite F] (y : F) (hy : y ≠ 0) (hy1 : y ≠ 1) :
    TwoRankAtLeastTwo (PSL2 F) := by
  refine ⟨(klein (1 : F) y).map (pi F), ?_, ?_⟩
  · rw [card_map_pi]
    exact klein_card one_ne_zero hy (Ne.symm hy1)
  · rintro ⟨_, g, hg, rfl⟩
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← map_pow]
    have : (g : SL2 F) ^ 2 = 1 := congrArg Subtype.val (klein_sq (1 : F) y ⟨g, hg⟩)
    rw [this, map_one]
    rfl

/-! ### Hypothesis (A) holds for `PSL(2, F)` acting on the projective line -/

public theorem hypothesisA1_psl2 [Finite F]
    (heven : Even (Nat.card F)) (hodd : Odd (Nat.card Fˣ)) :
    HypothesisA1 (PSL2 F) (P1 F) (PBorel F) (PTorus F) (PUnip F) (PWeyl F) where
  two_transitive := psl2_two_pretransitive
  point_stabilizer := ⟨pInf F, rfl⟩
  involution_t := PWeyl_isInvolution
  t_not_mem_H := PWeyl_notMem_PBorel
  D_eq := by
    rw [PTorus_eq]
    congr 1
    rw [PBorel, rightConjugate_stabilizer, PWeyl_inv, PWeyl_smul_pInf]
  Q_le_H := PUnip_le_PBorel
  D_le_H := PTorus_le_PBorel
  Q_normal_in_H := PUnip_normal_in_PBorel
  Q_disjoint_D := PUnip_disjoint_PTorus
  Q_sup_D := PUnip_sup_PTorus
  Q_even := by rw [PUnip_card]; exact heven
  D_odd := by rw [PTorus_card]; exact hodd

public theorem hypothesisA_psl2 [Finite F]
    (heven : Even (Nat.card F)) (hodd : Odd (Nat.card Fˣ))
    (y : F) (hy : y ≠ 0) (hy1 : y ≠ 1) :
    HypothesisA (PSL2 F) (P1 F) (PBorel F) (PTorus F) (PUnip F) (PWeyl F) where
  A1 := hypothesisA1_psl2 heven hodd
  A2 := inferInstance
  A3 := twoRank y hy hy1

end CharTwoPSL

/-! ### The concrete groups `PSL(2, 2ᵏ)` -/

variable (k : ℕ)

public theorem card_binaryGaloisField (hk : k ≠ 0) :
    Nat.card (BinaryGaloisField k) = 2 ^ k :=
  GaloisField.card 2 k hk

public theorem even_card_binaryGaloisField (hk : k ≠ 0) :
    Even (Nat.card (BinaryGaloisField k)) := by
  rw [card_binaryGaloisField k hk]
  exact (Nat.even_pow' hk).2 even_two

public theorem odd_card_units_binaryGaloisField (hk : k ≠ 0) :
    Odd (Nat.card (BinaryGaloisField k)ˣ) := by
  rw [Nat.card_units, card_binaryGaloisField k hk]
  exact Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow' hk).2 even_two) odd_one

public theorem exists_ne_zero_ne_one (hk : 2 ≤ k) :
    ∃ y : BinaryGaloisField k, y ≠ 0 ∧ y ≠ 1 := by
  have hk0 : k ≠ 0 := by omega
  have hcard : Nat.card (BinaryGaloisField k)ˣ = 2 ^ k - 1 := by
    rw [Nat.card_units, card_binaryGaloisField k hk0]
  have h1 : 1 < Nat.card (BinaryGaloisField k)ˣ := by
    rw [hcard]
    have : 4 ≤ 2 ^ k := by
      calc (4 : ℕ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
    omega
  have : Nontrivial (BinaryGaloisField k)ˣ := Finite.one_lt_card_iff_nontrivial.1 h1
  obtain ⟨u, hu⟩ := exists_ne (1 : (BinaryGaloisField k)ˣ)
  exact ⟨(u : BinaryGaloisField k), u.ne_zero, fun h => hu (Units.val_eq_one.1 h)⟩

/-- **Converse to the Suzuki theorem, `PSL₂` case.**  For every `k ≥ 2` the group
`PSL(2, 2ᵏ)`, acting on the projective line over `GF(2ᵏ)`, satisfies Hypothesis (A)
of Peterfalvi Part II — with `H` the Borel subgroup (the stabilizer of the point at
infinity), `Q` its unipotent radical, `D` the diagonal torus, and `t` the Weyl
involution. -/
public theorem hypothesisA_PSL2_binary (hk : 2 ≤ k) :
    HypothesisA (PSL2 (BinaryGaloisField k)) (P1 (BinaryGaloisField k))
      (PBorel (BinaryGaloisField k)) (PTorus (BinaryGaloisField k))
      (PUnip (BinaryGaloisField k)) (PWeyl (BinaryGaloisField k)) := by
  obtain ⟨y, hy, hy1⟩ := exists_ne_zero_ne_one k hk
  exact hypothesisA_psl2 (even_card_binaryGaloisField k (by omega))
    (odd_card_units_binaryGaloisField k (by omega)) y hy hy1

end Converse
end CFSG.BenderSuzuki
