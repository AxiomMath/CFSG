module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Tactic.LinearCombination

public noncomputable section

namespace CFSG.Quasithin.SteinbergBQ

open Matrix
open scoped MatrixGroups Pointwise

variable {k : Type*} [Field k]

@[expose] def uMat (x y z : k) : SL(3, k) :=
  ⟨!![1, x, z; 0, 1, y; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem coe_uMat (x y z : k) :
    ((uMat x y z : SL(3, k)) : Matrix (Fin 3) (Fin 3) k) = !![1, x, z; 0, 1, y; 0, 0, 1] := rfl

theorem uMat_mul (x y z x' y' z' : k) :
    uMat x y z * uMat x' y' z' = uMat (x + x') (y + y') (z + z' + x * y') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_uMat, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three] <;>
    ring

theorem uMat_zero : uMat (0 : k) 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_uMat]

theorem uMat_inv (x y z : k) : (uMat x y z)⁻¹ = uMat (-x) (-y) (x * y - z) := by
  rw [inv_eq_iff_mul_eq_one, uMat_mul, ← uMat_zero]
  congr 1 <;> ring

@[expose] def dMat (a b : kˣ) : SL(3, k) :=
  ⟨!![(a : k), 0, 0; 0, (b : k), 0; 0, 0, (((a * b)⁻¹ : kˣ) : k)], by
    simp [Matrix.det_fin_three, mul_assoc]⟩

theorem coe_dMat (a b : kˣ) : ((dMat a b : SL(3, k)) : Matrix (Fin 3) (Fin 3) k) =
    !![(a : k), 0, 0; 0, (b : k), 0; 0, 0, (((a * b)⁻¹ : kˣ) : k)] := rfl

theorem dMat_mul (a b a' b' : kˣ) : dMat a b * dMat a' b' = dMat (a * a') (b * b') := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_dMat, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_three,
      mul_comm, mul_left_comm, mul_assoc]

theorem dMat_one : dMat (1 : kˣ) 1 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [coe_dMat]

theorem dMat_inv (a b : kˣ) : (dMat a b)⁻¹ = dMat a⁻¹ b⁻¹ := by
  rw [inv_eq_iff_mul_eq_one, dMat_mul, mul_inv_cancel, mul_inv_cancel, dMat_one]

theorem dMat_mul_uMat (a b : kˣ) (x y z : k) :
    dMat a b * uMat x y z =
      uMat ((a : k) * (b : k)⁻¹ * x) ((b : k) * ((a : k) * b) * y) ((a : k) * ((a : k) * b) * z) *
        dMat a b := by
  have ha : (a : k) ≠ 0 := a.ne_zero
  have hb : (b : k) ≠ 0 := b.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_dMat, coe_uMat, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_three] <;> field_simp

theorem coe_uMat_mul_dMat (x y z : k) (a b : kˣ) :
    ((uMat x y z * dMat a b : SL(3, k)) : Matrix (Fin 3) (Fin 3) k) =
      !![(a : k), x * b, z * (((a * b)⁻¹ : kˣ) : k); 0, (b : k), y * (((a * b)⁻¹ : kˣ) : k);
        0, 0, (((a * b)⁻¹ : kˣ) : k)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_dMat, coe_uMat, Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply,
      Fin.sum_univ_three]

@[expose] def triA (k : Type*) [Field k] : Subgroup SL(3, k) where
  carrier := {g | ∃ x y z : k, g = uMat x y z}
  mul_mem' := by
    rintro _ _ ⟨x, y, z, rfl⟩ ⟨x', y', z', rfl⟩
    exact ⟨_, _, _, uMat_mul x y z x' y' z'⟩
  one_mem' := ⟨0, 0, 0, uMat_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨x, y, z, rfl⟩
    exact ⟨_, _, _, uMat_inv x y z⟩

variable {μ : Subgroup kˣ}

theorem uMat_dMat_mul (x y z x' y' z' : k) (a b a' b' : kˣ) :
    uMat x y z * dMat a b * (uMat x' y' z' * dMat a' b') =
      uMat (x + (a : k) * (b : k)⁻¹ * x') (y + (b : k) * ((a : k) * b) * y')
        (z + (a : k) * ((a : k) * b) * z' + x * ((b : k) * ((a : k) * b) * y')) *
        dMat (a * a') (b * b') := by
  rw [mul_assoc, ← mul_assoc (dMat a b), dMat_mul_uMat, mul_assoc, dMat_mul, ← mul_assoc,
    uMat_mul]

theorem uMat_dMat_inv (x y z : k) (a b : kˣ) :
    (uMat x y z * dMat a b)⁻¹ =
      uMat (((a⁻¹ : kˣ) : k) * ((b⁻¹ : kˣ) : k)⁻¹ * (-x))
        (((b⁻¹ : kˣ) : k) * (((a⁻¹ : kˣ) : k) * ((b⁻¹ : kˣ) : k)) * (-y))
        (((a⁻¹ : kˣ) : k) * (((a⁻¹ : kˣ) : k) * ((b⁻¹ : kˣ) : k)) * (x * y - z)) *
        dMat a⁻¹ b⁻¹ := by
  rw [mul_inv_rev, dMat_inv, uMat_inv, dMat_mul_uMat]

variable (μ)

@[expose] def triX : Subgroup SL(3, k) where
  carrier := {g | ∃ x y z : k, ∃ a ∈ μ, ∃ b ∈ μ, g = uMat x y z * dMat a b}
  mul_mem' := by
    rintro _ _ ⟨x, y, z, a, ha, b, hb, rfl⟩ ⟨x', y', z', a', ha', b', hb', rfl⟩
    exact ⟨_, _, _, a * a', μ.mul_mem ha ha', b * b', μ.mul_mem hb hb',
      uMat_dMat_mul _ _ _ _ _ _ _ _ _ _⟩
  one_mem' := ⟨0, 0, 0, 1, μ.one_mem, 1, μ.one_mem, by rw [uMat_zero, dMat_one, mul_one]⟩
  inv_mem' := by
    rintro _ ⟨x, y, z, a, ha, b, hb, rfl⟩
    exact ⟨_, _, _, a⁻¹, μ.inv_mem ha, b⁻¹, μ.inv_mem hb, uMat_dMat_inv x y z a b⟩

@[expose] def triP : Subgroup SL(3, k) where
  carrier := {g | ∃ a ∈ μ, ∃ b ∈ μ, g = dMat a b}
  mul_mem' := by
    rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
    exact ⟨_, μ.mul_mem ha ha', _, μ.mul_mem hb hb', dMat_mul a b a' b'⟩
  one_mem' := ⟨1, μ.one_mem, 1, μ.one_mem, dMat_one.symm⟩
  inv_mem' := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact ⟨_, μ.inv_mem ha, _, μ.inv_mem hb, dMat_inv a b⟩

@[expose] def triK : Subgroup SL(3, k) where
  carrier := {g | ∃ a ∈ μ, g = dMat a (a⁻¹ * a⁻¹)}
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨a', ha', rfl⟩
    refine ⟨a * a', μ.mul_mem ha ha', ?_⟩
    rw [dMat_mul, mul_inv, mul_mul_mul_comm]
  one_mem' := ⟨1, μ.one_mem, by rw [inv_one, one_mul, dMat_one]⟩
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a⁻¹, μ.inv_mem ha, by rw [dMat_inv, mul_inv]⟩

theorem triA_le_triX : triA k ≤ triX μ := by
  rintro _ ⟨x, y, z, rfl⟩
  exact ⟨x, y, z, 1, μ.one_mem, 1, μ.one_mem, by rw [dMat_one, mul_one]⟩

theorem coe_triX : (triX μ : Set SL(3, k)) = (triA k : Set SL(3, k)) * (triP μ : Set SL(3, k)) := by
  ext g
  constructor
  · rintro ⟨x, y, z, a, ha, b, hb, rfl⟩
    exact Set.mul_mem_mul ⟨x, y, z, rfl⟩ ⟨a, ha, b, hb, rfl⟩
  · rintro ⟨_, ⟨x, y, z, rfl⟩, _, ⟨a, ha, b, hb, rfl⟩, rfl⟩
    exact ⟨x, y, z, a, ha, b, hb, rfl⟩

theorem entry_mul_of_mem {g h : SL(3, k)} (hg : g ∈ triX μ) (hh : h ∈ triX μ) :
    ((g * h : SL(3, k)) : Matrix (Fin 3) (Fin 3) k) 0 0 =
        (g : Matrix (Fin 3) (Fin 3) k) 0 0 * (h : Matrix (Fin 3) (Fin 3) k) 0 0 ∧
      ((g * h : SL(3, k)) : Matrix (Fin 3) (Fin 3) k) 1 1 =
        (g : Matrix (Fin 3) (Fin 3) k) 1 1 * (h : Matrix (Fin 3) (Fin 3) k) 1 1 := by
  obtain ⟨x, y, z, a, -, b, -, rfl⟩ := hg
  obtain ⟨x', y', z', a', -, b', -, rfl⟩ := hh
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_uMat_mul_dMat, coe_uMat_mul_dMat]
  constructor <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem entry_ne_zero_of_mem {g : SL(3, k)} (hg : g ∈ triX μ) :
    (g : Matrix (Fin 3) (Fin 3) k) 0 0 ≠ 0 ∧ (g : Matrix (Fin 3) (Fin 3) k) 1 1 ≠ 0 := by
  obtain ⟨x, y, z, a, -, b, -, rfl⟩ := hg
  rw [coe_uMat_mul_dMat]
  exact ⟨by simp, by simp⟩

@[expose] def diagHom : triX μ →* kˣ × kˣ where
  toFun g :=
    (Units.mk0 _ (entry_ne_zero_of_mem μ g.2).1, Units.mk0 _ (entry_ne_zero_of_mem μ g.2).2)
  map_one' := by
    ext <;> simp
  map_mul' g h := by
    ext
    · exact (entry_mul_of_mem μ g.2 h.2).1
    · exact (entry_mul_of_mem μ g.2 h.2).2

theorem diagHom_eq {g : triX μ} {x y z : k} {a b : kˣ}
    (hg : (g : SL(3, k)) = uMat x y z * dMat a b) : diagHom μ g = (a, b) := by
  ext
  · change (g : Matrix (Fin 3) (Fin 3) k) 0 0 = a
    rw [hg, coe_uMat_mul_dMat]
    simp
  · change (g : Matrix (Fin 3) (Fin 3) k) 1 1 = b
    rw [hg, coe_uMat_mul_dMat]
    simp

theorem ker_diagHom : (diagHom μ).ker = (triA k).subgroupOf (triX μ) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  obtain ⟨x, y, z, a, ha, b, hb, hg⟩ := g.2
  rw [diagHom_eq μ hg, Prod.mk_eq_one, hg]
  constructor
  · rintro ⟨rfl, rfl⟩
    exact ⟨x, y, z, by rw [dMat_one, mul_one]⟩
  · rintro ⟨x', y', z', h⟩
    have h1 := congrArg (fun g : SL(3, k) => (g : Matrix (Fin 3) (Fin 3) k) 0 0) h
    have h2 := congrArg (fun g : SL(3, k) => (g : Matrix (Fin 3) (Fin 3) k) 1 1) h
    simp only [coe_uMat_mul_dMat, coe_uMat] at h1 h2
    simp at h1 h2
    exact ⟨h1, h2⟩

omit [Field k] in
theorem uMat_eq_iff [Field k] {x y z x' y' z' : k} :
    uMat x y z = uMat x' y' z' ↔ x = x' ∧ y = y' ∧ z = z' := by
  constructor
  · intro h
    have h1 := congrArg (fun g : SL(3, k) => (g : Matrix (Fin 3) (Fin 3) k) 0 1) h
    have h2 := congrArg (fun g : SL(3, k) => (g : Matrix (Fin 3) (Fin 3) k) 1 2) h
    have h3 := congrArg (fun g : SL(3, k) => (g : Matrix (Fin 3) (Fin 3) k) 0 2) h
    simp [coe_uMat] at h1 h2 h3
    exact ⟨h1, h2, h3⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem uMat_dMat_eq_iff {x y z x' y' z' : k} {a b a' b' : kˣ} :
    uMat x y z * dMat a b = uMat x' y' z' * dMat a' b' ↔
      x = x' ∧ y = y' ∧ z = z' ∧ a = a' ∧ b = b' := by
  constructor
  · intro h
    have e : ∀ i j, ((uMat x y z * dMat a b : SL(3, k)) : Matrix (Fin 3) (Fin 3) k) i j =
        ((uMat x' y' z' * dMat a' b' : SL(3, k)) : Matrix (Fin 3) (Fin 3) k) i j :=
      fun i j => by rw [h]
    have h00 := e 0 0
    have h11 := e 1 1
    have h22 := e 2 2
    have h01 := e 0 1
    have h12 := e 1 2
    have h02 := e 0 2
    simp only [coe_uMat_mul_dMat] at h00 h11 h22 h01 h12 h02
    simp at h00 h11 h22 h01 h12 h02
    have ha : a = a' := Units.ext h00
    have hb : b = b' := Units.ext h11
    subst ha hb
    have hc : (((a * b)⁻¹ : kˣ) : k) ≠ 0 := Units.ne_zero _
    refine ⟨mul_right_cancel₀ b.ne_zero h01, mul_right_cancel₀ hc ?_, mul_right_cancel₀ hc ?_,
      rfl, rfl⟩
    · simpa using h12
    · simpa using h02
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩
    rfl

theorem pow_four_uMat [CharP k 2] (x y z : k) : uMat x y z ^ 4 = 1 := by
  have h2 : uMat x y z ^ 2 = uMat 0 0 (x * y) := by
    rw [pow_two, uMat_mul, CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero,
      CharTwo.add_self_eq_zero, zero_add]
  rw [show 4 = 2 * 2 from rfl, pow_mul, h2, pow_two, uMat_mul, add_zero, mul_zero, add_zero,
    CharTwo.add_self_eq_zero, uMat_zero]

theorem isPGroup_triA [CharP k 2] : IsPGroup 2 (triA k) := by
  rintro ⟨_, x, y, z, rfl⟩
  exact ⟨2, Subtype.ext (by simpa using pow_four_uMat x y z)⟩

theorem pCore_triX [CharP k 2] (hodd : ∀ a ∈ μ, ∀ m : ℕ, a ^ (2 ^ m) = 1 → a = 1) :
    CFSG.pCore 2 (triX μ) = (triA k).subgroupOf (triX μ) := by
  refine le_antisymm (fun g hg => ?_) ?_
  · obtain ⟨m, hm⟩ := CFSG.pCore_isPGroup (p := 2) (G := triX μ) ⟨g, hg⟩
    have hm' : g ^ (2 ^ m) = 1 := congrArg Subtype.val hm
    rw [← ker_diagHom, MonoidHom.mem_ker]
    obtain ⟨x, y, z, a, ha, b, hb, hgeq⟩ := g.2
    have hd := congrArg (diagHom μ) hm'
    rw [map_pow, map_one, diagHom_eq μ hgeq, Prod.pow_mk, Prod.mk_eq_one] at hd
    rw [diagHom_eq μ hgeq, hodd a ha m hd.1, hodd b hb m hd.2]
    rfl
  · rw [← ker_diagHom]
    refine le_sSup ⟨inferInstance, ?_⟩
    rw [ker_diagHom]
    intro g
    obtain ⟨n, hn⟩ := isPGroup_triA (k := k) ⟨g.1.1, g.2⟩
    have hn' : (g.1.1 : SL(3, k)) ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    exact ⟨n, Subtype.ext (Subtype.ext hn')⟩

@[expose] def triZ (k : Type*) [Field k] : Subgroup SL(3, k) where
  carrier := {g | ∃ z : k, g = uMat 0 0 z}
  mul_mem' := by
    rintro _ _ ⟨z, rfl⟩ ⟨z', rfl⟩
    exact ⟨z + z', by rw [uMat_mul]; simp⟩
  one_mem' := ⟨0, uMat_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨z, rfl⟩
    exact ⟨-z, by rw [uMat_inv]; simp⟩

theorem center_triA : (Subgroup.center (triA k)).map (triA k).subtype = triZ k := by
  ext g
  constructor
  · rintro ⟨c, hc, rfl⟩
    obtain ⟨x, y, z, hxyz⟩ := c.2
    rw [SetLike.mem_coe, Subgroup.mem_center_iff] at hc
    have h1 := congrArg Subtype.val (hc ⟨uMat 1 0 0, 1, 0, 0, rfl⟩)
    have h2 := congrArg Subtype.val (hc ⟨uMat 0 1 0, 0, 1, 0, rfl⟩)
    simp only [Subgroup.coe_mul, hxyz, uMat_mul, uMat_eq_iff] at h1 h2
    refine ⟨z, ?_⟩
    change (c : SL(3, k)) = uMat 0 0 z
    rw [hxyz, uMat_eq_iff]
    refine ⟨?_, ?_, rfl⟩
    · linear_combination -h2.2.2
    · linear_combination h1.2.2
  · rintro ⟨z, rfl⟩
    refine ⟨⟨uMat 0 0 z, 0, 0, z, rfl⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    rintro ⟨_, x', y', z', rfl⟩
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, uMat_mul, uMat_eq_iff]
    exact ⟨by ring, by ring, by ring⟩

@[expose] def triAK : Subgroup SL(3, k) where
  carrier := {g | ∃ x y z : k, ∃ a ∈ μ, ∃ b : kˣ, b = a⁻¹ * a⁻¹ ∧ g = uMat x y z * dMat a b}
  mul_mem' := by
    rintro _ _ ⟨x, y, z, a, ha, b, hb, rfl⟩ ⟨x', y', z', a', ha', b', hb', rfl⟩
    refine ⟨_, _, _, a * a', μ.mul_mem ha ha', b * b', ?_, uMat_dMat_mul _ _ _ _ _ _ _ _ _ _⟩
    rw [hb, hb', mul_inv, mul_mul_mul_comm]
  one_mem' := ⟨0, 0, 0, 1, μ.one_mem, 1, by rw [inv_one, one_mul],
    by rw [uMat_zero, dMat_one, mul_one]⟩
  inv_mem' := by
    rintro _ ⟨x, y, z, a, ha, b, hb, rfl⟩
    refine ⟨_, _, _, a⁻¹, μ.inv_mem ha, b⁻¹, ?_, uMat_dMat_inv x y z a b⟩
    rw [hb, mul_inv]

theorem triAK_eq_sup : triAK μ = triA k ⊔ triK μ := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rintro _ ⟨x, y, z, a, ha, b, rfl, rfl⟩
    exact Subgroup.mul_mem_sup ⟨x, y, z, rfl⟩ ⟨a, ha, rfl⟩
  · rintro _ ⟨x, y, z, rfl⟩
    exact ⟨x, y, z, 1, μ.one_mem, 1, by rw [inv_one, one_mul], by rw [dMat_one, mul_one]⟩
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨0, 0, 0, a, ha, _, rfl, by rw [uMat_zero, one_mul]⟩

theorem triAK_le_triX : triAK μ ≤ triX μ := by
  rintro _ ⟨x, y, z, a, ha, b, rfl, rfl⟩
  exact ⟨x, y, z, a, ha, _, μ.mul_mem (μ.inv_mem ha) (μ.inv_mem ha), rfl⟩

theorem triX_inf_centralizer :
    triX μ ⊓ Subgroup.centralizer (triZ k : Set SL(3, k)) = triAK μ := by
  have key : ∀ (x y z w : k) (a b : kˣ), uMat 0 0 w * (uMat x y z * dMat a b) =
      uMat x y z * dMat a b * uMat 0 0 w ↔ w = (a : k) * ((a : k) * b) * w := by
    intro x y z w a b
    rw [← mul_assoc, uMat_mul, mul_assoc, dMat_mul_uMat, ← mul_assoc, uMat_mul, uMat_dMat_eq_iff]
    simp only [mul_zero, add_zero, zero_add, zero_mul, true_and, and_true]
    constructor
    · intro h
      linear_combination h
    · intro h
      linear_combination h
  ext g
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨⟨x, y, z, a, ha, b, hb, rfl⟩, hc⟩
    have h1 := (key x y z 1 a b).1 (hc (uMat 0 0 1) ⟨1, rfl⟩)
    have hab : a * (a * b) = 1 := by
      refine Units.ext ?_
      push_cast
      linear_combination -h1
    refine ⟨x, y, z, a, ha, b, ?_, rfl⟩
    rw [← mul_inv, eq_inv_iff_mul_eq_one, mul_comm, mul_assoc]
    exact hab
  · rintro ⟨x, y, z, a, ha, b, hb, rfl⟩
    refine ⟨⟨x, y, z, a, ha, b, hb ▸ μ.mul_mem (μ.inv_mem ha) (μ.inv_mem ha), rfl⟩, ?_⟩
    rintro _ ⟨w, rfl⟩
    refine (key x y z w a b).2 ?_
    have hab : (a : k) * ((a : k) * b) = 1 := by
      rw [hb]
      push_cast
      field_simp
    rw [hab, one_mul]

theorem card_triA : Nat.card (triA k) = Nat.card k ^ 3 := by
  let f : k × k × k → triA k := fun v => ⟨uMat v.1 v.2.1 v.2.2, v.1, v.2.1, v.2.2, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun v w h => ?_, fun g => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := uMat_eq_iff.1 (congrArg Subtype.val h)
      exact Prod.ext h1 (Prod.ext h2 h3)
    · obtain ⟨x, y, z, hg⟩ := g.2
      exact ⟨(x, y, z), Subtype.ext hg.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_prod]
  ring

theorem card_triAK : Nat.card (triAK μ) = Nat.card k ^ 3 * Nat.card μ := by
  let f : k × k × k × μ → triAK μ := fun v => ⟨uMat v.1 v.2.1 v.2.2.1 *
    dMat v.2.2.2 ((v.2.2.2 : kˣ)⁻¹ * (v.2.2.2 : kˣ)⁻¹),
    v.1, v.2.1, v.2.2.1, v.2.2.2, v.2.2.2.2, _, rfl, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun v w h => ?_, fun g => ?_⟩
    · obtain ⟨h1, h2, h3, h4, -⟩ := uMat_dMat_eq_iff.1 (congrArg Subtype.val h)
      exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 (Subtype.ext h4)))
    · obtain ⟨x, y, z, a, ha, b, rfl, hg⟩ := g.2
      exact ⟨(x, y, z, ⟨a, ha⟩), Subtype.ext hg.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_prod, Nat.card_prod]
  ring

theorem card_triX : Nat.card (triX μ) = Nat.card k ^ 3 * Nat.card μ ^ 2 := by
  let f : k × k × k × μ × μ → triX μ := fun v => ⟨uMat v.1 v.2.1 v.2.2.1 *
    dMat v.2.2.2.1 v.2.2.2.2, v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.1.2, v.2.2.2.2,
    v.2.2.2.2.2, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun v w h => ?_, fun g => ?_⟩
    · obtain ⟨h1, h2, h3, h4, h5⟩ := uMat_dMat_eq_iff.1 (congrArg Subtype.val h)
      exact Prod.ext h1 (Prod.ext h2 (Prod.ext h3 (Prod.ext (Subtype.ext h4) (Subtype.ext h5))))
    · obtain ⟨x, y, z, a, ha, b, hb, hg⟩ := g.2
      exact ⟨(x, y, z, ⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hg.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod, Nat.card_prod, Nat.card_prod,
    Nat.card_prod]
  ring

theorem card_triP : Nat.card (triP μ) = Nat.card μ ^ 2 := by
  let f : μ × μ → triP μ := fun v => ⟨dMat v.1 v.2, v.1, v.1.2, v.2, v.2.2, rfl⟩
  have hf : Function.Bijective f := by
    refine ⟨fun v w h => ?_, fun g => ?_⟩
    · have h' : uMat 0 0 0 * dMat (v.1 : kˣ) v.2 = uMat 0 0 0 * dMat (w.1 : kˣ) w.2 := by
        rw [uMat_zero, one_mul, one_mul]
        exact congrArg Subtype.val h
      obtain ⟨-, -, -, h4, h5⟩ := uMat_dMat_eq_iff.1 h'
      exact Prod.ext (Subtype.ext h4) (Subtype.ext h5)
    · obtain ⟨a, ha, b, hb, hg⟩ := g.2
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hg.symm⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_prod]
  ring

theorem dMat_pow (a b : kˣ) (n : ℕ) : dMat a b ^ n = dMat (a ^ n) (b ^ n) := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_zero, dMat_one]
  | succ n ih => rw [pow_succ, ih, dMat_mul, ← pow_succ, ← pow_succ]

theorem isElementaryAbelian_triP {p : ℕ} (hμ : ∀ a ∈ μ, a ^ p = 1) :
    IsElementaryAbelian p (triP μ) := by
  have hcomm : ∀ g h : triP μ, g * h = h * g := by
    rintro ⟨_, a, ha, b, hb, rfl⟩ ⟨_, a', ha', b', hb', rfl⟩
    refine Subtype.ext ?_
    change dMat a b * dMat a' b' = dMat a' b' * dMat a b
    rw [dMat_mul, dMat_mul, mul_comm a, mul_comm b]
  refine { is_comm := ⟨hcomm⟩, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun g => ?_
  obtain ⟨_, a, ha, b, hb, rfl⟩ := g
  refine Subtype.ext ?_
  change dMat a b ^ p = 1
  rw [dMat_pow, hμ a ha, hμ b hb, dMat_one]

theorem eq_one_of_mem_triX_of_scalar {p : ℕ} (hμ : ∀ a ∈ μ, a ^ p = 1) (hp3 : Nat.Coprime 3 p)
    {g : SL(3, k)} (hg : g ∈ triX μ) {c : kˣ} (hc : c ^ 3 = 1)
    (hgc : (g : Matrix (Fin 3) (Fin 3) k) = (c : k) • 1) : g = 1 := by
  obtain ⟨x, y, z, a, ha, b, -, rfl⟩ := hg
  have h00 := congrFun (congrFun hgc 0) 0
  rw [coe_uMat_mul_dMat] at h00
  have hac : a = c := Units.ext (by simpa using h00)
  have h1 : c = 1 := by
    have := pow_gcd_eq_one.2 ⟨hc, hac ▸ hμ a ha⟩
    rwa [Nat.Coprime.gcd_eq_one hp3, pow_one] at this
  refine Subtype.ext ?_
  rw [hgc, h1, Units.val_one, one_smul, Matrix.SpecialLinearGroup.coe_one]

theorem injOn_triX {G : Type*} [Group G] (π : SL(3, k) →* G) {p : ℕ}
    (hμ : ∀ a ∈ μ, a ^ p = 1) (hp3 : Nat.Coprime 3 p)
    (hπ : ∀ g ∈ π.ker, ∃ c : kˣ, c ^ 3 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) k) = (c : k) • 1) :
    Set.InjOn π (triX μ) := by
  intro g hg h hh hgh
  have hk : g * h⁻¹ ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hgh, mul_inv_cancel]
  obtain ⟨c, hc, hgc⟩ := hπ _ hk
  exact mul_inv_eq_one.1
    (eq_one_of_mem_triX_of_scalar μ hμ hp3 ((triX μ).mul_mem hg ((triX μ).inv_mem hh)) hc hgc)

section Transport

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂] (π : G₁ →* G₂) {H : Subgroup G₁}

@[expose] def mapIso (hH : Set.InjOn π H) : H ≃* H.map π :=
  MulEquiv.ofBijective
    ((π.comp H.subtype).codRestrict (H.map π) fun x => Subgroup.mem_map_of_mem π x.2)
    ⟨fun x y hxy => Subtype.ext (hH x.2 y.2 (congrArg Subtype.val hxy)),
      fun ⟨_, x, hx, hxy⟩ => ⟨⟨x, hx⟩, Subtype.ext hxy⟩⟩

theorem map_subgroupOf_mapIso (hH : Set.InjOn π H) {K : Subgroup G₁} (hKH : K ≤ H) :
    (K.subgroupOf H).map (mapIso π hH).toMonoidHom = (K.map π).subgroupOf (H.map π) := by
  ext ⟨g, hg⟩
  constructor
  · rintro ⟨x, hx, hxg⟩
    exact ⟨x, hx, congrArg Subtype.val hxg⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hKH hx⟩, hx, Subtype.ext rfl⟩

theorem card_map_of_injOn (hH : Set.InjOn π H) : Nat.card (H.map π) = Nat.card H :=
  (Nat.card_congr (mapIso π hH).toEquiv).symm

theorem pCore_map_of_injOn (hH : Set.InjOn π H) {K : Subgroup G₁} (hKH : K ≤ H) {p : ℕ}
    (hK : CFSG.pCore p H = K.subgroupOf H) :
    CFSG.pCore p (H.map π) = (K.map π).subgroupOf (H.map π) := by
  rw [← CFSG.pCore_map_iso p (mapIso π hH), hK]
  exact map_subgroupOf_mapIso π hH hKH

end Transport

theorem mem_map_center_subtype {H : Type*} [Group H] {N : Subgroup H} {z : H} :
    z ∈ (Subgroup.center N).map N.subtype ↔ z ∈ N ∧ ∀ n ∈ N, n * z = z * n := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c.2, fun n hn => congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨n, hn⟩)⟩
  · rintro ⟨hz, h⟩
    exact ⟨⟨z, hz⟩, Subgroup.mem_center_iff.2 fun n => Subtype.ext (h n n.2), rfl⟩

theorem isElementaryAbelian_quotient {H : Type*} [Group H] (N : Subgroup H) [N.Normal] {p : ℕ}
    (hcomm : ∀ x y : H, (x * y)⁻¹ * (y * x) ∈ N) (hpow : ∀ x : H, x ^ p ∈ N) :
    IsElementaryAbelian p (H ⧸ N) := by
  have hc : ∀ u v : H ⧸ N, u * v = v * u := by
    intro u v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective v
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    exact hcomm x y
  refine { is_comm := ⟨hc⟩, exponent_dvd_p := ?_ }
  refine Monoid.exponent_dvd_of_forall_pow_eq_one fun u => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective u
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact hpow x

theorem subgroupOf_centralizer_eq {H : Type*} [Group H] {X A : Subgroup H} (hAX : A ≤ X) :
    (X ⊓ Subgroup.centralizer ((Subgroup.center A).map A.subtype : Set H)).subgroupOf X =
      Subgroup.centralizer
        ((Subgroup.center (A.subgroupOf X)).map (A.subgroupOf X).subtype : Set X) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨-, hc⟩ z hz
    rw [SetLike.mem_coe, mem_map_center_subtype] at hz
    refine Subtype.ext (hc z ?_)
    rw [SetLike.mem_coe, mem_map_center_subtype]
    exact ⟨hz.1, fun n hn => congrArg Subtype.val (hz.2 ⟨n, hAX hn⟩ hn)⟩
  · intro hc
    refine ⟨x.2, fun s hs => ?_⟩
    rw [SetLike.mem_coe, mem_map_center_subtype] at hs
    have := hc ⟨s, hAX hs.1⟩ (by
      rw [SetLike.mem_coe, mem_map_center_subtype]
      exact ⟨hs.1, fun n hn => Subtype.ext (hs.2 n hn)⟩)
    exact congrArg Subtype.val this

theorem triZ_le_triA : triZ k ≤ triA k := by
  rintro _ ⟨z, rfl⟩
  exact ⟨0, 0, z, rfl⟩

theorem triA_le_triAK : triA k ≤ triAK μ := by
  rw [triAK_eq_sup]
  exact le_sup_left

theorem commutator_mem_triA (g h : triX μ) :
    (g * h)⁻¹ * (h * g) ∈ (triA k).subgroupOf (triX μ) := by
  rw [← ker_diagHom, MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul,
    mul_comm (diagHom μ h), inv_mul_cancel]

theorem pow_mem_triA {p : ℕ} (hμ : ∀ a ∈ μ, a ^ p = 1) (g : triX μ) :
    g ^ p ∈ (triA k).subgroupOf (triX μ) := by
  rw [← ker_diagHom, MonoidHom.mem_ker, map_pow]
  obtain ⟨x, y, z, a, ha, b, hb, hg⟩ := g.2
  rw [diagHom_eq μ hg, Prod.pow_mk, hμ a ha, hμ b hb]
  rfl

section Image

variable {G : Type*} [Group G] (π : SL(3, k) →* G)

theorem mem_center_map_triA (hinj : Set.InjOn π (triA k)) {s : G} :
    s ∈ (Subgroup.center ((triA k).map π)).map ((triA k).map π).subtype ↔
      ∃ w ∈ triZ k, π w = s := by
  rw [mem_map_center_subtype]
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, hc⟩
    refine ⟨a, ?_, rfl⟩
    rw [← center_triA]
    refine ⟨⟨a, ha⟩, Subgroup.mem_center_iff.2 fun b => Subtype.ext ?_, rfl⟩
    apply hinj ((triA k).mul_mem b.2 ha) ((triA k).mul_mem ha b.2)
    rw [map_mul, map_mul]
    exact hc _ ⟨(b : SL(3, k)), b.2, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    have hwA : w ∈ triA k := triZ_le_triA hw
    refine ⟨⟨w, hwA, rfl⟩, ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    rw [← center_triA] at hw
    obtain ⟨c, hc, rfl⟩ := hw
    have := congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨b, hb⟩)
    rw [← map_mul, ← map_mul]
    exact congrArg π this

theorem centralizer_center_map_eq (hinj : Set.InjOn π (triX μ)) :
    (triX μ).map π ⊓ Subgroup.centralizer
      ((Subgroup.center ((triA k).map π)).map ((triA k).map π).subtype : Set G) =
      (triAK μ).map π := by
  have hinjA : Set.InjOn π (triA k) := hinj.mono (triA_le_triX μ)
  ext x
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨⟨g, hg, rfl⟩, hc⟩
    refine ⟨g, ?_, rfl⟩
    rw [← triX_inf_centralizer μ]
    refine ⟨hg, Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩
    have hwX : w ∈ triX μ := triA_le_triX μ (triZ_le_triA hw)
    apply hinj ((triX μ).mul_mem hwX hg) ((triX μ).mul_mem hg hwX)
    rw [map_mul, map_mul]
    exact hc _ ((mem_center_map_triA π hinjA).2 ⟨w, hw, rfl⟩)
  · rintro ⟨g, hg, rfl⟩
    rw [← triX_inf_centralizer μ] at hg
    refine ⟨⟨g, hg.1, rfl⟩, fun s hs => ?_⟩
    obtain ⟨w, hw, rfl⟩ := (mem_center_map_triA π hinjA).1 hs
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hg.2 w hw]

end Image

theorem triangular_three_space_characteristic_prime_line {k : Type*} [Field k] [Finite k]
    [CharP k 2] {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) {l : kˣ} (hl : orderOf l = p)
    {μ : Subgroup kˣ} (hμ : μ = Subgroup.zpowers l) {G : Type*} [Group G] (π : SL(3, k) →* G)
    (hπ : ∀ g ∈ π.ker, ∃ c : kˣ, c ^ 3 = 1 ∧ (g : Matrix (Fin 3) (Fin 3) k) = (c : k) • 1)
    {Xb Ab Y : Subgroup G} (hXb : Xb = (triX μ).map π) (hAb : Ab = (triA k).map π)
    (hY : Y = Xb ⊓ Subgroup.centralizer ((Subgroup.center Ab).map Ab.subtype : Set G)) :
    (triX μ : Set SL(3, k)) = (triA k : Set SL(3, k)) * (triP μ : Set SL(3, k)) ∧
      Set.InjOn π (triX μ) ∧ CFSG.pCore 2 (triX μ) = (triA k).subgroupOf (triX μ) ∧
      IsElementaryAbelian p (triP μ) ∧ Nat.card (triP μ) = p ^ 2 ∧
      CFSG.pCore 2 Xb = Ab.subgroupOf Xb ∧ Ab ≤ Y ∧ (Y.subgroupOf Xb).Characteristic ∧
      Ab.relIndex Y = p ∧ Y.relIndex Xb = p ∧ Y = (triA k ⊔ triK μ).map π ∧
      IsElementaryAbelian p (Xb ⧸ CFSG.pCore 2 Xb) ∧ Nat.card (Xb ⧸ CFSG.pCore 2 Xb) = p ^ 2 ∧
      Nat.card ((Y.subgroupOf Xb).map (QuotientGroup.mk' (CFSG.pCore 2 Xb))) = p ∧
      ∀ σ : MulAut Xb, ∃ hσ : (CFSG.pCore 2 Xb).map (σ : Xb →* Xb) = CFSG.pCore 2 Xb,
        ((Y.subgroupOf Xb).map (QuotientGroup.mk' (CFSG.pCore 2 Xb))).map
            (QuotientGroup.congr _ _ σ hσ : Xb ⧸ CFSG.pCore 2 Xb →* Xb ⧸ CFSG.pCore 2 Xb) =
          (Y.subgroupOf Xb).map (QuotientGroup.mk' (CFSG.pCore 2 Xb)) := by
  subst hXb hAb
  have hp0 : 0 < p := hp.out.pos
  have hμp : ∀ a ∈ μ, a ^ p = 1 := fun a ha => by
    rw [hμ] at ha
    exact orderOf_dvd_iff_pow_eq_one.1 (hl ▸ orderOf_dvd_of_mem_zpowers ha)
  have hcardμ : Nat.card μ = p := by rw [hμ, Nat.card_zpowers, hl]
  have hp3 : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp.out).2 (by omega)
  have hodd : ∀ a ∈ μ, ∀ m : ℕ, a ^ (2 ^ m) = 1 → a = 1 := fun a ha m hm => by
    have hcop : Nat.Coprime p (2 ^ m) :=
      Nat.Coprime.pow_right m ((Nat.coprime_primes hp.out Nat.prime_two).2 (by omega))
    have := pow_gcd_eq_one.2 ⟨hμp a ha, hm⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
  have hinj : Set.InjOn π (triX μ) := injOn_triX μ π hμp hp3 hπ
  have hinjA : Set.InjOn π (triA k) := hinj.mono (triA_le_triX μ)
  have hinjAK : Set.InjOn π (triAK μ) := hinj.mono (triAK_le_triX μ)
  have hpX : CFSG.pCore 2 (triX μ) = (triA k).subgroupOf (triX μ) := pCore_triX μ hodd
  have hpXb : CFSG.pCore 2 ((triX μ).map π) = ((triA k).map π).subgroupOf ((triX μ).map π) :=
    pCore_map_of_injOn π hinj (triA_le_triX μ) hpX
  have hYeq : Y = (triAK μ).map π := hY.trans (centralizer_center_map_eq μ π hinj)
  have hAbY : (triA k).map π ≤ Y := by
    rw [hYeq]
    exact Subgroup.map_mono (triA_le_triAK μ)
  have hYXb : Y ≤ (triX μ).map π := by
    rw [hY]
    exact inf_le_left
  have hAbXb : (triA k).map π ≤ (triX μ).map π := Subgroup.map_mono (triA_le_triX μ)
  have hchar : (Y.subgroupOf ((triX μ).map π)).Characteristic := by
    rw [hY, subgroupOf_centralizer_eq hAbXb, ← hpXb]
    infer_instance
  have hq : 0 < Nat.card k ^ 3 := pow_pos Nat.card_pos 3
  have hAbcard : Nat.card ((triA k).map π) = Nat.card k ^ 3 := by
    rw [card_map_of_injOn π hinjA, card_triA]
  have hYcard : Nat.card Y = Nat.card k ^ 3 * p := by
    rw [hYeq, card_map_of_injOn π hinjAK, card_triAK, hcardμ]
  have hXbcard : Nat.card ((triX μ).map π) = Nat.card k ^ 3 * p ^ 2 := by
    rw [card_map_of_injOn π hinj, card_triX, hcardμ]
  have hrel1 : ((triA k).map π).relIndex Y = p := by
    have h := Subgroup.relIndex_mul_card (H := (triA k).map π) (K := Y)
    rw [inf_of_le_left hAbY, hAbcard, hYcard] at h
    exact Nat.eq_of_mul_eq_mul_right hq (by rw [h, mul_comm])
  have hrel2 : Y.relIndex ((triX μ).map π) = p := by
    have h := Subgroup.relIndex_mul_card (H := Y) (K := (triX μ).map π)
    rw [inf_of_le_left hYXb, hYcard, hXbcard] at h
    refine Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hq hp0) ?_
    rw [h]
    ring
  have hmemN : ∀ g : triX μ, g ∈ (triA k).subgroupOf (triX μ) →
      mapIso π hinj g ∈ CFSG.pCore 2 ((triX μ).map π) := by
    intro g hg
    rw [hpXb, ← map_subgroupOf_mapIso π hinj (triA_le_triX μ)]
    exact Subgroup.mem_map_of_mem _ hg
  have helem : IsElementaryAbelian p ((triX μ).map π ⧸ CFSG.pCore 2 ((triX μ).map π)) := by
    refine isElementaryAbelian_quotient _ (fun x y => ?_) (fun x => ?_)
    · obtain ⟨g, rfl⟩ := (mapIso π hinj).surjective x
      obtain ⟨h, rfl⟩ := (mapIso π hinj).surjective y
      rw [← map_mul, ← map_mul, ← map_inv, ← map_mul]
      exact hmemN _ (commutator_mem_triA μ g h)
    · obtain ⟨g, rfl⟩ := (mapIso π hinj).surjective x
      rw [← map_pow]
      exact hmemN _ (pow_mem_triA μ hμp g)
  have hNcard : Nat.card ((triX μ).map π ⧸ CFSG.pCore 2 ((triX μ).map π)) = p ^ 2 := by
    change (CFSG.pCore 2 ((triX μ).map π)).index = p ^ 2
    rw [hpXb]
    change ((triA k).map π).relIndex ((triX μ).map π) = p ^ 2
    rw [← Subgroup.relIndex_mul_relIndex _ _ _ hAbY hYXb, hrel1, hrel2, pow_two]
  have hNY : CFSG.pCore 2 ((triX μ).map π) ≤ Y.subgroupOf ((triX μ).map π) := by
    rw [hpXb]
    exact fun x hx => hAbY hx
  have hYbar : Nat.card ((Y.subgroupOf ((triX μ).map π)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ((triX μ).map π)))) = p := by
    have hindex := Subgroup.index_map_eq (Y.subgroupOf ((triX μ).map π))
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ((triX μ).map π)))
      (by rw [QuotientGroup.ker_mk']; exact hNY)
    have h := Subgroup.card_mul_index ((Y.subgroupOf ((triX μ).map π)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ((triX μ).map π))))
    rw [hindex, hNcard] at h
    change _ * Y.relIndex ((triX μ).map π) = _ at h
    rw [hrel2] at h
    exact Nat.eq_of_mul_eq_mul_right hp0 (by rw [h, pow_two])
  refine ⟨coe_triX μ, hinj, hpX, isElementaryAbelian_triP μ hμp, by rw [card_triP, hcardμ],
    hpXb, hAbY, hchar, hrel1, hrel2, by rw [hYeq, triAK_eq_sup], helem, hNcard, hYbar,
    fun σ => ?_⟩
  have hσ : (CFSG.pCore 2 ((triX μ).map π)).map (σ : (triX μ).map π →* (triX μ).map π) =
      CFSG.pCore 2 ((triX μ).map π) :=
    Subgroup.characteristic_iff_map_eq.1 inferInstance σ
  refine ⟨hσ, ?_⟩
  have hYσ : (Y.subgroupOf ((triX μ).map π)).map (σ : (triX μ).map π →* (triX μ).map π) =
      Y.subgroupOf ((triX μ).map π) :=
    Subgroup.characteristic_iff_map_eq.1 hchar σ
  have hcomp : (QuotientGroup.congr _ _ σ hσ :
        (triX μ).map π ⧸ CFSG.pCore 2 ((triX μ).map π) →*
          (triX μ).map π ⧸ CFSG.pCore 2 ((triX μ).map π)).comp
        (QuotientGroup.mk' (CFSG.pCore 2 ((triX μ).map π))) =
      (QuotientGroup.mk' (CFSG.pCore 2 ((triX μ).map π))).comp
        (σ : (triX μ).map π →* (triX μ).map π) := by
    ext x
    exact QuotientGroup.congr_mk _ _ σ hσ x
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hYσ]

end CFSG.Quasithin.SteinbergBQ
