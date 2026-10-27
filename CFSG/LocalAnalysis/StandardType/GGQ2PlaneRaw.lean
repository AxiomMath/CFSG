module

public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.StandardType.GGQ2Frame.PlaneRaw

open CFSG.Assembly
open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

abbrev F : Type := ZMod 3

abbrev V (t : ℕ) : Type := Fin t → F

inductive PlaneKind where
  | linear (epsilon : Fin 2)
  | symplectic
  | orthogonal (delta : Fin 2)
  deriving DecidableEq

namespace PlaneKind

@[expose]
def natDim (k : PlaneKind) (t : ℕ) : ℕ :=
  match k with
  | .linear ε => 2 * t + ε.val
  | .symplectic => 2 * t
  | .orthogonal δ => 2 * t + 2 * δ.val

end PlaneKind

inductive Code (t : ℕ) where
  | zero (S : Finset (Fin t))
  | extension (e : V t)
  deriving DecidableEq

namespace Code

@[expose]
def extSupport {t : ℕ} (e : V t) : Finset (Fin t) :=
  Finset.univ.filter fun i => e i ≠ 0

@[expose]
def support {t : ℕ} : Code t → Finset (Fin t)
  | .zero S => S
  | .extension e => extSupport e

end Code

instance instFintypeCode {t : ℕ} : Fintype (Code t) :=
  Fintype.ofEquiv (Finset (Fin t) ⊕ V t)
    { toFun := fun
        | .inl S => Code.zero S
        | .inr e => Code.extension e
      invFun := fun
        | .zero S => .inl S
        | .extension e => .inr e
      left_inv := by rintro (S | e) <;> rfl
      right_inv := by rintro (S | e) <;> rfl }

@[expose]
def vSupport {t : ℕ} (v : V t) : Finset (Fin t) :=
  Finset.univ.filter fun i => v i ≠ 0

@[simp] theorem mem_extSupport {t : ℕ} (e : V t) (i : Fin t) :
    i ∈ Code.extSupport e ↔ e i ≠ 0 := by
  simp [Code.extSupport]

@[simp] theorem mem_vSupport {t : ℕ} (v : V t) (i : Fin t) :
    i ∈ vSupport v ↔ v i ≠ 0 := by
  simp [vSupport]

@[expose]
def admissible {t : ℕ} (k : PlaneKind) : Code t → Prop
  | .zero S =>
      match k with
      | .linear ε => 3 ≤ 2 * S.card + ε.val
      | .symplectic => 2 ≤ S.card
      | .orthogonal δ =>
          (Even S.card ∧ 3 ≤ S.card + δ.val) ∨ (Odd S.card ∧ 2 ≤ S.card + δ.val)
  | .extension e =>
      e ≠ 0 ∧
        match k with
        | .linear _ => 2 ≤ (Code.extSupport e).card
        | .symplectic => 4 ≤ (Code.extSupport e).card
        | .orthogonal _ => 4 ≤ (Code.extSupport e).card

@[expose]
def label {t : ℕ} (k : PlaneKind) : Code t → LargeEvenLabel
  | .zero S =>
      match k with
      | .linear ε => ⟨.A, 2 * S.card + ε.val - 1, 1⟩
      | .symplectic => if S.card = 2 then ⟨.B2der, 0, 1⟩ else ⟨.C, S.card, 1⟩
      | .orthogonal δ =>
          if Even S.card then ⟨.D, S.card + δ.val, 1⟩ else ⟨.twD, S.card + δ.val, 1⟩
  | .extension e =>
      match k with
      | .linear _ => ⟨.A, (Code.extSupport e).card - 1, 2⟩
      | .symplectic => ⟨.twA, (Code.extSupport e).card - 1, 1⟩
      | .orthogonal _ => ⟨.twA, (Code.extSupport e).card - 1, 1⟩

@[expose]
def coordProj {t : ℕ} (i : Fin t) : V t →ₗ[F] F := LinearMap.proj i

@[simp] theorem coordProj_apply {t : ℕ} (i : Fin t) (v : V t) :
    coordProj i v = v i :=
  LinearMap.proj_apply i v

@[expose]
def evalRestr {t : ℕ} (U : Submodule F (V t)) (i : Fin t) : U →ₗ[F] F :=
  (coordProj i).comp U.subtype

@[expose]
def sumForm {t : ℕ} (e : V t) : V t →ₗ[F] F where
  toFun v := ∑ i, e i * v i
  map_add' := by
    intro a b
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c a
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

@[simp] theorem sumForm_apply {t : ℕ} (e v : V t) :
    sumForm e v = ∑ i, e i * v i := rfl

@[expose]
def occurs {t : ℕ} (U : Submodule F (V t)) : Code t → Prop
  | .zero S => ∀ i : Fin t, i ∈ S ↔ ∀ u : U, (u : V t) i = 0
  | .extension e =>
      e ≠ 0 ∧ ∃ χ : U →ₗ[F] F, χ ≠ 0 ∧
        (∀ i : Fin t, e i ≠ 0 → evalRestr U i = e i • χ) ∧
        (∀ j : Fin t, e j = 0 →
          evalRestr U j ≠ χ ∧ evalRestr U j ≠ -χ)

@[expose]
def centZero {t : ℕ} (S : Finset (Fin t)) : Submodule F (V t) :=
  ⨅ i : {i : Fin t // i ∈ S}, LinearMap.ker (coordProj i.1)

@[expose]
def insideZero {t : ℕ} (S : Finset (Fin t)) : Submodule F (V t) :=
  ⨅ i : {i : Fin t // i ∉ S}, LinearMap.ker (coordProj i.1)

@[expose]
def centExt {t : ℕ} (e : V t) : Submodule F (V t) where
  carrier := {v | ∀ i ∈ Code.extSupport e, ∀ j ∈ Code.extSupport e, e i * v i = e j * v j}
  zero_mem' := by
    intro i _ j _
    simp
  add_mem' := by
    intro a b ha hb i hi j hj
    simp only [Pi.add_apply]
    rw [mul_add, mul_add, ha i hi j hj, hb i hi j hj]
  smul_mem' := by
    intro c x hx i hi j hj
    simp only [Pi.smul_apply, smul_eq_mul]
    calc e i * (c * x i) = c * (e i * x i) := mul_left_comm (e i) c (x i)
      _ = c * (e j * x j) := by rw [hx i hi j hj]
      _ = e j * (c * x j) := (mul_left_comm (e j) c (x j)).symm

@[expose]
def insideExt {t : ℕ} (e : V t) : Submodule F (V t) :=
  insideZero (Code.extSupport e) ⊓ LinearMap.ker (sumForm e)

theorem mem_centZero {t : ℕ} (S : Finset (Fin t)) (v : V t) :
    v ∈ centZero S ↔ ∀ i ∈ S, v i = 0 := by
  rw [centZero, Submodule.mem_iInf]
  constructor
  · intro h i hi
    have := h ⟨i, hi⟩
    simpa only [LinearMap.mem_ker, coordProj_apply] using this
  · intro h i
    simpa only [LinearMap.mem_ker, coordProj_apply] using h i.1 i.2

theorem mem_insideZero' {t : ℕ} (S : Finset (Fin t)) (v : V t) :
    v ∈ insideZero S ↔ ∀ i, i ∉ S → v i = 0 := by
  rw [insideZero, Submodule.mem_iInf]
  constructor
  · intro h i hi
    have := h ⟨i, hi⟩
    simpa only [LinearMap.mem_ker, coordProj_apply] using this
  · intro h i
    simpa only [LinearMap.mem_ker, coordProj_apply] using h i.1 i.2

theorem mem_insideZero {t : ℕ} (S : Finset (Fin t)) (v : V t) :
    v ∈ insideZero S ↔ vSupport v ⊆ S := by
  rw [mem_insideZero']
  constructor
  · intro h i hi
    have hne : v i ≠ 0 := by simpa [vSupport] using hi
    by_contra hS
    exact hne (h i hS)
  · intro h i hi
    by_contra hne
    have hmem : i ∈ vSupport v := by simpa [vSupport] using hne
    exact hi (Finset.subset_iff.mp h hmem)

theorem mem_centExt {t : ℕ} (e : V t) (v : V t) :
    v ∈ centExt e ↔
      ∀ i ∈ Code.extSupport e, ∀ j ∈ Code.extSupport e, e i * v i = e j * v j :=
  Iff.rfl

theorem mem_insideExt {t : ℕ} (e : V t) (v : V t) :
    v ∈ insideExt e ↔ (∀ i, e i = 0 → v i = 0) ∧ ∑ i, e i * v i = 0 := by
  rw [insideExt, Submodule.mem_inf, mem_insideZero']
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro i hi
      exact h1 i (by simp [Code.extSupport, hi])
    · rwa [LinearMap.mem_ker, sumForm_apply] at h2
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · intro i hi
      exact h1 i (by simpa [Code.extSupport] using hi)
    · rw [LinearMap.mem_ker, sumForm_apply]
      exact h2

@[expose]
def cent {t : ℕ} (_k : PlaneKind) : Code t → Submodule F (V t)
  | .zero S => centZero S
  | .extension e => centExt e

@[expose]
def inside {t : ℕ} (_k : PlaneKind) : Code t → Submodule F (V t)
  | .zero S => insideZero S
  | .extension e => insideExt e

@[simp] theorem mem_cent_zero {t : ℕ} (k : PlaneKind) (S : Finset (Fin t)) (v : V t) :
    v ∈ cent k (Code.zero S) ↔ ∀ i ∈ S, v i = 0 := by
  have h : cent k (Code.zero S) = centZero S := rfl
  rw [h]
  exact mem_centZero S v

@[simp] theorem mem_cent_extension {t : ℕ} (k : PlaneKind) (e : V t) (v : V t) :
    v ∈ cent k (Code.extension e) ↔
      ∀ i ∈ Code.extSupport e, ∀ j ∈ Code.extSupport e, e i * v i = e j * v j := by
  have h : cent k (Code.extension e) = centExt e := rfl
  rw [h]
  exact mem_centExt e v

@[simp] theorem mem_inside_zero {t : ℕ} (k : PlaneKind) (S : Finset (Fin t)) (v : V t) :
    v ∈ inside k (Code.zero S) ↔ vSupport v ⊆ S := by
  have h : inside k (Code.zero S) = insideZero S := rfl
  rw [h]
  exact mem_insideZero S v

@[simp] theorem mem_inside_extension {t : ℕ} (k : PlaneKind) (e : V t) (v : V t) :
    v ∈ inside k (Code.extension e) ↔
      (∀ i, e i = 0 → v i = 0) ∧ ∑ i, e i * v i = 0 := by
  have h : inside k (Code.extension e) = insideExt e := rfl
  rw [h]
  exact mem_insideExt e v

end

end CFSG.StandardType.GGQ2Frame.PlaneRaw
