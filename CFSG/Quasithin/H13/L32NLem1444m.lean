module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.Quasithin.H13

namespace L1444

open Matrix

@[expose] def mR : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![0, 1, 0, 0; 1, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 1]

@[expose] def mB : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 0, 1, 0; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1]

@[expose] def mU : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, 1, 0, 0; 0, 1, 0, 0; 0, 0, 1, 1; 0, 0, 0, 1]

@[expose] def mC (x₀ x₁ x₂ y₀ y₁ y₂ w₀ w₁ w₂ : ZMod 2) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  !![1, x₀, y₀, w₀; 0, x₁, y₁, w₁; 0, x₂, y₂, w₂; 0, 0, 0, 1]

@[expose] def IsGood (W : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Prop :=
  W *ᵥ ![1, 0, 0, 0] = ![1, 0, 0, 0] ∧ W ^ 7 = 1 ∧ W ≠ 1

instance : DecidablePred IsGood := fun W => by unfold IsGood; infer_instance

@[expose] def InUPlus (M N : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Prop :=
  M * N = M ∨ M * N = mB * M ∨ M * N = mU * M ∨ M * N = mU * mB * M

instance (M N : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Decidable (InUPlus M N) := by
  unfold InUPlus; infer_instance

@[expose] def Admissible (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Prop :=
  M * M * M = 1 ∧ InUPlus M mB ∧ InUPlus M mU

instance (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Decidable (Admissible M) := by
  unfold Admissible; infer_instance

@[expose] def word1 (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  mR * mR * M * M * mR * M * mR * M * mR

@[expose] def word2 (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2) :=
  mR * M * mR * M * mR * mB * M * M * mR

@[expose] def KeyInner (x₁ x₂ y₁ y₂ : ZMod 2) : Prop :=
  ∀ x₀ y₀ w₀ w₁ w₂ : ZMod 2, Admissible (mC x₀ x₁ x₂ y₀ y₁ y₂ w₀ w₁ w₂) →
    IsGood (word1 (mC x₀ x₁ x₂ y₀ y₁ y₂ w₀ w₁ w₂)) ∨
      IsGood (word2 (mC x₀ x₁ x₂ y₀ y₁ y₂ w₀ w₁ w₂))

instance (x₁ x₂ y₁ y₂ : ZMod 2) : Decidable (KeyInner x₁ x₂ y₁ y₂) := by
  unfold KeyInner; infer_instance

theorem key : ∀ x₁ x₂ y₁ y₂ : ZMod 2, ¬ (x₁ = 1 ∧ x₂ = 0) → ¬ (y₁ = 0 ∧ y₂ = 1) →
    ¬ (x₁ + y₁ = 1 ∧ x₂ + y₂ = 1) → KeyInner x₁ x₂ y₁ y₂ := by
  decide +kernel

variable {G : Type*} [Group G]

@[expose] def cp (e : Fin 4 → G) (v : Fin 4 → ZMod 2) : G :=
  e 0 ^ (v 0).val * e 1 ^ (v 1).val * e 2 ^ (v 2).val * e 3 ^ (v 3).val

theorem cp_vec (e : Fin 4 → G) (x₀ x₁ x₂ x₃ : ZMod 2) :
    cp e ![x₀, x₁, x₂, x₃] = e 0 ^ x₀.val * e 1 ^ x₁.val * e 2 ^ x₂.val * e 3 ^ x₃.val := rfl

theorem cp_eq_vec (e : Fin 4 → G) (v : Fin 4 → ZMod 2) (hv : v 3 = 0) :
    cp e v = cp e ![v 0, v 1, v 2, 0] := by
  rw [cp_vec, cp, hv]

theorem cp_vec_one (e : Fin 4 → G) (x₀ x₁ x₂ : ZMod 2) :
    cp e ![x₀, x₁, x₂, 1] = cp e ![x₀, x₁, x₂, 0] * e 3 := by
  rw [cp_vec, cp_vec]
  simp [show (1 : ZMod 2).val = 1 from rfl]

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

theorem val_zero2 : (0 : ZMod 2).val = 0 := rfl

theorem val_one2 : (1 : ZMod 2).val = 1 := rfl

theorem pow_val_add {g : G} (hg : g * g = 1) (x y : ZMod 2) :
    g ^ (x + y).val = g ^ x.val * g ^ y.val := by
  rcases zmod2_cases x with rfl | rfl <;> rcases zmod2_cases y with rfl | rfl
  · simp
  · simp
  · simp
  · rw [show (1 + 1 : ZMod 2) = 0 from rfl, val_zero2, val_one2, pow_zero, pow_one, hg]

theorem cp_zero (e : Fin 4 → G) : cp e 0 = 1 := by
  simp [cp]

theorem cp_col_one (e : Fin 4 → G) (i : Fin 4) :
    cp e (fun j => (1 : Matrix (Fin 4) (Fin 4) (ZMod 2)) j i) = e i := by
  fin_cases i <;> simp [cp, Matrix.one_apply, val_one2]

section Comm

variable {e : Fin 4 → G} (hc : ∀ i j, Commute (e i) (e j)) (h2 : ∀ i, e i * e i = 1)
include hc h2

theorem cp_add (v w : Fin 4 → ZMod 2) : cp e (v + w) = cp e v * cp e w := by
  have c : ∀ i j (m n : ℕ), Commute (e i ^ m) (e j ^ n) := fun i j m n => (hc i j).pow_pow m n
  simp only [cp, Pi.add_apply, pow_val_add (h2 _), mul_assoc]
  congr 1
  rw [(c 0 1 (w 0).val (v 1).val).left_comm]
  congr 1
  rw [(c 1 2 (w 1).val (v 2).val).left_comm, (c 0 2 (w 0).val (v 2).val).left_comm]
  congr 1
  rw [(c 2 3 (w 2).val (v 3).val).left_comm, (c 1 3 (w 1).val (v 3).val).left_comm,
    (c 0 3 (w 0).val (v 3).val).left_comm]

omit hc h2 in
theorem cp_smul (k : ZMod 2) (v : Fin 4 → ZMod 2) : cp e (k • v) = cp e v ^ k.val := by
  rcases zmod2_cases k with rfl | rfl
  · rw [zero_smul, cp_zero, val_zero2, pow_zero]
  · rw [one_smul, val_one2, pow_one]

theorem cp_mul_self (v : Fin 4 → ZMod 2) : cp e v * cp e v = 1 := by
  have hvv : v + v = 0 := by
    funext i
    have : ∀ x : ZMod 2, x + x = 0 := by decide
    exact this (v i)
  rw [← cp_add hc h2, hvv, cp_zero]

theorem cp_conj {γ : G} {M : Matrix (Fin 4) (Fin 4) (ZMod 2)}
    (hγ : ∀ i, γ * e i * γ⁻¹ = cp e (fun j => M j i)) (v : Fin 4 → ZMod 2) :
    γ * cp e v * γ⁻¹ = cp e (M *ᵥ v) := by
  have hpow : ∀ i (n : ℕ), γ * e i ^ n * γ⁻¹ = (cp e (fun j => M j i)) ^ n := fun i n => by
    rw [← hγ i, conj_pow]
  have hsplit : γ * cp e v * γ⁻¹ = (γ * e 0 ^ (v 0).val * γ⁻¹) * (γ * e 1 ^ (v 1).val * γ⁻¹) *
      (γ * e 2 ^ (v 2).val * γ⁻¹) * (γ * e 3 ^ (v 3).val * γ⁻¹) := by
    simp only [cp]
    group
  rw [hsplit, hpow, hpow, hpow, hpow, ← cp_smul, ← cp_smul, ← cp_smul, ← cp_smul,
    ← cp_add hc h2, ← cp_add hc h2, ← cp_add hc h2]
  congr 1
  funext j
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_four, mul_comm]

theorem cp_injective (hind : ∀ v, cp e v = 1 → v = 0) : Function.Injective (cp e) := by
  intro v w h
  have h0 := hind (v + w) (by rw [cp_add hc h2, h, cp_mul_self hc h2])
  funext i
  have : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
  exact this (v i) (w i) (congrFun h0 i)

theorem cp_comm (v w : Fin 4 → ZMod 2) : Commute (cp e v) (cp e w) := by
  unfold Commute SemiconjBy
  rw [← cp_add hc h2, ← cp_add hc h2, add_comm]

theorem cp_inv (v : Fin 4 → ZMod 2) : (cp e v)⁻¹ = cp e v :=
  inv_eq_of_mul_eq_one_right (cp_mul_self hc h2 v)

end Comm

section Sub

variable (e : Fin 4 → G) (hc : ∀ i j, Commute (e i) (e j)) (h2 : ∀ i, e i * e i = 1)

@[expose] def cpRange : Subgroup G where
  carrier := Set.range (cp e)
  mul_mem' := by
    rintro _ _ ⟨v, rfl⟩ ⟨w, rfl⟩
    exact ⟨v + w, cp_add hc h2 v w⟩
  one_mem' := ⟨0, cp_zero e⟩
  inv_mem' := by
    rintro _ ⟨v, rfl⟩
    exact ⟨v, (cp_inv hc h2 v).symm⟩

@[expose] def cpPlane : Subgroup G where
  carrier := {x | ∃ v : Fin 4 → ZMod 2, v 3 = 0 ∧ cp e v = x}
  mul_mem' := by
    rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨v + w, by simp [hv, hw], cp_add hc h2 v w⟩
  one_mem' := ⟨0, rfl, cp_zero e⟩
  inv_mem' := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨v, hv, (cp_inv hc h2 v).symm⟩

theorem card_cpRange (hinj : Function.Injective (cp e)) : 16 ≤ Nat.card (cpRange e hc h2) := by
  have : Finite (cpRange e hc h2) :=
    Finite.of_surjective (fun v => (⟨cp e v, v, rfl⟩ : cpRange e hc h2)) (by
      rintro ⟨_, v, rfl⟩
      exact ⟨v, rfl⟩)
  have h := Nat.card_le_card_of_injective (fun v => (⟨cp e v, v, rfl⟩ : cpRange e hc h2))
    fun v w hvw => hinj (congrArg Subtype.val hvw)
  have h16 : Nat.card (Fin 4 → ZMod 2) = 16 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  omega

theorem card_cpPlane (hinj : Function.Injective (cp e)) : 8 ≤ Nat.card (cpPlane e hc h2) := by
  have : Finite (cpPlane e hc h2) :=
    Finite.of_surjective
      (fun v : {v : Fin 4 → ZMod 2 // v 3 = 0} => (⟨cp e v, v, v.2, rfl⟩ : cpPlane e hc h2)) (by
      rintro ⟨_, v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩)
  have h := Nat.card_le_card_of_injective
    (fun v : {v : Fin 4 → ZMod 2 // v 3 = 0} => (⟨cp e v, v, v.2, rfl⟩ : cpPlane e hc h2))
    fun v w hvw => Subtype.ext (hinj (congrArg Subtype.val hvw))
  have h8 : Nat.card {v : Fin 4 → ZMod 2 // v 3 = 0} = 8 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  omega

end Sub

theorem cp_eq_one {e : Fin 4 → G} {K₁ K₂ K₃ : Subgroup G} (h0 : e 0 ≠ 1) (h01 : e 0 ∈ K₁)
    (h1 : e 1 ∉ K₁) (h02 : e 0 ∈ K₂) (h12 : e 1 ∈ K₂) (h2 : e 2 ∉ K₂) (h03 : e 0 ∈ K₃)
    (h13 : e 1 ∈ K₃) (h23 : e 2 ∈ K₃) (h3 : e 3 ∉ K₃) (v : Fin 4 → ZMod 2) (hv : cp e v = 1) :
    v = 0 := by
  simp only [cp] at hv
  have hv3 : v 3 = 0 := by
    rcases zmod2_cases (v 3) with h | h
    · exact h
    · exfalso
      rw [h, val_one2, pow_one] at hv
      apply h3
      have e3 : e 3 = (e 0 ^ (v 0).val * e 1 ^ (v 1).val * e 2 ^ (v 2).val)⁻¹ :=
        eq_inv_of_mul_eq_one_right hv
      rw [e3]
      exact K₃.inv_mem (K₃.mul_mem (K₃.mul_mem (K₃.pow_mem h03 _) (K₃.pow_mem h13 _))
        (K₃.pow_mem h23 _))
  rw [hv3, val_zero2, pow_zero, mul_one] at hv
  have hv2 : v 2 = 0 := by
    rcases zmod2_cases (v 2) with h | h
    · exact h
    · exfalso
      rw [h, val_one2, pow_one] at hv
      apply h2
      rw [eq_inv_of_mul_eq_one_right hv]
      exact K₂.inv_mem (K₂.mul_mem (K₂.pow_mem h02 _) (K₂.pow_mem h12 _))
  rw [hv2, val_zero2, pow_zero, mul_one] at hv
  have hv1 : v 1 = 0 := by
    rcases zmod2_cases (v 1) with h | h
    · exact h
    · exfalso
      rw [h, val_one2, pow_one] at hv
      apply h1
      rw [eq_inv_of_mul_eq_one_right hv]
      exact K₁.inv_mem (K₁.pow_mem h01 _)
  rw [hv1, val_zero2, pow_zero, mul_one] at hv
  have hv0 : v 0 = 0 := by
    rcases zmod2_cases (v 0) with h | h
    · exact h
    · exfalso
      rw [h, val_one2, pow_one] at hv
      exact h0 hv
  funext i
  fin_cases i
  · exact hv0
  · exact hv1
  · exact hv2
  · exact hv3

@[expose] def ActsAs (e : Fin 4 → G) (γ : G) (M : Matrix (Fin 4) (Fin 4) (ZMod 2)) : Prop :=
  ∀ v, γ * cp e v * γ⁻¹ = cp e (M *ᵥ v)

variable {e : Fin 4 → G}

theorem actsAs_of_cols (hc : ∀ i j, Commute (e i) (e j)) (h2 : ∀ i, e i * e i = 1) {γ : G}
    {M : Matrix (Fin 4) (Fin 4) (ZMod 2)} (hγ : ∀ i, γ * e i * γ⁻¹ = cp e (fun j => M j i)) :
    ActsAs e γ M :=
  cp_conj hc h2 hγ

theorem ActsAs.mul {γ δ : G} {M N : Matrix (Fin 4) (Fin 4) (ZMod 2)} (h₁ : ActsAs e γ M)
    (h₂ : ActsAs e δ N) : ActsAs e (γ * δ) (M * N) := fun v => by
  rw [show γ * δ * cp e v * (γ * δ)⁻¹ = γ * (δ * cp e v * δ⁻¹) * γ⁻¹ by group, h₂, h₁,
    mulVec_mulVec]

theorem actsAs_one : ActsAs e 1 1 := fun v => by simp

theorem ActsAs.pow {γ : G} {M : Matrix (Fin 4) (Fin 4) (ZMod 2)} (h : ActsAs e γ M) (n : ℕ) :
    ActsAs e (γ ^ n) (M ^ n) := by
  induction n with
  | zero => simpa using (actsAs_one : ActsAs e 1 1)
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact ih.mul h

theorem ActsAs.unique (hinj : Function.Injective (cp e)) {γ : G}
    {M N : Matrix (Fin 4) (Fin 4) (ZMod 2)} (h₁ : ActsAs e γ M) (h₂ : ActsAs e γ N) : M = N := by
  have h : ∀ v, M *ᵥ v = N *ᵥ v := fun v => hinj ((h₁ v).symm.trans (h₂ v))
  apply Matrix.toLin'.injective
  exact LinearMap.ext fun v => by simpa using h v

theorem actsAs_one_of_comm (hc : ∀ i j, Commute (e i) (e j)) (h2 : ∀ i, e i * e i = 1) {p : G}
    (hp : ∀ i, Commute p (e i)) : ActsAs e p 1 :=
  actsAs_of_cols hc h2 fun i => by
    rw [cp_col_one, (hp i).eq, mul_inv_cancel_right]

theorem seven_dvd_of_actsAs (hinj : Function.Injective (cp e)) {γ : G}
    {M : Matrix (Fin 4) (Fin 4) (ZMod 2)} (h : ActsAs e γ M) (h7 : M ^ 7 = 1) (h1 : M ≠ 1)
    {n : ℕ} (hn : γ ^ n = 1) : 7 ∣ n := by
  by_contra h7n
  have hMn : M ^ n = 1 := (h.pow n).unique hinj (by rw [hn]; exact actsAs_one)
  have hg : M ^ Nat.gcd 7 n = 1 := pow_gcd_eq_one.mpr ⟨h7, hMn⟩
  have hcop : Nat.gcd 7 n = 1 := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h7n
  rw [hcop, pow_one] at hg
  exact h1 hg

section Gens

variable (hc : ∀ i j, Commute (e i) (e j)) (h2 : ∀ i, e i * e i = 1)
include hc h2

theorem actsAs_R {r : G} (h0 : r * e 0 * r⁻¹ = e 1) (h1 : r * e 1 * r⁻¹ = e 0 * e 1)
    (h2' : r * e 2 * r⁻¹ = e 3) (h3 : r * e 3 * r⁻¹ = e 2 * e 3) : ActsAs e r mR :=
  actsAs_of_cols hc h2 fun i => by
    fin_cases i <;> simp [mR, cp, val_one2, h0, h1, h2', h3]

theorem actsAs_B {b : G} (h0 : b * e 0 * b⁻¹ = e 0) (h1 : b * e 1 * b⁻¹ = e 1)
    (h2' : b * e 2 * b⁻¹ = e 0 * e 2) (h3 : b * e 3 * b⁻¹ = e 1 * e 3) : ActsAs e b mB :=
  actsAs_of_cols hc h2 fun i => by
    fin_cases i <;> simp [mB, cp, val_one2, h0, h1, h2', h3]

theorem actsAs_U {u : G} (h0 : u * e 0 * u⁻¹ = e 0) (h1 : u * e 1 * u⁻¹ = e 0 * e 1)
    (h2' : u * e 2 * u⁻¹ = e 2) (h3 : u * e 3 * u⁻¹ = e 2 * e 3) : ActsAs e u mU :=
  actsAs_of_cols hc h2 fun i => by
    fin_cases i <;> simp [mU, cp, val_one2, h0, h1, h2', h3]

theorem actsAs_C {c : G} {x₀ x₁ x₂ y₀ y₁ y₂ w₀ w₁ w₂ : ZMod 2} (h0 : c * e 0 * c⁻¹ = e 0)
    (h1 : c * e 1 * c⁻¹ = cp e ![x₀, x₁, x₂, 0]) (h2' : c * e 2 * c⁻¹ = cp e ![y₀, y₁, y₂, 0])
    (h3 : c * e 3 * c⁻¹ = cp e ![w₀, w₁, w₂, 1]) :
    ActsAs e c (mC x₀ x₁ x₂ y₀ y₁ y₂ w₀ w₁ w₂) :=
  actsAs_of_cols hc h2 fun i => by
    fin_cases i <;> simp [mC, cp, val_one2, h0, h1, h2', h3]

theorem exists_seven (hind : ∀ v, cp e v = 1 → v = 0) {r b u c : G}
    {x₀ x₁ x₂ y₀ y₁ y₂ w₀ w₁ w₂ : ZMod 2} (hr : ActsAs e r mR) (hb : ActsAs e b mB)
    (hu : ActsAs e u mU) (hcM : ActsAs e c (mC x₀ x₁ x₂ y₀ y₁ y₂ w₀ w₁ w₂)) (hc3 : c ^ 3 = 1)
    (hfx : ¬ (x₁ = 1 ∧ x₂ = 0)) (hfy : ¬ (y₁ = 0 ∧ y₂ = 1))
    (hfxy : ¬ (x₁ + y₁ = 1 ∧ x₂ + y₂ = 1))
    (hcb : ActsAs e (c * b * c⁻¹) 1 ∨ ActsAs e (c * b * c⁻¹) mB ∨ ActsAs e (c * b * c⁻¹) mU ∨
      ActsAs e (c * b * c⁻¹) (mU * mB))
    (hcu : ActsAs e (c * u * c⁻¹) 1 ∨ ActsAs e (c * u * c⁻¹) mB ∨ ActsAs e (c * u * c⁻¹) mU ∨
      ActsAs e (c * u * c⁻¹) (mU * mB)) :
    ∃ γ : G, γ * e 0 * γ⁻¹ = e 0 ∧ ∀ n : ℕ, γ ^ n = 1 → 7 ∣ n := by
  have hinj := cp_injective hc h2 hind
  set M := mC x₀ x₁ x₂ y₀ y₁ y₂ w₀ w₁ w₂ with hM
  have hM3 : M * M * M = 1 := by
    have h := (hcM.pow 3).unique hinj (by rw [hc3]; exact actsAs_one)
    rwa [pow_three, ← mul_assoc] at h
  have hnorm : ∀ {y : G} {N : Matrix (Fin 4) (Fin 4) (ZMod 2)}, ActsAs e y N →
      (ActsAs e (c * y * c⁻¹) 1 ∨ ActsAs e (c * y * c⁻¹) mB ∨ ActsAs e (c * y * c⁻¹) mU ∨
        ActsAs e (c * y * c⁻¹) (mU * mB)) → InUPlus M N := by
    intro y N hy hcy
    have h1 : ActsAs e (c * y) (M * N) := hcM.mul hy
    have e1 : c * y = c * y * c⁻¹ * c := by group
    rcases hcy with h | h | h | h
    · left
      have h2 := h.mul hcM
      rw [← e1, one_mul] at h2
      exact h1.unique hinj h2
    · right; left
      have h2 := h.mul hcM
      rw [← e1] at h2
      exact h1.unique hinj h2
    · right; right; left
      have h2 := h.mul hcM
      rw [← e1] at h2
      exact h1.unique hinj h2
    · right; right; right
      have h2 := h.mul hcM
      rw [← e1] at h2
      exact h1.unique hinj h2
  have hadm : Admissible M := ⟨hM3, hnorm hb hcb, hnorm hu hcu⟩
  have he0 : cp e ![1, 0, 0, 0] = e 0 := by simp [cp, val_one2]
  have hgood : ∀ {γ : G} {W : Matrix (Fin 4) (Fin 4) (ZMod 2)}, ActsAs e γ W → IsGood W →
      ∃ γ : G, γ * e 0 * γ⁻¹ = e 0 ∧ ∀ n : ℕ, γ ^ n = 1 → 7 ∣ n := by
    intro γ W hγ ⟨hfix, h7, h1⟩
    refine ⟨γ, ?_, fun n hn => seven_dvd_of_actsAs hinj hγ h7 h1 hn⟩
    rw [← he0, hγ, hfix]
  rcases key x₁ x₂ y₁ y₂ hfx hfy hfxy x₀ y₀ w₀ w₁ w₂ hadm with h | h
  · exact hgood (((((((((hr.mul hr).mul hcM).mul hcM).mul hr).mul hcM).mul hr).mul hcM).mul
      hr)) h
  · exact hgood (((((((((hr.mul hcM).mul hr).mul hcM).mul hr).mul hb).mul hcM).mul hcM).mul
      hr)) h

end Gens

end L1444

end CFSG.Quasithin.H13
