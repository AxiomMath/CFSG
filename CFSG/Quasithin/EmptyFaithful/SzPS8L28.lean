module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.Quasithin.SzPS8

namespace L28

open Matrix MatrixGroups
open scoped Pointwise

section Matrices

variable {K : Type*} [Field K]

@[expose] def up (x : K) : SL(2, K) := ⟨!![1, x; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def dg (a : K) (ha : a ≠ 0) : SL(2, K) :=
  ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two_of, ha]⟩

@[simp] theorem up_00 (x : K) : (up x : SL(2, K)) 0 0 = 1 := rfl
@[simp] theorem up_01 (x : K) : (up x : SL(2, K)) 0 1 = x := rfl
@[simp] theorem up_10 (x : K) : (up x : SL(2, K)) 1 0 = 0 := rfl
@[simp] theorem up_11 (x : K) : (up x : SL(2, K)) 1 1 = 1 := rfl

@[simp] theorem dg_00 (a : K) (ha : a ≠ 0) : (dg a ha : SL(2, K)) 0 0 = a := rfl
@[simp] theorem dg_01 (a : K) (ha : a ≠ 0) : (dg a ha : SL(2, K)) 0 1 = 0 := rfl
@[simp] theorem dg_10 (a : K) (ha : a ≠ 0) : (dg a ha : SL(2, K)) 1 0 = 0 := rfl
@[simp] theorem dg_11 (a : K) (ha : a ≠ 0) : (dg a ha : SL(2, K)) 1 1 = a⁻¹ := rfl

theorem sl2_ext {A B : SL(2, K)} (h00 : A 0 0 = B 0 0) (h01 : A 0 1 = B 0 1)
    (h10 : A 1 0 = B 1 0) (h11 : A 1 1 = B 1 1) : A = B := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;> assumption

theorem up_mul (x y : K) : up x * up y = up (x + y) := by
  apply sl2_ext <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem up_zero : up (0 : K) = 1 := by
  apply sl2_ext <;> simp

theorem sl2_det (A : SL(2, K)) : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
  have := A.2
  rw [Matrix.det_fin_two] at this
  exact this

theorem sl2_inv_00 (A : SL(2, K)) : (A⁻¹ : SL(2, K)) 0 0 = A 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem sl2_inv_01 (A : SL(2, K)) : (A⁻¹ : SL(2, K)) 0 1 = - A 0 1 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem sl2_inv_10 (A : SL(2, K)) : (A⁻¹ : SL(2, K)) 1 0 = - A 1 0 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem sl2_inv_11 (A : SL(2, K)) : (A⁻¹ : SL(2, K)) 1 1 = A 0 0 := by
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]

theorem sl2_mul_00 (A B : SL(2, K)) :
    (A * B : SL(2, K)) 0 0 = A 0 0 * B 0 0 + A 0 1 * B 1 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2_mul_01 (A B : SL(2, K)) :
    (A * B : SL(2, K)) 0 1 = A 0 0 * B 0 1 + A 0 1 * B 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2_mul_10 (A B : SL(2, K)) :
    (A * B : SL(2, K)) 1 0 = A 1 0 * B 0 0 + A 1 1 * B 1 0 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2_mul_11 (A B : SL(2, K)) :
    (A * B : SL(2, K)) 1 1 = A 1 0 * B 0 1 + A 1 1 * B 1 1 := by
  simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]

theorem up_injective : Function.Injective (up : K → SL(2, K)) := by
  intro x y h
  have := congrArg (fun A : SL(2, K) => A 0 1) h
  simpa using this

@[expose] def upHom : Multiplicative K →* SL(2, K) where
  toFun x := up (Multiplicative.toAdd x)
  map_one' := by simpa using (up_zero : up (0 : K) = 1)
  map_mul' x y := by
    simp only [toAdd_mul]
    exact (up_mul _ _).symm

variable (K) in
@[expose] def U : Subgroup SL(2, K) := (upHom (K := K)).range

theorem mem_U_iff {g : SL(2, K)} : g ∈ U K ↔ g 0 0 = 1 ∧ g 1 0 = 0 ∧ g 1 1 = 1 := by
  constructor
  · rintro ⟨x, rfl⟩
    simp [upHom]
  · rintro ⟨h0, h1, h2⟩
    refine ⟨Multiplicative.ofAdd (g 0 1), ?_⟩
    apply sl2_ext <;> simp [upHom, h0, h1, h2]

theorem up_mem_U (x : K) : up x ∈ U K := mem_U_iff.mpr ⟨rfl, rfl, rfl⟩

theorem eq_up_of_mem_U {g : SL(2, K)} (hg : g ∈ U K) : g = up (g 0 1) := by
  obtain ⟨h0, h1, h2⟩ := mem_U_iff.mp hg
  apply sl2_ext <;> simp [h0, h1, h2]

theorem sl2_diag_mul {b : SL(2, K)} (hb : b 1 0 = 0) : b 0 0 * b 1 1 = 1 := by
  have := sl2_det b
  rw [hb] at this
  simpa using this

set_option linter.unusedSimpArgs false in
theorem conj_up {b : SL(2, K)} (hb : b 1 0 = 0) (y : K) :
    b * up y * b⁻¹ = up (b 0 0 ^ 2 * y) := by
  have hd := sl2_diag_mul hb
  apply sl2_ext
  · simp [sl2_mul_00, sl2_mul_01, sl2_mul_10, sl2_mul_11, sl2_inv_00, sl2_inv_01, sl2_inv_10,
      sl2_inv_11, hb]
    linear_combination hd
  · simp [sl2_mul_00, sl2_mul_01, sl2_mul_10, sl2_mul_11, sl2_inv_00, sl2_inv_01, sl2_inv_10,
      sl2_inv_11, hb]
    ring
  · simp [sl2_mul_00, sl2_mul_01, sl2_mul_10, sl2_mul_11, sl2_inv_00, sl2_inv_01, sl2_inv_10,
      sl2_inv_11, hb]
  · simp [sl2_mul_00, sl2_mul_01, sl2_mul_10, sl2_mul_11, sl2_inv_00, sl2_inv_01, sl2_inv_10,
      sl2_inv_11, hb]
    linear_combination hd

theorem entry10_of_mem_normalizer {b : SL(2, K)}
    (hb : b ∈ Subgroup.normalizer ((U K : Subgroup SL(2, K)) : Set SL(2, K))) : b 1 0 = 0 := by
  have h := (Subgroup.mem_normalizer_iff.mp hb (up 1)).mp (up_mem_U 1)
  obtain ⟨-, h10, -⟩ := mem_U_iff.mp h
  simp [sl2_mul_10, sl2_mul_11, sl2_inv_00, sl2_inv_10] at h10
  have : b 1 0 * b 1 0 = 0 := by linear_combination -h10
  exact mul_self_eq_zero.mp this

theorem mem_normalizer_of_entry10 {b : SL(2, K)} (hb : b 1 0 = 0) :
    b ∈ Subgroup.normalizer ((U K : Subgroup SL(2, K)) : Set SL(2, K)) := by
  have hbi : (b⁻¹ : SL(2, K)) 1 0 = 0 := by rw [sl2_inv_10, hb, neg_zero]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [eq_up_of_mem_U hh, conj_up hb]
    exact up_mem_U _
  · intro hh
    have h2 : b⁻¹ * (b * h * b⁻¹) * b⁻¹⁻¹ ∈ U K := by
      rw [eq_up_of_mem_U hh, conj_up hbi]
      exact up_mem_U _
    simpa [mul_assoc] using h2

end Matrices

section Auto

variable {K : Type*} [Field K] (α : MulAut SL(2, K))

def tau (y : K) : K := (α (up y) : SL(2, K)) 0 1

variable {α}

theorem alpha_up (hα : ∀ g, g ∈ U K ↔ α g ∈ U K) (y : K) : α (up y) = up (tau α y) :=
  eq_up_of_mem_U ((hα (up y)).mp (up_mem_U y))

theorem tau_add (hα : ∀ g, g ∈ U K ↔ α g ∈ U K) (y z : K) :
    tau α (y + z) = tau α y + tau α z := by
  apply up_injective
  calc up (tau α (y + z)) = α (up (y + z)) := (alpha_up hα _).symm
    _ = α (up y * up z) := by rw [up_mul]
    _ = α (up y) * α (up z) := map_mul α _ _
    _ = up (tau α y) * up (tau α z) := by rw [alpha_up hα, alpha_up hα]
    _ = up (tau α y + tau α z) := up_mul _ _

theorem tau_zero (hα : ∀ g, g ∈ U K ↔ α g ∈ U K) : tau α 0 = 0 := by
  have := tau_add hα 0 0
  simpa using this

theorem tau_one_ne_zero (hα : ∀ g, g ∈ U K ↔ α g ∈ U K) : tau α 1 ≠ 0 := by
  intro h0
  have h1 : α (up 1) = α 1 := by
    rw [alpha_up hα, h0, up_zero, map_one]
  have h2 : up (1 : K) = 1 := α.injective h1
  have h3 : up (1 : K) = up 0 := by rw [h2, up_zero]
  exact one_ne_zero (up_injective h3)

theorem alpha_mem_normalizer (hα : ∀ g, g ∈ U K ↔ α g ∈ U K) {b : SL(2, K)}
    (hb : b ∈ Subgroup.normalizer ((U K : Subgroup SL(2, K)) : Set SL(2, K))) :
    α b ∈ Subgroup.normalizer ((U K : Subgroup SL(2, K)) : Set SL(2, K)) := by
  rw [Subgroup.mem_normalizer_iff] at hb ⊢
  intro h
  have h1 : h ∈ U K ↔ α.symm h ∈ U K := by
    have := hα (α.symm h)
    simpa using this.symm
  rw [h1, hb (α.symm h), hα]
  simp

theorem alpha_entry10 (hα : ∀ g, g ∈ U K ↔ α g ∈ U K) {b : SL(2, K)} (hb : b 1 0 = 0) :
    (α b : SL(2, K)) 1 0 = 0 :=
  entry10_of_mem_normalizer (alpha_mem_normalizer hα (mem_normalizer_of_entry10 hb))

theorem tau_relation (hα : ∀ g, g ∈ U K ↔ α g ∈ U K) {b : SL(2, K)} (hb : b 1 0 = 0) (y : K) :
    tau α (b 0 0 ^ 2 * y) = (α b : SL(2, K)) 0 0 ^ 2 * tau α y := by
  have hαb : (α b : SL(2, K)) 1 0 = 0 := alpha_entry10 hα hb
  apply up_injective
  calc up (tau α (b 0 0 ^ 2 * y)) = α (up (b 0 0 ^ 2 * y)) := (alpha_up hα _).symm
    _ = α (b * up y * b⁻¹) := by rw [conj_up hb]
    _ = α b * up (tau α y) * (α b)⁻¹ := by rw [map_mul, map_mul, map_inv, alpha_up hα]
    _ = up ((α b : SL(2, K)) 0 0 ^ 2 * tau α y) := conj_up hαb _

end Auto

section Psi

variable {K : Type*} [Field K] {α : MulAut SL(2, K)}

noncomputable def psi (α : MulAut SL(2, K)) (x : K) : K := tau α x / tau α 1

theorem psi_zero (hα : ∀ g, g ∈ U K ↔ α g ∈ U K) : psi α 0 = 0 := by
  simp [psi, tau_zero hα]

theorem psi_one (hα : ∀ g, g ∈ U K ↔ α g ∈ U K) : psi α 1 = 1 := by
  simp [psi, div_self (tau_one_ne_zero hα)]

theorem psi_add (hα : ∀ g, g ∈ U K ↔ α g ∈ U K) (x y : K) :
    psi α (x + y) = psi α x + psi α y := by
  simp [psi, tau_add hα, add_div]

theorem psi_sq_eq (hα : ∀ g, g ∈ U K ↔ α g ∈ U K) {b : SL(2, K)} (hb : b 1 0 = 0) :
    psi α (b 0 0 ^ 2) = (α b : SL(2, K)) 0 0 ^ 2 := by
  have h := tau_relation hα hb 1
  rw [mul_one] at h
  unfold psi
  rw [h, mul_div_assoc, div_self (tau_one_ne_zero hα), mul_one]

variable [CharP K 2]

theorem sq_injective : Function.Injective (fun a : K => a ^ 2) := by
  intro a b h
  have h2 : (a - b) ^ 2 = 0 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [sub_pow_char]
    simp only at h
    rw [h, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h2)

variable [Finite K]

theorem exists_sq_eq (x : K) : ∃ a : K, a ^ 2 = x :=
  Finite.injective_iff_surjective.mp sq_injective x

theorem psi_mul (hα : ∀ g, g ∈ U K ↔ α g ∈ U K) (x y : K) :
    psi α (x * y) = psi α x * psi α y := by
  by_cases hx : x = 0
  · subst hx
    simp [psi_zero hα]
  obtain ⟨a, rfl⟩ := exists_sq_eq x
  have ha : a ≠ 0 := fun h => hx (by rw [h]; norm_num)
  set b : SL(2, K) := dg a ha with hbdef
  have hb : b 1 0 = 0 := rfl
  have hb0 : b 0 0 = a := rfl
  have h1 := tau_relation hα hb y
  rw [hb0] at h1
  have h2 := psi_sq_eq hα hb
  rw [hb0] at h2
  unfold psi at h2 ⊢
  have hc := tau_one_ne_zero hα
  rw [h1, ← h2]
  field_simp

noncomputable def psiHom (hα : ∀ g, g ∈ U K ↔ α g ∈ U K) : K →+* K where
  toFun := psi α
  map_one' := psi_one hα
  map_mul' := psi_mul hα
  map_zero' := psi_zero hα
  map_add' := psi_add hα

theorem entry00_alpha (hα : ∀ g, g ∈ U K ↔ α g ∈ U K) {b : SL(2, K)} (hb : b 1 0 = 0) :
    (α b : SL(2, K)) 0 0 = psi α (b 0 0) := by
  have h := psi_sq_eq hα hb
  rw [sq, psi_mul hα, ← sq] at h
  exact (sq_injective h).symm

theorem alpha_pow_entries (hα : ∀ g, g ∈ U K ↔ α g ∈ U K) {b : SL(2, K)} (hb : b 1 0 = 0)
    (j : ℕ) :
    ((α ^ j) b : SL(2, K)) 1 0 = 0 ∧ ((α ^ j) b : SL(2, K)) 0 0 = (psi α)^[j] (b 0 0) := by
  induction j with
  | zero => simp [hb]
  | succ j ih =>
    obtain ⟨h1, h2⟩ := ih
    have : (α ^ (j + 1)) b = α ((α ^ j) b) := by rw [pow_succ']; rfl
    rw [this]
    refine ⟨alpha_entry10 hα h1, ?_⟩
    rw [entry00_alpha hα h1, h2, Function.iterate_succ_apply']

theorem psi_eq_self (hGal : ∀ f : K →+* K, ∀ x, f (f (f x)) = x)
    (hα : ∀ g, g ∈ U K ↔ α g ∈ U K) (m : ℕ) (hm : α ^ 2 ^ m = 1) (x : K) : psi α x = x := by
  have h3 : ∀ x, psi α (psi α (psi α x)) = x := hGal (psiHom hα)
  have h2m : ∀ x, (psi α)^[2 ^ m] x = x := by
    intro x
    by_cases hx : x = 0
    · subst hx
      exact Function.iterate_fixed (psi_zero hα) _
    · have := (alpha_pow_entries hα (b := dg x hx) rfl (2 ^ m)).2
      rw [hm] at this
      simpa using this.symm
  let σ : Equiv.Perm K :=
    { toFun := psi α
      invFun := fun x => psi α (psi α x)
      left_inv := fun x => h3 x
      right_inv := fun x => h3 x }
  have hσ3 : σ ^ 3 = 1 := by
    ext x
    simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    exact h3 x
  have hσ2m : σ ^ 2 ^ m = 1 := by
    ext x
    rw [Equiv.Perm.coe_pow]
    exact h2m x
  have hdvd : orderOf σ ∣ Nat.gcd 3 (2 ^ m) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hσ3) (orderOf_dvd_of_pow_eq_one hσ2m)
  have hcop : Nat.gcd 3 (2 ^ m) = 1 := Nat.Coprime.pow_right m (by norm_num)
  rw [hcop] at hdvd
  have h1 : σ = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
  have := congrArg (fun τ : Equiv.Perm K => τ x) h1
  simpa [σ] using this

theorem borel_trivial_U (hGal : ∀ f : K →+* K, ∀ x, f (f (f x)) = x)
    (hα : ∀ g, g ∈ U K ↔ α g ∈ U K) (m : ℕ) (hm : α ^ 2 ^ m = 1) {b : SL(2, K)}
    (hb : b ∈ Subgroup.normalizer ((U K : Subgroup SL(2, K)) : Set SL(2, K))) :
    α b * b⁻¹ ∈ U K := by
  have hb10 := entry10_of_mem_normalizer hb
  have hab10 := alpha_entry10 hα hb10
  have h00 : (α b : SL(2, K)) 0 0 = b 0 0 := by
    rw [entry00_alpha hα hb10, psi_eq_self hGal hα m hm]
  have hd := sl2_diag_mul hb10
  have hd' := sl2_diag_mul hab10
  rw [h00] at hd'
  rw [mem_U_iff]
  refine ⟨?_, ?_, ?_⟩
  · simp [sl2_mul_00, sl2_inv_00, sl2_inv_10, h00, hb10, hd]
  · simp [sl2_mul_10, sl2_inv_00, sl2_inv_10, hb10, hab10]
  · simp [sl2_mul_11, sl2_inv_01, sl2_inv_11, hab10, mul_comm, hd']

end Psi

section F8

abbrev F8 : Type := GaloisField 2 3

theorem ringHom_cube (f : F8 →+* F8) (x : F8) : f (f (f x)) = x := by
  classical
  let A : F8 →ₐ[ZMod 2] F8 :=
    { f with
      commutes' := fun r => by
        have := RingHom.ext_zmod (f.comp (algebraMap (ZMod 2) F8)) (algebraMap (ZMod 2) F8)
        exact DFunLike.congr_fun this r }
  have hbij : Function.Bijective A :=
    ⟨f.injective, Finite.injective_iff_surjective.mp f.injective⟩
  let σ : F8 ≃ₐ[ZMod 2] F8 := AlgEquiv.ofBijective A hbij
  have hcard : Nat.card (F8 ≃ₐ[ZMod 2] F8) = 3 := by
    rw [IsGalois.card_aut_eq_finrank (ZMod 2) F8, GaloisField.finrank 2 (by norm_num)]
  have h1 : σ ^ 3 = 1 := by
    have := pow_card_eq_one' (G := F8 ≃ₐ[ZMod 2] F8) (x := σ)
    rwa [hcard] at this
  have h2 := congrArg (fun τ : F8 ≃ₐ[ZMod 2] F8 => τ x) h1
  simpa [pow_succ, σ, A] using h2

theorem card_sl2_f8 : Nat.card SL(2, F8) = 504 := by
  classical
  have : Fintype F8 := Fintype.ofFinite F8
  have hK : Fintype.card F8 = 8 := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 3 (by norm_num)]
    norm_num
  rw [Matrix.card_SL_field 2, hK, Fin.prod_univ_two]
  norm_num

theorem card_U_f8 : Nat.card (U F8) = 8 := by
  have hinj : Function.Injective (upHom (K := F8)) := fun x y h =>
    Multiplicative.toAdd.injective (up_injective h)
  rw [U, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative F8 ≃ F8),
    GaloisField.card 2 3 (by norm_num)]
  norm_num

theorem isPGroup_U_f8 : IsPGroup 2 (U F8) := by
  intro g
  obtain ⟨x, hx⟩ := g.2
  refine ⟨1, Subtype.ext ?_⟩
  have h2 : (g : SL(2, F8)) ^ 2 = 1 := by
    rw [← hx, pow_two]
    show up (Multiplicative.toAdd x) * up (Multiplicative.toAdd x) = 1
    rw [up_mul, CharTwo.add_self_eq_zero, up_zero]
  simpa using h2

theorem index_U_f8 : ¬ 2 ∣ (U F8).index := by
  have h := (U F8).card_mul_index
  rw [card_U_f8, card_sl2_f8] at h
  have : (U F8).index = 63 := by omega
  rw [this]
  omega

theorem borel_trivial {P : Subgroup SL(2, F8)} (hP2 : IsPGroup 2 P) (hPidx : ¬ 2 ∣ P.index)
    {α : MulAut SL(2, F8)} (hα : ∀ g, g ∈ P ↔ α g ∈ P) (m : ℕ) (hm : α ^ 2 ^ m = 1)
    {b : SL(2, F8)} (hb : b ∈ Subgroup.normalizer (P : Set SL(2, F8))) : α b * b⁻¹ ∈ P := by
  classical
  let SP : Sylow 2 SL(2, F8) := hP2.toSylow hPidx
  let SU : Sylow 2 SL(2, F8) := isPGroup_U_f8.toSylow index_U_f8
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, F8) SU SP
  have hmem : ∀ x, x ∈ P ↔ g⁻¹ * x * g ∈ U F8 := by
    intro x
    have h1 : (SP : Subgroup SL(2, F8)) = MulAut.conj g • (SU : Subgroup SL(2, F8)) := by
      rw [← Sylow.coe_subgroup_smul, hg]
    have hSP : x ∈ (SP : Subgroup SL(2, F8)) ↔ x ∈ P := by simp [SP]
    rw [← hSP, h1, Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s, hs, rfl⟩
      have : s ∈ U F8 := by simpa [SU] using hs
      simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using this
    · intro h
      refine ⟨g⁻¹ * x * g, by simpa [SU] using h, ?_⟩
      simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
  set α' : MulAut SL(2, F8) :=
    (MulAut.conj g)⁻¹ * α * ((MulAut.conj g)⁻¹)⁻¹ with hα'
  have hα'apply : ∀ y, α' y = g⁻¹ * α (g * y * g⁻¹) * g := by
    intro y
    simp [hα', MulAut.conj_apply, mul_assoc]
  have hα'U : ∀ y, y ∈ U F8 ↔ α' y ∈ U F8 := by
    intro y
    rw [hα'apply, ← hmem, ← hα, hmem]
    simp [mul_assoc]
  have hα'm : α' ^ 2 ^ m = 1 := by
    rw [hα', conj_pow, hm]
    simp
  have hb' : g⁻¹ * b * g ∈ Subgroup.normalizer ((U F8 : Subgroup SL(2, F8)) : Set SL(2, F8)) := by
    rw [Subgroup.mem_normalizer_iff] at hb ⊢
    intro h
    have := hb (g * h * g⁻¹)
    rw [hmem (g * h * g⁻¹), hmem (b * (g * h * g⁻¹) * b⁻¹)] at this
    simpa [mul_assoc] using this
  have key := borel_trivial_U ringHom_cube hα'U m hα'm hb'
  rw [hα'apply] at key
  rw [hmem]
  simpa [mul_assoc] using key

end F8

section Ambient

variable {Γ : Type*} [Group Γ]

theorem borel_comm {N : Subgroup Γ} [N.Normal] (e : ↥N ≃* SL(2, F8)) {P : Subgroup Γ}
    (hPN : P ≤ N) (hP2 : IsPGroup 2 P) (hPidx : ¬ 2 ∣ (P.subgroupOf N).index)
    {γ : Γ} (m : ℕ) (hγ : γ ^ 2 ^ m = 1) (hγP : ∀ p, p ∈ P ↔ γ * p * γ⁻¹ ∈ P)
    {k : Γ} (hk : k ∈ Subgroup.normalizer (P : Set Γ)) (hkN : k ∈ N) :
    k * (γ * k⁻¹ * γ⁻¹) ∈ P := by
  classical
  set P₀ : Subgroup N := P.subgroupOf N with hP₀
  set P' : Subgroup SL(2, F8) := P₀.map e.toMonoidHom with hP'
  have hmemP' : ∀ n : N, e n ∈ P' ↔ (n : Γ) ∈ P := by
    intro n
    constructor
    · rintro ⟨n', hn', hen⟩
      have : n' = n := e.injective hen
      subst this
      exact hn'
    · intro hn
      exact ⟨n, hn, rfl⟩
  have hP'2 : IsPGroup 2 P' := by
    have : IsPGroup 2 P₀ := hP2.of_equiv (Subgroup.subgroupOfEquivOfLe hPN).symm
    exact this.map _
  have hP'idx : ¬ 2 ∣ P'.index := by
    have h := Subgroup.index_map_equiv (H := P₀) e
    change ¬ 2 ∣ (Subgroup.map (e : ↥N →* SL(2, F8)) P₀).index
    rw [h]
    exact hPidx
  set α : MulAut SL(2, F8) := (MulAut.congr e) (MulAut.conjNormal γ) with hα
  have hαapply : ∀ n : N, α (e n) = e (MulAut.conjNormal γ n) := by
    intro n
    simp [hα, MulAut.congr_apply]
  have hα' : ∀ g, g ∈ P' ↔ α g ∈ P' := by
    intro g
    obtain ⟨n, rfl⟩ := e.surjective g
    rw [hαapply, hmemP', hmemP', MulAut.conjNormal_apply]
    exact hγP n
  have hαm : α ^ 2 ^ m = 1 := by
    have : α = (MulAut.congr e).toMonoidHom (MulAut.conjNormal γ) := rfl
    rw [this, ← map_pow, ← map_pow, hγ, map_one, map_one]
  have hb : e ⟨k, hkN⟩ ∈ Subgroup.normalizer (P' : Set SL(2, F8)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    obtain ⟨n, rfl⟩ := e.surjective h
    have h1 : e ⟨k, hkN⟩ * e n * (e ⟨k, hkN⟩)⁻¹ = e (⟨k, hkN⟩ * n * ⟨k, hkN⟩⁻¹) := by
      simp
    rw [h1, hmemP', hmemP']
    have := Subgroup.mem_normalizer_iff.mp hk (n : Γ)
    simpa using this
  have key := borel_trivial hP'2 hP'idx hα' m hαm hb
  rw [hαapply, ← map_inv, ← map_mul, hmemP'] at key
  have h2 : ((MulAut.conjNormal γ ⟨k, hkN⟩ * ⟨k, hkN⟩⁻¹ : N) : Γ) = γ * k * γ⁻¹ * k⁻¹ := by
    simp [MulAut.conjNormal_apply]
  rw [h2] at key
  have := P.inv_mem key
  simpa [mul_assoc] using this

end Ambient

end L28

end CFSG.Quasithin.SzPS8
