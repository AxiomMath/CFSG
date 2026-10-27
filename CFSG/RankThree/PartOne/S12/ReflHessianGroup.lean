module

public import CFSG.RankThree.PartOne.S12.ReflHessian
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

public section

namespace CFSG.RankThree.PartOne

namespace ReflF

open Module LinearMap

abbrev HIdx : Type := {x : Equiv.Perm (Fin 3) × (Fin 3 → ZMod 3) // ∑ i, x.2 i = 0}

namespace HIdx

@[expose] def mul (x y : HIdx) : HIdx :=
  ⟨(x.1.1 * y.1.1, fun i => y.1.2 i + x.1.2 (y.1.1 i)), by
    have h1 := y.2
    have h2 := x.2
    simp only [Finset.sum_add_distrib, h1, zero_add]
    rw [Equiv.sum_comp y.1.1 x.1.2]
    exact h2⟩

@[expose] def one : HIdx := ⟨(1, fun _ => 0), by simp⟩

@[expose] def inv (x : HIdx) : HIdx :=
  ⟨(x.1.1⁻¹, fun j => -x.1.2 (x.1.1⁻¹ j)), by
    simp only [Finset.sum_neg_distrib]
    rw [Equiv.sum_comp x.1.1⁻¹ x.1.2]
    rw [x.2, neg_zero]⟩

theorem mul_inv' (x : HIdx) : mul x (inv x) = one := by
  apply Subtype.ext
  apply Prod.ext
  · simp [mul, inv, one]
  · funext i
    simp [mul, inv, one]

theorem inv_mul' (x : HIdx) : mul (inv x) x = one := by
  apply Subtype.ext
  apply Prod.ext
  · simp [mul, inv, one]
  · funext i
    simp [mul, inv, one]

end HIdx

@[expose] def hx01 : HIdx := ⟨(Equiv.swap 0 1, fun _ => 0), by simp⟩

@[expose] def hx12 : HIdx := ⟨(Equiv.swap 1 2, fun _ => 0), by simp⟩

@[expose] def hx02 : HIdx := ⟨(Equiv.swap 0 2, ![2, 0, 1]), by decide⟩

@[expose] def hzH : HIdx := ⟨(1, fun _ => 1), by decide⟩

@[expose] def R9 : Finset HIdx := Finset.univ.filter fun x => x ≠ HIdx.one ∧ HIdx.mul x x = HIdx.one

theorem R9_card : R9.card = 9 := by decide +kernel

theorem card_HIdx : Fintype.card HIdx = 54 := by decide +kernel

@[expose] def conjStep (S : Finset HIdx) : Finset HIdx :=
  S ∪ (S ×ˢ S).image fun p => HIdx.mul (HIdx.mul p.1 p.2) (HIdx.inv p.1)

@[expose] def chain (n : ℕ) : Finset HIdx := conjStep^[n] {hx01, hx12, hx02}

theorem R9_subset_chain : R9 ⊆ chain 2 := by decide +kernel

theorem HIdx_cover : ∀ x : HIdx, ∃ p ∈ (insert HIdx.one R9 ×ˢ insert HIdx.one R9).image
      (fun q => HIdx.mul q.1 q.2),
    ∃ q ∈ (insert HIdx.one R9 ×ˢ insert HIdx.one R9).image (fun q => HIdx.mul q.1 q.2),
      x = HIdx.mul p q := by decide +kernel

set_option synthInstance.maxSize 1024 in
theorem HIdx_order_three : ∀ x : HIdx, (HIdx.mul x (HIdx.mul x x) = HIdx.one ∧ x ≠ HIdx.one ∧
    x ≠ hzH ∧ x ≠ HIdx.mul hzH hzH) →
    ∃ a ∈ R9, ∃ b ∈ R9, a ≠ b ∧ (x = HIdx.mul a b ∨ x = HIdx.mul b a) := by decide +kernel

theorem HIdx_cube_iff : ∀ x : HIdx, HIdx.mul x (HIdx.mul x x) = HIdx.one ↔
    Equiv.Perm.sign x.1.1 = 1 := by decide +kernel

theorem card_even : Fintype.card {x : HIdx // Equiv.Perm.sign x.1.1 = 1} = 27 := by
  decide +kernel

section Psi

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def etaPow (η : K) (m : ZMod 3) : K := η ^ m.val

theorem etaPow_add {η : K} (h : η ^ 3 = 1) (m n : ZMod 3) :
    etaPow η (m + n) = etaPow η m * etaPow η n := by
  unfold etaPow
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.div_add_mod (m.val + n.val) 3, pow_add, pow_mul, h, one_pow, one_mul]

theorem etaPow_zero (η : K) : etaPow η 0 = 1 := by
  simp [etaPow]

theorem etaPow_ne_zero {η : K} (h : η ≠ 0) (m : ZMod 3) : etaPow η m ≠ 0 :=
  pow_ne_zero _ h

theorem etaPow_eq_one_iff {η : K} (h3 : η ^ 3 = 1) (h1 : η ≠ 1) (m : ZMod 3) :
    etaPow η m = 1 ↔ m = 0 := by
  constructor
  · intro h
    unfold etaPow at h
    have hv : m.val < 3 := ZMod.val_lt m
    interval_cases hm : m.val
    · exact (ZMod.val_eq_zero m).1 hm
    · rw [pow_one] at h
      exact absurd h h1
    · exfalso
      apply h1
      have h2' : η ^ 3 = η * η ^ 2 := by ring
      rw [h3, h, mul_one] at h2'
      exact h2'.symm
  · rintro rfl
    exact etaPow_zero η

theorem etaPow_neg_mul {η : K} (h3 : η ^ 3 = 1) (m : ZMod 3) :
    etaPow η (-m) * etaPow η m = 1 := by
  rw [← etaPow_add h3, neg_add_cancel, etaPow_zero]

variable (e : Basis (Fin 3) K V) (η : K)

noncomputable def psiMap (x : HIdx) : V →ₗ[K] V :=
  e.constr K fun i => etaPow η (x.1.2 i) • e (x.1.1 i)

theorem psiMap_apply_basis (x : HIdx) (i : Fin 3) :
    psiMap e η x (e i) = etaPow η (x.1.2 i) • e (x.1.1 i) := by
  simp [psiMap]

theorem psiMap_mul (h3 : η ^ 3 = 1) (x y : HIdx) :
    psiMap e η (HIdx.mul x y) = psiMap e η x ∘ₗ psiMap e η y := by
  apply e.ext
  intro i
  simp only [LinearMap.comp_apply, psiMap_apply_basis, map_smul, HIdx.mul, Equiv.Perm.coe_mul,
    Function.comp_apply, etaPow_add h3, smul_smul]

theorem psiMap_one : psiMap e η HIdx.one = LinearMap.id := by
  apply e.ext
  intro i
  simp [psiMap_apply_basis, HIdx.one, etaPow_zero]

noncomputable def psi (h3 : η ^ 3 = 1) (x : HIdx) : V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap (psiMap e η x) (psiMap e η (HIdx.inv x))
    (by rw [← psiMap_mul e η h3, HIdx.mul_inv', psiMap_one])
    (by rw [← psiMap_mul e η h3, HIdx.inv_mul', psiMap_one])

theorem psi_apply_basis (h3 : η ^ 3 = 1) (x : HIdx) (i : Fin 3) :
    psi e η h3 x (e i) = etaPow η (x.1.2 i) • e (x.1.1 i) :=
  psiMap_apply_basis e η x i

theorem psi_mul (h3 : η ^ 3 = 1) (x y : HIdx) :
    psi e η h3 (HIdx.mul x y) = psi e η h3 x * psi e η h3 y := by
  apply LinearEquiv.toLinearMap_injective
  show psiMap e η (HIdx.mul x y) = psiMap e η x ∘ₗ psiMap e η y
  exact psiMap_mul e η h3 x y

theorem psi_one (h3 : η ^ 3 = 1) : psi e η h3 HIdx.one = 1 := by
  apply LinearEquiv.toLinearMap_injective
  exact psiMap_one e η

theorem psi_inv (h3 : η ^ 3 = 1) (x : HIdx) : psi e η h3 (HIdx.inv x) = (psi e η h3 x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← psi_mul e η h3, HIdx.mul_inv', psi_one]

theorem psi_injective (h3 : η ^ 3 = 1) (h1 : η ≠ 1) (h0 : η ≠ 0) :
    Function.Injective (psi e η h3) := by
  intro x y hxy
  have key : ∀ i : Fin 3, x.1.1 i = y.1.1 i ∧ x.1.2 i = y.1.2 i := by
    intro i
    have h := congrArg (fun g => g (e i)) hxy
    simp only [psi_apply_basis] at h
    have h' := congrArg e.repr h
    simp only [map_smul, Basis.repr_self] at h'
    simp only [Finsupp.smul_single, smul_eq_mul, mul_one] at h'
    rcases (Finsupp.single_eq_single_iff _ _ _ _).1 h' with ⟨hσ, hc⟩ | ⟨hc, hc'⟩
    · refine ⟨hσ, ?_⟩
      have hm : etaPow η (x.1.2 i - y.1.2 i) = 1 := by
        rw [sub_eq_add_neg, etaPow_add h3]
        have := etaPow_neg_mul h3 (y.1.2 i)
        rw [hc]
        calc etaPow η (y.1.2 i) * etaPow η (-y.1.2 i) = etaPow η (-y.1.2 i) * etaPow η (y.1.2 i) :=
            mul_comm _ _
          _ = 1 := this
      exact sub_eq_zero.1 ((etaPow_eq_one_iff h3 h1 _).1 hm)
    · exact absurd hc (etaPow_ne_zero h0 _)
  apply Subtype.ext
  apply Prod.ext
  · ext i
    exact congrArg Fin.val (key i).1
  · funext i
    exact (key i).2

theorem etaPow_two {η : K} : etaPow η 2 = η ^ 2 := by
  unfold etaPow
  rfl

theorem etaPow_one {η : K} : etaPow η 1 = η := by
  have h : (1 : ZMod 3).val = 1 := rfl
  unfold etaPow
  rw [h, pow_one]

section Values

variable {e : Basis (Fin 3) K V} {η : K} (h3 : η ^ 3 = 1)

theorem psi_hx01_zero : psi e η h3 hx01 (e 0) = e 1 := by
  rw [psi_apply_basis]
  show etaPow η 0 • e ((Equiv.swap (0 : Fin 3) 1) 0) = e 1
  rw [Equiv.swap_apply_left, etaPow_zero, one_smul]

theorem psi_hx01_one : psi e η h3 hx01 (e 1) = e 0 := by
  rw [psi_apply_basis]
  show etaPow η 0 • e ((Equiv.swap (0 : Fin 3) 1) 1) = e 0
  rw [Equiv.swap_apply_right, etaPow_zero, one_smul]

theorem psi_hx01_two : psi e η h3 hx01 (e 2) = e 2 := by
  rw [psi_apply_basis]
  show etaPow η 0 • e ((Equiv.swap (0 : Fin 3) 1) 2) = e 2
  rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide), etaPow_zero, one_smul]

theorem psi_hx12_zero : psi e η h3 hx12 (e 0) = e 0 := by
  rw [psi_apply_basis]
  show etaPow η 0 • e ((Equiv.swap (1 : Fin 3) 2) 0) = e 0
  rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide), etaPow_zero, one_smul]

theorem psi_hx12_one : psi e η h3 hx12 (e 1) = e 2 := by
  rw [psi_apply_basis]
  show etaPow η 0 • e ((Equiv.swap (1 : Fin 3) 2) 1) = e 2
  rw [Equiv.swap_apply_left, etaPow_zero, one_smul]

theorem psi_hx12_two : psi e η h3 hx12 (e 2) = e 1 := by
  rw [psi_apply_basis]
  show etaPow η 0 • e ((Equiv.swap (1 : Fin 3) 2) 2) = e 1
  rw [Equiv.swap_apply_right, etaPow_zero, one_smul]

theorem psi_hx02_zero : psi e η h3 hx02 (e 0) = η ^ 2 • e 2 := by
  rw [psi_apply_basis]
  show etaPow η 2 • e ((Equiv.swap (0 : Fin 3) 2) 0) = η ^ 2 • e 2
  rw [Equiv.swap_apply_left, etaPow_two]

theorem psi_hx02_one : psi e η h3 hx02 (e 1) = e 1 := by
  rw [psi_apply_basis]
  show etaPow η 0 • e ((Equiv.swap (0 : Fin 3) 2) 1) = e 1
  rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide), etaPow_zero, one_smul]

theorem psi_hx02_two : psi e η h3 hx02 (e 2) = η • e 0 := by
  rw [psi_apply_basis]
  show etaPow η 1 • e ((Equiv.swap (0 : Fin 3) 2) 2) = η • e 0
  rw [Equiv.swap_apply_right, etaPow_one]

end Values

theorem sum_etaPow (hη : η ^ 2 + η + 1 = 0) : ∑ k : ZMod 3, etaPow η k = 0 := by
  have hu : (Finset.univ : Finset (ZMod 3)) = {0, 1, 2} := by decide
  rw [hu, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    etaPow_zero, etaPow_one, etaPow_two]
  linear_combination hη

theorem R9_fiber_card : ∀ (l j : Fin 3) (k : ZMod 3),
    (R9.filter fun x => (x.1.1 l, x.1.2 l) = (j, k)).card =
      if j = l then (if k = 0 then 3 else 0) else 1 := by decide +kernel

theorem sum_psi_R9_apply (hη3 : η ^ 3 = 1) (hη : η ^ 2 + η + 1 = 0) (l : Fin 3) :
    ∑ x ∈ R9, psi e η hη3 x (e l) = (3 : K) • e l := by
  have h1 : ∀ x ∈ R9, psi e η hη3 x (e l) = etaPow η (x.1.2 l) • e (x.1.1 l) :=
    fun x _ => psi_apply_basis e η hη3 x l
  have key : ∑ x ∈ R9, etaPow η (x.1.2 l) • e (x.1.1 l) =
      ∑ b : Fin 3 × ZMod 3,
        (R9.filter fun x => (x.1.1 l, x.1.2 l) = b).card • (etaPow η b.2 • e b.1) := by
    have := Finset.sum_fiberwise' R9 (fun x : HIdx => ((x.1.1 l, x.1.2 l) : Fin 3 × ZMod 3))
      (fun b : Fin 3 × ZMod 3 => etaPow η b.2 • e b.1)
    simp only [Finset.sum_const] at this
    exact this.symm
  have hj : ∀ j : Fin 3, ∑ k : ZMod 3, (if j = l then (if k = 0 then 3 else 0) else 1) •
      (etaPow η k • e j) = if j = l then (3 : K) • e j else 0 := by
    intro j
    by_cases hjl : j = l
    · simp [hjl, etaPow_zero, ofNat_smul_eq_nsmul K]
    · simp [hjl, ← Finset.sum_smul, sum_etaPow η hη]
  rw [Finset.sum_congr rfl h1, key, Fintype.sum_prod_type]
  simp only [R9_fiber_card]
  rw [Finset.sum_congr rfl fun j _ => hj j]
  simp

theorem hessian_frame [FiniteDimensional K V] (hdim : finrank K V = 3) (h3 : (3 : K) ≠ 0)
    {T₁ T₂ T₃ : V ≃ₗ[K] V} {r₁ r₂ r₃ : V} {φ₁ φ₂ φ₃ : V →ₗ[K] K}
    (d₁ : ReflData T₁ r₁ φ₁) (d₂ : ReflData T₂ r₂ φ₂) (d₃ : ReflData T₃ r₃ φ₃)
    (hli : LinearIndependent K ![r₁, r₂, r₃]) {θ : K}
    (h12 : φ₁ r₂ = -1) (h21 : φ₂ r₁ = -1) (h13 : φ₁ r₃ = -1) (h31 : φ₃ r₁ = -1)
    (h23 : φ₂ r₃ = θ) (h32 : φ₃ r₂ = 1 - θ) (hθ : θ ^ 2 - θ + 1 = 0) :
    ∃ (e : Basis (Fin 3) K V) (η : K) (h3' : η ^ 3 = 1), η ≠ 1 ∧ η ^ 2 + η + 1 = 0 ∧
      T₁ = psi e η h3' hx01 ∧ T₂ = psi e η h3' hx12 ∧ T₃ = psi e η h3' hx02 := by
  obtain ⟨η, hηθ⟩ : ∃ η : K, η = θ - 1 := ⟨_, rfl⟩
  have hη : η ^ 2 + η + 1 = 0 := by rw [hηθ]; linear_combination hθ
  have hη3 : η ^ 3 = 1 := by linear_combination (η - 1) * hη
  have hη1 : η ≠ 1 := by
    intro h
    rw [h] at hη
    apply h3
    linear_combination hη
  have hη2 : η ^ 2 - 1 ≠ 0 := by
    intro h
    apply hη1
    linear_combination hη3 - η * h
  have hθη : θ = η + 1 := by rw [hηθ]; ring
  obtain ⟨e₂, he₂⟩ : ∃ e₂ : V, (η ^ 2 - 1) • e₂ = r₁ + r₂ + r₃ :=
    ⟨(η ^ 2 - 1)⁻¹ • (r₁ + r₂ + r₃), by rw [smul_smul, mul_inv_cancel₀ hη2, one_smul]⟩
  obtain ⟨e₁, he₁⟩ : ∃ e₁ : V, e₁ = e₂ + r₂ := ⟨_, rfl⟩
  obtain ⟨e₀, he₀⟩ : ∃ e₀ : V, e₀ = e₁ + r₁ := ⟨_, rfl⟩
  have hr1 : r₁ = e₀ - e₁ := by rw [he₀]; abel
  have hr2 : r₂ = e₁ - e₂ := by rw [he₁]; abel
  have hr3 : r₃ = η ^ 2 • e₂ - e₀ := by
    have : r₃ = (η ^ 2 - 1) • e₂ - r₁ - r₂ := by rw [he₂]; abel
    rw [this, he₀, he₁]
    module
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by rw [Fintype.card_fin, hdim])
  have hb : ∀ i, b i = ![r₁, r₂, r₃] i := fun i => by
    simp [b, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hspan : ⊤ ≤ Submodule.span K (Set.range ![e₀, e₁, e₂]) := by
    rw [← b.span_eq]
    apply Submodule.span_le.2
    rintro _ ⟨i, rfl⟩
    rw [hb]
    fin_cases i
    · show r₁ ∈ Submodule.span K (Set.range ![e₀, e₁, e₂])
      rw [hr1]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨0, rfl⟩) (Submodule.subset_span ⟨1, rfl⟩)
    · show r₂ ∈ Submodule.span K (Set.range ![e₀, e₁, e₂])
      rw [hr2]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨1, rfl⟩) (Submodule.subset_span ⟨2, rfl⟩)
    · show r₃ ∈ Submodule.span K (Set.range ![e₀, e₁, e₂])
      rw [hr3]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨2, rfl⟩))
        (Submodule.subset_span ⟨0, rfl⟩)
  let e : Basis (Fin 3) K V :=
    basisOfTopLeSpanOfCardEqFinrank ![e₀, e₁, e₂] hspan (by rw [Fintype.card_fin, hdim])
  have he : ∀ i, e i = ![e₀, e₁, e₂] i := fun i => by
    simp [e, coe_basisOfTopLeSpanOfCardEqFinrank]
  have he0 : e 0 = e₀ := he 0
  have he1 : e 1 = e₁ := he 1
  have he2 : e 2 = e₂ := he 2
  have ext3 : ∀ (S S' : V ≃ₗ[K] V), S r₁ = S' r₁ → S r₂ = S' r₂ → S r₃ = S' r₃ → S = S' := by
    intro S S' h1 h2 h3'
    apply LinearEquiv.toLinearMap_injective
    refine b.ext fun i => ?_
    rw [LinearEquiv.coe_coe, LinearEquiv.coe_coe, hb]
    fin_cases i
    · exact h1
    · exact h2
    · exact h3'
  have hT1r1 : T₁ r₁ = -r₁ := d₁.apply_root
  have hT1r2 : T₁ r₂ = r₂ + r₁ := by rw [d₁.apply, h12]; module
  have hT1r3 : T₁ r₃ = r₃ + r₁ := by rw [d₁.apply, h13]; module
  have hT2r1 : T₂ r₁ = r₁ + r₂ := by rw [d₂.apply, h21]; module
  have hT2r2 : T₂ r₂ = -r₂ := d₂.apply_root
  have hT2r3 : T₂ r₃ = r₃ - θ • r₂ := by rw [d₂.apply, h23]
  have hT3r1 : T₃ r₁ = r₁ + r₃ := by rw [d₃.apply, h31]; module
  have hT3r2 : T₃ r₂ = r₂ - (1 - θ) • r₃ := by rw [d₃.apply, h32]
  have hT3r3 : T₃ r₃ = -r₃ := d₃.apply_root
  have hr1' : r₁ = e 0 - e 1 := by rw [he0, he1]; exact hr1
  have hr2' : r₂ = e 1 - e 2 := by rw [he1, he2]; exact hr2
  have hr3' : r₃ = η ^ 2 • e 2 - e 0 := by rw [he2, he0]; exact hr3
  have hθ' : θ = -η ^ 2 := by rw [hθη]; linear_combination hη
  have hθ'' : 1 - θ = -η := by rw [hθη]; ring
  have P1r1 : psi e η hη3 hx01 r₁ = e 1 - e 0 := by
    rw [hr1', map_sub, psi_hx01_zero, psi_hx01_one]
  have P1r2 : psi e η hη3 hx01 r₂ = e 0 - e 2 := by
    rw [hr2', map_sub, psi_hx01_one, psi_hx01_two]
  have P1r3 : psi e η hη3 hx01 r₃ = η ^ 2 • e 2 - e 1 := by
    rw [hr3', map_sub, map_smul, psi_hx01_two, psi_hx01_zero]
  have P2r1 : psi e η hη3 hx12 r₁ = e 0 - e 2 := by
    rw [hr1', map_sub, psi_hx12_zero, psi_hx12_one]
  have P2r2 : psi e η hη3 hx12 r₂ = e 2 - e 1 := by
    rw [hr2', map_sub, psi_hx12_one, psi_hx12_two]
  have P2r3 : psi e η hη3 hx12 r₃ = η ^ 2 • e 1 - e 0 := by
    rw [hr3', map_sub, map_smul, psi_hx12_two, psi_hx12_zero]
  have P3r1 : psi e η hη3 hx02 r₁ = η ^ 2 • e 2 - e 1 := by
    rw [hr1', map_sub, psi_hx02_zero, psi_hx02_one]
  have P3r2 : psi e η hη3 hx02 r₂ = e 1 - η • e 0 := by
    rw [hr2', map_sub, psi_hx02_one, psi_hx02_two]
  have P3r3 : psi e η hη3 hx02 r₃ = η ^ 3 • e 0 - η ^ 2 • e 2 := by
    rw [hr3', map_sub, map_smul, psi_hx02_two, psi_hx02_zero]
    module
  refine ⟨e, η, hη3, hη1, hη, ?_, ?_, ?_⟩
  · apply ext3
    · rw [hT1r1, P1r1, hr1']
      abel
    · rw [hT1r2, P1r2, hr1', hr2']
      abel
    · rw [hT1r3, P1r3, hr3', hr1']
      module
  · apply ext3
    · rw [hT2r1, P2r1, hr1', hr2']
      abel
    · rw [hT2r2, P2r2, hr2']
      abel
    · rw [hT2r3, P2r3, hθ', hr3', hr2']
      module
  · apply ext3
    · rw [hT3r1, P3r1, hr1', hr3']
      module
    · rw [hT3r2, P3r2, hθ'', hr2', hr3']
      match_scalars <;> first | ring1 | linear_combination hη3
    · rw [hT3r3, P3r3, hr3']
      match_scalars <;> first | ring1 | linear_combination (-1 : K) * hη3

theorem psi_mem_chain {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) (h3 : η ^ 3 = 1)
    (m1 : psi e η h3 hx01 ∈ 𝒟) (m2 : psi e η h3 hx12 ∈ 𝒟) (m3 : psi e η h3 hx02 ∈ 𝒟) :
    ∀ (n : ℕ), ∀ x ∈ chain n, psi e η h3 x ∈ 𝒟 := by
  intro n
  induction n with
  | zero =>
    intro x hx
    simp only [chain, Function.iterate_zero, id_eq, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  | succ n ih =>
    intro x hx
    simp only [chain, Function.iterate_succ_apply'] at hx
    unfold conjStep at hx
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact ih x hx
    · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.1 hx
      rw [Finset.mem_product] at hab
      rw [psi_mul e η h3, psi_mul e η h3, psi_inv e η h3]
      exact h.conj _ (ih a hab.1) _ (ih b hab.2)

theorem sum_psi_R9 (hη3 : η ^ 3 = 1) (hη : η ^ 2 + η + 1 = 0) :
    ∑ x ∈ R9, (psi e η hη3 x : V →ₗ[K] V) = (3 : K) • LinearMap.id := by
  apply e.ext
  intro l
  rw [LinearMap.sum_apply]
  simp only [LinearEquiv.coe_coe, LinearMap.smul_apply, LinearMap.id_apply]
  exact sum_psi_R9_apply e η hη3 hη l

theorem exists_eq_psi_of_mem [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0)
    {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟)
    (hnc : ∀ T ∈ 𝒟, ∀ S ∈ 𝒟, T ≠ S → T * S ≠ S * T)
    (hη3 : η ^ 3 = 1) (hη : η ^ 2 + η + 1 = 0) (hR9 : ∀ x ∈ R9, psi e η hη3 x ∈ 𝒟)
    {T : V ≃ₗ[K] V} (hT : T ∈ 𝒟) : ∃ x ∈ R9, psi e η hη3 x = T := by
  by_contra hcon
  push Not at hcon
  have htr : ∀ x ∈ R9, LinearMap.trace K V (Nop T * Nop (psi e η hη3 x)) = 1 := by
    intro x hx
    have hne : T ≠ psi e η hη3 x := fun he => hcon x hx he.symm
    rcases h.dich h2 h3 hT (hR9 x hx) hne with ⟨_, _, hc⟩ | ⟨ht, _, _, _⟩
    · exact absurd hc (hnc _ hT _ (hR9 x hx) hne)
    · exact ht
  have hN : ∑ x ∈ R9, Nop (psi e η hη3 x) = (6 : K) • LinearMap.id := by
    have h1 : ∀ x ∈ R9, Nop (psi e η hη3 x) = LinearMap.id - (psi e η hη3 x : V →ₗ[K] V) :=
      fun x _ => rfl
    rw [Finset.sum_congr rfl h1, Finset.sum_sub_distrib, sum_psi_R9 e η hη3 hη, Finset.sum_const,
      R9_card, ← ofNat_smul_eq_nsmul K 9 (LinearMap.id : V →ₗ[K] V)]
    module
  obtain ⟨r, φ, hd⟩ := h.refl T hT
  have h1 : LinearMap.trace K V (Nop T * ∑ x ∈ R9, Nop (psi e η hη3 x)) = 9 := by
    rw [Finset.mul_sum, map_sum, Finset.sum_congr rfl htr, Finset.sum_const, R9_card]
    simp
  have h2' : LinearMap.trace K V (Nop T * ((6 : K) • LinearMap.id)) = 12 := by
    have : Nop T * ((6 : K) • (LinearMap.id : V →ₗ[K] V)) = (6 : K) • Nop T := by
      ext x
      simp [Module.End.mul_apply]
    rw [this, map_smul, hd.trace_nop, smul_eq_mul]
    norm_num
  rw [hN, h2'] at h1
  apply h3
  linear_combination h1

theorem hessian_eq_image [FiniteDimensional K V] (hdim : finrank K V = 3) (h2 : (2 : K) ≠ 0)
    (h3 : (3 : K) ≠ 0) {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) (hU : Uspan 𝒟 = ⊤)
    (hnc : ∀ T ∈ 𝒟, ∀ S ∈ 𝒟, T ≠ S → T * S ≠ S * T) :
    ∃ (e : Basis (Fin 3) K V) (η : K) (h3' : η ^ 3 = 1), η ≠ 1 ∧ η ^ 2 + η + 1 = 0 ∧
      ∀ T : V ≃ₗ[K] V, T ∈ 𝒟 ↔ ∃ x ∈ R9, psi e η h3' x = T := by
  obtain ⟨T₁, T₂, T₃, r₁, r₂, r₃, φ₁, φ₂, φ₃, h₁, h₂, h₃, d₁, d₂, d₃, hli⟩ :=
    exists_hessian_triple hdim h hU
  obtain ⟨θ, r₂', r₃', φ₂', φ₃', hθ, d₂', d₃', hli', h12, h21, h13, h31, h23, h32⟩ :=
    hessian_normalize h2 h3 h hnc h₁ h₂ h₃ d₁ d₂ d₃ hli
  obtain ⟨e, η, hη3, hη1, hη, e1, e2, e3⟩ :=
    hessian_frame hdim h3 d₁ d₂' d₃' hli' h12 h21 h13 h31 h23 h32 hθ
  have hmem : ∀ x ∈ R9, psi e η hη3 x ∈ 𝒟 := by
    intro x hx
    refine psi_mem_chain e η h hη3 ?_ ?_ ?_ 2 x (R9_subset_chain hx)
    · rw [← e1]; exact h₁
    · rw [← e2]; exact h₂
    · rw [← e3]; exact h₃
  refine ⟨e, η, hη3, hη1, hη, fun T => ⟨fun hT => ?_, ?_⟩⟩
  · exact exists_eq_psi_of_mem e η h2 h3 h hnc hη3 hη hmem hT
  · rintro ⟨x, hx, rfl⟩
    exact hmem x hx

def psiRange (h3 : η ^ 3 = 1) : Subgroup (V ≃ₗ[K] V) where
  carrier := Set.range (psi e η h3)
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨HIdx.mul x y, psi_mul e η h3 x y⟩
  one_mem' := ⟨HIdx.one, psi_one e η h3⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨HIdx.inv x, psi_inv e η h3 x⟩

def psiThree (h3 : η ^ 3 = 1) : Subgroup (V ≃ₗ[K] V) where
  carrier := {y | ∃ x : HIdx, psi e η h3 x = y ∧ Equiv.Perm.sign x.1.1 = 1}
  mul_mem' := by
    rintro _ _ ⟨x, rfl, hx⟩ ⟨y, rfl, hy⟩
    refine ⟨HIdx.mul x y, psi_mul e η h3 x y, ?_⟩
    show Equiv.Perm.sign (x.1.1 * y.1.1) = 1
    rw [map_mul, hx, hy]
    rfl
  one_mem' := ⟨HIdx.one, psi_one e η h3, by simp [HIdx.one]⟩
  inv_mem' := by
    rintro _ ⟨x, rfl, hx⟩
    refine ⟨HIdx.inv x, psi_inv e η h3 x, ?_⟩
    show Equiv.Perm.sign (x.1.1)⁻¹ = 1
    rw [map_inv, hx]
    rfl

theorem psiThree_le_psiRange (h3 : η ^ 3 = 1) : psiThree e η h3 ≤ psiRange e η h3 := by
  rintro _ ⟨x, rfl, -⟩
  exact ⟨x, rfl⟩

theorem closure_R9_image (h3 : η ^ 3 = 1) [DecidableEq (V ≃ₗ[K] V)] :
    Subgroup.closure ((R9.image (psi e η h3) : Finset (V ≃ₗ[K] V)) : Set (V ≃ₗ[K] V)) =
      psiRange e η h3 := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro y hy
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
    exact ⟨x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    have hgen : ∀ a ∈ insert HIdx.one R9, psi e η h3 a ∈
        Subgroup.closure ((R9.image (psi e η h3) : Finset (V ≃ₗ[K] V)) : Set (V ≃ₗ[K] V)) := by
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · rw [psi_one]
        exact Subgroup.one_mem _
      · exact Subgroup.subset_closure (Finset.mem_coe.2 (Finset.mem_image_of_mem _ ha))
    obtain ⟨p, hp, q, hq, rfl⟩ := HIdx_cover x
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.1 hp
    obtain ⟨⟨c, d⟩, hcd, rfl⟩ := Finset.mem_image.1 hq
    rw [Finset.mem_product] at hab hcd
    simp only [psi_mul e η h3]
    exact mul_mem (mul_mem (hgen a hab.1) (hgen b hab.2))
      (mul_mem (hgen c hcd.1) (hgen d hcd.2))

theorem card_psiRange (h3 : η ^ 3 = 1) (h1 : η ≠ 1) :
    Nat.card (psiRange e η h3) = 54 := by
  have h0 : η ≠ 0 := by
    rintro rfl
    simp at h3
  have : Nat.card (psiRange e η h3) = Nat.card (Set.range (psi e η h3)) := rfl
  rw [this, Nat.card_range_of_injective (psi_injective e η h3 h1 h0), Nat.card_eq_fintype_card,
    card_HIdx]

theorem card_psiThree (h3 : η ^ 3 = 1) (h1 : η ≠ 1) :
    Nat.card (psiThree e η h3) = 27 := by
  have h0 : η ≠ 0 := by
    rintro rfl
    simp at h3
  have hinj := psi_injective e η h3 h1 h0
  let f : {x : HIdx // Equiv.Perm.sign x.1.1 = 1} → psiThree e η h3 :=
    fun x => ⟨psi e η h3 x.1, x.1, rfl, x.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      exact Subtype.ext (hinj (congrArg Subtype.val hxy))
    · rintro ⟨_, x, rfl, hx⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, card_even]

theorem hessian_structure [FiniteDimensional K V] (hdim : finrank K V = 3) (h2 : (2 : K) ≠ 0)
    (h3 : (3 : K) ≠ 0) {𝒟 : Finset (V ≃ₗ[K] V)} (h : IsRSet 𝒟) (hU : Uspan 𝒟 = ⊤)
    (hnc : ∀ T ∈ 𝒟, ∀ S ∈ 𝒟, T ≠ S → T * S ≠ S * T) :
    𝒟.card = 9 ∧ Nat.card (Subgroup.closure (𝒟 : Set (V ≃ₗ[K] V))) = 54 ∧
      ∃ (ω : K) (z : V ≃ₗ[K] V), ω ^ 2 + ω + 1 = 0 ∧
        z ∈ Subgroup.closure (𝒟 : Set (V ≃ₗ[K] V)) ∧ (∀ x, z x = ω • x) ∧ z ≠ 1 ∧ z ^ 3 = 1 ∧
        (∀ g : V ≃ₗ[K] V, z * g = g * z) ∧
        (∀ y ∈ Subgroup.closure (𝒟 : Set (V ≃ₗ[K] V)), y ^ 3 = 1 → y ∉ Subgroup.zpowers z →
          ∃ s ∈ 𝒟, ∃ t ∈ 𝒟, s ≠ t ∧ (y = s * t ∨ y = t * s)) ∧
        ∃ P : Subgroup (V ≃ₗ[K] V), P ≤ Subgroup.closure (𝒟 : Set (V ≃ₗ[K] V)) ∧
          Nat.card P = 27 ∧ z ∈ P ∧
          ∀ y ∈ Subgroup.closure (𝒟 : Set (V ≃ₗ[K] V)), y ∈ P ↔ y ^ 3 = 1 := by
  classical
  obtain ⟨e, η, hη3, hη1, hη, hdesc⟩ := hessian_eq_image hdim h2 h3 h hU hnc
  have h0 : η ≠ 0 := by
    rintro rfl
    simp at hη3
  have hinj := psi_injective e η hη3 hη1 h0
  have h𝒟 : 𝒟 = R9.image (psi e η hη3) := by
    ext T
    rw [hdesc T, Finset.mem_image]
  have hcl : Subgroup.closure (𝒟 : Set (V ≃ₗ[K] V)) = psiRange e η hη3 := by
    rw [h𝒟]
    exact closure_R9_image e η hη3
  have hcard : 𝒟.card = 9 := by
    rw [h𝒟, Finset.card_image_of_injective _ hinj, R9_card]
  have hz : ∀ x, psi e η hη3 hzH x = η • x := by
    intro x
    have : (psi e η hη3 hzH : V →ₗ[K] V) = η • LinearMap.id := by
      apply e.ext
      intro i
      rw [LinearEquiv.coe_coe, psi_apply_basis]
      show etaPow η 1 • e ((1 : Equiv.Perm (Fin 3)) i) = _
      rw [etaPow_one]
      rfl
    exact LinearMap.congr_fun this x
  refine ⟨hcard, ?_, η, psi e η hη3 hzH, hη, ?_, hz, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcl]
    exact card_psiRange e η hη3 hη1
  · rw [hcl]
    exact ⟨hzH, rfl⟩
  · intro hone
    have h1 := hz (e 0)
    rw [hone] at h1
    have h1' : (1 - η) • e 0 = 0 := by
      rw [sub_smul, one_smul]
      exact sub_eq_zero.2 h1
    rcases smul_eq_zero.1 h1' with hc | hc
    · exact hη1 (sub_eq_zero.1 hc).symm
    · exact e.ne_zero 0 hc
  · have hcube : HIdx.mul hzH (HIdx.mul hzH hzH) = HIdx.one := by decide +kernel
    rw [pow_three, ← psi_mul e η hη3, ← psi_mul e η hη3, hcube, psi_one]
  · intro g
    ext x
    show psi e η hη3 hzH (g x) = g (psi e η hη3 hzH x)
    rw [hz, hz, map_smul]
  · intro y hy hy3 hynot
    rw [hcl] at hy
    obtain ⟨x, rfl⟩ := hy
    have hx3 : HIdx.mul x (HIdx.mul x x) = HIdx.one := by
      apply hinj
      rw [psi_mul e η hη3, psi_mul e η hη3, psi_one, ← pow_three]
      exact hy3
    have hx1 : x ≠ HIdx.one := by
      rintro rfl
      exact hynot (by rw [psi_one]; exact Subgroup.one_mem _)
    have hx2 : x ≠ hzH := by
      rintro rfl
      exact hynot (Subgroup.mem_zpowers _)
    have hx2' : x ≠ HIdx.mul hzH hzH := by
      rintro rfl
      refine hynot ?_
      rw [psi_mul e η hη3]
      exact Subgroup.mul_mem _ (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)
    obtain ⟨a, ha, b, hb, hab, hx⟩ := HIdx_order_three x ⟨hx3, hx1, hx2, hx2'⟩
    refine ⟨psi e η hη3 a, (hdesc _).2 ⟨a, ha, rfl⟩, psi e η hη3 b, (hdesc _).2 ⟨b, hb, rfl⟩,
      fun hh => hab (hinj hh), ?_⟩
    rcases hx with rfl | rfl
    · left
      exact psi_mul e η hη3 a b
    · right
      exact psi_mul e η hη3 b a
  · refine ⟨psiThree e η hη3, ?_, card_psiThree e η hη3 hη1, ?_, ?_⟩
    · rw [hcl]
      exact psiThree_le_psiRange e η hη3
    · exact ⟨hzH, rfl, by simp [hzH]⟩
    · intro y hy
      rw [hcl] at hy
      obtain ⟨x, rfl⟩ := hy
      constructor
      · rintro ⟨x', hx', hs⟩
        have hxx : x' = x := hinj hx'
        subst hxx
        have hc := (HIdx_cube_iff x').2 hs
        rw [pow_three, ← psi_mul e η hη3, ← psi_mul e η hη3, hc, psi_one]
      · intro hy3
        refine ⟨x, rfl, ?_⟩
        apply (HIdx_cube_iff x).1
        apply hinj
        rw [psi_mul e η hη3, psi_mul e η hη3, psi_one, ← pow_three]
        exact hy3

end Psi

end ReflF

end CFSG.RankThree.PartOne
