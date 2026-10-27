module

public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.RankThree.Transfer

section KaloujnineKrasner

variable {P Q D : Type*} [Group P] [Group Q] [Group D]

theorem kaloujnineKrasner_mem (φ : P →* Q) (t : Q → P) (ht : ∀ x, φ (t x) = x) (g : P)
    (x : Q) : (t x)⁻¹ * g * t ((φ g)⁻¹ * x) ∈ φ.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, ht, ht]
  group

@[expose] def kaloujnineKrasner (φ : P →* Q) (t : Q → P) (ht : ∀ x, φ (t x) = x) (θ : φ.ker →* D) :
    P →* D ≀ᵣ Q where
  toFun g := ⟨fun x => θ ⟨_, kaloujnineKrasner_mem φ t ht g x⟩, φ g⟩
  map_one' := by
    ext x
    · simp only [RegularWreathProduct.one_left, Pi.one_apply]
      rw [← map_one θ]
      congr 1
      ext
      simp
    · simp
  map_mul' g h := by
    ext x
    · simp only [RegularWreathProduct.mul_left, Pi.mul_apply]
      rw [← map_mul]
      congr 1
      ext
      simp only [Subgroup.coe_mul, map_mul, mul_inv_rev, mul_assoc, mul_inv_cancel_left]
    · simp

theorem kaloujnineKrasner_left (φ : P →* Q) (t : Q → P) (ht : ∀ x, φ (t x) = x)
    (θ : φ.ker →* D) (g : P) (x : Q) :
    (kaloujnineKrasner φ t ht θ g).left x = θ ⟨_, kaloujnineKrasner_mem φ t ht g x⟩ := rfl

theorem kaloujnineKrasner_right (φ : P →* Q) (t : Q → P) (ht : ∀ x, φ (t x) = x)
    (θ : φ.ker →* D) (g : P) : (kaloujnineKrasner φ t ht θ g).right = φ g := rfl

theorem kaloujnineKrasner_surjective (φ : P →* Q) (t : Q → P) (ht : ∀ x, φ (t x) = x)
    (θ : φ.ker →* D)
    (hbase : ∀ f : Q → D, ∃ r : φ.ker, ∀ x, (kaloujnineKrasner φ t ht θ r).left x = f x) :
    Function.Surjective (kaloujnineKrasner φ t ht θ) := by
  intro w
  obtain ⟨r, hr⟩ :=
    hbase fun x => w.left x * ((kaloujnineKrasner φ t ht θ (t w.right)).left x)⁻¹
  refine ⟨r * t w.right, ?_⟩
  rw [map_mul]
  ext x
  · rw [RegularWreathProduct.mul_left, Pi.mul_apply, hr, kaloujnineKrasner_right,
      (MonoidHom.mem_ker.mp r.2), inv_one, one_mul, inv_mul_cancel_right]
  · rw [RegularWreathProduct.mul_right, kaloujnineKrasner_right, kaloujnineKrasner_right,
      (MonoidHom.mem_ker.mp r.2), one_mul, ht]

end KaloujnineKrasner

section Translation

open Polynomial

variable {p : ℕ}

theorem X_sub_one_pow_pred (hp : p.Prime) :
    ((X - 1 : (ZMod p)[X]) ^ (p - 1)) = ∑ i ∈ Finset.range p, (X : (ZMod p)[X]) ^ i := by
  have := Fact.mk hp
  have hX : (X - 1 : (ZMod p)[X]) ≠ 0 := by
    simpa using Polynomial.X_sub_C_ne_zero (1 : ZMod p)
  apply mul_right_cancel₀ hX
  rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le, geom_sum_mul, sub_pow_char, one_pow]

@[expose] noncomputable def shift : Module.End (ZMod p) (ZMod p → ZMod p) :=
  LinearMap.funLeft (ZMod p) (ZMod p) (· + 1)

theorem shift_apply (f : ZMod p → ZMod p) (x : ZMod p) : shift f x = f (x + 1) := rfl

theorem shift_pow_apply (n : ℕ) (f : ZMod p → ZMod p) (x : ZMod p) :
    (shift ^ n) f x = f (x + n) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih, shift_apply]
    push_cast
    ring_nf

variable [NeZero p]

theorem eq_const_of_shift_eq (g : ZMod p → ZMod p) (hg : shift g = g) (x : ZMod p) :
    g x = g 0 := by
  have h : ∀ n : ℕ, g n = g 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := congrFun hg (n : ZMod p)
      rw [shift_apply] at this
      push_cast
      rw [this, ih]
  rw [← ZMod.natCast_zmod_val x]
  exact h _

theorem sum_range_add (f : ZMod p → ZMod p) (x : ZMod p) :
    ∑ i ∈ Finset.range p, f (x + i) = ∑ y, f y := by
  refine Finset.sum_nbij (fun i => x + (i : ZMod p)) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have : (i : ZMod p) = j := add_left_cancel hij
    rw [ZMod.natCast_eq_natCast_iff'] at this
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  · intro y _
    refine ⟨(y - x).val, by simpa using ZMod.val_lt (y - x), ?_⟩
    simp
  · intro i _
    rfl

theorem shift_sub_one_pow_pred_apply (hp : p.Prime) (f : ZMod p → ZMod p) (x : ZMod p) :
    ((shift - 1 : Module.End (ZMod p) (ZMod p → ZMod p)) ^ (p - 1)) f x = ∑ y, f y := by
  have h := congrArg (Polynomial.aeval (shift : Module.End (ZMod p) (ZMod p → ZMod p)))
    (X_sub_one_pow_pred hp)
  rw [map_pow, map_sub, Polynomial.aeval_X, map_one, map_sum] at h
  rw [h, LinearMap.sum_apply, Finset.sum_apply]
  simp only [map_pow, Polynomial.aeval_X, shift_pow_apply]
  exact sum_range_add f x

theorem submodule_eq_top_of_shift_mem (hp : p.Prime)
    {S : Submodule (ZMod p) (ZMod p → ZMod p)} (hS : ∀ f ∈ S, shift f ∈ S)
    {f : ZMod p → ZMod p} (hf : f ∈ S) (hsum : ∑ y, f y ≠ 0) : S = ⊤ := by
  set T : Module.End (ZMod p) (ZMod p → ZMod p) := shift - 1 with hT
  have hTS : ∀ g ∈ S, T g ∈ S := fun g hg => by
    rw [hT, LinearMap.sub_apply, Module.End.one_apply]
    exact S.sub_mem (hS g hg) hg
  have hTpow : ∀ n, ∀ g ∈ S, (T ^ n) g ∈ S := by
    intro n
    induction n with
    | zero => intro g hg; simpa using hg
    | succ n ih =>
      intro g hg
      rw [pow_succ', Module.End.mul_apply]
      exact hTS _ (ih g hg)
  have hnorm : ∀ g : ZMod p → ZMod p, (T ^ (p - 1)) g = fun _ => ∑ y, g y :=
    fun g => funext (shift_sub_one_pow_pred_apply hp g)
  have hconst : ∀ g : ZMod p → ZMod p, T g = 0 → g = fun _ => g 0 := by
    intro g hg
    have : shift g = g := by
      rw [hT, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at hg
      exact hg
    exact funext (eq_const_of_shift_eq g this)
  have hTconst : ∀ d : ZMod p, T (fun _ => d) = 0 := by
    intro d
    ext x
    simp [hT, shift_apply]
  have key : ∀ m, m ≤ p → ∀ g, (T ^ m) g = 0 → g ∈ S := by
    intro m
    induction m with
    | zero =>
      intro _ g hg
      rw [pow_zero, Module.End.one_apply] at hg
      rw [hg]
      exact S.zero_mem
    | succ m ih =>
      intro hm g hg
      have hTh : T ((T ^ m) g) = 0 := by
        rw [← Module.End.mul_apply, ← pow_succ']
        exact hg
      set d := (T ^ m) g 0
      have hh : (T ^ m) g = fun _ => d := hconst _ hTh
      set c := ∑ y, f y
      set w := (T ^ (p - 1 - m)) f
      have hw : w ∈ S := hTpow _ f hf
      have hTw : (T ^ m) w = fun _ => c := by
        rw [← Module.End.mul_apply, ← pow_add, show m + (p - 1 - m) = p - 1 by omega, hnorm]
      have hg' : g - (d * c⁻¹) • w ∈ S := by
        refine ih (by omega) _ ?_
        rw [map_sub, map_smul, hh, hTw]
        ext x
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
        have := Fact.mk hp
        rw [mul_assoc, inv_mul_cancel₀ hsum, mul_one, sub_self]
      have := S.add_mem hg' (S.smul_mem (d * c⁻¹) hw)
      simpa using this
  refine eq_top_iff.mpr fun g _ => key p le_rfl g ?_
  have h : (T ^ p) g = T ((T ^ (p - 1)) g) := by
    rw [← Module.End.mul_apply, ← pow_succ', Nat.sub_add_cancel hp.one_lt.le]
  rw [h, hnorm]
  exact hTconst _

end Translation

section CyclicWreath

variable {p : ℕ} [NeZero p] {P : Type*} [Group P]

omit [NeZero p] in
theorem kaloujnineKrasner_left_conjNormal (φ : P →* Multiplicative (ZMod p))
    (t : Multiplicative (ZMod p) → P) (ht : ∀ x, φ (t x) = x)
    (θ : φ.ker →* Multiplicative (ZMod p)) (r : φ.ker) (z x : Multiplicative (ZMod p)) :
    (kaloujnineKrasner φ t ht θ (MulAut.conjNormal (t z)⁻¹ r)).left x =
      (kaloujnineKrasner φ t ht θ r).left (z * x) := by
  have hs : (t (z * x))⁻¹ * t z * t x ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, ht, ht, ht]
    group
  have h1 : φ ((MulAut.conjNormal (t z)⁻¹ r : φ.ker) : P) = 1 :=
    MonoidHom.mem_ker.mp (MulAut.conjNormal (t z)⁻¹ r).2
  have h2 : φ (r : P) = 1 := MonoidHom.mem_ker.mp r.2
  rw [kaloujnineKrasner_left, kaloujnineKrasner_left]
  have key : (⟨_, kaloujnineKrasner_mem φ t ht (MulAut.conjNormal (t z)⁻¹ r) x⟩ : φ.ker) =
      (⟨_, hs⟩ : φ.ker)⁻¹ * ⟨_, kaloujnineKrasner_mem φ t ht r (z * x)⟩ * ⟨_, hs⟩ := by
    apply Subtype.ext
    simp only [h1, h2, inv_one, one_mul]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
    group
  rw [key, map_mul, map_mul, mul_comm, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]

theorem exists_surjective_regularWreathProduct (hp : p.Prime) (φ : P →* Multiplicative (ZMod p))
    (t : Multiplicative (ZMod p) → P) (ht : ∀ x, φ (t x) = x)
    (θ : φ.ker →* Multiplicative (ZMod p)) (u : φ.ker)
    (hu : ∏ x, θ (MulAut.conjNormal (t x)⁻¹ u) ≠ 1) :
    ∃ Ψ : P →* Multiplicative (ZMod p) ≀ᵣ Multiplicative (ZMod p), Function.Surjective Ψ := by
  set Ψ := kaloujnineKrasner φ t ht θ with hΨ
  refine ⟨Ψ, kaloujnineKrasner_surjective φ t ht θ ?_⟩
  have hleft : ∀ (r : φ.ker) (x : Multiplicative (ZMod p)),
      (Ψ r).left x = θ (MulAut.conjNormal (t x)⁻¹ r) := by
    intro r x
    rw [hΨ, kaloujnineKrasner_left]
    congr 1
    apply Subtype.ext
    simp [MonoidHom.mem_ker.mp r.2]
  let β : Additive φ.ker →+ (ZMod p → ZMod p) :=
    { toFun := fun r a => Multiplicative.toAdd ((Ψ r.toMul).left (Multiplicative.ofAdd a))
      map_zero' := by
        ext a
        simp
      map_add' := by
        intro r s
        ext a
        simp only [toMul_add, Subgroup.coe_mul, map_mul, RegularWreathProduct.mul_left,
          Pi.mul_apply, Pi.add_apply]
        rw [hΨ, kaloujnineKrasner_right, MonoidHom.mem_ker.mp r.toMul.2, inv_one, one_mul,
          toAdd_mul] }
  have hβ : ∀ r a, β r a = Multiplicative.toAdd ((Ψ r.toMul).left (Multiplicative.ofAdd a)) :=
    fun _ _ => rfl
  set S : Submodule (ZMod p) (ZMod p → ZMod p) := AddSubgroup.toZModSubmodule p β.range
  have hmemS : ∀ g, g ∈ S ↔ g ∈ β.range := fun g => Iff.rfl
  have htop : S = ⊤ := by
    refine submodule_eq_top_of_shift_mem hp (f := β (Additive.ofMul u)) ?_ ?_ ?_
    · rintro g hg
      rw [hmemS] at hg ⊢
      obtain ⟨r, rfl⟩ := hg
      refine ⟨Additive.ofMul (MulAut.conjNormal (t (Multiplicative.ofAdd 1))⁻¹ r.toMul), ?_⟩
      ext a
      rw [hβ, shift_apply, hβ, toMul_ofMul, hΨ, kaloujnineKrasner_left_conjNormal, ← ofAdd_add,
        add_comm]
    · exact (hmemS _).mpr ⟨_, rfl⟩
    · intro h0
      apply hu
      have hsum : ∑ a, β (Additive.ofMul u) a =
          Multiplicative.toAdd (∏ x, (Ψ u).left x) := by
        rw [toAdd_prod]
        exact Fintype.sum_equiv Multiplicative.ofAdd _ _ fun a => rfl
      rw [hsum] at h0
      have h1 : ∏ x, (Ψ u).left x = 1 := by
        rw [← ofAdd_toAdd (∏ x, (Ψ u).left x), h0, ofAdd_zero]
      rw [← h1]
      exact Finset.prod_congr rfl fun x _ => (hleft u x).symm
  intro f
  have hf : (fun a => Multiplicative.toAdd (f (Multiplicative.ofAdd a))) ∈ S := by
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨r, hr⟩ := (hmemS _).mp hf
  refine ⟨r.toMul, fun x => ?_⟩
  have := congrFun hr (Multiplicative.toAdd x)
  rw [hβ, ofAdd_toAdd] at this
  exact Multiplicative.toAdd.injective this

end CyclicWreath

end CFSG.RankThree.Transfer

end
