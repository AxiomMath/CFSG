module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartOne

@[expose] def sumZero6 : AddSubgroup (Fin 6 → ZMod 3) :=
  AddMonoidHom.ker (∑ i : Fin 6, Pi.evalAddMonoidHom (fun _ : Fin 6 => ZMod 3) i)

theorem mem_sumZero6 {a : Fin 6 → ZMod 3} : a ∈ sumZero6 ↔ ∑ i, a i = 0 := by
  simp [sumZero6, AddMonoidHom.mem_ker]

@[expose] def permSumZero (σ : Equiv.Perm (Fin 6)) : sumZero6 ≃+ sumZero6 where
  toFun a := ⟨fun i => (a : Fin 6 → ZMod 3) (σ.symm i), by
    rw [mem_sumZero6, Equiv.sum_comp σ.symm (a : Fin 6 → ZMod 3)]
    exact mem_sumZero6.1 a.2⟩
  invFun a := ⟨fun i => (a : Fin 6 → ZMod 3) (σ i), by
    rw [mem_sumZero6, Equiv.sum_comp σ (a : Fin 6 → ZMod 3)]
    exact mem_sumZero6.1 a.2⟩
  left_inv a := by
    apply Subtype.ext
    funext i
    simp
  right_inv a := by
    apply Subtype.ext
    funext i
    simp
  map_add' a b := by
    apply Subtype.ext
    funext i
    rfl

namespace CentralCoverThree

open scoped commutatorElement

section CentralCover

variable {X Y : Type*} [Group X] [Group Y] {φ : Y →* X}

theorem commutator_mul_central_left {c : Y} (hc : c ∈ Subgroup.center Y) (y w : Y) :
    ⁅y * c, w⁆ = ⁅y, w⁆ := by
  have h : ⁅c, w⁆ = 1 := Commute.commutator_eq (Subgroup.mem_center_iff.mp hc w).symm
  rw [commutatorElement_mul_left_eq_conj_mul, h]
  simp

theorem commutator_mul_central_right {c : Y} (hc : c ∈ Subgroup.center Y) (y w : Y) :
    ⁅y, w * c⁆ = ⁅y, w⁆ := by
  have h : ⁅y, c⁆ = 1 := Commute.commutator_eq (Subgroup.mem_center_iff.mp hc y)
  rw [commutatorElement_mul_right_eq_mul_conj, h]
  simp

theorem commutator_eq_of_map_eq (hker : φ.ker ≤ Subgroup.center Y) {y y' z z' : Y}
    (hy : φ y = φ y') (hz : φ z = φ z') : ⁅y, z⁆ = ⁅y', z'⁆ := by
  have hc : y⁻¹ * y' ∈ Subgroup.center Y := hker (by simp [MonoidHom.mem_ker, hy])
  have hd : z⁻¹ * z' ∈ Subgroup.center Y := hker (by simp [MonoidHom.mem_ker, hz])
  have e1 : y' = y * (y⁻¹ * y') := by group
  have e2 : z' = z * (z⁻¹ * z') := by group
  rw [e1, e2, commutator_mul_central_left hc, commutator_mul_central_right hd]

theorem commutator_mem_center_of_commute (hker : φ.ker ≤ Subgroup.center Y) {y z : Y}
    (h : Commute (φ y) (φ z)) : ⁅y, z⁆ ∈ Subgroup.center Y :=
  hker (by rw [MonoidHom.mem_ker, map_commutatorElement]; exact h.commutator_eq)

theorem commutator_mul_left_of_central {y y' z : Y} (h : ⁅y', z⁆ ∈ Subgroup.center Y) :
    ⁅y * y', z⁆ = ⁅y, z⁆ * ⁅y', z⁆ := by
  rw [commutatorElement_mul_left_eq_conj_mul, Subgroup.mem_center_iff.mp h y,
    mul_inv_cancel_right]
  exact (Subgroup.mem_center_iff.mp h _).symm

theorem commutator_mul_right_of_central {y z z' : Y} (h : ⁅y, z'⁆ ∈ Subgroup.center Y) :
    ⁅y, z * z'⁆ = ⁅y, z⁆ * ⁅y, z'⁆ := by
  have e : z * ⁅y, z'⁆ * z⁻¹ = ⁅y, z'⁆ := by
    rw [Subgroup.mem_center_iff.mp h z, mul_inv_cancel_right]
  rw [commutatorElement_mul_right_eq_mul_conj]
  calc ⁅y, z⁆ * z * ⁅y, z'⁆ * z⁻¹ = ⁅y, z⁆ * (z * ⁅y, z'⁆ * z⁻¹) := by simp only [mul_assoc]
    _ = ⁅y, z⁆ * ⁅y, z'⁆ := by rw [e]

end CentralCover

section TorusPairing

variable {X Y : Type*} [Group X] [Group Y] {φ : Y →* X} {A : Type*} [AddCommMonoid A]

noncomputable def torusPairing (hφ : Function.Surjective φ) (ι : Multiplicative A →* X)
    (a b : A) : Y :=
  ⁅Function.surjInv hφ (ι (Multiplicative.ofAdd a)),
    Function.surjInv hφ (ι (Multiplicative.ofAdd b))⁆

variable (hφ : Function.Surjective φ) (ι : Multiplicative A →* X)

theorem torusPairing_eq (hker : φ.ker ≤ Subgroup.center Y) {a b : A} {y z : Y}
    (hy : φ y = ι (Multiplicative.ofAdd a)) (hz : φ z = ι (Multiplicative.ofAdd b)) :
    ⁅y, z⁆ = torusPairing hφ ι a b :=
  commutator_eq_of_map_eq hker (hy.trans (Function.surjInv_eq hφ _).symm)
    (hz.trans (Function.surjInv_eq hφ _).symm)

theorem torus_comm (a b : A) :
    ι (Multiplicative.ofAdd a) * ι (Multiplicative.ofAdd b) =
      ι (Multiplicative.ofAdd b) * ι (Multiplicative.ofAdd a) := by
  rw [← map_mul ι, ← map_mul ι, ← ofAdd_add, ← ofAdd_add, add_comm]

theorem torusPairing_mem_center (hker : φ.ker ≤ Subgroup.center Y) (a b : A) :
    torusPairing hφ ι a b ∈ Subgroup.center Y :=
  commutator_mem_center_of_commute hker (by
    show _ * _ = _ * _
    rw [Function.surjInv_eq hφ, Function.surjInv_eq hφ]
    exact torus_comm ι a b)

theorem torusPairing_add_left (hker : φ.ker ≤ Subgroup.center Y) (a a' b : A) :
    torusPairing hφ ι (a + a') b = torusPairing hφ ι a b * torusPairing hφ ι a' b := by
  have h1 : φ (Function.surjInv hφ (ι (Multiplicative.ofAdd a)) *
      Function.surjInv hφ (ι (Multiplicative.ofAdd a'))) =
        ι (Multiplicative.ofAdd (a + a')) := by
    rw [map_mul, Function.surjInv_eq hφ, Function.surjInv_eq hφ, ← map_mul ι, ← ofAdd_add]
  rw [← torusPairing_eq hφ ι hker (b := b) h1 (Function.surjInv_eq hφ _)]
  exact commutator_mul_left_of_central (torusPairing_mem_center hφ ι hker a' b)

theorem torusPairing_add_right (hker : φ.ker ≤ Subgroup.center Y) (a b b' : A) :
    torusPairing hφ ι a (b + b') = torusPairing hφ ι a b * torusPairing hφ ι a b' := by
  have h1 : φ (Function.surjInv hφ (ι (Multiplicative.ofAdd b)) *
      Function.surjInv hφ (ι (Multiplicative.ofAdd b'))) =
        ι (Multiplicative.ofAdd (b + b')) := by
    rw [map_mul, Function.surjInv_eq hφ, Function.surjInv_eq hφ, ← map_mul ι, ← ofAdd_add]
  rw [← torusPairing_eq hφ ι hker (a := a) (Function.surjInv_eq hφ _) h1]
  exact commutator_mul_right_of_central (torusPairing_mem_center hφ ι hker a b')

theorem torusPairing_self (a : A) : torusPairing hφ ι a a = 1 :=
  commutatorElement_self _

theorem torusPairing_swap (a b : A) :
    torusPairing hφ ι b a = (torusPairing hφ ι a b)⁻¹ :=
  (commutatorElement_inv _ _).symm

theorem torusPairing_zero_left (hker : φ.ker ≤ Subgroup.center Y) (b : A) :
    torusPairing hφ ι 0 b = 1 := by
  rw [← torusPairing_eq hφ ι hker (a := 0) (y := 1) (by simp) (Function.surjInv_eq hφ _)]
  exact commutatorElement_one_left _

theorem torusPairing_zero_right (hker : φ.ker ≤ Subgroup.center Y) (a : A) :
    torusPairing hφ ι a 0 = 1 := by
  rw [← torusPairing_eq hφ ι hker (b := 0) (z := 1) (Function.surjInv_eq hφ _) (by simp)]
  exact commutatorElement_one_right _

theorem torusPairing_nsmul_left (hker : φ.ker ≤ Subgroup.center Y) (n : ℕ) (a b : A) :
    torusPairing hφ ι (n • a) b = torusPairing hφ ι a b ^ n := by
  induction n with
  | zero => simp [torusPairing_zero_left hφ ι hker]
  | succ n ih => rw [succ_nsmul, torusPairing_add_left hφ ι hker, ih, pow_succ]

theorem torusPairing_conj (hker : φ.ker ≤ Subgroup.center Y) (e : A ≃+ A) (n : X)
    (hn : ∀ a : A, n * ι (Multiplicative.ofAdd a) * n⁻¹ = ι (Multiplicative.ofAdd (e a)))
    (a b : A) : torusPairing hφ ι (e a) (e b) = torusPairing hφ ι a b := by
  set m : Y := Function.surjInv hφ n
  have hm : φ m = n := Function.surjInv_eq hφ n
  have hconj : ∀ a : A, φ (m * Function.surjInv hφ (ι (Multiplicative.ofAdd a)) * m⁻¹) =
      ι (Multiplicative.ofAdd (e a)) := fun a => by
    rw [map_mul, map_mul, map_inv, hm, Function.surjInv_eq hφ, hn]
  rw [← torusPairing_eq hφ ι hker (hconj a) (hconj b), ← conjugate_commutatorElement]
  have hc := torusPairing_mem_center hφ ι hker a b
  change m * torusPairing hφ ι a b * m⁻¹ = _
  rw [Subgroup.mem_center_iff.mp hc m, mul_inv_cancel_right]

end TorusPairing

section SumZeroSix

theorem permSumZero_apply (σ : Equiv.Perm (Fin 6)) (a : sumZero6) (i : Fin 6) :
    ((permSumZero σ a : sumZero6) : Fin 6 → ZMod 3) i = (a : Fin 6 → ZMod 3) (σ.symm i) := rfl

@[expose] def dvec (i : Fin 6) : sumZero6 :=
  ⟨fun k => (if k = i then 1 else 0) + (if k = 0 then 2 else 0), by
    rw [mem_sumZero6, Finset.sum_add_distrib]
    simp
    decide⟩

theorem dvec_apply (i k : Fin 6) : ((dvec i : sumZero6) : Fin 6 → ZMod 3) k =
    (if k = i then 1 else 0) + (if k = 0 then 2 else 0) := rfl

theorem dvec_zero : dvec 0 = 0 := by
  apply Subtype.ext
  funext k
  rw [dvec_apply]
  by_cases hk : k = 0
  · subst hk
    decide
  · simp [hk]

theorem permSumZero_swap_dvec {i j : Fin 6} (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    permSumZero (Equiv.swap i j) (dvec i) = dvec j := by
  apply Subtype.ext
  funext k
  rw [permSumZero_apply, dvec_apply, dvec_apply, Equiv.symm_swap, Equiv.swap_apply_def]
  split_ifs <;> simp_all

theorem permSumZero_swap_dvec' {i j : Fin 6} (hi : i ≠ 0) (hj : j ≠ 0) (hij : i ≠ j) :
    permSumZero (Equiv.swap i j) (dvec j) = dvec i := by
  rw [Equiv.swap_comm]
  exact permSumZero_swap_dvec hj hi hij.symm

theorem eq_sum_dvec (a : sumZero6) :
    a = ∑ i : Fin 6, ((a : Fin 6 → ZMod 3) i).val • dvec i := by
  have hsum := mem_sumZero6.1 a.2
  apply Subtype.ext
  funext k
  rw [AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
  simp only [AddSubmonoidClass.coe_nsmul, Pi.smul_apply, dvec_apply, nsmul_eq_mul,
    ZMod.natCast_zmod_val]
  simp only [mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, hsum, zero_mul, add_zero]
  simp

theorem mem_closure_dvec (a : sumZero6) : a ∈ AddSubgroup.closure (Set.range dvec) := by
  have hgen : ∀ i, dvec i ∈ AddSubgroup.closure (Set.range dvec) := fun i =>
    AddSubgroup.subset_closure (Set.mem_range_self i)
  rw [eq_sum_dvec a]
  refine sum_mem fun i _ => ?_
  exact AddSubgroup.nsmul_mem _ (hgen i) _

theorem three_nsmul_sumZero6 (a : sumZero6) : 3 • a = 0 := by
  apply Subtype.ext
  funext k
  have h3 : (3 : ZMod 3) = 0 := by decide
  simp [← Nat.cast_smul_eq_nsmul (ZMod 3), h3]

end SumZeroSix

section Vanishing

variable {X Y : Type*} [Group X] [Group Y] {φ : Y →* X} (hφ : Function.Surjective φ)
  (ι : Multiplicative sumZero6 →* X) (hker : φ.ker ≤ Subgroup.center Y)
  (hσ : ∀ σ : Equiv.Perm (Fin 6), ∃ n : X, ∀ a : sumZero6,
    n * ι (Multiplicative.ofAdd a) * n⁻¹ = ι (Multiplicative.ofAdd (permSumZero σ a)))

include hker hσ in
theorem torusPairing_dvec (i j : Fin 6) : torusPairing hφ ι (dvec i) (dvec j) = 1 := by
  by_cases hi : i = 0
  · subst hi
    rw [dvec_zero]
    exact torusPairing_zero_left hφ ι hker _
  by_cases hj : j = 0
  · subst hj
    rw [dvec_zero]
    exact torusPairing_zero_right hφ ι hker _
  by_cases hij : i = j
  · subst hij
    exact torusPairing_self hφ ι _
  obtain ⟨n, hn⟩ := hσ (Equiv.swap i j)
  have h1 := torusPairing_conj hφ ι hker (permSumZero (Equiv.swap i j)) n hn (dvec i) (dvec j)
  rw [permSumZero_swap_dvec hi hj hij, permSumZero_swap_dvec' hi hj hij,
    torusPairing_swap hφ ι (dvec i) (dvec j)] at h1
  have h3 : torusPairing hφ ι (dvec i) (dvec j) ^ 3 = 1 := by
    rw [← torusPairing_nsmul_left hφ ι hker, three_nsmul_sumZero6,
      torusPairing_zero_left hφ ι hker]
  set z := torusPairing hφ ι (dvec i) (dvec j)
  have h2 : z * z = 1 := by
    calc z * z = z * z⁻¹ := by rw [h1]
      _ = 1 := mul_inv_cancel z
  calc z = z * (z * z) := by rw [h2, mul_one]
    _ = z ^ 3 := (pow_three z).symm
    _ = 1 := h3

include hker hσ in
theorem torusPairing_eq_one (a b : sumZero6) : torusPairing hφ ι a b = 1 := by
  have hgen : ∀ i b, torusPairing hφ ι (dvec i) b = 1 := fun i b =>
    AddSubgroup.closure_induction (k := Set.range dvec)
      (p := fun b _ => torusPairing hφ ι (dvec i) b = 1)
      (by
        rintro _ ⟨j, rfl⟩
        exact torusPairing_dvec hφ ι hker hσ i j)
      (torusPairing_zero_right hφ ι hker _)
      (fun x y _ _ hx hy => by rw [torusPairing_add_right hφ ι hker, hx, hy, one_mul])
      (fun x _ hx => by
        have h := torusPairing_add_right hφ ι hker (dvec i) x (-x)
        rwa [add_neg_cancel, torusPairing_zero_right hφ ι hker, hx, one_mul, eq_comm] at h)
      (mem_closure_dvec b)
  exact AddSubgroup.closure_induction (k := Set.range dvec)
    (p := fun a _ => torusPairing hφ ι a b = 1)
    (by
      rintro _ ⟨i, rfl⟩
      exact hgen i b)
    (torusPairing_zero_left hφ ι hker _)
    (fun x y _ _ hx hy => by rw [torusPairing_add_left hφ ι hker, hx, hy, one_mul])
    (fun x _ hx => by
      have h := torusPairing_add_left hφ ι hker x (-x) b
      rwa [add_neg_cancel, torusPairing_zero_left hφ ι hker, hx, one_mul, eq_comm] at h)
    (mem_closure_dvec a)

end Vanishing

section Counting

theorem card_sumZero6 : Nat.card sumZero6 = 3 ^ 5 := by
  let s : (Fin 6 → ZMod 3) →+ ZMod 3 :=
    ∑ i : Fin 6, Pi.evalAddMonoidHom (fun _ : Fin 6 => ZMod 3) i
  have hs : Function.Surjective s := fun t => ⟨fun i => if i = 0 then t else 0, by simp [s]⟩
  have h := AddSubgroup.card_ker_mul_card_of_surjective hs
  have h6 : Nat.card (Fin 6 → ZMod 3) = 3 ^ 6 := by simp
  rw [h6, Nat.card_zmod] at h
  change Nat.card (AddMonoidHom.ker s) * 3 = 3 ^ 6 at h
  change Nat.card (AddMonoidHom.ker s) = 3 ^ 5
  omega

theorem const_mem_sumZero6 (k : ZMod 3) : (fun _ : Fin 6 => k) ∈ sumZero6 := by
  rw [mem_sumZero6]
  revert k
  decide

theorem card_ker_eq_three {X : Type*} [Group X] (ι : Multiplicative sumZero6 →* X)
    (hι : ∀ a : sumZero6, ι (Multiplicative.ofAdd a) = 1 ↔
      ∃ k : ZMod 3, ∀ i, (a : Fin 6 → ZMod 3) i = k) : Nat.card ι.ker = 3 := by
  let e : ZMod 3 ≃ ι.ker :=
    { toFun := fun k => ⟨Multiplicative.ofAdd ⟨fun _ => k, const_mem_sumZero6 k⟩,
        MonoidHom.mem_ker.2 ((hι _).2 ⟨k, fun _ => rfl⟩)⟩
      invFun := fun x => ((Multiplicative.toAdd x.1 : sumZero6) : Fin 6 → ZMod 3) 0
      left_inv := fun k => rfl
      right_inv := fun x => by
        obtain ⟨k, hk⟩ := (hι (Multiplicative.toAdd x.1)).1 (MonoidHom.mem_ker.1 x.2)
        apply Subtype.ext
        apply Multiplicative.toAdd.injective
        apply Subtype.ext
        funext i
        exact (hk 0).trans (hk i).symm }
  rw [← Nat.card_congr e, Nat.card_zmod]

theorem card_range_eq {X : Type*} [Group X] (ι : Multiplicative sumZero6 →* X)
    (hι : ∀ a : sumZero6, ι (Multiplicative.ofAdd a) = 1 ↔
      ∃ k : ZMod 3, ∀ i, (a : Fin 6 → ZMod 3) i = k) : Nat.card ι.range = 3 ^ 4 := by
  have h := Subgroup.card_ker_mul_card_range ι
  rw [card_ker_eq_three ι hι, ← Nat.card_congr (Multiplicative.ofAdd (α := sumZero6)),
    card_sumZero6] at h
  omega

end Counting

section Elementary

theorem exists_isElementaryAbelian_of_surjective_cube {F T : Type*} [Group F] [Group T]
    [Finite F] [IsMulCommutative F] (ψ : F →* T) (hψ : Function.Surjective ψ)
    (hexp : ∀ x : F, ψ x ^ 3 = 1) (hT : Nat.card T = 3 ^ 4) :
    ∃ U : Subgroup F, CFSG.IsElementaryAbelian 3 U ∧ Nat.card U = 3 ^ 4 := by
  obtain ⟨c, hc⟩ : ∃ c : F →* F, ∀ x, c x = x ^ 3 :=
    ⟨MonoidHom.mk' (fun x => x ^ 3) fun x y => Commute.mul_pow (mul_comm' x y) 3, fun _ => rfl⟩
  have hrange : c.range ≤ ψ.ker := by
    rintro _ ⟨x, rfl⟩
    rw [MonoidHom.mem_ker, hc, map_pow]
    exact hexp x
  have h1 := Subgroup.card_ker_mul_card_range c
  have h2 := Subgroup.card_ker_mul_card_of_surjective hψ
  have h3 := Subgroup.card_le_of_le hrange
  have hpos : 0 < Nat.card ψ.ker := Nat.card_pos
  have h4 : 3 ^ 4 ≤ Nat.card c.ker := by
    rw [hT] at h2
    have h5 : Nat.card ψ.ker * 3 ^ 4 ≤ Nat.card ψ.ker * Nat.card c.ker :=
      calc Nat.card ψ.ker * 3 ^ 4 = Nat.card c.ker * Nat.card c.range := h2.trans h1.symm
        _ ≤ Nat.card c.ker * Nat.card ψ.ker := Nat.mul_le_mul_left _ h3
        _ = Nat.card ψ.ker * Nat.card c.ker := Nat.mul_comm _ _
    exact Nat.le_of_mul_le_mul_left h5 hpos
  have hcube : ∀ y : c.ker, (y : F) ^ 3 = 1 := fun y => by
    rw [← hc]
    exact MonoidHom.mem_ker.1 y.2
  have hP : IsPGroup 3 c.ker := fun g => ⟨1, Subtype.ext (by simpa using hcube g)⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hk4 : 4 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).1 (hk ▸ h4)
  obtain ⟨V, hV⟩ := Sylow.exists_subgroup_card_pow_prime (G := c.ker) 3 (n := 4)
    (by rw [hk]; exact pow_dvd_pow 3 hk4)
  refine ⟨V.map c.ker.subtype, ?_, ?_⟩
  · refine { toIsMulCommutative := inferInstance, exponent_dvd_p := ?_ }
    refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x => ?_
    apply Subtype.ext
    obtain ⟨y, _, hyx⟩ := Subgroup.mem_map.mp x.2
    show (x : F) ^ 3 = 1
    rw [← hyx]
    exact hcube y
  · rw [Subgroup.card_subtype]
    exact hV

end Elementary

theorem pow_three_eq_one_sumZero6 (a : Multiplicative sumZero6) : a ^ 3 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  exact three_nsmul_sumZero6 _

end CentralCoverThree

open CentralCoverThree in
theorem central_cover_elementary_three_four {X Y : Type*} [Group X] [Group Y] [Finite Y]
    (φ : Y →* X) (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    (ι : Multiplicative sumZero6 →* X)
    (hι : ∀ a : sumZero6, ι (Multiplicative.ofAdd a) = 1 ↔
      ∃ k : ZMod 3, ∀ i, (a : Fin 6 → ZMod 3) i = k)
    (hσ : ∀ σ : Equiv.Perm (Fin 6), ∃ n : X, ∀ a : sumZero6,
      n * ι (Multiplicative.ofAdd a) * n⁻¹ = ι (Multiplicative.ofAdd (permSumZero σ a))) :
    ∃ U : Subgroup Y, CFSG.IsElementaryAbelian 3 U ∧ Nat.card U = 3 ^ 4 := by
  have hcomm : ∀ x y : Y, φ x ∈ ι.range → φ y ∈ ι.range → x * y = y * x := by
    intro x y hx hy
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 hx
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 hy
    have h := torusPairing_eq hφ ι hker (a := Multiplicative.toAdd a) (b := Multiplicative.toAdd b)
      (y := x) (z := y) (by rw [ofAdd_toAdd]; exact ha.symm) (by rw [ofAdd_toAdd]; exact hb.symm)
    rw [torusPairing_eq_one hφ ι hker hσ] at h
    exact commutatorElement_eq_one_iff_mul_comm.1 h
  have : IsMulCommutative (ι.range.comap φ) :=
    IsMulCommutative.of_comm fun x y => Subtype.ext (hcomm x y x.2 y.2)
  have hexp : ∀ x : ι.range.comap φ, (φ.subgroupComap ι.range x) ^ 3 = 1 := fun x => by
    obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 (φ.subgroupComap ι.range x).2
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← ha, ← map_pow, pow_three_eq_one_sumZero6, map_one]
    rfl
  obtain ⟨U, hU, hUcard⟩ := exists_isElementaryAbelian_of_surjective_cube
    (φ.subgroupComap ι.range) (φ.subgroupComap_surjective ι.range hφ) hexp (card_range_eq ι hι)
  have := hU
  refine ⟨U.map (ι.range.comap φ).subtype, CFSG.IsElementaryAbelian.map_subtype, ?_⟩
  rw [Subgroup.card_subtype]
  exact hUcard

end CFSG.RankThree.PartOne
