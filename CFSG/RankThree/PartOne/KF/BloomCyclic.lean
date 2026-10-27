module

public import CFSG.RankThree.PartOne.KF.BloomBasic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.RankThree.PartOne.KFBloom

open Matrix Polynomial

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem aeval_conj_unit {K : Type*} [Field K] {n : ℕ} (g : GL (Fin n) K)
    (b : Matrix (Fin n) (Fin n) K) (q : K[X]) :
    aeval ((g : Matrix (Fin n) (Fin n) K) * b *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) q =
      (g : Matrix (Fin n) (Fin n) K) * aeval b q *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have hgi' : ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      (g : Matrix (Fin n) (Fin n) K) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hpow : ∀ k : ℕ, ((g : Matrix (Fin n) (Fin n) K) * b *
      ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) ^ k =
      (g : Matrix (Fin n) (Fin n) K) * b ^ k *
        ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ih]
      calc (g : Matrix (Fin n) (Fin n) K) * b ^ k *
            ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
            ((g : Matrix (Fin n) (Fin n) K) * b *
              ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
          = (g : Matrix (Fin n) (Fin n) K) * b ^ k *
            (((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
              (g : Matrix (Fin n) (Fin n) K)) * b *
              ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
            simp only [Matrix.mul_assoc]
        _ = _ := by rw [hgi']; simp only [Matrix.mul_one, pow_succ, Matrix.mul_assoc]
  induction q using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq, Matrix.mul_add, Matrix.add_mul]
  | monomial k a =>
    simp only [aeval_monomial, hpow]
    rw [Algebra.algebraMap_eq_smul_one]
    simp only [smul_mul_assoc, Matrix.mul_smul, Matrix.one_mul]

theorem adjoin_singleton_comm {K : Type*} [Field K] {n : ℕ} (X : Matrix (Fin n) (Fin n) K)
    {a b : Matrix (Fin n) (Fin n) K} (ha : a ∈ Algebra.adjoin K {X})
    (hb : b ∈ Algebra.adjoin K {X}) : a * b = b * a := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at ha hb
  obtain ⟨q1, rfl⟩ := ha
  obtain ⟨q2, rfl⟩ := hb
  simp only [← map_mul, mul_comm q1 q2]

theorem card_roots_adjoin_le {K : Type*} [Field K] [Finite K]
    (X : Matrix (Fin 3) (Fin 3) K)
    (hinj : ∀ a ∈ Algebra.adjoin K {X}, a ≠ 0 → ∀ v : Fin 3 → K, a *ᵥ v = 0 → v = 0) :
    ∃ R : Finset (Algebra.adjoin K {X}),
      (∀ b : Algebra.adjoin K {X},
        b ∈ R ↔ aeval (b : Matrix (Fin 3) (Fin 3) K) (minpoly K X) = 0) ∧
      R.card ≤ 3 := by
  classical
  set A : Subalgebra K (Matrix (Fin 3) (Fin 3) K) := Algebra.adjoin K {X} with hA
  let _ : CommRing A :=
    { (inferInstance : Ring A) with
      mul_comm := fun a b => Subtype.ext (adjoin_singleton_comm X a.2 b.2) }
  have _ : NoZeroDivisors A := ⟨fun {a b} hab => by
    by_cases ha : (a : Matrix (Fin 3) (Fin 3) K) = 0
    · exact Or.inl (Subtype.ext ha)
    · right
      apply Subtype.ext
      ext i j
      have hab' : (a : Matrix (Fin 3) (Fin 3) K) * (b : Matrix (Fin 3) (Fin 3) K) = 0 := by
        have := congrArg (fun x : A => (x : Matrix (Fin 3) (Fin 3) K)) hab
        simpa using this
      have h1 : ∀ v : Fin 3 → K, (b : Matrix (Fin 3) (Fin 3) K) *ᵥ v = 0 := by
        intro v
        apply hinj (a : Matrix (Fin 3) (Fin 3) K) a.2 ha
        rw [Matrix.mulVec_mulVec, hab', Matrix.zero_mulVec]
      have := congrFun (h1 (Pi.single j 1)) i
      simpa [Matrix.mulVec_single_one] using this⟩
  have _ : IsDomain A := NoZeroDivisors.to_isDomain A
  set P : A[X] := (minpoly K X).map (algebraMap K A) with hP
  have hmonic : (minpoly K X).Monic := minpoly.monic (Matrix.isIntegral X)
  have hPne : P ≠ 0 := (hmonic.map _).ne_zero
  have hPdeg : P.natDegree ≤ 3 := by
    refine (Polynomial.natDegree_map_le).trans ?_
    have h1 := Polynomial.natDegree_le_of_dvd (Matrix.minpoly_dvd_charpoly X)
      (Matrix.charpoly_monic X).ne_zero
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin] at h1
  refine ⟨P.roots.toFinset, fun b => ?_, ?_⟩
  · rw [Multiset.mem_toFinset, Polynomial.mem_roots hPne, Polynomial.IsRoot.def, hP,
      Polynomial.eval_map_algebraMap]
    have : ((aeval b (minpoly K X) : A) : Matrix (Fin 3) (Fin 3) K) =
        aeval (b : Matrix (Fin 3) (Fin 3) K) (minpoly K X) :=
      (Polynomial.aeval_algHom_apply A.val b (minpoly K X)).symm
    constructor
    · intro h
      rw [← this, h]
      rfl
    · intro h
      apply Subtype.ext
      rw [this, h]
      rfl
  · exact (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' P).trans hPdeg)

theorem cyclic_conj_fixed {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (h0 : GL (Fin 3) (ZMod p))
    (hirr : ∀ W : Submodule (ZMod p) (Fin 3 → ZMod p),
      (∀ w ∈ W, (h0 : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w ∈ W) →
      (∀ w ∈ W, ((h0⁻¹ : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ w ∈ W) →
        W = ⊥ ∨ W = ⊤)
    {g : GL (Fin 3) (ZMod p)} (hgp : g ^ p = 1)
    (hnorm : g * h0 * g⁻¹ ∈ Subgroup.zpowers h0) :
    g * h0 * g⁻¹ = h0 := by
  classical
  set K := ZMod p
  set X : Matrix (Fin 3) (Fin 3) K := (h0 : Matrix (Fin 3) (Fin 3) K) with hX
  set A : Subalgebra K (Matrix (Fin 3) (Fin 3) K) := Algebra.adjoin K {X} with hA
  have hXA : X ∈ A := Algebra.self_mem_adjoin_singleton K X
  have hinvA : ((h0⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ∈ A := by
    have hn : 0 < orderOf h0 := orderOf_pos h0
    have h1 : h0⁻¹ = h0 ^ (orderOf h0 - 1) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ', Nat.sub_add_cancel hn, pow_orderOf_eq_one]
    rw [h1, Units.val_pow_eq_pow_val]
    exact A.pow_mem hXA _
  have hzpow : ∀ k : ℤ, ((h0 ^ k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ∈ A := by
    intro k
    induction k using Int.induction_on with
    | zero => simp
    | succ i ih => rw [_root_.zpow_add_one, Units.val_mul]; exact A.mul_mem ih hXA
    | pred i ih => rw [_root_.zpow_sub_one, Units.val_mul]; exact A.mul_mem ih hinvA
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb => adjoin_singleton_comm X ha hb
  have hinj : ∀ a ∈ A, a ≠ 0 → ∀ v : Fin 3 → K, a *ᵥ v = 0 → v = 0 := by
    intro a ha ha0 v hv
    let W : Submodule K (Fin 3 → K) := LinearMap.ker (Matrix.toLin' a)
    have hWX : ∀ w ∈ W, X *ᵥ w ∈ W := by
      intro w hw
      have hw' : a *ᵥ w = 0 := hw
      show a *ᵥ (X *ᵥ w) = 0
      rw [Matrix.mulVec_mulVec, hcomm a ha X hXA, ← Matrix.mulVec_mulVec, hw', Matrix.mulVec_zero]
    have hWinv : ∀ w ∈ W, ((h0⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W := by
      intro w hw
      have hw' : a *ᵥ w = 0 := hw
      show a *ᵥ (((h0⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w) = 0
      rw [Matrix.mulVec_mulVec, hcomm a ha _ hinvA, ← Matrix.mulVec_mulVec, hw',
        Matrix.mulVec_zero]
    rcases hirr W hWX hWinv with hbot | htop
    · have : v ∈ W := hv
      rw [hbot] at this
      simpa using this
    · exfalso
      apply ha0
      ext i j
      have : (Pi.single j (1 : K)) ∈ W := by rw [htop]; trivial
      have h2 := congrFun (show a *ᵥ (Pi.single j 1) = 0 from this) i
      simpa [Matrix.mulVec_single_one] using h2
  obtain ⟨R, hR, hRcard⟩ := card_roots_adjoin_le X hinj
  have hyA : ((g * h0 * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ∈ A := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hnorm
    rw [← hk]
    exact hzpow k
  have hy : (g : Matrix (Fin 3) (Fin 3) K) * X *
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((g * h0 * g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    simp [hX, Units.val_mul]
  have hconjA : ∀ b ∈ A, (g : Matrix (Fin 3) (Fin 3) K) * b *
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ∈ A := by
    intro b hb
    have hb' : b ∈ (aeval (R := K) X).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]
      exact hb
    obtain ⟨q, hq⟩ := hb'
    have hq' : aeval X q = b := hq
    rw [← hq', ← aeval_conj_unit g X q, hy]
    exact (Algebra.adjoin_le (Set.singleton_subset_iff.mpr hyA))
      (Polynomial.aeval_mem_adjoin_singleton K _)
  have hmem : ∀ b : A, b ∈ R → (⟨(g : Matrix (Fin 3) (Fin 3) K) * b *
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), hconjA b b.2⟩ : A) ∈ R := by
    intro b hb
    rw [hR] at hb ⊢
    show aeval ((g : Matrix (Fin 3) (Fin 3) K) * (b : Matrix (Fin 3) (Fin 3) K) *
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) (minpoly K X) = 0
    rw [aeval_conj_unit, hb]
    simp
  let σ : R → R := fun b => ⟨⟨(g : Matrix (Fin 3) (Fin 3) K) * (b : A) *
      ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), hconjA b b.1.2⟩, hmem b b.2⟩
  have hσiter : ∀ k : ℕ, ∀ b : R, (((σ^[k] b : R) : A) : Matrix (Fin 3) (Fin 3) K) =
      ((g ^ k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((b : A) : Matrix (Fin 3) (Fin 3) K) *
        (((g ^ k)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    intro k
    induction k with
    | zero => intro b; simp
    | succ k ih =>
      intro b
      rw [Function.iterate_succ_apply']
      show (g : Matrix (Fin 3) (Fin 3) K) * (((σ^[k] b : R) : A) : Matrix (Fin 3) (Fin 3) K) *
        ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
      rw [ih]
      simp only [pow_succ', _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]
  have hσper : ∀ b : R, σ^[p] b = b := by
    intro b
    apply Subtype.ext
    apply Subtype.ext
    rw [hσiter, hgp]
    simp
  have hcardR : Nat.card R < p := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    omega
  have hfix := self_eq_of_iterate_prime hcardR σ hσper
  have hXR : (⟨X, hXA⟩ : A) ∈ R := by
    rw [hR]
    exact minpoly.aeval K X
  have h1 := hfix ⟨⟨X, hXA⟩, hXR⟩
  have h2 := congrArg (fun b : R => (((b : A)) : Matrix (Fin 3) (Fin 3) K)) h1
  simp only [σ] at h2
  apply Units.ext
  simp only [Units.val_mul]
  rw [Matrix.mul_assoc] at *
  exact h2

end CFSG.RankThree.PartOne.KFBloom
