module

public import CFSG.Milestones.ASVolI.H6

public section

open scoped commutatorElement Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

abbrev PairN (n : ℕ) : Type := Multiplicative (Fin n → ZMod 2) × Multiplicative (Fin n → ZMod 2)

@[expose] def dualGLn (n : ℕ) (g : GL (Fin n) (ZMod 2)) : GL (Fin n) (ZMod 2) where
  val := ((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ
  inv := (g : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ
  val_inv := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.transpose_one]
  inv_val := by
    rw [← Matrix.transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.transpose_one]

@[expose] def dualHomN (n : ℕ) : GL (Fin n) (ZMod 2) →* GL (Fin n) (ZMod 2) where
  toFun := dualGLn n
  map_one' := Units.ext (by
    show (((1 : GL (Fin n) (ZMod 2))⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ = 1
    rw [inv_one, Units.val_one, Matrix.transpose_one])
  map_mul' g h := Units.ext (by
    show (((g * h)⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ =
      ((g⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ *
        ((h⁻¹ : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2))ᵀ
    rw [mul_inv_rev, Units.val_mul, Matrix.transpose_mul])

@[expose] noncomputable def pairActN (n : ℕ) : GL (Fin n) (ZMod 2) →* MulAut (PairN n) :=
  prodAct (natHom n (ZMod 2)) ((natHom n (ZMod 2)).comp (dualHomN n))

@[expose] noncomputable def Lg (n : ℕ) : Subgroup (MulAut (PairN n)) := (pairActN n).range

@[expose] def swapN (n : ℕ) : MulAut (PairN n) := MulEquiv.prodComm

@[expose] noncomputable def Mg (n : ℕ) : Subgroup (MulAut (PairN n)) := Lg n ⊔ Subgroup.zpowers (swapN n)

@[expose] def V1n (n : ℕ) : Subgroup (PairN n) :=
  (⊤ : Subgroup (Multiplicative (Fin n → ZMod 2))).prod ⊥

@[expose] def V2n (n : ℕ) : Subgroup (PairN n) :=
  (⊥ : Subgroup (Multiplicative (Fin n → ZMod 2))).prod ⊤

@[expose] def pairQn (n : ℕ) (x : PairN n) : ZMod 2 :=
  ∑ i, Multiplicative.toAdd x.1 i * Multiplicative.toAdd x.2 i

@[expose] def polarN (n : ℕ) (x y : PairN n) : ZMod 2 :=
  ∑ i, (Multiplicative.toAdd x.1 i * Multiplicative.toAdd y.2 i +
    Multiplicative.toAdd y.1 i * Multiplicative.toAdd x.2 i)

theorem polarN_mul_left {n : ℕ} (x y s : PairN n) :
    polarN n (x * y) s = polarN n x s + polarN n y s := by
  unfold polarN
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Prod.fst_mul, Prod.snd_mul, toAdd_mul, Pi.add_apply]
  ring

theorem polarN_inv_left {n : ℕ} (x s : PairN n) : polarN n x⁻¹ s = polarN n x s := by
  unfold polarN
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ∀ u : ZMod 2, -u = u := fun u => ZMod.neg_eq_self_mod_two u
  simp only [Prod.fst_inv, Prod.snd_inv, toAdd_inv, Pi.neg_apply, h]

@[expose] def perpN (n : ℕ) (S : Subgroup (PairN n)) : Subgroup (PairN n) where
  carrier := {x | ∀ s ∈ S, polarN n x s = 0}
  mul_mem' {x y} hx hy s hs := by
    rw [polarN_mul_left, hx s hs, hy s hs, add_zero]
  one_mem' s _ := by simp [polarN]
  inv_mem' {x} hx s hs := by
    exact (polarN_inv_left x s).trans (hx s hs)

@[expose] def IsQuadFormN {n : ℕ} (q : PairN n → ZMod 2) : Prop :=
  q 1 = 0 ∧ ∀ x x' y : PairN n,
    q (x * x' * y) + q (x * x') + q y = (q (x * y) + q x + q y) + (q (x' * y) + q x' + q y)

@[expose] def IsNondegN {n : ℕ} (q : PairN n → ZMod 2) : Prop :=
  ∀ x : PairN n, x ≠ 1 → ∃ y : PairN n, q (x * y) + q x + q y ≠ 0

@[expose] def Oorb (n : ℕ) : Fin 3 → Set (PairN n)
  | 0 => {x | x ≠ 1 ∧ (x ∈ V1n n ∨ x ∈ V2n n)}
  | 1 => {x | x.1 ≠ 1 ∧ x.2 ≠ 1 ∧ pairQn n x = 0}
  | 2 => {x | x.1 ≠ 1 ∧ x.2 ≠ 1 ∧ pairQn n x = 1}

@[expose] def ThetaIso (n : ℕ) (t : MulAut (PairN n)) : Prop :=
  commV (Subgroup.zpowers t) = fixV (Subgroup.zpowers t) ∧
  (∀ w ∈ V1n n, ∀ w' ∈ V1n n, w * t w = w' * t w' → w = w') ∧
  (∀ x ∈ fixV (Subgroup.zpowers t), ∃ w ∈ V1n n, x = w * t w) ∧
  (∀ w ∈ V1n n, w * t w ∈ fixV (Subgroup.zpowers t)) ∧
  (∀ g ∈ Lg n ⊓ Subgroup.centralizer ({t} : Set (MulAut (PairN n))), ∀ w ∈ V1n n,
    g (w * t w) = g w * t (g w))

end CFSG.ASVolI.ChH
