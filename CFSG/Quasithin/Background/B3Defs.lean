module

public import CFSG.Quasithin.Background.B3Sec
public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Quasithin.B3

structure U (n : ℕ) where
  val : Fin n → ZMod 2
  deriving DecidableEq

namespace U

variable {n : ℕ}

@[ext] theorem ext {a b : U n} (h : ∀ i, a.val i = b.val i) : a = b := by
  cases a; cases b
  congr
  funext i
  exact h i

@[expose] def equiv (n : ℕ) : U n ≃ Multiplicative (Fin n → ZMod 2) where
  toFun w := Multiplicative.ofAdd w.val
  invFun f := ⟨Multiplicative.toAdd f⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instCommGroup (n : ℕ) : CommGroup (U n) := (equiv n).commGroup

instance instFintype (n : ℕ) : Fintype (U n) :=
  Fintype.ofEquiv (Fin n → ZMod 2) ⟨fun f => ⟨f⟩, fun w => w.val, fun _ => rfl, fun _ => rfl⟩

@[simp] theorem val_mul (a b : U n) (i : Fin n) : (a * b).val i = a.val i + b.val i := rfl

@[simp] theorem val_one (i : Fin n) : (1 : U n).val i = 0 := rfl

@[simp] theorem val_inv (a : U n) (i : Fin n) : (a⁻¹).val i = - a.val i := rfl

end U

@[expose] def permEquiv (n : ℕ) (σ : Equiv.Perm (Fin n)) : MulAut (U n) where
  toFun w := ⟨fun i => w.val (σ.symm i)⟩
  invFun w := ⟨fun i => w.val (σ i)⟩
  left_inv w := by
    apply U.ext
    intro i
    simp
  right_inv w := by
    apply U.ext
    intro i
    simp
  map_mul' a b := by
    apply U.ext
    intro i
    simp

@[expose] def permAct (n : ℕ) : Equiv.Perm (Fin n) →* MulAut (U n) where
  toFun := permEquiv n
  map_one' := by
    refine MulEquiv.ext fun w => ?_
    apply U.ext
    intro i
    rfl
  map_mul' σ τ := by
    refine MulEquiv.ext fun w => ?_
    apply U.ext
    intro i
    rfl

theorem permAct_val (n : ℕ) (σ : Equiv.Perm (Fin n)) (w : U n) (i : Fin n) :
    (permAct n σ w).val i = w.val (σ.symm i) := rfl

@[expose] def eVec (n : ℕ) : U n := ⟨fun _ => 1⟩

@[expose] def wt (n : ℕ) : U n →* Multiplicative (ZMod 2) where
  toFun w := Multiplicative.ofAdd (∑ i, w.val i)
  map_one' := by simp
  map_mul' a b := by simp [Finset.sum_add_distrib, ofAdd_add]

@[expose] def U0 (n : ℕ) : Subgroup (U n) := (wt n).ker

@[expose] def Esub (n : ℕ) : Subgroup (U n) := Subgroup.zpowers (eVec n)

theorem isInv_top (n : ℕ) : IsInv (permAct n) (⊤ : Subgroup (U n)) := fun _ _ _ => trivial

theorem isInv_bot (n : ℕ) : IsInv (permAct n) (⊥ : Subgroup (U n)) := by
  intro g w hw
  rw [Subgroup.mem_bot] at hw ⊢
  rw [hw, map_one]

theorem isInv_U0 (n : ℕ) : IsInv (permAct n) (U0 n) := by
  intro g w hw
  have hw' : ∑ i, w.val i = 0 := by
    have h1 : wt n w = 1 := hw
    have h2 : wt n w = Multiplicative.ofAdd (∑ i, w.val i) := rfl
    rw [h2] at h1
    exact ofAdd_eq_one.1 h1
  show wt n (permAct n g w) = 1
  simp only [wt, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [show (1 : Multiplicative (ZMod 2)) = Multiplicative.ofAdd 0 from rfl]
  congr 1
  rw [← hw']
  exact Equiv.sum_comp g.symm w.val

theorem permAct_eVec (n : ℕ) (g : Equiv.Perm (Fin n)) : permAct n g (eVec n) = eVec n := rfl

theorem isInv_Esub (n : ℕ) : IsInv (permAct n) (Esub n) := by
  intro g w hw
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  rw [map_zpow, permAct_eVec]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) k

inductive Mod
  | u : Mod
  | u0 : Mod
  | ut : Mod
  | ut0 : Mod
  deriving DecidableEq

@[expose] def Mod.W (n : ℕ) : Mod → Subgroup (U n)
  | .u => ⊤
  | .u0 => U0 n
  | .ut => ⊤
  | .ut0 => U0 n

@[expose] def Mod.N (n : ℕ) : Mod → Subgroup (U n)
  | .u => ⊥
  | .u0 => ⊥
  | .ut => Esub n
  | .ut0 => Esub n

theorem Mod.isInv_W (n : ℕ) (k : Mod) : IsInv (permAct n) (k.W n) := by
  cases k
  · exact isInv_top n
  · exact isInv_U0 n
  · exact isInv_top n
  · exact isInv_U0 n

theorem Mod.isInv_N (n : ℕ) (k : Mod) : IsInv (permAct n) (k.N n) := by
  cases k
  · exact isInv_bot n
  · exact isInv_bot n
  · exact isInv_Esub n
  · exact isInv_Esub n

abbrev Mod.V (n : ℕ) (k : Mod) : Type := Sec (k.W n) (k.N n)

@[expose] noncomputable def Mod.act (n : ℕ) (k : Mod) : Equiv.Perm (Fin n) →* MulAut (k.V n) :=
  secAct (permAct n) (k.isInv_W n) (k.isInv_N n)

end CFSG.Quasithin.B3
