module

public import CFSG.Sporadic.Th.Max3.AllConj
public import Certificates.Certificate24390

public section

namespace CFSG.Sporadic.Recognition.ThMultiplier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3
open CFSG.Sporadic.Th.Max3.AllConj

@[expose] noncomputable def vGen (j : Fin 5) : J :=
  nfN (vS j) (vE j)

theorem isRows_vGen (j : Fin 5) :
    IsRows (rowsV j) (vGen j) :=
  isRows_nfN _ _

@[expose] noncomputable def iotaN (c : Fin 5 → ℕ) : J :=
  (List.ofFn fun j => vGen j ^ c j).prod

private theorem forall₂_ofFn_aux {α β : Type*} (R : α → β → Prop) :
    ∀ {n : ℕ} (f : Fin n → α) (g : Fin n → β), (∀ i, R (f i) (g i)) →
      List.Forall₂ R (List.ofFn f) (List.ofFn g)
  | 0, _, _, _ => by simp
  | n + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ]
    exact List.Forall₂.cons (h 0) (forall₂_ofFn_aux R _ _ fun i => h i.succ)

theorem isRows_iotaN
    (c : Fin 5 → ℕ) : IsRows (rowsIota c) (iotaN c) :=
  IsRows.prod (forall₂_ofFn_aux _ _ _ fun j => (isRows_vGen j).pow (c j))

private theorem facts :
    (∀ j : Fin 5, eqRows (mulRows (rowsV j) (rowsV j)) idRows = true) ∧
    (∀ i j : Fin 5, eqRows (mulRows (rowsV i) (rowsV j)) (mulRows (rowsV j) (rowsV i)) = true) ∧
    (∀ c : Fin 5 → ZMod 2, c ≠ 0 → eqRows (rowsIota fun j => (c j).val) idRows = false) ∧
    (∀ j : Fin 5, eqRows (mulRows rowsA1 (rowsV j)) (mulRows (rowsIota (colA1 j)) rowsA1) = true) ∧
    (∀ j : Fin 5, eqRows (mulRows rowsA2 (rowsV j)) (mulRows (rowsIota (colA2 j)) rowsA2) = true) ∧
    (∀ j : Fin 5, eqRows (mulRows rowsA3 (rowsV j)) (mulRows (rowsIota (colA3 j)) rowsA3) = true) :=
  Certificates.certificate24390

theorem vGen_mul_self
    (j : Fin 5) : vGen j * vGen j = 1 :=
  ((isRows_vGen j).mul (isRows_vGen j)).eq_of_eqRows IsRows.one (facts.1 j)

theorem vGen_comm
    (i j : Fin 5) : vGen i * vGen j = vGen j * vGen i :=
  ((isRows_vGen i).mul (isRows_vGen j)).eq_of_eqRows ((isRows_vGen j).mul (isRows_vGen i))
    (facts.2.1 i j)

theorem iotaN_ne_one
    {c : Fin 5 → ZMod 2} (hc : c ≠ 0) :
    iotaN (fun j => (c j).val) ≠ 1 :=
  (isRows_iotaN _).ne_of_eqRows IsRows.one (facts.2.2.1 c hc)

theorem vGen_zero : vGen 0 = z := by
  simp [vGen, nfN, vS, vE]

@[expose] noncomputable def A1 : J := y ^ 5 * x

@[expose] noncomputable def A2 : J := y * x * y ^ 5

@[expose] noncomputable def gElt : J := abProd gWord

@[expose] noncomputable def A3 : J :=
  gElt * (a * (gElt⁻¹ * q 0 * gElt)) ^ 9 * y ^ 4

theorem isRows_A1 :
    IsRows rowsA1 A1 :=
  (isRows_y.pow 5).mul isRows_x

theorem isRows_A2 :
    IsRows rowsA2 A2 :=
  (isRows_y.mul isRows_x).mul (isRows_y.pow 5)

theorem isRows_A3 :
    IsRows rowsA3 A3 :=
  ((isRows_abProd gWord).mul
    (isRows_a.mul (((isRows_abProd_inv gWord).mul (isRows_q 0)).mul (isRows_abProd gWord))
      |>.pow 9)).mul (isRows_y.pow 4)

theorem A1_vGen
    (j : Fin 5) : A1 * vGen j = iotaN (colA1 j) * A1 :=
  (isRows_A1.mul (isRows_vGen j)).eq_of_eqRows ((isRows_iotaN _).mul isRows_A1)
    (facts.2.2.2.1 j)

theorem A2_vGen
    (j : Fin 5) : A2 * vGen j = iotaN (colA2 j) * A2 :=
  (isRows_A2.mul (isRows_vGen j)).eq_of_eqRows ((isRows_iotaN _).mul isRows_A2)
    (facts.2.2.2.2.1 j)

theorem A3_vGen
    (j : Fin 5) : A3 * vGen j = iotaN (colA3 j) * A3 :=
  (isRows_A3.mul (isRows_vGen j)).eq_of_eqRows ((isRows_iotaN _).mul isRows_A3)
    (facts.2.2.2.2.2 j)

end CFSG.Sporadic.Recognition.ThMultiplier
