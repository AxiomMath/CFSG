module

public import CFSG.LieType.Universal.SymplecticExtras.Matrices
public import CFSG.Blueprint.Chevalley
public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import CFSG.LieType.Universal.SymplecticExtras
public import CFSG.Timmesfeld.ARS.Defs

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.Blueprint.Chevalley
open TauCeti.GLSymplecticFin

theorem NSLFrameData.comm_of_cartan_ne {K : Type*} [Group K] {D : UniversalRootDatum K}
    (h : D.cartan ≠ Symplectic.cartanC D.rank) :
    D.cartan = Symplectic.cartanC D.rank → ∀ i j, D.cartan i j = -2 →
      Commuting (D.rootGroup (Pi.single i 1)) (D.rootGroup (Pi.single i 1 + Pi.single j 1)) :=
  fun e => absurd e h

section Symplectic

open Symplectic Symplectic.SpExtras Matrix

variable {n : ℕ} {F : Type} [Field F]

theorem spE_difference_mul_positiveSum [CharP F 2] {i j : Fin n} (hne : i ≠ j) (hlt : i < j) :
    E F (.difference i j hne) * E F (.positiveSum i j hlt) =
      E F (.positiveSum i j hlt) * E F (.difference i j hne) := by
  simp only [E, sub_mul, add_mul, mul_sub, mul_add, single_mul_single_same, mul_one,
    single_mul_single_of_ne, ne_eq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, hne,
    Ne.symm hne, not_false_eq_true, sub_zero, zero_sub, add_zero, zero_add]
  rw [eq_neg_iff_add_eq_zero, ← single_add, one_add_one_eq_two, CharTwo.two_eq_zero, single_zero]

theorem commute_spElt_difference_positiveSum [CharP F 2] {i j : Fin n} (hne : i ≠ j)
    (hlt : i < j) (a b : F) :
    Commute (elt (.difference i j hne) a) (elt (.positiveSum i j hlt) b) := by
  show _ * _ = _ * _
  apply mat_injective
  rw [map_mul, map_mul, mat_elt, mat_elt]
  simp only [add_mul, mul_add, one_mul, mul_one, smul_mul_smul_comm,
    spE_difference_mul_positiveSum hne hlt, mul_comm a b]
  abel

theorem NSLFrameData.comm_symplecticDatum [CharP F 2] :
    (Symplectic.rootDatum n F).cartan = cartanC (Symplectic.rootDatum n F).rank →
      ∀ i j, (Symplectic.rootDatum n F).cartan i j = -2 →
        Commuting ((Symplectic.rootDatum n F).rootGroup (Pi.single i 1))
          ((Symplectic.rootDatum n F).rootGroup (Pi.single i 1 + Pi.single j 1)) := by
  intro _
  show ∀ i j : Fin n, cartanC n i j = -2 →
    Commuting (Symplectic.rootGroup n F (Pi.single i 1))
      (Symplectic.rootGroup n F (Pi.single i 1 + Pi.single j 1))
  intro i j hij
  simp only [cartanC, Matrix.of_apply] at hij
  have hi : i.val + 2 = n ∧ j.val + 1 = n := by
    split_ifs at hij <;> omega
  have hne : i ≠ j := Fin.ne_of_val_ne (by omega)
  have hlt : i < j := Fin.lt_def.2 (by omega)
  have hi1 : i.val + 1 < n := by omega
  have hj : (⟨i.val + 1, hi1⟩ : Fin n) = j := Fin.ext (show i.val + 1 = j.val by omega)
  have hj1 : ¬ j.val + 1 < n := by omega
  have hr : stdVec (.difference i j hne) = toStd n (Pi.single i 1) := by
    rw [toStd_single_of_lt' hi1, hj]
    rfl
  have hr' : stdVec (.positiveSum i j hlt) = toStd n (Pi.single i 1 + Pi.single j 1) := by
    rw [toStd_add', toStd_single_of_lt' hi1, toStd_single_of_not_lt' hj1, hj]
    change Pi.single i 1 + Pi.single j 1 = _
    abel
  intro x hx y hy
  obtain ⟨a, rfl⟩ := (mem_rootGroup_iff hr).1 hx
  obtain ⟨b, rfl⟩ := (mem_rootGroup_iff hr').1 hy
  exact commute_spElt_difference_positiveSum hne hlt a b

end Symplectic

theorem cartanB_ne_cartanC {m : ℕ} (hm : 2 ≤ m) : Spin.cartanB m ≠ Symplectic.cartanC m := by
  intro h
  have e := congrFun (congrFun h ⟨m - 1, by omega⟩) ⟨m - 2, by omega⟩
  simp only [Spin.cartanB, Symplectic.cartanC, Matrix.of_apply, Fin.mk.injEq] at e
  split_ifs at e <;> omega

theorem NSLFrameData.comm_minusDatum {n : ℕ} (hn : 3 ≤ n) {K : Type*} [Field K] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (Spin.Twisted.minusDatum n hirr).cartan =
        Symplectic.cartanC (Spin.Twisted.minusDatum n hirr).rank →
      ∀ i j, (Spin.Twisted.minusDatum n hirr).cartan i j = -2 →
        Commuting ((Spin.Twisted.minusDatum n hirr).rootGroup (Pi.single i 1))
          ((Spin.Twisted.minusDatum n hirr).rootGroup (Pi.single i 1 + Pi.single j 1)) :=
  NSLFrameData.comm_of_cartan_ne (cartanB_ne_cartanC (m := n - 1) (by omega))

theorem cartan_G2_ne_cartanC : Tag.cartan .G2 ≠ Symplectic.cartanC (Tag.rank .G2) := by
  decide

theorem cartan_F4_ne_cartanC : Tag.cartan .F4 ≠ Symplectic.cartanC (Tag.rank .F4) := by
  decide

end CFSG.Timmesfeld.ARS
