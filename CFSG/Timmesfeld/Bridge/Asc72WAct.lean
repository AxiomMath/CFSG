module

public import CFSG.Timmesfeld.Bridge.Asc72Defs

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open Equiv SemidirectProduct

namespace WreathAct

variable {L : Type*} [Group L] {n : ℕ}

theorem permAct_apply' (σ : Perm (Fin n)) (x : Fin n → L) (i : Fin n) :
    permAct (Fin n) L σ x i = x (σ⁻¹ i) := rfl

theorem permAct_mulSingle (σ : Perm (Fin n)) (k : Fin n) (y : L) :
    permAct (Fin n) L σ (Pi.mulSingle k y) = Pi.mulSingle (σ k) y := by
  funext l
  rw [permAct_apply']
  by_cases hl : l = σ k
  · subst hl
    simp
  · rw [Pi.mulSingle_eq_of_ne hl, Pi.mulSingle_eq_of_ne]
    intro h
    exact hl (by rw [← h]; simp)

theorem conj_mulSingle (h : Fin n → L) (k : Fin n) (y : L) :
    h * Pi.mulSingle k y * h⁻¹ = Pi.mulSingle k (h k * y * (h k)⁻¹) := by
  funext l
  by_cases hl : l = k
  · subst hl
    simp
  · simp [Pi.mulSingle_eq_of_ne hl]

@[expose] def act (L : Type*) [Group L] (n : ℕ) :
    ((Fin n → L) ⋊[permAct (Fin n) L] Perm (Fin n)) →* MulAut (Fin n → L) :=
  SemidirectProduct.lift MulAut.conj (permAct (Fin n) L) fun σ => by
    ext h x
    simp [MulAut.conj_apply, MulAut.mul_apply]

theorem act_apply (w : (Fin n → L) ⋊[permAct (Fin n) L] Perm (Fin n)) (x : Fin n → L) :
    act L n w x = w.left * permAct (Fin n) L w.right x * w.left⁻¹ := rfl

theorem act_mulSingle (w : (Fin n → L) ⋊[permAct (Fin n) L] Perm (Fin n)) (k : Fin n) (y : L) :
    act L n w (Pi.mulSingle k y) =
      Pi.mulSingle (w.right k) (w.left (w.right k) * y * (w.left (w.right k))⁻¹) := by
  rw [act_apply, permAct_mulSingle, conj_mulSingle]

theorem act_injective [Nontrivial L] (hZ : ∀ z : L, (∀ y, z * y = y * z) → z = 1) :
    Function.Injective (act L n) := by
  refine (injective_iff_map_eq_one _).mpr fun w hw => ?_
  have hfix : ∀ x, act L n w x = x := fun x => by rw [hw]; rfl
  obtain ⟨y, hy⟩ := exists_ne (1 : L)
  have hr : w.right = 1 := by
    refine Equiv.ext fun k => ?_
    rw [Perm.one_apply]
    by_contra hk
    have h := congrFun (hfix (Pi.mulSingle k y)) (w.right k)
    rw [act_mulSingle, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hk, conj_eq_one_iff] at h
    exact hy h
  have hl : w.left = 1 := by
    funext k
    refine hZ _ fun z => ?_
    have h := congrFun (hfix (Pi.mulSingle k z)) k
    rw [act_mulSingle, hr, Perm.one_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_same] at h
    calc w.left k * z = w.left k * z * (w.left k)⁻¹ * w.left k := by group
      _ = z * w.left k := by rw [h]
  exact SemidirectProduct.ext hl hr

theorem finite_wreath [Finite L] : Finite ((Fin n → L) ⋊[permAct (Fin n) L] Perm (Fin n)) :=
  Finite.of_equiv _ SemidirectProduct.equivProd.symm

theorem card_wreath :
    Nat.card ((Fin n → L) ⋊[permAct (Fin n) L] Perm (Fin n)) = Nat.card L ^ n * n.factorial := by
  rw [SemidirectProduct.card, Nat.card_fun, Nat.card_perm, Nat.card_fin]

end WreathAct

end CFSG.Timmesfeld.Bridge.Asc72
