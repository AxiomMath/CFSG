module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Matrix.Mul

public section

namespace CFSG.Quasithin.H13.U43

section Coord

variable {C : Type} [CommGroup C]

@[expose] def evC (x : Fin 4 → C) (a : Fin 4 → ZMod 3) : C := ∏ i, x i ^ (a i).val

theorem pow_val_add {g : C} (hg : g ^ 3 = 1) (c d : ZMod 3) :
    g ^ (c + d).val = g ^ c.val * g ^ d.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hg, pow_add]

theorem evC_add {x : Fin 4 → C} (hx : ∀ i, x i ^ 3 = 1) (a b : Fin 4 → ZMod 3) :
    evC x (a + b) = evC x a * evC x b := by
  unfold evC
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => pow_val_add (hx i) _ _

theorem evC_zero (x : Fin 4 → C) : evC x 0 = 1 := by
  simp [evC]

theorem evC_neg {x : Fin 4 → C} (hx : ∀ i, x i ^ 3 = 1) (a : Fin 4 → ZMod 3) :
    evC x (-a) = (evC x a)⁻¹ := by
  have h := evC_add hx a (-a)
  have h0 : a + -a = 0 := add_neg_cancel a
  rw [h0, evC_zero] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

theorem evC_smul {x : Fin 4 → C} (hx : ∀ i, x i ^ 3 = 1) (c : ZMod 3) (a : Fin 4 → ZMod 3) :
    evC x (c • a) = (evC x a) ^ c.val := by
  unfold evC
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, ZMod.val_mul, ← pow_eq_pow_mod _ (hx i), pow_mul']

theorem evC_sum {x : Fin 4 → C} (hx : ∀ i, x i ^ 3 = 1) {ι : Type} (s : Finset ι)
    (f : ι → Fin 4 → ZMod 3) : evC x (∑ j ∈ s, f j) = ∏ j ∈ s, evC x (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [evC_zero]
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, evC_add hx, ih]

theorem evC_single {x : Fin 4 → C} (i : Fin 4) : evC x (Pi.single i 1) = x i := by
  unfold evC
  have h1 : (1 : ZMod 3).val = 1 := rfl
  rw [Finset.prod_eq_single i]
  · simp [h1]
  · intro j _ hj
    simp [hj]
  · simp

end Coord

section Rep

variable {C : Type} [CommGroup C] {x : Fin 4 → C}

theorem evC_surjective (hx : ∀ i, x i ^ 3 = 1) (hgen : Subgroup.closure (Set.range x) = ⊤) :
    Function.Surjective (evC x) := by
  let R : Subgroup C :=
    { carrier := Set.range (evC x)
      mul_mem' := by
        rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
        exact ⟨a + b, evC_add hx a b⟩
      one_mem' := ⟨0, evC_zero x⟩
      inv_mem' := by
        rintro _ ⟨a, rfl⟩
        exact ⟨-a, evC_neg hx a⟩ }
  have hle : Subgroup.closure (Set.range x) ≤ R := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨Pi.single i 1, evC_single i⟩
  intro g
  have hg : g ∈ R := hle (by rw [hgen]; exact Subgroup.mem_top g)
  exact hg

theorem card_vec : Nat.card (Fin 4 → ZMod 3) = 81 := by
  rw [Nat.card_eq_fintype_card]
  simp

theorem evC_bijective (hx : ∀ i, x i ^ 3 = 1) (hgen : Subgroup.closure (Set.range x) = ⊤)
    (hcard : Nat.card C = 81) : Function.Bijective (evC x) :=
  (evC_surjective hx hgen).bijective_of_nat_card_le (by rw [hcard, card_vec])

@[expose] def IsRep (x : Fin 4 → C) (φ : C →* C) (X : Matrix (Fin 4) (Fin 4) (ZMod 3)) : Prop :=
  ∀ a, φ (evC x a) = evC x (X.mulVec a)

theorem IsRep.one : IsRep x (MonoidHom.id C) 1 := fun a => by
  simp [Matrix.one_mulVec]

theorem IsRep.comp {φ ψ : C →* C} {X Y : Matrix (Fin 4) (Fin 4) (ZMod 3)} (h₁ : IsRep x φ X)
    (h₂ : IsRep x ψ Y) : IsRep x (φ.comp ψ) (X * Y) := fun a => by
  rw [MonoidHom.comp_apply, h₂ a, h₁ (Y.mulVec a), Matrix.mulVec_mulVec]

theorem IsRep.unique (hb : Function.Bijective (evC x)) {φ : C →* C}
    {X Y : Matrix (Fin 4) (Fin 4) (ZMod 3)} (h₁ : IsRep x φ X) (h₂ : IsRep x φ Y) : X = Y := by
  have hXY : ∀ a, X.mulVec a = Y.mulVec a := fun a => hb.1 ((h₁ a).symm.trans (h₂ a))
  ext i j
  have := congrFun (hXY (Pi.single j 1)) i
  simpa [Matrix.mulVec_single_one] using this

theorem isRep_of_cols (hx : ∀ i, x i ^ 3 = 1) (φ : C →* C) (X : Matrix (Fin 4) (Fin 4) (ZMod 3))
    (h : ∀ j, φ (x j) = evC x (fun i => X i j)) : IsRep x φ X := fun a => by
  have h1 : φ (evC x a) = ∏ j, evC x ((a j) • (fun i => X i j)) := by
    have hrw : evC x a = ∏ j, x j ^ (a j).val := rfl
    rw [hrw, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_pow, evC_smul hx, ← h j]
  have h2 : X.mulVec a = ∑ j, (a j) • (fun i => X i j) := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [h1, h2, evC_sum hx]

theorem exists_matrix (hx : ∀ i, x i ^ 3 = 1) (hb : Function.Bijective (evC x)) (φ : C →* C) :
    ∃ X, IsRep x φ X := by
  let e := Equiv.ofBijective _ hb
  refine ⟨Matrix.of fun i j => e.symm (φ (x j)) i, isRep_of_cols hx φ _ fun j => ?_⟩
  exact (e.apply_symm_apply (φ (x j))).symm

end Rep

end CFSG.Quasithin.H13.U43
