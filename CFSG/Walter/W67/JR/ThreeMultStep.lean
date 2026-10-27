module

public import CFSG.Walter.W67.JR.ThreeMultAlg
public import CFSG.Walter.W67.JR.ThreeMultLayers
public import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.Walter.W67

namespace ThreeMult

open scoped commutatorElement

section Add

variable {A B C : Type*} [CommGroup A] [CommGroup B] [CommGroup C]

@[expose] def addPair (f : A →* (B →* C)) : Additive A →+ (Additive B →+ Additive C) where
  toFun x := (f (Additive.toMul x)).toAdditive
  map_zero' := by
    ext y
    simp
  map_add' x y := by
    ext z
    simp [MonoidHom.mul_apply]

theorem addPair_apply (f : A →* (B →* C)) (x : Additive A) (y : Additive B) :
    addPair f x y = Additive.ofMul (f (Additive.toMul x) (Additive.toMul y)) := rfl

end Add

section ML

variable {V M : Type*} [AddCommGroup V] [Module (ZMod 3) V] [AddCommGroup M] [Module (ZMod 3) M]

theorem map_smul_of_add {f : V →+ M} (c : ZMod 3) (x : V) : f (c • x) = c • f x := by
  have h1 : c • x = c.val • x := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
  have h2 : c • f x = c.val • f x := by
    rw [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]
  rw [h1, h2, map_nsmul]

@[expose] def ml2 (f : V →+ V →+ M) : MultilinearMap (ZMod 3) (fun _ : Fin 2 => V) M where
  toFun m := f (m 0) (m 1)
  map_update_add' := by
    intro inst m i x y
    obtain rfl : inst = instDecidableEqFin _ := Subsingleton.elim _ _
    fin_cases i <;> simp [Function.update, AddMonoidHom.add_apply]
  map_update_smul' := by
    intro inst m i c x
    obtain rfl : inst = instDecidableEqFin _ := Subsingleton.elim _ _
    fin_cases i <;> simp [Function.update]
    · rw [map_smul_of_add c x]
      rfl
    · exact map_smul_of_add c x

@[expose] def ml3 (f : V →+ V →+ V →+ M) : MultilinearMap (ZMod 3) (fun _ : Fin 3 => V) M where
  toFun m := f (m 0) (m 1) (m 2)
  map_update_add' := by
    intro inst m i x y
    obtain rfl : inst = instDecidableEqFin _ := Subsingleton.elim _ _
    fin_cases i <;> simp [Function.update, AddMonoidHom.add_apply]
  map_update_smul' := by
    intro inst m i c x
    obtain rfl : inst = instDecidableEqFin _ := Subsingleton.elim _ _
    fin_cases i <;> simp [Function.update]
    · rw [map_smul_of_add c x]
      rfl
    · rw [map_smul_of_add (f := f (m 0)) c x]
      rfl
    · exact map_smul_of_add c x

@[expose] def ml4 (f : V →+ V →+ V →+ V →+ M) :
    MultilinearMap (ZMod 3) (fun _ : Fin 4 => V) M where
  toFun m := f (m 0) (m 1) (m 2) (m 3)
  map_update_add' := by
    intro inst m i x y
    obtain rfl : inst = instDecidableEqFin _ := Subsingleton.elim _ _
    fin_cases i <;> simp [Function.update, AddMonoidHom.add_apply]
  map_update_smul' := by
    intro inst m i c x
    obtain rfl : inst = instDecidableEqFin _ := Subsingleton.elim _ _
    fin_cases i <;> simp [Function.update]
    · rw [map_smul_of_add c x]
      rfl
    · rw [map_smul_of_add (f := f (m 0)) c x]
      rfl
    · rw [map_smul_of_add (f := f (m 0) (m 1)) c x]
      rfl
    · exact map_smul_of_add c x

end ML

section Step

variable {E : Type*} [Group E] (P : Subgroup E)

theorem end_sum_apply {M : Type*} [AddCommMonoid M] (s : Finset ℕ) (f : ℕ → AddMonoid.End M)
    (m : M) : (∑ j ∈ s, f j) m = ∑ j ∈ s, f j m := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

@[expose] noncomputable def addConj (g : E) (hg : g ∈ Subgroup.normalizer (P : Set E)) (i : ℕ) :
    Additive (LayerQ P i) →+ Additive (LayerQ P i) :=
  (layerConj g hg i).toAdditive

theorem addConj_iterate (g : E) (hg : g ∈ Subgroup.normalizer (P : Set E)) (i j : ℕ)
    (m : Additive (LayerQ P i)) :
    (addConj P g hg i)^[j] m = Additive.ofMul ((layerConj g hg i)^[j] (Additive.toMul m)) := by
  induction j generalizing m with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply, ih, Function.iterate_succ_apply]
    rfl

theorem eq_one_of_fixed {n i k : ℕ} [Module (ZMod 3) (Additive (LayerQ P 0))]
    [Fintype (Additive (LayerQ P 0))] [Module (ZMod 3) (Additive (LayerQ P i))]
    (hV : Fintype.card (Additive (LayerQ P 0)) = 3 ^ n)
    {g : E} (hg : g ∈ Subgroup.normalizer (P : Set E))
    (hT : ∀ v : LayerQ P 0, (layerConj g hg 0)^[3 ^ n - 1] v = v)
    (hfree : ∀ j, 0 < j → j < 3 ^ n - 1 → ∀ v, (layerConj g hg 0)^[j] v = v → v = 1)
    (hk1 : 1 ≤ k) (hk : k < 2 * n)
    (c : MultilinearMap (ZMod 3) (fun _ : Fin k => Additive (LayerQ P 0)) (Additive (LayerQ P i)))
    (hc : ∀ x, c (fun j => addConj P g hg 0 (x j)) = addConj P g hg i (c x))
    (hθ : ∀ m : LayerQ P i, (layerConj g hg i)^[3 ^ n - 1] m = m)
    (hgen : Subgroup.closure (Set.range fun x => Additive.toMul (c x)) = ⊤)
    (z : LayerQ P i) (hz : layerConj g hg i z = z) : z = 1 := by
  have hn : 1 ≤ n := by omega
  have hq3 : 3 ≤ 3 ^ n := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  set q := 3 ^ n with hq
  let T : Additive (LayerQ P 0) →ₗ[ZMod 3] Additive (LayerQ P 0) :=
    (addConj P g hg 0).toZModLinearMap 3
  have hTpow : ∀ (j : ℕ) (v : Additive (LayerQ P 0)), (T ^ j) v = (addConj P g hg 0)^[j] v := by
    intro j v
    rw [Module.End.coe_pow]
    rfl
  have hT1 : T ^ (q - 1) = 1 := by
    ext v
    rw [hTpow, addConj_iterate, hT, Module.End.one_apply]
    rfl
  have hfreeT : ∀ j, 0 < j → j < q - 1 → ∀ v, (T ^ j) v = v → v = 0 := by
    intro j hj0 hjq v hv
    rw [hTpow, addConj_iterate] at hv
    have hv' : (layerConj g hg 0)^[j] (Additive.toMul v) = Additive.toMul v := by
      have := congrArg Additive.toMul hv
      exact this
    have := hfree j hj0 hjq _ hv'
    exact congrArg Additive.ofMul this
  let θ : AddMonoid.End (Additive (LayerQ P i)) := addConj P g hg i
  let N : AddMonoid.End (Additive (LayerQ P i)) := ∑ j ∈ Finset.range (q - 1), θ ^ j
  have hθq : θ ^ (q - 1) = 1 := by
    ext m
    change (addConj P g hg i)^[q - 1] m = m
    rw [addConj_iterate, hθ]
    rfl
  have hNθ : N * θ = N := by
    have h1 : N * θ = ∑ j ∈ Finset.range (q - 1), θ ^ (j + 1) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun j _ => (pow_succ θ j).symm
    rw [h1]
    change ∑ j ∈ Finset.range (q - 1), θ ^ (j + 1) = ∑ j ∈ Finset.range (q - 1), θ ^ j
    have hq1 : q - 1 = (q - 2) + 1 := by omega
    rw [hq1, Finset.sum_range_succ, Finset.sum_range_succ' (fun j => θ ^ j), ← hq1, hθq,
      pow_zero]
  let Nl : Additive (LayerQ P i) →ₗ[ZMod 3] Additive (LayerQ P i) :=
    (N : Additive (LayerQ P i) →+ Additive (LayerQ P i)).toZModLinearMap 3
  let Φ := Nl.compMultilinearMap c
  have hΦ : ∀ x, Φ (fun j => T (x j)) = Φ x := by
    intro x
    change N (c (fun j => addConj P g hg 0 (x j))) = N (c x)
    rw [hc]
    change (N * θ) (c x) = N (c x)
    rw [hNθ]
  have hΦ0 := eq_zero_of_free_invariant hV T hT1 hfreeT hk1 hk Φ hΦ
  let S : Subgroup (LayerQ P i) :=
    { carrier := {m | N (Additive.ofMul m) = 0}
      one_mem' := by
        change N (Additive.ofMul 1) = 0
        rw [ofMul_one, map_zero]
      mul_mem' := by
        intro a b ha hb
        change N (Additive.ofMul (a * b)) = 0
        rw [ofMul_mul, map_add, ha, hb, add_zero]
      inv_mem' := by
        intro a ha
        change N (Additive.ofMul a⁻¹) = 0
        rw [ofMul_inv, map_neg]
        change -(N (Additive.ofMul a)) = 0
        rw [ha, neg_zero] }
  have hS : Subgroup.closure (Set.range fun x => Additive.toMul (c x)) ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    exact hΦ0 x
  rw [hgen] at hS
  have hzS : N (Additive.ofMul z) = 0 := hS (Subgroup.mem_top z)
  have hNz : N (Additive.ofMul z) = (q - 1) • Additive.ofMul z := by
    change (∑ j ∈ Finset.range (q - 1), θ ^ j) (Additive.ofMul z) = _
    rw [end_sum_apply]
    have hfix : ∀ j : ℕ, (θ ^ j) (Additive.ofMul z) = Additive.ofMul z := by
      intro j
      rw [AddMonoid.End.coe_pow]
      change (addConj P g hg i)^[j] (Additive.ofMul z) = _
      rw [addConj_iterate]
      congr 1
      exact Function.IsFixedPt.iterate hz j
    rw [Finset.sum_congr rfl fun j _ => hfix j, Finset.sum_const, Finset.card_range]
  rw [hNz] at hzS
  have := eq_zero_of_nsmul_eq_zero hn hzS
  exact congrArg Additive.toMul this

theorem addConj_addPair (g : E) (hg : g ∈ Subgroup.normalizer (P : Set E)) (i : ℕ)
    (u : Additive (LayerQ P i)) (y : Additive (LayerQ P 0)) :
    addConj P g hg (i + 1) (addPair (pair P i) u y) =
      addPair (pair P i) (addConj P g hg i u) (addConj P g hg 0 y) :=
  congrArg Additive.ofMul (layerConj_pair g hg i (Additive.toMul u) (Additive.toMul y))

theorem closure_pair_of_closure {i : ℕ} (S : Set (LayerQ P i)) (hS : Subgroup.closure S = ⊤) :
    Subgroup.closure ((fun uy : LayerQ P i × LayerQ P 0 => pair P i uy.1 uy.2) ''
      (S ×ˢ Set.univ)) = ⊤ := by
  set H := Subgroup.closure ((fun uy : LayerQ P i × LayerQ P 0 => pair P i uy.1 uy.2) ''
      (S ×ˢ Set.univ))
  let K : Subgroup (LayerQ P i) :=
    { carrier := {u | ∀ y, pair P i u y ∈ H}
      one_mem' := fun y => by rw [map_one, MonoidHom.one_apply]; exact H.one_mem
      mul_mem' := fun {a b} ha hb y => by
        rw [map_mul, MonoidHom.mul_apply]; exact H.mul_mem (ha y) (hb y)
      inv_mem' := fun {a} ha y => by
        rw [map_inv, MonoidHom.inv_apply]; exact H.inv_mem (ha y) }
  have hSK : S ⊆ K := fun u hu y => Subgroup.subset_closure ⟨(u, y), ⟨hu, Set.mem_univ _⟩, rfl⟩
  have hK : K = ⊤ := by
    rw [eq_top_iff, ← hS, Subgroup.closure_le]
    exact hSK
  rw [eq_top_iff, ← closure_range_pair P i, Subgroup.closure_le]
  rintro _ ⟨⟨u, y⟩, rfl⟩
  have : u ∈ K := hK ▸ Subgroup.mem_top u
  exact this y

end Step

end ThreeMult

end CFSG.Walter.W67
