module

public import CFSG.Monster.B.Rep4371.SpinAct
public import CFSG.Monster.B.Rep4371.FourEigen

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Rep4371

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.Griess Matrix

@[expose] def wvec : Fin 24 → ℚ := Pi.single 0 1 - Pi.single 1 1

@[expose] def unitVec (j : ℕ) : Fin 24 → ℚ := fun i => if (i : ℕ) = j then 1 else 0

theorem unitVec_eq_single {j : ℕ} (h : j < 24) : unitVec j = Pi.single ⟨j, h⟩ 1 := by
  funext i
  simp only [unitVec, Pi.single_apply, Fin.ext_iff]

theorem coe_toC_apply (a : ℕ) (i : Fin 24) :
    (toC a : Fin 24 → ZMod 2) i = boolZ ((Model.wordN a).testBit i) := by
  rw [coe_toC]
  rfl

@[expose] noncomputable def keyVec (κ : Model.Key) : SpaceB :=
  if κ.1 = 0 then inA (crossMat wvec (unitVec κ.2.1))
  else if κ.1 = 1 then inX (Xlift (pauliQ (false, κ.2.1, κ.2.2)))
  else inW (tensor (Evec (κ.2.1 != 0) κ.2.2) wvec)

theorem keyVec_zero (j x : ℕ) : keyVec (0, j, x) = inA (crossMat wvec (unitVec j)) := rfl

theorem keyVec_one (a d : ℕ) : keyVec (1, a, d) = inX (Xlift (pauliQ (false, a, d))) := rfl

theorem keyVec_two (t e c : ℕ) :
    keyVec (t + 2, e, c) = inW (tensor (Evec (e != 0) c) wvec) := rfl

theorem keyVec_A (j : ℕ) : keyVec (Model.Key.A j) = inA (crossMat wvec (unitVec j)) := rfl

theorem keyVec_X (a d : ℕ) : keyVec (Model.Key.X a d) = inX (Xlift (pauliQ (false, a, d))) := rfl

theorem keyVec_W (η : Bool) (c : ℕ) : keyVec (Model.Key.W η c) = inW (tensor (Evec η c) wvec) := by
  rw [Model.Key.W, keyVec_two 0]
  cases η <;> rfl

@[expose] def KeyValid (κ : Model.Key) : Prop := κ.1 = 0 → κ.2.1 < 24

@[expose] noncomputable def interp (D : ℚ) (v : List (Model.Key × ℤ)) : SpaceB :=
  (v.map fun e => ((e.2 : ℚ) / D) • keyVec e.1).sum

@[simp] theorem interp_nil (D : ℚ) : interp D [] = 0 := rfl

theorem interp_cons (D : ℚ) (e : Model.Key × ℤ) (v : List (Model.Key × ℤ)) :
    interp D (e :: v) = ((e.2 : ℚ) / D) • keyVec e.1 + interp D v := by
  rw [interp, List.map_cons, List.sum_cons]
  rfl

theorem interp_append (D : ℚ) (v w : List (Model.Key × ℤ)) :
    interp D (v ++ w) = interp D v + interp D w := by
  rw [interp, List.map_append, List.sum_append]
  rfl

theorem coeffOf_cons (κ : Model.Key) (e : Model.Key × ℤ) (v : List (Model.Key × ℤ)) :
    Model.coeffOf κ (e :: v) = (if e.1 = κ then e.2 else 0) + Model.coeffOf κ v := rfl

theorem coeffOf_eq_zero {κ : Model.Key} :
    ∀ {v : List (Model.Key × ℤ)}, κ ∉ v.map Prod.fst → Model.coeffOf κ v = 0
  | [], _ => rfl
  | e :: v, h => by
    rw [coeffOf_cons, coeffOf_eq_zero (fun h' => h (List.mem_cons_of_mem _ h'))]
    rw [List.map_cons, List.mem_cons, not_or] at h
    rw [ite_eq_right (fun h' => h.1 h'.symm), add_zero]

theorem interp_eq_sum (D : ℚ) (S : Finset Model.Key) :
    ∀ v : List (Model.Key × ℤ), (∀ e ∈ v, e.1 ∈ S) →
      interp D v = ∑ κ ∈ S, ((Model.coeffOf κ v : ℚ) / D) • keyVec κ
  | [], _ => by simp [Model.coeffOf]
  | e :: v, h => by
    rw [interp_cons, interp_eq_sum D S v fun f hf => h f (List.mem_cons_of_mem _ hf)]
    simp only [coeffOf_cons, Int.cast_add, add_div, add_smul, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_eq_single e.1]
    · rw [ite_eq_left rfl]
    · intro κ _ hκ
      rw [ite_eq_right (fun h' => hκ h'.symm), Int.cast_zero, zero_div, zero_smul]
    · intro hS
      exact absurd (h e List.mem_cons_self) hS

theorem eqModel_sound {D₁ D₂ : ℤ} (h₁ : D₁ ≠ 0) (h₂ : D₂ ≠ 0) {v₁ v₂ : List (Model.Key × ℤ)}
    (h : Model.eqModel D₁ v₁ D₂ v₂ = true) : interp D₁ v₁ = interp D₂ v₂ := by
  classical
  let S : Finset Model.Key := ((v₁ ++ v₂).map Prod.fst).toFinset
  have hS₁ : ∀ e ∈ v₁, e.1 ∈ S := fun e he =>
    List.mem_toFinset.2 (List.mem_map_of_mem (List.mem_append_left _ he))
  have hS₂ : ∀ e ∈ v₂, e.1 ∈ S := fun e he =>
    List.mem_toFinset.2 (List.mem_map_of_mem (List.mem_append_right _ he))
  rw [interp_eq_sum _ S v₁ hS₁, interp_eq_sum _ S v₂ hS₂]
  refine Finset.sum_congr rfl fun κ hκ => ?_
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hκ)
  have hc := List.all_eq_true.1 h e he
  rw [beq_iff_eq] at hc
  have hD₁ : (D₁ : ℚ) ≠ 0 := Int.cast_ne_zero.2 h₁
  have hD₂ : (D₂ : ℚ) ≠ 0 := Int.cast_ne_zero.2 h₂
  congr 1
  rw [div_eq_div_iff hD₁ hD₂]
  exact_mod_cast hc

theorem interp_map_mul (c : ℤ) (D : ℚ) :
    ∀ w : List (Model.Key × ℤ),
      interp (D * 64) (w.map fun f => (f.1, c * f.2)) = ((c : ℚ) / D) • interp 64 w
  | [] => by simp
  | f :: w => by
    rw [List.map_cons, interp_cons, interp_cons, interp_map_mul c D w, smul_add, smul_smul]
    congr 2
    rw [Int.cast_mul, mul_div_mul_comm]

theorem interp_actVec (g : Model.Key → List (Model.Key × ℤ)) (f : SpaceB →ₗ[ℚ] SpaceB) (D : ℚ) :
    ∀ v : List (Model.Key × ℤ), (∀ e ∈ v, f (keyVec e.1) = interp 64 (g e.1)) →
      f (interp D v) = interp (D * 64) (Model.actVec g v)
  | [], _ => by simp [Model.actVec]
  | e :: v, h => by
    have hcons : Model.actVec g (e :: v) =
        (g e.1).map (fun f => (f.1, e.2 * f.2)) ++ Model.actVec g v := rfl
    rw [hcons, interp_append, interp_map_mul, interp_cons, map_add, map_smul,
      h e List.mem_cons_self, interp_actVec g f D v fun f' hf => h f' (List.mem_cons_of_mem _ hf)]

end CFSG.Monster.B.Rep4371
