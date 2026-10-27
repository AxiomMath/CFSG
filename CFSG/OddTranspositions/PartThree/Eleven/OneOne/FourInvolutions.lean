module


import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Group
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.OddTranspositions.PartThree

private def elt {G : Type*} [Group G] (v : Fin 4 → G) (i : Fin 4) (t : Bool) : G :=
  if t then v i else 1

private def nf {G : Type*} [Group G] (v : Fin 4 → G) (a : Fin 4 → Bool) : G :=
  elt v 0 (a 0) * elt v 1 (a 1) * elt v 2 (a 2) * elt v 3 (a 3)

private theorem v_mul_elt {G : Type*} [Group G] {v : Fin 4 → G}
    (hsq : ∀ i, v i * v i = 1) (i : Fin 4) (t : Bool) :
    v i * elt v i t = elt v i (!t) := by
  cases t <;> simp [elt, hsq]

private theorem commute_v_elt {G : Type*} [Group G] {v : Fin 4 → G}
    (hcomm : ∀ i j, Commute (v i) (v j)) (i j : Fin 4) (t : Bool) :
    Commute (v i) (elt v j t) := by
  cases t
  · simp [elt]
  · simpa [elt] using hcomm i j

private theorem mul_four_update {G : Type*} [Group G] (A : Fin 4 → G) (z : G) (i : Fin 4)
    (hA : ∀ j, j < i → Commute z (A j)) :
    z * (A 0 * A 1 * A 2 * A 3) =
      Function.update A i (z * A i) 0 * Function.update A i (z * A i) 1 *
        Function.update A i (z * A i) 2 * Function.update A i (z * A i) 3 := by
  fin_cases i
  · simp only [Function.update_apply]; simp
    group
  · simp only [Function.update_apply]; simp
    have h0 : Commute z (A 0) := hA 0 (by decide)
    calc z * (A 0 * A 1 * A 2 * A 3)
        = z * A 0 * A 1 * A 2 * A 3 := by group
      _ = A 0 * (z * A 1) * A 2 * A 3 := by rw [h0.eq]; group
  · simp only [Function.update_apply]; simp
    have h0 : Commute z (A 0) := hA 0 (by decide)
    have h1 : Commute z (A 1) := hA 1 (by decide)
    have h01 : Commute z (A 0 * A 1) := h0.mul_right h1
    calc z * (A 0 * A 1 * A 2 * A 3)
        = (z * (A 0 * A 1)) * (A 2 * A 3) := by group
      _ = ((A 0 * A 1) * z) * (A 2 * A 3) := by rw [h01.eq]
      _ = A 0 * A 1 * (z * A 2) * A 3 := by group
  · simp only [Function.update_apply]; simp
    have h0 : Commute z (A 0) := hA 0 (by decide)
    have h1 : Commute z (A 1) := hA 1 (by decide)
    have h2 : Commute z (A 2) := hA 2 (by decide)
    have h012 : Commute z (A 0 * A 1 * A 2) := (h0.mul_right h1).mul_right h2
    calc z * (A 0 * A 1 * A 2 * A 3)
        = (z * (A 0 * A 1 * A 2)) * A 3 := by group
      _ = ((A 0 * A 1 * A 2) * z) * A 3 := by rw [h012.eq]
      _ = A 0 * A 1 * A 2 * (z * A 3) := by group

private theorem v_mul_nf {G : Type*} [Group G] {v : Fin 4 → G}
    (hcomm : ∀ i j, Commute (v i) (v j)) (hsq : ∀ i, v i * v i = 1)
    (i : Fin 4) (a : Fin 4 → Bool) :
    v i * nf v a = nf v (Function.update a i (!a i)) := by
  let A : Fin 4 → G := fun j => elt v j (a j)
  let A' : Fin 4 → G := fun j => elt v j ((Function.update a i (!a i)) j)
  have hfun : A' = Function.update A i (v i * A i) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp only [A', A, Function.update_self]
      exact (v_mul_elt hsq j (a j)).symm
    · simp only [A', A, Function.update_of_ne hj]
  have h := mul_four_update A (v i) i (fun j _ => commute_v_elt hcomm i j (a j))
  change v i * (A 0 * A 1 * A 2 * A 3) = A' 0 * A' 1 * A' 2 * A' 3
  rw [h, hfun]

private theorem elt_mul_nf {G : Type*} [Group G] {v : Fin 4 → G}
    (hcomm : ∀ i j, Commute (v i) (v j)) (hsq : ∀ i, v i * v i = 1)
    (i : Fin 4) (t : Bool) (b : Fin 4 → Bool) :
    elt v i t * nf v b = nf v (Function.update b i (xor t (b i))) := by
  cases t
  · simp [elt, Function.update_eq_self]
  · simpa [elt] using v_mul_nf hcomm hsq i b

private theorem nf_assoc {G : Type*} [Group G] {v : Fin 4 → G}
    (a : Fin 4 → Bool) (X : G) :
    nf v a * X = elt v 0 (a 0) * (elt v 1 (a 1) * (elt v 2 (a 2) * (elt v 3 (a 3) * X))) := by
  rw [nf]; group

private theorem nf_mul_nf {G : Type*} [Group G] {v : Fin 4 → G}
    (hcomm : ∀ i j, Commute (v i) (v j)) (hsq : ∀ i, v i * v i = 1)
    (a b : Fin 4 → Bool) :
    nf v a * nf v b = nf v (fun i => xor (a i) (b i)) := by
  rw [nf_assoc]
  rw [elt_mul_nf hcomm hsq]
  rw [elt_mul_nf hcomm hsq]
  rw [elt_mul_nf hcomm hsq]
  rw [elt_mul_nf hcomm hsq]
  congr 1
  funext i
  fin_cases i <;> simp [Function.update_apply]

private theorem nf_mem {G : Type*} [Group G] {v : Fin 4 → G} (a : Fin 4 → Bool) :
    nf v a ∈ Subgroup.closure (Set.range v) := by
  have helt : ∀ (i : Fin 4) (t : Bool), elt v i t ∈ Subgroup.closure (Set.range v) := by
    intro i t
    cases t
    · simp [elt]
    · simp only [elt, if_true]
      exact Subgroup.subset_closure ⟨i, rfl⟩
  rw [nf]
  apply Subgroup.mul_mem
  · apply Subgroup.mul_mem
    · apply Subgroup.mul_mem
      · exact helt 0 (a 0)
      · exact helt 1 (a 1)
    · exact helt 2 (a 2)
  · exact helt 3 (a 3)

private theorem nf_surj {G : Type*} [Group G] {v : Fin 4 → G}
    (hcomm : ∀ i j, Commute (v i) (v j)) (hsq : ∀ i, v i * v i = 1) :
    ∀ q ∈ Subgroup.closure (Set.range v), ∃ a : Fin 4 → Bool, nf v a = q := by
  intro q hq
  refine Subgroup.closure_induction_left (p := fun y _ => ∃ a : Fin 4 → Bool, nf v a = y)
    ?_ ?_ ?_ hq
  · exact ⟨fun _ => false, by simp [nf, elt]⟩
  · intro x hx y hy ih
    rcases hx with ⟨i, rfl⟩
    rcases ih with ⟨a, ha⟩
    refine ⟨Function.update a i (!a i), ?_⟩
    rw [← ha]
    exact (v_mul_nf hcomm hsq i a).symm
  · intro x hx y hy ih
    rcases hx with ⟨i, rfl⟩
    rw [inv_eq_of_mul_eq_one_right (hsq i)]
    rcases ih with ⟨a, ha⟩
    refine ⟨Function.update a i (!a i), ?_⟩
    rw [← ha]
    exact (v_mul_nf hcomm hsq i a).symm

private theorem nf_injective {G : Type*} [Group G] {v : Fin 4 → G}
    (hcomm : ∀ i j, Commute (v i) (v j)) (hsq : ∀ i, v i * v i = 1)
    (hcard : Nat.card (Subgroup.closure (Set.range v)) = 16) :
    ∀ a b : Fin 4 → Bool, nf v a = nf v b → a = b := by
  have hsurj : Function.Surjective (fun a : Fin 4 → Bool =>
      (⟨nf v a, nf_mem a⟩ : Subgroup.closure (Set.range v))) := by
    intro q
    rcases q with ⟨q, hq⟩
    rcases nf_surj hcomm hsq q hq with ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩
  have hbij := hsurj.bijective_of_nat_card_le (by simp [hcard])
  intro a b hab
  exact hbij.1 (Subtype.ext hab)

private theorem conj_four {G : Type*} [Group G] (z A0 A1 A2 A3 : G) :
    z * (A0 * A1 * A2 * A3) * z⁻¹ =
      (z * A0 * z⁻¹) * (z * A1 * z⁻¹) * (z * A2 * z⁻¹) * (z * A3 * z⁻¹) := by
  group

private theorem conj_inv {G : Type*} [Group G] {a b z : G} (h : z * a * z⁻¹ = b) :
    z⁻¹ * b * z = a := by rw [← h]; group

private theorem conj_elt {G : Type*} [Group G] {v c : Fin 4 → G} {z : G}
    (hc : ∀ i, z * v i * z⁻¹ = c i) (i : Fin 4) (t : Bool) :
    z * elt v i t * z⁻¹ = elt c i t := by
  cases t
  · simpa [elt] using conj_one z
  · simpa [elt] using hc i

private theorem conj_nf {G : Type*} [Group G] {v c : Fin 4 → G} {z : G} (a : Fin 4 → Bool)
    (hc : ∀ i, z * v i * z⁻¹ = c i) :
    z * nf v a * z⁻¹ = nf c a := by
  rw [nf, nf, conj_four]
  simp only [conj_elt hc]

private theorem nf_x {G : Type*} [Group G] {v : Fin 4 → G}
    (hcomm : ∀ i j, Commute (v i) (v j)) (a : Fin 4 → Bool) :
    nf (fun i => ![v 1, v 0, v 2, v 3] i) a = nf v (fun i => ![a 1, a 0, a 2, a 3] i) := by
  simp only [nf, elt]
  cases a 0 <;> cases a 1 <;> cases a 2 <;> cases a 3 <;> simp
  all_goals first | group | rw [(hcomm 0 1).eq.symm]
  all_goals group

private theorem nf_y {G : Type*} [Group G] {v : Fin 4 → G}
    (hcomm : ∀ i j, Commute (v i) (v j)) (hsq : ∀ i, v i * v i = 1) (a : Fin 4 → Bool) :
    nf (fun i => ![v 0, v 1, v 3, v 0 * v 1 * v 2 * v 3] i) a =
      nf v (fun i => ![xor (a 0) (a 3), xor (a 1) (a 3), a 3, xor (a 2) (a 3)] i) := by
  have h1 : nf (fun i => ![v 0, v 1, v 3, v 0 * v 1 * v 2 * v 3] i) a =
      nf v (fun i => ![a 0, a 1, false, a 2] i) *
        (if a 3 then v 0 * v 1 * v 2 * v 3 else 1) := by
    simp only [nf, elt]
    cases a 0 <;> cases a 1 <;> cases a 2 <;> cases a 3 <;> simp
    all_goals group
  have h2 : nf v (fun i => ![a 0, a 1, false, a 2] i) *
        (if a 3 then v 0 * v 1 * v 2 * v 3 else 1) =
      nf v (fun i => ![xor (a 0) (a 3), xor (a 1) (a 3), a 3, xor (a 2) (a 3)] i) := by
    cases a 3
    · simp only [Bool.false_eq_true, if_false, one_mul, mul_one]
      have hfun : (fun i => ![xor (a 0) false, xor (a 1) false, false, xor (a 2) false] i) =
          (fun i => ![a 0, a 1, false, a 2] i) := by
        funext i
        fin_cases i <;> simp
      rw [hfun]
    · simp only [if_true]
      have hu : v 0 * v 1 * v 2 * v 3 = nf v (fun _ : Fin 4 => true) := by simp [nf, elt]
      rw [hu, nf_mul_nf hcomm hsq]
      have hfun : (fun i => xor ((fun i => ![a 0, a 1, false, a 2] i) i) true) =
          (fun i => ![a 0 ^^ true, a 1 ^^ true, true, a 2 ^^ true] i) := by
        funext i
        fin_cases i <;> simp
      rw [hfun]
  exact h1.trans h2

theorem mul_self_eq_one_or_of_four_involutions {G : Type*} [Group G] {v : Fin 4 → G}
    (hcomm : ∀ i j, Commute (v i) (v j)) (hsq : ∀ i, v i * v i = 1)
    (hcard : Nat.card (Subgroup.closure (Set.range v)) = 16) {x y : G}
    (hx0 : x * v 0 * x⁻¹ = v 1) (hx1 : x * v 1 * x⁻¹ = v 0) (hx2 : x * v 2 * x⁻¹ = v 2)
    (hx3 : x * v 3 * x⁻¹ = v 3) (hy0 : y * v 0 * y⁻¹ = v 0) (hy1 : y * v 1 * y⁻¹ = v 1)
    (hy2 : y * v 2 * y⁻¹ = v 3) (hy3 : y * v 3 * y⁻¹ = v 0 * v 1 * v 2 * v 3)
    (hq : x * x ∈ Subgroup.closure (Set.range v))
    (hb : x⁻¹ * (y * x * y⁻¹) ∈ Subgroup.closure (Set.range v)) :
    x * x = 1 ∨ x * x = v 0 * v 1 := by
  obtain ⟨a, ha⟩ := nf_surj hcomm hsq (x * x) hq
  obtain ⟨c, hc⟩ := nf_surj hcomm hsq (x⁻¹ * (y * x * y⁻¹)) hb
  have hxq : x * nf v a * x⁻¹ = nf v a := by rw [ha]; group
  have hcx : ∀ i, x * v i * x⁻¹ = ![v 1, v 0, v 2, v 3] i := by
    intro i; fin_cases i <;> simp [hx0, hx1, hx2, hx3]
  have hE1 : nf v (fun i => ![a 1, a 0, a 2, a 3] i) = nf v a := by
    rw [← nf_x hcomm a]
    rw [← conj_nf (v := v) (c := fun i => ![v 1, v 0, v 2, v 3] i) (z := x) a hcx]
    exact hxq
  have ha10 : a 1 = a 0 := by
    simpa using congrFun (nf_injective hcomm hsq hcard _ _ hE1) 0
  have ha01 : a 0 = a 1 := ha10.symm
  have hcy : ∀ i, y * v i * y⁻¹ = ![v 0, v 1, v 3, v 0 * v 1 * v 2 * v 3] i := by
    intro i; fin_cases i <;> simp [hy0, hy1, hy2, hy3]
  have hcyq : y * nf v a * y⁻¹ =
      nf v (fun i => ![xor (a 0) (a 3), xor (a 1) (a 3), a 3, xor (a 2) (a 3)] i) := by
    rw [← nf_y hcomm hsq a]
    exact conj_nf a hcy
  have hxinv : ∀ i, x⁻¹ * v i * x = ![v 1, v 0, v 2, v 3] i := by
    intro i
    fin_cases i <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_succ]
    · exact conj_inv hx1
    · exact conj_inv hx0
    · exact conj_inv hx2
    · exact conj_inv hx3
  have hxinv_nf : x⁻¹ * nf v c * x = nf v (fun i => ![c 1, c 0, c 2, c 3] i) := by
    have h := conj_nf (v := v) (c := fun i => ![v 1, v 0, v 2, v 3] i) (z := x⁻¹) c
      (fun i => by simpa using hxinv i)
    rw [inv_inv] at h
    rw [nf_x hcomm c] at h
    exact h
  have hE2a : y * nf v a * y⁻¹ = nf v a * (x⁻¹ * nf v c * x) * nf v c := by
    rw [ha, hc]; group
  have hE2b : nf v a * (x⁻¹ * nf v c * x) * nf v c =
      nf v (fun i => xor (xor (a i) (![c 1, c 0, c 2, c 3] i)) (c i)) := by
    rw [hxinv_nf, nf_mul_nf hcomm hsq, nf_mul_nf hcomm hsq]
  have hE2 : nf v (fun i => ![xor (a 0) (a 3), xor (a 1) (a 3), a 3, xor (a 2) (a 3)] i) =
      nf v (fun i => xor (xor (a i) (![c 1, c 0, c 2, c 3] i)) (c i)) := by
    rw [← hcyq, hE2a, hE2b]
  have hE2fun := nf_injective hcomm hsq hcard _ _ hE2
  have h3 : xor (a 2) (a 3) = a 3 := by simpa using congrFun hE2fun 3
  have h2 : a 3 = a 2 := by simpa using congrFun hE2fun 2
  have ha2 : a 2 = false := by
    rw [h2] at h3
    have h3' : (false : Bool) = a 2 := by simpa using h3
    exact h3'.symm
  have ha3 : a 3 = false := by rw [ha2] at h2; exact h2
  have ha1 : a 1 = a 0 := ha01.symm
  have hcases : a = ![false, false, false, false] ∨ a = ![true, true, false, false] := by
    cases h0 : a 0
    · left
      funext i; fin_cases i <;> simp [h0, ha1, ha2, ha3]
    · right
      funext i; fin_cases i <;> simp [h0, ha1, ha2, ha3]
  rcases hcases with h | h
  · left
    rw [← ha, h]; simp [nf, elt]
  · right
    rw [← ha, h]; simp [nf, elt]

end CFSG.OddTranspositions.PartThree
