module

public import CFSG.LieType.Chevalley.TorusCoordinates

public section

namespace CFSG.RankThree.PartOne

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section TorusWords

variable {τ : Tag} {K : Type} [Field K]

theorem list_prod_torusElt_conj_pinnedX {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (c : K) :
    ∀ l : List (Fin τ.rank × Kˣ),
      (l.map fun p => torusElt τ K p.1 p.2).prod * pinnedX τ K α c *
          ((l.map fun p => torusElt τ K p.1 p.2).prod)⁻¹ =
        pinnedX τ K α
          ((((l.map fun p => p.2 ^ (∑ k, τ.cartan p.1 k * α k)).prod : Kˣ) : K) * c)
  | [] => by simp
  | p :: l => by
    have ih := list_prod_torusElt_conj_pinnedX hα c l
    simp only [List.map_cons, List.prod_cons, Units.val_mul]
    calc torusElt τ K p.1 p.2 * (l.map fun p => torusElt τ K p.1 p.2).prod * pinnedX τ K α c *
          (torusElt τ K p.1 p.2 * (l.map fun p => torusElt τ K p.1 p.2).prod)⁻¹
        = torusElt τ K p.1 p.2 * ((l.map fun p => torusElt τ K p.1 p.2).prod * pinnedX τ K α c *
            ((l.map fun p => torusElt τ K p.1 p.2).prod)⁻¹) * (torusElt τ K p.1 p.2)⁻¹ := by
          group
      _ = _ := by
          rw [ih, root_torus_conjugation p.1 hα p.2]
          congr 1
          ring

variable (τ K) in
@[expose] noncomputable def torusWord (S : Finset (Fin τ.rank)) : ModGL τ K :=
  ((torusCoordHom τ K (fun j => if j ∈ S then (-1 : Kˣ) else 1) : torusGroup τ K) : ModGL τ K)

theorem torusWord_eq_list_prod (S : Finset (Fin τ.rank)) :
    torusWord τ K S =
      (List.ofFn fun i => torusElt τ K i (if i ∈ S then (-1 : Kˣ) else 1)).prod := rfl

theorem neg_one_zpow_mul_eq (n : ℤ) (c : K) :
    ((((-1 : Kˣ) ^ n : Kˣ) : K) * c) = if n % 2 = 0 then c else -c := by
  split_ifs with hn
  · rw [(Int.even_iff.2 hn).neg_one_zpow, Units.val_one, one_mul]
  · rw [(Int.odd_iff.2 (by omega)).neg_one_zpow, Units.val_neg, Units.val_one, neg_one_mul]

theorem torusWord_conj_pinnedX (S : Finset (Fin τ.rank)) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α)
    (c : K) :
    torusWord τ K S * pinnedX τ K α c * (torusWord τ K S)⁻¹ =
      pinnedX τ K α (if (∑ j ∈ S, ∑ k, τ.cartan j k * α k) % 2 = 0 then c else -c) := by
  classical
  set t : Fin τ.rank → Kˣ := fun j => if j ∈ S then (-1 : Kˣ) else 1 with ht
  have h := list_prod_torusElt_conj_pinnedX hα c (List.ofFn fun i => (i, t i))
  have e1 : ((List.ofFn fun i => (i, t i)).map fun p => torusElt τ K p.1 p.2) =
      List.ofFn fun i => torusElt τ K i (t i) := by
    rw [List.map_ofFn]
    rfl
  have e2 : ((List.ofFn fun i => (i, t i)).map
      fun p => p.2 ^ (∑ k, τ.cartan p.1 k * α k)) =
      List.ofFn fun i => t i ^ (∑ k, τ.cartan i k * α k) := by
    rw [List.map_ofFn]
    rfl
  rw [e1, e2, List.prod_ofFn] at h
  have hprod : ∏ i, t i ^ (∑ k, τ.cartan i k * α k) =
      (-1 : Kˣ) ^ (∑ j ∈ S, ∑ k, τ.cartan j k * α k) := by
    have h1 : ∀ i, t i ^ (∑ k, τ.cartan i k * α k) =
        if i ∈ S then (-1 : Kˣ) ^ (∑ k, τ.cartan i k * α k) else 1 := by
      intro i
      simp only [ht]
      split_ifs <;> simp
    simp only [h1]
    rw [Finset.prod_ite_mem Finset.univ S (fun i => (-1 : Kˣ) ^ (∑ k, τ.cartan i k * α k)),
      Finset.univ_inter]
    exact prod_zpow_eq_zpow_sum S _ (-1)
  rw [hprod, neg_one_zpow_mul_eq] at h
  rw [torusWord_eq_list_prod]
  exact h

theorem torusWord_sq (S : Finset (Fin τ.rank)) : torusWord τ K S ^ 2 = 1 := by
  have h : (fun j => if j ∈ S then (-1 : Kˣ) else 1) ^ 2 = 1 := by
    funext j
    simp only [Pi.pow_apply, Pi.one_apply]
    split_ifs <;> simp
  unfold torusWord
  rw [← Subgroup.coe_pow, ← map_pow, h, map_one, Subgroup.coe_one]

theorem torusWord_mem_adjointGroup (S : Finset (Fin τ.rank)) :
    torusWord τ K S ∈ adjointGroup τ K := by
  rw [torusWord_eq_list_prod]
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  exact torusElt_mem_adjointGroup i _

theorem torusWord_commute_pinnedX_of_even (S : Finset (Fin τ.rank)) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (c : K) (h : (∑ j ∈ S, ∑ k, τ.cartan j k * α k) % 2 = 0) :
    Commute (torusWord τ K S) (pinnedX τ K α c) := by
  have := torusWord_conj_pinnedX S hα c
  rw [ite_eq_left h] at this
  exact mul_inv_eq_iff_eq_mul.1 this

theorem torusWord_conj_pinnedX_of_odd (S : Finset (Fin τ.rank)) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (c : K) (h : (∑ j ∈ S, ∑ k, τ.cartan j k * α k) % 2 = 1) :
    torusWord τ K S * pinnedX τ K α c * (torusWord τ K S)⁻¹ = (pinnedX τ K α c)⁻¹ := by
  rw [torusWord_conj_pinnedX S hα c, ite_eq_right (by omega), pinnedX_neg]

theorem torusWord_ne_one_of_odd (S : Finset (Fin τ.rank)) {α : Fin τ.rank → ℤ}
    (hα : IsRoot τ α) (h : (∑ j ∈ S, ∑ k, τ.cartan j k * α k) % 2 = 1) (h2 : (2 : K) ≠ 0) :
    torusWord τ K S ≠ 1 := by
  intro h1
  have := torusWord_conj_pinnedX_of_odd S hα (1 : K) h
  rw [h1, one_mul, inv_one, mul_one, pinnedX_neg] at this
  have h3 := pinnedX_injective τ K α this
  exact h2 (by linear_combination h3)

end TorusWords

end CFSG.RankThree.PartOne
