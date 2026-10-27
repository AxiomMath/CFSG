module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG

open scoped commutatorElement

namespace FiveTransitive.CentralTwoTripleCommutation

private theorem commutator_eq_square
    {G : Type*} [Group G] (a x y : G) (ha : a ^ 2 = 1)
    (hx : x ^ 2 = a) (hy : y ^ 2 = a) : ⁅x, y⁆ = (x * y) ^ 2 := by
  have hix : x⁻¹ = x * a := inv_eq_of_mul_eq_one_right (by
    rw [← mul_assoc, ← pow_two, hx, ← pow_two, ha])
  have hiy : y⁻¹ = a * y := inv_eq_of_mul_eq_one_left (by
    rw [mul_assoc, ← pow_two, hy, ← pow_two, ha])
  rw [commutatorElement_def, hix, hiy]
  calc
    x * y * (x * a) * (a * y) = x * y * x * (a * a) * y := by group
    _ = (x * y) ^ 2 := by rw [← pow_two a, ha]; simp only [mul_one, pow_two, mul_assoc]

theorem commute_triple_fibre
    {G H : Type*} [Group G] [Group H] (f : G →* H) (B Q : Subgroup G)
    (hk : B ⊓ f.ker = Q)
    (hcentral : ∀ q : Q, ∀ g : G, Commute q.val g)
    (hQsq : ∀ q : Q, q.val ^ 2 = 1)
    (a x y z v : G) (ha : a ^ 2 = 1)
    (hx : x ∈ B) (hy : y ∈ B) (hz : z ∈ B) (hv : v ∈ B)
    (hxsq : x ^ 2 = a) (hysq : y ^ 2 = a) (hzsq : z ^ 2 = a)
    (hpair : (x * y) ^ 2 = (x * z) ^ 2)
    (hcomm : Commute (f x) (f y)) (hfv : f v = f (x * y * z)) : Commute x v := by
  have hcQ : ⁅x, y⁆ ∈ Q := by
    apply hk.le
    change ⁅x, y⁆ ∈ B ∧ ⁅x, y⁆ ∈ f.ker
    refine ⟨?_, ?_⟩
    · simpa only [commutatorElement_def] using B.mul_mem
        (B.mul_mem (B.mul_mem hx hy) (B.inv_mem hx)) (B.inv_mem hy)
    · rw [MonoidHom.mem_ker, map_commutatorElement, hcomm.commutator_eq]
  have he : ⁅x, y⁆ = ⁅x, z⁆ :=
    (commutator_eq_square a x y ha hxsq hysq).trans
      (hpair.trans (commutator_eq_square a x z ha hxsq hzsq).symm)
  have hcy : Commute ⁅x, y⁆ y := hcentral ⟨⁅x, y⁆, hcQ⟩ y
  have hc2 : ⁅x, y⁆ ^ 2 = 1 := hQsq ⟨⁅x, y⁆, hcQ⟩
  have hcyz : Commute x (y * z) := commutatorElement_eq_one_iff_commute.mp (by
    rw [commutatorElement_mul_right_eq_mul_conj, ← he, hcy.eq,
      mul_assoc y ⁅x, y⁆ ⁅x, y⁆, ← pow_two, hc2, mul_one, mul_inv_cancel])
  have hcprod : Commute x (x * y * z) := by
    rw [mul_assoc]
    exact (Commute.refl x).mul_right hcyz
  let q := (x * y * z) * v⁻¹
  have hqQ : q ∈ Q := hk.le ⟨B.mul_mem (B.mul_mem (B.mul_mem hx hy) hz) (B.inv_mem hv), by
    change f ((x * y * z) * v⁻¹) = 1
    rw [map_mul, map_inv, ← hfv, mul_inv_cancel]⟩
  have hqx : Commute x q := (hcentral ⟨q, hqQ⟩ x).symm
  have hvq : v = q⁻¹ * (x * y * z) := by dsimp [q]; group
  rw [hvq]
  exact hqx.inv_right.mul_right hcprod

end FiveTransitive.CentralTwoTripleCommutation

end CFSG
