module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65Invariant
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBarConj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eight65_false_of_invariant_centralizer
    {L X Z X0 : Subgroup G} {t : G}
    (hcomm : ∀ x ∈ X, ∀ z ∈ Z, x * z = z * x)
    (hZ3 : ∀ z ∈ Z, z ^ 3 = 1)
    (hXcard : Nat.card X = 3) (hZcard : Nat.card Z = 3)
    (hXneZ : X ≠ Z)
    (hX : ∀ x ∈ X, t * x * t⁻¹ = x)
    (hZinv : ∀ z ∈ Z, t * z * t⁻¹ = z⁻¹)
    (hX0le : X0 ≤ X ⊔ Z) (hX0card : Nat.card X0 = 3) (hX0ne : X0 ≠ Z)
    (hX0inv : ∀ w ∈ X0, t * w * t⁻¹ ∈ X0)
    (hX0eq : X0 = centralizerBar (X ⊔ Z) L)
    (hnot : ¬ ⁅L, X⁆ ≤ CFSG.Open.pCoreOf 2 L) :
    False := by
  classical
  have hX0 : X0 = X := by
    rcases eq_left_or_right_of_invariant_order_three hcomm hZ3 hXcard hZcard hXneZ hX hZinv
      hX0le hX0card hX0inv with h | h
    · exact h
    · exact absurd h hX0ne
  have hXle : X ≤ centralizerBar (X ⊔ Z) L := by
    rw [← hX0eq, hX0]
  have hmem : ∀ x ∈ X, ∀ y ∈ L, ⁅y, x⁆ ∈ CFSG.Open.pCoreOf 2 L := by
    intro x hx y hy
    have hx' : x ∈ centralizerBar (X ⊔ Z) L := hXle hx
    have h1 : ⁅x, y⁆ ∈ CFSG.Open.pCoreOf 2 L := hx'.2 y hy
    have h2 : ⁅y, x⁆ = ⁅x, y⁆⁻¹ := (commutatorElement_inv x y).symm
    rw [h2]
    exact (CFSG.Open.pCoreOf 2 L).inv_mem h1
  exact hnot (Subgroup.commutator_le.mpr fun y hy x hx => hmem x hx y hy)

theorem map_conj_eq_of_centralizes {X : Subgroup G} {t : G}
    (hX : ∀ x ∈ X, t * x * t⁻¹ = x) :
    X.map (MulAut.conj t).toMonoidHom = X := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change MulAut.conj t x ∈ X
    rw [MulAut.conj_apply, hX x hx]
    exact hx
  · intro hy
    refine ⟨y, hy, ?_⟩
    change MulAut.conj t y = y
    rw [MulAut.conj_apply, hX y hy]

theorem map_conj_eq_of_inverts {Z : Subgroup G} {t : G}
    (hZ : ∀ z ∈ Z, t * z * t⁻¹ = z⁻¹) :
    Z.map (MulAut.conj t).toMonoidHom = Z := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    change MulAut.conj t z ∈ Z
    rw [MulAut.conj_apply, hZ z hz]
    exact Z.inv_mem hz
  · intro hy
    refine ⟨y⁻¹, Z.inv_mem hy, ?_⟩
    change MulAut.conj t y⁻¹ = y
    rw [MulAut.conj_apply, hZ y⁻¹ (Z.inv_mem hy), inv_inv]

theorem eight65_false_of_inverting_element
    {L X Z X0 : Subgroup G} {t : G}
    (hcomm : ∀ x ∈ X, ∀ z ∈ Z, x * z = z * x)
    (hZ3 : ∀ z ∈ Z, z ^ 3 = 1)
    (hXcard : Nat.card X = 3) (hZcard : Nat.card Z = 3)
    (hXneZ : X ≠ Z)
    (hX : ∀ x ∈ X, t * x * t⁻¹ = x)
    (hZinv : ∀ z ∈ Z, t * z * t⁻¹ = z⁻¹)
    (hX0card : Nat.card X0 = 3) (hX0ne : X0 ≠ Z)
    (hX0eq : X0 = centralizerBar (X ⊔ Z) L)
    (htL : L.map (MulAut.conj t).toMonoidHom = L)
    (hnot : ¬ ⁅L, X⁆ ≤ CFSG.Open.pCoreOf 2 L) :
    False := by
  have hE : (X ⊔ Z).map (MulAut.conj t).toMonoidHom = X ⊔ Z := by
    rw [Subgroup.map_sup, map_conj_eq_of_centralizes hX, map_conj_eq_of_inverts hZinv]
  have hX0le : X0 ≤ X ⊔ Z := by
    rw [hX0eq]; exact centralizerBar_le (X ⊔ Z) L
  have hX0inv : ∀ w ∈ X0, t * w * t⁻¹ ∈ X0 := by
    intro w hw
    rw [hX0eq] at hw ⊢
    exact conj_mem_centralizerBar t (X ⊔ Z) L hE htL hw
  exact eight65_false_of_invariant_centralizer hcomm hZ3 hXcard hZcard hXneZ hX hZinv
    hX0le hX0card hX0ne hX0inv hX0eq hnot

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
