module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.RankThree.PartOne.Census3.Interface

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.RankThree.PartOne
open scoped commutatorElement

section Coprime

variable {X : Type*} [Group X] {p : ℕ} [Fact p.Prime]

theorem exists_fixed_mem_coset {F : Subgroup (MulAut X)} (hF : IsPGroup p F) {Z : Subgroup X}
    (hZp : ¬ p ∣ Nat.card Z) (hZF : ∀ φ ∈ F, ∀ z ∈ Z, φ z ∈ Z) {x : X}
    (hx : ∀ φ ∈ F, x⁻¹ * φ x ∈ Z) : ∃ z ∈ Z, ∀ φ ∈ F, φ (x * z) = x * z := by
  classical
  let S : SubMulAction F X :=
    { carrier := {y | x⁻¹ * y ∈ Z}
      smul_mem' := fun φ y hy => by
        have hφ : (φ : MulAut X) ∈ F := φ.2
        have h1 : x⁻¹ * (φ : MulAut X) y = (x⁻¹ * (φ : MulAut X) x) * (φ : MulAut X) (x⁻¹ * y) := by
          rw [map_mul, map_inv]
          group
        show x⁻¹ * (φ : MulAut X) y ∈ Z
        rw [h1]
        exact Z.mul_mem (hx _ hφ) (hZF _ hφ _ hy) }
  have hcard : Nat.card ↥S = Nat.card Z := by
    refine Nat.card_congr
      { toFun := fun y => ⟨x⁻¹ * y.1, y.2⟩
        invFun := fun z => ⟨x * z.1, by
          show x⁻¹ * (x * z.1) ∈ Z
          rw [inv_mul_cancel_left]
          exact z.2⟩
        left_inv := fun y => Subtype.ext (by simp)
        right_inv := fun z => Subtype.ext (by simp) }
  obtain ⟨y, hy⟩ := hF.nonempty_fixed_point_of_prime_not_dvd_card ↥S (by rwa [hcard])
  refine ⟨x⁻¹ * y.1, y.2, fun φ hφ => ?_⟩
  have h1 : (⟨φ, hφ⟩ : F) • y = y := hy ⟨φ, hφ⟩
  have h2 := congrArg Subtype.val h1
  have h3 : φ y.1 = y.1 := h2
  rw [mul_inv_cancel_left]
  exact h3

end Coprime

end CFSG.RankThree.PartOne.CTP
