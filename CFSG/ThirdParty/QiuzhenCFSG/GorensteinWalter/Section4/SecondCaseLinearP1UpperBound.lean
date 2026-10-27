module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationEightDefs
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The second equation-(8) conjugate-count bound
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The conjugates of `P` contained in the elementary-abelian plane `A`
form a subfamily of all order-`p` subgroups of `A`. -/
public theorem secondCase_linear_conjugateCount_le_p_add_one
    {G : Type u} [Group G] [Finite G]
    {P A : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hPcard : Nat.card P = p) (hAcard : Nat.card A = p ^ 2)
    (hAelem : IsElementaryAbelian p A) :
    conjugateCount P A ≤ p + 1 := by
  classical
  let : IsElementaryAbelian p A := hAelem
  let : Nontrivial A := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [hAcard]
    exact one_lt_pow₀ (Fact.out : Nat.Prime p).one_lt (by norm_num)
  have hexp : Monoid.exponent A = p :=
    IsElementaryAbelian.exponent_eq_prime
  let C : Type u := {X : Subgroup G // X ≤ A ∧ IsConjugateSubgroup P X}
  let S : Type u := {X : Subgroup A // Nat.card X = p}
  let f : C → S := fun X => ⟨X.1.subgroupOf A, by
    rcases X.2.2 with ⟨g, hg⟩
    calc
      Nat.card (X.1.subgroupOf A) = Nat.card X.1 :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe X.2.1).toEquiv
      _ = Nat.card (conjugateSubgroup P g) := by rw [hg]
      _ = Nat.card P := by
        exact Subgroup.card_map_of_injective
          (K := P) (f := (MulAut.conj g).toMonoidHom)
          (MulAut.conj g).injective
      _ = p := hPcard⟩
  have hf_inj : Function.Injective f := by
    intro X Y hXY
    have hsub : X.1.subgroupOf A = Y.1.subgroupOf A :=
      congrArg (fun z : S => z.1) hXY
    apply Subtype.ext
    apply Subgroup.ext
    intro x
    constructor
    · intro hx
      have hxX : (⟨x, X.2.1 hx⟩ : A) ∈ X.1.subgroupOf A :=
        Subgroup.mem_subgroupOf.mpr hx
      have hxY : (⟨x, X.2.1 hx⟩ : A) ∈ Y.1.subgroupOf A := by
        rw [← hsub]
        exact hxX
      exact Subgroup.mem_subgroupOf.mp hxY
    · intro hx
      have hxY : (⟨x, Y.2.1 hx⟩ : A) ∈ Y.1.subgroupOf A :=
        Subgroup.mem_subgroupOf.mpr hx
      have hxX : (⟨x, Y.2.1 hx⟩ : A) ∈ X.1.subgroupOf A := by
        rw [hsub]
        exact hxY
      exact Subgroup.mem_subgroupOf.mp hxX
  have hcard : Nat.card C ≤ Nat.card S :=
    Nat.card_le_card_of_injective f hf_inj
  have hS_card : Nat.card S = p + 1 :=
    order_p_subgroups_card_of_order_p_sq_exponent_p hAcard hexp
  rw [hS_card] at hcard
  exact hcard

end CFSG.GorensteinWalter
