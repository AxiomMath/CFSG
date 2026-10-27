module

public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4Chief
public import CFSG.LocalAnalysis.StandardType.GGReeFixedVectorDescent

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Ree

section Inputs

@[expose] def GGReeB2SimpleModuleFixedInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime] (m : ℕ),
    Nat.card K = 2 ^ (2 * m + 1) → ∀ (p : ℕ), p.Prime → ∀ w : Kˣ, orderOf w = p →
    ∀ e : reeFixed ReeTag.F4 K m,
      (e : adjointGroup ReeTag.F4.tag K) = F4Chief.reeB2Elt K m w →
    ∀ (W : Type) [AddCommGroup W] [Module (AlgebraicClosure (ZMod 2)) W]
      [Module.Finite (AlgebraicClosure (ZMod 2)) W]
      (ρ : Representation (AlgebraicClosure (ZMod 2)) (reeFixed ReeTag.F4 K m) W)
      [IsSimpleModule (MonoidAlgebra (AlgebraicClosure (ZMod 2)) (reeFixed ReeTag.F4 K m))
        ρ.asModule],
      ∃ v : W, v ≠ 0 ∧ ρ e v = v

theorem ggReeB2ModuleFixedInput_of_simple (h : GGReeB2SimpleModuleFixedInput) :
    GGReeB2ModuleFixedInput := by
  intro K _ _ _ m hK p hp w hw e he Q _ _ hQ2 hQ ρ hρ
  have hwp : w ^ p = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  have hb : (e : adjointGroup ReeTag.F4.tag K) ^ p = 1 := by
    rw [he]
    exact F4Chief.b2TorusElt_pow_eq_one hK hwp
  have hpodd : Odd p := by
    rw [← hw]
    exact F4Chief.odd_orderOf_units hK w
  have hodd : Odd (orderOf e) := by
    rw [← Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat hpodd (orderOf_dvd_of_pow_eq_one hb)
  exact fixed_vector_descent e hodd (h K m hK p hp w hw e he) Q hQ2 ρ hρ

end Inputs

end CFSG.StandardType
