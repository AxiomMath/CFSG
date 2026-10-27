module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.Basic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.Section8

universe v
universe w
universe u

@[expose] public def theorem_8_2_a_statement
    {G : Type u} [Group G] [Finite G]
    (M MF U U1 U0 : Subgroup G) : Prop :=
  typeFData M MF U U1 U0 →
    Nat.card U0 = Monoid.exponent U

/-- Peterfalvi `(8.2)(b)`. -/


public theorem theorem_8_2_a
    {G : Type u} [Group G] [Finite G]
    (M MF U U1 U0 : Subgroup G) :
    theorem_8_2_a_statement M MF U U1 U0 := by
  intro hF
  rcases hF with
    ⟨_hsolvM, hoddM, _hMF, _hMFne, _hMFM, _hUne, hcomp, _hU1leU, _hU1comm,
      _hU1norm, _hcent, hU0leU, hexpU0U, hFrob⟩
  have hU0leM : U0 ≤ M := hU0leU.trans hcomp.2.1
  have hU0_odd : Odd (Nat.card U0) := odd_of_card_dvd hoddM (Subgroup.card_dvd_of_le hU0leM)
  let S : Subgroup G := MF ⊔ U0
  have hU0sub_odd : Odd (Nat.card (U0.subgroupOf S)) := by
    simpa [S, natCard_subgroupOf_eq U0 S le_sup_right] using hU0_odd
  have hZ : IsZGroup (U0.subgroupOf S) :=
    isZGroup_of_frobenius_complement_of_odd
      (K := MF.subgroupOf S) (R := U0.subgroupOf S) hFrob hU0sub_odd
  have hcard : Nat.card U0 = Monoid.exponent U0 := by
    calc
      Nat.card U0 = Nat.card (U0.subgroupOf S) := by
        symm
        exact natCard_subgroupOf_eq U0 S le_sup_right
      _ = Monoid.exponent (U0.subgroupOf S) := by
        letI : IsZGroup (U0.subgroupOf S) := hZ
        exact (IsZGroup.exponent_eq_card (U0.subgroupOf S)).symm
      _ = Monoid.exponent U0 := by
        exact Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe le_sup_right)
  exact hcard.trans hexpU0U

end CFSG.Section8
