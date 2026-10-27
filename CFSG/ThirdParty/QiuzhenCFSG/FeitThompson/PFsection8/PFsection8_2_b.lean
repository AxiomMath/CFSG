module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection8.PFsection8_2_a

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.Section8

universe v
universe w
universe u

@[expose] public def theorem_8_2_b_statement
    {G : Type u} [Group G] [Finite G]
    (M MF U U1 U0 : Subgroup G) : Prop :=
  typeFData M MF U U1 U0 →
    (section12FrobeniusJoinWithKernel MF U ↔
      ∀ p : Nat.Primes, ∀ P : Sylow p.val U, IsCyclic (P : Subgroup U))

/-- Peterfalvi `(8.2)(c)`. -/


public theorem theorem_8_2_b
    {G : Type u} [Group G] [Finite G]
    (M MF U U1 U0 : Subgroup G) :
    theorem_8_2_b_statement M MF U U1 U0 := by
  intro hF
  have h82a : Nat.card U0 = Monoid.exponent U :=
    theorem_8_2_a M MF U U1 U0 hF
  rcases hF with
    ⟨_hsolvM, hoddM, _hMF, _hMFne, _hMFM, _hUne, hcomp, _hU1leU, _hU1comm,
      _hU1norm, _hcent, hU0leU, _hexpU0U, hFrobU0⟩
  constructor
  · intro hFrobU p P
    have hU_odd : Odd (Nat.card U) :=
      odd_of_card_dvd hoddM (Subgroup.card_dvd_of_le hcomp.2.1)
    let S : Subgroup G := MF ⊔ U
    have hUsub_odd : Odd (Nat.card (U.subgroupOf S)) := by
      simpa [S, natCard_subgroupOf_eq U S le_sup_right] using hU_odd
    have hZUsub : IsZGroup (U.subgroupOf S) :=
      isZGroup_of_frobenius_complement_of_odd
        (K := MF.subgroupOf S) (R := U.subgroupOf S) hFrobU hUsub_odd
    have hZU : IsZGroup U := by
      let e : U.subgroupOf S ≃* U :=
        Subgroup.subgroupOfEquivOfLe (H := U) (K := S) le_sup_right
      exact IsZGroup.of_injective (f := e.symm.toMonoidHom) e.symm.injective
    exact (isZGroup_iff (G := U)).mp hZU p.val p.property P
  · intro hcyc
    have hZU : IsZGroup U := by
      rw [isZGroup_iff]
      intro p hp P
      exact hcyc ⟨p, hp⟩ P
    have hcardU : Nat.card U = Monoid.exponent U := by
      letI : IsZGroup U := hZU
      exact (IsZGroup.exponent_eq_card U).symm
    have hcardU0U : Nat.card U0 = Nat.card U :=
      h82a.trans hcardU.symm
    have hU0eqU : U0 = U :=
      Subgroup.eq_of_le_of_card_ge hU0leU (by rw [hcardU0U])
    simpa [hU0eqU] using hFrobU0

end CFSG.Section8
