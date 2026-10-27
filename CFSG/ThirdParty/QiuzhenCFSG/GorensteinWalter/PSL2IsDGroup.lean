module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearULift

import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.example_1_3
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow

namespace CFSG
end CFSG
open CFSG

/-!
# Odd projective special linear groups are D-groups

This module packages the model-side endpoint needed after a recognition
theorem identifies an ambient finite group with `PSL₂(K)`.
-/

namespace CFSG.GorensteinWalter

universe u

noncomputable section

/-- A finite group isomorphic to `PSL₂(K)`, where `K` is a finite field of
odd prime-power order greater than three, is a D-group.  The coefficient
field is universe zero so that concrete fields such as `ZMod 7` and
`GaloisField 3 2` can model an ambient group in any universe. -/
public theorem isDGroup_of_mulEquiv_psl2_odd
    {G : Type u} [Group G] [Finite G]
    (K : Type) [Field K] [Finite K]
    (hKprimePower : IsOddPrimePower (Nat.card K))
    (hKlarge : 3 < Nat.card K)
    (e : Nonempty (G ≃* PSL2 K)) :
    IsDGroup G := by
  rcases e with ⟨e⟩
  have hDihedral : HasDihedralSylowTwo G :=
    hasDihedralSylowTwo_of_mulEquiv e
      (psl2_odd_hasDihedralSylowTwo_model K hKprimePower)
  have hSylow : HasCyclicOrDihedralSylowTwo G := by
    intro S
    exact Or.inr (hDihedral S)
  rcases BenderSuzuki.External.huppert_blackburn_XI_example_1_3_a K with
    ⟨_hprojectiveCard, _rho, _iota, _hrho, _hiota, _hiotaApply,
      _hrhoApply, _hiotaNormal, _hiotaIndex, _hsharp, hlarge,
      _hsmallTwo, _hsmallThree⟩
  have hsimplePSL : IsSimpleGroup (PSL2 K) := (hlarge hKlarge).1
  letI : IsSimpleGroup (PSL2 K) := hsimplePSL
  letI : IsSimpleGroup G := e.isSimpleGroup
  have hEven : 2 ∣ Nat.card G := by
    let S : Sylow 2 G := Classical.choice Sylow.nonempty
    obtain ⟨m, _hm, ⟨eS⟩⟩ := hDihedral S
    have hcardS : Nat.card (S : Subgroup G) = 2 * 2 ^ m := by
      calc
        Nat.card (S : Subgroup G) = Nat.card (DihedralGroup (2 ^ m)) :=
          Nat.card_congr eS.toEquiv
        _ = 2 * 2 ^ m := DihedralGroup.nat_card
    rw [← (S : Subgroup G).card_mul_index, hcardS]
    exact (dvd_mul_right 2 (2 ^ m)).mul_right (S : Subgroup G).index
  have hcore : pPrimeCore 2 G = ⊥ :=
    pPrimeCore_eq_bot_of_simple_of_even hEven
  refine IsDGroup.quotientHasLinearNormalSubgroup hSylow
    (ULift.{u} K) ?_ ⊤ inferInstance (by simp) ?_
  · simpa using hKprimePower
  · left
    refine ⟨Subgroup.topEquiv.trans ?_⟩
    exact ((QuotientGroup.quotientMulEquivOfEq (G := G) hcore).trans
      (QuotientGroup.quotientBot (G := G))).trans
        (e.trans (psl2ULiftEquiv (R := K)).symm)

end

end CFSG.GorensteinWalter
