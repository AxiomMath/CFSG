module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallCardTwoNormalizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.AlternatingFourSylowThree
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThree
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# The top-normalizer case in the order-two branch

When `|K| = 2` and the normalizer of the involution centralizer is the whole
group, the normalizer calculation identifies the group with `A₄`.  Its odd
core is trivial, its Sylow `2`-subgroups are Klein four, and the exceptional
isomorphism `A₄ ≃ PSL₂(3)` realizes it as a `D`-group.
-/

namespace CFSG.GorensteinWalter

universe u

/-- The top-normalizer subcase of the `|K| = 2` branch is a `D`-group. -/
public theorem
    BrauerSuzukiWallHypotheses.isDGroup_of_card_K_eq_two_of_normalizer_eq_top
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G)
    (hk : Nat.card h.K = 2)
    (hN : Subgroup.normalizer (h.H : Set G) = ⊤) :
    IsDGroup G := by
  classical
  have eN :=
    h.normalizer_mulEquiv_alternatingGroup_four_of_card_K_eq_two hk
  rw [hN] at eN
  let eA4 : G ≃* alternatingGroup (Fin 4) :=
    Subgroup.topEquiv.symm.trans eN.some
  have hGcard : Nat.card G = 12 := by
    calc
      Nat.card G = Nat.card (alternatingGroup (Fin 4)) :=
        Nat.card_congr eA4.toEquiv
      _ = 12 := alternatingGroup.card_of_card_eq_four (by simp)
  have hcore : pPrimeCore 2 G = ⊥ := by
    let O : Subgroup G := pPrimeCore 2 G
    have hOdiv : Nat.card O ∣ 12 := by
      rw [← hGcard]
      exact O.card_subgroup_dvd_card
    have hOcop : Nat.Coprime 2 (Nat.card O) :=
      pPrimeCore_coprime_card (p := 2) (G := G)
    have hFourO : Nat.Coprime 4 (Nat.card O) := by
      simpa using hOcop.pow_left 2
    have hOdivThree : Nat.card O ∣ 3 := by
      apply hFourO.symm.dvd_of_dvd_mul_right
      norm_num at hOdiv ⊢
      exact hOdiv
    have hOcard : Nat.card O = 1 ∨ Nat.card O = 3 :=
      (Nat.dvd_prime Nat.prime_three).mp hOdivThree
    rcases hOcard with hOone | hOthree
    · exact (Subgroup.eq_bot_iff_card O).2 hOone
    · let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hfactor : 3 ^ (Nat.card G).factorization 3 = 3 := by
        rw [hGcard]
        rw [Nat.factorization_def _ Nat.prime_three]
        rw [show 12 = 4 * 3 by norm_num,
          padicValNat.mul (by norm_num) (by norm_num),
          padicValNat.eq_zero_of_not_dvd (by norm_num), padicValNat.self] <;>
          norm_num
      let Osyl : Sylow 3 G := Sylow.ofCard O (by
        rw [hOthree, hfactor])
      let : Unique (Sylow 3 G) :=
        Sylow.unique_of_normal Osyl (show O.Normal from pPrimeCore_normal)
      have hone : Nat.card (Sylow 3 G) = 1 := Nat.card_unique
      have hfour : Nat.card (Sylow 3 G) = 4 :=
        sylow_three_card_eq_four_of_mulEquiv_alternatingGroup_four ⟨eA4⟩
      omega
  have hSylow : HasDihedralSylowTwo G := by
    apply hasDihedralSylowTwo_of_mulEquiv eA4
    intro S
    refine ⟨1, by omega, ?_⟩
    rw [alternatingGroup.two_sylow_eq_kleinFour_of_card_eq_four (by simp) S]
    let : IsKleinFour (alternatingGroup.kleinFour (Fin 4)) :=
      alternatingGroup.kleinFour_isKleinFour (by simp)
    simpa using
      (IsKleinFour.nonempty_mulEquiv
        (G₁ := alternatingGroup.kleinFour (Fin 4))
        (G₂ := DihedralGroup 2))
  have ePSL : Nonempty (G ≃* PSL2 (ZMod 3)) :=
    ⟨eA4.trans psl2_three_equiv_alternatingGroup.symm⟩
  exact isDGroup_of_iso_PSL2_three hcore hSylow ePSL

end CFSG.GorensteinWalter
