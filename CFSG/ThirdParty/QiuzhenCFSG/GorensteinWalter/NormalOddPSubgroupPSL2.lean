module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupAlternatingFour
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearRingEquiv
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow
import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Normal odd-prime subgroups of odd `PSL₂`

An odd-prime-power `PSL₂` has no nontrivial normal subgroup of odd
prime-power order.  The field of order three is handled through
`PSL₂(3) ≃ A₄`; larger fields use simplicity.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A normal odd-prime subgroup of `PSL₂(K)`, for `K` of odd prime-power
order, is trivial. -/
public theorem normal_pSubgroup_eq_bot_of_psl2_odd
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (P : Subgroup (PSL2 K)) (hPnormal : P.Normal) (hPp : IsPGroup p P) :
    P = ⊥ := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hcard_ge_three : 3 ≤ Nat.card K := by
    rcases hK with ⟨r, n, hr, hrodd, hn, hcard⟩
    have hr_ne_two : r ≠ 2 := by
      intro hr_two
      subst r
      exact hrodd.not_two_dvd_nat (by simp)
    have hr_two_le : 2 ≤ r := hr.two_le
    have hr_ge_three : 3 ≤ r := by omega
    rw [hcard]
    calc
      3 ≤ r := hr_ge_three
      _ = r ^ 1 := by simp
      _ ≤ r ^ n := Nat.pow_le_pow_right (by omega) hn
  by_cases hcard_three : Nat.card K = 3
  · let : Fintype K := Fintype.ofFinite K
    have hFcard : Fintype.card K = 3 := by
      simpa [Nat.card_eq_fintype_card] using hcard_three
    let eK : ZMod 3 ≃+* K :=
      ZMod.ringEquivOfPrime K Nat.prime_three hFcard
    let ePSL : PSL2 K ≃* alternatingGroup (Fin 4) :=
      (psl2RingEquiv eK).symm.trans psl2_three_equiv_alternatingGroup
    exact normal_pSubgroup_eq_bot_of_mulEquiv_alternatingGroup_four
      ⟨ePSL⟩ p hp hpodd P hPnormal hPp
  · have hcard_four : 4 ≤ Nat.card K := by omega
    have hsimple : IsSimpleGroup (PSL2 K) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcard_four
    rcases (haveI := hPnormal; hsimple.eq_bot_or_eq_top_of_normal P) with hPbot | hPtop
    · exact hPbot
    · exfalso
      let S : Sylow 2 (PSL2 K) := Classical.choice Sylow.nonempty
      have hSleP : (S : Subgroup (PSL2 K)) ≤ P := by
        rw [hPtop]
        exact le_top
      let S' : Subgroup P := (S : Subgroup (PSL2 K)).subgroupOf P
      have hS'p : IsPGroup p S' := hPp.to_subgroup S'
      have hSp : IsPGroup p (S : Subgroup (PSL2 K)) :=
        hS'p.of_equiv (Subgroup.subgroupOfEquivOfLe hSleP)
      have hS2 : IsPGroup 2 (S : Subgroup (PSL2 K)) := S.isPGroup'
      let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hp_ne_two : 2 ≠ p := by
        intro h
        subst p
        exact hpodd.not_two_dvd_nat (by simp)
      have hcoprime : Nat.Coprime (Nat.card S) (Nat.card S) :=
        IsPGroup.coprime_card_of_ne 2 p hp_ne_two
          (S : Subgroup (PSL2 K)) (S : Subgroup (PSL2 K)) hS2 hSp
      have hScard_one : Nat.card S = 1 :=
        hcoprime.eq_one_of_dvd (dvd_refl _)
      rcases psl2_odd_hasDihedralSylowTwo_model K hK S with
        ⟨m, _hm, ⟨eS⟩⟩
      have hScard : Nat.card S = 2 * 2 ^ m := by
        calc
          Nat.card S = Nat.card (DihedralGroup (2 ^ m)) :=
            Nat.card_congr eS.toEquiv
          _ = 2 * 2 ^ m := DihedralGroup.nat_card
      rw [hScard_one] at hScard
      have hpow_pos : 0 < 2 ^ m := pow_pos (by norm_num) m
      omega

end CFSG.GorensteinWalter
