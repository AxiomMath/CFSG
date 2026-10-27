module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupPSL2
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearRingEquiv
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThreeEquiv
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalOddPSubgroupSymmetricFour
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddSubgroupLeNormalIndexTwo
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DerivedSubgroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2InnerAction
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Normal odd-prime subgroups of odd `PGL₂`

For the field of order three, use `PGL₂(3) ≃ S₄`.  Over larger odd fields,
an odd subgroup lies in the index-two derived `PSL₂` subgroup, where the
normal odd-prime subgroup theorem for `PSL₂` applies.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- A normal odd-prime subgroup of `PGL₂(K)`, for `K` of odd prime-power
order, is trivial. -/
public theorem normal_pSubgroup_eq_bot_of_pgl2_odd
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (P : Subgroup (PGL2 K)) (hPnormal : P.Normal) (hPp : IsPGroup p P) :
    P = ⊥ := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
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
    let ePGL : PGL2 K ≃* Equiv.Perm (Fin 4) :=
      (pgl2RingEquiv eK).symm.trans pgl2_three_equiv_perm
    exact normal_pSubgroup_eq_bot_of_mulEquiv_perm_four
      ⟨ePGL⟩ p hp hpodd P hPnormal hPp
  · have hcard_gt_three : 3 < Nat.card K := by omega
    let C : Subgroup (PGL2 K) := commutator (PGL2 K)
    have hCnormal : C.Normal := by
      dsimp [C]
      infer_instance
    have hCindex : C.index = 2 := by
      dsimp [C]
      rw [pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard_gt_three]
      exact pgl2_psl2Range_index_eq_two K hK
    have hPcard_odd : Odd (Nat.card P) := by
      rcases hPp.exists_card_eq with ⟨m, hm⟩
      rw [hm]
      exact hpodd.pow
    have hPleC : P ≤ C :=
      odd_card_subgroup_le_normal_index_two C P hCnormal hCindex hPcard_odd
    let PC : Subgroup C := P.subgroupOf C
    have hPCnormal : PC.Normal := hPnormal.subgroupOf C
    have hPCp : IsPGroup p PC :=
      hPp.of_equiv (Subgroup.subgroupOfEquivOfLe hPleC).symm
    let eC : C ≃* PSL2 K :=
      (commutator_mulEquiv_psl2_of_mulEquiv_pgl2_card_gt_three
        K hK hcard_gt_three (MulEquiv.refl (PGL2 K))).some
    let Q : Subgroup (PSL2 K) := PC.map eC.toMonoidHom
    have hQnormal : Q.Normal :=
      hPCnormal.map eC.toMonoidHom eC.surjective
    have hQp : IsPGroup p Q := IsPGroup.map hPCp eC.toMonoidHom
    have hQbot : Q = ⊥ :=
      normal_pSubgroup_eq_bot_of_psl2_odd K hK p hp hpodd Q hQnormal hQp
    have hPCbot : PC = ⊥ := by
      apply (Subgroup.map_eq_bot_iff_of_injective
        (H := PC) (f := eC.toMonoidHom) eC.injective).mp
      simpa [Q] using hQbot
    apply le_bot_iff.mp
    intro x hx
    have hxPC : (⟨x, hPleC hx⟩ : C) ∈ PC :=
      Subgroup.mem_subgroupOf.mpr hx
    have hxone : (⟨x, hPleC hx⟩ : C) = 1 := by
      rw [hPCbot] at hxPC
      exact Subgroup.mem_bot.mp hxPC
    exact congrArg Subtype.val hxone

end CFSG.GorensteinWalter
