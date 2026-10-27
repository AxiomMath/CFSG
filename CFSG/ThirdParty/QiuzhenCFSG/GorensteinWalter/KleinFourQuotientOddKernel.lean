module

public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # Klein four subgroups survive quotients by odd kernels -/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- Mapping a Klein four subgroup through a quotient by an odd normal subgroup
again gives a Klein four subgroup. -/
public theorem isKleinFour_map_quotient_of_odd_kernel
    {H : Type u} [Group H] [Finite H]
    (O V : Subgroup H) [O.Normal]
    (hOodd : Odd (Nat.card O)) (hVK : IsKleinFour V) :
    IsKleinFour (V.map (QuotientGroup.mk' O)) := by
  classical
  let q : H →* H ⧸ O := QuotientGroup.mk' O
  let fV : V →* H ⧸ O := q.comp V.subtype
  have hfVinj : Function.Injective fV := by
    apply (MonoidHom.ker_eq_bot_iff fV).mp
    apply le_bot_iff.mp
    intro v hv
    rw [Subgroup.mem_bot]
    have hqv : q (v : H) = 1 := MonoidHom.mem_ker.mp hv
    have hvO : (v : H) ∈ O :=
      (QuotientGroup.eq_one_iff (N := O) (v : H)).mp hqv
    have hv2 : (v : H) * (v : H) = 1 :=
      congrArg Subtype.val (hVK.mul_self v)
    have hord2 : orderOf (v : H) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hv2)
    have hordO : orderOf (v : H) ∣ Nat.card O :=
      Subgroup.orderOf_dvd_natCard O hvO
    have hordOdd : Odd (orderOf (v : H)) := Odd.of_dvd_nat hOodd hordO
    have hord1 : orderOf (v : H) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hord2 with h | h
      · exact h
      · exfalso
        exact hordOdd.not_two_dvd_nat (by rw [h])
    exact Subtype.ext (orderOf_eq_one_iff.mp hord1)
  let eV : V ≃* fV.range :=
    MulEquiv.ofBijective fV.rangeRestrict
      ⟨fun a b h => hfVinj (congrArg Subtype.val h),
        MonoidHom.rangeRestrict_surjective fV⟩
  have hrange : fV.range = V.map q := by
    change (q.comp V.subtype).range = V.map q
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hRangeK : IsKleinFour fV.range := {
    card_four := (Nat.card_congr eV.toEquiv).symm.trans hVK.card_four
    exponent_two :=
      (Monoid.exponent_eq_of_mulEquiv eV).symm.trans hVK.exponent_two
  }
  change IsKleinFour (V.map q)
  rw [← hrange]
  exact hRangeK

end CFSG.GorensteinWalter
