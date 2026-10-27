module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Classification

namespace CFSG
end CFSG
open CFSG

/-!
# Recovering an involution from an odd-kernel quotient image

If the image of an involution modulo an odd normal subgroup lies in the
image of another normal subgroup, the involution already lies in that
subgroup.
-/

namespace CFSG.GorensteinWalter

/-- Let `E` and `O` be normal subgroups, with `O` of odd order.  If the image
of an involution `t` modulo `O` lies in the image of `E`, then `t ∈ E`. -/
public theorem involution_mem_normal_subgroup_of_quotient_mem_map_odd_kernel
    {H : Type*} [Group H] [Finite H]
    (E O : Subgroup H) (hEnormal : E.Normal) (hOnormal : O.Normal)
    (hOodd : Odd (Nat.card O))
    {t : H} (ht : IsInvolution t)
    (htq : QuotientGroup.mk' O t ∈ E.map (QuotientGroup.mk' O)) :
    t ∈ E := by
  classical
  let : E.Normal := hEnormal
  let : O.Normal := hOnormal
  let qO : H →* H ⧸ O := QuotientGroup.mk' O
  let qE : H →* H ⧸ E := QuotientGroup.mk' E
  rcases Subgroup.mem_map.mp htq with ⟨e, heE, het⟩
  have hteO : t * e⁻¹ ∈ O := by
    rw [← QuotientGroup.eq_one_iff (N := O)]
    change qO (t * e⁻¹) = 1
    simp [qO, map_mul, map_inv, ← het]
  let Obar : Subgroup (H ⧸ E) := O.map qE
  have hObarOdd : Odd (Nat.card Obar) :=
    Odd.of_dvd_nat hOodd (Subgroup.card_map_dvd O qE)
  have hqtObar : qE t ∈ Obar := by
    refine Subgroup.mem_map.mpr ⟨t * e⁻¹, hteO, ?_⟩
    simp [qE, map_mul, map_inv,
      (QuotientGroup.eq_one_iff (N := E) e).mpr heE]
  let tbar : Obar := ⟨qE t, hqtObar⟩
  have htbar_sq : tbar ^ 2 = 1 := by
    apply Subtype.ext
    simpa [tbar, qE] using congrArg qE ht.2
  have htbar_one : tbar = 1 := by
    have hord2 : orderOf tbar ∣ 2 :=
      (orderOf_dvd_iff_pow_eq_one (x := tbar) (n := 2)).2 htbar_sq
    have hordCard : orderOf tbar ∣ Nat.card Obar :=
      orderOf_dvd_natCard tbar
    have hdvd : orderOf tbar ∣ (2 : ℕ).gcd (Nat.card Obar) :=
      Nat.dvd_gcd hord2 hordCard
    have hgcd : (2 : ℕ).gcd (Nat.card Obar) = 1 :=
      hObarOdd.coprime_two_left.gcd_eq_one
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (by simpa [hgcd] using hdvd))
  have hqt_one : qE t = 1 := congrArg Subtype.val htbar_one
  exact (QuotientGroup.eq_one_iff (N := E) t).mp hqt_one

end CFSG.GorensteinWalter
