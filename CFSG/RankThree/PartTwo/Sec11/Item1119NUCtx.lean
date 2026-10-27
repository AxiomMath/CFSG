module

import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarCenter
public import CFSG.RankThree.PartTwo.Sec11.RFacts
import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolNumbers

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.GorensteinWalter

namespace Item1119NU

section Ctx


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem three_pow_dvd_orderOf_x (h : Sec11Data G A c L a R Y d x s r g) {m : ℕ}
    (hm : 3 ^ m ∣ Nat.card (L ⧸ aschbacherSolvableCore 3 L)) : 3 ^ m ∣ orderOf x := by
  have hsyl : IsSylowOf 3 (Subgroup.zpowers x) L := by
    have hs := h.toSec11Std.isSylowOf_inf_L
    rwa [h.inf_L_eq] at hs
  rw [CFSG.RankThree.PartTwo.Sec11.Item1120V0Bar.orderOf_eq_three_pow_of_isSylowOf hsyl]
  have hdvd : Nat.card (L ⧸ aschbacherSolvableCore 3 L) ∣ Nat.card L := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 L)]
    exact dvd_mul_right _ _
  have hne : Nat.card L ≠ 0 := Nat.card_pos.ne'
  exact pow_dvd_pow 3 ((Nat.prime_three.pow_dvd_iff_le_factorization hne).mp (hm.trans hdvd))

theorem not_isInnerAut_of_mem_closure (h : Sec11Data G A c L a R Y d x s r g)
    {f : G} (hf : f ∈ Subgroup.closure ({a, c} : Set G)) (hfc : f ∉ Subgroup.zpowers c)
    (hfN : f ∈ Subgroup.normalizer (L : Set G)) :
    ¬ KFacts.IsInnerAut (Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨f, hfN⟩)) := by
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) :=
    CFSG.RankThree.PartTwo.Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hcL : ∀ l ∈ L, c * l = l * c := fun l hl =>
    Subgroup.mem_centralizer_iff.mp (hLc hl) c (Set.mem_singleton c)
  have hcN : c ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer (L : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun l hl => (hcL l hl).symm)
  have hcAct : Sec4.compAction L ⟨c, hcN⟩ = 1 := by
    refine MulEquiv.ext fun l => Subtype.ext ?_
    show ((L.normalizerMonoidHom ⟨c, hcN⟩ l : L) : G) = (l : G)
    rw [Sec4.normalizerMonoidHom_apply_coe, hcL (l : G) l.2, mul_inv_cancel_right]
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hca : c * a = a * c :=
    congrArg Subtype.val (h.mem_partTwoF.1.1.is_comm.comm ⟨c, h.mem_A⟩ ⟨a, h.a_mem⟩)
  obtain ⟨j, n, hfj⟩ := CFSG.RankThree.PartTwo.Sec11.Item1119Sym.exists_zpow_form hca.symm hf
  have haN : a ∈ Subgroup.normalizer (L : Set G) := h.toHyp81.a_mem_normalizer
  have hsub : (⟨f, hfN⟩ : Subgroup.normalizer (L : Set G)) =
      (⟨a, haN⟩ : Subgroup.normalizer (L : Set G)) ^ j *
        (⟨c, hcN⟩ : Subgroup.normalizer (L : Set G)) ^ n := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_zpow]
    exact hfj
  have hψc : Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨c, hcN⟩) = 1 := by
    rw [hcAct, map_one]
  have hφf : Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨f, hfN⟩) =
      Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a, haN⟩) ^ j := by
    rw [hsub]
    simp only [map_mul, map_zpow, hψc, one_zpow, mul_one]
  have hna : ¬ KFacts.IsInnerAut (Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a, haN⟩)) :=
    h.toHyp81.not_isInnerAut_induced
  have hpow : Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a, haN⟩) ^ (3 : ℤ) = 1 := by
    rw [zpow_ofNat]
    exact h.toHyp81.induced_pow_three
  intro hin
  rw [hφf] at hin
  set τ := Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a, haN⟩) with hτ
  have hn3 : ¬ (3 : ℤ) ∣ j := by
    rintro ⟨k, rfl⟩
    apply hfc
    have ha : a ^ (3 * k) = 1 := by
      rw [zpow_mul, zpow_ofNat, ha3, one_zpow]
    rw [hfj, ha, one_mul]
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩
  obtain ⟨u, v, huv⟩ := (_root_.Prime.coprime_iff_not_dvd Int.prime_three).mpr hn3
  have hu3 : τ ^ (u * 3) = 1 := by
    rw [mul_comm, zpow_mul, hpow, one_zpow]
  have key : τ = (τ ^ j) ^ v := by
    calc τ = τ ^ (u * 3 + v * j) := by rw [huv, zpow_one]
      _ = τ ^ (u * 3) * τ ^ (v * j) := zpow_add τ (u * 3) (v * j)
      _ = (τ ^ j) ^ v := by rw [zpow_mul' τ v j, hu3, one_mul]
  apply hna
  rw [key]
  exact Subgroup.zpow_mem _ hin v

end Ctx

end Item1119NU

end CFSG.RankThree.PartTwo.Sec11

end
