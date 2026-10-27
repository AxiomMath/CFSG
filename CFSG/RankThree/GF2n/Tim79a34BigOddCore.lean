module

public import CFSG.CGT.Timmesfeld75.Defs
import CFSG.GroupTheory.HyperplaneGeneration

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type*} [Group G]

theorem eq_one_of_odd_card_of_sq_eq_one {N : Subgroup G} (hNodd : Odd (Nat.card N)) {y : G}
    (hy : y ∈ N) (hy2 : y ^ 2 = 1) : y = 1 := by
  have hodd : Odd (orderOf y) := Odd.of_dvd_nat hNodd (Subgroup.orderOf_dvd_natCard N hy)
  have hdvd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (by decide)

theorem mem_centralizer_of_commute_of_isTI {B N : Subgroup G} [hNn : N.Normal]
    (hBe : IsElemAbelian 2 B) (hTI : IsTI B) (hNodd : Odd (Nat.card N)) {b n : G} (hb : b ∈ B)
    (hb1 : b ≠ 1) (hn : n ∈ N) (hbn : n * b = b * n) :
    n ∈ Subgroup.centralizer (B : Set G) := by
  have hbconj : b ∈ conjSubgroup n B := by
    rw [mem_conjSubgroup]
    have : n⁻¹ * b * n = b := by
      rw [mul_assoc, ← hbn, inv_mul_cancel_left]
    rw [this]
    exact hb
  have hBle : B ≤ conjSubgroup n B := by
    rcases hTI n with h | h
    · exact absurd (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_inf.mpr ⟨hb, hbconj⟩)) hb1
    · exact inf_eq_left.mp h
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx' : n⁻¹ * x * n ∈ B := mem_conjSubgroup.mp (hBle hx)
  have hyB : n⁻¹ * x * n * x⁻¹ ∈ B := mul_mem hx' (inv_mem hx)
  have hyN : n⁻¹ * x * n * x⁻¹ ∈ N := by
    have h1 : n⁻¹ * (x * n * x⁻¹) ∈ N := mul_mem (inv_mem hn) (hNn.conj_mem n hn x)
    rwa [← mul_assoc, ← mul_assoc] at h1
  have h2 : n⁻¹ * x * n * x⁻¹ = 1 :=
    eq_one_of_odd_card_of_sq_eq_one hNodd hyN (hBe.2 _ hyB)
  have h3 : n⁻¹ * x * n = x := mul_inv_eq_one.mp h2
  calc x * n = n * (n⁻¹ * x * n) := by group
    _ = n * x := by rw [h3]

theorem le_centralizer_of_odd_card_of_isTI {M : Type*} [Group M] [Finite M] {B N : Subgroup M}
    [hNn : N.Normal] (hBe : IsElemAbelian 2 B) (hB4 : 4 ≤ Nat.card B) (hTI : IsTI B)
    (hNodd : Odd (Nat.card N)) : N ≤ Subgroup.centralizer (B : Set M) := by
  haveI : CFSG.IsElementaryAbelian 2 B :=
    { toIsMulCommutative := hBe.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by rw [Subgroup.coe_pow, hBe.2 x x.2, Subgroup.coe_one]) }
  let _action : MulDistribMulAction B N :=
    MulDistribMulAction.compHom N ((MulAut.conjNormal (H := N)).comp B.subtype)
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := 2) (A := B) (H := N)
    (by simpa using hB4) hNodd.not_two_dvd_nat
  have hle : (⊤ : Subgroup N) ≤ (Subgroup.centralizer (B : Set M)).comap N.subtype := by
    rw [← hgen]
    refine iSup_le fun a => iSup_le fun ha1 => ?_
    intro x hx
    rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hx
    have hsmul : (a : M) * (x : M) * (a : M)⁻¹ = (x : M) := congrArg Subtype.val hx
    have ha1' : (a : M) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hax : (x : M) * (a : M) = (a : M) * (x : M) := (mul_inv_eq_iff_eq_mul.mp hsmul).symm
    exact mem_centralizer_of_commute_of_isTI hBe hTI hNodd a.2 ha1' x.2 hax
  intro n hn
  exact hle (Subgroup.mem_top (⟨n, hn⟩ : N))

theorem le_centralizer_of_odd_card_of_le_normalizer {R N : Subgroup G} [hNn : N.Normal]
    (hRs : IsSimpleGroup R) (hRe : Even (Nat.card R)) (hNodd : Odd (Nat.card N))
    (hNR : N ≤ Subgroup.normalizer (R : Set G)) : N ≤ Subgroup.centralizer (R : Set G) := by
  have hbot : N.subgroupOf R = ⊥ := by
    rcases hRs.eq_bot_or_eq_top_of_normal (N.subgroupOf R) with h | h
    · exact h
    · exfalso
      have hRN : R ≤ N := fun r hr => by
        have hmem : (⟨r, hr⟩ : R) ∈ N.subgroupOf R := h ▸ Subgroup.mem_top _
        exact Subgroup.mem_subgroupOf.mp hmem
      exact hNodd.not_two_dvd_nat
        ((even_iff_two_dvd.mp hRe).trans (Subgroup.card_dvd_of_le hRN))
  intro n hn
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  have hnr : n * r * n⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hNR hn) r).mp hr
  have hcR : n * r * n⁻¹ * r⁻¹ ∈ R := mul_mem hnr (inv_mem hr)
  have hcN : n * r * n⁻¹ * r⁻¹ ∈ N := by
    have h1 : n * (r * n⁻¹ * r⁻¹) ∈ N := mul_mem hn (hNn.conj_mem n⁻¹ (inv_mem hn) r)
    rwa [← mul_assoc, ← mul_assoc] at h1
  have hmem : (⟨_, hcR⟩ : R) ∈ N.subgroupOf R := Subgroup.mem_subgroupOf.mpr hcN
  rw [hbot, Subgroup.mem_bot] at hmem
  have h2 : n * r * n⁻¹ * r⁻¹ = 1 := congrArg Subtype.val hmem
  have h3 : n * r * n⁻¹ = r := mul_inv_eq_one.mp h2
  calc r * n = (n * r * n⁻¹) * n := by rw [h3]
    _ = n * r := by group

end CFSG.RankThree.GF2n.Tim79a
