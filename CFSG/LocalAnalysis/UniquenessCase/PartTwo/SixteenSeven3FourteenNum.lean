module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3FourteenDefs
public import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c1614_false_of_index {p : ℕ} (hp : p.Prime) {M K : Subgroup G}
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M) (hKM : ¬ K ≤ M) {n : ℕ}
    (hidx : (K ⊓ M).relIndex K = 2 ^ n + 1) (hpn : p ∣ 2 ^ n - 1)
    (hpK : p ∣ Nat.card ↥(K ⊓ M)) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hK := hsp.subgroupOf hKM hpK
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hxp : (x : G) ^ p = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx] at h
    simpa using congrArg Subtype.val h
  have hx1 : (x : G) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    exact hp.one_lt.ne hx
  set x' : K := ⟨(x : G), x.2.1⟩ with hx'
  have hQp : IsPGroup p (Subgroup.zpowers x') := by
    refine CFSG.RankThree.PartOne.StrongP.isPGroup_zpowers_of_pow_eq_one ?_
    exact Subtype.ext hxp
  have hx'Y : x' ∈ (K ⊓ M).subgroupOf K := Subgroup.mem_subgroupOf.2 x.2
  have hmod := hK.index_modEq (Q := Subgroup.zpowers x')
    (by rw [Ne, Subgroup.zpowers_eq_bot]; exact fun h => hx1 (congrArg Subtype.val h)) hQp
    (Subgroup.zpowers_le.mpr hx'Y)
  have hidx' : ((K ⊓ M).subgroupOf K).index = 2 ^ n + 1 := hidx
  rw [hidx'] at hmod
  have h2 : 2 ^ n ≡ 0 [MOD p] := Nat.ModEq.add_right_cancel' 1 (by simpa using hmod)
  have hdvd : p ∣ 2 ^ n := Nat.modEq_zero_iff_dvd.1 h2
  have h1 : p ∣ 2 ^ n - (2 ^ n - 1) := Nat.dvd_sub hdvd hpn
  rw [Nat.sub_sub_self Nat.one_le_two_pow] at h1
  exact hp.not_dvd_one h1

theorem s16c1614_not_dvd_of_cartan (D : Data G) {V U : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M) (h : Cartan1614 D V U) {n : ℕ}
    (hn : rMV D.M V = (n : ℕ∞)) : ¬ p ∣ 2 ^ n - 1 := by
  intro hpn
  obtain ⟨n', K, X, hn', -, hKM, -, hidx, hXK, -, hXcard, -, -⟩ := h
  have hnn : n' = n := ENat.coe_inj.1 (hn'.symm.trans hn)
  subst hnn
  refine s16c1614_false_of_index hp hsp hKM hidx hpn ?_
  rw [← hXcard] at hpn
  exact hpn.trans (Subgroup.card_dvd_of_le hXK)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
