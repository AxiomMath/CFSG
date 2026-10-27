module

import CFSG.RankThree.Transfer.PGroup
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartOne.CTP.StrongPClassification
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourSymmetricFourEndpoint

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.GorensteinWalter CFSG.Open CFSG.RankThree.PartOne.CTP

section Generic

variable {G : Type*} [Group G]

theorem k108Field_mul_eq_one_of_mem_normalizer (T : Sylow 2 G) {a b : G}
    (ha : a ∈ Subgroup.normalizer ((T : Subgroup G) : Set G))
    (hb : b ∈ Subgroup.normalizer ((T : Subgroup G) : Set G)) (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1)
    {m : ℕ} (hm : Odd m) (habm : (a * b) ^ m = 1) : a * b = 1 := by
  have haT := CFSG.RankThree.Transfer.mem_of_pow_eq_one_of_mem_normalizer T ha (k := 1)
    (by rwa [pow_one])
  have hbT := CFSG.RankThree.Transfer.mem_of_pow_eq_one_of_mem_normalizer T hb (k := 1)
    (by rwa [pow_one])
  obtain ⟨k, hk⟩ := T.isPGroup' ⟨a * b, (mul_mem haT hbT : a * b ∈ (T : Subgroup G))⟩
  have hk' : (a * b) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd : orderOf (a * b) ∣ Nat.gcd m (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one habm) (orderOf_dvd_of_pow_eq_one hk')
  rw [(Nat.Coprime.pow_right k hm.coprime_two_right).gcd_eq_one, Nat.dvd_one] at hdvd
  exact orderOf_eq_one_iff.mp hdvd

theorem k108Field_eq_top_of_mul_pow_odd (T : Sylow 2 G) {H : Subgroup G}
    (hover : H ≠ ⊤ → H ≤ Subgroup.normalizer ((T : Subgroup G) : Set G)) {a b : G}
    (ha : a ∈ H) (hb : b ∈ H) (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1) {m : ℕ} (hm : Odd m)
    (habm : (a * b) ^ m = 1) (hab : a * b ≠ 1) : H = ⊤ := by
  by_contra hH
  exact hab (k108Field_mul_eq_one_of_mem_normalizer T (hover hH ha) (hover hH hb) ha2 hb2 hm habm)

end Generic

end CFSG.LocalAnalysis.UniquenessCase.UC22
