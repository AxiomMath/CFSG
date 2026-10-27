module

public import CFSG.Quasithin.Background.F6Basic
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtX1512Bar

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace X1512

variable {G : Type} [Group G] [Finite G]

theorem le_kerIn {T H P C : Subgroup G} (hmp : MinParabolic H T P) (hCH : C ≤ H)
    (hCn : H ≤ Subgroup.normalizer (C : Set G)) (hK : ¬ oTwoUpper H ≤ C) : C ≤ kerIn P H := by
  have hK' : ¬ twoResidual H ≤ C := by
    rw [F6.twoResidual_eq_oTwoUpper]
    exact hK
  exact hmp.le_kerIn_of_not_twoResidual_le hCH hCn hK'

theorem le_and_isSylow {T H P C : Subgroup G} (hmp : MinParabolic H T P) (hCH : C ≤ H)
    (hCn : H ≤ Subgroup.normalizer (C : Set G)) (hQC : pCoreOf 2 H ≤ C)
    (hK : ¬ oTwoUpper H ≤ C) : C ≤ P ∧ IsSylowTwoOf (pCoreOf 2 H) C := by
  have hCJ : C ≤ kerIn P H := le_kerIn hmp hCH hCn hK
  refine ⟨hCJ.trans kerIn_le, ?_⟩
  have hJ := hmp.isSylowTwoOf_pCoreOf_kerIn
  refine ⟨hQC, hJ.2.1, fun hdvd => hJ.2.2 ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex (pCoreOf 2 H) C (kerIn P H) hQC hCJ
  have h2 : 2 ∣ (pCoreOf 2 H).relIndex C := hdvd
  show 2 ∣ (pCoreOf 2 H).relIndex (kerIn P H)
  rw [← h1]
  exact Dvd.dvd.mul_right h2 _

theorem inf_le_pCoreOf {T H P C : Subgroup G} (hmp : MinParabolic H T P) (hCH : C ≤ H)
    (hCn : H ≤ Subgroup.normalizer (C : Set G)) (hK : ¬ oTwoUpper H ≤ C) :
    T ⊓ C ≤ pCoreOf 2 H :=
  hmp.le_pCoreOf_of_isPGroup_of_le_kerIn (hmp.isSylow.2.1.to_le inf_le_left)
    (inf_le_right.trans (le_kerIn hmp hCH hCn hK))

theorem mem_pCoreOf_of_sq_mem {H C : Subgroup G} (hCH : C ≤ H)
    (hCsyl : IsSylowTwoOf (pCoreOf 2 H) C) {c : G} (hc : c ∈ C) (hc2 : c ^ 2 ∈ pCoreOf 2 H) :
    c ∈ pCoreOf 2 H := by
  have hQC : pCoreOf 2 H ≤ C := hCsyl.1
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 H) ⟨c ^ 2, hc2⟩
  have hk0 : (c ^ 2) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hk' : c ^ 2 ^ (k + 1) = 1 := by
    rw [pow_succ', pow_mul]
    exact hk0
  have hp : IsPGroup 2 (Subgroup.zpowers c) := by
    have hdvd : orderOf c ∣ 2 ^ (k + 1) := orderOf_dvd_of_pow_eq_one hk'
    obtain ⟨n, -, hn⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  have hle := B6.le_of_isPGroup_of_odd_relIndex (H := C) (N := pCoreOf 2 H)
    (T := Subgroup.zpowers c) (Subgroup.zpowers_le.mpr hc) hp hQC
    (hCH.trans (le_normalizer_pCoreOf 2 H)) hCsyl.2.2
  exact hle (Subgroup.mem_zpowers c)

theorem odd_card_imBar {H C : Subgroup G} (hCH : C ≤ H) (hCsyl : IsSylowTwoOf (pCoreOf 2 H) C) :
    Odd (Nat.card (imBar H C)) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card (imBar H C) := by
    rw [Nat.not_odd_iff_even] at hodd
    exact even_iff_two_dvd.mp hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨z, hzC⟩, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hz2 : orderOf z = 2 := by simpa using hz
  obtain ⟨c, hcH, hcC, rfl⟩ := mem_imBar.mp hzC
  have hsq : bar H c ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp hz2.dvd
  have hc2 : c ^ 2 ∈ pCoreOf 2 H := by
    rw [← bar_eq_one_iff (H.pow_mem hcH 2), bar_pow hcH]
    exact hsq
  have hcQ : c ∈ pCoreOf 2 H := mem_pCoreOf_of_sq_mem hCH hCsyl hcC hc2
  have h1 : bar H c = 1 := (bar_eq_one_iff hcH).mpr hcQ
  rw [h1, orderOf_one] at hz2
  exact absurd hz2 (by norm_num)

end X1512

end CFSG.Quasithin
