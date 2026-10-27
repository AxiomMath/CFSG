module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJ12Facts90
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HJNormalizer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TwoNatHolds
public import CFSG.Quasithin.Background.D2Y5

@[expose] public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin Subgroup

theorem hjData_model
    {Y : Subgroup (MulAut W12)} (hLY : hjL0 ≤ Y)
    (hN : (hjL0.subgroupOf Y).Normal) :
    (∀ x : MulAut W12, x ∈ Y → orderOf x = 7 → fixV (Subgroup.zpowers x) = ⊥) ∧
      (∀ x : MulAut W12, x ∈ Y → orderOf x = 3 →
        4 ≤ rk (commSub (⊤ : Subgroup W12) (Subgroup.zpowers x))) := by
  classical
  have hfin : Finite (MulAut W12) := MulEquiv.finite_left
  have hLcard : Nat.card hjL0 = 604800 := by
    obtain ⟨e⟩ := hjL0_isSpor
    exact (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.J2.card_J2
  have hfac7 : (Nat.card hjL0).factorization 7 = 1 := by
    rw [hLcard]
    have h1 : 1 ≤ (604800 : ℕ).factorization 7 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_seven (by norm_num)).mp
        (by norm_num : 7 ^ 1 ∣ (604800 : ℕ))
    have h2 : ¬ 2 ≤ (604800 : ℕ).factorization 7 := by
      intro h2
      exact absurd ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_seven
        (by norm_num)).mpr h2) (by norm_num)
    exact le_antisymm (Nat.lt_succ_iff.mp (Nat.lt_of_not_le h2)) h1
  have hfac3 : (Nat.card hjL0).factorization 3 = 3 := by
    rw [hLcard]
    have h1 : 3 ≤ (604800 : ℕ).factorization 3 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three (by norm_num)).mp
        (by norm_num : 3 ^ 3 ∣ (604800 : ℕ))
    have h2 : ¬ 4 ≤ (604800 : ℕ).factorization 3 := by
      intro h2
      exact absurd ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three
        (by norm_num)).mpr h2) (by norm_num)
    exact le_antisymm (Nat.lt_succ_iff.mp (Nat.lt_of_not_le h2)) h1
  constructor
  · intro x hxY hx7
    have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    let H : Subgroup ↥Y := hjL0.subgroupOf Y
    have : H.Normal := hN
    have hHcard : Nat.card ↥H = Nat.card hjL0 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLY).toEquiv
    have h1 : H.index * Nat.card ↥H ∣ 6 * Nat.card ↥H := by
      rw [Subgroup.index_mul_card H, hHcard]
      exact card_dvd_six_mul_of_normal hLY hN
    have h1' : Nat.card ↥H * H.index ∣ Nat.card ↥H * 6 := by
      rw [mul_comm (Nat.card ↥H) H.index, mul_comm (Nat.card ↥H) 6]
      exact h1
    have hidx6 : H.index ∣ 6 :=
      Nat.dvd_of_mul_dvd_mul_left Nat.card_pos h1'
    have hx6H : x ^ 6 ∈ hjL0 := by
      have hpow : (⟨x, hxY⟩ : ↥Y) ^ H.index ∈ H := Subgroup.pow_index_mem H _
      have hmem : ((⟨x, hxY⟩ : ↥Y) ^ H.index) ^ (6 / H.index) ∈ H :=
        H.pow_mem hpow (6 / H.index)
      rw [← pow_mul, Nat.mul_div_cancel' hidx6] at hmem
      have hmem' : ((⟨x, hxY⟩ : ↥Y) ^ 6 : MulAut W12) ∈ hjL0 := by
        rwa [Subgroup.mem_subgroupOf] at hmem
      simpa using hmem'
    have hx7' : x ^ 7 = 1 := by
      rw [← hx7]
      exact pow_orderOf_eq_one x
    have hx6x : x * x ^ 6 = 1 := by
      calc x * x ^ 6 = x ^ (6 + 1) := (pow_succ' x 6).symm
        _ = x ^ 7 := by norm_num
        _ = 1 := hx7'
    have hxL : x ∈ hjL0 := by
      have hxeq : x = (x ^ 6)⁻¹ := (mul_eq_one_iff_eq_inv).mp hx6x
      rw [hxeq]
      exact hjL0.inv_mem hx6H
    obtain ⟨hX7mem, hX7ord, hX7fix⟩ := hjX7_facts
    have hsylx : IsSylowIn 7 (Subgroup.zpowers x) hjL0 :=
      isSylowIn_of_card_eq (Subgroup.zpowers_le.2 hxL)
        (by rw [Nat.card_zpowers, hx7, hfac7, pow_one])
    have hsylX7 : IsSylowIn 7 (Subgroup.zpowers hjX7) hjL0 :=
      isSylowIn_of_card_eq (Subgroup.zpowers_le.2 hX7mem)
        (by rw [Nat.card_zpowers, hX7ord, hfac7, pow_one])
    obtain ⟨k, -, hconj⟩ := isSylowIn_exists_conj hsylx hsylX7
    have h1 : (fixV (Subgroup.zpowers x)).map k.toMonoidHom = ⊥ := by
      have h2 := fixV_map_conj_eq (Subgroup.zpowers x) k
      rw [← hconj] at h2
      exact h2.symm.trans hX7fix
    exact (Subgroup.map_eq_bot_iff_of_injective (fixV (Subgroup.zpowers x))
      k.injective).mp h1
  · intro x hxY hx3
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hx3' : x ^ 3 = 1 := by
      rw [← hx3]
      exact pow_orderOf_eq_one x
    have hx4 : x ^ 4 = x := by
      calc x ^ 4 = x ^ (3 + 1) := by norm_num
        _ = x ^ 3 * x := pow_succ x 3
        _ = x := by rw [hx3', one_mul]
    have hx2sq : (x ^ 2) ^ 2 = x := by
      calc (x ^ 2) ^ 2 = x ^ 4 := by group
        _ = x := hx4
    obtain ⟨l, hlL, c, hcOmega, hsq⟩ := sq_mem_of_normal hLY hN (Y.pow_mem hxY 2)
    have hxl : x = l * c := by
      rw [← hx2sq]
      exact hsq
    have hcCent : c ∈ Subgroup.centralizer (hjL0 : Set (MulAut W12)) :=
      Subgroup.zpowers_le.2 hjOmega_mem_centralizer hcOmega
    have hcomm : l * c = c * l := Subgroup.mem_centralizer_iff.mp hcCent l hlL
    have hc3 : c ^ 3 = 1 := by
      have hdvd : orderOf c ∣ 3 := by
        rw [← orderOf_hjOmega]
        exact orderOf_dvd_of_mem_zpowers hcOmega
      exact orderOf_dvd_iff_pow_eq_one.mp hdvd
    have hl3 : l ^ 3 = 1 := by
      have h : (l * c) ^ 3 = 1 := by rw [← hxl, hx3']
      rw [Commute.mul_pow (show Commute l c from hcomm), hc3, mul_one] at h
      exact h
    have hP3 := hjP3_facts
    have hP3syl : IsSylowIn 3 hjP3 hjL0 :=
      isSylowIn_of_card_eq hP3.1 (by rw [hP3.2.1, hfac3]; norm_num)
    have hPl : IsPGroup 3 (Subgroup.zpowers l) := by
      apply IsPGroup.of_card_dvd_pow (n := 1)
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_iff_pow_eq_one.mpr hl3
    obtain ⟨S, hS, hleS⟩ := exists_isSylowIn_ge 3 (Subgroup.zpowers_le.2 hlL) hPl
    obtain ⟨k, hkL, hconj⟩ := isSylowIn_exists_conj hS hP3syl
    have hkP3 : k * l * k⁻¹ ∈ hjP3 := by
      have h1 : MulAut.conj k l ∈ S.map (MulAut.conj k).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨l, hleS (Subgroup.mem_zpowers l), rfl⟩
      rw [← hconj] at h1
      simpa [MulAut.conj_apply] using h1
    have hc_fix : k * c * k⁻¹ = c := by
      have hk : k * c = c * k := Subgroup.mem_centralizer_iff.mp hcCent k hkL
      calc k * c * k⁻¹ = c * k * k⁻¹ := by rw [hk]
        _ = c := by group
    have hkc : (k * l * k⁻¹) * c = c * (k * l * k⁻¹) :=
      Subgroup.mem_centralizer_iff.mp hcCent (k * l * k⁻¹) (hP3.1 hkP3)
    have hconjx : k * x * k⁻¹ = c * (k * l * k⁻¹) := by
      rw [hxl]
      calc k * (l * c) * k⁻¹ = (k * l * k⁻¹) * (k * c * k⁻¹) := by group
        _ = (k * l * k⁻¹) * c := by rw [hc_fix]
        _ = c * (k * l * k⁻¹) := hkc
    have hord : orderOf (c * (k * l * k⁻¹)) = 3 := by
      rw [← hconjx, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hx3]
    have hne : c * (k * l * k⁻¹) ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hord
      exact absurd hord (by norm_num)
    have hrk : 4 ≤ rk (commSub (⊤ : Subgroup W12)
        (Subgroup.zpowers (c * (k * l * k⁻¹)))) :=
      hP3.2.2 c hcOmega (k * l * k⁻¹) hkP3 hne
    have hxeq : x = k⁻¹ * (c * (k * l * k⁻¹)) * k := by
      rw [← hconjx]
      group
    have hrkeq : rk (commSub (⊤ : Subgroup W12) (Subgroup.zpowers x)) =
        rk (commSub (⊤ : Subgroup W12)
          (Subgroup.zpowers (c * (k * l * k⁻¹)))) := by
      rw [← commV_eq_commSub, ← commV_eq_commSub, hxeq]
      have h := rk_commV_zpowers_conj k⁻¹ (c * (k * l * k⁻¹))
      rw [inv_inv] at h
      exact h
    rw [hrkeq]
    exact hrk

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
