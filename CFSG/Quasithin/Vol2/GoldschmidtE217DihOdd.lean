module

public import CFSG.Quasithin.Background.E2SeventeenSolv
public import CFSG.Quasithin.Vol2.Ch3E213MKer
public import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits B2F

namespace E2

namespace DihedralPair

variable {G : Type*} [Group G] [Finite G] {H T V U : Subgroup G} {x z : G}

omit [Finite G] in
theorem zpowers_x_le_normalizer (d : DihedralPair H T V U x z) :
    Subgroup.zpowers x ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
  refine Subgroup.zpowers_le.2 (B6.mem_normalizer_of_forall_mem (fun c hc => ?_) (fun c hc => ?_))
  · rw [conj_eq_inv_of_mem_zpowers d.xz hc]
    exact (Subgroup.zpowers z).inv_mem hc
  · have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right d.x2
    have h1 := conj_eq_inv_of_mem_zpowers d.xz hc
    rw [hxi] at h1 ⊢
    rw [h1]
    exact (Subgroup.zpowers z).inv_mem hc

theorem charTwo_dpI (d : DihedralPair H T V U x z) : CharTwo (dpI V z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 H with hQ
  set X := Q ⊔ dpI V z with hX
  have hXH : X ≤ H := sup_le (pCoreOf_le 2 H) d.IH
  have hXN : X ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le Subgroup.le_normalizer (d.IH.trans d.HQ)
  have hQX : Q ≤ pCoreOf 2 X :=
    le_pCoreOf_of_le_normalizer 2 le_sup_left hXN (pCoreOf_isPGroup 2 H)
  have hcharX : CharTwo X := by
    intro g hg
    have hgC : g ∈ Subgroup.centralizer (Q : Set G) :=
      Subgroup.mem_centralizer_iff.2 fun q hq =>
        Subgroup.mem_centralizer_iff.1 hg.2 q (hQX hq)
    exact hQX (d.char ⟨hXH hg.1, hgC⟩)
  exact CharTwo.of_normal hcharX le_sup_right
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).2
      (sup_le d.QI Subgroup.le_normalizer))

theorem pCoreOf_dpI_le (d : DihedralPair H T V U x z) : pCoreOf 2 (dpI V z) ≤ dpP H V U z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := dpI V z with hI
  set P := dpP H V U z with hP
  set O := pCoreOf 2 I with hO
  have hP2 : IsPGroup 2 P := d.T2.to_le (d.PR.trans d.RT)
  have hPI : P ≤ I := d.PR.trans inf_le_left
  have hPO : P ≤ O := le_pCoreOf_of_le_normalizer 2 hPI d.IP hP2
  have hO2 : IsPGroup 2 O := pCoreOf_isPGroup 2 I
  have hSN : Subgroup.zpowers z ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (P : Set G) :=
    d.S_le.trans d.IP
  intro e he
  have he' : e ∈ (((Subgroup.zpowers z ⊔ Subgroup.zpowers x) ⊔ P : Subgroup G) : Set G) :=
    d.le_S_sup_P (pCoreOf_le 2 I he)
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hSN] at he'
  obtain ⟨s, hs, p, hp, rfl⟩ := he'
  change s * p ∈ O at he
  show s * p ∈ P
  have hsO : s ∈ O := by simpa using O.mul_mem he (O.inv_mem (hPO hp))
  have hs1 : s = 1 := by
    have hs' : s ∈ ((Subgroup.zpowers z ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := hs
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ d.zpowers_x_le_normalizer] at hs'
    obtain ⟨c, hc, y, hy, rfl⟩ := hs'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    change c * x ^ k ∈ O at hsO
    show c * x ^ k = 1
    have hx2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two, d.x2]
    rw [zpow_eq_zpow_emod k hx2] at hsO ⊢
    have hcodd : Odd (orderOf c) :=
      Odd.of_dvd_nat d.zodd (orderOf_dvd_of_mem_zpowers hc)
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · rw [h, zpow_zero, mul_one] at hsO ⊢
      obtain ⟨k', hk'⟩ := exists_pow_two_pow_eq_one hO2 hsO
      exact eq_one_of_odd_orderOf_of_pow_two_pow hcodd hk'
    · exfalso
      rw [h, zpow_one] at hsO
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
      have hcz : z ^ j * z = z * z ^ j := ((Commute.refl z).zpow_right j).symm.eq
      have hxz' : x * z⁻¹ * x⁻¹ = z := by
        have := congrArg (·⁻¹) d.xz
        simpa [mul_assoc] using this
      have hzO : z ∈ Subgroup.normalizer (O : Set G) := le_normalizer_pCoreOf 2 I d.zI
      have h1 : z * (z ^ j * x) * z⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp hzO _).mp hsO
      have h2 := O.mul_mem h1 (O.inv_mem hsO)
      have e2 : z * (z ^ j * x) * z⁻¹ * (z ^ j * x)⁻¹ = z ^ 2 := by
        calc z * (z ^ j * x) * z⁻¹ * (z ^ j * x)⁻¹
            = z * z ^ j * (x * z⁻¹ * x⁻¹) * (z ^ j)⁻¹ := by group
          _ = z * z ^ j * z * (z ^ j)⁻¹ := by rw [hxz']
          _ = z * (z ^ j * z) * (z ^ j)⁻¹ := by group
          _ = z * (z * z ^ j) * (z ^ j)⁻¹ := by rw [hcz]
          _ = z ^ 2 := by group
      rw [e2] at h2
      obtain ⟨k', hk'⟩ := exists_pow_two_pow_eq_one hO2 h2
      have hodd2 : Odd (orderOf (z ^ 2)) := Odd.of_dvd_nat d.zodd (orderOf_pow_dvd 2)
      have hz2 : z ^ 2 = 1 := eq_one_of_odd_orderOf_of_pow_two_pow hodd2 hk'
      have hdvd : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
      have h1' : orderOf z = 1 := by
        rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
        · exact h
        · have hzodd := d.zodd
          rw [h] at hzodd
          exact absurd hzodd (by decide)
      exact d.z1 (orderOf_eq_one_iff.1 h1')
  rw [hs1, one_mul]
  exact hp

theorem inf_centralizer_dpP_le (d : DihedralPair H T V U x z) :
    dpI V z ⊓ Subgroup.centralizer (dpP H V U z : Set G) ≤ dpP H V U z := by
  intro g hg
  have hC : g ∈ dpI V z ⊓ Subgroup.centralizer (pCoreOf 2 (dpI V z) : Set G) :=
    ⟨hg.1, Subgroup.mem_centralizer_iff.2 fun q hq =>
      Subgroup.mem_centralizer_iff.1 hg.2 q (d.pCoreOf_dpI_le hq)⟩
  exact d.pCoreOf_dpI_le (d.charTwo_dpI hC)

theorem eq_three_of_prime_dvd (d : DihedralPair H T V U x z) (hV16 : Nat.card V = 2 ^ 4)
    (hq : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI d.elem H)) {p : ℕ} (hp : p.Prime)
    (hpd : p ∣ orderOf z) : p = 3 := by
  obtain ⟨m, hm⟩ := hpd
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h, mul_zero] at hm
      exact absurd hm (orderOf_pos z).ne'
    · exact h
  have hord : orderOf (z ^ m) = p := by
    rw [orderOf_pow' z hm0.ne', hm, Nat.gcd_mul_left_left]
    exact Nat.mul_div_cancel _ hm0
  have hz1 : z ^ m ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hord
    exact hp.one_lt.ne' hord.symm
  have h3 := (d.pow m hz1).stage_one (hord ▸ hp) hV16 hq
  rw [← hord]
  exact h3.1

theorem orderOf_eq_three_of_odd (d : DihedralPair H T V U x z) (hV16 : Nat.card V = 2 ^ 4)
    (hq : (((3 : ℚ) / 2 : ℚ) : WithTop ℚ) ≤ qhatOf (autI d.elem H)) : orderOf z = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm0 : orderOf z ≠ 0 := (orderOf_pos z).ne'
  have hpow : orderOf z = 3 ^ (orderOf z).primeFactorsList.length :=
    Nat.eq_prime_pow_of_unique_prime_dvd hm0 fun hp hpd => d.eq_three_of_prime_dvd hV16 hq hp hpd
  set k := (orderOf z).primeFactorsList.length with hk
  have hk0 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hpow
    exact d.z1 (orderOf_eq_one_iff.1 hpow)
  by_cases hk1 : k = 1
  · rw [hpow, hk1, pow_one]
  exfalso
  have hk2 : 2 ≤ k := by omega
  obtain ⟨-, hZ2, hCA⟩ := d.counts hV16 (d.cube_le_sq hq)
  have hPext := d.isExtraspecialPlus hV16 hZ2 hCA
  set P := dpP H V U z with hP
  have hPcard : Nat.card P = 2 ^ 5 := by rw [hPext.2.1]
  have hzN : z ∈ Subgroup.normalizer (P : Set G) := d.IP d.zI
  set c : Subgroup.normalizer (P : Set G) := ⟨z, hzN⟩ with hcdef
  have hc : orderOf c = 3 ^ ((k - 1) + 1) := by
    rw [hcdef, Subgroup.orderOf_mk, hpow, Nat.sub_add_cancel (by omega)]
  have hcoe : ((c ^ 3 ^ (k - 1) : Subgroup.normalizer (P : Set G)) : G) = z ^ 3 ^ (k - 1) := by
    rw [Subgroup.coe_pow]
  have hz0ord : orderOf (z ^ 3 ^ (k - 1)) = 3 := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ (by norm_num)) (hpow ▸ pow_dvd_pow 3 (by omega)), hpow]
    have h3k : 3 ^ k = 3 * 3 ^ (k - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [h3k, Nat.mul_div_cancel _ (pow_pos (by norm_num) _)]
  have hz0I : z ^ 3 ^ (k - 1) ∈ dpI V z := (dpI V z).pow_mem d.zI _
  have hne : P.normalizerMonoidHom (c ^ 3 ^ (k - 1)) ≠ 1 := by
    intro h1
    have hC : z ^ 3 ^ (k - 1) ∈ Subgroup.centralizer (P : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have h2 := congrArg Subtype.val (DFunLike.congr_fun h1 ⟨p, hp⟩)
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hcoe, MulAut.one_apply] at h2
      calc p * z ^ 3 ^ (k - 1) = (z ^ 3 ^ (k - 1) * p * (z ^ 3 ^ (k - 1))⁻¹) * z ^ 3 ^ (k - 1) := by
            rw [h2]
        _ = z ^ 3 ^ (k - 1) * p := by group
    have hmemP := d.inf_centralizer_dpP_le ⟨hz0I, hC⟩
    obtain ⟨n, hn⟩ := exists_pow_two_pow_eq_one (d.T2.to_le (d.PR.trans d.RT)) hmemP
    have h1' := eq_one_of_odd_orderOf_of_pow_two_pow
      (by rw [hz0ord]; decide : Odd (orderOf (z ^ 3 ^ (k - 1)))) hn
    rw [h1', orderOf_one] at hz0ord
    exact absurd hz0ord (by norm_num)
  have hZP : dpZ V z ≤ P := d.ZU.trans le_sup_left
  have hfix : ∀ ζ ∈ (dpZ V z).subgroupOf P, P.normalizerMonoidHom (c ^ 3 ^ (k - 1)) ζ = ζ := by
    intro ζ hζ
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, hcoe]
    have hζc := d.ZC _ (Subgroup.mem_subgroupOf.1 hζ) _ hz0I
    rw [hζc, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨m', hm'0, hm'Z, hm'dvd⟩ := Ch3E213M.exists_two_pow_of_orderOf P.normalizerMonoidHom
    (d := 5) hPcard (by norm_num : Nat.Prime 3) (by norm_num) hc hne _ hfix
  have hZcard : Nat.card ((dpZ V z).subgroupOf P) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZP).toEquiv, hZ2]
  rw [hZcard] at hm'Z
  have h9 : 9 ∣ 2 ^ m' - 1 := by
    refine (Dvd.dvd.trans ?_ hm'dvd)
    rw [Nat.sub_add_cancel (by omega)]
    exact (pow_dvd_pow 3 hk2 : 3 ^ 2 ∣ 3 ^ k)
  have h6 := Ch3E213M.six_dvd_of_nine_dvd_two_pow_sub_one h9
  have hm6 : 6 ≤ m' := Nat.le_of_dvd hm'0 h6
  have : 2 ^ 6 * 2 ≤ 2 ^ m' * 2 := Nat.mul_le_mul_right 2 (Nat.pow_le_pow_right (by norm_num) hm6)
  have h5 : 2 ^ 6 * 2 ≤ 2 ^ 5 := this.trans hm'Z
  norm_num at h5

end DihedralPair

end E2

end CFSG.Quasithin
