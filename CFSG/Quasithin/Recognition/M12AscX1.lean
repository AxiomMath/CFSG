module

public import CFSG.Quasithin.Recognition.M12AscClasses
public import CFSG.Quasithin.Recognition.M12AscP2G
public import CFSG.Quasithin.Recognition.M12AscX1Abs
public import CFSG.GH74.M12.HypGroup

public section

namespace CFSG.Quasithin

open Subgroup CFSG.GH74.M12.Hyp

variable {G : Type*} [Group G] {z : G}

open CFSG.GH74.M12 (Asc03Hyp)

theorem conj_comm_of_inverts {x u p : G} (hu2 : u * u = 1) (hux : u * x * u = x⁻¹)
    (hp : p * x = x * p) : (u * p * u⁻¹) * x = x * (u * p * u⁻¹) := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hpx : Commute p x⁻¹ := Commute.inv_right (show Commute p x from hp)
  have hux' : u * x⁻¹ = x * u := by
    calc u * x⁻¹ = u * (u * x * u) := by rw [hux]
      _ = (u * u) * x * u := by group
      _ = x * u := by rw [hu2, one_mul]
  calc (u * p * u⁻¹) * x = u * p * (u⁻¹ * x * u) * u⁻¹ := by group
    _ = u * p * x⁻¹ * u⁻¹ := by rw [show u⁻¹ * x * u = x⁻¹ by rw [hui]; exact hux]
    _ = u * (p * x⁻¹) * u⁻¹ := by group
    _ = u * (x⁻¹ * p) * u⁻¹ := by rw [show p * x⁻¹ = x⁻¹ * p from hpx]
    _ = (u * x⁻¹) * p * u⁻¹ := by group
    _ = x * (u * p * u⁻¹) := by rw [hux']; group

namespace AscModel

variable (m : AscModel z)

include m

theorem ψ_mX_mem : m.ψ mX ∈ ascH z := m.ψ_mem mX

theorem tb_ψ_mX : m.tb (m.ψ mX) = xTab := m.tb_ψ mX

theorem tb_ψ_mU : m.tb (m.ψ mU) = uTab := m.tb_ψ mU

theorem x_cube : m.ψ mX * m.ψ mX * m.ψ mX = 1 := by
  rw [← map_mul, ← map_mul, mX_cube, map_one]

theorem x_ne : m.ψ mX ≠ 1 := fun h => mX_ne (m.ψ_injective (by rw [h, map_one]))

theorem x_orderOf : orderOf (m.ψ mX) = 3 := by
  apply orderOf_eq_prime
  · have := m.x_cube
    calc m.ψ mX ^ 3 = m.ψ mX * m.ψ mX * m.ψ mX := by rw [pow_succ, pow_two]
      _ = 1 := this
  · exact m.x_ne

theorem CHx [Finite G] {h : G} (hh : h ∈ ascH z)
    (hc : h * m.ψ mX = m.ψ mX * h) :
    ∃ k < 6, m.tb h = tpow (tmul xTab zTab) k := by
  have h1 := CH_x (m.tb h) (m.tb_mem hh) (by
    rw [← m.tb_ψ_mX]
    exact (m.comm_iff hh m.ψ_mX_mem).1 hc)
  exact h1

theorem two_sub_cent [Finite G] (hyp : Asc03Hyp G z) {R : Subgroup G}
    (hRC : R ≤ Subgroup.centralizer ({m.ψ mX} : Set G)) (hRp : IsPGroup 2 R) (hzR : z ∈ R) :
    R = zpowers z := by
  classical
  have hzle : zpowers z ≤ R := (Subgroup.zpowers_le).2 hzR
  by_contra hne
  have hlt' : (zpowers z).subgroupOf R < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    refine le_antisymm (fun g hg => ?_) hzle
    have : (⟨g, hg⟩ : ↥R) ∈ (zpowers z).subgroupOf R := by rw [htop]; trivial
    exact Subgroup.mem_subgroupOf.1 this
  have hRnil : Group.IsNilpotent ↥R := hRp.isNilpotent
  obtain ⟨⟨n, hnR⟩, hnN, hnT⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt')
  have hnZ : n ∉ zpowers z := fun h => hnT (Subgroup.mem_subgroupOf.2 h)
  have hzn : n * z * n⁻¹ ∈ zpowers z := by
    have h1 : (⟨z, hzR⟩ : ↥R) ∈ (zpowers z).subgroupOf R :=
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers z)
    exact Subgroup.mem_subgroupOf.1 ((Subgroup.mem_normalizer_iff.1 hnN _).1 h1)
  have hnzc : n * z * n⁻¹ = z := by
    rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_two hyp.orderTwo hzn with h | h
    · exfalso
      apply asc_z_ne_one hyp
      calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
        _ = 1 := by rw [h]; group
    · exact h
  have hnH : n ∈ ascH z := by
    rw [ascH, Subgroup.mem_centralizer_singleton_iff]
    calc n * z = (n * z * n⁻¹) * n := by group
      _ = z * n := by rw [hnzc]
  have hnC : n * m.ψ mX = m.ψ mX * n := Subgroup.mem_centralizer_singleton_iff.1 (hRC hnR)
  obtain ⟨k, hk6, hnk⟩ := m.CHx hnH hnC
  have hn6 : n ^ 6 = 1 := by
    apply m.tb_inj (Subgroup.pow_mem _ hnH 6) (one_mem _)
    rw [m.tb_pow hnH, m.tb_one, hnk]
    exact tpow_six_w k hk6
  obtain ⟨e, he⟩ := hRp ⟨n, hnR⟩
  have hne : n ^ (2 ^ e) = 1 := by
    have := congrArg Subtype.val he
    simpa using this
  have hn2 : n * n = 1 := by
    have hdvd6 : orderOf n ∣ 6 := orderOf_dvd_of_pow_eq_one hn6
    have hdvd2 : orderOf n ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one hne
    obtain ⟨a, ha, hoa⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd2
    have ha1 : a ≤ 1 := by
      by_contra hcon
      push Not at hcon
      have h4 : 2 ^ 2 ∣ 2 ^ a := pow_dvd_pow 2 hcon
      rw [← hoa] at h4
      have := h4.trans hdvd6
      omega
    have hord : orderOf n ∣ 2 := by
      rw [hoa]
      calc 2 ^ a ∣ 2 ^ 1 := pow_dvd_pow 2 ha1
        _ = 2 := by norm_num
    have := orderOf_dvd_iff_pow_eq_one.1 hord
    rwa [pow_two] at this
  have htb : tmul (m.tb n) (m.tb n) = tid := by
    rw [← m.tb_mul hnH hnH, hn2, m.tb_one]
  rcases sq_split_w k hk6 (by rw [← hnk]; exact htb) with h | h
  · apply hnZ
    have : n = 1 := (m.eq_one_iff hnH).2 (by rw [hnk]; exact h)
    rw [this]
    exact one_mem _
  · apply hnZ
    have : n = z := (m.eq_z_iff hnH).2 (by rw [hnk]; exact h)
    rw [this]
    exact Subgroup.mem_zpowers z

theorem exists_P [Finite G] (hyp : Asc03Hyp G z) (h27 : 27 ∣ Nat.card G) :
    ∃ P : Subgroup G, P ≤ Subgroup.centralizer ({m.ψ mX} : Set G) ∧
      (∀ c ∈ Subgroup.centralizer ({m.ψ mX} : Set G), ∀ w ∈ P, c * w * c⁻¹ ∈ P) ∧ z ∉ P ∧
      (∀ a ∈ Subgroup.centralizer ({m.ψ mX} : Set G), a ∈ P ∨ a * z ∈ P) ∧
      (∀ c ∈ Subgroup.centralizer ({m.ψ mX} : Set G), Odd (orderOf c) → c ∈ P) ∧
      Odd (Nat.card P) ∧ m.ψ mX ∈ P ∧ 9 ∣ Nat.card P := by
  classical
  have hz2 : z * z = 1 := asc_z_sq hyp
  have hxzc : z * m.ψ mX = m.ψ mX * z := (m.ψ_comm_z mX).symm
  have hzC : z ∈ Subgroup.centralizer ({m.ψ mX} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hxzc
  have hxC : m.ψ mX ∈ Subgroup.centralizer ({m.ψ mX} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hSp : IsPGroup 2 (zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyp.orderTwo]; norm_num)
  have hmax : ∀ R : Subgroup G, R ≤ Subgroup.centralizer ({m.ψ mX} : Set G) → IsPGroup 2 R →
      zpowers z ≤ R → R = zpowers z := fun R hRC hRp hle =>
    m.two_sub_cent hyp hRC hRp (hle (Subgroup.mem_zpowers z))
  have hSC : zpowers z ≤ Subgroup.centralizer ({m.ψ mX} : Set G) :=
    (Subgroup.zpowers_le).2 hzC
  have hidx : (⊥ : Subgroup G).relIndex (zpowers z) = 2 :=
    relIndex_eq_two_of_card bot_le (by rw [Nat.card_zpowers, hyp.orderTwo, Subgroup.card_bot])
  have hQu : ∀ a ∈ Subgroup.centralizer ({m.ψ mX} : Set G), a⁻¹ * z * a ∉ (⊥ : Subgroup G) := by
    intro a _ h
    rw [Subgroup.mem_bot] at h
    apply asc_z_ne_one hyp
    calc z = a * (a⁻¹ * z * a) * a⁻¹ := by group
      _ = 1 := by rw [h]; group
  obtain ⟨P, hPC, hPn, hcard, hzP, htr, -⟩ :=
    thompson_transfer_index_two_sub _ (zpowers z) ⊥ hSC hSp hmax hidx hz2 (Subgroup.mem_zpowers z)
      hQu
  have hsq : ∀ a ∈ Subgroup.centralizer ({m.ψ mX} : Set G), a * a ∈ P := fun a ha =>
    sq_mem_of_transversal hPn hz2 hzC htr ha
  have hodd : ∀ c ∈ Subgroup.centralizer ({m.ψ mX} : Set G), Odd (orderOf c) → c ∈ P := by
    intro c hc ⟨t, ht⟩
    have h1 : c ^ (2 * t + 1) = 1 := by rw [← ht]; exact pow_orderOf_eq_one c
    have h2 : c ^ (2 * (t + 1)) = c := by
      rw [show 2 * (t + 1) = (2 * t + 1) + 1 by ring, pow_succ, h1, one_mul]
    have h3 : c = (c * c) ^ (t + 1) := by
      rw [← pow_two, ← pow_mul, h2]
    rw [h3]
    exact Subgroup.pow_mem P (hsq c hc) (t + 1)
  obtain ⟨m', hm'odd, hCm⟩ := exists_odd_card_of_maximal _ (zpowers z) hSC hSp hmax
  rw [Nat.card_zpowers, hyp.orderTwo] at hCm
  have hPodd : Odd (Nat.card P) := by
    have : Nat.card P = m' := by omega
    rw [this]
    exact hm'odd
  obtain ⟨B, hBC, hBp, hB9⟩ := exists_three_group_centralizing m.x_orderOf h27
  have hBP : B ≤ P := by
    intro b hb
    obtain ⟨k, hk⟩ := hBp ⟨b, hb⟩
    have hbk : b ^ (3 ^ k) = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hodd3 : Odd (orderOf b) :=
      Odd.of_dvd_nat (Odd.pow (by decide : Odd 3)) (orderOf_dvd_of_pow_eq_one hbk)
    exact hodd b (hBC hb) hodd3
  refine ⟨P, hPC, hPn, hzP, htr, hodd, hPodd, ?_, hB9.trans (Subgroup.card_dvd_of_le hBP)⟩
  exact hodd _ hxC (by rw [m.x_orderOf]; decide)

theorem exists_x1 [Finite G] (hyp : Asc03Hyp G z) (h27 : 27 ∣ Nat.card G) :
    ∃ u' x1 : G, (u' = m.ψ mU ∨ u' = m.ψ (mU * mZ)) ∧ orderOf x1 = 3 ∧
      x1 * m.ψ mX = m.ψ mX * x1 ∧ x1 * u' = u' * x1 ∧ z * x1 * z⁻¹ = x1⁻¹ ∧
      x1 ∉ zpowers (m.ψ mX) := by
  classical
  obtain ⟨P, hPC, hPn, hzP, htr, hodd, hPodd, hxP, h9⟩ := m.exists_P hyp h27
  have hz2 : z * z = 1 := asc_z_sq hyp
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hxzc : z * m.ψ mX = m.ψ mX * z := (m.ψ_comm_z mX).symm
  have hzC : z ∈ Subgroup.centralizer ({m.ψ mX} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 hxzc
  have hPx : ∀ p ∈ P, p * m.ψ mX = m.ψ mX * p := fun p hp =>
    Subgroup.mem_centralizer_singleton_iff.1 (hPC hp)
  have hu2 : m.ψ mU * m.ψ mU = 1 := by rw [← map_mul, mU_sq, map_one]
  have hux : m.ψ mU * m.ψ mX * m.ψ mU = (m.ψ mX)⁻¹ := by
    rw [← map_mul, ← map_mul, mU_mX, map_inv]
  have hzu : z * m.ψ mU = m.ψ mU * z := (m.ψ_comm_z mU).symm
  have hPoddord : ∀ p ∈ P, Odd (orderOf p) := fun p hp => by
    have h1 : orderOf (⟨p, hp⟩ : ↥P) ∣ Nat.card ↥P := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at h1
    exact Odd.of_dvd_nat hPodd h1
  have huP : ∀ p ∈ P, m.ψ mU * p * (m.ψ mU)⁻¹ ∈ P := by
    intro p hp
    have hcomm := conj_comm_of_inverts hu2 hux (hPx p hp)
    have hC : m.ψ mU * p * (m.ψ mU)⁻¹ ∈ Subgroup.centralizer ({m.ψ mX} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 hcomm
    apply hodd _ hC
    have := (MulAut.conj (m.ψ mU)).orderOf_eq p
    rw [MulAut.conj_apply] at this
    rw [this]
    exact hPoddord p hp
  have hzfix : ∀ p ∈ P, z * p * z⁻¹ = p → p ∈ zpowers (m.ψ mX) := by
    intro p hp hfix
    have hpz : p * z = z * p := by
      calc p * z = (z * p * z⁻¹) * z := by rw [hfix]
        _ = z * p := by group
    have hpH : p ∈ ascH z := Subgroup.mem_centralizer_singleton_iff.2 hpz
    obtain ⟨k, hk6, hpk⟩ := m.CHx hpH (hPx p hp)
    have hp6 : p ^ 6 = 1 := by
      apply m.tb_inj (Subgroup.pow_mem _ hpH 6) (one_mem _)
      rw [m.tb_pow hpH, m.tb_one, hpk]
      exact tpow_six_w k hk6
    have hp3 : p ^ 3 = 1 := by
      have hdvd6 : orderOf p ∣ 6 := orderOf_dvd_of_pow_eq_one hp6
      have hcop : Nat.Coprime (orderOf p) 2 := Nat.coprime_two_right.2 (hPoddord p hp)
      have h3 : orderOf p ∣ 3 := hcop.dvd_of_dvd_mul_right (by simpa using hdvd6)
      exact orderOf_dvd_iff_pow_eq_one.1 h3
    have hxH := m.ψ_mX_mem
    rcases cube_split_w k hk6 (by rw [← hpk, ← m.tb_pow hpH 3, hp3, m.tb_one]) with h | h | h
    · have : p = 1 := (m.eq_one_iff hpH).2 (by rw [hpk]; exact h)
      rw [this]
      exact one_mem _
    · have : p = m.ψ mX := m.tb_inj hpH hxH (by rw [hpk, h, m.tb_ψ_mX])
      rw [this]
      exact Subgroup.mem_zpowers _
    · have : p = m.ψ mX * m.ψ mX :=
        m.tb_inj hpH (mul_mem hxH hxH) (by rw [hpk, h, m.tb_mul hxH hxH, m.tb_ψ_mX])
      rw [this]
      exact mul_mem (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)
  have hzP' : ∀ p ∈ P, z * p * z⁻¹ ∈ P := fun p hp => hPn z hzC p hp
  obtain ⟨g, x1, hg, hx1P, hx1o, hx1X, hx1g, hx1z⟩ := exists_x1_abstract P m.x_orderOf hxP hPx h9
    hz2 hxzc hzP' hzfix hu2 hux hzu huP
  refine ⟨g, x1, ?_, hx1o, hPx x1 hx1P, hx1g, hx1z, hx1X⟩
  rcases hg with rfl | rfl
  · exact Or.inl rfl
  · right
    rw [map_mul, m.ψ_hz]

end AscModel

end CFSG.Quasithin
