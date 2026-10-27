module

public import CFSG.Quasithin.H13.GoldschmidtU43ECent
public import CFSG.GroupTheory.BurnsideNormalComplement

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable {z : G} (S : JWSetup z)
include S

@[expose] def Tg : Subgroup G := S.R.map (Hz z).subtype

@[expose] def Cg : Subgroup G := Subgroup.centralizer (S.Tg : Set G)

theorem mem_Tg {x : G} : x ∈ S.Tg ↔ ∃ r ∈ S.R, ((r : ↥(Hz z)) : G) = x := by
  simp [Tg, Subgroup.mem_map]

theorem coe_mem_Tg {r : ↥(Hz z)} (hr : r ∈ S.R) : (r : G) ∈ S.Tg := ⟨r, hr, rfl⟩

theorem card_Tg : Nat.card S.Tg = 9 := by
  rw [Tg, Subgroup.card_map_of_injective (Hz z).subtype_injective]
  exact S.hR.card

theorem Tg_le_Hz : S.Tg ≤ Hz z := by
  rintro _ ⟨r, -, rfl⟩
  exact r.2

theorem mem_Cg {x : G} : x ∈ S.Cg ↔ ∀ t ∈ S.Tg, t * x = x * t := Subgroup.mem_centralizer_iff

theorem z_sq : z * z = 1 := S.hyp.sq_z

theorem z_mem_Cg : z ∈ S.Cg := by
  rw [S.mem_Cg]
  intro t ht
  exact z_comm_H (⟨t, S.Tg_le_Hz ht⟩ : ↥(Hz z))

variable [Finite G]

theorem pow_three_Tg {x : G} (hx : x ∈ S.Tg) : x ^ 3 = 1 := by
  obtain ⟨r, hr, rfl⟩ := (S.mem_Tg).1 hx
  have := S.hR.pow_three hr
  exact congrArg Subtype.val this

theorem comm_Tg {x y : G} (hx : x ∈ S.Tg) (hy : y ∈ S.Tg) : x * y = y * x := by
  obtain ⟨r, hr, rfl⟩ := (S.mem_Tg).1 hx
  obtain ⟨r', hr', rfl⟩ := (S.mem_Tg).1 hy
  exact congrArg Subtype.val (S.hR.comm hr hr')

theorem Tg_le_Cg : S.Tg ≤ S.Cg := fun _ hx => (S.mem_Cg).2 fun _ ht => S.comm_Tg ht hx

theorem cent_Hz {x : G} (hxC : x ∈ S.Cg) (hxH : x ∈ Hz z) :
    ∃ r ∈ S.Tg, x = r ∨ x = z * r := by
  obtain ⟨r, hr, h⟩ := S.centralizer_R (x := ⟨x, hxH⟩) (fun r hr => by
    apply Subtype.ext
    exact ((S.mem_Cg).1 hxC r (S.coe_mem_Tg hr)).symm)
  refine ⟨r, S.coe_mem_Tg hr, ?_⟩
  rcases h with h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (congrArg Subtype.val h)

theorem r_eq_one_of_mem {P : Subgroup G} (h2 : IsPGroup 2 P) {r x : G} (hr : r ∈ S.Tg)
    (hx : x ∈ P) (hxr : x = r ∨ x = z * r) : r = 1 := by
  have hzr : z * r = r * z := (z_comm_H (⟨r, S.Tg_le_Hz hr⟩ : ↥(Hz z))).symm
  have hr3 : r ^ 3 = 1 := S.pow_three_Tg hr
  have hrx : r ∈ P := by
    rcases hxr with rfl | rfl
    · exact hx
    · have h4 : (z * r) ^ 4 = r := by
        have e : (z * r) ^ 4 = z ^ 4 * r ^ 4 := (Commute.mul_pow (hzr) 4)
        have hz4 : z ^ 4 = 1 := by
          calc z ^ 4 = (z ^ 2) ^ 2 := by rw [← pow_mul]
            _ = 1 := by rw [pow_two z, S.z_sq]; simp
        have hr4 : r ^ 4 = r := by
          have : r ^ 4 = r ^ 3 * r := by rw [← pow_succ]
          rw [this, hr3, one_mul]
        rw [e, hz4, hr4, one_mul]
      rw [← h4]
      exact pow_mem hx 4
  obtain ⟨n, hn⟩ := h2 ⟨r, hrx⟩
  have h3 : (⟨r, hrx⟩ : P) ^ 3 = 1 := Subtype.ext hr3
  have hord : orderOf (⟨r, hrx⟩ : P) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hord2 : orderOf (⟨r, hrx⟩ : P) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn
  have hgcd : orderOf (⟨r, hrx⟩ : P) ∣ Nat.gcd 3 (2 ^ n) := Nat.dvd_gcd hord hord2
  have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right n (by norm_num)
  rw [hcop] at hgcd
  have h1 : orderOf (⟨r, hrx⟩ : P) = 1 := Nat.dvd_one.mp hgcd
  have := orderOf_eq_one_iff.mp h1
  exact congrArg Subtype.val this

theorem two_group_le {P : Subgroup G} (hP : P ≤ S.Cg) (h2 : IsPGroup 2 P) (hz : z ∈ P) :
    P ≤ Subgroup.zpowers z := by
  have hCz : ∀ x ∈ P, x * z = z * x → x ∈ Subgroup.zpowers z := by
    intro x hx hxz
    have hxH : x ∈ Hz z := Subgroup.mem_centralizer_singleton_iff.mpr hxz
    obtain ⟨r, hr, hxr⟩ := S.cent_Hz (hP hx) hxH
    have hr1 : r = 1 := S.r_eq_one_of_mem h2 hr hx hxr
    rcases hxr with h | h
    · rw [h, hr1]; exact one_mem _
    · rw [h, hr1, mul_one]; exact Subgroup.mem_zpowers z
  have hnt : Nontrivial P := ⟨⟨⟨z, hz⟩, 1, fun h => S.hyp.z_ne_one (congrArg Subtype.val h)⟩⟩
  have hnc : Nontrivial ↥(Subgroup.center ↥P) := h2.center_nontrivial
  obtain ⟨c, hc1⟩ := exists_ne (1 : ↥(Subgroup.center ↥P))
  have hcz : (c : P) * ⟨z, hz⟩ = ⟨z, hz⟩ * (c : P) :=
    (Subgroup.mem_center_iff.mp c.2 ⟨z, hz⟩).symm
  have hcmem : ((c : P) : G) ∈ Subgroup.zpowers z :=
    hCz _ (c : P).2 (by simpa using congrArg Subtype.val hcz)
  have hcz' : ((c : P) : G) = z := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcmem
    have hz2 : z ^ (2 : ℤ) = 1 := by
      rw [zpow_ofNat, pow_two]
      exact S.z_sq
    have hcases : k % 2 = 0 ∨ k % 2 = 1 := by omega
    have e : z ^ k = z ^ (k % 2) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, hz2, one_zpow, mul_one]
    rcases hcases with h0 | h1
    · exfalso
      apply hc1
      apply Subtype.ext
      apply Subtype.ext
      rw [← hk, e, h0]
      simp
    · rw [← hk, e, h1]
      simp
  have hzC : ∀ x ∈ P, x * z = z * x := by
    intro x hx
    have hcc : (c : P) ∈ Subgroup.center P := c.2
    have := Subgroup.mem_center_iff.mp hcc ⟨x, hx⟩
    have e : ((c : P) : G) * x = x * ((c : P) : G) := congrArg Subtype.val this.symm
    rw [hcz'] at e
    exact e.symm
  intro x hx
  exact hCz x hx (hzC x hx)

end JWSetup

theorem eq_of_card_two {Q : Type} [Group Q] (h : Nat.card Q = 2) {a b : Q} (ha : a ≠ 1)
    (hb : b ≠ 1) : a = b := by
  obtain ⟨x, y, hxy, hs⟩ := Nat.card_eq_two_iff.mp h
  have h1 : (1 : Q) ∈ ({x, y} : Set Q) := hs ▸ Set.mem_univ _
  have h2 : a ∈ ({x, y} : Set Q) := hs ▸ Set.mem_univ _
  have h3 : b ∈ ({x, y} : Set Q) := hs ▸ Set.mem_univ _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1 h2 h3
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    first | exact h2.trans h3.symm | (exfalso; simp_all)

theorem mem_zpowers_involution {K : Type} [Group K] {a : K} (h2 : a * a = 1) {x : K}
    (hx : x ∈ Subgroup.zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have ha2 : a ^ (2 : ℤ) = 1 := by
    rw [zpow_ofNat, pow_two]
    exact h2
  have e : a ^ k = a ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul, ha2, one_zpow, mul_one]
  rcases (by omega : k % 2 = 0 ∨ k % 2 = 1) with h0 | h1
  · left
    rw [e, h0]
    simp
  · right
    rw [e, h1]
    simp

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z)
include S

theorem exists_Mg : ∃ M : Subgroup G, M ≤ S.Cg ∧ (∀ x : G, x ∈ M ↔ x ∈ S.Cg ∧ Odd (orderOf x)) ∧
    Odd (Nat.card M) ∧ ∀ x ∈ S.Cg, x ∈ M ∨ z * x ∈ M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := S.Cg with hC
  let zC : ↥C := ⟨z, S.z_mem_Cg⟩
  have hz2 : zC * zC = 1 := Subtype.ext S.z_sq
  have hz1 : zC ≠ 1 := fun h => S.hyp.z_ne_one (congrArg Subtype.val h)
  have hord : orderOf zC = 2 := by
    apply orderOf_eq_prime
    · rwa [pow_two]
    · exact hz1
  have hP2 : IsPGroup 2 (Subgroup.zpowers zC) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hord]
    norm_num
  obtain ⟨P, hP⟩ := hP2.exists_le_sylow
  have hPeq : (P : Subgroup ↥C) = Subgroup.zpowers zC := by
    refine le_antisymm (fun x hx => ?_) hP
    have h2 : IsPGroup 2 ((P : Subgroup ↥C).map C.subtype) := P.isPGroup'.map _
    have hle : (P : Subgroup ↥C).map C.subtype ≤ S.Cg := by
      rintro _ ⟨k, -, rfl⟩
      exact k.2
    have hzP : z ∈ (P : Subgroup ↥C).map C.subtype := ⟨zC, hP (Subgroup.mem_zpowers zC), rfl⟩
    have hmem := S.two_group_le hle h2 hzP ⟨x, hx, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk)⟩
  have hNC : Subgroup.normalizer (P : Set ↥C) ≤ Subgroup.centralizer (P : Set ↥C) := by
    intro x hx
    have hzP : zC ∈ (P : Subgroup ↥C) := hP (Subgroup.mem_zpowers zC)
    have h1 : x * zC * x⁻¹ ∈ (P : Subgroup ↥C) := (Subgroup.mem_normalizer_iff.mp hx zC).mp hzP
    rw [hPeq] at h1
    have hcomm : x * zC = zC * x := by
      rcases mem_zpowers_involution hz2 h1 with h | h
      · exfalso
        apply hz1
        have : zC = x⁻¹ * (x * zC * x⁻¹) * x := by group
        rw [this, h]
        group
      · calc x * zC = x * zC * x⁻¹ * x := by group
          _ = zC * x := by rw [h]
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hh' : h ∈ (P : Subgroup ↥C) := hh
    rw [hPeq] at hh'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh'
    exact (Commute.zpow_left (show Commute zC x from hcomm.symm) k).eq
  obtain ⟨K, hKn, hKodd, hKidx, -⟩ := CFSG.GroupTheory.burnside_normal_complement P hNC
  have hPcard : Nat.card (P : Subgroup ↥C) = 2 := by
    rw [hPeq, Nat.card_zpowers, hord]
  have hKodd' : Odd (Nat.card K) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hKodd)
  have hQ : Nat.card (↥C ⧸ K) = 2 := by
    rw [← Subgroup.index_eq_card, hKidx, hPcard]
  refine ⟨K.map C.subtype, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    exact k.2
  · intro x
    constructor
    · intro hx
      refine ⟨by obtain ⟨k, -, rfl⟩ := hx; exact k.2, ?_⟩
      have hcard : Odd (Nat.card (K.map C.subtype)) := by
        rw [Subgroup.card_map_of_injective C.subtype_injective]
        exact hKodd'
      have h1 := orderOf_dvd_natCard (⟨x, hx⟩ : ↥(K.map C.subtype))
      rw [Subgroup.orderOf_mk] at h1
      exact Odd.of_dvd_nat hcard h1
    · rintro ⟨hxC, hxodd⟩
      have h1 := orderOf_dvd_natCard (QuotientGroup.mk (⟨x, hxC⟩ : ↥C) : ↥C ⧸ K)
      have h2 : orderOf (QuotientGroup.mk (⟨x, hxC⟩ : ↥C) : ↥C ⧸ K) ∣ orderOf (⟨x, hxC⟩ : ↥C) :=
        orderOf_dvd_of_pow_eq_one (by
          rw [← QuotientGroup.mk_pow, pow_orderOf_eq_one, QuotientGroup.mk_one])
      rw [Subgroup.orderOf_mk] at h2
      have h3 : orderOf (QuotientGroup.mk (⟨x, hxC⟩ : ↥C) : ↥C ⧸ K) = 1 := by
        have h5 := Nat.dvd_gcd h2 (hQ ▸ h1)
        rw [Nat.Coprime.gcd_eq_one hxodd.coprime_two_right] at h5
        exact Nat.dvd_one.mp h5
      have h4 := orderOf_eq_one_iff.mp h3
      rw [QuotientGroup.eq_one_iff] at h4
      exact ⟨⟨x, hxC⟩, h4, rfl⟩
  · rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact hKodd'
  · intro x hx
    by_cases hxK : (⟨x, hx⟩ : ↥C) ∈ K
    · exact Or.inl ⟨⟨x, hx⟩, hxK, rfl⟩
    · right
      have hzK : zC ∉ K := by
        intro h
        have h1 := orderOf_dvd_natCard (⟨zC, h⟩ : ↥K)
        rw [Subgroup.orderOf_mk, hord] at h1
        exact absurd (Odd.of_dvd_nat hKodd' h1) (by decide)
      have e : (QuotientGroup.mk zC : ↥C ⧸ K) = QuotientGroup.mk ⟨x, hx⟩ :=
        eq_of_card_two hQ (by rwa [Ne, QuotientGroup.eq_one_iff])
          (by rwa [Ne, QuotientGroup.eq_one_iff])
      rw [QuotientGroup.eq] at e
      refine ⟨zC⁻¹ * ⟨x, hx⟩, e, ?_⟩
      show (z⁻¹ * x : G) = z * x
      rw [inv_eq_of_mul_eq_one_right S.z_sq]

end JWSetup

end CFSG.Quasithin.H13.U43
