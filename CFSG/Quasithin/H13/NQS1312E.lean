module

public import CFSG.Quasithin.Background.A318PC1
public import CFSG.Quasithin.EmptyFaithful.SBc13JRaMain
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Quasithin.Background.C2Nine

public section

namespace CFSG.Quasithin.H13.U3.NLine

open Subgroup CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem three_dvd_card_inf_centralizer {Y : Subgroup G} (hY : 3 ∣ Nat.card Y) {x : G}
    (hx : x ^ 3 = 1) (hxY : x ∈ normalizer (Y : Set G)) :
    3 ∣ Nat.card (Y ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := zpowers x with hP
  have hPN : P ≤ normalizer (Y : Set G) := zpowers_le.2 hxY
  have hPp : IsPGroup 3 P := by
    intro ⟨y, hy⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]
  let _ : MulDistribMulAction P Y :=
    MulDistribMulAction.compHom Y ((Y.normalizerMonoidHom).comp (inclusion hPN))
  have hcong := hPp.card_modEq_card_fixedPoints Y
  have h3fix : 3 ∣ Nat.card (FixedPoints.subgroup P Y) := by
    have h1 : Nat.card Y % 3 = 0 := Nat.mod_eq_zero_of_dvd hY
    have h2 : Nat.card (MulAction.fixedPoints P Y) % 3 = 0 := hcong ▸ h1
    exact Nat.dvd_of_mod_eq_zero h2
  let f : FixedPoints.subgroup P Y →* (Y ⊓ centralizer ({x} : Set G) : Subgroup G) :=
    { toFun := fun a => ⟨(a : Y), ⟨(a : Y).2, mem_centralizer_singleton_iff.2 (by
          have hfx := (FixedPoints.mem_subgroup P Y _).1 a.2 ⟨x, mem_zpowers x⟩
          have h2 := congrArg Subtype.val hfx
          change x * ((a : Y) : G) * x⁻¹ = ((a : Y) : G) at h2
          calc ((a : Y) : G) * x = x * ((a : Y) : G) * x⁻¹ * x := by rw [h2]
            _ = x * ((a : Y) : G) := by group)⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => ?_, fun c => ?_⟩
    · have h := congrArg (fun c : (Y ⊓ centralizer ({x} : Set G) : Subgroup G) => (c : G)) hab
      exact Subtype.ext (Subtype.ext h)
    · obtain ⟨c, hcY, hcx⟩ := c
      refine ⟨⟨⟨c, hcY⟩, (FixedPoints.mem_subgroup P Y _).2 fun ⟨p, hp⟩ => ?_⟩, rfl⟩
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hp
      have hc : x * c = c * x := (mem_centralizer_singleton_iff.1 hcx).symm
      apply Subtype.ext
      change x ^ m * c * (x ^ m)⁻¹ = c
      rw [(Commute.zpow_left hc m).eq]
      group
  rw [← Nat.card_congr (MulEquiv.ofBijective f hf).toEquiv]
  exact h3fix

theorem exists_orderOf_three_commute {Y : Subgroup G} (hY : 3 ∣ Nat.card Y) {x : G}
    (hx : x ^ 3 = 1) (hxY : x ∈ normalizer (Y : Set G)) :
    ∃ a ∈ Y, orderOf a = 3 ∧ x * a = a * x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc3⟩ :=
    exists_prime_orderOf_dvd_card' 3 (three_dvd_card_inf_centralizer hY hx hxY)
  exact ⟨c, (Subgroup.mem_inf.1 c.2).1, (Subgroup.orderOf_coe c).trans hc3,
    (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 c.2).2).symm⟩

theorem exists_orderOf_three_commute_pair {Y : Subgroup G} (hY : 3 ∣ Nat.card Y) {x k : G}
    (hx : x ^ 3 = 1) (hk : k ^ 3 = 1) (hxk : x * k = k * x)
    (hxY : x ∈ normalizer (Y : Set G)) (hkY : k ∈ normalizer (Y : Set G)) :
    ∃ a ∈ Y, orderOf a = 3 ∧ x * a = a * x ∧ k * a = a * k := by
  set C := Y ⊓ centralizer ({k} : Set G) with hC
  have hC3 : 3 ∣ Nat.card C := three_dvd_card_inf_centralizer hY hk hkY
  have hkx : x * k * x⁻¹ = k := by rw [hxk]; group
  have hkey : ∀ c : G, k * (x * c * x⁻¹) = x * c * x⁻¹ * k ↔ k * c = c * k := by
    intro c
    have e1 : k * (x * c * x⁻¹) = x * (k * c) * x⁻¹ := by
      conv_lhs => rw [← hkx]
      group
    have e2 : x * c * x⁻¹ * k = x * (c * k) * x⁻¹ := by
      conv_lhs => rw [← hkx]
      group
    rw [e1, e2]
    constructor
    · intro h
      have h' : x⁻¹ * (x * (k * c) * x⁻¹) * x = x⁻¹ * (x * (c * k) * x⁻¹) * x := by rw [h]
      rwa [show x⁻¹ * (x * (k * c) * x⁻¹) * x = k * c by group,
        show x⁻¹ * (x * (c * k) * x⁻¹) * x = c * k by group] at h'
    · intro h
      rw [h]
  have hkc : ∀ c : G, c ∈ centralizer ({k} : Set G) ↔ k * c = c * k := fun c => by
    rw [mem_centralizer_singleton_iff]
    exact eq_comm
  have hxC : x ∈ normalizer (C : Set G) := by
    rw [mem_normalizer_iff]
    intro c
    rw [hC, Subgroup.mem_inf, Subgroup.mem_inf, hkc, hkc, hkey, ← mem_normalizer_iff.1 hxY c]
  obtain ⟨a, ⟨haY, hak⟩, ha3, hxa⟩ := exists_orderOf_three_commute hC3 hx hxC
  exact ⟨a, haY, ha3, hxa, (mem_centralizer_singleton_iff.1 hak).symm⟩

theorem mem_of_commute_three {N H K : Subgroup G} (hN : CFSG.Open.pRank 3 (⊤ : Subgroup ↥N) ≤ 2)
    (hHN : H ≤ N) (hKH : K ≤ H) (hK3 : 3 ∣ Nat.card K) {x k : G} (hxN : x ∈ N) (hkN : k ∈ N)
    (hx : orderOf x = 3) (hk : orderOf k = 3) (hxk : x * k = k * x)
    (hxK : x ∈ normalizer (K : Set G)) (hkK : k ∈ normalizer (K : Set G)) (hkH : k ∈ H)
    (hxH : x ∉ H) : k ∈ K := by
  by_contra hkK'
  have hx3 : x ^ 3 = 1 := hx ▸ pow_orderOf_eq_one x
  have hk3 : k ^ 3 = 1 := hk ▸ pow_orderOf_eq_one k
  obtain ⟨a, haK, ha3, hxa, hka⟩ := exists_orderOf_three_commute_pair hK3 hx3 hk3 hxk hxK hkK
  have hk1 : k ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hk
    omega
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha3
    omega
  have haN : a ∈ N := hHN (hKH haK)
  refine A318P.false_of_centralized_pair (X := ↥N) (S := H.subgroupOf N) hN
    (x := ⟨x, hxN⟩) (a := ⟨k, hkN⟩) (b := ⟨a, haN⟩) (by rw [Subgroup.orderOf_mk]; exact hx)
    (by rw [Subgroup.mem_subgroupOf]; exact hxH) (by rw [Subgroup.mem_subgroupOf]; exact hkH)
    (by rw [Subgroup.mem_subgroupOf]; exact hKH haK) (Subtype.ext hk3)
    (Subtype.ext (ha3 ▸ pow_orderOf_eq_one a)) (Subtype.ext hka)
    (fun h => hk1 (congrArg Subtype.val h)) (fun h => ha1 (congrArg Subtype.val h))
    (fun h => hkK' (by
      have : a = k := congrArg Subtype.val h
      exact this ▸ haK))
    (fun h => hkK' (by
      have h2 : a = k ^ 2 := congrArg Subtype.val h
      have h4 : k = a ^ 2 := by
        rw [h2, ← pow_mul]
        calc k = k ^ 3 * k := by rw [hk3, one_mul]
          _ = k ^ (2 * 2) := by rw [← pow_succ]
      exact h4 ▸ K.pow_mem haK 2))
    (Subtype.ext hxk) (Subtype.ext hxa)

theorem le_normalizer_of_commute_three (hA3 : A3Orbits G) (h38 : A38ForSQTK) {N H K : Subgroup G}
    (hNs : IsSQTKIn N) (hHN : H ≤ N) (hNH : N ≤ normalizer (H : Set G)) (hK : K ∈ cComp N)
    (hKH : K ≤ H) (hK3 : 3 ∣ Nat.card K) {x k : G} (hxN : x ∈ N) (hkN : k ∈ N)
    (hx : orderOf x = 3) (hk : orderOf k = 3) (hxk : x * k = k * x) (hkH : k ∈ H)
    (hxH : x ∉ H) : k ∈ K ∧ N ≤ normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd 3 := by decide
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥N) ≤ 2 := hNs.1 3 Nat.prime_three (by norm_num)
  have hnorm : ∀ J ∈ cComp N, x ∈ normalizer (J : Set G) ∧ k ∈ normalizer (J : Set G) :=
    fun J hJ => ⟨SBc13.mem_normalizer_of_odd_of_sqtk h38 hNs hJ hxN (hx ▸ hodd),
      SBc13.mem_normalizer_of_odd_of_sqtk h38 hNs hJ hkN (hk ▸ hodd)⟩
  have hmem : ∀ J ∈ cComp N, J ≤ H → 3 ∣ Nat.card J → k ∈ J := fun J hJ hJH hJ3 =>
    mem_of_commute_three hrank hHN hJH hJ3 hxN hkN hx hk hxk (hnorm J hJ).1 (hnorm J hJ).2 hkH
      hxH
  have hkK := hmem K hK hKH hK3
  refine ⟨hkK, ?_⟩
  obtain ⟨T, hT⟩ := exists_isSylowTwoOf N
  obtain ⟨horb, hcase⟩ := hA3 N T K hNs hT hK
  rcases hcase with hTn | ⟨t, htT, htn, -, -, hint, -⟩
  ·
    intro n hn
    have h1 : K.map (MulAut.conj n).toMonoidHom ∈ conjSubgroupsBy N K := ⟨n, hn, rfl⟩
    rw [horb] at h1
    obtain ⟨s, hs, hsK⟩ := h1
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe, hsK]
    have := hTn s hs
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe] at this
    exact this
  ·
    exfalso
    have htN : t ∈ N := hT.1 htT
    have hKt : conjByElt t K ∈ cComp N := C2Nine.conjByElt_mem_cComp hK (Subgroup.le_normalizer htN)
    have hKtH : conjByElt t K ≤ H := by
      intro y hy
      rw [mem_conjByElt] at hy
      have h1 := hKH hy
      have h2 := (mem_normalizer_iff.1 (hNH htN) _).1 h1
      simpa [mul_assoc] using h2
    have hKt3 : 3 ∣ Nat.card (conjByElt t K) := by
      rw [conjByElt, Subgroup.card_map_of_injective (MulAut.conj t).injective]
      exact hK3
    have hkKt := hmem _ hKt hKtH hKt3
    have hkO : k ∈ pCoreOf 2 N := by
      rw [← hint]
      exact ⟨Subgroup.mem_sup_left hkK, Subgroup.mem_sup_left hkKt⟩
    obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N) ⟨k, hkO⟩
    have h1 : k ^ 2 ^ m = 1 := congrArg Subtype.val hm
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hk] at h2
    have h3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h2)
    omega

end CFSG.Quasithin.H13.U3.NLine
