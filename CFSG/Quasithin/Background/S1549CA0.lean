module

public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Background.ThreePrimeGroup
public import CFSG.Quasithin.EmptyFaithful.S153Cases
public import CFSG.Quasithin.EmptyFaithful.T1531Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
open scoped commutatorElement Pointwise

namespace S1549C

theorem exists_elemAbelian_nine {P : Type*} [Group P] [Finite P] (hexp : ∀ x : P, x ^ 3 = 1)
    (h9 : 9 ∣ Nat.card P) : ∃ E : Subgroup P, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 P := fun x => ⟨1, by simpa using hexp x⟩
  have hnt : Nontrivial P := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    have := Nat.le_of_dvd Nat.card_pos h9
    omega
  have := hP.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : ↥(Subgroup.center P))
  have hz1 : (z : P) ≠ 1 := fun h => hz (Subtype.ext h)
  have hzc : ∀ y : P, y * (z : P) = (z : P) * y := fun y => by
    have := z.2
    rw [Subgroup.mem_center_iff] at this
    exact this y
  have hzo : orderOf (z : P) = 3 := by
    have h1 : orderOf (z : P) ∣ 3 := orderOf_dvd_of_pow_eq_one (hexp _)
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  have hzcard : Nat.card (Subgroup.zpowers (z : P)) = 3 := by rw [Nat.card_zpowers, hzo]
  have hex : ∃ a : P, a ∉ Subgroup.zpowers (z : P) := by
    by_contra hall
    push Not at hall
    have : (Subgroup.zpowers (z : P)) = ⊤ := eq_top_iff.mpr fun a _ => hall a
    have h3 : Nat.card P = 3 := by rw [← Subgroup.card_top, ← this, hzcard]
    have := Nat.le_of_dvd (by norm_num) (h3 ▸ h9)
    omega
  obtain ⟨a, ha⟩ := hex
  have ha1 : a ≠ 1 := fun h => ha (h ▸ Subgroup.one_mem _)
  have hao : orderOf a = 3 := by
    have h1 : orderOf a ∣ 3 := orderOf_dvd_of_pow_eq_one (hexp _)
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ha1
    · exact h
  have hE0 : IsElemAbelian 3 (Subgroup.zpowers (z : P)) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp x.2
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp y.2
      apply Subtype.ext
      show (x : P) * y = y * x
      rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hexp, one_zpow]
  obtain ⟨hE, hEc⟩ := exists_elemAbelian_sup_zpowers (p := 3) hE0 hao
    (fun e he => by
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp he
      exact (Commute.zpow_left (show Commute (z : P) a from (hzc a).symm) m)) ha
  exact ⟨_, hE, by rw [hEc, hzcard]⟩

section Quot

variable {G : Type} [Group G] [Finite G] {T Mc M : Subgroup G}

theorem pRank_three_quot_le (h : Hyp153 G T Mc M) :
    CFSG.Open.pRank 3 (⊤ : Subgroup (OTwoQuot M)) ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup ↥M := CFSG.Open.pCore 2 ↥M with hN
  have hnd : ¬ 3 ∣ Nat.card N := by
    intro hd
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥M) 2).exists_card_eq
    rw [hk] at hd
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow hd)) (by norm_num)
  have h1 := CFSG.SectionRank.pRank_quotient_eq (p := 3) N hnd
  have h2 := pRank_top_subtype (p := 3) M
  have h3 := pRank_le_two_of_isTwoLocal h.qtfe.qtke h.inM.1.1 Nat.prime_three (by norm_num)
  calc CFSG.Open.pRank 3 (⊤ : Subgroup (OTwoQuot M)) = CFSG.Open.pRank 3 (⊤ : Subgroup ↥M) := h1
    _ = CFSG.Open.pRank 3 M := h2
    _ ≤ 2 := h3

theorem nine_dvd_card_Ystar (h113 : StageLemma14113) (h : Hyp153 G T Mc M) :
    9 ∣ Nat.card ↥(imageOTwoQuot M (Y153 Mc M)) := by
  obtain ⟨φ, -⟩ := exists_mulEquiv_imageOTwoQuot (Y153_le Mc M) (le_normalizer_Y153 Mc M)
  rw [← Nat.card_congr φ.toEquiv]
  rcases h.lemma_15_3_7_cases h113 with ⟨-, ⟨e⟩⟩ | ⟨hP, -⟩
  · rw [Nat.card_congr e.toEquiv]
    simp
  · rw [hP.2.1]
    norm_num

theorem mem_Y153_of_orderOf_three (h113 : StageLemma14113) (h : Hyp153 G T Mc M) {x : G}
    (hxM : x ∈ M) (hxC : x ∈ Subgroup.centralizer (VZ T M : Set G)) (hx3 : orderOf x = 3) :
    x ∈ Y153 Mc M := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYM := Y153_le Mc M
  have hMY := le_normalizer_Y153 Mc M
  set Ys := imageOTwoQuot M (Y153 Mc M) with hYs
  have hxo : x ^ 3 = 1 := hx3 ▸ pow_orderOf_eq_one x
  set xs : OTwoQuot M := QuotientGroup.mk (⟨x, hxM⟩ : ↥M) with hxs
  have hxs3 : xs ^ 3 = 1 := by
    rw [hxs, ← QuotientGroup.mk_pow]
    have : (⟨x, hxM⟩ : ↥M) ^ 3 = 1 := Subtype.ext (by simpa using hxo)
    rw [this]; exact QuotientGroup.mk_one _
  have hxs1 : xs ≠ 1 := by
    intro h1
    have hx2 : x ∈ pCoreOf 2 M := (mk_eq_one_iff_mem_pCoreOf ⟨x, hxM⟩).mp h1
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 M ⟨x, hx2⟩
    have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hd : 3 ∣ 2 ^ k := hx3 ▸ orderOf_dvd_of_pow_eq_one hk'
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.prime_three.dvd_of_dvd_pow hd)) (by norm_num)
  have hxso : orderOf xs = 3 := by
    have h1 : orderOf xs ∣ 3 := orderOf_dvd_of_pow_eq_one hxs3
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h' | h'
    · exact absurd (orderOf_eq_one_iff.mp h') hxs1
    · exact h'
  have hC : x ∈ M ⊓ Subgroup.centralizer (VZ T M : Set G) := ⟨hxM, hxC⟩
  have hcomm : ∀ y ∈ Ys, Commute y xs := by
    intro u hu
    obtain ⟨y, hyM, hyY, rfl⟩ := mem_imageOTwoQuot_iff.mp hu
    exact (mk_commute_iff ⟨y, hyM⟩ ⟨x, hxM⟩).mpr (h.commutator_Y153_le hyY hC)
  have hxsY : xs ∈ Ys := by
    by_contra hnot
    obtain ⟨E', hE', hE'card⟩ := exists_elemAbelian_nine (P := ↥Ys)
      (fun x => (Hyp153.Ystar_structure h113 h).1.2.2 x) (nine_dvd_card_Ystar h113 h)
    set E : Subgroup (OTwoQuot M) := E'.map Ys.subtype with hE
    have hEY : E ≤ Ys := fun u hu => by
      obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.mp hu
      exact a.2
    have hEcard : Nat.card E = 9 := by
      rw [hE, Subgroup.card_map_of_injective Ys.subtype_injective, hE'card]
    have hEab : IsElemAbelian 3 E := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
      · obtain ⟨a', ha', ha''⟩ := Subgroup.mem_map.mp a.2
        obtain ⟨b', hb', hb''⟩ := Subgroup.mem_map.mp b.2
        apply Subtype.ext
        show (a : OTwoQuot M) * b = b * a
        rw [← ha'', ← hb'']
        have h1 : a' * b' = b' * a' :=
          congrArg Subtype.val (hE'.1.1.comm (⟨a', ha'⟩ : ↥E') ⟨b', hb'⟩)
        exact congrArg Subtype.val h1
      · obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
        have := hE'.2 a' ha'
        simpa using congrArg Subtype.val this
    have hxE : xs ∉ E := fun hx => hnot (hEY hx)
    obtain ⟨hE3, hc3⟩ := exists_elemAbelian_sup_zpowers (p := 3) hEab hxso
      (fun e he => (hcomm e (hEY he))) hxE
    have hle := le_pRank Nat.prime_three (X := (⊤ : Subgroup (OTwoQuot M))) le_top hE3
      (k := 3) (by rw [hc3, hEcard]; norm_num)
    have := pRank_three_quot_le h
    omega
  obtain ⟨y, hyM, hyY, hyx⟩ := mem_imageOTwoQuot_iff.mp hxsY
  have hmem : (⟨y, hyM⟩ : ↥M)⁻¹ * ⟨x, hxM⟩ ∈ CFSG.Open.pCore 2 ↥M := by
    rw [← QuotientGroup.eq]
    exact hyx
  have ho2 : y⁻¹ * x ∈ pCoreOf 2 M := ⟨_, hmem, rfl⟩
  have : ((Y153 Mc M).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).mpr hMY
  let φ : ↥M →* ↥M ⧸ (Y153 Mc M).subgroupOf M := QuotientGroup.mk' _
  have hφy : φ ⟨y, hyM⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hyY)
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 M ⟨y⁻¹ * x, ho2⟩
  have hk' : (y⁻¹ * x) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hφx : φ ⟨x, hxM⟩ = φ ⟨y⁻¹ * x, M.mul_mem (M.inv_mem hyM) hxM⟩ := by
    have e : (⟨x, hxM⟩ : ↥M) = ⟨y, hyM⟩ * ⟨y⁻¹ * x, M.mul_mem (M.inv_mem hyM) hxM⟩ :=
      Subtype.ext (by simp)
    rw [e, map_mul, hφy, one_mul]
  have h1 : orderOf (φ ⟨x, hxM⟩) ∣ 3 := by
    refine (orderOf_map_dvd φ ⟨x, hxM⟩).trans ?_
    rw [Subgroup.orderOf_mk, hx3]
  have h2 : orderOf (φ ⟨x, hxM⟩) ∣ 2 ^ k := by
    rw [hφx]
    refine (orderOf_map_dvd φ _).trans ?_
    rw [Subgroup.orderOf_mk]
    exact orderOf_dvd_of_pow_eq_one hk'
  have hcop : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have h4 : orderOf (φ ⟨x, hxM⟩) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have h5 : φ ⟨x, hxM⟩ = 1 := orderOf_eq_one_iff.mp h4
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h5)

theorem pow_three_eq_one_of_odd (h113 : StageLemma14113) (h : Hyp153 G T Mc M) {y : G}
    (hy : y ∈ Y153 Mc M) (ho : Odd (orderOf y)) : y ^ 3 = 1 := by
  have h3 := h.pow_three_mem_pCoreOf_Y153 h113 hy
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (Y153 Mc M) ⟨y ^ 3, h3⟩
  have hk' : (y ^ 3) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hd1 : orderOf (y ^ 3) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hd2 : orderOf (y ^ 3) ∣ orderOf y := orderOf_pow_dvd 3
  have hcop : Nat.Coprime (2 ^ k) (orderOf y) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr ho)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)

theorem threePrime_of_case_one (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    (h1 : Case157One T Mc M) :
    IsThreePrimeGroup (M ⊓ Subgroup.centralizer (VZ T M : Set G)) := by
  intro hdvd
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  have hxo : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  have hxY : (x : G) ∈ Y153 Mc M := mem_Y153_of_orderOf_three h113 h x.2.1 x.2.2 hxo
  have hx2 : (x : G) ∈ pCoreOf 2 (Y153 Mc M) := by
    rw [h1.1]
    exact ⟨hxY, x.2.2⟩
  obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (Y153 Mc M) ⟨x, hx2⟩
  have hk' : (x : G) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hd : 3 ∣ 2 ^ k := hxo ▸ orderOf_dvd_of_pow_eq_one hk'
  exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
    (Nat.prime_three.dvd_of_dvd_pow hd)) (by norm_num)

end Quot

end S1549C

end CFSG.Quasithin
