module

public import CFSG.GroupTheory.PowerMapConj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WXU3P
public import CFSG.Blueprint.LieModelAPI
public import CFSG.RankThree.PartTwo.Sec10.Sec10XProofTen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.GroupTheory

variable {G : Type} [Group G] [Finite G]

abbrev borelQuotN (L : Subgroup G) : Subgroup G := Subgroup.normalizer (L : Set G)

abbrev borelQuotK (L : Subgroup G) : Subgroup ↥(borelQuotN L) :=
  (pCoreOf 2 L).subgroupOf (borelQuotN L)

instance borelQuotK_normal (L : Subgroup G) : (borelQuotK L).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)

abbrev borelQuotY (L : Subgroup G) : Type := ↥(borelQuotN L) ⧸ borelQuotK L

abbrev borelQuotPi (L : Subgroup G) : ↥(borelQuotN L) →* borelQuotY L :=
  QuotientGroup.mk' (borelQuotK L)

abbrev borelQuotL (L : Subgroup G) : Subgroup (borelQuotY L) :=
  (L.subgroupOf (borelQuotN L)).map (borelQuotPi L)

abbrev borelQuotU (L U : Subgroup G) : Subgroup (borelQuotY L) :=
  (U.subgroupOf (borelQuotN L)).map (borelQuotPi L)

noncomputable def bar2EquivLBar (L : Subgroup G) : Bar2 L ≃* ↥(borelQuotL L) := by
  classical
  let f : ↥L →* borelQuotY L :=
    (borelQuotPi L).comp (Subgroup.inclusion (Subgroup.le_normalizer (H := L)))
  have hker : f.ker = CFSG.pCore 2 ↥L := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    constructor
    · intro hx
      have hx' : (x : G) ∈ pCoreOf 2 L := Subgroup.mem_subgroupOf.mp hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
      have hyx' : y = x := Subtype.ext hyx
      rwa [hyx'] at hy
    · intro hx
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hrange : f.range = borelQuotL L := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := hy
      exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion _ x, x.2, rfl⟩
    · intro hy
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨(n : G), hn⟩, rfl⟩
  exact (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hrange))

theorem mem_piBar_map_iff {L U : Subgroup G} (hK : pCoreOf 2 L ≤ U)
    (n : ↥(borelQuotN L)) :
    borelQuotPi L n ∈ borelQuotU L U ↔ (n : G) ∈ U := by
  constructor
  · intro hn
    rw [borelQuotU, Subgroup.mem_map] at hn
    obtain ⟨u, hu, huu⟩ := hn
    have hker : u⁻¹ * n ∈ (borelQuotPi L).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, huu, inv_mul_cancel]
    rw [show (borelQuotPi L).ker = borelQuotK L from QuotientGroup.ker_mk' (borelQuotK L)] at hker
    have hmem : ((u⁻¹ * n : ↥(borelQuotN L)) : G) ∈ pCoreOf 2 L :=
      Subgroup.mem_subgroupOf.mp hker
    have huU : (u : G) ∈ U := Subgroup.mem_subgroupOf.mp hu
    have hn_eq : (n : G) = (u : G) * ((u⁻¹ * n : ↥(borelQuotN L)) : G) := by
      simp [mul_assoc]
    rw [hn_eq]
    exact U.mul_mem huU (hK hmem)
  · intro hn
    exact Subgroup.mem_map.mpr ⟨n, Subgroup.mem_subgroupOf.mpr hn, rfl⟩

theorem isSylowTwoOf_map_borelQuotPi {L U : Subgroup G}
    (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf U L) :
    CFSG.QuasithinUnique.IsSylowTwoOf (borelQuotU L U) (borelQuotL L) :=
  CFSG.Quasithin.SmithC27.isSylowTwoOf_map' (borelQuotPi L)
    (CFSG.Quasithin.SmithC27.isSylowTwoOf_subgroupOf hSyl
      (Subgroup.le_normalizer (H := L)))

theorem isSU3_LBar {L : Subgroup G} {n : ℕ} (h : IsSU3 (Bar2 L) n) :
    IsSU3 (borelQuotL L) n :=
  ⟨CFSG.Open.IsQuasisimple.of_mulEquiv (bar2EquivLBar L).symm h.1,
    CFSG.Blueprint.LieModel.quotient_center_of_mulEquiv (bar2EquivLBar L) h.2⟩

theorem isL2_LBar {L : Subgroup G} {n : ℕ} (h : IsL2 (Bar2 L) n) :
    IsL2 (borelQuotL L) n :=
  CFSG.Blueprint.LieModel.of_mulEquiv (bar2EquivLBar L) h

theorem exists_powerMap_lift_bar2 {L U : Subgroup G}
    (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf U L)
    {t : G} (ht : t ∈ borelQuotN L ⊓ Subgroup.normalizer (U : Set G))
    (hpow : ∀ r ∈ Subgroup.normalizer (borelQuotL L : Set (borelQuotY L)) ⊓
        Subgroup.normalizer (borelQuotU L U : Set (borelQuotY L)),
      ∃ j : ℕ, ∀ b ∈ borelQuotL L ⊓ Subgroup.normalizer (borelQuotU L U : Set (borelQuotY L)),
        r * b * r⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ borelQuotU L U) :
    ∃ j : ℕ, ∀ b ∈ L ⊓ Subgroup.normalizer (U : Set G),
      t * b * t⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ U := by
  have hK : pCoreOf 2 L ≤ U :=
    CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hSyl
  let tN : ↥(borelQuotN L) := ⟨t, ht.1⟩
  have htL : tN ∈ Subgroup.normalizer
      ((L.subgroupOf (borelQuotN L) : Subgroup ↥(borelQuotN L)) : Set ↥(borelQuotN L)) :=
    CFSG.RankThree.PartTwo.Sec10.Sec10XProof.mem_normalizer_subgroupOf_of_mem_normalizer
      (K := L) (H := borelQuotN L) ht.1
  have htU : tN ∈ Subgroup.normalizer
      ((U.subgroupOf (borelQuotN L) : Subgroup ↥(borelQuotN L)) : Set ↥(borelQuotN L)) :=
    CFSG.RankThree.PartTwo.Sec10.Sec10XProof.mem_normalizer_subgroupOf_of_mem_normalizer
      (K := U) (H := borelQuotN L) ht.2
  have htbarL : borelQuotPi L tN ∈ Subgroup.normalizer (borelQuotL L : Set (borelQuotY L)) :=
    Subgroup.le_normalizer_map (borelQuotPi L) (Subgroup.mem_map.mpr ⟨tN, htL, rfl⟩)
  have htbarU : borelQuotPi L tN ∈
      Subgroup.normalizer (borelQuotU L U : Set (borelQuotY L)) :=
    Subgroup.le_normalizer_map (borelQuotPi L) (Subgroup.mem_map.mpr ⟨tN, htU, rfl⟩)
  obtain ⟨j, hj⟩ := hpow (borelQuotPi L tN) ⟨htbarL, htbarU⟩
  refine ⟨j, fun b hb => ?_⟩
  let bN : ↥(borelQuotN L) := ⟨b, Subgroup.le_normalizer (H := L) hb.1⟩
  have hbU : bN ∈ Subgroup.normalizer
      ((U.subgroupOf (borelQuotN L) : Subgroup ↥(borelQuotN L)) : Set ↥(borelQuotN L)) :=
    CFSG.RankThree.PartTwo.Sec10.Sec10XProof.mem_normalizer_subgroupOf_of_mem_normalizer
      (K := U) (H := borelQuotN L) hb.2
  have hbbarL : borelQuotPi L bN ∈ borelQuotL L := Subgroup.mem_map.mpr ⟨bN, hb.1, rfl⟩
  have hbbarU : borelQuotPi L bN ∈
      Subgroup.normalizer (borelQuotU L U : Set (borelQuotY L)) :=
    Subgroup.le_normalizer_map (borelQuotPi L) (Subgroup.mem_map.mpr ⟨bN, hbU, rfl⟩)
  have hmem := hj (borelQuotPi L bN) ⟨hbbarL, hbbarU⟩
  let n : ↥(borelQuotN L) := tN * bN * tN⁻¹ * (bN ^ 2 ^ j)⁻¹
  have hn_eq : borelQuotPi L n = borelQuotPi L tN * borelQuotPi L bN * (borelQuotPi L tN)⁻¹ *
      (borelQuotPi L bN ^ 2 ^ j)⁻¹ := by
    simp [n, map_mul, map_inv, map_pow]
  have hn : (n : G) ∈ U := by
    refine (mem_piBar_map_iff (L := L) (U := U) hK n).mp ?_
    rw [hn_eq]
    exact hmem
  simpa [n, bN, tN] using hn

theorem powerMap_of_isSU3_bar2
    {L U : Subgroup G} {n : ℕ} (hSU3 : IsSU3 (Bar2 L) n)
    (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf U L)
    {t : G} (ht : t ∈ borelQuotN L ⊓ Subgroup.normalizer (U : Set G)) :
    ∃ j : ℕ, ∀ b ∈ L ⊓ Subgroup.normalizer (U : Set G),
      t * b * t⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ U := by
  have hn2 : 2 ≤ n := s13_two_le_of_isU3 hSU3.2
  have hSU3bar : IsSU3 (borelQuotL L) n := isSU3_LBar hSU3
  have hperf : Group.IsPerfect ↥(borelQuotL L) := Group.IsPerfect.mk hSU3bar.1.1
  have hPSU : CFSG.Quasithin.IsPSU 3 2 n
      (↥(borelQuotL L) ⧸ Subgroup.center ↥(borelQuotL L)) :=
    (CFSG.Blueprint.LieModel.classical_iff (by decide)).1 hSU3bar.2
  have hUbar : CFSG.QuasithinUnique.IsSylowTwoOf (borelQuotU L U) (borelQuotL L) :=
    isSylowTwoOf_map_borelQuotPi hSyl
  obtain ⟨-, -, -, -, hpow⟩ :=
    CFSG.Quasithin.H13.P31X.u3BorelFacts_holds n hn2 (borelQuotY L) (borelQuotL L) (borelQuotU L U)
      hperf hPSU hUbar
  exact exists_powerMap_lift_bar2 hSyl ht hpow

theorem powerMap_of_isL2_bar2
    {L U : Subgroup G} {n : ℕ} (hL2 : IsL2 (Bar2 L) n)
    (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf U L)
    {t : G} (ht : t ∈ borelQuotN L ⊓ Subgroup.normalizer (U : Set G)) :
    ∃ j : ℕ, ∀ b ∈ L ⊓ Subgroup.normalizer (U : Set G),
      t * b * t⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ U := by
  have hn2 : 2 ≤ n := s13_two_le_of_isL2 hL2
  have hL2bar : IsL2 (borelQuotL L) n := isL2_LBar hL2
  have hPSL : CFSG.Quasithin.IsPSL 2 2 n (borelQuotL L) :=
    (CFSG.Blueprint.LieModel.classical_iff (by decide)).1 hL2bar
  have hUbar : CFSG.QuasithinUnique.IsSylowTwoOf (borelQuotU L U) (borelQuotL L) :=
    isSylowTwoOf_map_borelQuotPi hSyl
  obtain ⟨-, -, -, -, -, -, hpow⟩ :=
    CFSG.Quasithin.H13.P31X.l2BorelFacts_holds n hn2 (borelQuotY L) (borelQuotL L) (borelQuotU L U)
      hPSL hUbar
  exact exists_powerMap_lift_bar2 hSyl ht hpow

theorem map_inf_normalizer_bar2 {L U : Subgroup G}
    (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf U L) :
    ((L ⊓ Subgroup.normalizer (U : Set G)).subgroupOf (borelQuotN L)).map (borelQuotPi L) =
      borelQuotL L ⊓ Subgroup.normalizer (borelQuotU L U : Set (borelQuotY L)) := by
  have hK : pCoreOf 2 L ≤ U :=
    CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hSyl
  have hker : (borelQuotPi L).ker ≤ U.subgroupOf (borelQuotN L) := by
    rw [show (borelQuotPi L).ker = borelQuotK L from QuotientGroup.ker_mk' (borelQuotK L)]
    intro x hx
    have hx' : (x : G) ∈ pCoreOf 2 L := by
      simpa only [borelQuotK, Subgroup.mem_subgroupOf] using hx
    exact Subgroup.mem_subgroupOf.mpr (hK hx')
  ext y
  constructor
  · intro hy
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hy
    have hnL : (n : G) ∈ L := Subgroup.mem_subgroupOf.mp hn.1
    have hnU : (n : G) ∈ Subgroup.normalizer (U : Set G) := hn.2
    refine ⟨Subgroup.mem_map.mpr ⟨n, Subgroup.mem_subgroupOf.mpr hnL, rfl⟩, ?_⟩
    refine Subgroup.le_normalizer_map (borelQuotPi L) (Subgroup.mem_map.mpr ⟨n, ?_, rfl⟩)
    exact CFSG.RankThree.PartTwo.Sec10.Sec10XProof.mem_normalizer_subgroupOf_of_mem_normalizer
      (K := U) (H := borelQuotN L) hnU
  · rintro ⟨hyL, hyU⟩
    obtain ⟨n, hnL, rfl⟩ := Subgroup.mem_map.mp hyL
    have hnUnorm : n ∈ Subgroup.normalizer
        ((U.subgroupOf (borelQuotN L) : Subgroup ↥(borelQuotN L)) : Set ↥(borelQuotN L)) := by
      have hcomap :
          (Subgroup.normalizer (borelQuotU L U : Set (borelQuotY L))).comap
            (borelQuotPi L) =
          Subgroup.normalizer (U.subgroupOf (borelQuotN L) : Subgroup ↥(borelQuotN L)) := by
        rw [Subgroup.comap_normalizer_eq_of_surjective (H := borelQuotU L U)
          (QuotientGroup.mk'_surjective (borelQuotK L))]
        have hker' : (QuotientGroup.mk' (borelQuotK L)).ker ≤ U.subgroupOf (borelQuotN L) := by
          simpa [borelQuotPi] using hker
        have hc : (borelQuotU L U).comap (QuotientGroup.mk' (borelQuotK L)) =
            U.subgroupOf (borelQuotN L) := by
          simpa [borelQuotU] using
            Subgroup.comap_map_eq_self (f := QuotientGroup.mk' (borelQuotK L)) hker'
        rw [hc]
      exact hcomap ▸ hyU
    have hnN : (n : G) ∈ Subgroup.normalizer (U : Set G) :=
      CFSG.RankThree.PartTwo.Sec10.Sec10XProof.mem_normalizer_of_mem_normalizer_subgroupOf
        (K := U) (H := borelQuotN L) (hSyl.1.trans (Subgroup.le_normalizer (H := L))) hnUnorm
    exact Subgroup.mem_map.mpr ⟨n,
      Subgroup.mem_subgroupOf.mpr ⟨Subgroup.mem_subgroupOf.mp hnL, hnN⟩, rfl⟩

theorem card_inf_normalizer_bar2_dvd {L U : Subgroup G}
    (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf U L) :
    Nat.card ↥(borelQuotL L ⊓
      Subgroup.normalizer (borelQuotU L U : Set (borelQuotY L))) ∣
      Nat.card ↥(L ⊓ Subgroup.normalizer (U : Set G)) := by
  have hBN : L ⊓ Subgroup.normalizer (U : Set G) ≤ borelQuotN L :=
    inf_le_left.trans (Subgroup.le_normalizer (H := L))
  have h := Subgroup.card_map_dvd
    ((L ⊓ Subgroup.normalizer (U : Set G)).subgroupOf (borelQuotN L)) (borelQuotPi L)
  rwa [map_inf_normalizer_bar2 hSyl,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv] at h

theorem dvd_card_inf_normalizer_of_bar2 {L U : Subgroup G} {n r : ℕ}
    (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf U L)
    (hcard : Nat.card ↥(borelQuotL L ⊓
        Subgroup.normalizer (borelQuotU L U : Set (borelQuotY L))) *
        Nat.gcd 3 (2 ^ n + 1) =
      Nat.card (borelQuotU L U) * (4 ^ n - 1) * Nat.card (Subgroup.center (borelQuotL L)))
    (hr : r.Prime) (hr3 : r ≠ 3) (hrdvd : r ∣ 2 ^ n - 1) :
    r ∣ Nat.card ↥(L ⊓ Subgroup.normalizer (U : Set G)) := by
  have h4 : r ∣ 4 ^ n - 1 := by
    have h := Nat.sub_dvd_pow_sub_pow (2 ^ n) 1 2
    have e4 : (2 ^ n) ^ 2 = 4 ^ n := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [e4, one_pow] at h
    exact hrdvd.trans h
  have hgcd : ¬ r ∣ Nat.gcd 3 (2 ^ n + 1) := by
    intro hd
    have h3 : r ∣ 3 := hd.trans (Nat.gcd_dvd_left 3 (2 ^ n + 1))
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp h3)
  have hdvdBbar : r ∣
      Nat.card ↥(borelQuotL L ⊓
        Subgroup.normalizer (borelQuotU L U : Set (borelQuotY L))) := by
    have hprod : r ∣
        Nat.card ↥(borelQuotL L ⊓
          Subgroup.normalizer (borelQuotU L U : Set (borelQuotY L))) *
          Nat.gcd 3 (2 ^ n + 1) := by
      rw [hcard]
      exact (h4.mul_left (Nat.card (borelQuotU L U))).mul_right
        (Nat.card (Subgroup.center (borelQuotL L)))
    rcases (Nat.Prime.dvd_mul hr).mp hprod with h | h
    · exact h
    · exact absurd h hgcd
  exact hdvdBbar.trans (card_inf_normalizer_bar2_dvd hSyl)

theorem prime_dvd_card_inf_normalizer_of_isSU3_bar2
    {L U : Subgroup G} {n r : ℕ} (hSU3 : IsSU3 (Bar2 L) n)
    (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf U L)
    (hr : r.Prime) (hr3 : r ≠ 3) (hrdvd : r ∣ 2 ^ n - 1) :
    r ∣ Nat.card ↥(L ⊓ Subgroup.normalizer (U : Set G)) := by
  have hn2 : 2 ≤ n := s13_two_le_of_isU3 hSU3.2
  have hSU3bar : IsSU3 (borelQuotL L) n := isSU3_LBar hSU3
  have hperf : Group.IsPerfect ↥(borelQuotL L) := Group.IsPerfect.mk hSU3bar.1.1
  have hPSU : CFSG.Quasithin.IsPSU 3 2 n
      (↥(borelQuotL L) ⧸ Subgroup.center ↥(borelQuotL L)) :=
    (CFSG.Blueprint.LieModel.classical_iff (by decide)).1 hSU3bar.2
  have hUbar : CFSG.QuasithinUnique.IsSylowTwoOf (borelQuotU L U) (borelQuotL L) :=
    isSylowTwoOf_map_borelQuotPi hSyl
  obtain ⟨-, hcard, -, -, -⟩ :=
    CFSG.Quasithin.H13.P31X.u3BorelFacts_holds n hn2 (borelQuotY L) (borelQuotL L) (borelQuotU L U)
      hperf hPSU hUbar
  exact dvd_card_inf_normalizer_of_bar2 hSyl hcard hr hr3 hrdvd

theorem exists_prime_order_le_normalizer_of_isSU3_bar2
    {L T : Subgroup G} {n s r : ℕ}
    (hTL : T ≤ borelQuotN L) (hT2 : IsPGroup 2 T)
    (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (L ⊓ T) L)
    (hSU3 : IsSU3 (Bar2 L) n)
    (hs : Odd s) (hsn : s ∣ n)
    (hr : r.Prime) (hrdvd : r ∣ 2 ^ s - 1) :
    ∃ X : Subgroup G, X ≤ L ∧ Nat.card X = r ∧
      X ≤ Subgroup.normalizer (T : Set G) := by
  have hTU : T ≤ Subgroup.normalizer ((L ⊓ T : Subgroup G) : Set G) :=
    (le_inf hTL (Subgroup.le_normalizer (H := T))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hrdvdn : r ∣ 2 ^ n - 1 :=
    hrdvd.trans (Nat.pow_sub_one_dvd_pow_sub_one (x := 2) hsn)
  have hr3 : r ≠ 3 := by
    rintro rfl
    have h1 : (2 ^ s - 1) % 3 = 1 := s13_Facts13_two_pow_sub_one_mod_three hs
    have h0 : (2 ^ s - 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp hrdvd
    omega
  have hdvdB : r ∣ Nat.card ↥(L ⊓ Subgroup.normalizer ((L ⊓ T : Subgroup G) : Set G)) :=
    prime_dvd_card_inf_normalizer_of_isSU3_bar2 hSU3 hSyl hr hr3 hrdvdn
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨xB, hxBord⟩ := exists_prime_orderOf_dvd_card' r hdvdB
  let x : G := xB
  have hxBmem : x ∈ L ⊓ Subgroup.normalizer ((L ⊓ T : Subgroup G) : Set G) := xB.2
  have hxr : orderOf x = r := by
    rw [show x = (xB : G) from rfl, Subgroup.orderOf_coe, hxBord]
  have hpowT : ∀ u ∈ T, ∃ e : ℕ, u ^ 2 ^ e = 1 := by
    intro u hu
    obtain ⟨e, he⟩ := hT2 ⟨u, hu⟩
    exact ⟨e, by simpa using congrArg Subtype.val he⟩
  have hconj : ∀ u ∈ T, x⁻¹ * u * x ∈ T := by
    intro u hu
    have huN : u ∈ borelQuotN L ⊓ Subgroup.normalizer ((L ⊓ T : Subgroup G) : Set G) :=
      ⟨hTL hu, hTU hu⟩
    obtain ⟨e, he⟩ := hpowT u hu
    obtain ⟨j, hj⟩ := powerMap_of_isSU3_bar2 hSU3 hSyl huN
    have hmem := inv_mul_conj_mem_of_powerMap (Y := G)
      (B := L ⊓ Subgroup.normalizer ((L ⊓ T : Subgroup G) : Set G))
      (U := L ⊓ T) (t := u) (x := x) huN.2 hxBmem.2 hSyl.2.1 he hj hs hr hrdvd
      hxBmem hxr
    have heq : x⁻¹ * u * x = (x⁻¹ * (u * x * u⁻¹)) * u := by group
    rw [heq]
    exact T.mul_mem (Subgroup.mem_inf.mp hmem).2 hu
  have hxT : x ∈ Subgroup.normalizer (T : Set G) := by
    have h := Subgroup.mem_normalizer_fintype (S := (T : Set G)) (x := x⁻¹) fun u hu => by
      simpa using hconj u hu
    simpa using inv_mem h
  exact ⟨Subgroup.zpowers x, Subgroup.zpowers_le.mpr hxBmem.1, by
    rw [Nat.card_zpowers, hxr], Subgroup.zpowers_le.mpr hxT⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
