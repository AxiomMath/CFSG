module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiftyFive
public import CFSG.Quasithin.EmptyFaithful.S146zYZSzData
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.NormalizerSubgroupCyclic
public import CFSG.Quasithin.Recognition.Stroth.BenderNoFF
public import CFSG.Quasithin.Vol2.Ch5Sec1L34DiscAut
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.StabilizerLift
public import CFSG.RankThree.PartOne.K1320.L4Final
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 CFSG.GroupTheory
open CFSG.ShultStronglyClosedTI.OddPrimeInverters
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem prime_dvd_card_inf_normalizer_of_isL2_bar2 {L U : Subgroup G} {n r : ℕ}
    (hL2 : IsL2 (Bar2 L) n) (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf U L)
    (hrdvd : r ∣ 2 ^ n - 1) :
    r ∣ Nat.card ↥(L ⊓ Subgroup.normalizer (U : Set G)) := by
  have hn2 : 2 ≤ n := s13_two_le_of_isL2 hL2
  have hL2bar : IsL2 (borelQuotL L) n := isL2_LBar hL2
  have hPSL : CFSG.Quasithin.IsPSL 2 2 n (borelQuotL L) :=
    (CFSG.Blueprint.LieModel.classical_iff (by decide)).1 hL2bar
  have hUbar : CFSG.QuasithinUnique.IsSylowTwoOf (borelQuotU L U) (borelQuotL L) :=
    isSylowTwoOf_map_borelQuotPi hSyl
  obtain ⟨-, -, hcardB, -⟩ :=
    CFSG.Quasithin.H13.P31X.l2BorelFacts_holds n hn2 (borelQuotY L) (borelQuotL L)
      (borelQuotU L U) hPSL hUbar
  have hdvd : r ∣ Nat.card ↥(borelQuotL L ⊓
      Subgroup.normalizer (borelQuotU L U : Set (borelQuotY L))) := by
    rw [hcardB]
    exact Dvd.dvd.mul_left hrdvd (2 ^ n)
  exact hdvd.trans (card_inf_normalizer_bar2_dvd hSyl)

theorem relIndex_inf_normalizer_eq_bar {L U : Subgroup G}
    (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf U L) :
    (L ⊓ Subgroup.normalizer (U : Set G)).relIndex L =
      (borelQuotL L ⊓
        Subgroup.normalizer (borelQuotU L U : Set (borelQuotY L))).relIndex (borelQuotL L) := by
  have hK : pCoreOf 2 L ≤ U :=
    CFSG.Quasithin.B6.pCoreOf_two_le_of_isSylowTwoOf hSyl
  have hKL : borelQuotK L ≤ L.subgroupOf (borelQuotN L) := by
    intro x hx
    have hx' : (x : G) ∈ pCoreOf 2 L := by
      simpa only [borelQuotK, Subgroup.mem_subgroupOf] using hx
    exact Subgroup.mem_subgroupOf.mpr (CFSG.LieType.BorelTits.pCoreOf_le (r := 2) L hx')
  have hKB : borelQuotK L ≤
      (L ⊓ Subgroup.normalizer (U : Set G)).subgroupOf (borelQuotN L) := by
    intro x hx
    have hx' : (x : G) ∈ pCoreOf 2 L := by
      simpa only [borelQuotK, Subgroup.mem_subgroupOf] using hx
    refine Subgroup.mem_subgroupOf.mpr ⟨?_, ?_⟩
    · exact CFSG.LieType.BorelTits.pCoreOf_le (r := 2) L hx'
    · exact Subgroup.le_normalizer (hK hx')
  have h := Subgroup.relIndex_map_map (borelQuotPi L)
    ((L ⊓ Subgroup.normalizer (U : Set G)).subgroupOf (borelQuotN L))
    (L.subgroupOf (borelQuotN L))
  rw [map_inf_normalizer_bar2 hSyl, QuotientGroup.ker_mk'] at h
  rw [sup_eq_left.mpr hKB, sup_eq_left.mpr hKL] at h
  change (borelQuotL L ⊓
        Subgroup.normalizer (borelQuotU L U : Set (borelQuotY L))).relIndex (borelQuotL L) =
      ((L ⊓ Subgroup.normalizer (U : Set G)).subgroupOf (borelQuotN L)).relIndex
        (L.subgroupOf (borelQuotN L)) at h
  rw [Subgroup.relIndex_subgroupOf (H := L ⊓ Subgroup.normalizer (U : Set G))
    (K := L) (L := borelQuotN L) (Subgroup.le_normalizer (H := L))] at h
  exact h.symm

theorem relIndex_inf_normalizer_of_isL2_bar2 {L U : Subgroup G} {n : ℕ}
    (hL2 : IsL2 (Bar2 L) n) (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf U L) :
    (L ⊓ Subgroup.normalizer (U : Set G)).relIndex L = 2 ^ n + 1 := by
  have hn2 : 2 ≤ n := s13_two_le_of_isL2 hL2
  have hL2bar : IsL2 (borelQuotL L) n := isL2_LBar hL2
  have hPSL : CFSG.Quasithin.IsPSL 2 2 n (borelQuotL L) :=
    (CFSG.Blueprint.LieModel.classical_iff (by decide)).1 hL2bar
  have hUbar : CFSG.QuasithinUnique.IsSylowTwoOf (borelQuotU L U) (borelQuotL L) :=
    isSylowTwoOf_map_borelQuotPi hSyl
  obtain ⟨hcardX, -, hcardB, -⟩ :=
    CFSG.Quasithin.H13.P31X.l2BorelFacts_holds n hn2 (borelQuotY L) (borelQuotL L)
      (borelQuotU L U) hPSL hUbar
  have hcardrel : Nat.card ↥(borelQuotL L) =
      Nat.card ↥(borelQuotL L ⊓
        Subgroup.normalizer (borelQuotU L U : Set (borelQuotY L))) *
        (borelQuotL L ⊓
          Subgroup.normalizer (borelQuotU L U : Set (borelQuotY L))).relIndex (borelQuotL L) := by
    rw [← Subgroup.relIndex_mul_card]
    exact (mul_comm _ _).trans (by rw [inf_eq_left.mpr inf_le_left])
  rw [hcardX, hcardB] at hcardrel
  have h4 : 4 ^ n = (2 ^ n) ^ 2 := by
    calc 4 ^ n = (2 ^ 2) ^ n := by norm_num
      _ = 2 ^ (2 * n) := by rw [pow_mul]
      _ = 2 ^ (n * 2) := by rw [mul_comm]
      _ = (2 ^ n) ^ 2 := by rw [pow_mul]
  rw [h4] at hcardrel
  have harith : 2 ^ n * ((2 ^ n) ^ 2 - 1) = (2 ^ n * (2 ^ n - 1)) * (2 ^ n + 1) := by
    have hq2 : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
      have h := Nat.sq_sub_sq (2 ^ n) 1
      simp only [one_pow] at h
      rw [h]; ring
    rw [hq2]; ring
  rw [harith] at hcardrel
  have hpos : 0 < 2 ^ n * (2 ^ n - 1) := by
    have h1 : 0 < 2 ^ n := by positivity
    have h2 : 0 < 2 ^ n - 1 := by
      have : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      omega
    exact Nat.mul_pos h1 h2
  have hthis := Nat.mul_left_cancel hpos hcardrel
  rw [relIndex_inf_normalizer_eq_bar hSyl]
  exact hthis.symm

theorem relIndex_inf_normalizer_of_isSz_bar2
    {L U : Subgroup G} {n : ℕ} (hSz : IsSz (Bar2 L) n)
    (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf U L) :
    (L ⊓ Subgroup.normalizer (U : Set G)).relIndex L = (2 ^ n) ^ 2 + 1 := by
  have hSzbar : IsSz (borelQuotL L) n :=
    CFSG.Blueprint.LieModel.of_mulEquiv (bar2EquivLBar L) hSz
  have hM : CFSG.Blueprint.SuzukiModel (borelQuotL L) 2 n :=
    (CFSG.Blueprint.LieModel.suzukiModel hSzbar).2
  obtain ⟨-, a, ha, K, hfield, hfin, hf, hKcard, ⟨e0⟩⟩ := hM
  letI := hfield
  letI := hfin
  have hKa : Nat.card K = 2 ^ (2 * a + 1) := by rw [hKcard, hf]
  let e : borelQuotL L ≃* CFSG.Open.Sz a :=
    e0.trans (CFSG.Quasithin.Stroth.suzukiGroupEquivSz a K hKa)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUbar : CFSG.QuasithinUnique.IsSylowTwoOf (borelQuotU L U) (borelQuotL L) :=
    isSylowTwoOf_map_borelQuotPi hSyl
  have hUK : borelQuotU L U ≤ borelQuotL L := hUbar.1
  let Ū : Subgroup ↥(borelQuotL L) := (borelQuotU L U).subgroupOf (borelQuotL L)
  have hŪp : IsPGroup 2 ↥Ū :=
    hUbar.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hUK).symm
  let S : Sylow 2 ↥(borelQuotL L) := hŪp.toSylow hUbar.2.2
  have hScoe : (S : Subgroup ↥(borelQuotL L)) = Ū := rfl
  have hdata := CFSG.Quasithin.S146zY.SzNoFive.szSylowData_of_equiv ha e S
  have hNbridge : Subgroup.normalizer ((S : Subgroup ↥(borelQuotL L)) : Set ↥(borelQuotL L)) =
      (borelQuotL L ⊓ Subgroup.normalizer (borelQuotU L U : Set (borelQuotY L))).subgroupOf
        (borelQuotL L) := by
    rw [hScoe]
    exact CFSG.GorensteinWalter.normalizer_subgroupOf_eq_subgroupOf_inf_normalizer
      (borelQuotL L) (borelQuotU L U) hUK
  have hcardX : Nat.card ↥(borelQuotL L) =
      (2 ^ n) ^ 2 * ((2 ^ n) ^ 2 + 1) * (2 ^ n - 1) := by
    rw [hdata.card, hf]
  have hcardB : Nat.card ↥(borelQuotL L ⊓
      Subgroup.normalizer (borelQuotU L U : Set (borelQuotY L))) =
      (2 ^ n) ^ 2 * (2 ^ n - 1) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv,
      ← hNbridge, hdata.card_normalizer, hf]
  have hcardrel : Nat.card ↥(borelQuotL L) =
      Nat.card ↥(borelQuotL L ⊓
        Subgroup.normalizer (borelQuotU L U : Set (borelQuotY L))) *
        (borelQuotL L ⊓
          Subgroup.normalizer (borelQuotU L U : Set (borelQuotY L))).relIndex (borelQuotL L) := by
    rw [← Subgroup.relIndex_mul_card]
    exact (mul_comm _ _).trans (by rw [inf_eq_left.mpr inf_le_left])
  rw [hcardX, hcardB] at hcardrel
  have harith : (2 ^ n) ^ 2 * ((2 ^ n) ^ 2 + 1) * (2 ^ n - 1) =
      ((2 ^ n) ^ 2 * (2 ^ n - 1)) * ((2 ^ n) ^ 2 + 1) := by ring
  rw [harith] at hcardrel
  have hpos : 0 < (2 ^ n) ^ 2 * (2 ^ n - 1) := by
    have h1 : 0 < (2 ^ n) ^ 2 := by positivity
    have h2 : 0 < 2 ^ n - 1 := by
      have h3 : 3 ≤ n := (s13_odd_three_le_of_isSz hSz).2
      have h4 : 2 ≤ 2 ^ n := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact Nat.mul_pos h1 h2
  have hthis := Nat.mul_left_cancel hpos hcardrel
  rw [relIndex_inf_normalizer_eq_bar hSyl]
  exact hthis.symm

theorem not_dvd_relIndex_inf_normalizer_of_isL2_bar2 {L U : Subgroup G} {n r : ℕ}
    (hL2 : IsL2 (Bar2 L) n) (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf U L)
    (hr : r.Prime) (hrdvd : r ∣ 2 ^ n - 1) :
    ¬ r ∣ (L ⊓ Subgroup.normalizer (U : Set G)).relIndex L := by
  rw [relIndex_inf_normalizer_of_isL2_bar2 hL2 hSyl]
  intro h
  have h1 : r ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub h hrdvd
  have h2 : 2 ^ n + 1 - (2 ^ n - 1) = 2 := by
    have h3 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  rw [h2] at h1
  have hn2 : 2 ≤ n := s13_two_le_of_isL2 hL2
  exact (CFSG.RankThree.PartOne.K1320.prime_ne_two_of_dvd_two_pow_sub_one (f := n) (by omega) hrdvd)
    ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h1)

theorem not_dvd_relIndex_inf_normalizer_of_isSz_bar2
    {L U : Subgroup G} {n r : ℕ} (hSz : IsSz (Bar2 L) n)
    (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf U L)
    (hr : r.Prime) (hrdvd : r ∣ 2 ^ n - 1) :
    ¬ r ∣ (L ⊓ Subgroup.normalizer (U : Set G)).relIndex L := by
  rw [relIndex_inf_normalizer_of_isSz_bar2 hSz hSyl]
  intro h
  have hq1 : r ∣ (2 ^ n) ^ 2 - 1 := by
    have heq : (2 ^ n) ^ 2 - 1 = (2 ^ n - 1) * (2 ^ n + 1) := by
      have hh := Nat.sq_sub_sq (2 ^ n) 1
      simp only [one_pow] at hh
      rw [hh]; ring
    rw [heq]
    exact Dvd.dvd.mul_right hrdvd _
  have h1 : r ∣ ((2 ^ n) ^ 2 + 1) - ((2 ^ n) ^ 2 - 1) := Nat.dvd_sub h hq1
  have h2 : (2 ^ n) ^ 2 + 1 - ((2 ^ n) ^ 2 - 1) = 2 := by
    have h3 : 1 ≤ (2 ^ n) ^ 2 := by
      have h4 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      nlinarith
    omega
  rw [h2] at h1
  have h3 : 3 ≤ n := (s13_odd_three_le_of_isSz hSz).2
  exact (CFSG.RankThree.PartOne.K1320.prime_ne_two_of_dvd_two_pow_sub_one (f := n) (by omega) hrdvd)
    ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h1)

theorem exists_conj_le_normalizer_inf_of_isL2_bar2 {L U X : Subgroup G} {n r : ℕ}
    (hL2 : IsL2 (Bar2 L) n) (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf U L)
    (hr : r.Prime) (hrdvd : r ∣ 2 ^ n - 1) (hXL : X ≤ L) (hXcard : Nat.card X = r) :
    ∃ g ∈ L, X.map (MulAut.conj g).toMonoidHom ≤ L ⊓ Subgroup.normalizer (U : Set G) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hX : IsPGroup r X :=
    IsPGroup.of_card (n := 1) (by rw [hXcard, pow_one])
  exact CFSG.LieType.Chevalley.exists_conj_le_of_not_dvd_index hXL hX
    (not_dvd_relIndex_inf_normalizer_of_isL2_bar2 hL2 hSyl hr hrdvd)

theorem exists_conj_le_normalizer_inf_of_isSz_bar2
    {L U X : Subgroup G} {n r : ℕ}
    (hSz : IsSz (Bar2 L) n) (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf U L)
    (hr : r.Prime) (hrdvd : r ∣ 2 ^ n - 1) (hXL : X ≤ L) (hXcard : Nat.card X = r) :
    ∃ g ∈ L, X.map (MulAut.conj g).toMonoidHom ≤ L ⊓ Subgroup.normalizer (U : Set G) := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hX : IsPGroup r X :=
    IsPGroup.of_card (n := 1) (by rw [hXcard, pow_one])
  exact CFSG.LieType.Chevalley.exists_conj_le_of_not_dvd_index hXL hX
    (not_dvd_relIndex_inf_normalizer_of_isSz_bar2 hSz hSyl hr hrdvd)

theorem powerMap_of_isSz_bar2
    {L T : Subgroup G} {n : ℕ} (hSz : IsSz (Bar2 L) n)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hT2 : IsPGroup 2 T)
    (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (L ⊓ T) L) {t : G} (htT : t ∈ T) :
    ∃ j : ℕ, ∀ b ∈ L ⊓ Subgroup.normalizer (L ⊓ T : Set G),
      t * b * t⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ L ⊓ T := by
  refine ⟨0, fun b hb => ?_⟩
  simp only [pow_zero, pow_one]
  have htL : t ∈ Subgroup.normalizer (L : Set G) := hTL htT
  have htU : t ∈ Subgroup.normalizer ((L ⊓ T : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact ⟨(Subgroup.mem_normalizer_iff.mp htL x).mp hx.1,
        T.mul_mem (T.mul_mem htT hx.2) (T.inv_mem htT)⟩
    · intro hx
      refine ⟨(Subgroup.mem_normalizer_iff.mp htL x).mpr hx.1, ?_⟩
      have h := T.mul_mem (T.mul_mem (T.inv_mem htT) hx.2) htT
      simpa [mul_assoc] using h
  obtain ⟨m, hm⟩ := hT2 ⟨t, htT⟩
  have htpow : t ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  let tN : ↥(Subgroup.normalizer (L : Set G)) := ⟨t, htL⟩
  let α : MulAut (Bar2 L) := CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L tN
  have hαpow : α ^ 2 ^ m = 1 := by
    calc α ^ 2 ^ m = CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L (tN ^ 2 ^ m) :=
          (map_pow _ _ _).symm
      _ = CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L 1 := by
          congr 1
          exact Subtype.ext htpow
      _ = 1 := map_one _
  have hSzM : CFSG.Blueprint.SuzukiModel (Bar2 L) 2 n :=
    (CFSG.Blueprint.LieModel.suzukiModel hSz).2
  obtain ⟨q, hq⟩ := CFSG.Quasithin.H13.szTwoAutInnerFact (Bar2 L) n hSzM α ⟨m, hαpow⟩
  let W : Subgroup (Bar2 L) :=
    ((L ⊓ T).subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L))
  have hWtop : CFSG.QuasithinUnique.IsSylowTwoOf
      ((L ⊓ T).subgroupOf L) (⊤ : Subgroup ↥L) :=
    CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hSyl
  have hW : CFSG.QuasithinUnique.IsSylowTwoOf W ⊤ :=
    CFSG.Quasithin.A312.isSylowTwoOf_top_map (QuotientGroup.mk' (pCore 2 ↥L))
      (QuotientGroup.mk'_surjective _) hWtop
  have hαW : W.map α.toMonoidHom = W := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
      have huU : (u : G) ∈ L ⊓ T := Subgroup.mem_subgroupOf.mp hu
      have htu : t * (u : G) * t⁻¹ ∈ L ⊓ T :=
        (Subgroup.mem_normalizer_iff.mp htU (u : G)).mp huU
      let u' : ↥L := ⟨t * (u : G) * t⁻¹, htu.1⟩
      have hu' : u' ∈ (L ⊓ T).subgroupOf L := htu
      have himg : QuotientGroup.mk' (pCore 2 ↥L) u' ∈ W :=
        Subgroup.mem_map.mpr ⟨u', hu', rfl⟩
      have heq : α (QuotientGroup.mk u) = QuotientGroup.mk' (pCore 2 ↥L) u' := by
        rw [show α = CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L tN from rfl,
          CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_mk]
        rw [show (Subgroup.normalizerMonoidHom L tN) u = u' from Subtype.ext rfl]
        rfl
      change α (QuotientGroup.mk u) ∈ W
      rw [heq]
      exact himg
    · rw [Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective]
  have hqW : W.map (MulAut.conj q).toMonoidHom = W := by
    rw [← hq]
    exact hαW
  have hqN : q ∈ Subgroup.normalizer (W : Set (Bar2 L)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hqW
  have hcenter : Subgroup.center (Bar2 L) = ⊥ := by
    have hsimple : IsSimpleGroup (Bar2 L) :=
      isSimpleGroup_bar2_of_isL2_or_isSz (Or.inr hSz)
    have hperf : Group.IsPerfect (Bar2 L) :=
      isPerfect_bar2_of_isL2_or_isSz (Or.inr hSz)
    haveI : Nontrivial (Bar2 L) :=
      CFSG.ComponentClassification.Quasisimple.nontrivial
        (CFSG.ComponentClassification.Quasisimple.simple_of_perfect (Bar2 L))
    have hnc : ∃ a b : Bar2 L, a * b ≠ b * a := by
      by_contra h
      push Not at h
      exact (Group.IsPerfect.not_isMulCommutative (Bar2 L)) (IsMulCommutative.mk ⟨h⟩)
    exact CFSG.SignalizerFunctorTheorem.CatalogBridge.center_eq_bot_of_isSimpleGroup_of_noncomm
      hsimple hnc
  have hqpow : q ^ 2 ^ m = 1 := by
    have h1 : (MulAut.conj q) ^ 2 ^ m = 1 := by rw [← hq]; exact hαpow
    have h2 : MulAut.conj (q ^ 2 ^ m) = 1 := by
      calc MulAut.conj (q ^ 2 ^ m) = (MulAut.conj q) ^ 2 ^ m := map_pow _ _ _
        _ = 1 := h1
    have hcent : q ^ 2 ^ m ∈ Subgroup.center (Bar2 L) := by
      rw [Subgroup.mem_center_iff]
      intro y
      have hy := congrArg (fun φ : MulAut (Bar2 L) => φ y) h2
      simp only [MulAut.conj_apply, MulAut.one_apply] at hy
      calc y * q ^ 2 ^ m = (q ^ 2 ^ m * y * (q ^ 2 ^ m)⁻¹) * q ^ 2 ^ m := by rw [hy]
        _ = q ^ 2 ^ m * y := by group
    rw [hcenter] at hcent
    exact Subgroup.mem_bot.mp hcent
  have hqmem : q ∈ W :=
    CFSG.Quasithin.H13.KGHe.mem_of_mem_normalizer_of_pow hW (Subgroup.mem_top q) hqN hqpow
  have hbL : b ∈ L := hb.1
  have hbU : b ∈ Subgroup.normalizer ((L ⊓ T : Subgroup G) : Set G) := hb.2
  have hbW : W.map (MulAut.conj (QuotientGroup.mk (⟨b, hbL⟩ : ↥L))).toMonoidHom = W := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
      have huU : (u : G) ∈ L ⊓ T := Subgroup.mem_subgroupOf.mp hu
      have hbu : b * (u : G) * b⁻¹ ∈ L ⊓ T :=
        (Subgroup.mem_normalizer_iff.mp hbU (u : G)).mp huU
      let u' : ↥L := ⟨b * (u : G) * b⁻¹, hbu.1⟩
      have hu' : u' ∈ (L ⊓ T).subgroupOf L := hbu
      have himg : QuotientGroup.mk' (pCore 2 ↥L) u' ∈ W :=
        Subgroup.mem_map.mpr ⟨u', hu', rfl⟩
      have heq : MulAut.conj (QuotientGroup.mk (⟨b, hbL⟩ : ↥L)) (QuotientGroup.mk u) =
          QuotientGroup.mk' (pCore 2 ↥L) u' := by
        rw [show (MulAut.conj (QuotientGroup.mk (⟨b, hbL⟩ : ↥L)) :
            MulAut (Bar2 L)) = CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L
              ⟨b, Subgroup.le_normalizer hbL⟩ by
          exact (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_inner L b hbL).symm,
          CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_mk]
        rw [show (Subgroup.normalizerMonoidHom L ⟨b, Subgroup.le_normalizer hbL⟩) u = u'
          from Subtype.ext rfl]
        rfl
      change MulAut.conj (QuotientGroup.mk (⟨b, hbL⟩ : ↥L)) (QuotientGroup.mk u) ∈ W
      rw [heq]
      exact himg
    · rw [Subgroup.card_map_of_injective (f := (MulAut.conj _).toMonoidHom)
        (MulAut.conj _).injective]
  have hbN : (QuotientGroup.mk (⟨b, hbL⟩ : ↥L) : Bar2 L) ∈
      Subgroup.normalizer (W : Set (Bar2 L)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hbW
  have hcommW : q * (QuotientGroup.mk (⟨b, hbL⟩ : ↥L) : Bar2 L) * q⁻¹ *
      (QuotientGroup.mk (⟨b, hbL⟩ : ↥L) : Bar2 L)⁻¹ ∈ W := by
    have h1 : (QuotientGroup.mk (⟨b, hbL⟩ : ↥L) : Bar2 L) * q *
        (QuotientGroup.mk (⟨b, hbL⟩ : ↥L) : Bar2 L)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp hbN q).mp hqmem
    have h2 : ((QuotientGroup.mk (⟨b, hbL⟩ : ↥L) : Bar2 L) * q *
        (QuotientGroup.mk (⟨b, hbL⟩ : ↥L) : Bar2 L)⁻¹) * q⁻¹ ∈ W :=
      W.mul_mem h1 (W.inv_mem hqmem)
    have h3 : q * (QuotientGroup.mk (⟨b, hbL⟩ : ↥L) : Bar2 L) * q⁻¹ *
        (QuotientGroup.mk (⟨b, hbL⟩ : ↥L) : Bar2 L)⁻¹ =
        (((QuotientGroup.mk (⟨b, hbL⟩ : ↥L) : Bar2 L) * q *
          (QuotientGroup.mk (⟨b, hbL⟩ : ↥L) : Bar2 L)⁻¹) * q⁻¹)⁻¹ := by group
    rw [h3]
    exact W.inv_mem h2
  have htb : t * b * t⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp htL b).mp hbL
  have hxL : t * b * t⁻¹ * b⁻¹ ∈ L := L.mul_mem htb (L.inv_mem hbL)
  have hclass : QuotientGroup.mk' (pCore 2 ↥L) (⟨t * b * t⁻¹ * b⁻¹, hxL⟩ : ↥L) =
      q * (QuotientGroup.mk' (pCore 2 ↥L) (⟨b, hbL⟩ : ↥L)) * q⁻¹ *
        (QuotientGroup.mk' (pCore 2 ↥L) (⟨b, hbL⟩ : ↥L))⁻¹ := by
    have hbt : QuotientGroup.mk' (pCore 2 ↥L) (⟨t * b * t⁻¹ * b⁻¹, hxL⟩ : ↥L) =
        (QuotientGroup.mk' (pCore 2 ↥L) (⟨t * b * t⁻¹, htb⟩ : ↥L)) *
        (QuotientGroup.mk' (pCore 2 ↥L) (⟨b, hbL⟩ : ↥L))⁻¹ := by
      calc QuotientGroup.mk' (pCore 2 ↥L) (⟨t * b * t⁻¹ * b⁻¹, hxL⟩ : ↥L)
          = QuotientGroup.mk' (pCore 2 ↥L)
              ((⟨t * b * t⁻¹, htb⟩ : ↥L) * (⟨b, hbL⟩ : ↥L)⁻¹) := by
            congr 1
        _ = (QuotientGroup.mk' (pCore 2 ↥L) (⟨t * b * t⁻¹, htb⟩ : ↥L)) *
              (QuotientGroup.mk' (pCore 2 ↥L) (⟨b, hbL⟩ : ↥L))⁻¹ := by
            rw [map_mul, map_inv]
    rw [hbt]
    have htbar : (QuotientGroup.mk' (pCore 2 ↥L) (⟨t * b * t⁻¹, htb⟩ : ↥L)) =
        α (QuotientGroup.mk' (pCore 2 ↥L) (⟨b, hbL⟩ : ↥L)) := by
      rw [show α = CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L tN from rfl]
      change QuotientGroup.mk (⟨t * b * t⁻¹, htb⟩ : ↥L) =
        CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L tN
          (QuotientGroup.mk (⟨b, hbL⟩ : ↥L))
      rw [CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_mk]
      rfl
    rw [htbar, hq]
    rfl
  have hxW : QuotientGroup.mk' (pCore 2 ↥L) (⟨t * b * t⁻¹ * b⁻¹, hxL⟩ : ↥L) ∈ W := by
    rw [hclass]
    simpa [QuotientGroup.mk'_apply] using hcommW
  have hxU : (⟨t * b * t⁻¹ * b⁻¹, hxL⟩ : ↥L) ∈ (L ⊓ T).subgroupOf L := by
    have hker_le : (QuotientGroup.mk' (pCore 2 ↥L)).ker ≤ (L ⊓ T).subgroupOf L := by
      rw [QuotientGroup.ker_mk']
      exact CFSG.Quasithin.pCore_two_le_subgroupOf hSyl
    have hx' : (⟨t * b * t⁻¹ * b⁻¹, hxL⟩ : ↥L) ∈
        (((L ⊓ T).subgroupOf L).map (QuotientGroup.mk' (pCore 2 ↥L))).comap
          (QuotientGroup.mk' (pCore 2 ↥L)) := hxW
    rwa [Subgroup.comap_map_eq_self hker_le] at hx'
  exact Subgroup.mem_subgroupOf.mp hxU

theorem le_normalizer_of_powerMap {X B T U : Subgroup G} {s r : ℕ}
    (hXB : X ≤ B) (hXU : X ≤ Subgroup.normalizer (U : Set G))
    (hTU : T ≤ Subgroup.normalizer (U : Set G)) (hUT : U ≤ T)
    (hU2 : IsPGroup 2 U) (hT2 : IsPGroup 2 T)
    (hpow : ∀ t ∈ T, ∃ j : ℕ, ∀ b ∈ B,
      t * b * t⁻¹ * (b ^ 2 ^ j)⁻¹ ∈ U)
    (hs : Odd s) (hr : r.Prime) (hrdvd : r ∣ 2 ^ s - 1)
    (hXr : ∀ x ∈ X, x ≠ 1 → orderOf x = r) :
    X ≤ Subgroup.normalizer (T : Set G) := by
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1]
    exact Subgroup.one_mem _
  · have hxr : orderOf x = r := hXr x hx hx1
    have hxU : x ∈ Subgroup.normalizer (U : Set G) := hXU hx
    have hconj : ∀ t ∈ T, x⁻¹ * t * x ∈ T := by
      intro t ht
      obtain ⟨e, he⟩ := hT2 ⟨t, ht⟩
      have hte : t ^ 2 ^ e = 1 := by simpa using congrArg Subtype.val he
      obtain ⟨j, hj⟩ := hpow t ht
      have hmem := inv_mul_conj_mem_of_powerMap (Y := G) (B := B) (U := U) (t := t) (x := x)
        (hTU ht) hxU hU2 hte hj hs hr hrdvd (hXB hx) hxr
      have heq : x⁻¹ * t * x = (x⁻¹ * (t * x * t⁻¹)) * t := by group
      rw [heq]
      exact T.mul_mem (hUT hmem) ht
    have h := Subgroup.mem_normalizer_fintype (S := (T : Set G)) (x := x⁻¹)
      fun t ht => by simpa using hconj t ht
    simpa using inv_mem h

theorem exists_conj_le_normalizer_T_of_isL2_bar2 {L T X : Subgroup G} {n s r : ℕ}
    (hL2 : IsL2 (Bar2 L) n) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hT2 : IsPGroup 2 T) (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (L ⊓ T) L)
    (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime) (hrdvd : r ∣ 2 ^ s - 1)
    (hXL : X ≤ L) (hXcard : Nat.card X = r) :
    ∃ g ∈ L, X.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (T : Set G) := by
  have hrdvdn : r ∣ 2 ^ n - 1 :=
    hrdvd.trans (Nat.pow_sub_one_dvd_pow_sub_one (x := 2) hsn)
  obtain ⟨g, hgL, hXB⟩ :=
    exists_conj_le_normalizer_inf_of_isL2_bar2 hL2 hSyl hr hrdvdn hXL hXcard
  refine ⟨g, hgL, ?_⟩
  have hXr : ∀ x ∈ X.map (MulAut.conj g).toMonoidHom, x ≠ 1 → orderOf x = r := by
    rintro x ⟨y, hy, rfl⟩ hx1
    change orderOf (MulAut.conj g y) = r
    rw [MulAut.conj_apply]
    have hord : orderOf (g * y * g⁻¹) = orderOf y := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    rw [hord]
    have hydvd : orderOf y ∣ r := by
      rw [← hXcard]; exact Subgroup.orderOf_dvd_natCard X hy
    rcases (Nat.dvd_prime hr).mp hydvd with h | h
    · have hy1 : y = 1 := orderOf_eq_one_iff.mp h
      exact absurd (by simp [hy1]) hx1
    · exact h
  have hTU : T ≤ Subgroup.normalizer ((L ⊓ T : Subgroup G) : Set G) :=
    (le_inf hTL (Subgroup.le_normalizer (H := T))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  refine le_normalizer_of_powerMap (B := L ⊓ Subgroup.normalizer ((L ⊓ T : Subgroup G) : Set G))
    (U := L ⊓ T) hXB ?_ hTU inf_le_right hSyl.2.1 hT2 ?_ hs hr hrdvd hXr
  · exact hXB.trans inf_le_right
  · intro t ht
    obtain ⟨j, hj⟩ := powerMap_of_isL2_bar2 hL2 hSyl (t := t) ⟨hTL ht, (hTU ht)⟩
    exact ⟨j, hj⟩

theorem exists_conj_le_normalizer_T_of_isSz_bar2
    {L T X : Subgroup G} {n s r : ℕ}
    (hSz : IsSz (Bar2 L) n) (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hT2 : IsPGroup 2 T) (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf (L ⊓ T) L)
    (hs : Odd s) (hsn : s ∣ n) (hr : r.Prime) (hrdvd : r ∣ 2 ^ s - 1)
    (hXL : X ≤ L) (hXcard : Nat.card X = r) :
    ∃ g ∈ L, X.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (T : Set G) := by
  have hrdvdn : r ∣ 2 ^ n - 1 :=
    hrdvd.trans (Nat.pow_sub_one_dvd_pow_sub_one (x := 2) hsn)
  obtain ⟨g, hgL, hXB⟩ :=
    exists_conj_le_normalizer_inf_of_isSz_bar2 hSz hSyl hr hrdvdn hXL hXcard
  refine ⟨g, hgL, ?_⟩
  have hXr : ∀ x ∈ X.map (MulAut.conj g).toMonoidHom, x ≠ 1 → orderOf x = r := by
    rintro x ⟨y, hy, rfl⟩ hx1
    change orderOf (MulAut.conj g y) = r
    rw [MulAut.conj_apply]
    have hord : orderOf (g * y * g⁻¹) = orderOf y := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    rw [hord]
    have hydvd : orderOf y ∣ r := by
      rw [← hXcard]; exact Subgroup.orderOf_dvd_natCard X hy
    rcases (Nat.dvd_prime hr).mp hydvd with h | h
    · have hy1 : y = 1 := orderOf_eq_one_iff.mp h
      exact absurd (by simp [hy1]) hx1
    · exact h
  have hTU : T ≤ Subgroup.normalizer ((L ⊓ T : Subgroup G) : Set G) :=
    (le_inf hTL (Subgroup.le_normalizer (H := T))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  refine le_normalizer_of_powerMap (B := L ⊓ Subgroup.normalizer ((L ⊓ T : Subgroup G) : Set G))
    (U := L ⊓ T) hXB ?_ hTU inf_le_right hSyl.2.1 hT2 ?_ hs hr hrdvd hXr
  · exact hXB.trans inf_le_right
  · intro t ht
    exact powerMap_of_isSz_bar2 hSz hTL hT2 hSyl ht

theorem exists_conj_eq_of_card_prime {U V P : Subgroup G} {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hU : Nat.card U = r) (hV : Nat.card V = r)
    (hP : IsPGroup 2 P) (hUP : U ≤ Subgroup.normalizer (P : Set G))
    (hVY : V ≤ U ⊔ P) :
    ∃ p ∈ P, V = U.map (MulAut.conj p).toMonoidHom := by
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := U ⊔ P with hY
  have hU2 : IsPGroup r U := IsPGroup.of_card (n := 1) (by rw [hU, pow_one])
  have hV2 : IsPGroup r V := IsPGroup.of_card (n := 1) (by rw [hV, pow_one])
  have hUP1 : P ⊓ U = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hP
    rw [hm, hU]
    exact Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr (hr.odd_of_ne_two hr2))
  have hcardY : Nat.card Y = r * Nat.card P := by
    have h1 : P.relIndex (U ⊔ P) = P.relIndex U :=
      CFSG.Quasithin.A4.relIndex_sup_eq_of_le_normalizer' hUP
    have h2 := Subgroup.relIndex_mul_card P U
    rw [hUP1, Subgroup.card_bot, mul_one, hU] at h2
    have h3 := Subgroup.relIndex_mul_card P (U ⊔ P)
    rw [inf_eq_left.mpr le_sup_right, h1, h2] at h3
    exact h3.symm
  have hrel : U.relIndex Y = Nat.card P := by
    have h := Subgroup.relIndex_mul_card U Y
    rw [inf_eq_left.mpr le_sup_left, hcardY, hU] at h
    rw [mul_comm (U.relIndex Y) r] at h
    exact Nat.mul_left_cancel hr.pos h
  have hnot : ¬ r ∣ U.relIndex Y := by
    rw [hrel]
    intro hd
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hP
    rw [hm] at hd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hd))
  obtain ⟨g, hgY, hg⟩ :=
    CFSG.Walter.Huppert.exists_conj_eq (R := Y) (T := U) (T₂ := V)
      le_sup_left hVY hU2 hV2 hnot (by rw [hV, hU])
  have hgY' : g ∈ P ⊔ U := by
    rw [hY, sup_comm] at hgY
    exact hgY
  obtain ⟨p, hp, u, hu, hgpu⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hUP).mp hgY'
  have hUu : U.map (MulAut.conj u).toMonoidHom = U :=
    CFSG.Quasithin.A38.map_conj_eq_iff.mpr (Subgroup.le_normalizer hu)
  have hconj : U.map (MulAut.conj g).toMonoidHom =
      U.map (MulAut.conj p).toMonoidHom := by
    have e1 : (MulAut.conj g).toMonoidHom =
        (MulAut.conj p).toMonoidHom.comp (MulAut.conj u).toMonoidHom := by
      ext x
      simp [hgpu, MulAut.conj_apply, mul_assoc]
    rw [e1, ← Subgroup.map_map, hUu]
  refine ⟨p, hp, ?_⟩
  rw [hg, hconj]

theorem exists_inverted_of_inverts_mod_pCore {L X : Subgroup G} {r : ℕ}
    (hXL : X ≤ L) (hXcard : Nat.card X = r) (hr : r.Prime) (hr2 : r ≠ 2)
    {k : G} (hkL : k ∈ L)
    (hkinv : ∀ x ∈ X, k * x * k⁻¹ * x ∈ pCoreOf 2 L) :
    ∃ h ∈ L, ∀ x ∈ X, h * x * h⁻¹ = x⁻¹ := by
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  let Q := pCoreOf 2 L
  have hQL : Q ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hQ2 : IsPGroup 2 Q :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).map L.subtype
  have hQn : (Q.subgroupOf L).Normal := by
    rw [show Q.subgroupOf L = CFSG.pCore 2 ↥L from
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective _]
    exact CFSG.LieType.BorelTits.pCore_normal 2
  have hLN : L ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQL).mp hQn
  have hXQ : X ≤ Subgroup.normalizer (Q : Set G) := hXL.trans hLN
  let V : Subgroup G := X.map (MulAut.conj k).toMonoidHom
  have hVC : V ≤ X ⊔ Q := by
    rintro _ ⟨x, hx, rfl⟩
    change k * x * k⁻¹ ∈ X ⊔ Q
    have hxc : k * x * k⁻¹ = (k * x * k⁻¹ * x) * x⁻¹ := by group
    rw [hxc]
    exact (X ⊔ Q).mul_mem (Subgroup.mem_sup_right (hkinv x hx))
      ((X ⊔ Q).inv_mem (Subgroup.mem_sup_left hx))
  have hVcard : Nat.card V = r := by
    rw [show Nat.card V = Nat.card X from
      Subgroup.card_map_of_injective (MulAut.conj k).injective, hXcard]
  obtain ⟨p, hpQ, hpV⟩ :=
    exists_conj_eq_of_card_prime hr hr2 hXcard hVcard hQ2 hXQ hVC
  have hXQbot : X ⊓ Q = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard ?_).eq_bot
    rw [hXcard]
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hQ2
    rw [hm]
    exact (Nat.coprime_two_left.mpr hrodd).symm.pow_right m
  refine ⟨p⁻¹ * k, L.mul_mem (L.inv_mem (hQL hpQ)) hkL, ?_⟩
  intro x hx
  have hmemV : k * x * k⁻¹ ∈ V := ⟨x, hx, rfl⟩
  rw [hpV] at hmemV
  obtain ⟨y, hyX, hyeq⟩ := (Subgroup.mem_map (f := (MulAut.conj p).toMonoidHom) (K := X)).mp hmemV
  have hyval : y = p⁻¹ * (k * x * k⁻¹) * p := by
    rw [show (MulEquiv.toMonoidHom (MulAut.conj p)) y = p * y * p⁻¹ from
      MulAut.conj_apply p y] at hyeq
    rw [← hyeq]
    group
  have hxp : x⁻¹ * p * x ∈ Q := by
    simpa using (Subgroup.mem_normalizer_iff.mp (hXQ (X.inv_mem hx)) p).mp hpQ
  have hcQ : k * x * k⁻¹ * x ∈ Q := hkinv x hx
  have hyxQ : y * x ∈ Q := by
    have h1 : p⁻¹ * (k * x * k⁻¹ * x) ∈ Q := Q.mul_mem (Q.inv_mem hpQ) hcQ
    have hkx : k * x * k⁻¹ = (k * x * k⁻¹ * x) * x⁻¹ := by group
    have heq : y * x = (p⁻¹ * (k * x * k⁻¹ * x)) * (x⁻¹ * p * x) := by
      rw [hyval, hkx]
      group
    rw [heq]
    exact Q.mul_mem h1 hxp
  have hyxX : y * x ∈ X := X.mul_mem hyX hx
  have hyx1 : y * x = 1 := by
    have h : y * x ∈ X ⊓ Q := ⟨hyxX, hyxQ⟩
    rw [hXQbot] at h
    exact Subgroup.mem_bot.mp h
  have hy : y = x⁻¹ := by
    have h := congrArg (fun z => z * x⁻¹) hyx1
    simpa [mul_assoc] using h
  calc (p⁻¹ * k) * x * (p⁻¹ * k)⁻¹ = p⁻¹ * (k * x * k⁻¹) * p := by group
    _ = y := hyval.symm
    _ = x⁻¹ := hy

theorem exists_involution_inverts_of_isL2
    {L : Subgroup G} {n r : ℕ} (hL2 : IsL2 (Bar2 L) n)
    {x : Bar2 L} (hr : r.Prime) (hr2 : r ≠ 2) (hxr : orderOf x = r) :
    ∃ s : Bar2 L, orderOf s = 2 ∧ s * x * s⁻¹ = x⁻¹ := by
  obtain ⟨-, K, hfield, hfin, hKcard, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel hL2 (by decide)
  letI := hfield
  letI := hfin
  have hf : 2 ≤ n := s13_two_le_of_isL2 hL2
  let e' : Bar2 L ≃* CFSG.BenderSuzuki.MatrixGroups.PSL2MatrixGroup K :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hstruct :=
    oddPrimeInvertersAndSplitFusion_of_mulEquiv_psl2 hf hKcard e'
  obtain ⟨s, hs2, hsinv⟩ := hstruct.exists_involution_inverts x (by rwa [hxr]) (by rwa [hxr])
  exact ⟨s, hs2, hsinv⟩

theorem exists_involution_inverts_of_isSz
    {L : Subgroup G} {n r : ℕ} (hSz : IsSz (Bar2 L) n)
    {x : Bar2 L} (hr : r.Prime) (hr2 : r ≠ 2) (hxr : orderOf x = r) :
    ∃ s : Bar2 L, orderOf s = 2 ∧ s * x * s⁻¹ = x⁻¹ := by
  have hM : CFSG.Blueprint.SuzukiModel (Bar2 L) 2 n :=
    (CFSG.Blueprint.LieModel.suzukiModel hSz).2
  obtain ⟨-, a, ha, K, hfield, hfin, hf, hKcard, ⟨e0⟩⟩ := hM
  letI := hfield
  letI := hfin
  have hKa : Nat.card K = 2 ^ (2 * a + 1) := by rw [hKcard, hf]
  let e : Bar2 L ≃* CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a :=
    e0.trans (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup
      (a := a) hKa)
  have hstruct :=
    oddPrimeInvertersAndSplitFusion_of_mulEquiv_suzukiMatrixGroup ha e
  obtain ⟨s, hs2, hsinv⟩ := hstruct.exists_involution_inverts x (by rwa [hxr]) (by rwa [hxr])
  exact ⟨s, hs2, hsinv⟩

theorem exists_involution_inverts_of_shape
    {L : Subgroup G} {n r : ℕ}
    (hshape : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n)
    {x : Bar2 L} (hr : r.Prime) (hr2 : r ≠ 2) (hxr : orderOf x = r) :
    ∃ s : Bar2 L, orderOf s = 2 ∧ s * x * s⁻¹ = x⁻¹ := by
  rcases hshape with h | h
  · exact exists_involution_inverts_of_isL2 h hr hr2 hxr
  · exact exists_involution_inverts_of_isSz h hr hr2 hxr

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
