module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.PCore.PrimeCoreImages
public import CFSG.RankThree.PartTwo.Sec14.Item14Tools
public import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec17.Item17Q0ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec15.ThmC

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem thmc_top_le_oPrimeResidual {Y : Subgroup G} (hY3 : Y = oPrimeResidualOf 3 Y) :
    (⊤ : Subgroup ↥Y) ≤ CFSG.GH74.GLS.oPrimeResidual 3 ↥Y := by
  intro x _
  have hx : (x : G) ∈ oPrimeResidualOf 3 Y := by
    rw [← hY3]
    exact x.2
  have hx' : (x : G) ∈ (CFSG.GH74.GLS.oPrimeResidual 3 ↥Y).map Y.subtype := hx
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx'
  have hzx' : z = x := Subtype.ext hzx
  rw [← hzx']
  exact hz

private theorem thmc_coprime_three_card_pCore (Y : Subgroup G) :
    Nat.Coprime 3 (Nat.card (CFSG.pCore 2 ↥Y)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥Y))
  rw [hn]
  exact Nat.Coprime.pow_right n (by norm_num)

private theorem thmc_commutator_Y_zpowers_le {Y V : Subgroup G} {x : G} (hVY : V ≤ Y)
    (hYV : Y ≤ Subgroup.normalizer (V : Set G)) (hV2 : IsPGroup 2 V)
    (hY3 : Y = oPrimeResidualOf 3 Y) (hxV : x ∈ Subgroup.normalizer (V : Set G))
    (hYx : ∀ y ∈ Y, ⁅y, x⁆ ∈ V) : ⁅Y, Subgroup.zpowers x⁆ ≤ ⁅V, Y⁆ := by
  set N := ⁅V, Y⁆ with hN
  have hNV : N ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp hYV
  have hNY : N ≤ Y := hNV.trans hVY
  have hYN : Y ≤ Subgroup.normalizer (N : Set G) :=
    CFSG.RankThree.PartTwo.Sec14.le_normalizer_commutator (A := Y) hYV Subgroup.le_normalizer
  have hxs : Subgroup.zpowers x ≤ CFSG.RankThree.PartTwo.Sec14.commutatorInSubgroup Y V :=
    Subgroup.zpowers_le.mpr (CFSG.RankThree.PartTwo.Sec14.mem_commutatorInSubgroup.mpr ⟨hxV, hYx⟩)
  have hYT : Y ≤ CFSG.RankThree.PartTwo.Sec14.commutatorInSubgroup (Subgroup.zpowers x) N := by
    refine hY3.le.trans ?_
    rw [CFSG.RankThree.PartTwo.Sec14.oPrimeResidualOf_eq_closure, Subgroup.closure_le]
    rintro y ⟨hy, k, hyk⟩
    refine CFSG.RankThree.PartTwo.Sec14.mem_commutatorInSubgroup.mpr ⟨hYN hy, fun q hq => ?_⟩
    have h := CFSG.RankThree.PartTwo.Sec17.Proof17Q0.commutatorElement_mem_of_pow_three hVY hNY
      hYN le_rfl hV2 hy hyk
      ((CFSG.RankThree.PartTwo.Sec14.mem_commutatorInSubgroup.mp (hxs hq)).2 y hy)
    rw [← commutatorElement_inv]
    exact N.inv_mem h
  rw [Subgroup.commutator_le]
  intro y hy q hq
  have h := (CFSG.RankThree.PartTwo.Sec14.mem_commutatorInSubgroup.mp (hYT hy)).2 q hq
  rw [← commutatorElement_inv]
  exact N.inv_mem h

theorem lemma7_perfect {A : Subgroup G} {Y : Subgroup G} (hY : Y ∈ scriptY0 A (lB A)) :
    Group.IsPerfect ↥Y := by
  obtain ⟨⟨-, hY3, -, hQ⟩, -⟩ := hY
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQperf : Group.IsPerfect (↥Y ⧸ CFSG.pCore 2 ↥Y) := hQ.1
  have hmapTop : Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) ⁅(⊤ : Subgroup ↥Y), ⊤⁆ = ⊤ := by
    rw [Subgroup.map_commutator,
      Subgroup.map_top_of_surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))
        (QuotientGroup.mk'_surjective _)]
    exact Group.isPerfect_def.mp hQperf
  have hsup : (⊤ : Subgroup ↥Y) ≤ ⁅(⊤ : Subgroup ↥Y), ⊤⁆ ⊔ CFSG.pCore 2 ↥Y := by
    intro y _
    have hy : QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y ∈
        Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) ⁅(⊤ : Subgroup ↥Y), ⊤⁆ := by
      rw [hmapTop]
      exact Subgroup.mem_top _
    obtain ⟨m, hm, hmy⟩ := Subgroup.mem_map.mp hy
    have hk : m⁻¹ * y ∈ CFSG.pCore 2 ↥Y := by
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥Y), MonoidHom.mem_ker, map_mul, map_inv, hmy,
        inv_mul_cancel]
    have hmk := Subgroup.mul_mem_sup hm hk
    rwa [mul_inv_cancel_left] at hmk
  have hcop : Nat.Coprime 3 (Nat.card (CFSG.pCore 2 ↥Y)) := thmc_coprime_three_card_pCore Y
  have hCD : CFSG.pCore 2 ↥Y ≤ Subgroup.normalizer
      ((⁅(⊤ : Subgroup ↥Y), ⊤⁆ : Subgroup ↥Y) : Set ↥Y) :=
    Subgroup.le_normalizer_of_normal
  have hsmall : CFSG.GH74.GLS.oPrimeResidual 3 ↥Y ≤ ⁅(⊤ : Subgroup ↥Y), ⊤⁆ := by
    unfold CFSG.GH74.GLS.oPrimeResidual
    rw [Subgroup.closure_le]
    rintro x ⟨k, hk⟩
    exact CFSG.RankThree.PartTwo.Sec14.mem_left_of_pow_prime_pow Nat.prime_three hCD hcop
      (hsup (Subgroup.mem_top x)) hk
  have htop : (⊤ : Subgroup ↥Y) ≤ ⁅(⊤ : Subgroup ↥Y), ⊤⁆ :=
    (thmc_top_le_oPrimeResidual hY3).trans hsmall
  exact Group.isPerfect_def.mpr (le_antisymm le_top htop)

theorem lemma7_center {A : Subgroup G} {Y : Subgroup G} (hY : Y ∈ scriptY0 A (lB A)) :
    Odd (Nat.card (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y))) ∧
      Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) (CFSG.pPrimeCore 3 ↥Y) =
        CFSG.pPrimeCore 3 (↥Y ⧸ CFSG.pCore 2 ↥Y) ∧
      CFSG.pPrimeCore 3 (↥Y ⧸ CFSG.pCore 2 ↥Y) ≤ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  obtain ⟨⟨-, hY3, -, hQ⟩, -⟩ := hY
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hker : ¬ 3 ∣ Nat.card (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).ker := by
    rw [QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (thmc_coprime_three_card_pCore Y)
  have hmap : Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) (CFSG.pPrimeCore 3 ↥Y) =
      CFSG.pPrimeCore 3 (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
    (CFSG.prime_complement_kernel_core_preimage (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))
      (QuotientGroup.mk'_surjective _) hker).2
  have hO2 : CFSG.pCore 2 (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊥ :=
    CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hodd : Odd (Nat.card (Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y))) := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    intro h2
    obtain ⟨z, hz⟩ :=
      exists_prime_orderOf_dvd_card' (G := Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y)) 2 h2
    have hzc : (z : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) := z.2
    have hzn : (Subgroup.zpowers (z : ↥Y ⧸ CFSG.pCore 2 ↥Y)).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hzc)
    have hzp : IsPGroup 2 (Subgroup.zpowers (z : ↥Y ⧸ CFSG.pCore 2 ↥Y)) := by
      rw [IsPGroup.iff_card]
      exact ⟨1, by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz, pow_one]⟩
    have hle : Subgroup.zpowers (z : ↥Y ⧸ CFSG.pCore 2 ↥Y) ≤
        CFSG.pCore 2 (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
      le_sSup ⟨hzn, hzp⟩
    rw [hO2, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
    have hz1 : z = 1 := Subtype.ext hle
    rw [hz1, orderOf_one] at hz
    norm_num at hz
  have hcen : CFSG.pPrimeCore 3 (↥Y ⧸ CFSG.pCore 2 ↥Y) ≤
      Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ
        (CFSG.pPrimeCore_normal (p := 3) (G := ↥Y ⧸ CFSG.pCore 2 ↥Y)) with h | h
    · exfalso
      have hcopQ : Nat.Coprime 3 (Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y)) := by
        have := CFSG.pPrimeCore_coprime_card (p := 3) (G := ↥Y ⧸ CFSG.pCore 2 ↥Y)
        rwa [h, Subgroup.card_top] at this
      have hsm : CFSG.GH74.GLS.oPrimeResidual 3 ↥Y ≤ CFSG.pCore 2 ↥Y := by
        unfold CFSG.GH74.GLS.oPrimeResidual
        rw [Subgroup.closure_le]
        rintro x ⟨k, hk⟩
        have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥Y) x ^ 3 ^ k = 1 := by
          rw [← map_pow, hk, map_one]
        have h2 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) x) ∣
            Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
          orderOf_dvd_natCard _
        have h3 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) x) ∣ 3 ^ k :=
          orderOf_dvd_of_pow_eq_one h1
        have hord : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) x) = 1 :=
          Nat.dvd_one.mp ((Nat.Coprime.pow_left k hcopQ).gcd_eq_one ▸ Nat.dvd_gcd h3 h2)
        rw [orderOf_eq_one_iff] at hord
        exact (QuotientGroup.eq_one_iff x).mp hord
      have hall : (⊤ : Subgroup ↥Y) ≤ CFSG.pCore 2 ↥Y :=
        (thmc_top_le_oPrimeResidual hY3).trans hsm
      have hQt : ∀ q : ↥Y ⧸ CFSG.pCore 2 ↥Y, q = 1 := by
        intro q
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
        exact (QuotientGroup.eq_one_iff y).mpr (hall (Subgroup.mem_top y))
      haveI : Nontrivial (↥Y ⧸ CFSG.pCore 2 ↥Y) := CFSG.LocalCores.isQuasisimple_nontrivial hQ
      obtain ⟨p1, p2, hp⟩ := exists_pair_ne (↥Y ⧸ CFSG.pCore 2 ↥Y)
      exact hp ((hQt p1).trans (hQt p2).symm)
    · exact h
  exact ⟨hodd, hmap, hcen⟩

theorem lemma7_centralizes {A : Subgroup G} {Y : Subgroup G} (hY : Y ∈ scriptY0 A (lB A))
    {a : G} (ha : a ∈ A) (hYa : ⁅Y, Subgroup.zpowers a⁆ ≤ pPrimeCoreOf 3 Y) :
    (∀ y ∈ Y, ⁅y, a⁆ ∈ CFSG.Open.pCoreOf 2 Y) ∧
      ⁅Y, Subgroup.zpowers a⁆ ≤ ⁅CFSG.Open.pCoreOf 2 Y, Y⁆ ∧
      ⁅CFSG.Open.pCoreOf 2 Y, Subgroup.zpowers a⁆ ≤ ⁅CFSG.Open.pCoreOf 2 Y, Y⁆ := by
  have hperf := lemma7_perfect hY
  obtain ⟨-, hmap, hcen⟩ := lemma7_center hY
  obtain ⟨⟨⟨-, hAY⟩, hY3, -, -⟩, -⟩ := hY
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmemc : ∀ y : ↥Y, ⁅(y : G), a⁆ ∈ Y := by
    intro y
    have h1 : a * (y : G)⁻¹ * a⁻¹ ∈ Y :=
      (Subgroup.mem_normalizer_iff.mp (hAY ha) _).mp (Y.inv_mem y.2)
    have h2 : ⁅(y : G), a⁆ = (y : G) * (a * (y : G)⁻¹ * a⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact Y.mul_mem y.2 h1
  obtain ⟨c, hc⟩ : ∃ c : ↥Y → ↥Y, ∀ y, (c y : G) = ⁅(y : G), a⁆ :=
    ⟨fun y => ⟨⁅(y : G), a⁆, hmemc y⟩, fun y => rfl⟩
  have hR : ∀ y z : ↥Y, c (y * z) = y * c z * y⁻¹ * c y := by
    intro y z
    apply Subtype.ext
    simp only [hc, Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
    group
  have hcenc : ∀ y : ↥Y, QuotientGroup.mk' (CFSG.pCore 2 ↥Y) (c y) ∈
      Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
    intro y
    have h1 : c y ∈ CFSG.pPrimeCore 3 ↥Y := by
      have h2 : ⁅(y : G), a⁆ ∈ (CFSG.pPrimeCore 3 ↥Y).map Y.subtype :=
        hYa (Subgroup.commutator_mem_commutator y.2 (Subgroup.mem_zpowers a))
      obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp h2
      have hwc : w = c y := Subtype.ext (by rw [hc]; exact hwy)
      rw [← hwc]
      exact hw
    have h3 : QuotientGroup.mk' (CFSG.pCore 2 ↥Y) (c y) ∈
        Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) (CFSG.pPrimeCore 3 ↥Y) :=
      Subgroup.mem_map_of_mem _ h1
    rw [hmap] at h3
    exact hcen h3
  have hcommut : ∀ y z : ↥Y, QuotientGroup.mk' (CFSG.pCore 2 ↥Y) (c (y * z)) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥Y) (c y) * QuotientGroup.mk' (CFSG.pCore 2 ↥Y) (c z) := by
    intro y z
    have hS := Subgroup.mem_center_iff.mp (hcenc z) (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y)
    have hT := Subgroup.mem_center_iff.mp (hcenc y) (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) (c z))
    rw [hR, map_mul, map_mul, map_mul, map_inv, hS, mul_inv_cancel_right]
    exact hT
  obtain ⟨g, hg⟩ : ∃ g : ↥Y →* ↥Y ⧸ CFSG.pCore 2 ↥Y,
      ∀ y, g y = QuotientGroup.mk' (CFSG.pCore 2 ↥Y) (c y) :=
    ⟨MonoidHom.mk' (fun y => QuotientGroup.mk' (CFSG.pCore 2 ↥Y) (c y)) hcommut, fun y => rfl⟩
  have hgcen : ∀ u : ↥Y, g u ∈ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) := fun u => by
    rw [hg]
    exact hcenc u
  have hgc : ⁅(⊤ : Subgroup ↥Y), ⊤⁆ ≤ g.ker := by
    rw [Subgroup.commutator_le]
    intro u _ v _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_commute]
    exact (Subgroup.mem_center_iff.mp (hgcen u) (g v)).symm
  have htop : (⊤ : Subgroup ↥Y) ≤ g.ker := by
    have hperf' : ⁅(⊤ : Subgroup ↥Y), ⊤⁆ = ⊤ := Group.isPerfect_def.mp hperf
    calc (⊤ : Subgroup ↥Y) = ⁅(⊤ : Subgroup ↥Y), ⊤⁆ := hperf'.symm
      _ ≤ g.ker := hgc
  have hk1 : ∀ y : ↥Y, QuotientGroup.mk' (CFSG.pCore 2 ↥Y) (c y) = 1 := fun y => by
    have h := htop (Subgroup.mem_top y)
    rw [MonoidHom.mem_ker, hg] at h
    exact h
  have hi : ∀ y ∈ Y, ⁅y, a⁆ ∈ CFSG.Open.pCoreOf 2 Y := by
    intro y hy
    have h1 : c ⟨y, hy⟩ ∈ CFSG.pCore 2 ↥Y := (QuotientGroup.eq_one_iff _).mp (hk1 ⟨y, hy⟩)
    have h2 : (c ⟨y, hy⟩ : G) ∈ (CFSG.pCore 2 ↥Y).map Y.subtype :=
      Subgroup.mem_map_of_mem _ h1
    have h3 : (c ⟨y, hy⟩ : G) = ⁅y, a⁆ := hc ⟨y, hy⟩
    rw [h3] at h2
    exact h2
  have hY3' : Y = oPrimeResidualOf 3 Y := hY3
  have hxV : a ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) :=
    (hAY.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)) ha
  refine ⟨hi, ?_, ?_⟩
  ·
    exact thmc_commutator_Y_zpowers_le (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y) hY3' hxV hi
  ·
    exact CFSG.RankThree.PartTwo.Sec17.Proof17Q0.commutator_zpowers_le
      (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y) hY3' hxV hi

end CFSG.RankThree.PartTwo.Sec15.ThmC
