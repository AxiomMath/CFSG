module

public import CFSG.RankThree.PartTwo.Sec18.Item183NMProofTools
public import CFSG.RankThree.PartTwo.Sec18.Item183NMProofCbZ3
public import CFSG.RankThree.PartTwo.Sec18.Item183NMProofCbHeis
import CFSG.RankThree.PartTwo.Sec18.Item184a
import CFSG.RankThree.PartTwo.Sec18.Item181b
import CFSG.RankThree.PartTwo.KFacts.KS18OuterHeis
import CFSG.RankThree.CentralCover.FourGroupWitness
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeCentralizer
public import CFSG.RankThree.PartTwo.Sec18.Item183NMProofStatements
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open scoped Pointwise

namespace Item183NMProof

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_mul_mem_of_pow {H L : Subgroup G} (hLH : L ≤ H)
    (hHL : H ≤ Subgroup.normalizer (L : Set G)) {b t : G} (hbH : b ∈ H) (hb3 : b ^ 3 = 1)
    (ht : t ∈ L) {n : ℕ} (hr : (b * t) ^ (2 ^ n) = 1) : b ∈ L := by
  have : (L.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLH).mpr hHL
  set φ := QuotientGroup.mk' (L.subgroupOf H) with hφ
  have htH : t ∈ H := hLH ht
  have hφt : φ ⟨t, htH⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr ht)
  have hφ1 : φ ⟨b, hbH⟩ = φ (⟨b, hbH⟩ * ⟨t, htH⟩) := by rw [map_mul, hφt, mul_one]
  have h3 : φ ⟨b, hbH⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨b, hbH⟩ : H) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
    rw [this, map_one]
  have h2 : φ ⟨b, hbH⟩ ^ (2 ^ n) = 1 := by
    rw [hφ1, ← map_pow]
    have : ((⟨b, hbH⟩ : H) * ⟨t, htH⟩) ^ (2 ^ n) = 1 := Subtype.ext (by simpa using hr)
    rw [this, map_one]
  have hord : orderOf (φ ⟨b, hbH⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2))
      (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2)
  have h1 : φ ⟨b, hbH⟩ = 1 := orderOf_eq_one_iff.mp hord
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)

theorem exists_mem_normalizer_map_eq {H B : Subgroup G} (hBH : B ≤ H)
    (hB : CFSG.Assembly.IsElemAbelian 3 B) {w : H ⧸ CFSG.pCore 2 H}
    (hwL : w ∈ (perfectResidual H).map (QuotientGroup.mk' (CFSG.pCore 2 H)))
    (hwB : ∀ β ∈ (B.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 H)),
      w * β * w⁻¹ ∈ (B.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 H))) :
    ∃ ℓ : H, (ℓ : G) ∈ inSubgroup perfectResidual H ⊓ Subgroup.normalizer (B : Set G) ∧
      QuotientGroup.mk' (CFSG.pCore 2 H) ℓ = w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π : H →* H ⧸ CFSG.pCore 2 H := QuotientGroup.mk' (CFSG.pCore 2 H) with hπ
  set L := inSubgroup perfectResidual H with hLdef
  set O := CFSG.Open.pCoreOf 2 H with hOdef
  set R := O ⊓ L with hRdef
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := le_normalizer_inSubgroup_perfectResidual H
  have hHO : H ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hR2 : IsPGroup 2 R := hO2.to_le inf_le_left
  have hHR : H ≤ Subgroup.normalizer (R : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hHO hx, hHL hx⟩
  have hmemO : ∀ x : H, π x = 1 ↔ (x : G) ∈ O := by
    intro x
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf]
  obtain ⟨ℓ₀, hℓ₀, rfl⟩ := hwL
  have hℓ₀L : (ℓ₀ : G) ∈ L := ⟨ℓ₀, hℓ₀, rfl⟩
  have hconjB : ∀ β ∈ B, (ℓ₀ : G) * β * (ℓ₀ : G)⁻¹ ∈ B ⊔ R := by
    intro β hβ
    have hβH : β ∈ H := hBH hβ
    obtain ⟨β', hβ', hβ'eq⟩ :=
      hwB (π ⟨β, hβH⟩) ⟨⟨β, hβH⟩, Subgroup.mem_subgroupOf.mpr hβ, rfl⟩
    have hβ'B : (β' : G) ∈ B := Subgroup.mem_subgroupOf.mp hβ'
    have hrO : (β' : G)⁻¹ * ((ℓ₀ : G) * β * (ℓ₀ : G)⁻¹) ∈ O := by
      have h1 : π (β'⁻¹ * (ℓ₀ * ⟨β, hβH⟩ * ℓ₀⁻¹)) = 1 := by
        rw [map_mul, map_inv, hβ'eq, map_mul, map_mul, map_inv]
        group
      exact (hmemO _).mp h1
    have ht : β⁻¹ * (ℓ₀ : G) * β * (ℓ₀ : G)⁻¹ ∈ L := by
      have h1 : β⁻¹ * (ℓ₀ : G) * β⁻¹⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hHL (H.inv_mem hβH)) _).mp hℓ₀L
      rw [inv_inv] at h1
      exact L.mul_mem h1 (L.inv_mem hℓ₀L)
    have hb3 : ((β' : G)⁻¹ * β) ^ 3 = 1 := hB.2 _ (B.mul_mem (B.inv_mem hβ'B) hβ)
    obtain ⟨n, hn⟩ := hO2 ⟨_, hrO⟩
    have e1 : (β' : G)⁻¹ * ((ℓ₀ : G) * β * (ℓ₀ : G)⁻¹) =
        ((β' : G)⁻¹ * β) * (β⁻¹ * (ℓ₀ : G) * β * (ℓ₀ : G)⁻¹) := by group
    have hrL : (β' : G)⁻¹ * ((ℓ₀ : G) * β * (ℓ₀ : G)⁻¹) ∈ L := by
      have hbL := mem_of_mul_mem_of_pow hLH hHL (H.mul_mem (H.inv_mem β'.2) hβH) hb3 ht
        (n := n) (by rw [← e1]; simpa using congrArg Subtype.val hn)
      rw [e1]
      exact L.mul_mem hbL ht
    have e2 : (ℓ₀ : G) * β * (ℓ₀ : G)⁻¹ =
        (β' : G) * ((β' : G)⁻¹ * ((ℓ₀ : G) * β * (ℓ₀ : G)⁻¹)) := by group
    rw [e2]
    exact Subgroup.mul_mem_sup hβ'B ⟨hrO, hrL⟩
  have hℓ₀N : (ℓ₀ : G) ∈ Subgroup.normalizer ((B ⊔ R : Subgroup G) : Set G) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hle : B ⊔ R ≤ (B ⊔ R).comap (MulAut.conj (ℓ₀ : G)).toMonoidHom := by
      refine sup_le (fun β hβ => hconjB β hβ) (fun r hr => ?_)
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hHR ℓ₀.2) r).mp hr)
    exact hle hx
  have hBR : B ≤ Subgroup.normalizer (R : Set G) := hBH.trans hHR
  have hB3 : IsPGroup 3 B := fun x => ⟨1, Subtype.ext (by simpa using hB.2 x x.2)⟩
  have hBRbot : B ⊓ R = ⊥ := inf_eq_bot_of_elemAbelian_three hB hR2
  have hcard : Nat.card (B ⊔ R : Subgroup G) = Nat.card B * Nat.card R := by
    rw [sup_comm, CFSG.RankThree.CentralCover.card_sup_eq_mul_of_le_normalizer hBR
      (by rw [inf_comm]; exact hBRbot), mul_comm]
  have hsyl : CFSG.ABGLocalTools.IsSylowOf 3 B (B ⊔ R) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_sup_left, hB3, ?_⟩
    have hrel : B.relIndex (B ⊔ R) = Nat.card R := by
      have h1 := Subgroup.relIndex_mul_card B (B ⊔ R)
      rw [inf_eq_left.mpr le_sup_left, hcard] at h1
      exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [h1, mul_comm])
    rw [hrel]
    obtain ⟨k, hk⟩ := hR2.exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  obtain ⟨n, hn, m, hm, hℓ₀nm⟩ := exists_mul_of_isSylowOf hsyl
    (K := Subgroup.zpowers (ℓ₀ : G)) (Subgroup.zpowers_le.mpr hℓ₀N) (Subgroup.mem_zpowers _)
  have hn' : n⁻¹ ∈ ((B : Set G) * (R : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right B R hBR]
    exact (B ⊔ R).inv_mem hn
  obtain ⟨β, hβ, r, hr, hβr⟩ := hn'
  have hℓ : r * (ℓ₀ : G) = β⁻¹ * m := by
    have hn2 : n = r⁻¹ * β⁻¹ := by
      rw [← inv_inv n, ← hβr]
      group
    rw [hℓ₀nm, hn2]
    group
  have hrH : r ∈ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H hr.1
  refine ⟨⟨r, hrH⟩ * ℓ₀, ⟨?_, ?_⟩, ?_⟩
  · exact L.mul_mem hr.2 hℓ₀L
  · change r * (ℓ₀ : G) ∈ _
    rw [hℓ]
    exact (Subgroup.normalizer _).mul_mem (Subgroup.le_normalizer (B.inv_mem hβ)) hm
  · rw [map_mul, (hmemO ⟨r, hrH⟩).mpr hr.1, one_mul]

theorem mem_of_commute_of_sec18Std {B X : Subgroup G} (h : Sec18Std G B X) {x : G}
    (hx : x ^ 3 = 1) (hxB : ∀ b ∈ B, b * x = x * b) : x ∈ B := by
  have hB := isE27_of_mem_partTwoE h.mem_partTwoE
  have hFE := (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
  have hBF : B ∈ partTwoF G := hFE ▸ h.mem_partTwoE
  have hab : CFSG.Assembly.IsElemAbelian 3 (B ⊔ Subgroup.zpowers x) := by
    refine Sec13.isElemAbelian_sup hB.1 (Sec13.isElemAbelian_zpowers hx) fun a ha y hy => ?_
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_right (show Commute a x from hxB a ha) i).eq
  have heq := hBF.2.1 _ hab le_sup_left
  exact heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)

theorem mem_map_of_commute {B X H : Subgroup G} (h : Sec18Std G B X) (hBH : B ≤ H)
    {z : H ⧸ CFSG.pCore 2 H} (hz3 : z ^ 3 = 1)
    (hz : ∀ β ∈ (B.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 H)), z * β = β * z) :
    z ∈ (B.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π : H →* H ⧸ CFSG.pCore 2 H := QuotientGroup.mk' (CFSG.pCore 2 H) with hπ
  have hB := isE27_of_mem_partTwoE h.mem_partTwoE
  have hB3 : IsPGroup 3 (B.subgroupOf H) := fun x =>
    ⟨1, Subtype.ext (Subtype.ext (by simpa using hB.1.2 _ (Subgroup.mem_subgroupOf.mp x.2)))⟩
  have hker : ¬ 3 ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := H)).exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
    omega
  have hcent :=
    CFSG.RankThreeEvenClassification.Helpers.centralizer_map_eq_of_pGroup_prime_complement_kernel
      3 Nat.prime_three π (QuotientGroup.mk'_surjective _) hker (B.subgroupOf H) hB3
  have hzC : z ∈ Subgroup.centralizer (((B.subgroupOf H).map π : Subgroup _) : Set _) :=
    Subgroup.mem_centralizer_iff.mpr fun β hβ => (hz β hβ).symm
  rw [← hcent] at hzC
  obtain ⟨g, hg, rfl⟩ := hzC
  obtain ⟨e, m, hm3, hnm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3 (by norm_num)
  have hge : (g ^ m) ^ (3 ^ e) = 1 := by
    rw [← pow_mul, mul_comm, ← hnm, pow_orderOf_eq_one]
  have hπ3 : π ((g ^ m) ^ 3) = 1 := by
    rw [map_pow, map_pow, ← pow_mul, mul_comm, pow_mul, hz3, one_pow]
  have hO : (((g ^ m) ^ 3 : H) : G) ∈ CFSG.Open.pCoreOf 2 H := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf] at hπ3
    exact hπ3
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H ⟨_, hO⟩
  have hk' : ((g ^ m) ^ 3) ^ (2 ^ k) = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
  have h3e : ((g ^ m) ^ 3) ^ (3 ^ e) = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hge, one_pow]
  have hord : orderOf ((g ^ m) ^ 3) = 1 :=
    Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow k e (by norm_num : Nat.Coprime 2 3))
      (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one h3e)
  have hh3 : (g ^ m) ^ 3 = 1 := orderOf_eq_one_iff.mp hord
  have hgB : (((g ^ m : H)) : G) ∈ B := by
    refine mem_of_commute_of_sec18Std h (by simpa using congrArg Subtype.val hh3) fun b hb => ?_
    have hbg : (⟨b, hBH hb⟩ : H) * g = g * ⟨b, hBH hb⟩ :=
      Subgroup.mem_centralizer_iff.mp hg _ (Subgroup.mem_subgroupOf.mpr hb)
    have h1 : (⟨b, hBH hb⟩ : H) * g ^ m = g ^ m * ⟨b, hBH hb⟩ :=
      ((show Commute (⟨b, hBH hb⟩ : H) g from hbg).pow_right m).eq
    exact congrArg Subtype.val h1
  have hzm : π g ^ m ∈ (B.subgroupOf H).map π :=
    ⟨g ^ m, Subgroup.mem_subgroupOf.mpr hgB, by rw [map_pow]⟩
  have hmm : (m * m) % 3 = 1 := by
    have : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases this with h1 | h1 <;> simp [Nat.mul_mod, h1]
  have hzz : (π g ^ m) ^ m = π g := by
    rw [← pow_mul, ← Nat.mod_add_div (m * m) 3, hmm, pow_add, pow_mul, hz3, one_pow, mul_one,
      pow_one]
  rw [← hzz]
  exact Subgroup.pow_mem _ hzm _

theorem step183Cb :
    Step183Cb := by
  intro G _ _ B X H s h hH hs D hDB hD3 hDN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hH₀ := (mem_scriptH_iff_mem_scriptH₀.mp hH).1
  have hBH : B ≤ H := le_of_mem_scriptH₀ hH₀
  have hB := isE27_of_mem_partTwoE h.mem_partTwoE
  set Q := CFSG.pCore 2 H with hQ
  set π : H →* H ⧸ Q := QuotientGroup.mk' Q with hπ
  set L := inSubgroup perfectResidual H with hLdef
  set Lb := (perfectResidual H).map π with hLb
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hmemR : ∀ x : H, π x = 1 ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 H := by
    intro x
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf]
  obtain ⟨hsS, -, -, hsH, Xb, hXn, hX, hXt, -⟩ := id hs
  have hS2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 (H ⊓ X)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have ht2 : IsPGroup 2 (Subgroup.zpowers (π ⟨s, hsH⟩)) := by
    have hT2 : IsPGroup 2 ((CFSG.Open.pCoreOf 2 (H ⊓ X)).subgroupOf H) := hS2.comap_subtype
    refine (hT2.map π).to_le (Subgroup.zpowers_le.mpr ?_)
    exact ⟨⟨s, hsH⟩, Subgroup.mem_subgroupOf.mpr hsS, rfl⟩
  have hq2 : IsPGroup 2 ((H ⧸ Q) ⧸ Xb) := by
    have h1 := ht2.map (QuotientGroup.mk' Xb)
    have h2 : (Subgroup.zpowers (π ⟨s, hsH⟩)).map (QuotientGroup.mk' Xb) = ⊤ := by
      rw [← Subgroup.map_top_of_surjective (QuotientGroup.mk' Xb)
        (QuotientGroup.mk'_surjective Xb), ← hXt, Subgroup.map_sup,
        (QuotientGroup.map_mk'_self Xb), bot_sup_eq]
    rw [h2] at h1
    exact h1.of_equiv Subgroup.topEquiv
  have hqs : Group.IsSolvable ((H ⧸ Q) ⧸ Xb) := by
    have := hq2.isNilpotent
    infer_instance
  have hLbeq : ⁅⁅Xb, Xb⁆, ⁅Xb, Xb⁆⁆ = ⁅Xb, Xb⁆ → Lb = ⁅Xb, Xb⁆ := fun hp => by
    rw [hLb, map_perfectResidual_eq (QuotientGroup.mk'_surjective Q)]
    exact perfectResidual_eq_commutator hqs hp
  have hR2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hbot : B ⊓ CFSG.Open.pCoreOf 2 H = ⊥ := inf_eq_bot_of_elemAbelian_three hB.1 hR2
  have hinj : ∀ K : Subgroup G, K ≤ B →
      Nat.card ((K.subgroupOf H).map π) = Nat.card K := by
    intro K hKB
    have h1 := card_eq_card_map_mul_card_inf_ker π (K.subgroupOf H)
    have h2 : K.subgroupOf H ⊓ π.ker = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxO : (x : G) ∈ CFSG.Open.pCoreOf 2 H := (hmemR x).mp hx.2
      have hxB : (x : G) ∈ B ⊓ CFSG.Open.pCoreOf 2 H :=
        ⟨hKB (Subgroup.mem_subgroupOf.mp hx.1), hxO⟩
      rw [hbot, Subgroup.mem_bot] at hxB
      exact Subgroup.mem_bot.mpr (Subtype.ext hxB)
    rw [h2, Subgroup.card_bot, mul_one] at h1
    rw [← h1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hKB.trans hBH)).toEquiv
  set Bb := (B.subgroupOf H).map π with hBb
  set Db := (D.subgroupOf H).map π with hDb
  have hBb27 : Nat.card Bb = 27 := by rw [hBb, hinj B le_rfl, hB.2]
  have hDb3 : Nat.card Db = 3 := by rw [hDb, hinj D hDB, hD3]
  have hBbX : Bb ≤ Xb := by
    rintro _ ⟨x, hx, rfl⟩
    refine mem_of_isPGroup_quotient hq2 (k := 1) ?_
    rw [pow_one, ← map_pow]
    have : x ^ 3 = 1 := Subtype.ext (by simpa using hB.1.2 _ (Subgroup.mem_subgroupOf.mp hx))
    rw [this, map_one]
  have hDbB : Db ≤ Bb := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hDB (Subgroup.mem_subgroupOf.mp hx))
  intro d hd
  by_contra hdC
  have hdB : d ∈ B := hDB hd
  have hdH : d ∈ H := hBH hdB
  have hdL : π ⟨d, hdH⟩ ∉ Subgroup.centralizer (Lb : Set (H ⧸ Q)) :=
    fun hc => hdC ⟨hdB, (forall_mem_pCoreOf_iff hdH).mpr hc⟩
  have hdDb : π ⟨d, hdH⟩ ∈ Db := ⟨⟨d, hdH⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
  obtain ⟨w, hwL, hwB, x, hx, hxw⟩ : ∃ w ∈ Lb, (∀ β ∈ Bb, w * β * w⁻¹ ∈ Bb) ∧
      ∃ x ∈ Db, w * x * w⁻¹ ∉ Db := by
    rcases hX with he | ⟨U, V, hsup, hUV, hU, ⟨eV⟩, h3⟩
    ·
      obtain ⟨e⟩ := he
      have hk : Nat.card (GaloisField 2 2) = 4 := KFacts.L34.card_galoisField_two_two
      set e' := e.trans (MulEquiv.prodCongr (MulEquiv.refl _)
        (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2))) with he'
      have hcomm := KFacts.KS18.commutator_eq_range e'
      have hperf : Group.IsPerfect (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3
          (GaloisField 2 2)) := KFacts.KS18.isPerfect_projectiveSL _
      have hrp : ⁅(KFacts.KS18.inrY e').range, (KFacts.KS18.inrY e').range⁆ =
          (KFacts.KS18.inrY e').range := by
        rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def,
          Group.IsPerfect.commutator_eq_top]
      have hLbr : Lb = (KFacts.KS18.inrY e').range := by
        rw [hLbeq (by rw [hcomm, hrp]), hcomm]
      have hDbL : ¬ Db ≤ Subgroup.centralizer ((KFacts.KS18.inrY e').range : Set (H ⧸ Q)) :=
        fun hle => hdL (by rw [hLbr]; exact hle hdDb)
      obtain ⟨w, hw, hwB, x, hx, hxw⟩ :=
        exists_conj_not_mem_of_prod hk e' hBb27 hBbX hDbB hDb3 hDbL
      exact ⟨w, by rw [hLbr]; exact hw, hwB, x, hx, hxw⟩
    ·
      have hcomm := KFacts.KS18.commutator_eq_of_isHeisSL hsup hUV hU ⟨eV⟩ h3
      have hXX : ⁅Xb, Xb⁆ = V.map Xb.subtype := by
        rw [← Subgroup.map_subtype_commutator, hcomm]
      have hVp : Group.IsPerfect V := by
        have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2)) :=
          CFSG.LinearGroups.special_linear_isPerfect (by norm_num) (Or.inl le_rfl)
        exact Group.IsPerfect.ofSurjective (f := eV.symm.toMonoidHom) eV.symm.surjective
      have hVmp : ⁅V.map Xb.subtype, V.map Xb.subtype⁆ = V.map Xb.subtype := by
        rw [← Subgroup.map_commutator, ← Subgroup.map_subtype_commutator,
          Group.IsPerfect.commutator_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
      have hLbV : Lb = V.map Xb.subtype := by
        rw [hLbeq (by rw [hXX, hVmp]), hXX]
      have hBbE : IsE27 Bb := ⟨CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 π _
        (isE27_subgroupOf hB hBH).1, hBb27⟩
      have hB' := isE27_subgroupOf hBbE hBbX
      have hD'3 : Nat.card (Db.subgroupOf Xb) = 3 := by
        rw [← hDb3]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hDbB.trans hBbX)).toEquiv
      have hD'B' : Db.subgroupOf Xb ≤ Bb.subgroupOf Xb := fun y hy =>
        Subgroup.mem_subgroupOf.mpr (hDbB (Subgroup.mem_subgroupOf.mp hy))
      have hD'U : ¬ Db.subgroupOf Xb ≤ U := by
        intro hle
        apply hdL
        have hmem : (⟨π ⟨d, hdH⟩, hBbX (hDbB hdDb)⟩ : Xb) ∈ U :=
          hle (Subgroup.mem_subgroupOf.mpr hdDb)
        rw [hLbV, Subgroup.mem_centralizer_iff]
        rintro _ ⟨v, hv, rfl⟩
        exact congrArg Subtype.val (hUV _ hmem v hv).symm
      have hnoB : ∀ W : Subgroup Xb, W ≤ Bb.subgroupOf Xb → Nat.card W = 9 → ¬ W ≤ U := by
        intro W hWB hW9 hWU
        set W₁ := W.map Xb.subtype with hW₁
        have hW₁B : W₁ ≤ Bb := by
          rintro _ ⟨y, hy, rfl⟩
          exact Subgroup.mem_subgroupOf.mp (hWB hy)
        have hW₁9 : Nat.card W₁ = 9 := by
          rw [hW₁, Subgroup.card_map_of_injective Xb.subtype_injective, hW9]
        have hW₁C : ∀ y ∈ W₁, ∀ l ∈ Lb, l * y = y * l := by
          rintro _ ⟨y, hy, rfl⟩ l hl
          rw [hLbV] at hl
          obtain ⟨v, hv, rfl⟩ := hl
          exact congrArg Subtype.val (hUV y (hWU hy) v hv).symm
        set f : B.subgroupOf H →* H ⧸ Q := π.comp (B.subgroupOf H).subtype with hf
        have hfinj : Function.Injective f := by
          rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
          intro a ha
          rw [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, Subgroup.coe_subtype, hmemR] at ha
          have : ((a : H) : G) ∈ B ⊓ CFSG.Open.pCoreOf 2 H := ⟨Subgroup.mem_subgroupOf.mp a.2, ha⟩
          rw [hbot, Subgroup.mem_bot] at this
          exact Subgroup.mem_bot.mpr (Subtype.ext (Subtype.ext this))
        have hfrange : f.range = Bb := by rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
        set B'' := W₁.comap f with hB''
        have hB''9 : Nat.card B'' = 9 := by
          have : B''.map f = W₁ := by
            rw [hB'', Subgroup.map_comap_eq, hfrange, inf_eq_right.mpr hW₁B]
          rw [← hW₁9, ← this, Subgroup.card_map_of_injective hfinj]
        set B₀ : Subgroup G := (B''.map (B.subgroupOf H).subtype).map H.subtype with hB₀
        have hB₀B : B₀ ≤ B := by
          rintro _ ⟨_, ⟨b, -, rfl⟩, rfl⟩
          exact Subgroup.mem_subgroupOf.mp b.2
        have hB₀9 : Nat.card B₀ = 9 := by
          rw [hB₀, Subgroup.card_map_of_injective H.subtype_injective,
            Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hB''9]
        apply perfectResidual_not_le_of_mem_scriptH h hH
        refine perfectResidual_le_of_commutator_le h hBH hB₀B hB₀9 fun l hl b hb => ?_
        obtain ⟨l', hl', rfl⟩ := hl
        obtain ⟨_, ⟨b', hb', rfl⟩, rfl⟩ := hb
        have hlπ : π l' ∈ Lb := ⟨l', hl', rfl⟩
        have hc := hW₁C _ hb' _ hlπ
        have h1 : π (l' * (b' : H) * l'⁻¹ * (b' : H)⁻¹) = 1 := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv]
          change π l' * f b' * (π l')⁻¹ * (f b')⁻¹ = 1
          rw [hc]
          group
        have h2 := (hmemR _).mp h1
        simpa using h2
      have hZB : U ⊓ V ≤ Bb.subgroupOf Xb := by
        intro z hz
        have hzc : z ∈ Subgroup.center Xb := by
          rw [KFacts.L34.center_eq_inf_of_isHeisSL hsup hUV hU ⟨eV⟩ h3]
          exact hz
        have hz3 : (z : H ⧸ Q) ^ 3 = 1 := by
          have h1 := Monoid.pow_exponent_eq_one (⟨z, hz.1⟩ : U)
          rw [hU.2.2] at h1
          have h2 : z ^ 3 = 1 := by simpa using congrArg Subtype.val h1
          simpa using congrArg Subtype.val h2
        refine Subgroup.mem_subgroupOf.mpr (mem_map_of_commute h hBH hz3 fun β hβ => ?_)
        have h1 := Subgroup.mem_center_iff.mp hzc ⟨β, hBbX hβ⟩
        exact (congrArg Subtype.val h1).symm
      obtain ⟨w, hwV, hwB, x, hx, hxw⟩ :=
        exists_conj_not_mem_of_heis hsup hUV hU eV h3 hB'.1 hB'.2 hnoB hZB hD'B' hD'3 hD'U
      refine ⟨(w : H ⧸ Q), by rw [hLbV]; exact ⟨w, hwV, rfl⟩, fun β hβ => ?_, (x : H ⧸ Q),
        Subgroup.mem_subgroupOf.mp hx, fun hmem => hxw (Subgroup.mem_subgroupOf.mpr hmem)⟩
      exact Subgroup.mem_subgroupOf.mp (hwB ⟨β, hBbX hβ⟩ (Subgroup.mem_subgroupOf.mpr hβ))
  obtain ⟨ℓ, ⟨hℓL, hℓN⟩, hℓw⟩ := exists_mem_normalizer_map_eq hBH hB.1 hwL hwB
  have hℓD := hDN ⟨hℓL, hℓN⟩
  obtain ⟨x', hx', rfl⟩ := hx
  apply hxw
  have hx'D : (x' : G) ∈ D := Subgroup.mem_subgroupOf.mp hx'
  have h1 : (ℓ : G) * x' * (ℓ : G)⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hℓD _).mp hx'D
  refine ⟨ℓ * x' * ℓ⁻¹, Subgroup.mem_subgroupOf.mpr h1, ?_⟩
  rw [map_mul, map_mul, map_inv, hℓw]

end Item183NMProof

end CFSG.RankThree.PartTwo.Sec18
