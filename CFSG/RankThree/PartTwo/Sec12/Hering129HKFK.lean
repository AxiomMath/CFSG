module

public import CFSG.RankThree.PartTwo.Sec12.Hering129HLift
import CFSG.RankThree.PartTwo.Sec18.Claim184LcProof
import CFSG.RankThree.PartTwo.Sec4.LThreePiHessian
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec12.Hering129HBasic
public import CFSG.RankThree.PartTwo.Sec18.Transport
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Aux

variable {G : Type} [Group G] [Finite G]

theorem resCent_eq_map (K : Subgroup G) {z : G} (hz : z ∈ K) :
    resCent K z = (inSubgroup perfectResidual
      (Subgroup.centralizer ({(⟨z, hz⟩ : K)} : Set K))).map K.subtype := by
  have h : K ⊓ Subgroup.centralizer ({z} : Set G) =
      (Subgroup.centralizer ({(⟨z, hz⟩ : K)} : Set K)).map K.subtype := by
    ext y
    constructor
    · rintro ⟨hyK, hyc⟩
      exact ⟨⟨y, hyK⟩, Subgroup.mem_centralizer_singleton_iff.mpr (Subtype.ext
        (Subgroup.mem_centralizer_singleton_iff.mp hyc)), rfl⟩
    · rintro ⟨y', hy', rfl⟩
      exact ⟨y'.2, Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy'))⟩
  rw [resCent, h]
  exact Sec18.inSubgroup_perfectResidual_map K.subtype K.subtype_injective _

theorem map_resCent_quot {Y : Type} [Group Y] [Finite Y] (N : Subgroup Y) [N.Normal]
    (hN : ¬ 3 ∣ Nat.card N) {t : Y} (ht : t ^ 3 = 1) :
    (inSubgroup perfectResidual (Subgroup.centralizer ({t} : Set Y))).map
        (QuotientGroup.mk' N) =
      resCent (⊤ : Subgroup (Y ⧸ N)) (QuotientGroup.mk' N t) := by
  rw [Sec18.Claim184LcProof.map_inSubgroup_perfectResidual,
    Hering129HLift.map_centralizer_eq N hN ht]
  unfold resCent
  rw [top_inf_eq]

theorem exists_pow_two_pow_eq_one {Y : Type} [Group Y] [Finite Y] {n : Y}
    (hn : n ∈ CFSG.pCore 2 Y) : ∃ k : ℕ, n ^ (2 ^ k) = 1 := by
  have hp : IsPGroup 2 (CFSG.pCore 2 Y) := CFSG.pCore_isPGroup
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hp) ⟨n, hn⟩
  refine ⟨k, ?_⟩
  have h1 : orderOf n = 2 ^ k := (Subgroup.orderOf_coe (⟨n, hn⟩ : CFSG.pCore 2 Y)).trans hk
  rw [← h1]
  exact pow_orderOf_eq_one n

theorem not_three_dvd_card_pCore_two (Y : Type) [Group Y] [Finite Y] :
    ¬ 3 ∣ Nat.card (CFSG.pCore 2 Y) := by
  have hp : IsPGroup 2 (CFSG.pCore 2 Y) := CFSG.pCore_isPGroup
  obtain ⟨k, hk⟩ := hp.exists_card_eq
  rw [hk]
  intro h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem inf_centralizer_eq_of_mem_D {A K : Subgroup G} {a b x : G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (haA : a ∈ A) (hbA : b ∈ A)
    (hKb : K ≤ Subgroup.centralizer ({b} : Set G)) (hxD : x ∈ D129 a b)
    (hxb : x ∉ Subgroup.zpowers b) :
    K ⊓ Subgroup.centralizer ({x} : Set G) = K ⊓ Subgroup.centralizer ({a} : Set G) := by
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have ha3 : a ^ 3 = 1 := hAe.2 a haA
  obtain ⟨i, j, hij⟩ := Sec4.exists_zpow_mul_of_mem_sup (hAc a haA b hbA) hxD
  have hai : a ^ i = a ∨ a ^ i = a⁻¹ := by
    have h3 : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
    rcases h3 with h | h | h
    · exfalso
      apply hxb
      rw [hij, Sec4.zpow_emod_three ha3 i, h, zpow_zero, one_mul]
      exact Subgroup.zpow_mem_zpowers b j
    · left
      rw [Sec4.zpow_emod_three ha3 i, h, zpow_one]
    · right
      rw [Sec4.zpow_emod_three ha3 i, h]
      have h3 : a ^ (3 : ℤ) = 1 := by
        rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, zpow_natCast]
        exact ha3
      calc a ^ (2 : ℤ) = a ^ (3 : ℤ) * a⁻¹ := by
            rw [← zpow_neg_one, ← zpow_add]
            norm_num
        _ = a⁻¹ := by rw [h3, one_mul]
  ext k
  constructor
  · rintro ⟨hkK, hkx⟩
    refine ⟨hkK, ?_⟩
    have hkb : Commute k b := Subgroup.mem_centralizer_singleton_iff.mp (hKb hkK)
    have hkx' : Commute k x := Subgroup.mem_centralizer_singleton_iff.mp hkx
    have hkai : Commute k (a ^ i) := by
      have : a ^ i = x * (b ^ j)⁻¹ := by rw [hij]; group
      rw [this]
      exact hkx'.mul_right (hkb.zpow_right j).inv_right
    have hka : Commute k a := by
      rcases hai with h | h
      · rwa [h] at hkai
      · rw [h] at hkai
        simpa using hkai.inv_right
    exact Subgroup.mem_centralizer_singleton_iff.mpr hka
  · rintro ⟨hkK, hka⟩
    refine ⟨hkK, ?_⟩
    have hkb : Commute k b := Subgroup.mem_centralizer_singleton_iff.mp (hKb hkK)
    have hka' : Commute k a := Subgroup.mem_centralizer_singleton_iff.mp hka
    rw [hij]
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((hka'.zpow_right i).mul_right (hkb.zpow_right j))

theorem eq_one_of_pow_three_of_pow_two_pow {Y : Type} [Group Y] {z : Y} (h3 : z ^ 3 = 1)
    {k : ℕ} (h2 : z ^ 2 ^ k = 1) : z = 1 := by
  have h : orderOf z ∣ Nat.gcd 3 (2 ^ k) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2)
  have hg : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right _ (by norm_num)
  rw [hg] at h
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h)

end Aux

@[expose] def Gap129KFKStrong : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (b a : G)
    (K S : Subgroup G), Cfg129 G A c L b a K S → GTwoType129 L K →
    ∀ x ∈ D129 a b, x ∉ Subgroup.zpowers b →
      c ∈ resCent K x ∧ S ≤ resCent K x ∧
        IsQuasisimple (↥(resCent K x) ⧸ aschbacherSolvableCore 3 ↥(resCent K x)) ∧
        ∀ z ∈ Subgroup.center (↥(resCent K x) ⧸ aschbacherSolvableCore 3 ↥(resCent K x)),
          z ^ 2 = 1

end CFSG.RankThree.PartTwo.Sec12
