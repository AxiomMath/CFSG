module

public import CFSG.GroupTheory.CardMapInfKer
public import CFSG.ClassicalGroups.PCoreSection
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CComponents
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123a
public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndPhi

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

open Equiv Equiv.Perm Subgroup
open CFSG.GH74.Uniqueness.SU.SU13.TA.L10

variable {G : Type} [Group G] [Finite G] {D : Data G}

private theorem subgroupOf_zpowers {G : Type*} [Group G] {x : G} {H : Subgroup G} (hx : x ∈ H) :
    (Subgroup.zpowers x).subgroupOf H = Subgroup.zpowers (⟨x, hx⟩ : ↥H) := by
  ext y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hn)⟩
  · rintro ⟨n, hn⟩
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩

namespace A10Perm

open Equiv Equiv.Perm Subgroup
open CFSG.GH74.Uniqueness.SU.SU13.TA.L10

theorem card_support_eq_nine_iff (i j k : Fin 3) :
    (toP i j k).support.card = 9 ↔ i ≠ 0 ∧ j ≠ 0 ∧ k ≠ 0 := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel

theorem support_pow_mul_ne_three : ∀ (i j k : Fin 3), i ≠ 0 → j ≠ 0 → k ≠ 0 → ∀ a b : Fin 3,
    (toP i j k ^ (a : ℕ) * toP i (j + j) 0 ^ (b : ℕ)).support.card ≠ 3 := by
  decide +kernel

theorem pow_toP_ne : ∀ (i j k : Fin 3), i ≠ 0 → k ≠ 0 → ∀ m : Fin 3,
    (toP i j k) ^ (m : ℕ) ≠ toP i (j + j) 0 := by
  decide +kernel

theorem exists_mem_zpowers_sup : ∀ (i j k : Fin 3), i ≠ 0 → j ≠ 0 → k ≠ 0 → ∀ i' j' k' : Fin 3,
    (∀ a b : Fin 3, (toP i j k ^ (a : ℕ) * toP i' j' k' ^ (b : ℕ)).support.card ≠ 3) →
    ∃ c e : Fin 3, toP i' j' k' = toP i j k ^ (c : ℕ) * toP i (j + j) 0 ^ (e : ℕ) := by
  decide +kernel

theorem pow_three_eq_one (x : ↥atilde) : x ^ 3 = 1 := by
  apply Subtype.ext
  simpa using isElemAbelian_atilde.2 x x.2

theorem card_sup_zpowers_eq_nine {x y : ↥atilde} (hx1 : x ≠ 1)
    (hyx : y ∉ Subgroup.zpowers x) :
    Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) = 9 := by
  classical
  haveI : IsMulCommutative ↥atilde := isElemAbelian_atilde.1
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    simpa using isElemAbelian_atilde.2 x x.2
  have hy3 : y ^ 3 = 1 := by
    apply Subtype.ext
    simpa using isElemAbelian_atilde.2 y y.2
  have hcx : Nat.card ↥(Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx3 hx1
  have hcy : Nat.card ↥(Subgroup.zpowers y) = 3 := by
    rw [Nat.card_zpowers]
    refine orderOf_eq_prime hy3 ?_
    intro h1
    exact hyx (by rw [h1]; exact Subgroup.one_mem _)
  have hnorm : Subgroup.zpowers x ≤
      Subgroup.normalizer (Subgroup.zpowers y : Set ↥atilde) := by
    refine Subgroup.le_normalizer_iff.mpr fun a ha b hb => ?_
    have hca : a * b = b * a := by
      have h := isElemAbelian_atilde.1.is_comm.comm a b
      simpa using h
    rw [hca, mul_assoc, mul_inv_cancel, mul_one]
    exact hb
  have hinf : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers x ⊓ Subgroup.zpowers y) ∣ 3 := by
      have h := Subgroup.card_dvd_of_le (inf_le_left : Subgroup.zpowers x ⊓ Subgroup.zpowers y ≤
        Subgroup.zpowers x)
      rwa [hcx] at h
    have hne : Nat.card ↥(Subgroup.zpowers x ⊓ Subgroup.zpowers y) ≠ 3 := by
      intro h3
      have heq : Subgroup.zpowers x ⊓ Subgroup.zpowers y = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hcx])
      have hle : Subgroup.zpowers x ≤ Subgroup.zpowers y := heq ▸ inf_le_right
      have heq2 : Subgroup.zpowers x = Subgroup.zpowers y :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hcx, hcy])
      exact hyx (by rw [heq2]; exact Subgroup.mem_zpowers y)
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exact absurd h3 hne
  have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
    (H := Subgroup.zpowers x) (K := Subgroup.zpowers y) hnorm
  rw [hinf, hcx, hcy] at h
  simpa using h

theorem exists_pow_mul_of_mem_sup {x y z : ↥atilde}
    (hz : z ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y) :
    ∃ a b : Fin 3, z = x ^ (a : ℕ) * y ^ (b : ℕ) := by
  classical
  haveI : IsMulCommutative ↥atilde := isElemAbelian_atilde.1
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    simpa using isElemAbelian_atilde.2 x x.2
  have hy3 : y ^ 3 = 1 := by
    apply Subtype.ext
    simpa using isElemAbelian_atilde.2 y y.2
  obtain ⟨p, hp, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hz
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hp
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hq
  have hx3z : x ^ (3 : ℤ) = 1 := by simpa using hx3
  have hy3z : y ^ (3 : ℤ) = 1 := by simpa using hy3
  have hm : x ^ m = x ^ ((m % 3).toNat) := by
    have h1 : x ^ m = x ^ (m % 3) := zpow_eq_zpow_emod m hx3z
    have h2 : x ^ (m % 3) = x ^ ((m % 3).toNat) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg m (by norm_num))]
    rw [h1, h2]
  have hn : y ^ n = y ^ ((n % 3).toNat) := by
    have h1 : y ^ n = y ^ (n % 3) := zpow_eq_zpow_emod n hy3z
    have h2 : y ^ (n % 3) = y ^ ((n % 3).toNat) := by
      rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg n (by norm_num))]
    rw [h1, h2]
  refine ⟨⟨(m % 3).toNat, ?_⟩, ⟨(n % 3).toNat, ?_⟩, ?_⟩
  · have h2 : 0 ≤ m % 3 := Int.emod_nonneg m (by norm_num)
    have h3 : m % 3 < 3 := Int.emod_lt_of_pos m (by norm_num)
    omega
  · have h2 : 0 ≤ n % 3 := Int.emod_nonneg n (by norm_num)
    have h3 : n % 3 < 3 := Int.emod_lt_of_pos n (by norm_num)
    omega
  · rw [hm, hn]

theorem exists_fin_pow_of_mem_zpowers {x y : ↥atilde} (hx3 : x ^ 3 = 1)
    (hy : y ∈ Subgroup.zpowers x) : ∃ m : Fin 3, x ^ (m : ℕ) = y := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hk3 : x ^ (3 : ℤ) = 1 := by simpa using hx3
  have h1 : x ^ k = x ^ (k % 3) := zpow_eq_zpow_emod k hk3
  have h2 : 0 ≤ k % 3 := Int.emod_nonneg k (by norm_num)
  have h3 : k % 3 < 3 := Int.emod_lt_of_pos k (by norm_num)
  refine ⟨⟨(k % 3).toNat, by omega⟩, ?_⟩
  rw [← hk, h1, ← zpow_natCast, Int.toNat_of_nonneg h2]

private theorem toP_ne_one (i j k : Fin 3) (hi : i ≠ 0) (hj : j ≠ 0) (hk : k ≠ 0) :
    toP i j k ≠ 1 := by
  intro h
  have h9 : (toP i j k).support.card = 9 := (card_support_eq_nine_iff i j k).mpr ⟨hi, hj, hk⟩
  rw [h] at h9
  simp at h9

private theorem toP_notMem_zpowers (i j k : Fin 3) (hi : i ≠ 0) (hk : k ≠ 0) :
    toP i (j + j) 0 ∉ Subgroup.zpowers (toP i j k) := by
  intro hmem
  have hx_at : toP i j k ∈ atilde := mem_atilde_iff.mpr ⟨i, j, k, rfl⟩
  have hy_at : toP i (j + j) 0 ∈ atilde := mem_atilde_iff.mpr ⟨i, j + j, 0, rfl⟩
  have hmem' : (⟨toP i (j + j) 0, hy_at⟩ : ↥atilde) ∈
      Subgroup.zpowers (⟨toP i j k, hx_at⟩ : ↥atilde) := by
    have h1 : (⟨toP i (j + j) 0, hy_at⟩ : ↥atilde) ∈
        (Subgroup.zpowers (toP i j k)).subgroupOf atilde := Subgroup.mem_subgroupOf.mpr hmem
    rwa [subgroupOf_zpowers hx_at] at h1
  obtain ⟨m, hm⟩ := exists_fin_pow_of_mem_zpowers (pow_three_eq_one _) hmem'
  exact pow_toP_ne i j k hi hk m (by simpa using congrArg Subtype.val hm)

theorem cycleType_eq_three_three_three_of_support_nine {σ : Perm (Fin 10)}
    (h3 : σ ^ 3 = 1) (h9 : σ.support.card = 9) : σ.cycleType = {3, 3, 3} := by
  obtain ⟨k, hk⟩ : ∃ k, σ.cycleType = Multiset.replicate k 3 :=
    ⟨_, Equiv.Perm.cycleType_of_pow_prime_eq_one h3⟩
  have hsum := Equiv.Perm.sum_cycleType σ
  rw [hk, Multiset.sum_replicate, smul_eq_mul, h9] at hsum
  have hk3 : k = 3 := by omega
  rw [hk, hk3]
  rfl

theorem card_centralizer_perm_of_cycleType_eq_three_three_three {σ : Perm (Fin 10)}
    (h : σ.cycleType = {3, 3, 3}) :
    Nat.card ↥(Subgroup.centralizer ({σ} : Set (Perm (Fin 10)))) = 162 := by
  rw [Equiv.Perm.nat_card_centralizer, h, Fintype.card_fin]
  decide

theorem card_sup_zpowers_eq_nine_perm {x y : Perm (Fin 10)} (hx : x ∈ atilde) (hy : y ∈ atilde)
    (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x) :
    Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) = 9 := by
  have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ atilde :=
    sup_le (Subgroup.zpowers_le.mpr hx) (Subgroup.zpowers_le.mpr hy)
  have h1 : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) =
      Nat.card ↥((Subgroup.zpowers x ⊔ Subgroup.zpowers y).subgroupOf atilde) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).symm
  rw [h1, Subgroup.subgroupOf_sup (Subgroup.zpowers_le.mpr hx) (Subgroup.zpowers_le.mpr hy),
    subgroupOf_zpowers hx, subgroupOf_zpowers hy]
  refine card_sup_zpowers_eq_nine ?_ ?_
  · intro h
    exact hx1 (by simpa using congrArg Subtype.val h)
  · intro hmem
    apply hyx
    have h1 : (⟨y, hy⟩ : ↥atilde) ∈ (Subgroup.zpowers x).subgroupOf atilde := by
      rwa [subgroupOf_zpowers hx]
    exact Subgroup.mem_subgroupOf.mp h1

theorem exists_pow_mul_of_mem_sup_perm {x y z : Perm (Fin 10)} (hx : x ∈ atilde) (hy : y ∈ atilde)
    (hz : z ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y) :
    ∃ a b : Fin 3, z = x ^ (a : ℕ) * y ^ (b : ℕ) := by
  have hzat : z ∈ atilde :=
    (sup_le (Subgroup.zpowers_le.mpr hx) (Subgroup.zpowers_le.mpr hy)) hz
  have hz1 : (⟨z, hzat⟩ : ↥atilde) ∈
      Subgroup.zpowers (⟨x, hx⟩ : ↥atilde) ⊔ Subgroup.zpowers (⟨y, hy⟩ : ↥atilde) := by
    rw [← subgroupOf_zpowers hx, ← subgroupOf_zpowers hy,
      ← Subgroup.subgroupOf_sup (Subgroup.zpowers_le.mpr hx) (Subgroup.zpowers_le.mpr hy)]
    exact hz
  obtain ⟨a, b, hab⟩ := exists_pow_mul_of_mem_sup hz1
  exact ⟨a, b, by simpa using congrArg Subtype.val hab⟩

end A10Perm

namespace Ctx82E3.A10Frame

variable {c : Ctx82E3 D}

private theorem inf_ker_phiA_eq_bot (F : A10Frame c) :
    F.A.subgroupOf D.M ⊓ F.phiA.ker = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxA, hxK⟩ := Subgroup.mem_inf.mp hx
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    simpa [Subgroup.coe_pow] using F.elemAbelian.2 (x : G) (Subgroup.mem_subgroupOf.mp hxA)
  have hord3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  have hordker : orderOf x ∣ Nat.card F.phiA.ker := Subgroup.orderOf_dvd_natCard _ hxK
  have hone : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes F.coprime_card_ker_phiA hordker hord3
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp hone)

private theorem exists_generator_of_card_three {B : Subgroup G} (hB3 : Nat.card B = 3) :
    ∃ b ∈ B, b ≠ 1 := by
  rcases Subgroup.bot_or_exists_ne_one B with h | h
  · rw [h] at hB3
    simp at hB3
  · exact h

private theorem cycleType_phiA_of_deg_nine (F : A10Frame c) {B : Subgroup G} {b : G}
    (hbB : b ∈ B) (hBA : B ≤ F.A) (hB9 : F.deg B = 9) (hBz : B = Subgroup.zpowers b) :
    (F.phiA ⟨b, F.A_le_M (hBA hbB)⟩).cycleType = {3, 3, 3} := by
  have hbL : b ∈ c.L := F.A_le.trans F.P_le_L (hBA hbB)
  have hsupp : (F.phiA ⟨b, F.A_le_M (hBA hbB)⟩).support.card = 9 := by
    rw [← F.deg_zpowers_eq hbL, ← hBz]
    exact hB9
  have hb3 : (F.phiA ⟨b, F.A_le_M (hBA hbB)⟩) ^ 3 = 1 := by
    have h := A10Perm.pow_three_eq_one
      ⟨F.phiA ⟨b, F.A_le_M (hBA hbB)⟩, ?_⟩
    · simpa using congrArg Subtype.val h
    · have h1 : (⟨b, F.A_le_M (hBA hbB)⟩ : ↥D.M) ∈ F.A.subgroupOf D.M := by
        rw [Subgroup.mem_subgroupOf]
        exact hBA hbB
      have h := Subgroup.mem_map_of_mem F.phiA h1
      rwa [F.map_A_phiA] at h
  exact A10Perm.cycleType_eq_three_three_three_of_support_nine hb3 hsupp

private theorem phiA_inj_of_mem (F : A10Frame c) {x y : ↥D.M}
    (hx : x ∈ F.A.subgroupOf D.M) (hy : y ∈ F.A.subgroupOf D.M)
    (h : F.phiA x = F.phiA y) : x = y := by
  have h1 : x * y⁻¹ ∈ F.A.subgroupOf D.M := (F.A.subgroupOf D.M).mul_mem hx (inv_mem hy)
  have h2 : F.phiA (x * y⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  have h3 : x * y⁻¹ ∈ F.A.subgroupOf D.M ⊓ F.phiA.ker := Subgroup.mem_inf.mpr ⟨h1, h2⟩
  rw [inf_ker_phiA_eq_bot F] at h3
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp h3)

private theorem exists_mem_A_phiA_eq (F : A10Frame c) {y : Perm (Fin 10)}
    (hy : y ∈ A10Perm.atilde) : ∃ d : G, ∃ hd : d ∈ F.A,
      F.phiA ⟨d, F.A_le_M hd⟩ = y := by
  have hy' : y ∈ (F.A.subgroupOf D.M).map F.phiA := by
    rw [F.map_A_phiA]
    exact hy
  obtain ⟨m, hm, hmy⟩ := Subgroup.mem_map.mp hy'
  exact ⟨(m : G), Subgroup.mem_subgroupOf.mp hm, hmy⟩

private theorem not_dvd_162 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ p ∣ 162 := by
  have h162 : (162 : ℕ) = 2 * 3 ^ 4 := by norm_num
  rw [h162]
  intro hd
  rcases hp.dvd_mul.mp hd with h | h
  · rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h1
    · exact hp.ne_one h1
    · omega
  · rcases (Nat.dvd_prime Nat.prime_three).mp (hp.dvd_of_dvd_pow h) with h1 | h1
    · exact hp.ne_one h1
    · omega

private theorem A_le_centralizer (F : A10Frame c) {B : Subgroup G} (hBA : B ≤ F.A) :
    F.A ≤ Subgroup.centralizer (B : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b' hb'
  have h := F.elemAbelian.1.is_comm.comm (⟨a, ha⟩ : F.A) ⟨b', hBA hb'⟩
  have h' : a * b' = b' * a := by simpa using h
  exact h'.symm

private theorem A_le_normalizer_pCoreOf (F : A10Frame c) {p : ℕ} {B : Subgroup G}
    (hBA : B ≤ F.A) :
    F.A ≤ Subgroup.normalizer
      (CFSG.Open.pCoreOf p (Subgroup.centralizer (B : Set G)) : Set G) :=
  Subgroup.le_normalizer_iff.mpr fun a ha o ho =>
    CFSG.ClassicalGroups.PCoreSection.conj_mem_pCoreOf (F.A_le_centralizer hBA ha) ho

private theorem phiA_eq_one_of_mem_inf_pCoreOf (F : A10Frame c) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {B : Subgroup G} (hBA : B ≤ F.A) (hB3 : Nat.card B = 3) (hB9 : F.deg B = 9) :
    ∀ z ∈ CFSG.Open.pCoreOf p (Subgroup.centralizer (B : Set G)) ⊓ D.M, ∀ hzD : z ∈ D.M,
      F.phiA ⟨z, hzD⟩ = 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set H : Subgroup G := Subgroup.centralizer (B : Set G)
  set X : Subgroup G := CFSG.Open.pCoreOf p H
  have hXH : X ≤ H := CFSG.ClassicalGroups.PCoreSection.pCoreOf_le p H
  have hXp : IsPGroup p X := CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf p H
  obtain ⟨b, hbB, hb1⟩ := exists_generator_of_card_three hB3
  have hbD : b ∈ D.M := F.A_le_M (hBA hbB)
  have hBz : B = Subgroup.zpowers b := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbB) ?_).symm
    rw [hB3, F.card_zpowers_of_mem_A (hBA hbB) hb1]
  have hcyc := F.cycleType_phiA_of_deg_nine hbB hBA hB9 hBz
  have hCcard : Nat.card ↥(Subgroup.centralizer ({F.phiA ⟨b, hbD⟩} : Set (Perm (Fin 10)))) = 162 :=
    A10Perm.card_centralizer_perm_of_cycleType_eq_three_three_three hcyc
  have hp162 : ¬ p ∣ 162 := not_dvd_162 hp hp5
  intro z hz hzD
  obtain ⟨hzX, hzM⟩ := Subgroup.mem_inf.mp hz
  have hzH : z ∈ H := hXH hzX
  have hcent : F.phiA ⟨z, hzD⟩ ∈
      Subgroup.centralizer ({F.phiA ⟨b, hbD⟩} : Set (Perm (Fin 10))) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzb : z * b = b * z := (Subgroup.mem_centralizer_iff.mp hzH b hbB).symm
    have h1 : (⟨z, hzD⟩ : ↥D.M) * ⟨b, hbD⟩ = ⟨b, hbD⟩ * ⟨z, hzD⟩ := Subtype.ext hzb
    calc F.phiA ⟨z, hzD⟩ * F.phiA ⟨b, hbD⟩
        = F.phiA (⟨z, hzD⟩ * ⟨b, hbD⟩) := (map_mul F.phiA _ _).symm
      _ = F.phiA (⟨b, hbD⟩ * ⟨z, hzD⟩) := by rw [h1]
      _ = F.phiA ⟨b, hbD⟩ * F.phiA ⟨z, hzD⟩ := map_mul F.phiA _ _
  have hdvd162 : orderOf (F.phiA ⟨z, hzD⟩) ∣ 162 := by
    rw [← hCcard]
    exact Subgroup.orderOf_dvd_natCard _ hcent
  obtain ⟨n, hn⟩ := hXp ⟨z, hzX⟩
  have hzpow : z ^ p ^ n = 1 := by
    simpa using congrArg Subtype.val hn
  have hdvdpow : orderOf (F.phiA ⟨z, hzD⟩) ∣ p ^ n := by
    apply orderOf_dvd_of_pow_eq_one
    have h1 : (⟨z, hzD⟩ : ↥D.M) ^ (p ^ n) = 1 := by
      apply Subtype.ext
      simpa using hzpow
    rw [← map_pow, h1, map_one]
  have hcop : Nat.Coprime (p ^ n) 162 := by
    have h := Nat.Coprime.pow n 1 ((hp.coprime_iff_not_dvd).mpr hp162)
    simpa using h
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvdpow hdvd162)

private theorem inf_pCoreOf_inf_pCore_two_eq_bot (F : A10Frame c) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {B : Subgroup G} (hBA : B ≤ F.A) (hB3 : Nat.card B = 3) :
    (CFSG.Open.pCoreOf p (Subgroup.centralizer (B : Set G)) ⊓ D.M) ⊓
      (CFSG.Open.pCore 2 ↥c.L).map c.L.subtype = ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set H : Subgroup G := Subgroup.centralizer (B : Set G)
  set X : Subgroup G := CFSG.Open.pCoreOf p H
  have hXp : IsPGroup p X := CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf p H
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨hwZ, hwO⟩ := Subgroup.mem_inf.mp hw
  obtain ⟨hwX, -⟩ := Subgroup.mem_inf.mp hwZ
  obtain ⟨n, hn⟩ := hXp ⟨w, hwX⟩
  have hwn : w ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hOw : IsPGroup 2 ((CFSG.Open.pCore 2 ↥c.L).map c.L.subtype) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)).map c.L.subtype
  obtain ⟨k, hk⟩ := hOw ⟨w, hwO⟩
  have hwk : w ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf w ∣ p ^ n := orderOf_dvd_of_pow_eq_one hwn
  have h2 : orderOf w ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hwk
  have hcop : Nat.Coprime (p ^ n) (2 ^ k) := by
    have hp2 : Nat.Coprime p 2 := by
      refine (hp.coprime_iff_not_dvd).mpr ?_
      intro h
      rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h1
      · exact hp.ne_one h1
      · omega
    exact Nat.Coprime.pow n k hp2
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2))

private theorem commutator_inf_pCoreOf_eq_one (F : A10Frame c) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {B : Subgroup G} (hBA : B ≤ F.A) (hB3 : Nat.card B = 3) (hB9 : F.deg B = 9) :
    ∀ g ∈ CFSG.Open.pCoreOf p (Subgroup.centralizer (B : Set G)) ⊓ D.M, ∀ h ∈ F.A,
      g * h * g⁻¹ * h⁻¹ = 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set H : Subgroup G := Subgroup.centralizer (B : Set G)
  set X : Subgroup G := CFSG.Open.pCoreOf p H
  set Z : Subgroup G := X ⊓ D.M
  have hAX : F.A ≤ Subgroup.normalizer (X : Set G) := F.A_le_normalizer_pCoreOf hBA
  have hZker : ∀ z ∈ Z, ∀ hzD : z ∈ D.M, F.phiA ⟨z, hzD⟩ = 1 :=
    F.phiA_eq_one_of_mem_inf_pCoreOf hp hp5 hBA hB3 hB9
  have hbot : Z ⊓ (CFSG.Open.pCore 2 ↥c.L).map c.L.subtype = ⊥ :=
    F.inf_pCoreOf_inf_pCore_two_eq_bot hp hp5 hBA hB3
  intro g hg h hh
  obtain ⟨hgX, hgM⟩ := Subgroup.mem_inf.mp hg
  have hhM : h ∈ D.M := F.A_le_M hh
  have hhL : h ∈ c.L := F.A_le.trans F.P_le_L hh
  have hmemZ : g * h * g⁻¹ * h⁻¹ ∈ Z := by
    constructor
    · have hhn : h ∈ Subgroup.normalizer (X : Set G) := hAX hh
      have hconj : h * g⁻¹ * h⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp hhn g⁻¹).mp (X.inv_mem hgX)
      have heq : g * h * g⁻¹ * h⁻¹ = g * (h * g⁻¹ * h⁻¹) := by group
      rw [heq]
      exact X.mul_mem hgX hconj
    · exact (D.M).mul_mem ((D.M).mul_mem ((D.M).mul_mem hgM hhM) ((D.M).inv_mem hgM))
        ((D.M).inv_mem hhM)
  have hmemL : g * h * g⁻¹ * h⁻¹ ∈ c.L := by
    have h1 : g * h * g⁻¹ ∈ c.L :=
      (Subgroup.mem_normalizer_iff.mp (c.le_normalizer_L hgM) h).mp hhL
    exact c.L.mul_mem h1 (c.L.inv_mem hhL)
  have hmemO : g * h * g⁻¹ * h⁻¹ ∈ (CFSG.Open.pCore 2 ↥c.L).map c.L.subtype := by
    rw [← F.phiA_eq_one_iff hmemL]
    have hg1 : F.phiA ⟨g, hgM⟩ = 1 := hZker g hg hgM
    have heq : (⟨g * h * g⁻¹ * h⁻¹, c.hyp81.1 hmemL⟩ : ↥D.M) =
        ⟨g, hgM⟩ * ⟨h, hhM⟩ * ⟨g, hgM⟩⁻¹ * ⟨h, hhM⟩⁻¹ := by
      ext
      simp
    rw [heq, map_mul, map_mul, map_mul, map_inv, map_inv, hg1]
    simp
  have hmem : g * h * g⁻¹ * h⁻¹ ∈ Z ⊓ (CFSG.Open.pCore 2 ↥c.L).map c.L.subtype :=
    Subgroup.mem_inf.mpr ⟨hmemZ, hmemO⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hmem

private theorem inf_pCoreOf_M_le_centralizer (F : A10Frame c) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {B : Subgroup G} (hBA : B ≤ F.A) (hB3 : Nat.card B = 3)
    (hB9 : F.deg B = 9) :
    CFSG.Open.pCoreOf p (Subgroup.centralizer (B : Set G)) ⊓ D.M ≤
      Subgroup.centralizer (F.A : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have h1 : z * a * z⁻¹ * a⁻¹ = 1 :=
    F.commutator_inf_pCoreOf_eq_one hp hp5 hBA hB3 hB9 z hz a ha
  have h2 : z * a * (a * z)⁻¹ = 1 := by
    rw [mul_inv_rev, ← mul_assoc]
    exact h1
  exact (mul_inv_eq_one.mp h2).symm

private theorem map_sup_phiA_of_zpowers (F : A10Frame c) {B : Subgroup G} {b d : G}
    (hbB : b ∈ B) (hBA : B ≤ F.A) (hBz : B = Subgroup.zpowers b) (hdA : d ∈ F.A) :
    ((B ⊔ Subgroup.zpowers d).subgroupOf D.M).map F.phiA =
      Subgroup.zpowers (F.phiA ⟨b, F.A_le_M (hBA hbB)⟩) ⊔
        Subgroup.zpowers (F.phiA ⟨d, F.A_le_M hdA⟩) := by
  have hdD : d ∈ D.M := F.A_le_M hdA
  have hBsub : B.subgroupOf D.M =
      Subgroup.zpowers (⟨b, F.A_le_M (hBA hbB)⟩ : ↥D.M) := by
    rw [hBz, subgroupOf_zpowers (F.A_le_M (hBA hbB))]
  have hdsub : (Subgroup.zpowers d).subgroupOf D.M =
      Subgroup.zpowers (⟨d, hdD⟩ : ↥D.M) := subgroupOf_zpowers hdD
  rw [Subgroup.subgroupOf_sup (hBA.trans F.A_le_M) (Subgroup.zpowers_le.mpr hdD),
    Subgroup.map_sup, hBsub, hdsub, MonoidHom.map_zpowers, MonoidHom.map_zpowers]

private theorem inf_ker_subgroupOf_sup_eq_bot (F : A10Frame c) {B : Subgroup G} {d : G}
    (hBA : B ≤ F.A) (hdA : d ∈ F.A) :
    ((B ⊔ Subgroup.zpowers d).subgroupOf D.M) ⊓ F.phiA.ker = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  have hx1' : (x : G) ∈ B ⊔ Subgroup.zpowers d := Subgroup.mem_subgroupOf.mp hx1
  have hx' : x ∈ F.A.subgroupOf D.M := by
    rw [Subgroup.mem_subgroupOf]
    exact (sup_le hBA (Subgroup.zpowers_le.mpr hdA)) hx1'
  have hmem : x ∈ F.A.subgroupOf D.M ⊓ F.phiA.ker := Subgroup.mem_inf.mpr ⟨hx', hx2⟩
  rwa [inf_ker_phiA_eq_bot F] at hmem

private theorem phiA_mem_sup_of_forall_deg_ne_three (F : A10Frame c) {B Z : Subgroup G} {b : G}
    (hbB : b ∈ B) (hBA : B ≤ F.A) (hBz : B = Subgroup.zpowers b) (hZA : Z ≤ F.A)
    (hBZ : B ≤ Z) (hZ : ∀ a ∈ Z, F.deg (Subgroup.zpowers a) ≠ 3) {i j k : Fin 3}
    (hi : i ≠ 0) (hj : j ≠ 0) (hk : k ≠ 0)
    (hx : F.phiA ⟨b, F.A_le_M (hBA hbB)⟩ = toP i j k) {z : G} (hz : z ∈ Z) :
    F.phiA ⟨z, F.A_le_M (hZA hz)⟩ ∈
      Subgroup.zpowers (toP i j k) ⊔ Subgroup.zpowers (toP i (j + j) 0) := by
  have hzD : z ∈ D.M := F.A_le_M (hZA hz)
  have hz_at : F.phiA ⟨z, hzD⟩ ∈ A10Perm.atilde := by
    have h1 : (⟨z, hzD⟩ : ↥D.M) ∈ F.A.subgroupOf D.M := by
      rw [Subgroup.mem_subgroupOf]
      exact hZA hz
    have h := Subgroup.mem_map_of_mem F.phiA h1
    rwa [F.map_A_phiA] at h
  obtain ⟨i', j', k', hijk'⟩ := A10Perm.mem_atilde_iff.mp hz_at
  have hysupp : ∀ u v : Fin 3,
      (toP i j k ^ (u : ℕ) * toP i' j' k' ^ (v : ℕ)).support.card ≠ 3 := by
    intro u v
    have hzZ : b ^ (u : ℕ) * z ^ (v : ℕ) ∈ Z :=
      Z.mul_mem (Z.pow_mem (hBZ hbB) u) (Z.pow_mem hz v)
    have hzL : b ^ (u : ℕ) * z ^ (v : ℕ) ∈ c.L := F.A_le.trans F.P_le_L (hZA hzZ)
    have hzdeg := hZ _ hzZ
    rw [F.deg_zpowers_eq hzL] at hzdeg
    have hzval : F.phiA ⟨b ^ (u : ℕ) * z ^ (v : ℕ), F.A_le_M (hZA hzZ)⟩ =
        toP i j k ^ (u : ℕ) * toP i' j' k' ^ (v : ℕ) := by
      have hprod : (⟨b ^ (u : ℕ) * z ^ (v : ℕ), F.A_le_M (hZA hzZ)⟩ : ↥D.M) =
          ⟨b, F.A_le_M (hBA hbB)⟩ ^ (u : ℕ) * ⟨z, hzD⟩ ^ (v : ℕ) := by
        ext
        simp [Subgroup.coe_pow]
      rw [hprod, map_mul, map_pow, map_pow, hx, hijk']
    rwa [hzval] at hzdeg
  obtain ⟨u, v, huv⟩ := A10Perm.exists_mem_zpowers_sup i j k hi hj hk i' j' k' hysupp
  rw [hijk', huv]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) u))
    (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) v))

private theorem card_sup_zpowers_of_phiA (F : A10Frame c) {B : Subgroup G} {b d : G}
    (hbB : b ∈ B) (hBA : B ≤ F.A) (hBz : B = Subgroup.zpowers b) (hdA : d ∈ F.A)
    {i j k : Fin 3} (hi : i ≠ 0) (hj : j ≠ 0) (hk : k ≠ 0)
    (hx : F.phiA ⟨b, F.A_le_M (hBA hbB)⟩ = toP i j k)
    (hy : F.phiA ⟨d, F.A_le_M hdA⟩ = toP i (j + j) 0) :
    Nat.card ↥(B ⊔ Subgroup.zpowers d) = 9 := by
  have hBdM : B ⊔ Subgroup.zpowers d ≤ D.M :=
    sup_le (hBA.trans F.A_le_M) (Subgroup.zpowers_le.mpr (F.A_le_M hdA))
  have hmap : ((B ⊔ Subgroup.zpowers d).subgroupOf D.M).map F.phiA =
      Subgroup.zpowers (toP i j k) ⊔ Subgroup.zpowers (toP i (j + j) 0) := by
    rw [F.map_sup_phiA_of_zpowers hbB hBA hBz hdA, hx, hy]
  have hcard1 : Nat.card ↥(B ⊔ Subgroup.zpowers d) =
      Nat.card ↥((B ⊔ Subgroup.zpowers d).subgroupOf D.M) :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBdM).toEquiv).symm
  have hcard2 : Nat.card ↥(((B ⊔ Subgroup.zpowers d).subgroupOf D.M).map F.phiA) =
      Nat.card ↥((B ⊔ Subgroup.zpowers d).subgroupOf D.M) :=
    CFSG.card_map_eq_card_of_inf_ker_eq_bot F.phiA (F.inf_ker_subgroupOf_sup_eq_bot hBA hdA)
  rw [hcard1, ← hcard2, hmap]
  exact A10Perm.card_sup_zpowers_eq_nine_perm
    (A10Perm.mem_atilde_iff.mpr ⟨i, j, k, rfl⟩)
    (A10Perm.mem_atilde_iff.mpr ⟨i, j + j, 0, rfl⟩)
    (A10Perm.toP_ne_one i j k hi hj hk) (A10Perm.toP_notMem_zpowers i j k hi hk)

private theorem deg_ne_three_of_mem_sup (F : A10Frame c) {B : Subgroup G} {b d : G}
    (hbB : b ∈ B) (hBA : B ≤ F.A) (hBz : B = Subgroup.zpowers b) (hdA : d ∈ F.A)
    {i j k : Fin 3} (hi : i ≠ 0) (hj : j ≠ 0) (hk : k ≠ 0)
    (hx : F.phiA ⟨b, F.A_le_M (hBA hbB)⟩ = toP i j k)
    (hy : F.phiA ⟨d, F.A_le_M hdA⟩ = toP i (j + j) 0) {a : G}
    (ha : a ∈ B ⊔ Subgroup.zpowers d) : F.deg (Subgroup.zpowers a) ≠ 3 := by
  have haA : a ∈ F.A := (sup_le hBA (Subgroup.zpowers_le.mpr hdA)) ha
  have hmem : F.phiA ⟨a, F.A_le_M haA⟩ ∈
      Subgroup.zpowers (toP i j k) ⊔ Subgroup.zpowers (toP i (j + j) 0) := by
    have h1 : (⟨a, F.A_le_M haA⟩ : ↥D.M) ∈ (B ⊔ Subgroup.zpowers d).subgroupOf D.M := by
      rw [Subgroup.mem_subgroupOf]
      exact ha
    have h2 := Subgroup.mem_map_of_mem F.phiA h1
    rwa [F.map_sup_phiA_of_zpowers hbB hBA hBz hdA, hx, hy] at h2
  obtain ⟨u, v, huv⟩ := A10Perm.exists_pow_mul_of_mem_sup_perm
    (A10Perm.mem_atilde_iff.mpr ⟨i, j, k, rfl⟩)
    (A10Perm.mem_atilde_iff.mpr ⟨i, j + j, 0, rfl⟩) hmem
  rw [F.deg_zpowers_eq (F.A_le.trans F.P_le_L haA), huv]
  exact A10Perm.support_pow_mul_ne_three i j k hi hj hk u v

private theorem exists_generator_coordinates (F : A10Frame c) {B : Subgroup G} (hBA : B ≤ F.A)
    (hB3 : Nat.card B = 3) (hB9 : F.deg B = 9) :
    ∃ (b : G) (i j k : Fin 3) (hb : b ∈ B),
      b ≠ 1 ∧ B = Subgroup.zpowers b ∧ i ≠ 0 ∧ j ≠ 0 ∧ k ≠ 0 ∧
        F.phiA ⟨b, F.A_le_M (hBA hb)⟩ = toP i j k := by
  obtain ⟨b, hbB, hb1⟩ := exists_generator_of_card_three hB3
  have hbA : b ∈ F.A := hBA hbB
  have hbD : b ∈ D.M := F.A_le_M hbA
  have hBz : B = Subgroup.zpowers b := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbB) ?_).symm
    rw [hB3, F.card_zpowers_of_mem_A hbA hb1]
  have hbsupp : (F.phiA ⟨b, hbD⟩).support.card = 9 := by
    rw [← F.deg_zpowers_eq (F.A_le.trans F.P_le_L hbA), ← hBz]
    exact hB9
  obtain ⟨i, j, k, hijk⟩ : ∃ i j k : Fin 3, F.phiA ⟨b, hbD⟩ = toP i j k := by
    refine A10Perm.mem_atilde_iff.mp ?_
    have h1 : (⟨b, hbD⟩ : ↥D.M) ∈ F.A.subgroupOf D.M := by
      rw [Subgroup.mem_subgroupOf]
      exact hbA
    have h := Subgroup.mem_map_of_mem F.phiA h1
    rwa [F.map_A_phiA] at h
  have h9 : (toP i j k).support.card = 9 := by rw [← hijk]; exact hbsupp
  obtain ⟨hi, hj, hk⟩ := (A10Perm.card_support_eq_nine_iff i j k).mp h9
  exact ⟨b, i, j, k, hbB, hb1, hBz, hi, hj, hk, hijk⟩

private theorem exists_hyperplane_data (F : A10Frame c) {B : Subgroup G} (hBA : B ≤ F.A)
    (hB3 : Nat.card B = 3) (hB9 : F.deg B = 9) :
    ∃ d ∈ F.A, Nat.card ↥(B ⊔ Subgroup.zpowers d) = 9 ∧
      ∀ a ∈ B ⊔ Subgroup.zpowers d, F.deg (Subgroup.zpowers a) ≠ 3 := by
  obtain ⟨b, i, j, k, hbB, -, hBz, hi, hj, hk, hijk⟩ :=
    F.exists_generator_coordinates hBA hB3 hB9
  obtain ⟨d, hdA, hdval⟩ := F.exists_mem_A_phiA_eq
    (y := toP i (j + j) 0) (A10Perm.mem_atilde_iff.mpr ⟨i, j + j, 0, rfl⟩)
  exact ⟨d, hdA, F.card_sup_zpowers_of_phiA hbB hBA hBz hdA hi hj hk hijk hdval,
    fun a ha => F.deg_ne_three_of_mem_sup hbB hBA hBz hdA hi hj hk hijk hdval ha⟩

private theorem card_sup_zpowers_phiA_of_card_sup (F : A10Frame c) {B : Subgroup G} {b d : G}
    (hbB : b ∈ B) (hBA : B ≤ F.A) (hBz : B = Subgroup.zpowers b) (hdA : d ∈ F.A)
    (hd9 : Nat.card ↥(B ⊔ Subgroup.zpowers d) = 9) :
    Nat.card ↥(Subgroup.zpowers (F.phiA ⟨b, F.A_le_M (hBA hbB)⟩) ⊔
      Subgroup.zpowers (F.phiA ⟨d, F.A_le_M hdA⟩)) = 9 := by
  have hBdM : B ⊔ Subgroup.zpowers d ≤ D.M :=
    sup_le (hBA.trans F.A_le_M) (Subgroup.zpowers_le.mpr (F.A_le_M hdA))
  calc Nat.card ↥(Subgroup.zpowers (F.phiA ⟨b, F.A_le_M (hBA hbB)⟩) ⊔
        Subgroup.zpowers (F.phiA ⟨d, F.A_le_M hdA⟩))
      = Nat.card ↥(((B ⊔ Subgroup.zpowers d).subgroupOf D.M).map F.phiA) := by
        rw [F.map_sup_phiA_of_zpowers hbB hBA hBz hdA]
    _ = Nat.card ↥((B ⊔ Subgroup.zpowers d).subgroupOf D.M) :=
        CFSG.card_map_eq_card_of_inf_ker_eq_bot F.phiA (F.inf_ker_subgroupOf_sup_eq_bot hBA hdA)
    _ = Nat.card ↥(B ⊔ Subgroup.zpowers d) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBdM).toEquiv
    _ = 9 := hd9

private theorem mem_sup_of_phiA_mem (F : A10Frame c) {B : Subgroup G} {b d z : G}
    (hbB : b ∈ B) (hBA : B ≤ F.A) (hBz : B = Subgroup.zpowers b) (hdA : d ∈ F.A)
    (hzA : z ∈ F.A)
    (hmem : F.phiA ⟨z, F.A_le_M hzA⟩ ∈
      Subgroup.zpowers (F.phiA ⟨b, F.A_le_M (hBA hbB)⟩) ⊔
        Subgroup.zpowers (F.phiA ⟨d, F.A_le_M hdA⟩)) :
    z ∈ B ⊔ Subgroup.zpowers d := by
  have h2 : F.phiA ⟨z, F.A_le_M hzA⟩ ∈
      ((B ⊔ Subgroup.zpowers d).subgroupOf D.M).map F.phiA := by
    rw [F.map_sup_phiA_of_zpowers hbB hBA hBz hdA]
    exact hmem
  obtain ⟨w, hw, hwφ⟩ := Subgroup.mem_map.mp h2
  have hwA : w ∈ F.A.subgroupOf D.M :=
    Subgroup.mem_subgroupOf.mpr
      ((sup_le hBA (Subgroup.zpowers_le.mpr hdA)) (Subgroup.mem_subgroupOf.mp hw))
  have h3 : w = ⟨z, F.A_le_M hzA⟩ :=
    phiA_inj_of_mem F hwA (Subgroup.mem_subgroupOf.mpr hzA) hwφ
  exact Subgroup.mem_subgroupOf.mp (h3 ▸ hw)

private theorem le_sup_zpowers_of_forall_deg_ne_three (F : A10Frame c) {B : Subgroup G}
    (hBA : B ≤ F.A) (hB3 : Nat.card B = 3) (hB9 : F.deg B = 9) {d : G} (hdA : d ∈ F.A)
    (hd9 : Nat.card ↥(B ⊔ Subgroup.zpowers d) = 9)
    (hd : ∀ a ∈ B ⊔ Subgroup.zpowers d, F.deg (Subgroup.zpowers a) ≠ 3)
    {S : Subgroup G} (hSA : S ≤ F.A) (hBS : B ≤ S)
    (hS : ∀ a ∈ S, F.deg (Subgroup.zpowers a) ≠ 3) :
    S ≤ B ⊔ Subgroup.zpowers d := by
  classical
  obtain ⟨b, i, j, k, hbB, -, hBz, hi, hj, hk, hijk⟩ :=
    F.exists_generator_coordinates hBA hB3 hB9
  have hx_at : toP i j k ∈ A10Perm.atilde := A10Perm.mem_atilde_iff.mpr ⟨i, j, k, rfl⟩
  have hy_at : toP i (j + j) 0 ∈ A10Perm.atilde :=
    A10Perm.mem_atilde_iff.mpr ⟨i, j + j, 0, rfl⟩
  have hd_mem : F.phiA ⟨d, F.A_le_M hdA⟩ ∈
      Subgroup.zpowers (toP i j k) ⊔ Subgroup.zpowers (toP i (j + j) 0) :=
    F.phiA_mem_sup_of_forall_deg_ne_three hbB hBA hBz
      (sup_le hBA (Subgroup.zpowers_le.mpr hdA)) le_sup_left hd hi hj hk hijk
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))
  have hW9 : Nat.card ↥(Subgroup.zpowers (toP i j k) ⊔
      Subgroup.zpowers (toP i (j + j) 0)) = 9 :=
    A10Perm.card_sup_zpowers_eq_nine_perm hx_at hy_at
      (A10Perm.toP_ne_one i j k hi hj hk) (A10Perm.toP_notMem_zpowers i j k hi hk)
  have hVle : Subgroup.zpowers (toP i j k) ⊔
      Subgroup.zpowers (F.phiA ⟨d, F.A_le_M hdA⟩) ≤
      Subgroup.zpowers (toP i j k) ⊔ Subgroup.zpowers (toP i (j + j) 0) :=
    sup_le le_sup_left (Subgroup.zpowers_le.mpr hd_mem)
  have hV9 : Nat.card ↥(Subgroup.zpowers (toP i j k) ⊔
      Subgroup.zpowers (F.phiA ⟨d, F.A_le_M hdA⟩)) = 9 := by
    rw [← hijk]
    exact F.card_sup_zpowers_phiA_of_card_sup hbB hBA hBz hdA hd9
  have hVeq : Subgroup.zpowers (toP i j k) ⊔ Subgroup.zpowers (F.phiA ⟨d, F.A_le_M hdA⟩) =
      Subgroup.zpowers (toP i j k) ⊔ Subgroup.zpowers (toP i (j + j) 0) :=
    Subgroup.eq_of_le_of_card_ge hVle (by rw [hW9, hV9])
  intro s hs
  by_cases hsB : s ∈ B
  · exact Subgroup.mem_sup_left hsB
  have hsA : s ∈ F.A := hSA hs
  have hs_mem : F.phiA ⟨s, F.A_le_M hsA⟩ ∈
      Subgroup.zpowers (toP i j k) ⊔ Subgroup.zpowers (toP i (j + j) 0) :=
    F.phiA_mem_sup_of_forall_deg_ne_three hbB hBA hBz hSA hBS hS hi hj hk hijk hs
  rw [← hVeq, ← hijk] at hs_mem
  exact F.mem_sup_of_phiA_mem hbB hBA hBz hdA hsA hs_mem

private theorem exists_hyperplane_aux (F : A10Frame c) {B : Subgroup G} (hBA : B ≤ F.A)
    (hB3 : Nat.card B = 3) (hB9 : F.deg B = 9) :
    ∃ d ∈ F.A, Nat.card ↥(B ⊔ Subgroup.zpowers d) = 9 ∧
      (∀ a ∈ B ⊔ Subgroup.zpowers d, F.deg (Subgroup.zpowers a) ≠ 3) ∧
      (∀ S : Subgroup G, S ≤ F.A → B ≤ S →
        (∀ a ∈ S, F.deg (Subgroup.zpowers a) ≠ 3) → S ≤ B ⊔ Subgroup.zpowers d) := by
  obtain ⟨d, hdA, hd9, hd⟩ := F.exists_hyperplane_data hBA hB3 hB9
  exact ⟨d, hdA, hd9, hd, fun S hSA hBS hS =>
    F.le_sup_zpowers_of_forall_deg_ne_three hBA hB3 hB9 hdA hd9 hd hSA hBS hS⟩

theorem exists_hyperplane_deg_ne_three (F : A10Frame c) {B : Subgroup G} (hBA : B ≤ F.A)
    (hB3 : Nat.card B = 3) (hB9 : F.deg B = 9) :
    ∃ d ∈ F.A, Nat.card ↥(B ⊔ Subgroup.zpowers d) = 9 ∧
      ∀ a ∈ B ⊔ Subgroup.zpowers d, F.deg (Subgroup.zpowers a) ≠ 3 := by
  obtain ⟨d, hdA, h9, hnd, -⟩ := F.exists_hyperplane_aux hBA hB3 hB9
  exact ⟨d, hdA, h9, hnd⟩

private theorem exists_complement (F : A10Frame c) {B : Subgroup G} (hBA : B ≤ F.A)
    (hB3 : Nat.card B = 3) :
    ∃ E : Subgroup G, E ≤ F.A ∧ E ⊓ B = ⊥ ∧ Nat.card E = 9 := by
  classical
  haveI : CFSG.IsElementaryAbelian 3 ↥F.A := F.elemAbelian.isElementaryAbelian
  obtain ⟨C, hC⟩ := CFSG.IsElementaryAbelian.exists_isCompl 3 ↥F.A (B.subgroupOf F.A)
  let E : Subgroup G := C.map F.A.subtype
  have hEA : E ≤ F.A := Subgroup.map_subtype_le C
  have hCE : Nat.card C = Nat.card E :=
    (Subgroup.card_map_of_injective F.A.subtype_injective).symm
  have hEsub : E.subgroupOf F.A = C := by
    apply Subgroup.map_injective F.A.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hEA]
  have hEinf : E ⊓ B = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxE, hxB⟩ := Subgroup.mem_inf.mp hx
    have hxFA : x ∈ F.A := hEA hxE
    have h1 : (⟨x, hxFA⟩ : ↥F.A) ∈ E.subgroupOf F.A := Subgroup.mem_subgroupOf.mpr hxE
    have h2 : (⟨x, hxFA⟩ : ↥F.A) ∈ B.subgroupOf F.A := Subgroup.mem_subgroupOf.mpr hxB
    rw [hEsub] at h1
    have hmem : (⟨x, hxFA⟩ : ↥F.A) ∈ B.subgroupOf F.A ⊓ C :=
      Subgroup.mem_inf.mpr ⟨h2, h1⟩
    have hbot : B.subgroupOf F.A ⊓ C = ⊥ := by
      have hd := hC.disjoint
      rwa [disjoint_iff] at hd
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    simpa using congrArg Subtype.val hmem
  have hE9 : Nat.card E = 9 := by
    haveI : IsMulCommutative ↥F.A := F.elemAbelian.1
    have hnorm : B.subgroupOf F.A ≤ Subgroup.normalizer (C : Set ↥F.A) := by
      refine Subgroup.le_normalizer_iff.mpr fun x hx y hy => ?_
      have hcomm : x * y = y * x := F.elemAbelian.1.is_comm.comm x y
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      exact hy
    have hB3' : Nat.card ↥(B.subgroupOf F.A) = 3 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBA).toEquiv, hB3]
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := B.subgroupOf F.A) (K := C) hnorm
    have hbot : B.subgroupOf F.A ⊓ C = ⊥ := by
      have hd := hC.disjoint
      rwa [disjoint_iff] at hd
    rw [hC.sup_eq_top, hbot, hB3'] at h
    have htop : Nat.card ↥(⊤ : Subgroup ↥F.A) = 27 := by
      rw [Nat.card_congr (Subgroup.topEquiv (G := ↥F.A)).toEquiv]
      exact F.card_A
    rw [htop] at h
    simp at h
    omega
  exact ⟨E, hEA, hEinf, hE9⟩

private theorem card_sup_zpowers_eq_nine_of_complement (F : A10Frame c) {B : Subgroup G}
    (hBA : B ≤ F.A) (hB3 : Nat.card B = 3) {E : Subgroup G} (hEA : E ≤ F.A)
    (hEinf : E ⊓ B = ⊥) {e : G} (he : e ∈ E) (he1 : e ≠ 1) :
    Nat.card ↥(B ⊔ Subgroup.zpowers e) = 9 := by
    haveI : IsMulCommutative ↥F.A := F.elemAbelian.1
    have hBe : B ≤ F.A := hBA
    have heA : e ∈ F.A := hEA he
    have hnorm : B ≤ Subgroup.normalizer (Subgroup.zpowers e : Set G) := by
      refine Subgroup.le_normalizer_iff.mpr fun x hx y hy => ?_
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hcomm : x * e ^ k = e ^ k * x := by
        have h := F.elemAbelian.1.is_comm.comm (⟨x, hBA hx⟩ : F.A) ⟨e ^ k, hEA (E.zpow_mem he k)⟩
        simpa using h
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers e) k
    have h := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := B) (K := Subgroup.zpowers e) hnorm
    have hinf : B ⊓ Subgroup.zpowers e = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      obtain ⟨hzB, hze⟩ := Subgroup.mem_inf.mp hz
      have hzE : z ∈ E := by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hze
        exact E.zpow_mem he k
      have h1 : z ∈ E ⊓ B := Subgroup.mem_inf.mpr ⟨hzE, hzB⟩
      rwa [hEinf] at h1
    have hze : Nat.card ↥(Subgroup.zpowers e) = 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (F.elemAbelian.2 e heA) he1
    rw [hinf, hB3, hze] at h
    simp at h
    exact h

private theorem inf_pCoreOf_inf_centralizer_le_sup (F : A10Frame c) {p : ℕ} {B : Subgroup G}
    (hBA : B ≤ F.A) {e : G} :
    CFSG.Open.pCoreOf p (Subgroup.centralizer (B : Set G)) ⊓
        Subgroup.centralizer ({e} : Set G) ≤
      Subgroup.centralizer ((B ⊔ Subgroup.zpowers e : Subgroup G) : Set G) := by
    intro x hx
    obtain ⟨hxX, hxe⟩ := Subgroup.mem_inf.mp hx
    have hxH : x ∈ Subgroup.centralizer (B : Set G) :=
      CFSG.ClassicalGroups.PCoreSection.pCoreOf_le p (Subgroup.centralizer (B : Set G)) hxX
    have hxB : B ≤ Subgroup.centralizer ({x} : Set G) := by
      intro b' hb'
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hxH b' hb'
    have hxE : Subgroup.zpowers e ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hxe).symm
    have hsup : B ⊔ Subgroup.zpowers e ≤ Subgroup.centralizer ({x} : Set G) := sup_le hxB hxE
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hsup hy)

private theorem not_three_dvd_card_pCoreOf (F : A10Frame c) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {B : Subgroup G} :
    ¬ 3 ∣ Nat.card (CFSG.Open.pCoreOf p (Subgroup.centralizer (B : Set G))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hXp : IsPGroup p (CFSG.Open.pCoreOf p (Subgroup.centralizer (B : Set G))) :=
    CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf p _
  obtain ⟨n, hn⟩ := hXp.exists_card_eq
  rw [hn]
  intro h3
  have h3p : (3 : ℕ) ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  rcases hp.eq_one_or_self_of_dvd 3 h3p with h1 | h1
  · omega
  · omega

private theorem inf_centralizer_le_of_exists_deg_three (F : A10Frame c) (hF : A10Facts F)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {B Y : Subgroup G} (hBA : B ≤ F.A)
    (hB3 : Nat.card B = 3) (hB9 : F.deg B = 9) {E : Subgroup G} (hEA : E ≤ F.A) {e : G}
    (he : e ∈ E) (hYA : Y ≤ F.A)
    (h3 : ∃ a ∈ B ⊔ Subgroup.zpowers e, F.deg (Subgroup.zpowers a) = 3) :
    CFSG.Open.pCoreOf p (Subgroup.centralizer (B : Set G)) ⊓ Subgroup.centralizer ({e} : Set G) ≤
      Subgroup.centralizer (Y : Set G) := by
  obtain ⟨a, ha, ha3⟩ := h3
  have haA : a ∈ F.A := (sup_le hBA (Subgroup.zpowers_le.mpr (hEA he))) ha
  have hM : CFSG.Open.pCoreOf p (Subgroup.centralizer (B : Set G)) ⊓
      Subgroup.centralizer ({e} : Set G) ≤ D.M :=
    (F.inf_pCoreOf_inf_centralizer_le_sup hBA).trans
      ((Subgroup.centralizer_le (by
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        exact hy ▸ ha)).trans (F.centralizer_le_M_of_deg_three hF haA ha3))
  refine (le_inf inf_le_left hM).trans ?_
  refine (F.inf_pCoreOf_M_le_centralizer hp hp5 hBA hB3 hB9).trans (Subgroup.centralizer_le ?_)
  intro y hy
  exact hYA hy

private theorem inf_centralizer_le_of_no_deg_three (F : A10Frame c) {p : ℕ} {B Y : Subgroup G}
    (hBA : B ≤ F.A) (hB3 : Nat.card B = 3) {E : Subgroup G} (hEA : E ≤ F.A)
    (hEinf : E ⊓ B = ⊥) {e : G} (he : e ∈ E) (he1 : e ≠ 1) {d : G}
    (hd9 : Nat.card ↥(B ⊔ Subgroup.zpowers d) = 9)
    (hduniq : ∀ S : Subgroup G, S ≤ F.A → B ≤ S →
      (∀ a ∈ S, F.deg (Subgroup.zpowers a) ≠ 3) → S ≤ B ⊔ Subgroup.zpowers d)
    (hYB : Y ≤ B ⊔ Subgroup.zpowers d)
    (h3 : ¬ ∃ a ∈ B ⊔ Subgroup.zpowers e, F.deg (Subgroup.zpowers a) = 3) :
    CFSG.Open.pCoreOf p (Subgroup.centralizer (B : Set G)) ⊓ Subgroup.centralizer ({e} : Set G) ≤
      Subgroup.centralizer (Y : Set G) := by
  push Not at h3
  have hpair9 := F.card_sup_zpowers_eq_nine_of_complement hBA hB3 hEA hEinf he he1
  have hSle : B ⊔ Subgroup.zpowers e ≤ B ⊔ Subgroup.zpowers d :=
    hduniq (B ⊔ Subgroup.zpowers e) (sup_le hBA (Subgroup.zpowers_le.mpr (hEA he)))
      le_sup_left h3
  have heq : B ⊔ Subgroup.zpowers e = B ⊔ Subgroup.zpowers d :=
    Subgroup.eq_of_le_of_card_ge hSle (by rw [hpair9, hd9])
  refine (F.inf_pCoreOf_inf_centralizer_le_sup hBA).trans (Subgroup.centralizer_le ?_)
  intro y hy
  rw [heq]
  exact hYB hy

theorem pCoreOf_centralizer_le_centralizer (F : A10Frame c) (hF : A10Facts F) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {B Y : Subgroup G} (hBA : B ≤ F.A) (hB3 : Nat.card B = 3)
    (hB9 : F.deg B = 9) (hYA : Y ≤ F.A) (hY : ∀ a ∈ B ⊔ Y, F.deg (Subgroup.zpowers a) ≠ 3) :
    CFSG.Open.pCoreOf p (Subgroup.centralizer (B : Set G)) ≤
      Subgroup.centralizer (Y : Set G) := by
  classical
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  set H : Subgroup G := Subgroup.centralizer (B : Set G)
  set X : Subgroup G := CFSG.Open.pCoreOf p H
  have hAX : F.A ≤ Subgroup.normalizer (X : Set G) := F.A_le_normalizer_pCoreOf hBA
  have hX3 : ¬ 3 ∣ Nat.card X := F.not_three_dvd_card_pCoreOf hp hp5
  obtain ⟨d, hdA, hd9, hd, hduniq⟩ := F.exists_hyperplane_aux hBA hB3 hB9
  have hYB : Y ≤ B ⊔ Subgroup.zpowers d :=
    le_trans le_sup_right (hduniq (B ⊔ Y) (sup_le hBA hYA) le_sup_left hY)
  obtain ⟨E, hEA, hEinf, hE9⟩ := F.exists_complement hBA hB3
  have hgen := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma123.le_iSup_inf_centralizer
    (p := 3) (P := E) (X := X) (F.elemAbelian.mono hEA) (by rw [hE9]; norm_num) hX3
    (hEA.trans hAX)
  refine le_trans hgen (iSup_le fun e => iSup_le fun he => iSup_le fun he1 => ?_)
  by_cases hcase : ∃ a ∈ B ⊔ Subgroup.zpowers e, F.deg (Subgroup.zpowers a) = 3
  · exact F.inf_centralizer_le_of_exists_deg_three hF hp hp5 hBA hB3 hB9 hEA he hYA hcase
  · exact F.inf_centralizer_le_of_no_deg_three hBA hB3 hEA hEinf he he1 hd9 hduniq hYB hcase

end Ctx82E3.A10Frame

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

end
