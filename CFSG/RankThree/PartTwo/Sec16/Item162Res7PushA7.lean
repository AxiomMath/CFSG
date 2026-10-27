module

public import CFSG.RankThree.PartTwo.Sec16.Item162Res7Push
public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating7Rep
public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating7Conj
import CFSG.GroupTheory.PCore.InfPCoreOf
import CFSG.RankThree.PartTwo.Sec14.Item1411
import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private def centralizingModPCore (K S : Subgroup G)
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) : Subgroup G where
  carrier := {y | y ∈ K ⊔ S ∧ ∀ z ∈ K, y * z * y⁻¹ * z⁻¹ ∈ CFSG.Open.pCoreOf 2 (K ⊔ S)}
  one_mem' := ⟨one_mem _, fun z _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨mul_mem ha hb, fun z hz => ?_⟩
    have hKSR : K ⊔ S ≤
        Subgroup.normalizer (CFSG.Open.pCoreOf 2 (K ⊔ S) : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ S)
    have hconj : a * (b * z * b⁻¹ * z⁻¹) * a⁻¹ ∈ CFSG.Open.pCoreOf 2 (K ⊔ S) :=
      (Subgroup.mem_normalizer_iff.mp (hKSR ha) _).mp (hb' z hz)
    have e : a * b * z * (a * b)⁻¹ * z⁻¹ =
        a * (b * z * b⁻¹ * z⁻¹) * a⁻¹ * (a * z * a⁻¹ * z⁻¹) := by group
    rw [e]
    exact mul_mem hconj (ha' z hz)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨inv_mem ha, fun z hz => ?_⟩
    have hKS : K ⊔ S ≤ Subgroup.normalizer (K : Set G) :=
      sup_le Subgroup.le_normalizer hSK
    have hz' : a⁻¹ * z * a ∈ K := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hKS (inv_mem ha)) z).mp hz
    have h1 := ha' _ hz'
    have e : a * (a⁻¹ * z * a) * a⁻¹ * (a⁻¹ * z * a)⁻¹ = (a⁻¹ * z * a * z⁻¹)⁻¹ := by
      group
    rw [e] at h1
    simpa using inv_mem h1

private theorem centralizingModPCore_le {K S : Subgroup G}
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) :
    centralizingModPCore K S hSK ≤ K ⊔ S :=
  fun _ hy => hy.1

private theorem inf_centralizingModPCore_le {K S : Subgroup G}
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) :
    centralizingModPCore K S hSK ⊓ K ≤ CFSG.Open.pCoreOf 2 K := by
  intro y hy
  obtain ⟨hyC, hyK⟩ := Subgroup.mem_inf.mp hy
  have hyC' : y ∈ K ⊔ S ∧
      ∀ z ∈ K, y * z * y⁻¹ * z⁻¹ ∈ CFSG.Open.pCoreOf 2 (K ⊔ S) := hyC
  have hcomm : ∀ z ∈ K, y * z * y⁻¹ * z⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
    intro z hz
    refine CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 (le_sup_left : K ≤ K ⊔ S)
      ⟨?_, hyC'.2 z hz⟩
    exact K.mul_mem (K.mul_mem (K.mul_mem hyK hz) (K.inv_mem hyK)) (K.inv_mem hz)
  have hcent : ((⟨y, hyK⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) ∈
      Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) w
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      QuotientGroup.eq_iff_div_mem]
    refine (CFSG.mem_openPCoreOf_iff (p := 2) (H := K)
      (u * ⟨y, hyK⟩ / (⟨y, hyK⟩ * u))).mp ?_
    have hgoal : ((u * ⟨y, hyK⟩ / (⟨y, hyK⟩ * u) : ↥K) : G) =
        (u : G) * ((⟨y, hyK⟩ : ↥K) : G) * (u : G)⁻¹ * ((⟨y, hyK⟩ : ↥K) : G)⁻¹ := by
      simp [div_eq_mul_inv, mul_assoc]
    rw [hgoal]
    simpa [mul_assoc] using inv_mem (hcomm u u.2)
  rw [hZ, Subgroup.mem_bot] at hcent
  have hmem : (⟨y, hyK⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := (QuotientGroup.eq_one_iff _).mp hcent
  exact (CFSG.mem_openPCoreOf_iff (p := 2) (H := K) ⟨y, hyK⟩).mpr hmem

private theorem isPGroup_centralizingModPCore {K S : Subgroup G} (hS : IsPGroup 2 S)
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) :
    IsPGroup 2 (centralizingModPCore K S hSK) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCKS : centralizingModPCore K S hSK ≤ K ⊔ S := centralizingModPCore_le hSK
  have hCK : centralizingModPCore K S hSK ⊓ K ≤ CFSG.Open.pCoreOf 2 K :=
    inf_centralizingModPCore_le hSK hZ
  intro c
  have hcC' : (c : G) ∈ K ⊔ S ∧
      ∀ z ∈ K, (c : G) * z * (c : G)⁻¹ * z⁻¹ ∈ CFSG.Open.pCoreOf 2 (K ⊔ S) := c.2
  have hc : (c : G) ∈ K ⊔ S := hcC'.1
  have hc' : (c : G) ∈ (K : Set G) * (S : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left K S hSK]
    simpa using hc
  obtain ⟨k, hk, s, hs, hks⟩ := hc'
  obtain ⟨n, hn⟩ := hS ⟨s, hs⟩
  have hn' : s ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have key : ∀ m : ℕ, ∃ k' ∈ K, (c : G) ^ 2 ^ m = k' * s ^ 2 ^ m := by
    intro m
    induction m with
    | zero => exact ⟨k, hk, by simp [← hks]⟩
    | succ m ih =>
      obtain ⟨km, hkm, hkm'⟩ := ih
      set t : G := s ^ 2 ^ m with ht
      refine ⟨km * (t * km * t⁻¹), K.mul_mem hkm ?_, ?_⟩
      · rw [ht]
        exact (Subgroup.mem_normalizer_iff.mp (hSK (Subgroup.pow_mem S hs (2 ^ m))) km).mp hkm
      · calc (c : G) ^ 2 ^ (m + 1)
            = ((c : G) ^ 2 ^ m) ^ 2 := by rw [Nat.pow_succ, ← pow_mul]
          _ = (km * t) ^ 2 := by rw [hkm', ht]
          _ = km * (t * km * t⁻¹) * (t * t) := by rw [pow_two]; simp [mul_assoc]
          _ = km * (t * km * t⁻¹) * s ^ 2 ^ (m + 1) := by
                rw [ht, ← pow_two, Nat.pow_succ, ← pow_mul]
  obtain ⟨kn, hkn, hkn'⟩ := key n
  have hpowK : (c : G) ^ 2 ^ n ∈ K := by
    rw [hkn', hn', mul_one]
    exact hkn
  have hmemC : (c : G) ^ 2 ^ n ∈ centralizingModPCore K S hSK :=
    Subgroup.pow_mem _ c.2 (2 ^ n)
  have hmemO : (c : G) ^ 2 ^ n ∈ CFSG.Open.pCoreOf 2 K := hCK ⟨hmemC, hpowK⟩
  obtain ⟨m, hm⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K
    ⟨(c : G) ^ 2 ^ n, hmemO⟩
  refine ⟨n + m, Subtype.ext ?_⟩
  have h1 : ((c : G) ^ 2 ^ n) ^ 2 ^ m = 1 := by
    simpa using congrArg Subtype.val hm
  have h2 : (c : G) ^ 2 ^ (n + m) = ((c : G) ^ 2 ^ n) ^ 2 ^ m := by
    rw [Nat.pow_add, pow_mul]
  show ((c : G) ^ 2 ^ (n + m)) = 1
  rw [h2, h1]

private theorem le_normalizer_centralizingModPCore {K S : Subgroup G}
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) :
    K ⊔ S ≤ Subgroup.normalizer (centralizingModPCore K S hSK : Set G) := by
  have hKS : K ⊔ S ≤ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer hSK
  intro g hg
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  have hy' : y ∈ K ⊔ S ∧
      ∀ z ∈ K, y * z * y⁻¹ * z⁻¹ ∈ CFSG.Open.pCoreOf 2 (K ⊔ S) := hy
  refine ⟨(K ⊔ S).mul_mem ((K ⊔ S).mul_mem hg hy'.1) ((K ⊔ S).inv_mem hg), fun z hz => ?_⟩
  have hz' : g⁻¹ * z * g ∈ K := by
    simpa using (Subgroup.mem_normalizer_iff.mp (hKS (inv_mem hg)) z).mp hz
  have h1 : y * (g⁻¹ * z * g) * y⁻¹ * (g⁻¹ * z * g)⁻¹ ∈ CFSG.Open.pCoreOf 2 (K ⊔ S) :=
    hy'.2 _ hz'
  have e : g * y * g⁻¹ * z * (g * y * g⁻¹)⁻¹ * z⁻¹ =
      g * (y * (g⁻¹ * z * g) * y⁻¹ * (g⁻¹ * z * g)⁻¹) * g⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp
    ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ S)) hg) _).mp h1

theorem mem_pCoreOf_sup_of_commutator_mem {K S : Subgroup G} (hS : IsPGroup 2 S)
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) {x : G} (hx : x ∈ K ⊔ S)
    (hxK : ∀ y ∈ K, x * y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 (K ⊔ S)) :
    x ∈ CFSG.Open.pCoreOf 2 (K ⊔ S) :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (centralizingModPCore_le hSK) (le_normalizer_centralizingModPCore hSK)
    (isPGroup_centralizingModPCore hS hSK hZ) ⟨hx, hxK⟩

private theorem mem_normalizer_sup_of_mem_normalizer {K S : Subgroup G}
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) {b : G}
    (hbK : b ∈ Subgroup.normalizer (K : Set G))
    (hbS : b ∈ Subgroup.normalizer (S : Set G)) :
    b ∈ Subgroup.normalizer (K ⊔ S : Subgroup G) := by
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  have hz' : z ∈ (K : Set G) * (S : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left K S hSK]
    simpa using hz
  obtain ⟨k, hk, s, hs, rfl⟩ := hz'
  have e : b * (k * s) * b⁻¹ = (b * k * b⁻¹) * (b * s * b⁻¹) := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hbK k).mp hk))
    (Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hbS s).mp hs))

private theorem commutator_centralizes_mod_pCoreOf {K S : Subgroup G}
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) {b : G}
    (hbK : b ∈ Subgroup.normalizer (K : Set G))
    (hbN : b ∈ Subgroup.normalizer (K ⊔ S : Subgroup G))
    (hb : ∀ y ∈ K, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 K)
    {x : G} (hx : x ∈ K ⊔ S) :
    ∀ y ∈ K, (b * x * b⁻¹ * x⁻¹) * y * (b * x * b⁻¹ * x⁻¹)⁻¹ * y⁻¹ ∈
      CFSG.Open.pCoreOf 2 (K ⊔ S) := by
  have hKS : K ⊔ S ≤ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer hSK
  have hKSR : K ⊔ S ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 (K ⊔ S) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ S)
  have hK_le_R : CFSG.Open.pCoreOf 2 K ≤ CFSG.Open.pCoreOf 2 (K ⊔ S) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (N := CFSG.Open.pCoreOf 2 K) 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left)
      ((sup_le Subgroup.le_normalizer hSK).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K)
  have hbR : b ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (K ⊔ S) : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (K ⊔ S) hbN
  intro y hy
  have hxK : x ∈ Subgroup.normalizer (K : Set G) := hKS hx
  have hk : x⁻¹ * y * x ∈ K := by
    simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hxK) y).mp hy
  have hbk : b⁻¹ * (x⁻¹ * y * x) * b ∈ K := by
    simpa using (Subgroup.mem_normalizer_iff.mp (inv_mem hbK) _).mp hk
  have hbinv : b⁻¹ * (x⁻¹ * y * x) * b * (x⁻¹ * y * x)⁻¹ ∈
      CFSG.Open.pCoreOf 2 (K ⊔ S) := by
    have h1 : b * (b⁻¹ * (x⁻¹ * y * x) * b) * b⁻¹ *
        (b⁻¹ * (x⁻¹ * y * x) * b)⁻¹ ∈ CFSG.Open.pCoreOf 2 (K ⊔ S) :=
      hK_le_R (hb _ hbk)
    have e : b * (b⁻¹ * (x⁻¹ * y * x) * b) * b⁻¹ * (b⁻¹ * (x⁻¹ * y * x) * b)⁻¹ =
        (b⁻¹ * (x⁻¹ * y * x) * b * (x⁻¹ * y * x)⁻¹)⁻¹ := by group
    rw [e] at h1
    simpa using inv_mem h1
  have hxconj : x * (b⁻¹ * (x⁻¹ * y * x) * b * (x⁻¹ * y * x)⁻¹) * x⁻¹ ∈
      CFSG.Open.pCoreOf 2 (K ⊔ S) :=
    (Subgroup.mem_normalizer_iff.mp (hKSR hx) _).mp hbinv
  have hbconj : b * (x * (b⁻¹ * (x⁻¹ * y * x) * b * (x⁻¹ * y * x)⁻¹) * x⁻¹) * b⁻¹ ∈
      CFSG.Open.pCoreOf 2 (K ⊔ S) :=
    (Subgroup.mem_normalizer_iff.mp hbR _).mp hxconj
  have hby : b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 (K ⊔ S) := hK_le_R (hb y hy)
  have e : (b * x * b⁻¹ * x⁻¹) * y * (b * x * b⁻¹ * x⁻¹)⁻¹ * y⁻¹ =
      b * (x * (b⁻¹ * (x⁻¹ * y * x) * b * (x⁻¹ * y * x)⁻¹) * x⁻¹) * b⁻¹ *
        (b * y * b⁻¹ * y⁻¹) := by group
  rw [e]
  exact mul_mem hbconj hby

theorem commutator_mem_pCoreOf_sup {K S : Subgroup G} (hS : IsPGroup 2 S)
    (hSK : S ≤ Subgroup.normalizer (K : Set G))
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) {b : G}
    (hbK : b ∈ Subgroup.normalizer (K : Set G)) (hbS : b ∈ Subgroup.normalizer (S : Set G))
    (hb : ∀ y ∈ K, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 K) {x : G} (hx : x ∈ K ⊔ S) :
    b * x * b⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 (K ⊔ S) := by
  have hbN : b ∈ Subgroup.normalizer (K ⊔ S : Subgroup G) :=
    mem_normalizer_sup_of_mem_normalizer hSK hbK hbS
  have hz : b * x * b⁻¹ * x⁻¹ ∈ K ⊔ S := by
    have h1 : b * x * b⁻¹ ∈ K ⊔ S := (Subgroup.mem_normalizer_iff.mp hbN x).mp hx
    exact mul_mem h1 (inv_mem hx)
  exact mem_pCoreOf_sup_of_commutator_mem hS hSK hZ hz
    (commutator_centralizes_mod_pCoreOf hSK hbK hbN hb hx)

theorem eq_one_of_mem_two_group_of_mem_elemAbelian_three {H K' : Subgroup G}
    (h2 : IsPGroup 2 H) (h3 : CFSG.Assembly.IsElemAbelian 3 K') {x : G}
    (hxH : x ∈ H) (hxK : x ∈ K') : x = 1 := by
  obtain ⟨m, hm⟩ := h2 ⟨x, hxH⟩
  have h2' : x ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have h3' : x ^ 3 = 1 := h3.2 x hxK
  have ho : orderOf x ∣ Nat.gcd (2 ^ m) 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2') (orderOf_dvd_of_pow_eq_one h3')
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left m (by decide : Nat.Coprime 2 3))] at ho
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp ho)

theorem a7Rep_eq_one_of_mem_pCoreOf_sup {K T : Subgroup G}
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7)) {x : G}
    (hx : x ∈ K ⊔ T) (hxN : x ∈ Subgroup.normalizer (K : Set G))
    (hxQ : x ∈ CFSG.Open.pCoreOf 2 (K ⊔ T)) :
    CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ ⟨x, hxN⟩ = 1 := by
  rw [CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep_eq_one_iff]
  intro y hy
  have hQN : K ⊔ T ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 (K ⊔ T) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ T)
  have hyN : y ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (K ⊔ T) : Set G) :=
    hQN (Subgroup.mem_sup_left hy)
  have h1 : y * x⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 (K ⊔ T) :=
    (Subgroup.mem_normalizer_iff.mp hyN x⁻¹).mp
      ((CFSG.Open.pCoreOf 2 (K ⊔ T)).inv_mem hxQ)
  have h2 : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
  rw [h2]
  have hmemK : x * (y * x⁻¹ * y⁻¹) ∈ K := by
    have h3 : x * (y * x⁻¹ * y⁻¹) = (x * y * x⁻¹) * y⁻¹ := by group
    rw [h3]
    exact K.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN y).mp hy) (K.inv_mem hy)
  exact CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 (le_sup_left : K ≤ K ⊔ T)
    ⟨hmemK, (CFSG.Open.pCoreOf 2 (K ⊔ T)).mul_mem hxQ h1⟩

theorem mem_pCoreOf_sup_of_a7Rep_eq_one {K T : Subgroup G} (hT : IsPGroup 2 T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥)
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7)) {x : G}
    (hx : x ∈ K ⊔ T) (hxN : x ∈ Subgroup.normalizer (K : Set G))
    (h1 : CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ ⟨x, hxN⟩ = 1) :
    x ∈ CFSG.Open.pCoreOf 2 (K ⊔ T) := by
  have hO : CFSG.Open.pCoreOf 2 K ≤ CFSG.Open.pCoreOf 2 (K ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans (le_sup_left : K ≤ K ⊔ T))
      ((sup_le Subgroup.le_normalizer hTK).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K)
  exact mem_pCoreOf_sup_of_commutator_mem hT hTK hZ hx fun y hy =>
    hO ((CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep_eq_one_iff K φ ⟨x, hxN⟩).mp h1 y hy)

theorem a7Rep_eq_one_iff_mem_pCoreOf_sup {K T : Subgroup G} (hT : IsPGroup 2 T)
    (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥)
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7)) {x : G}
    (hx : x ∈ K ⊔ T) (hxN : x ∈ Subgroup.normalizer (K : Set G)) :
    CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ ⟨x, hxN⟩ = 1 ↔
      x ∈ CFSG.Open.pCoreOf 2 (K ⊔ T) :=
  ⟨mem_pCoreOf_sup_of_a7Rep_eq_one hT hTK hZ φ hx hxN,
    a7Rep_eq_one_of_mem_pCoreOf_sup hTK φ hx hxN⟩

theorem a7Rep_eq_one_iff_mem_pCoreOf {K : Subgroup G}
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7)) {y : G} (hy : y ∈ K) :
    CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ
        ⟨y, Subgroup.le_normalizer hy⟩ = 1 ↔ y ∈ CFSG.Open.pCoreOf 2 K := by
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
    (CFSG.RankThree.PartTwo.KFacts.KS14.a7_facts _ ⟨φ⟩).2.1
  constructor
  · intro h1
    have hcomm : ∀ z ∈ K, y * z * y⁻¹ * z⁻¹ ∈ CFSG.Open.pCoreOf 2 K :=
      fun z hz =>
        (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep_eq_one_iff K φ
          ⟨y, Subgroup.le_normalizer hy⟩).mp h1 z hz
    have hcent : ((⟨y, hy⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) ∈
        Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) w
      rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
        QuotientGroup.eq_iff_div_mem]
      refine (CFSG.mem_openPCoreOf_iff (p := 2) (H := K)
        (u * ⟨y, hy⟩ / (⟨y, hy⟩ * u))).mp ?_
      have hgoal : ((u * ⟨y, hy⟩ / (⟨y, hy⟩ * u) : ↥K) : G) = u * y * u⁻¹ * y⁻¹ := by
        simp [div_eq_mul_inv, mul_assoc]
      rw [hgoal]
      simpa [mul_assoc] using inv_mem (hcomm u u.2)
    rw [hZ, Subgroup.mem_bot] at hcent
    have hmem : (⟨y, hy⟩ : ↥K) ∈ CFSG.pCore 2 ↥K := (QuotientGroup.eq_one_iff _).mp hcent
    exact (CFSG.mem_openPCoreOf_iff (p := 2) (H := K) ⟨y, hy⟩).mpr hmem
  · intro hyO
    rw [CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep_eq_one_iff]
    intro z hz
    have hzy : z * y * z⁻¹ ∈ CFSG.Open.pCoreOf 2 K :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K hz) y).mp hyO
    have e : y * z * y⁻¹ * z⁻¹ = y * (z * y * z⁻¹)⁻¹ := by group
    rw [e]
    exact (CFSG.Open.pCoreOf 2 K).mul_mem hyO ((CFSG.Open.pCoreOf 2 K).inv_mem hzy)

private theorem a7Rep_eq_one_of_mem_inf_elemAbelian {A K : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7)) {x : G}
    (hxAK : x ∈ A ⊓ K) (hxN : x ∈ Subgroup.normalizer (K : Set G))
    (h1 : CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ ⟨x, hxN⟩ = 1) : x = 1 := by
  have hxO : x ∈ CFSG.Open.pCoreOf 2 K :=
    (a7Rep_eq_one_iff_mem_pCoreOf φ (Subgroup.mem_inf.mp hxAK).2).mp h1
  exact eq_one_of_mem_two_group_of_mem_elemAbelian_three
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K) hA hxO
    (Subgroup.mem_inf.mp hxAK).1

theorem a7Rep_injective_inf {A K : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7)) :
    Function.Injective (fun d : ↥(A ⊓ K) =>
      CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ
        ⟨(d : G), Subgroup.le_normalizer (Subgroup.mem_inf.mp d.2).2⟩) := by
  intro x y hxy
  have hmem : ((x : G) * (y : G)⁻¹) ∈ A ⊓ K := by
    refine Subgroup.mem_inf.mpr ⟨A.mul_mem (Subgroup.mem_inf.mp x.2).1
      (A.inv_mem (Subgroup.mem_inf.mp y.2).1), ?_⟩
    exact K.mul_mem (Subgroup.mem_inf.mp x.2).2 (K.inv_mem (Subgroup.mem_inf.mp y.2).2)
  let N := Subgroup.normalizer (K : Set G)
  have hxy' : CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ
        ⟨(x : G), Subgroup.le_normalizer (Subgroup.mem_inf.mp x.2).2⟩ =
      CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ
        ⟨(y : G), Subgroup.le_normalizer (Subgroup.mem_inf.mp y.2).2⟩ := hxy
  have h1 : CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ
      ⟨(x : G) * (y : G)⁻¹, Subgroup.le_normalizer hmem.2⟩ = 1 := by
    have hx' : (⟨(x : G), Subgroup.le_normalizer (Subgroup.mem_inf.mp x.2).2⟩ : ↥N) *
        (⟨(y : G), Subgroup.le_normalizer (Subgroup.mem_inf.mp y.2).2⟩ : ↥N)⁻¹ =
        ⟨(x : G) * (y : G)⁻¹, Subgroup.le_normalizer hmem.2⟩ := Subtype.ext rfl
    rw [← hx', map_mul, map_inv, hxy', mul_inv_cancel]
  have h2 : (x : G) * (y : G)⁻¹ = 1 :=
    a7Rep_eq_one_of_mem_inf_elemAbelian hA φ hmem (Subgroup.le_normalizer hmem.2) h1
  exact Subtype.ext (mul_inv_eq_one.mp h2)

theorem card_map_a7Rep_inf {A K : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    (hA9 : Nat.card (A ⊓ K : Subgroup G) = 9) :
    Nat.card ((((A ⊓ K).subgroupOf (Subgroup.normalizer (K : Set G))).map
      (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ) : Subgroup (Equiv.Perm (Fin 7)))) = 9 := by
  classical
  let N := Subgroup.normalizer (K : Set G)
  let D : Subgroup ↥N := (A ⊓ K).subgroupOf N
  let ρ := CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ
  let F : ↥D → ↥(D.map ρ) :=
    fun x => ⟨ρ x.1, Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩⟩
  have hinj : Function.Injective F := by
    intro x y hxy
    have hxy' : ρ x.1 = ρ y.1 := congrArg Subtype.val hxy
    have hmem : ((x.1 * y.1⁻¹ : ↥N) : G) ∈ A ⊓ K :=
      Subgroup.mem_inf.mpr ⟨A.mul_mem (Subgroup.mem_inf.mp x.2).1
        (A.inv_mem (Subgroup.mem_inf.mp y.2).1),
        K.mul_mem (Subgroup.mem_inf.mp x.2).2 (K.inv_mem (Subgroup.mem_inf.mp y.2).2)⟩
    have h1 : ρ (x.1 * y.1⁻¹) = 1 := by
      rw [map_mul, map_inv, hxy', mul_inv_cancel]
    have h2 : x.1 * y.1⁻¹ = 1 := by
      apply Subtype.ext
      exact a7Rep_eq_one_of_mem_inf_elemAbelian hA φ hmem (x.1 * y.1⁻¹).2 h1
    have h3 : x.1 = y.1 := by
      calc x.1 = x.1 * y.1⁻¹ * y.1 := by group
        _ = y.1 := by rw [h2, one_mul]
    exact Subtype.ext h3
  have hsurj : Function.Surjective F := by
    rintro ⟨v, hv⟩
    obtain ⟨x, hx, hxv⟩ := Subgroup.mem_map.mp hv
    exact ⟨⟨x, hx⟩, Subtype.ext hxv⟩
  have hcard : Nat.card ↥D = Nat.card ↥(D.map ρ) :=
    Nat.card_congr (Equiv.ofBijective F ⟨hinj, hsurj⟩)
  have hD : Nat.card ↥D = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show A ⊓ K ≤ N from inf_le_right.trans Subgroup.le_normalizer)).toEquiv, hA9]
  rw [← hcard]
  exact hD

theorem exists_a7Rep_eq_of_mem_alternating {K : Subgroup G}
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    {v : Equiv.Perm (Fin 7)} (hv : v ∈ alternatingGroup (Fin 7)) :
    ∃ y : ↥K, CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ
      ⟨(y : G), Subgroup.le_normalizer y.2⟩ = v := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) (φ.symm ⟨v, hv⟩)
  refine ⟨x, ?_⟩
  rw [CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep_of_mem]
  have hx' : φ (x : ↥K ⧸ CFSG.pCore 2 ↥K) = ⟨v, hv⟩ := by
    have := congrArg φ hx
    simpa using this
  rw [hx']

private def pushUpPreimage (K T : Subgroup G)
    (hKTN : K ⊔ T ≤ Subgroup.normalizer (K : Set G))
    (ρ : ↥(Subgroup.normalizer (K : Set G)) →* Equiv.Perm (Fin 7))
    (V : Subgroup (Equiv.Perm (Fin 7))) : Subgroup G :=
  (V.comap (ρ.comp (Subgroup.inclusion hKTN))).map (K ⊔ T).subtype

private theorem mem_pushUpPreimage {K T : Subgroup G}
    {hKTN : K ⊔ T ≤ Subgroup.normalizer (K : Set G)}
    {ρ : ↥(Subgroup.normalizer (K : Set G)) →* Equiv.Perm (Fin 7)}
    {V : Subgroup (Equiv.Perm (Fin 7))} {x : G} (hx : x ∈ K ⊔ T) :
    x ∈ pushUpPreimage K T hKTN ρ V ↔
      (ρ.comp (Subgroup.inclusion hKTN)) ⟨x, hx⟩ ∈ V := by
  constructor
  · intro hxW
    obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp hxW
    rw [Subgroup.mem_comap] at hw
    have hw' : (⟨x, hx⟩ : ↥(K ⊔ T)) = w := Subtype.ext hwx.symm
    rwa [hw']
  · intro h
    exact Subgroup.mem_map.mpr ⟨⟨x, hx⟩, by rwa [Subgroup.mem_comap], rfl⟩

private theorem pushUpPreimage_le {K T : Subgroup G}
    {hKTN : K ⊔ T ≤ Subgroup.normalizer (K : Set G)}
    {ρ : ↥(Subgroup.normalizer (K : Set G)) →* Equiv.Perm (Fin 7)}
    (V : Subgroup (Equiv.Perm (Fin 7))) :
    pushUpPreimage K T hKTN ρ V ≤ K ⊔ T :=
  Subgroup.map_subtype_le _

private theorem le_pCoreOf_sup_of_map_a7Rep_eq_bot {A : Subgroup G} {K T : Subgroup G}
    (hT : T ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (K : Set G)) (piOf 2))
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥)
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    (hbot : (T.subgroupOf (Subgroup.normalizer (K : Set G))).map
      (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ) = ⊥) :
    T ≤ CFSG.Open.pCoreOf 2 (K ⊔ T) := by
  intro t ht
  have hmem : CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ ⟨t, hT.prop.1.2 ht⟩ ∈
      (T.subgroupOf (Subgroup.normalizer (K : Set G))).map
        (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ) :=
    Subgroup.mem_map.mpr ⟨⟨t, hT.prop.1.2 ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact (a7Rep_eq_one_iff_mem_pCoreOf_sup (isPGroup_of_mem_scriptQPi Nat.prime_two hT.prop)
    hT.prop.1.2 hZ φ (Subgroup.mem_sup_right ht) (hT.prop.1.2 ht)).mp hmem

private theorem isPGroup_pushUpPreimage {K T : Subgroup G}
    {hKTN : K ⊔ T ≤ Subgroup.normalizer (K : Set G)}
    {ρ : ↥(Subgroup.normalizer (K : Set G)) →* Equiv.Perm (Fin 7)}
    {V : Subgroup (Equiv.Perm (Fin 7))}
    (hker : ∀ (x : G) (hx : x ∈ K ⊔ T) (hxN : x ∈ Subgroup.normalizer (K : Set G)),
      ρ ⟨x, hxN⟩ = 1 ↔ x ∈ CFSG.Open.pCoreOf 2 (K ⊔ T))
    (hQ2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 (K ⊔ T)))
    (hQle : CFSG.Open.pCoreOf 2 (K ⊔ T) ≤ K ⊔ T)
    (hV2 : IsPGroup 2 V) :
    IsPGroup 2 (pushUpPreimage K T hKTN ρ V) := by
  let W := pushUpPreimage K T hKTN ρ V
  have hWle : W ≤ K ⊔ T := pushUpPreimage_le V
  let f : ↥W →* Equiv.Perm (Fin 7) :=
    (ρ.comp (Subgroup.inclusion hKTN)).comp (Subgroup.inclusion hWle)
  have hfker : f.ker ≤ ((CFSG.Open.pCoreOf 2 (K ⊔ T)).subgroupOf (K ⊔ T)).comap
      (Subgroup.inclusion hWle) := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hx1 : f x = 1 := hx
    have hx1' : ρ ⟨((x : ↥W) : G), hKTN (hWle x.2)⟩ = 1 := hx1
    exact (hker _ (hWle x.2) (hKTN (hWle x.2))).mp hx1'
  have hQsub2 : IsPGroup 2 ((CFSG.Open.pCoreOf 2 (K ⊔ T)).subgroupOf (K ⊔ T)) :=
    hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe hQle).symm
  have hfker2 : IsPGroup 2 f.ker :=
    (hQsub2.comap_of_injective (Subgroup.inclusion hWle)
      (Subgroup.inclusion_injective hWle)).to_le hfker
  have hrange : f.range ≤ V := by
    rintro _ ⟨x, rfl⟩
    exact (mem_pushUpPreimage (pushUpPreimage_le V x.2)).mp x.2
  have htop : V.comap f = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_comap]
    exact hrange ⟨x, rfl⟩
  have htop2 : IsPGroup 2 (⊤ : Subgroup ↥W) :=
    htop ▸ hV2.comap_of_ker_isPGroup f hfker2
  exact htop2.of_equiv Subgroup.topEquiv

private theorem pushUpPreimage_le_normalizer {K T : Subgroup G}
    {hKTN : K ⊔ T ≤ Subgroup.normalizer (K : Set G)}
    {ρ : ↥(Subgroup.normalizer (K : Set G)) →* Equiv.Perm (Fin 7)}
    (V : Subgroup (Equiv.Perm (Fin 7))) :
    pushUpPreimage K T hKTN ρ V ≤ Subgroup.normalizer (K : Set G) :=
  (pushUpPreimage_le V).trans hKTN

private theorem pushUpPreimage_le_normalizer_T {K T : Subgroup G}
    {hKTN : K ⊔ T ≤ Subgroup.normalizer (K : Set G)}
    {ρ : ↥(Subgroup.normalizer (K : Set G)) →* Equiv.Perm (Fin 7)}
    (V : Subgroup (Equiv.Perm (Fin 7))) (hTeq : T = CFSG.Open.pCoreOf 2 (K ⊔ T)) :
    pushUpPreimage K T hKTN ρ V ≤ Subgroup.normalizer (T : Set G) := by
  have h1 : K ⊔ T ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (K ⊔ T) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ T)
  rw [← hTeq] at h1
  exact (pushUpPreimage_le V).trans h1

private theorem a7Rep_mem_map_inf_of_mem_A {A : Subgroup G} {k : G} {Lk K : Subgroup G}
    (h : Sec14Std G A k Lk) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    (hk : ∀ y ∈ K, k * y * k⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 K)
    (hAk : (A ⊓ K) ⊔ Subgroup.zpowers k = A) {a : G} (ha : a ∈ A) :
    CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ ⟨a, hAK ha⟩ ∈
      ((A ⊓ K).subgroupOf (Subgroup.normalizer (K : Set G))).map
        (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ) := by
  set N := Subgroup.normalizer (K : Set G)
  set ρ := CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ
  have hkA : k ∈ A := (zpowers_mem_omegaA_iff.mp h.toSec13Data.zpowers_mem_omegaA).1
  have hzk : Subgroup.zpowers k ≤ Subgroup.normalizer ((A ⊓ K : Subgroup G) : Set G) := by
    refine Subgroup.zpowers_le.mpr ?_
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have hxAK : x ∈ A ⊓ K := hx
    have hcomm : k * x = x * k := congrArg Subtype.val
      (h.chosen136.1.1.1.is_comm.comm ⟨k, hkA⟩ ⟨x, (Subgroup.mem_inf.mp hxAK).1⟩)
    have h1 : k * x * k⁻¹ = x := by rw [hcomm]; group
    rw [h1]
    exact hxAK
  have hdec : ∀ a ∈ A, ∃ m ∈ (A ⊓ K : Subgroup G), ∃ z ∈ Subgroup.zpowers k, m * z = a := by
    intro a ha
    have hmem : a ∈ ((A ⊓ K : Subgroup G) : Set G) *
        ((Subgroup.zpowers k : Subgroup G) : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left (A ⊓ K) (Subgroup.zpowers k) hzk,
        hAk]
      exact ha
    exact hmem
  have hkρ : ρ ⟨k, hAK hkA⟩ = 1 :=
    (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep_eq_one_iff K φ ⟨k, hAK hkA⟩).mpr hk
  obtain ⟨m, hm, z, hz, hmz⟩ := hdec a ha
  have hzA : z ∈ A := Subgroup.zpowers_le.mpr hkA hz
  have hzN : z ∈ N := hAK hzA
  have hmN : m ∈ N := hAK (Subgroup.mem_inf.mp hm).1
  have hρz : ρ ⟨z, hzN⟩ = 1 := by
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [show (⟨k ^ j, hzN⟩ : ↥N) = ⟨k, hAK hkA⟩ ^ j from Subtype.ext (by simp)]
    rw [map_zpow, hkρ, one_zpow]
  have hρa : ρ ⟨a, hAK ha⟩ = ρ ⟨m, hmN⟩ := by
    have hsub : (⟨a, hAK ha⟩ : ↥N) = ⟨m, hmN⟩ * ⟨z, hzN⟩ := Subtype.ext hmz.symm
    rw [hsub, map_mul, hρz, mul_one]
  rw [hρa]
  exact Subgroup.mem_map.mpr ⟨⟨m, hmN⟩, Subgroup.mem_subgroupOf.mpr hm, rfl⟩

private theorem le_normalizer_pushUpPreimage {A : Subgroup G} {k : G} {Lk K T : Subgroup G}
    (h : Sec14Std G A k Lk) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    (hk : ∀ y ∈ K, k * y * k⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 K)
    (hAk : (A ⊓ K) ⊔ Subgroup.zpowers k = A)
    {hKTN : K ⊔ T ≤ Subgroup.normalizer (K : Set G)}
    {V : Subgroup (Equiv.Perm (Fin 7))}
    (hA_NKT : A ≤ Subgroup.normalizer (K ⊔ T : Subgroup G))
    (hE : ((A ⊓ K).subgroupOf (Subgroup.normalizer (K : Set G))).map
      (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ) ≤
      Subgroup.normalizer (V : Set (Equiv.Perm (Fin 7)))) :
    A ≤ Subgroup.normalizer (pushUpPreimage K T hKTN
      (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ) V : Set G) := by
  intro a ha
  refine Subgroup.mem_normalizer_fintype fun w hw => ?_
  have hwKT : (w : G) ∈ K ⊔ T :=
    pushUpPreimage_le V hw
  have hconjKT : a * (w : G) * a⁻¹ ∈ K ⊔ T :=
    (Subgroup.mem_normalizer_iff.mp (hA_NKT ha) w).mp hwKT
  have h1 : ((CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ).comp
      (Subgroup.inclusion hKTN)) ⟨a * (w : G) * a⁻¹, hconjKT⟩ =
      CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ ⟨a, hAK ha⟩ *
        ((CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ).comp (Subgroup.inclusion hKTN))
          ⟨w, hwKT⟩ *
        (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ ⟨a, hAK ha⟩)⁻¹ := by
    have hsub : (⟨a * (w : G) * a⁻¹, hKTN hconjKT⟩ :
        ↥(Subgroup.normalizer (K : Set G))) =
        ⟨a, hAK ha⟩ * ⟨w, hKTN hwKT⟩ * ⟨a, hAK ha⟩⁻¹ :=
      Subtype.ext (by simp [mul_assoc])
    change CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ ⟨a * (w : G) * a⁻¹, hKTN hconjKT⟩ =
      CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ ⟨a, hAK ha⟩ *
        CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ ⟨w, hKTN hwKT⟩ *
        (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ ⟨a, hAK ha⟩)⁻¹
    rw [hsub, map_mul, map_mul, map_inv]
  change a * (w : G) * a⁻¹ ∈ pushUpPreimage K T hKTN
    (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ) V
  rw [mem_pushUpPreimage hconjKT, h1]
  exact (Subgroup.mem_normalizer_iff.mp
    (hE (a7Rep_mem_map_inf_of_mem_A h hAK φ hk hAk ha))
    (((CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ).comp (Subgroup.inclusion hKTN))
      ⟨w, hwKT⟩)).mp ((mem_pushUpPreimage hwKT).mp hw)

private theorem commutator_k_mem_pushUpPreimage {A : Subgroup G} {k : G} {K T : Subgroup G}
    (hT : T ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (K : Set G)) (piOf 2))
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥)
    (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hAT : A ≤ Subgroup.normalizer (T : Set G))
    (hk : ∀ y ∈ K, k * y * k⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 K)
    (hkA : k ∈ A) (hTeq : T = CFSG.Open.pCoreOf 2 (K ⊔ T))
    {hKTN : K ⊔ T ≤ Subgroup.normalizer (K : Set G)}
    {ρ : ↥(Subgroup.normalizer (K : Set G)) →* Equiv.Perm (Fin 7)}
    {V : Subgroup (Equiv.Perm (Fin 7))} :
    ∀ w ∈ pushUpPreimage K T hKTN ρ V, k * w * k⁻¹ * w⁻¹ ∈ T := by
  intro w hw
  rw [hTeq]
  exact commutator_mem_pCoreOf_sup (isPGroup_of_mem_scriptQPi Nat.prime_two hT.prop)
    hT.prop.1.2 hZ (hAK hkA) (hAT hkA) hk (pushUpPreimage_le V hw)

private theorem eq_bot_of_map_a7Rep_eq_bot {A : Subgroup G} {K T : Subgroup G}
    {hKTN : K ⊔ T ≤ Subgroup.normalizer (K : Set G)}
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    (hT : T ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (K : Set G)) (piOf 2))
    (hbot : (T.subgroupOf (Subgroup.normalizer (K : Set G))).map
      (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ) = ⊥)
    {V : Subgroup (Equiv.Perm (Fin 7))} (hV : V ≤ alternatingGroup (Fin 7))
    (hW : pushUpPreimage K T hKTN (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ) V = T) :
    V = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  have hvA : v ∈ alternatingGroup (Fin 7) := hV hv
  obtain ⟨y, hy⟩ := exists_a7Rep_eq_of_mem_alternating φ hvA
  have hyW : (y : G) ∈ pushUpPreimage K T hKTN
      (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ) V := by
    rw [mem_pushUpPreimage (Subgroup.mem_sup_left y.2)]
    have h1 : ((CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ).comp
        (Subgroup.inclusion hKTN)) ⟨(y : G), Subgroup.mem_sup_left y.2⟩ = v := hy
    rw [h1]
    exact hv
  have hyT : (y : G) ∈ T := by
    rw [← hW]
    exact hyW
  have hmem : CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ ⟨(y : G), hT.prop.1.2 hyT⟩ ∈
      (T.subgroupOf (Subgroup.normalizer (K : Set G))).map
        (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ) :=
    Subgroup.mem_map.mpr ⟨⟨(y : G), hT.prop.1.2 hyT⟩, Subgroup.mem_subgroupOf.mpr hyT, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  rw [← hy]
  exact hmem

private theorem pushUpPreimage_eq_T_of_map_a7Rep_eq_bot {A : Subgroup G} {k : G}
    {Lk K T : Subgroup G}
    (h : Sec14Std G A k Lk) (h146 : Item146 A (lB A)) (h142 : Concl142 A (lB A))
    (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hT : T ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (K : Set G)) (piOf 2))
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    (hk : ∀ y ∈ K, k * y * k⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 K)
    (hKT : CFSG.Open.pCoreOf 2 K ≤ T)
    (hAk : (A ⊓ K) ⊔ Subgroup.zpowers k = A)
    (hbot : (T.subgroupOf (Subgroup.normalizer (K : Set G))).map
      (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ) = ⊥)
    {g : Equiv.Perm (Fin 7)}
    (hE : ((A ⊓ K).subgroupOf (Subgroup.normalizer (K : Set G))).map
      (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ) ≤
      Subgroup.normalizer ((CFSG.RankThree.PartTwo.KFacts.KP2.vTwo.map
        (MulAut.conj g).toMonoidHom : Subgroup (Equiv.Perm (Fin 7))) :
          Set (Equiv.Perm (Fin 7)))) :
    pushUpPreimage K T (sup_le Subgroup.le_normalizer hT.prop.1.2)
      (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ)
      (CFSG.RankThree.PartTwo.KFacts.KP2.vTwo.map (MulAut.conj g).toMonoidHom) = T := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ
  set V : Subgroup (Equiv.Perm (Fin 7)) :=
    CFSG.RankThree.PartTwo.KFacts.KP2.vTwo.map (MulAut.conj g).toMonoidHom
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hT.prop.1.2
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := (mem_scriptQ_iff.mp hT.prop.1.1).2.1
  have hKTN : K ⊔ T ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hTK
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
    (CFSG.RankThree.PartTwo.KFacts.KS14.a7_facts _ ⟨φ⟩).2.1
  have hQ2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 (K ⊔ T)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (K ⊔ T)
  have hQle : CFSG.Open.pCoreOf 2 (K ⊔ T) ≤ K ⊔ T :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 (K ⊔ T)
  have hTleQ : T ≤ CFSG.Open.pCoreOf 2 (K ⊔ T) :=
    le_pCoreOf_sup_of_map_a7Rep_eq_bot hT hZ φ hbot
  have hTeqQ : T = CFSG.Open.pCoreOf 2 (K ⊔ T) := le_antisymm hTleQ
    (pCoreOf_sup_le_of_centralizes h h146 h142 hAK hT hk hKT)
  have hkA : k ∈ A := (zpowers_mem_omegaA_iff.mp h.toSec13Data.zpowers_mem_omegaA).1
  have hV2 : IsPGroup 2 V := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [CFSG.RankThree.PartTwo.KFacts.KP2.card_map_vTwo g]
    norm_num
  have hW2 : IsPGroup 2 (pushUpPreimage K T hKTN ρ V) :=
    isPGroup_pushUpPreimage
      (fun x hx hxN => a7Rep_eq_one_iff_mem_pCoreOf_sup
        (isPGroup_of_mem_scriptQPi Nat.prime_two hT.prop) hTK hZ φ hx hxN)
      hQ2 hQle hV2
  have hTW : T ≤ pushUpPreimage K T hKTN ρ V := by
    intro t ht
    rw [mem_pushUpPreimage (Subgroup.mem_sup_right ht)]
    have h1 : (ρ.comp (Subgroup.inclusion hKTN)) ⟨t, Subgroup.mem_sup_right ht⟩ = 1 := by
      have hmem : ρ ⟨t, hTK ht⟩ ∈ (T.subgroupOf (Subgroup.normalizer (K : Set G))).map ρ :=
        Subgroup.mem_map.mpr ⟨⟨t, hTK ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at hmem
    rw [h1]
    exact V.one_mem
  have hWK : pushUpPreimage K T hKTN ρ V ≤ Subgroup.normalizer (K : Set G) :=
    pushUpPreimage_le_normalizer V
  have hWT : pushUpPreimage K T hKTN ρ V ≤ Subgroup.normalizer (T : Set G) :=
    pushUpPreimage_le_normalizer_T V hTeqQ
  have hA_NKT : A ≤ Subgroup.normalizer (K ⊔ T : Subgroup G) :=
    (le_inf hAK hAT).trans (Subgroup.inf_normalizer_le_normalizer_sup K T)
  have hAW : A ≤ Subgroup.normalizer (pushUpPreimage K T hKTN ρ V : Set G) :=
    le_normalizer_pushUpPreimage h hAK φ hk hAk hA_NKT hE
  have hkW : ∀ w ∈ pushUpPreimage K T hKTN ρ V, k * w * k⁻¹ * w⁻¹ ∈ T :=
    commutator_k_mem_pushUpPreimage hT hZ hAK hAT hk hkA hTeqQ
  exact eq_of_commutator_mem h h146 h142 hT hW2 hTW hWK hWT hAW hkW

private theorem exists_pushUpPreimage_eq_of_map_a7Rep_eq_bot {A : Subgroup G} {k : G}
    {Lk K T : Subgroup G}
    (h : Sec14Std G A k Lk) (h146 : Item146 A (lB A)) (h142 : Concl142 A (lB A))
    (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hT : T ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (K : Set G)) (piOf 2))
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    (hk : ∀ y ∈ K, k * y * k⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 K)
    (hKT : CFSG.Open.pCoreOf 2 K ≤ T) (hA9 : Nat.card (A ⊓ K : Subgroup G) = 9)
    (hAk : (A ⊓ K) ⊔ Subgroup.zpowers k = A)
    (hbot : (T.subgroupOf (Subgroup.normalizer (K : Set G))).map
      (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ) = ⊥) :
    ∃ g : Equiv.Perm (Fin 7),
      pushUpPreimage K T (sup_le Subgroup.le_normalizer hT.prop.1.2)
        (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ)
        (CFSG.RankThree.PartTwo.KFacts.KP2.vTwo.map (MulAut.conj g).toMonoidHom) = T := by
  have hEcard : Nat.card (((A ⊓ K).subgroupOf (Subgroup.normalizer (K : Set G))).map
      (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ)) = 9 :=
    card_map_a7Rep_inf h.chosen136.1.1 φ hA9
  obtain ⟨g, hgN⟩ := CFSG.RankThree.PartTwo.KFacts.KP2.exists_le_normalizer_map_vTwo
    (P := ((A ⊓ K).subgroupOf (Subgroup.normalizer (K : Set G))).map
      (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ)) hEcard
  exact ⟨g, pushUpPreimage_eq_T_of_map_a7Rep_eq_bot h h146 h142 hAK hT φ hk hKT hAk hbot hgN⟩

private theorem map_subgroupOf_a7Rep_ne_bot {A : Subgroup G} {k : G} {Lk K T : Subgroup G}
    (h : Sec14Std G A k Lk) (h146 : Item146 A (lB A)) (h142 : Concl142 A (lB A))
    (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hT : T ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (K : Set G)) (piOf 2))
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    (hk : ∀ y ∈ K, k * y * k⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 K)
    (hKT : CFSG.Open.pCoreOf 2 K ≤ T) (hA9 : Nat.card (A ⊓ K : Subgroup G) = 9)
    (hAk : (A ⊓ K) ⊔ Subgroup.zpowers k = A) :
    (T.subgroupOf (Subgroup.normalizer (K : Set G))).map
      (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ) ≠ ⊥ := by
  classical
  intro hbot
  obtain ⟨g, hW⟩ := exists_pushUpPreimage_eq_of_map_a7Rep_eq_bot h h146 h142 hAK hT φ hk hKT
    hA9 hAk hbot
  have hVbot : CFSG.RankThree.PartTwo.KFacts.KP2.vTwo.map (MulAut.conj g).toMonoidHom = ⊥ :=
    eq_bot_of_map_a7Rep_eq_bot φ hT hbot
      (CFSG.RankThree.PartTwo.KFacts.KP2.map_vTwo_le_alternatingGroup g) hW
  have hcardV : Nat.card (CFSG.RankThree.PartTwo.KFacts.KP2.vTwo.map
      (MulAut.conj g).toMonoidHom) = 4 :=
    CFSG.RankThree.PartTwo.KFacts.KP2.card_map_vTwo g
  rw [hVbot, Subgroup.card_bot] at hcardV
  norm_num at hcardV

theorem exists_map_eq_map_vTwo_of_a7 {A : Subgroup G} {k : G} {Lk K T : Subgroup G}
    (h : Sec14Std G A k Lk) (h146 : Item146 A (lB A)) (h142 : Concl142 A (lB A))
    (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hT : T ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (K : Set G)) (piOf 2))
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    (hk : ∀ y ∈ K, k * y * k⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 K)
    (hKT : CFSG.Open.pCoreOf 2 K ≤ T) (hA9 : Nat.card (A ⊓ K : Subgroup G) = 9)
    (hAk : (A ⊓ K) ⊔ Subgroup.zpowers k = A) :
    ∃ g : Equiv.Perm (Fin 7), (T.subgroupOf (Subgroup.normalizer (K : Set G))).map
      (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ) =
        CFSG.RankThree.PartTwo.KFacts.KP2.vTwo.map (MulAut.conj g).toMonoidHom := by
  have hA3 : CFSG.Assembly.IsElemAbelian 3 A := h.chosen136.1.1
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hT.prop.1.2
  have hT2 : IsPGroup 2 T := isPGroup_of_mem_scriptQPi Nat.prime_two hT.prop
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := (mem_scriptQ_iff.mp hT.prop.1.1).2.1
  have hEcard : Nat.card (((A ⊓ K).subgroupOf (Subgroup.normalizer (K : Set G))).map
      (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ)) = 9 :=
    card_map_a7Rep_inf hA3 φ hA9
  set T' : Subgroup (Equiv.Perm (Fin 7)) :=
    (T.subgroupOf (Subgroup.normalizer (K : Set G))).map
      (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ)
  have hT'2 : IsPGroup 2 T' := by
    have h : IsPGroup 2 (T.subgroupOf (Subgroup.normalizer (K : Set G))) :=
      hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTK).symm
    exact h.map (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ)
  have hENT' : ((A ⊓ K).subgroupOf (Subgroup.normalizer (K : Set G))).map
      (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ) ≤
      Subgroup.normalizer (T' : Set (Equiv.Perm (Fin 7))) := by
    rintro _ ⟨d, hd, rfl⟩
    refine Subgroup.mem_normalizer_fintype fun t ht => ?_
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp ht
    have hdA : ((d : ↥(Subgroup.normalizer (K : Set G))) : G) ∈ A :=
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hd)).1
    have hsT : ((s : ↥(Subgroup.normalizer (K : Set G))) : G) ∈ T :=
      Subgroup.mem_subgroupOf.mp hs
    have hconjT : ((d : ↥(Subgroup.normalizer (K : Set G))) : G) *
        ((s : ↥(Subgroup.normalizer (K : Set G))) : G) *
        ((d : ↥(Subgroup.normalizer (K : Set G))) : G)⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp (hAT hdA) _).mp hsT
    refine Subgroup.mem_map.mpr ⟨⟨_, hTK hconjT⟩, Subgroup.mem_subgroupOf.mpr hconjT, ?_⟩
    rw [show (⟨_, hTK hconjT⟩ : ↥(Subgroup.normalizer (K : Set G))) = d * s * d⁻¹
      from Subtype.ext rfl, map_mul, map_mul, map_inv]
  rcases CFSG.RankThree.PartTwo.KFacts.KP2.eq_bot_or_eq_map_vTwo
    (P := ((A ⊓ K).subgroupOf (Subgroup.normalizer (K : Set G))).map
      (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ)) hEcard hT'2 hENT' with hbot | ⟨g, hg⟩
  · exact absurd hbot (map_subgroupOf_a7Rep_ne_bot h h146 h142 hAK hT φ hk hKT hA9 hAk)
  · exact ⟨g, hg⟩

theorem sup_eq_sup_pCoreOf_of_a7 {A : Subgroup G} {k : G} {Lk K T : Subgroup G}
    (h : Sec14Std G A k Lk) (h146 : Item146 A (lB A)) (h142 : Concl142 A (lB A))
    (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hT : T ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (K : Set G)) (piOf 2))
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    (hk : ∀ y ∈ K, k * y * k⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 K)
    (hKT : CFSG.Open.pCoreOf 2 K ≤ T) (hA9 : Nat.card (A ⊓ K : Subgroup G) = 9)
    (hAk : (A ⊓ K) ⊔ Subgroup.zpowers k = A) :
    K ⊔ T = K ⊔ CFSG.Open.pCoreOf 2 (K ⊔ T) := by
  obtain ⟨g, hg⟩ := exists_map_eq_map_vTwo_of_a7 h h146 h142 hAK hT φ hk hKT hA9 hAk
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hT.prop.1.2
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
    (CFSG.RankThree.PartTwo.KFacts.KS14.a7_facts _ ⟨φ⟩).2.1
  have hQleT : CFSG.Open.pCoreOf 2 (K ⊔ T) ≤ T :=
    pCoreOf_sup_le_of_centralizes h h146 h142 hAK hT hk hKT
  refine le_antisymm ?_ (sup_le_sup le_rfl hQleT)
  refine sup_le le_sup_left ?_
  intro t ht
  have htV : CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ ⟨t, hTK ht⟩ ∈
      CFSG.RankThree.PartTwo.KFacts.KP2.vTwo.map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact Subgroup.mem_map.mpr ⟨⟨t, hTK ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  have htA : CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ ⟨t, hTK ht⟩ ∈
      alternatingGroup (Fin 7) :=
    CFSG.RankThree.PartTwo.KFacts.KP2.map_vTwo_le_alternatingGroup g htV
  obtain ⟨y, hy⟩ := exists_a7Rep_eq_of_mem_alternating φ htA
  have hyN : (y : G) ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer y.2
  have htN : t ∈ Subgroup.normalizer (K : Set G) := hTK ht
  have hmemKT : (y : G)⁻¹ * t ∈ K ⊔ T :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left (K.inv_mem y.2)) (Subgroup.mem_sup_right ht)
  have hmemN : (y : G)⁻¹ * t ∈ Subgroup.normalizer (K : Set G) :=
    (sup_le Subgroup.le_normalizer hTK) hmemKT
  have h1 : CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ ⟨(y : G)⁻¹ * t, hmemN⟩ = 1 := by
    rw [show (⟨(y : G)⁻¹ * t, hmemN⟩ : ↥(Subgroup.normalizer (K : Set G))) =
        ⟨(y : G), hyN⟩⁻¹ * ⟨t, htN⟩ from Subtype.ext rfl, map_mul, map_inv]
    rw [show (⟨(y : G), hyN⟩ : ↥(Subgroup.normalizer (K : Set G))) = ⟨(y : G),
      Subgroup.le_normalizer y.2⟩ from Subtype.ext rfl, hy, inv_mul_cancel]
  have hQ : (y : G)⁻¹ * t ∈ CFSG.Open.pCoreOf 2 (K ⊔ T) :=
    (a7Rep_eq_one_iff_mem_pCoreOf_sup (isPGroup_of_mem_scriptQPi Nat.prime_two hT.prop) hTK hZ φ
      hmemKT hmemN).mp h1
  have ht' : t ∈ K ⊔ CFSG.Open.pCoreOf 2 (K ⊔ T) := by
    have h2 : (y : G) * ((y : G)⁻¹ * t) = t := by group
    rw [← h2]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left y.2) (Subgroup.mem_sup_right hQ)
  exact ht'

theorem card_eq_four_mul_of_a7 {A : Subgroup G} {k : G} {Lk K T : Subgroup G}
    (h : Sec14Std G A k Lk) (h146 : Item146 A (lB A)) (h142 : Concl142 A (lB A))
    (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hT : T ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (K : Set G)) (piOf 2))
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    (hk : ∀ y ∈ K, k * y * k⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 K)
    (hKT : CFSG.Open.pCoreOf 2 K ≤ T) (hA9 : Nat.card (A ⊓ K : Subgroup G) = 9)
    (hAk : (A ⊓ K) ⊔ Subgroup.zpowers k = A) :
    Nat.card T = 4 * Nat.card (CFSG.Open.pCoreOf 2 (K ⊔ T)) := by
  obtain ⟨g, hg⟩ := exists_map_eq_map_vTwo_of_a7 h h146 h142 hAK hT φ hk hKT hA9 hAk
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hT.prop.1.2
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ :=
    (CFSG.RankThree.PartTwo.KFacts.KS14.a7_facts _ ⟨φ⟩).2.1
  have hQleT : CFSG.Open.pCoreOf 2 (K ⊔ T) ≤ T :=
    pCoreOf_sup_le_of_centralizes h h146 h142 hAK hT hk hKT
  let f : ↥T →* Equiv.Perm (Fin 7) :=
    (CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ).comp (Subgroup.inclusion hTK)
  have hfker : f.ker = (CFSG.Open.pCoreOf 2 (K ⊔ T)).subgroupOf T := by
    ext t
    change CFSG.RankThree.PartTwo.KFacts.KP2.a7Rep K φ ⟨(t : G), hTK t.2⟩ = 1 ↔
      (t : G) ∈ CFSG.Open.pCoreOf 2 (K ⊔ T)
    exact a7Rep_eq_one_iff_mem_pCoreOf_sup (isPGroup_of_mem_scriptQPi Nat.prime_two hT.prop) hTK
      hZ φ (Subgroup.mem_sup_right t.2) (hTK t.2)
  have hcardker : Nat.card f.ker = Nat.card (CFSG.Open.pCoreOf 2 (K ⊔ T)) := by
    rw [hfker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQleT).toEquiv
  have hfrange : f.range = CFSG.RankThree.PartTwo.KFacts.KP2.vTwo.map
      (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    apply le_antisymm
    · rintro _ ⟨t, rfl⟩
      exact Subgroup.mem_map.mpr ⟨⟨t, hTK t.2⟩, Subgroup.mem_subgroupOf.mpr t.2, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have h1 := Subgroup.card_ker_mul_card_range f
  rw [hcardker, hfrange, CFSG.RankThree.PartTwo.KFacts.KP2.card_map_vTwo g] at h1
  rw [← h1]
  exact Nat.mul_comm _ _

private def quotientMap (K T : Subgroup G) :
    ↥K →* ↥(K ⊔ T) ⧸ CFSG.pCore 2 ↥(K ⊔ T) :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥(K ⊔ T))).comp
    (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ T))

private theorem inf_pCoreOf_eq_of_a7 {K T : Subgroup G}
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) :
    K ⊓ CFSG.Open.pCoreOf 2 (K ⊔ T) = CFSG.Open.pCoreOf 2 K := by
  refine le_antisymm (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 le_sup_left) ?_
  exact le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans (le_sup_left : K ≤ K ⊔ T))
      ((sup_le Subgroup.le_normalizer hTK).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) K))

private theorem ker_quotientMap {K T : Subgroup G}
    (hKQ : K ⊓ CFSG.Open.pCoreOf 2 (K ⊔ T) = CFSG.Open.pCoreOf 2 K) :
    (quotientMap K T).ker = CFSG.pCore 2 ↥K := by
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    have hxQ : (x : G) ∈ CFSG.Open.pCoreOf 2 (K ⊔ T) :=
      (CFSG.mem_openPCoreOf_iff (p := 2) (H := K ⊔ T)
        (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ T) x)).mpr
        ((QuotientGroup.eq_one_iff _).mp hx)
    have hxKQ : (x : G) ∈ K ⊓ CFSG.Open.pCoreOf 2 (K ⊔ T) := ⟨x.2, hxQ⟩
    rw [hKQ] at hxKQ
    exact (CFSG.mem_openPCoreOf_iff (p := 2) (H := K) x).mp hxKQ
  · intro hx
    have hxQ : (x : G) ∈ CFSG.Open.pCoreOf 2 (K ⊔ T) := by
      have hxKQ : (x : G) ∈ K ⊓ CFSG.Open.pCoreOf 2 (K ⊔ T) := by
        rw [hKQ]
        exact (CFSG.mem_openPCoreOf_iff (p := 2) (H := K) x).mpr hx
      exact (Subgroup.mem_inf.mp hxKQ).2
    refine (QuotientGroup.eq_one_iff _).mpr ?_
    exact (CFSG.mem_openPCoreOf_iff (p := 2) (H := K ⊔ T)
      (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ T) x)).mp (by simpa using hxQ)

private theorem surjective_quotientMap {K T : Subgroup G}
    (hTeq : K ⊔ T = K ⊔ CFSG.Open.pCoreOf 2 (K ⊔ T))
    (hKNQ : K ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (K ⊔ T) : Set G)) :
    Function.Surjective (quotientMap K T) := by
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(K ⊔ T)) q
  have hy : (y : G) ∈ (((K : Subgroup G) ⊔ CFSG.Open.pCoreOf 2 (K ⊔ T) : Subgroup G) :
      Set G) := by
    rw [← hTeq]
    exact y.2
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K _ hKNQ] at hy
  obtain ⟨d, hd, o, ho, hdo⟩ := hy
  obtain ⟨o', ho', rfl⟩ := Subgroup.mem_map.mp ho
  have hy' : y = Subgroup.inclusion (le_sup_left : K ≤ K ⊔ T) ⟨d, hd⟩ * o' :=
    Subtype.ext hdo.symm
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥(K ⊔ T)) o' = 1 :=
    (QuotientGroup.eq_one_iff o').mpr ho'
  have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥(K ⊔ T)) y = (quotientMap K T) ⟨d, hd⟩ := by
    rw [hy', map_mul, h1, mul_one]
    rfl
  exact ⟨⟨d, hd⟩, h2.symm⟩

theorem nonempty_quotient_equiv_of_a7 {A : Subgroup G} {k : G} {Lk K T : Subgroup G}
    (h : Sec14Std G A k Lk) (h146 : Item146 A (lB A)) (h142 : Concl142 A (lB A))
    (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hT : T ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (K : Set G)) (piOf 2))
    (φ : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7))
    (hk : ∀ y ∈ K, k * y * k⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 K)
    (hKT : CFSG.Open.pCoreOf 2 K ≤ T) (hA9 : Nat.card (A ⊓ K : Subgroup G) = 9)
    (hAk : (A ⊓ K) ⊔ Subgroup.zpowers k = A) :
    Nonempty (↥(K ⊔ T) ⧸ CFSG.pCore 2 ↥(K ⊔ T) ≃* alternatingGroup (Fin 7)) := by
  have hTeq : K ⊔ T = K ⊔ CFSG.Open.pCoreOf 2 (K ⊔ T) :=
    sup_eq_sup_pCoreOf_of_a7 h h146 h142 hAK hT φ hk hKT hA9 hAk
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hT.prop.1.2
  have hKNQ : K ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 (K ⊔ T) : Set G) :=
    le_sup_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K ⊔ T))
  have hFker : (quotientMap K T).ker = CFSG.pCore 2 ↥K :=
    ker_quotientMap (inf_pCoreOf_eq_of_a7 hTK)
  have hFsurj : Function.Surjective (quotientMap K T) :=
    surjective_quotientMap hTeq hKNQ
  have e : ↥K ⧸ (quotientMap K T).ker ≃* ↥(K ⊔ T) ⧸ CFSG.pCore 2 ↥(K ⊔ T) :=
    QuotientGroup.quotientKerEquivOfSurjective (quotientMap K T) hFsurj
  have eKer : ↥K ⧸ CFSG.pCore 2 ↥K ≃* ↥K ⧸ (quotientMap K T).ker :=
    QuotientGroup.quotientMulEquivOfEq hFker.symm
  exact ⟨((eKer.trans e).symm).trans φ⟩

end CFSG.RankThree.PartTwo.Sec16
