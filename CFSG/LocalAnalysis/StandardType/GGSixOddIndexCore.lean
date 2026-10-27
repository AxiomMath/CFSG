module

public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CoprimeAxB
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.GroupTheory.PCore.Defs
import CFSG.GroupTheory.PCore.Transport

public section

namespace CFSG.StandardType

open CFSG.Assembly

variable {G : Type*} [Group G]

theorem ggSix_pCore_eq (p : ℕ) (X : Type*) [Group X] :
    CFSG.Assembly.pCore p X = CFSG.pCore p X :=
  CFSG.RankThreeCoreUniqueness.Helpers.pCore_eq_sSup (G := X) p

theorem ggSix_pCoreOf_isPGroup (p : ℕ) (H : Subgroup G) : IsPGroup p (pCoreOf p H) := by
  unfold pCoreOf
  exact CFSG.pCore_isPGroup.map _

theorem ggSix_pCoreOf_le (p : ℕ) (H : Subgroup G) : pCoreOf p H ≤ H := CFSG.openPCoreOf_le p H

theorem ggSix_le_normalizer_pCoreOf (p : ℕ) (H : Subgroup G) :
    H ≤ Subgroup.normalizer (pCoreOf p H : Set G) := by
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (ggSix_pCoreOf_le p H)).mp ?_
  unfold pCoreOf Subgroup.subgroupOf
  rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  exact CFSG.pCore_normal

theorem ggSix_eq_one_of_mem_of_odd {P : Subgroup G} (hP : IsPGroup 2 P) {a : G} (ha : a ∈ P)
    (hodd : Odd (orderOf a)) : a = 1 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP ⟨a, ha⟩
  rw [Subgroup.orderOf_mk] at hk
  rw [hk] at hodd
  have hk0 : k = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  rw [hk0, pow_zero] at hk
  exact orderOf_eq_one_iff.mp hk

theorem ggSix_centralizer_le_normalizer_zpowers (t : G) :
    Subgroup.centralizer {t} ≤ Subgroup.normalizer (Subgroup.zpowers t : Set G) := by
  intro n hn
  rw [Subgroup.mem_centralizer_singleton_iff] at hn
  have hconj : n * t * n⁻¹ = t := by rw [hn, mul_inv_cancel_right]
  have hconj' : n⁻¹ * t * n = t := by
    calc n⁻¹ * t * n = n⁻¹ * (t * n) := by group
      _ = t := by rw [← hn, inv_mul_cancel_left]
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, by simp only [← conj_zpow, hconj]⟩
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hz : z = n⁻¹ * (n * z * n⁻¹) * n := by group
    show t ^ k = z
    have hpow : n⁻¹ * t ^ k * n = (n⁻¹ * t * n) ^ k := by
      rw [show n⁻¹ * t * n = n⁻¹ * t * n⁻¹⁻¹ by rw [inv_inv], conj_zpow, inv_inv]
    rw [hz, ← hk, hpow, hconj']

theorem ggSix_normalizer_zpowers_le_centralizer [Finite G] {t : G} (ht : orderOf t = 2) :
    Subgroup.normalizer (Subgroup.zpowers t : Set G) ≤ Subgroup.centralizer {t} := by
  classical
  intro n hn
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hmem : n * t * n⁻¹ ∈ Subgroup.zpowers t :=
    (Subgroup.mem_normalizer_iff.mp hn t).mp (Subgroup.mem_zpowers t)
  rw [mem_zpowers_iff_mem_range_orderOf, ht, Finset.mem_image] at hmem
  obtain ⟨i, hi, hit⟩ := hmem
  rw [Finset.mem_range] at hi
  interval_cases i
  · exfalso
    rw [pow_zero] at hit
    have ht1 : t = 1 := by
      have := congrArg (fun y => n⁻¹ * y * n) hit
      simpa [mul_assoc] using this.symm
    rw [ht1, orderOf_one] at ht
    exact absurd ht (by norm_num)
  · rw [pow_one] at hit
    calc n * t = n * t * n⁻¹ * n := by group
      _ = t * n := by rw [← hit]

theorem ggSix_isTwoLocal_normalizer_zpowers [Finite G] {t : G} (ht : orderOf t = 2) :
    IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers t : Set G)) := by
  refine ⟨Subgroup.zpowers t, ?_, IsPGroup.of_card (n := 1) ?_, rfl⟩
  · rw [Ne, Subgroup.zpowers_eq_bot]
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  · rw [Nat.card_zpowers, ht, pow_one]

section TwoLocal

variable [Finite G] {M Y : Subgroup G} {t : G}

omit [Finite G] in
theorem ggSix_pCoreOf_inf_eq_bot (hYt : Y ≤ Subgroup.centralizer {t})
    (hY : ∀ Q : Subgroup G, Q ≤ Y → IsPGroup 2 Q → Y ≤ Subgroup.normalizer (Q : Set G) → Q = ⊥) :
    pCoreOf 2 (Subgroup.normalizer (Subgroup.zpowers t : Set G)) ⊓ Y = ⊥ := by
  set P := pCoreOf 2 (Subgroup.normalizer (Subgroup.zpowers t : Set G))
  have hYN : Y ≤ Subgroup.normalizer (P : Set G) :=
    (hYt.trans (ggSix_centralizer_le_normalizer_zpowers t)).trans
      (ggSix_le_normalizer_pCoreOf 2 _)
  refine hY (P ⊓ Y) inf_le_right ((ggSix_pCoreOf_isPGroup 2 _).to_le inf_le_left) ?_
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have h1 := Subgroup.mem_normalizer_iff.mp (hYN hy) z
  have h2 : z ∈ Y ↔ y * z * y⁻¹ ∈ Y := by
    constructor
    · intro hz
      exact Y.mul_mem (Y.mul_mem hy hz) (Y.inv_mem hy)
    · intro hz
      have := Y.mul_mem (Y.mul_mem (Y.inv_mem hy) hz) hy
      simpa [mul_assoc] using this
  simp only [Subgroup.mem_inf]
  exact ⟨fun h => ⟨h1.mp h.1, h2.mp h.2⟩, fun h => ⟨h1.mpr h.1, h2.mpr h.2⟩⟩

theorem ggSix_commute_of_mem_pCoreOf_inf (ht : orderOf t = 2)
    (hYt : Y ≤ Subgroup.centralizer {t})
    (hY : ∀ Q : Subgroup G, Q ≤ Y → IsPGroup 2 Q → Y ≤ Subgroup.normalizer (Q : Set G) → Q = ⊥)
    (hMY : M ⊓ Subgroup.centralizer {t} ≤ Subgroup.normalizer (Y : Set G)) {x : G}
    (hx : x ∈ pCoreOf 2 (Subgroup.normalizer (Subgroup.zpowers t : Set G)) ⊓ M) {y : G}
    (hy : y ∈ Y) : x * y = y * x := by
  set P := pCoreOf 2 (Subgroup.normalizer (Subgroup.zpowers t : Set G))
  have hYN : Y ≤ Subgroup.normalizer (P : Set G) :=
    (hYt.trans (ggSix_centralizer_le_normalizer_zpowers t)).trans
      (ggSix_le_normalizer_pCoreOf 2 _)
  have hxt : x ∈ M ⊓ Subgroup.centralizer {t} :=
    ⟨hx.2, ggSix_normalizer_zpowers_le_centralizer ht (ggSix_pCoreOf_le 2 _ hx.1)⟩
  have hc1 : x * y * x⁻¹ * y⁻¹ ∈ P := by
    have h := (Subgroup.mem_normalizer_iff.mp (hYN hy) x⁻¹).mp (P.inv_mem hx.1)
    have := P.mul_mem hx.1 h
    simpa [mul_assoc] using this
  have hc2 : x * y * x⁻¹ * y⁻¹ ∈ Y :=
    Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hMY hxt) y).mp hy) (Y.inv_mem hy)
  have hc : x * y * x⁻¹ * y⁻¹ = 1 := by
    have h : x * y * x⁻¹ * y⁻¹ ∈ P ⊓ Y := ⟨hc1, hc2⟩
    rw [ggSix_pCoreOf_inf_eq_bot hYt hY] at h
    exact Subgroup.mem_bot.mp h
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [hc, one_mul]

theorem ggSix_eq_one_of_charTwo (hchar : IsCharTwoType G) {b a : G} (ht : orderOf t = 2)
    (hYt : Y ≤ Subgroup.centralizer {t})
    (hY : ∀ Q : Subgroup G, Q ≤ Y → IsPGroup 2 Q → Y ≤ Subgroup.normalizer (Q : Set G) → Q = ⊥)
    (hMY : M ⊓ Subgroup.centralizer {t} ≤ Subgroup.normalizer (Y : Set G)) (hbY : b ∈ Y)
    (hb : IsPGroup 2 (Subgroup.zpowers b)) (hbM : Subgroup.centralizer {b} ≤ M) (haY : a ∈ Y)
    (hab : a * b = b * a) (ha : Odd (orderOf a)) : a = 1 := by
  set H := Subgroup.normalizer (Subgroup.zpowers t : Set G) with hH
  set P := pCoreOf 2 H with hP
  have hP2 : IsPGroup 2 P := ggSix_pCoreOf_isPGroup 2 H
  have hYH : Y ≤ H := hYt.trans (ggSix_centralizer_le_normalizer_zpowers t)
  have hHP : H ≤ Subgroup.normalizer (P : Set G) := ggSix_le_normalizer_pCoreOf 2 H
  have hcop : (Nat.card P).Coprime (Nat.card (Subgroup.zpowers a)) := by
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    rw [hk, Nat.card_zpowers]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr ha)
  have hab' : a ∈ Subgroup.centralizer (Subgroup.zpowers b : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact ((Commute.zpow_right (show Commute a b from hab) k).symm).eq
  have hfix : a ∈ Subgroup.centralizer
      ((P ⊓ Subgroup.centralizer (Subgroup.zpowers b : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hhb : h ∈ Subgroup.centralizer {b} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have := Subgroup.mem_centralizer_iff.mp hh.2 b (Subgroup.mem_zpowers b)
      exact this.symm
    exact ggSix_commute_of_mem_pCoreOf_inf ht hYt hY hMY ⟨hh.1, hbM hhb⟩ haY
  have hAB := CFSG.RankThreeCoreUniqueness.Helpers.ambient_subgroup_axb_centralizer_le 2
    Nat.prime_two (Subgroup.zpowers b) (Subgroup.zpowers a) P hb hP2 hcop
    (Subgroup.zpowers_le.mpr (hHP (hYH hbY))) (Subgroup.zpowers_le.mpr (hHP (hYH haY)))
    (Subgroup.zpowers_le.mpr hab') (Subgroup.zpowers_le.mpr hfix)
  have haP : a ∈ P :=
    hchar H (ggSix_isTwoLocal_normalizer_zpowers ht) ⟨hYH haY, hAB (Subgroup.mem_zpowers a)⟩
  exact ggSix_eq_one_of_mem_of_odd hP2 haP ha

theorem ggSix_false_of_charTwo (hchar : IsCharTwoType G) {b a : G} (ht : orderOf t = 2)
    (hYt : Y ≤ Subgroup.centralizer {t})
    (hY : ∀ Q : Subgroup G, Q ≤ Y → IsPGroup 2 Q → Y ≤ Subgroup.normalizer (Q : Set G) → Q = ⊥)
    (hMY : M ⊓ Subgroup.centralizer {t} ≤ Subgroup.normalizer (Y : Set G)) (hbY : b ∈ Y)
    (hb : IsPGroup 2 (Subgroup.zpowers b)) (hbM : Subgroup.centralizer {b} ≤ M) (haY : a ∈ Y)
    (hab : a * b = b * a) (ha : Odd (orderOf a)) (ha1 : a ≠ 1) : False :=
  ha1 (ggSix_eq_one_of_charTwo hchar ht hYt hY hMY hbY hb hbM haY hab ha)

end TwoLocal

end CFSG.StandardType
