module

public import CFSG.Quasithin.Background.A1cRank
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped commutatorElement

namespace SBc13

section Rank

variable {G : Type*} [Group G]

def wzpowers (W : Subgroup G) (k : G) (hk : k ∈ Subgroup.normalizer (W : Set G)) : Subgroup G where
  carrier := {x | ∃ w ∈ W, ∃ n : ℤ, x = w * k ^ n}
  mul_mem' := by
    rintro _ _ ⟨w, hw, n, rfl⟩ ⟨w', hw', m, rfl⟩
    have hkn : k ^ n ∈ Subgroup.normalizer (W : Set G) := Subgroup.zpow_mem _ hk n
    have h1 : k ^ n * w' * (k ^ n)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp hkn w').mp hw'
    refine ⟨w * (k ^ n * w' * (k ^ n)⁻¹), W.mul_mem hw h1, n + m, ?_⟩
    rw [zpow_add]
    group
  one_mem' := ⟨1, W.one_mem, 0, by simp⟩
  inv_mem' := by
    rintro _ ⟨w, hw, n, rfl⟩
    have hkn : k ^ (-n) ∈ Subgroup.normalizer (W : Set G) := Subgroup.zpow_mem _ hk (-n)
    have h1 : k ^ (-n) * w⁻¹ * (k ^ (-n))⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp hkn w⁻¹).mp (W.inv_mem hw)
    refine ⟨k ^ (-n) * w⁻¹ * (k ^ (-n))⁻¹, h1, -n, ?_⟩
    group

theorem le_wzpowers (W : Subgroup G) {k : G} (hk : k ∈ Subgroup.normalizer (W : Set G)) :
    W ≤ wzpowers W k hk := fun w hw => ⟨w, hw, 0, by simp⟩

theorem mem_wzpowers_self (W : Subgroup G) {k : G} (hk : k ∈ Subgroup.normalizer (W : Set G)) :
    k ∈ wzpowers W k hk := ⟨1, W.one_mem, 1, by simp⟩

theorem zpow_mem_eq_one_of_prime_order [Finite G] {p : ℕ} [hp : Fact p.Prime] {J : Subgroup G}
    {k : G} (hk : orderOf k = p) (hkJ : k ∉ J) {n : ℤ} (h : k ^ n ∈ J) : k ^ n = 1 := by
  by_contra hne
  have hpow : (k ^ n) ^ p = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hk, pow_orderOf_eq_one,
      one_zpow]
  have hord : orderOf (k ^ n) = p := orderOf_eq_prime hpow hne
  have hle : Subgroup.zpowers (k ^ n) ≤ Subgroup.zpowers k := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers k) n
  have hcard : Nat.card (Subgroup.zpowers k) ≤ Nat.card (Subgroup.zpowers (k ^ n)) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hord, hk]
  have heq : Subgroup.zpowers (k ^ n) = Subgroup.zpowers k :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  apply hkJ
  have : k ∈ Subgroup.zpowers (k ^ n) := by rw [heq]; exact Subgroup.mem_zpowers k
  exact (Subgroup.zpowers_le.mpr h) this

theorem pRank_succ_le_of_commutes {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) [Finite G]
    {X J : Subgroup G} (hJX : J ≤ X) {k : G} (hkX : k ∈ X)
    (hkN : k ∈ Subgroup.normalizer (J : Set G)) (hk : orderOf k = p) (hkJ : k ∉ J)
    (hcomm : ∀ x ∈ J, ⁅x, k⁆ ∈ pCoreOf 2 J) : pRank p J + 1 ≤ pRank p X := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W : Subgroup G := pCoreOf 2 J with hW
  have hWJ : W ≤ J := CFSG.LieType.BorelTits.pCoreOf_le 2 J
  have hW2 : IsPGroup 2 W := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J
  have hJW : J ≤ Subgroup.normalizer (W : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J
  have hkW : k ∈ Subgroup.normalizer (W : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 J hkN
  set H : Subgroup G := wzpowers W k hkW with hH
  have hHX : H ≤ X := by
    rintro _ ⟨w, hw, n, rfl⟩
    exact X.mul_mem (hJX (hWJ hw)) (Subgroup.zpow_mem X hkX n)
  have hEH : J ≤ Subgroup.normalizer (H : Set G) := by
    intro e he
    apply Subgroup.mem_normalizer_fintype
    rintro _ ⟨w, hw, n, rfl⟩
    have h1 : e * w * e⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hJW he) w).mp hw
    have h2' : e * k * e⁻¹ ∈ H := by
      have : e * k * e⁻¹ = ⁅e, k⁆ * k := by simp only [commutatorElement_def]; group
      rw [this]
      exact H.mul_mem (le_wzpowers W hkW (hcomm e he)) (mem_wzpowers_self W hkW)
    have h3 : e * (w * k ^ n) * e⁻¹ = (e * w * e⁻¹) * (e * k * e⁻¹) ^ n := by
      rw [conj_zpow]
      group
    show e * (w * k ^ n) * e⁻¹ ∈ H
    rw [h3]
    exact H.mul_mem (le_wzpowers W hkW h1) (Subgroup.zpow_mem H h2' n)
  obtain ⟨E, hEJ, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.out.one_lt J
  have hdvd : p ∣ Nat.card H := by
    have h1 : Subgroup.zpowers k ≤ H := Subgroup.zpowers_le.mpr (mem_wzpowers_self W hkW)
    have h2' := Subgroup.card_dvd_of_le h1
    rwa [Nat.card_zpowers, hk] at h2'
  obtain ⟨y, hyH, hyord, hyc⟩ := exists_orderOf_eq_of_isPGroup_normalizer
    (isPGroup_of_isElemAbelian hE) (fun e he => hEH (hEJ he)) hdvd
  have hyE : y ∉ E := by
    intro hyE
    obtain ⟨w, hw, n, hyw⟩ := hyH
    have hyJ : y ∈ J := hEJ hyE
    have hkn : k ^ n ∈ J := by
      have : k ^ n = w⁻¹ * y := by rw [hyw]; group
      rw [this]
      exact J.mul_mem (J.inv_mem (hWJ hw)) hyJ
    have h1 := zpow_mem_eq_one_of_prime_order hk hkJ hkn
    rw [h1, mul_one] at hyw
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hW2) ⟨y, hyw ▸ hw⟩
    have hym : orderOf y = 2 ^ m := by
      rw [← hm]
      exact Subgroup.orderOf_coe (⟨y, hyw ▸ hw⟩ : W)
    rw [hyord] at hym
    have h5 : p ∣ 2 := hp.out.dvd_of_dvd_pow (dvd_of_eq hym)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h5)
  obtain ⟨hA, hAcard⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers hE hyord
    (fun e he => Subgroup.mem_centralizer_iff.mp hyc e he) hyE
  have hAX : E ⊔ Subgroup.zpowers y ≤ X :=
    sup_le (hEJ.trans hJX) (Subgroup.zpowers_le.mpr (hHX hyH))
  exact CFSG.Quasithin.le_pRank hp.out hAX hA (k := pRank p J + 1)
    (by rw [hAcard, hEcard, pow_succ])

end Rank

end SBc13

end CFSG.Quasithin
