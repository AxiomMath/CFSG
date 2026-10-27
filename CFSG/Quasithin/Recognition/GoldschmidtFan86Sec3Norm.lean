module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Iface
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3TSlide
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Frattini
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Local
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Star
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TArcEven

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

local notation "pval" => CFSG.Quasithin.Fan86.valence

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace FanTree

variable (F : FanTree Γ G)
include F

theorem false_of_normalizes {v : V} {y : G} (hy : y ∈ MulAction.stabilizer G v)
    (hyo : orderOf y = pval Γ v)
    (hn : ∀ g ∈ MulAction.stabilizer G v, g * y * g⁻¹ ∈ Subgroup.zpowers y) : False := by
  set H := MulAction.stabilizer G v with hH
  have : Finite H := F.loc_finite v
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : (pval Γ v).Prime := F.valence_isPrime v
  have hodd : pval Γ v ≠ 2 := by
    have e : pval Γ v = Nat.card (Γ.neighborSet v) := rfl
    rw [e]
    rcases F.valence v with h | h <;> omega
  have hO2 : IsPGroup 2 (pCoreOf 2 H) := (pCore_isPGroup (G := ↥H) 2).map H.subtype
  have hxp : y ^ pval Γ v = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
  have key : ∀ c ∈ Subgroup.zpowers y, c ∈ pCoreOf 2 H → c = 1 := by
    intro c hc hcO
    obtain ⟨k, rfl⟩ := hc
    obtain ⟨n, hn⟩ := hO2 ⟨y ^ k, hcO⟩
    have h2 : (y ^ k) ^ (2 ^ n) = 1 := congrArg Subtype.val hn
    have h3 : (y ^ k) ^ pval Γ v = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxp, one_zpow]
    have hcop : Nat.Coprime (2 ^ n) (pval Γ v) :=
      Nat.Coprime.pow_left n ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hodd))
    have := pow_gcd_eq_one.2 ⟨h2, h3⟩
    rwa [hcop, pow_one] at this
  have hcent : y ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro o ho
    have hoH : o ∈ H := pCoreOf_le 2 H ho
    have h1 : o⁻¹ * y * o⁻¹⁻¹ ∈ Subgroup.zpowers y := hn o⁻¹ (H.inv_mem hoH)
    have h2 : y⁻¹ * o⁻¹ * y * o ∈ Subgroup.zpowers y := by
      have := (Subgroup.zpowers y).mul_mem (inv_mem (Subgroup.mem_zpowers y)) h1
      simpa [mul_assoc] using this
    have h3 : y⁻¹ * o⁻¹ * y * o ∈ pCoreOf 2 H := by
      have hn' := le_normalizer_pCoreOf 2 H (H.inv_mem hy)
      have := (pCoreOf 2 H).mul_mem ((Subgroup.mem_normalizer_iff.1 hn' o⁻¹).1
        ((pCoreOf 2 H).inv_mem ho)) ho
      simpa [mul_assoc] using this
    have hc := key _ h2 h3
    have e1 : o⁻¹ * y * o = y := by
      have := congrArg (fun z => y * z) hc
      simpa [mul_assoc] using this
    calc o * y = o * (o⁻¹ * y * o) * 1 := by rw [e1, mul_one]
      _ = y * o := by group
  have hyO : y ∈ pCoreOf 2 H := F.charTwo v ⟨hy, hcent⟩
  have := key y (Subgroup.mem_zpowers y) hyO
  rw [this, orderOf_one] at hyo
  have := hp.two_le
  omega

theorem normalizes_of_centralizes (L : LocalFacts F) {v : V} {y : G}
    (hy : y ∈ MulAction.stabilizer G v) (hyo : orderOf y = pval Γ v)
    (hc : ∀ k ∈ nbrStab Γ G v, y * k * y⁻¹ = k) :
    ∀ g ∈ MulAction.stabilizer G v, g * y * g⁻¹ ∈ Subgroup.zpowers y := by
  intro g hg
  obtain ⟨i, k, hk, hgk⟩ := L.conj_mem hy hyo hg
  have hyp : y ^ pval Γ v = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
  have hcomm : Commute (y ^ i) k := by
    have : y * k = k * y := by
      have := hc k hk
      rwa [mul_inv_eq_iff_eq_mul] at this
    exact (Commute.pow_left (show Commute y k from this) i)
  have h1 : (g * y * g⁻¹) ^ pval Γ v = 1 := by
    have : (g * y * g⁻¹) ^ pval Γ v = g * y ^ pval Γ v * g⁻¹ := by
      rw [← conj_pow]
    rw [this, hyp]
    group
  rw [hgk, hcomm.mul_pow, ← pow_mul, mul_comm i, pow_mul, hyp, one_pow, one_mul] at h1
  obtain ⟨m, hm⟩ := (F.nbrStab_isPGroup v) ⟨k, hk⟩
  have hk2 : k ^ (2 ^ m) = 1 := congrArg Subtype.val hm
  have hp : (pval Γ v).Prime := F.valence_isPrime v
  have hodd : pval Γ v ≠ 2 := by
    have e : pval Γ v = Nat.card (Γ.neighborSet v) := rfl
    rw [e]
    rcases F.valence v with h | h <;> omega
  have hcop : Nat.Coprime (2 ^ m) (pval Γ v) :=
    Nat.Coprime.pow_left m ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hodd))
  have hk1 : k = 1 := by
    have := pow_gcd_eq_one.2 ⟨hk2, h1⟩
    rwa [hcop, pow_one] at this
  rw [hgk, hk1, mul_one]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers y) i

theorem false_of_centralizes (L : LocalFacts F) {v : V} {y : G} (hy : y ∈ MulAction.stabilizer G v)
    (hyo : orderOf y = pval Γ v) (hc : ∀ k ∈ nbrStab Γ G v, y * k * y⁻¹ = k) : False :=
  F.false_of_normalizes hy hyo (F.normalizes_of_centralizes L hy hyo hc)

end FanTree

end CFSG.Quasithin.Fan86
