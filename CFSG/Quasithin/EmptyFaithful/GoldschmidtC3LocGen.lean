module

public import CFSG.Quasithin.EmptyFaithful.A38c8Out
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239ListedBasic
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S151ZD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace GoldC3

open CFSG.QuasithinUnique.Vol2Native.L239 (HasChi0Block isChi0Block_of_isChi0Block_sup)

variable {G : Type} [Group G]

theorem eq_or_eq_of_card_three [Finite G] {B K P : Subgroup G} (hBK : B ≤ K) (hKP : K ≤ P)
    (hcard : Nat.card P = 3 * Nat.card B) : K = B ∨ K = P := by
  have h1 : Nat.card B ∣ Nat.card K := Subgroup.card_dvd_of_le hBK
  have h2 : Nat.card K ∣ Nat.card P := Subgroup.card_dvd_of_le hKP
  have hBpos : 0 < Nat.card B := Nat.card_pos
  obtain ⟨d, hd⟩ := h1
  have hd3 : d ∣ 3 := by
    rw [hcard, hd, mul_comm 3] at h2
    exact Nat.dvd_of_mul_dvd_mul_left hBpos h2
  rcases (Nat.dvd_prime Nat.prime_three).1 hd3 with h | h
  · left
    subst h
    exact (Subgroup.eq_of_le_of_card_ge hBK (by rw [hd]; omega)).symm
  · right
    subst h
    exact Subgroup.eq_of_le_of_card_ge hKP (by rw [hcard, hd]; omega)

theorem sMin_of_card_three [Finite G] {L S P : Subgroup G} (hPL : P ≤ L) (hBP : S ⊓ L ≤ P)
    (hcard : Nat.card P = 3 * Nat.card (S ⊓ L : Subgroup G))
    (hSP : S ≤ Subgroup.normalizer (P : Set G)) : SMin L S P where
  le := hPL
  sl := hBP
  ne := by
    intro h
    have h1 : Nat.card (S ⊓ L : Subgroup G) = Nat.card P := by rw [h]
    have h2 : 0 < Nat.card P := Nat.card_pos
    omega
  sP := hSP
  minimal K _ hBK hKP := eq_or_eq_of_card_three hBK hKP hcard

theorem oPrime_sup_eq [Finite G] {P B : Subgroup G} (hB2 : IsPGroup 2 B) (hBP : B ≤ P)
    (hcard : Nat.card P = 3 * Nat.card B) : oPrimeResidualOf 3 P ⊔ B = P := by
  have hle : oPrimeResidualOf 3 P ≤ P := (Subgroup.closure_le P).2 fun x hx => hx.1
  rcases eq_or_eq_of_card_three (le_sup_right : B ≤ oPrimeResidualOf 3 P ⊔ B)
      (sup_le hle hBP) hcard with h | h
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3 : 3 ∣ Nat.card P := by rw [hcard]; exact Dvd.intro _ rfl
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 3 h3
    have hxo : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
    have hxO : (x : G) ∈ oPrimeResidualOf 3 P :=
      Subgroup.subset_closure ⟨x.2, 1, by rw [pow_one]; exact hxo⟩
    have hxB : (x : G) ∈ B := by
      rw [← h]
      exact Subgroup.mem_sup_left hxO
    obtain ⟨k, hk⟩ := hB2 ⟨x, hxB⟩
    have hk' : (x : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hdvd : 3 ∣ 2 ^ k := by
      have := orderOf_dvd_of_pow_eq_one hk'
      rwa [hxo] at this
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega
  · exact h

theorem not_c126Third_of_not_hasChi0Block {P S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSP : S ≤ Subgroup.normalizer (P : Set G)) (hP : ¬ HasChi0Block P) :
    ¬ C126Third (P ⊔ S) S := by
  rintro ⟨r, K, hr, hK, -⟩
  exact hP ⟨K ⟨0, hr⟩, isChi0Block_of_isChi0Block_sup hS2 hSP (hK ⟨0, hr⟩).1⟩

theorem le_normalizer_inf {L S : Subgroup G} (hSN : S ≤ Subgroup.normalizer (L : Set G)) :
    S ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have hsL := Subgroup.mem_normalizer_iff.1 (hSN hs)
  have hsL' := Subgroup.mem_normalizer_iff.1 (hSN (S.inv_mem hs))
  constructor
  · rintro ⟨hxS, hxL⟩
    exact ⟨S.mul_mem (S.mul_mem hs hxS) (S.inv_mem hs), (hsL x).1 hxL⟩
  · rintro ⟨hxS, hxL⟩
    have h1 : s⁻¹ * (s * x * s⁻¹) * s ∈ S := S.mul_mem (S.mul_mem (S.inv_mem hs) hxS) hs
    have h2 := (hsL' (s * x * s⁻¹)).1 hxL
    refine ⟨?_, ?_⟩
    · simpa [mul_assoc] using h1
    · simpa [mul_assoc] using h2

theorem exists_conj_of_odd_out {L S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSN : S ≤ Subgroup.normalizer (L : Set G))
    (hout : ∀ α : MulAut ↥L, (∃ a : ℕ, α ^ 2 ^ a = 1) → ∃ g : ↥L, ∀ x, α x = g * x * g⁻¹)
    (hZ : ∀ g : ↥L, (∀ x : ↥L, x * g = g * x) → g = 1) {s : G} (hs : s ∈ S) :
    ∃ g ∈ L, (∀ x ∈ L, s * x * s⁻¹ = g * x * g⁻¹) ∧ ∃ a : ℕ, g ^ 2 ^ a = 1 := by
  obtain ⟨a, ha⟩ := hS2 ⟨s, hs⟩
  have ha' : s ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  let ψ : MulAut ↥L := L.normalizerMonoidHom ⟨s, hSN hs⟩
  have hψ : ∀ y : ↥L, ((ψ y : ↥L) : G) = s * (y : G) * s⁻¹ := fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨s, hSN hs⟩ y
  have hψa : ψ ^ 2 ^ a = 1 := by
    rw [← map_pow]
    have : (⟨s, hSN hs⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 2 ^ a = 1 :=
      Subtype.ext (by simpa using ha')
    rw [this, map_one]
  obtain ⟨g, hg⟩ := hout ψ ⟨a, hψa⟩
  have hconj : ∀ x ∈ L, s * x * s⁻¹ = (g : G) * x * (g : G)⁻¹ := by
    intro x hx
    have := congrArg Subtype.val (hg ⟨x, hx⟩)
    rw [hψ] at this
    simpa using this
  have hZ' : Subgroup.center ↥L = ⊥ :=
    (Subgroup.eq_bot_iff_forall _).2 fun x hx => hZ x (Subgroup.mem_center_iff.1 hx)
  exact ⟨(g : G), g.2, hconj, a, A38c8.pow_eq_one_of_conj_eq_of_center_eq_bot hZ' g.2 hconj ha'⟩

variable [Finite G]

theorem normalizer_le_of_odd_out {L S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) (hSyl : IsSylowTwoOf (S ⊓ L) L)
    (hout : ∀ α : MulAut ↥L, (∃ a : ℕ, α ^ 2 ^ a = 1) → ∃ g : ↥L, ∀ x, α x = g * x * g⁻¹)
    (hZ : ∀ g : ↥L, (∀ x : ↥L, x * g = g * x) → g = 1) :
    L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) ≤ Subgroup.normalizer (S : Set G) := by
  have key : ∀ s ∈ S, ∃ g ∈ (S ⊓ L : Subgroup G), ∀ x ∈ L, s * x * s⁻¹ = g * x * g⁻¹ := by
    intro s hs
    obtain ⟨g, hgL, hconj, a, ha⟩ := exists_conj_of_odd_out hS2 hSN hout hZ hs
    have hgN : g ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
      A38c8.mem_normalizer_of_conj_eq_on_le inf_le_right hgL hconj (le_normalizer_inf hSN hs)
    have hz2 : IsPGroup 2 (Subgroup.zpowers g) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨j, -, hjn⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one ha)
      exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hjn])
    have hle : Subgroup.zpowers g ≤ S ⊓ L :=
      FLc.le_of_normalizes_of_sylow hSyl le_rfl inf_le_right ((Subgroup.zpowers_le).2 hgL) hz2
        ((Subgroup.zpowers_le).2 hgN)
    exact ⟨g, hle (Subgroup.mem_zpowers g), hconj⟩
  intro n hn
  have hnL : n ∈ L := hn.1
  have hnB : n ∈ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) := hn.2
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨g, hgB, hgconj⟩ := key x hx
  have hc : n * (g⁻¹ * x) = (g⁻¹ * x) * n := by
    have h1 := hgconj n hnL
    calc n * (g⁻¹ * x) = g⁻¹ * (g * n * g⁻¹) * x := by group
      _ = g⁻¹ * (x * n * x⁻¹) * x := by rw [h1]
      _ = (g⁻¹ * x) * n := by group
  have hdec : n * x * n⁻¹ = (n * g * n⁻¹) * (g⁻¹ * x) := by
    calc n * x * n⁻¹ = (n * g * n⁻¹) * (n * (g⁻¹ * x) * n⁻¹) := by group
      _ = (n * g * n⁻¹) * (g⁻¹ * x) := by rw [hc]; group
  rw [hdec]
  exact S.mul_mem ((Subgroup.mem_normalizer_iff.1 hnB g).1 hgB).1
    (S.mul_mem (S.inv_mem hgB.1) hx)

end GoldC3

end CFSG.Quasithin
