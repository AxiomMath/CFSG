module

public import CFSG.Sporadic.Recognition.JankoWongBSStep
import CFSG.Dihedral.DisconnectedInvolutionGraph.OddCore

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open Subgroup

section Core

private theorem zpowers_le_center {K : Type*} [Group K] {a : K} (haK : ∀ k : K, k * a = a * k) :
    zpowers a ≤ center K :=
  Subgroup.zpowers_le.mpr (Subgroup.mem_center_iff.mpr haK)

private theorem brauerSuzuki_quotient
    {K : Type*} [Group K] [Finite K] {a z r₁ r₂ : K} [(zpowers a).Normal]
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (haK : ∀ k : K, k * a = a * k) (hz2 : z ^ 2 = 1)
    (hBS : (QuotientGroup.mk z : K ⧸ CFSG.oddCore K) ∈ Subgroup.center (K ⧸ CFSG.oddCore K))
    (hT : Nat.card ↥(Subgroup.centralizer ({z} : Set K)) = 360)
    (hodd : ∀ W : Subgroup K, W ≤ Subgroup.centralizer ({z} : Set K) →
      (∀ t ∈ Subgroup.centralizer ({z} : Set K), ∀ w ∈ W, t * w * t⁻¹ ∈ W) →
      Odd (Nat.card W) → W ≤ Subgroup.zpowers a)
    (hr₁ : orderOf r₁ = 5) (hr₂ : orderOf r₂ = 5) (hr₁₂ : (r₁ * r₂) ^ 2 = z) :
    Nat.card K * 3 = Nat.card (CFSG.oddCore K) * 360 ∧
    zpowers a ≤ CFSG.oddCore K ∧
    CFSG.oddCore K ⊓ centralizer ({z} : Set K) = zpowers a ∧
    (∀ x ∈ (CFSG.oddCore K).map (QuotientGroup.mk' (zpowers a)),
      ∀ y ∈ (CFSG.oddCore K).map (QuotientGroup.mk' (zpowers a)), x * y = y * x) ∧
    (∀ x ∈ (CFSG.oddCore K).map (QuotientGroup.mk' (zpowers a)),
      QuotientGroup.mk' (zpowers a) z * x * (QuotientGroup.mk' (zpowers a) z)⁻¹ = x⁻¹) ∧
    QuotientGroup.mk' (zpowers a) r₁ ^ 5 = 1 ∧ QuotientGroup.mk' (zpowers a) r₂ ^ 5 = 1 ∧
    (QuotientGroup.mk' (zpowers a) r₁ * QuotientGroup.mk' (zpowers a) r₂) ^ 2 =
      QuotientGroup.mk' (zpowers a) z := by
  have hMn : (CFSG.oddCore K).Normal := CFSG.oddCore_normal K
  have hModd : Odd (Nat.card (CFSG.oddCore K)) :=
    CFSG.DisconnectedInvolutionGraph.Helpers.oddCore_odd
  have haorder : orderOf a = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime ha3 ha1
  have hZcard : Nat.card (zpowers a) = 3 := by rw [Nat.card_zpowers, haorder]
  have hZc : ∀ c ∈ zpowers a, ∀ g : K, g * c = c * g := fun c hc g =>
    Subgroup.mem_center_iff.mp (zpowers_le_center haK hc) g
  have hZ3 : ∀ c ∈ zpowers a, c ^ 3 = 1 := by
    intro c hc
    have := pow_card_eq_one' (G := zpowers a) (x := ⟨c, hc⟩)
    rw [hZcard] at this
    exact congrArg Subtype.val this
  have hZM : zpowers a ≤ CFSG.oddCore K :=
    CFSG.DisconnectedInvolutionGraph.Helpers.normal_odd_le_oddCore _ inferInstance
      (by rw [hZcard]; exact ⟨1, rfl⟩)
  have hKMT := fun k : K => exists_mem_centralizer_of_central_mod hModd hz2 hBS k
  have hW : CFSG.oddCore K ⊓ centralizer ({z} : Set K) = zpowers a := by
    have hle : CFSG.oddCore K ⊓ centralizer ({z} : Set K) ≤ zpowers a := by
      refine hodd _ inf_le_right (fun t ht w hw => ⟨hMn.conj_mem w hw.1 t, ?_⟩) ?_
      · exact (centralizer ({z} : Set K)).mul_mem
          ((centralizer ({z} : Set K)).mul_mem ht hw.2) ((centralizer ({z} : Set K)).inv_mem ht)
      · exact Odd.of_dvd_nat hModd (Subgroup.card_dvd_of_le inf_le_left)
    refine le_antisymm hle (le_inf hZM ?_)
    intro c hc
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hZc c hc z).symm
  have hcardMT : Nat.card K * 3 = Nat.card (CFSG.oddCore K) * 360 := by
    have := card_mul_card_inf_of_exists_mem hKMT
    rwa [hW, hZcard, hT] at this
  have hMbn : ((CFSG.oddCore K).map (QuotientGroup.mk' (zpowers a))).Normal :=
    hMn.map _ (QuotientGroup.mk'_surjective _)
  have hfpf : ∀ y ∈ (CFSG.oddCore K).map (QuotientGroup.mk' (zpowers a)),
      QuotientGroup.mk' (zpowers a) z * y = y * QuotientGroup.mk' (zpowers a) z → y = 1 := by
    intro y hy hyz
    refine eq_one_of_commute_map hZ3 hZc hz2 ?_ hy hyz
    intro m hm hmz
    rw [← hW]
    exact ⟨hm, Subgroup.mem_centralizer_singleton_iff.mpr hmz.symm⟩
  have hz2b : QuotientGroup.mk' (zpowers a) z ^ 2 = 1 := by rw [← map_pow, hz2, map_one]
  have hinv := inverts_of_fpf hz2b (fun y hy => hMbn.conj_mem y hy _) hfpf
  refine ⟨hcardMT, hZM, hW, commutative_of_inverted hinv, hinv, ?_, ?_, ?_⟩
  · rw [← map_pow, ← hr₁, pow_orderOf_eq_one, map_one]
  · rw [← map_pow, ← hr₂, pow_orderOf_eq_one, map_one]
  · rw [← map_mul, ← map_pow, hr₁₂]

end Core

theorem brauerSuzuki_structure
    {K : Type*} [Group K] [Finite K] {a z r₁ r₂ : K}
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (haK : ∀ k : K, k * a = a * k) (hz2 : z ^ 2 = 1)
    (hBS : (QuotientGroup.mk z : K ⧸ CFSG.oddCore K) ∈ Subgroup.center (K ⧸ CFSG.oddCore K))
    (hT : Nat.card ↥(Subgroup.centralizer ({z} : Set K)) = 360)
    (hodd : ∀ W : Subgroup K, W ≤ Subgroup.centralizer ({z} : Set K) →
      (∀ t ∈ Subgroup.centralizer ({z} : Set K), ∀ w ∈ W, t * w * t⁻¹ ∈ W) →
      Odd (Nat.card W) → W ≤ Subgroup.zpowers a)
    (hr₁ : orderOf r₁ = 5) (hr₂ : orderOf r₂ = 5) (hr₁₂ : (r₁ * r₂) ^ 2 = z) :
    Nat.card K * 3 = Nat.card (CFSG.oddCore K) * 360 ∧
    Subgroup.zpowers a ≤ CFSG.oddCore K ∧
    CFSG.oddCore K ⊓ Subgroup.centralizer ({z} : Set K) = Subgroup.zpowers a ∧
    (∀ m ∈ CFSG.oddCore K, ∀ n ∈ CFSG.oddCore K, m * n * m⁻¹ * n⁻¹ ∈ Subgroup.zpowers a) ∧
    (∀ m ∈ CFSG.oddCore K, z * m * z⁻¹ * m ∈ Subgroup.zpowers a) := by
  have : (zpowers a).Normal := Subgroup.normal_of_le_center (zpowers_le_center haK)
  obtain ⟨hcard, hZM, hW, hcomm, hinv, -, -, -⟩ :=
    brauerSuzuki_quotient ha3 ha1 haK hz2 hBS hT hodd hr₁ hr₂ hr₁₂
  refine ⟨hcard, hZM, hW, fun m hm n hn => ?_, fun m hm => ?_⟩
  · refine (QuotientGroup.eq_one_iff _).mp ?_
    have h := hcomm _ (Subgroup.mem_map_of_mem _ hm) _ (Subgroup.mem_map_of_mem _ hn)
    change QuotientGroup.mk' (zpowers a) (m * n * m⁻¹ * n⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  · refine (QuotientGroup.eq_one_iff _).mp ?_
    change QuotientGroup.mk' (zpowers a) (z * m * z⁻¹ * m) = 1
    rw [map_mul, map_mul, map_mul, map_inv, hinv _ (Subgroup.mem_map_of_mem _ hm)]
    group

theorem eq_zpowers_or_eq_oddCore_of_normal
    {K : Type*} [Group K] [Finite K] {a z r₁ r₂ : K}
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) (haK : ∀ k : K, k * a = a * k) (hz2 : z ^ 2 = 1)
    (hBS : (QuotientGroup.mk z : K ⧸ CFSG.oddCore K) ∈ Subgroup.center (K ⧸ CFSG.oddCore K))
    (hT : Nat.card ↥(Subgroup.centralizer ({z} : Set K)) = 360)
    (hodd : ∀ W : Subgroup K, W ≤ Subgroup.centralizer ({z} : Set K) →
      (∀ t ∈ Subgroup.centralizer ({z} : Set K), ∀ w ∈ W, t * w * t⁻¹ ∈ W) →
      Odd (Nat.card W) → W ≤ Subgroup.zpowers a)
    (hr₁ : orderOf r₁ = 5) (hr₂ : orderOf r₂ = 5) (hr₁₂ : (r₁ * r₂) ^ 2 = z)
    (hM3 : IsPGroup 3 (CFSG.oddCore K)) (hM : Nat.card (CFSG.oddCore K) = 3 ^ 5)
    {D : Subgroup K} (hDn : D.Normal) (haD : a ∈ D) (hDM : D ≤ CFSG.oddCore K) :
    D = Subgroup.zpowers a ∨ D = CFSG.oddCore K := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : (zpowers a).Normal := Subgroup.normal_of_le_center (zpowers_le_center haK)
  obtain ⟨-, hZM, -, -, hinv, hr₁5, hr₂5, hzb⟩ :=
    brauerSuzuki_quotient ha3 ha1 haK hz2 hBS hT hodd hr₁ hr₂ hr₁₂
  by_cases hDeq : D = CFSG.oddCore K
  · exact Or.inr hDeq
  refine Or.inl ?_
  have hZD : zpowers a ≤ D := Subgroup.zpowers_le.mpr haD
  have hlt : Nat.card D < Nat.card (CFSG.oddCore K) :=
    lt_of_le_of_ne (Subgroup.card_le_of_le hDM)
      (fun h => hDeq (Subgroup.eq_of_le_of_card_ge hDM h.ge))
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hM3.to_le hDM)
  have hn4 : n ≤ 4 := by
    by_contra h
    have : 3 ^ 5 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hD81 : Nat.card D ≤ 81 := by
    rw [hn]
    calc 3 ^ n ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) hn4
      _ = 81 := by norm_num
  have haorder : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  have hZcard : Nat.card (zpowers a) = 3 := by rw [Nat.card_zpowers, haorder]
  have hDcard : Nat.card D = Nat.card ↥(D.map (QuotientGroup.mk' (zpowers a))) * 3 := by
    have h := card_eq_card_map_mk'_mul_card hZD
    rwa [hZcard] at h
  have hDb27 : Nat.card ↥(D.map (QuotientGroup.mk' (zpowers a))) ≤ 27 := by omega
  have hDb3 : IsPGroup 3 ↥(D.map (QuotientGroup.mk' (zpowers a))) :=
    IsPGroup.of_card_dvd_pow (n := n) ⟨3, by rw [← hn]; exact hDcard⟩
  have hDbn : (D.map (QuotientGroup.mk' (zpowers a))).Normal :=
    hDn.map _ (QuotientGroup.mk'_surjective _)
  have hDbM : D.map (QuotientGroup.mk' (zpowers a)) ≤
      (CFSG.oddCore K).map (QuotientGroup.mk' (zpowers a)) := Subgroup.map_mono hDM
  have hbot := eq_bot_of_inverted_card_le_twentySeven hDb3 hDb27 hr₁5 hr₂5
    (fun y hy => hDbn.conj_mem y hy _) (fun y hy => hDbn.conj_mem y hy _)
    (fun y hy => by rw [hzb]; exact hinv y (hDbM hy))
  have hDZ : D ≤ zpowers a := by
    intro d hd
    have h1 : QuotientGroup.mk' (zpowers a) d ∈ D.map (QuotientGroup.mk' (zpowers a)) :=
      Subgroup.mem_map_of_mem _ hd
    rw [hbot, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff d).mp h1
  exact le_antisymm hDZ hZD

end CFSG.Sporadic.Recognition.JankoWong
