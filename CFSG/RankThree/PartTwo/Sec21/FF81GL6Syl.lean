module

public import CFSG.RankThree.PartTwo.Sec21.FF81GL6Defs

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.GL6

private theorem syl_exists_P (X B : Subgroup G6) (hBX : B ≤ X) (hB : Nat.card B = 27)
    (h81 : 81 ∣ Nat.card X) : ∃ P : Subgroup G6, Nat.card P = 81 ∧ B ≤ P ∧ P ≤ X := by
  have hBX' : Nat.card (B.subgroupOf X) = 3 ^ 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBX).toEquiv).trans (hB.trans (by norm_num))
  have hdvd : 3 ^ (3 + 1) ∣ Nat.card X := by
    rw [show (3 : ℕ) ^ (3 + 1) = 81 by norm_num]
    exact h81
  obtain ⟨K, hKc, hBK⟩ := Sylow.exists_subgroup_card_pow_succ hdvd hBX'
  refine ⟨K.map X.subtype, ?_, ?_, ?_⟩
  · exact (Subgroup.card_map_of_injective X.subtype_injective).trans (hKc.trans (by norm_num))
  · intro b hb
    have hbX : b ∈ X := hBX hb
    have hmem : (⟨b, hbX⟩ : X) ∈ B.subgroupOf X := Subgroup.mem_subgroupOf.mpr hb
    exact Subgroup.mem_map.mpr ⟨⟨b, hbX⟩, hBK hmem, rfl⟩
  · intro x hx
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hx
    exact y.2

private theorem syl_normal_subgroupOf (P B : Subgroup G6) (hBP : B ≤ P) (hB : Nat.card B = 27)
    (hP : Nat.card P = 81) : (B.subgroupOf P).Normal := by
  have hidx : (B.subgroupOf P).index = 3 := by
    have h := Subgroup.card_mul_index (B.subgroupOf P)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBP).toEquiv, hB, hP] at h
    omega
  have hmin : (Nat.card P).minFac = 3 := by
    rw [hP]
    norm_num
  exact Subgroup.normal_of_index_eq_minFac_card (by rw [hidx, hmin])

private theorem syl_mem_normalizer (P B : Subgroup G6) (hBP : B ≤ P) (hB : Nat.card B = 27)
    (hP : Nat.card P = 81) {σ : G6} (hσ : σ ∈ P) :
    σ ∈ Subgroup.normalizer (B : Set G6) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hBP).mp
    (syl_normal_subgroupOf P B hBP hB hP) hσ

private theorem syl_sq_comm {σ u : G6} (hc : σ * u * σ⁻¹ = u⁻¹) :
    σ ^ 2 * u = u * σ ^ 2 := by
  have h2 : σ * (σ * u * σ⁻¹) * σ⁻¹ = u := by
    rw [hc]
    calc σ * u⁻¹ * σ⁻¹ = (σ * u * σ⁻¹)⁻¹ := by group
      _ = u := by rw [hc, inv_inv]
  calc σ ^ 2 * u = (σ * (σ * u * σ⁻¹) * σ⁻¹) * σ ^ 2 := by rw [sq σ]; group
    _ = u * σ ^ 2 := by rw [h2]

theorem exists_sigma_of (hK : Nat.card K0 = 2160) (hB : Nat.card B3 = 27) (hBK : B3 ≤ K0)
    (ho : orderOf u0 = 3) (X : Subgroup G6) (hX : X ⊓ Subgroup.centralizer {u0} = K0)
    (h81 : 81 ∣ Nat.card X) :
    ∃ σ ∈ X, σ ∈ Subgroup.normalizer (B3 : Set G6) ∧
      σ * u0 * σ⁻¹ ≠ u0 ∧ σ * u0 * σ⁻¹ ≠ u0⁻¹ := by
  have hK0X : K0 ≤ X := by
    rw [← hX]
    exact inf_le_left
  have hK0C : K0 ≤ Subgroup.centralizer {u0} := by
    rw [← hX]
    exact inf_le_right
  have hBX : B3 ≤ X := hBK.trans hK0X
  obtain ⟨P, hP, hBP, hPX⟩ := syl_exists_P X B3 hBX hB h81
  have hne : B3 ≠ P := by
    intro h
    rw [← h, hB] at hP
    norm_num at hP
  obtain ⟨σ, hσP, hσB⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hBP hne)
  have hσX : σ ∈ X := hPX hσP
  have hσN : σ ∈ Subgroup.normalizer (B3 : Set G6) := syl_mem_normalizer P B3 hBP hB hP hσP
  refine ⟨σ, hσX, hσN, ?_, ?_⟩
  ·
    intro hc
    have hcC : σ ∈ Subgroup.centralizer {u0} :=
      Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hc)
    have hσK0 : σ ∈ K0 := by
      rw [← hX]
      exact Subgroup.mem_inf.mpr ⟨hσX, hcC⟩
    have hBH : B3 ≤ P ⊓ K0 := le_inf hBP hBK
    have hd1 : Nat.card ↥(P ⊓ K0) ∣ 81 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : P ⊓ K0 ≤ P)
      rwa [hP] at this
    have hd2 : Nat.card ↥(P ⊓ K0) ∣ 2160 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : P ⊓ K0 ≤ K0)
      rwa [hK] at this
    have hd : Nat.card ↥(P ⊓ K0) ∣ 27 := (Nat.dvd_gcd hd1 hd2).trans (by norm_num)
    have hle : Nat.card ↥(P ⊓ K0) ≤ Nat.card B3 := by
      rw [hB]
      exact Nat.le_of_dvd (by norm_num) hd
    have heq : B3 = P ⊓ K0 := Subgroup.eq_of_le_of_card_ge hBH hle
    have hσH : σ ∈ P ⊓ K0 := Subgroup.mem_inf.mpr ⟨hσP, hσK0⟩
    rw [← heq] at hσH
    exact hσB hσH
  ·
    intro hc
    have hsq : σ ^ 2 * u0 = u0 * σ ^ 2 := syl_sq_comm hc
    have hσ2K0 : σ ^ 2 ∈ K0 := by
      rw [← hX]
      exact Subgroup.mem_inf.mpr
        ⟨X.pow_mem hσX 2, Subgroup.mem_centralizer_singleton_iff.mpr hsq⟩
    have h81σ : σ ^ 81 = 1 := by
      have h := congrArg Subtype.val (pow_card_eq_one' (G := ↥P) (x := ⟨σ, hσP⟩))
      rw [hP] at h
      simpa using h
    have hσe : σ = (σ ^ 2) ^ 41 := by
      rw [← pow_mul, show 2 * 41 = 81 + 1 from rfl, pow_succ, h81σ, one_mul]
    have hσK0 : σ ∈ K0 := by
      rw [hσe]
      exact K0.pow_mem hσ2K0 41
    have hcomm : σ * u0 = u0 * σ := Subgroup.mem_centralizer_singleton_iff.mp (hK0C hσK0)
    have hu : u0 = u0⁻¹ := (mul_inv_eq_iff_eq_mul.mpr hcomm).symm.trans hc
    have h2 : u0 ^ 2 = 1 := by
      calc u0 ^ 2 = u0 * u0 := sq u0
        _ = u0 * u0⁻¹ := by rw [← hu]
        _ = 1 := mul_inv_cancel u0
    have h3 := orderOf_dvd_of_pow_eq_one h2
    rw [ho] at h3
    norm_num at h3

end CFSG.RankThree.PartTwo.Sec21.FF81.GL6
