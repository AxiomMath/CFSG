module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3FinA
public import CFSG.GF2Type.Aschbacher1976Full.HSGL3Simple
public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuGL32

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup Matrix
open scoped Pointwise

private theorem s16h_normalizer_conj {H : Subgroup s16h_GL32} {g f : s16h_GL32}
    (hf : f ∈ Subgroup.normalizer H) :
    g * f * g⁻¹ ∈ Subgroup.normalizer (H.map (MulAut.conj g).toMonoidHom) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply le_antisymm
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hn
    refine Subgroup.mem_map.mpr ⟨f * m * f⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hf m).mp hm
    · change g * (f * m * f⁻¹) * g⁻¹ = (g * f * g⁻¹) * (g * m * g⁻¹) * (g * f * g⁻¹)⁻¹
      group
  · intro x hx
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hx
    refine Subgroup.mem_map.mpr ⟨g * (f⁻¹ * m * f) * g⁻¹, ?_, ?_⟩
    · refine Subgroup.mem_map.mpr ⟨f⁻¹ * m * f, ?_, rfl⟩
      refine (Subgroup.mem_normalizer_iff.mp hf (f⁻¹ * m * f)).mpr ?_
      rwa [show f * (f⁻¹ * m * f) * f⁻¹ = m from by group]
    · change (g * f * g⁻¹) * (g * (f⁻¹ * m * f) * g⁻¹) * (g * f * g⁻¹)⁻¹ = g * m * g⁻¹
      group

theorem s16h_gl3_subgroup_seven_dvd {H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))}
    (h7 : 7 ∣ Nat.card ↥H) :
    Nat.card ↥H = 168 ∨ ((Nat.card ↥H = 7 ∨ Nat.card ↥H = 21) ∧
      ∃ P : Subgroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)), P ≤ H ∧ Nat.card ↥P = 7 ∧
        ∀ x ∈ H, P.map (MulAut.conj x).toMonoidHom = P) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hdvd : Nat.card ↥H ∣ 168 := by
    rw [← CFSG.ComponentClassification.GHarris.card_GL32_gh]
    exact Subgroup.card_subgroup_dvd_card H
  obtain ⟨S⟩ : Nonempty (Sylow 7 ↥H) := inferInstance
  have hScard : Nat.card ↥(S : Subgroup ↥H) = 7 :=
    CFSG.GF2Type.Aschbacher1976Full.HS.card_sylow_seven_of_dvd_168 hdvd h7 S
  let P : Subgroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :=
    (S : Subgroup ↥H).map H.subtype
  have hPle : P ≤ H := Subgroup.map_subtype_le _
  have hPcard : Nat.card ↥P = 7 := by
    rw [show P = (S : Subgroup ↥H).map H.subtype from rfl,
      Subgroup.card_map_of_injective H.subtype_injective, hScard]
  by_cases hnorm : (S : Subgroup ↥H).Normal
  · have hHle : H ≤ Subgroup.normalizer
        (P : Set (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) := by
      have h := Subgroup.le_normalizer_map (H := (S : Subgroup ↥H)) H.subtype
      rw [Subgroup.normalizer_eq_top_iff.mpr hnorm, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at h
      exact h
    have hPH : ∀ x ∈ H, P.map (MulAut.conj x).toMonoidHom = P := by
      intro x hx
      simpa using Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHle hx)
    have hNcard : Nat.card ↥(Subgroup.normalizer
        (P : Set (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)))) = 21 :=
      CFSG.ComponentClassification.GMS78.card_normalizer_eq_of_card_eq_seven_GL32 hPcard
    have hdvd21 : Nat.card ↥H ∣ 21 := (Subgroup.card_dvd_of_le hHle).trans hNcard.dvd
    right
    refine ⟨?_, P, hPle, hPcard, hPH⟩
    obtain ⟨m, hm⟩ := h7
    have hm3 : m ∣ 3 := by
      have h : 7 * m ∣ 7 * 3 := by
        rw [hm] at hdvd21
        simpa using hdvd21
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
    have hmpos : 0 < m := Nat.pos_of_dvd_of_pos hm3 (by norm_num)
    have hmle : m ≤ 3 := Nat.le_of_dvd (by norm_num) hm3
    interval_cases m <;> omega
  · have hne : Nat.card (Sylow 7 ↥H) ≠ 1 := by
      intro h1
      haveI : Subsingleton (Sylow 7 ↥H) := (Nat.card_eq_one_iff_unique.mp h1).1
      exact hnorm (Sylow.normal_of_subsingleton S)
    have hmul : (S : Subgroup ↥H).index * 7 = Nat.card ↥H := by
      have h := (S : Subgroup ↥H).card_mul_index
      rw [hScard] at h
      omega
    have hindex24 : (S : Subgroup ↥H).index ∣ 24 := by
      have h : (S : Subgroup ↥H).index * 7 ∣ 24 * 7 := by
        rw [hmul]
        simpa [mul_comm] using hdvd
      exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h
    have hdvd24 : (Subgroup.normalizer (S : Set ↥H)).index ∣ 24 :=
      (Subgroup.index_dvd_of_le le_normalizer).trans hindex24
    have hn := Sylow.card_eq_index_normalizer S
    have hmod := card_sylow_modEq_one 7 ↥H
    rw [hn] at hmod
    have hle := Nat.le_of_dvd (by norm_num) hdvd24
    have hidx8 : (Subgroup.normalizer (S : Set ↥H)).index = 8 := by
      have hne1 : (Subgroup.normalizer (S : Set ↥H)).index ≠ 1 := by
        intro h1
        exact hne (by rw [hn, h1])
      unfold Nat.ModEq at hmod
      interval_cases hk : (Subgroup.normalizer (S : Set ↥H)).index <;>
        first | rfl | (exfalso; revert hdvd24; decide) | omega
    have h8 : 8 ∣ Nat.card ↥H := by
      have h := (Subgroup.normalizer (S : Set ↥H)).index_mul_card
      rw [hidx8] at h
      exact ⟨Nat.card ↥(Subgroup.normalizer (S : Set ↥H)), by rw [h]⟩
    left
    have h2 : 2 ∣ Nat.card ↥H := (by norm_num : (2 : ℕ) ∣ 8).trans h8
    have htop := CFSG.ComponentClassification.GMS78.eq_top_of_two_dvd_of_seven_dvd_GL32 h2 h7
    rw [htop, Subgroup.card_top]
    exact CFSG.ComponentClassification.GHarris.card_GL32_gh

theorem s16h_e3_l3_cover_three {H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))}
    (hH : 21 ∣ Nat.card ↥H) (M : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hM : M ≠ 0) :
    ∃ u : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2), ∃ h ∈ H,
      u ^ 3 = 1 ∧ h ^ 3 = 1 ∧ (u ≠ 1 ∨ h ≠ 1) ∧
        (u : Matrix (Fin 3) (Fin 3) (ZMod 2)) * M *
          (h : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose = M := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h7H : 7 ∣ Nat.card ↥H := (by norm_num : (7 : ℕ) ∣ 21).trans hH
  rcases s16h_gl3_subgroup_seven_dvd h7H with h168 | ⟨hcard, P, hPle, hPcard, hPnorm⟩
  · have htop : H = ⊤ :=
      Subgroup.eq_top_of_card_eq H (by rw [h168, CFSG.ComponentClassification.GHarris.card_GL32_gh])
    obtain ⟨p, hp, hfix⟩ := s16h_cover M hM
    obtain ⟨hu3, hf3, hfF, hpne⟩ := s16h_cov_valid p hp
    have hpne' : p.1 ≠ 1 ∨ p.2 ≠ 1 := by
      by_cases h : p.1 = 1
      · right
        intro h2
        exact hpne (Prod.ext h h2)
      · left
        exact h
    exact ⟨p.1, p.2, by rw [htop]; exact Subgroup.mem_top _, hu3, hf3, hpne', hfix⟩
  · have hH21 : Nat.card ↥H = 21 := by
      rcases hcard with h | h
      · exfalso
        rw [h] at hH
        norm_num at hH
      · exact h
    have hHle : H ≤ Subgroup.normalizer
        (P : Set (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) := by
      intro x hx
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hPnorm x hx)
    have hNcard : Nat.card ↥(Subgroup.normalizer
        (P : Set (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)))) = 21 :=
      CFSG.ComponentClassification.GMS78.card_normalizer_eq_of_card_eq_seven_GL32 hPcard
    have hHeq : H = Subgroup.normalizer
        (P : Set (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) :=
      Subgroup.eq_of_le_of_card_ge hHle (by rw [hNcard, hH21])
    let SP : Sylow 7 (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :=
      Sylow.ofCard P (by
        rw [hPcard, CFSG.ComponentClassification.GHarris.card_GL32_gh]
        decide +kernel)
    let SP0 : Sylow 7 (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :=
      Sylow.ofCard (Subgroup.zpowers s16h_C) (by
        rw [s16h_C_card_zpowers, CFSG.ComponentClassification.GHarris.card_GL32_gh]
        decide +kernel)
    obtain ⟨g, hg⟩ :=
      MulAction.exists_smul_eq (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) SP0 SP
    have hPconj : P = (Subgroup.zpowers s16h_C).map (MulAut.conj g).toMonoidHom := by
      have hSP : (SP : Subgroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) = P :=
        Sylow.coe_ofCard _ _
      have hSP0 : (SP0 : Subgroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) =
          Subgroup.zpowers s16h_C := Sylow.coe_ofCard _ _
      ext x
      rw [← hSP, ← hg]
      change x ∈ MulAut.conj g •
          (SP0 : Subgroup (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) ↔
        x ∈ (Subgroup.zpowers s16h_C).map (MulAut.conj g).toMonoidHom
      rw [hSP0, Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
      simp
    let X : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
      (((g⁻¹ : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2))).transpose
    let M' : Matrix (Fin 3) (Fin 3) (ZMod 2) := M * X
    have hgX : X * (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose = 1 := by
      change ((((g⁻¹ : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2))).transpose) *
        (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose = 1
      rw [← Matrix.transpose_mul]
      simp
    have hM' : M' ≠ 0 := by
      intro hzero
      apply hM
      calc M = M * 1 := (Matrix.mul_one M).symm
        _ = M * (X * (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose) := by rw [hgX]
        _ = (M * X) * (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose := by
              rw [Matrix.mul_assoc]
        _ = 0 := by rw [show M * X = 0 from hzero, Matrix.zero_mul]
    obtain ⟨p, hp, hfix⟩ := s16h_cover M' hM'
    obtain ⟨hu3, hf3, hfF, hpne⟩ := s16h_cov_valid p hp
    have hfN : p.2 ∈ Subgroup.normalizer (Subgroup.zpowers s16h_C : Set s16h_GL32) :=
      s16h_FSet_le_normalizer p.2 hfF
    let h : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2) := g * p.2 * g⁻¹
    have hhH : h ∈ H := by
      rw [hHeq, hPconj]
      exact s16h_normalizer_conj hfN
    have hh3 : h ^ 3 = 1 := by
      change (g * p.2 * g⁻¹) ^ 3 = 1
      have hconj : (g * p.2 * g⁻¹) ^ 3 = g * p.2 ^ 3 * g⁻¹ := by
        change ((MulAut.conj g) p.2) ^ 3 = g * p.2 ^ 3 * g⁻¹
        rw [← map_pow]
        rfl
      rw [hconj, hf3]
      group
    have hpne' : p.1 ≠ 1 ∨ h ≠ 1 := by
      by_cases h1 : p.1 = 1
      · right
        intro hh1
        apply hpne
        have h2 : p.2 = 1 := by
          calc p.2 = g⁻¹ * (g * p.2 * g⁻¹) * g := by group
            _ = g⁻¹ * h * g := by rw [show h = g * p.2 * g⁻¹ from rfl]
            _ = 1 := by rw [hh1]; group
        exact Prod.ext h1 h2
      · left
        exact h1
    have hmain : (p.1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) * M *
        (h : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose = M := by
      have htrans : (h : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose =
          X * (p.2 : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose *
            (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose := by
        change (((g * p.2 * g⁻¹ : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :
          Matrix (Fin 3) (Fin 3) (ZMod 2))).transpose =
          X * (p.2 : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose *
            (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose
        simp only [X, Units.val_mul, Matrix.transpose_mul, Matrix.mul_assoc]
      rw [htrans]
      calc (p.1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) * M *
            (X * (p.2 : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose *
              (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose)
          = ((p.1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) * M' *
              (p.2 : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose) *
                (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose := by
              simp only [M', Matrix.mul_assoc]
        _ = M' * (g : Matrix (Fin 3) (Fin 3) (ZMod 2)).transpose := by rw [hfix]
        _ = M := by
              rw [show M' = M * X from rfl, Matrix.mul_assoc, hgX, Matrix.mul_one]
    exact ⟨p.1, h, hhH, hu3, hh3, hpne', hmain⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
