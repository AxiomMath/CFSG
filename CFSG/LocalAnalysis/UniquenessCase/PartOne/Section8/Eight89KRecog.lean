module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KLift
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KRecogCore
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KCover3Cases
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KCover6Cases
public import Certificates.Certificate1491001
public import Certificates.Certificate1491002
public import Certificates.Certificate14984
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.UC22.F08

theorem model3_facts :
    orderOf s3 = 15 ∧ a3 ^ 2 = 1 ∧ b3 ^ 4 = 1 ∧ (a3 * b3 * b3) ^ 5 = 1 ∧ c3 ∈ center model3 :=
  Certificates.certificate1491001.2

theorem model6_facts :
    orderOf s6 = 30 ∧ a6 ^ 2 = c6 ^ 3 ∧ b6 ^ 4 = c6 ^ 3 ∧ (a6 * b6 * b6) ^ 5 = 1 ∧
      c6 ∈ center model6 :=
  Certificates.certificate1491002.2

theorem coverPG3_cases (k l : ℕ) (hk : k < 2) (hl : l < 3) :
    Finite (CoverPG 3 0 0 k l) ∧ (Nat.card (CoverPG 3 0 0 k l) < 1080 ∨
      (Nat.card (CoverPG 3 0 0 k l) ≤ 1080 ∧ ((k = 1 ∧ l = 0) ∨
        ∃ χ : CoverPG 3 0 0 k l →* Multiplicative (ZMod 6), χ ≠ 1))) :=
  coverPG3_cases_of_bounds Certificates.certificate1491001.1 k l hk hl

theorem coverPG6_cases (i j k l : ℕ) (hi : i < 2) (hj : j < 2)
    (hk : k < 2) (hl : l < 3) :
    Finite (CoverPG 6 i j k l) ∧ (Nat.card (CoverPG 6 i j k l) < 2160 ∨
      (Nat.card (CoverPG 6 i j k l) ≤ 2160 ∧ ((i = 1 ∧ j = 1 ∧ k = 1 ∧ l = 0) ∨
        ∃ χ : CoverPG 6 i j k l →* Multiplicative (ZMod 6), χ ≠ 1))) :=
  coverPG6_cases_of_bounds Certificates.certificate1491002.1 i j k l hi hj hk hl

theorem orderOf_c3 : orderOf c3 = 3 := by
  have h := model3_facts.1
  change orderOf (s3 ^ 5) = 3
  rw [orderOf_pow_of_dvd (by norm_num) (by rw [h]; norm_num), h]

theorem orderOf_e3 : orderOf e3 = 5 := by
  have h := model3_facts.1
  change orderOf (s3 ^ 3) = 5
  rw [orderOf_pow_of_dvd (by norm_num) (by rw [h]; norm_num), h]

theorem orderOf_c6 : orderOf c6 = 6 := by
  have h := model6_facts.1
  change orderOf (s6 ^ 5) = 6
  rw [orderOf_pow_of_dvd (by norm_num) (by rw [h]; norm_num), h]

theorem orderOf_e6 : orderOf e6 = 5 := by
  have h := model6_facts.1
  change orderOf (s6 ^ 6) = 5
  rw [orderOf_pow_of_dvd (by norm_num) (by rw [h]; norm_num), h]

theorem orderOf_z6 : orderOf z6 = 3 := by
  change orderOf (c6 ^ 2) = 3
  rw [orderOf_pow_of_dvd (by norm_num) (by rw [orderOf_c6]; norm_num), orderOf_c6]

theorem nonempty_mulEquiv_model3
    {K : Type} [Group K] [Finite K] (hK : IsA6Z3 K) : Nonempty (K ≃* model3) := by
  obtain ⟨hq, hZ, hA⟩ := hK
  have hn6 : CFSG.CGT.T75JM.A6Nodup := Certificates.certificate14984.2.1
  obtain ⟨i, j, k, l, hij, -, -, hk, hl, φ, hφ, hcen⟩ :=
    exists_surjective_coverHom hn6 (Or.inl rfl) hZ hA
  obtain ⟨rfl, rfl⟩ := hij rfl
  have hKcard : Nat.card K = 1080 := by rw [card_eq_of_isAlt6_quot hA, hZ]
  obtain ⟨hfin, hcases⟩ := coverPG3_cases k l hk hl
  have hge : Nat.card K ≤ Nat.card (CoverPG 3 0 0 k l) := Nat.card_le_card_of_surjective φ hφ
  rcases hcases with hlt | ⟨hle, hbase | ⟨χ, hχ⟩⟩
  · omega
  · obtain ⟨rfl, rfl⟩ := hbase
    obtain ⟨-, ha, hb, habb, hc⟩ := model3_facts
    obtain ⟨ψ, -, -, hψc, hψr⟩ := exists_coverHom 3 0 0 1 0 a3 b3 c3
      (orderOf_c3 ▸ pow_orderOf_eq_one c3) (mem_center_iff.mp hc a3) (mem_center_iff.mp hc b3)
      (by rw [mul_zero, pow_zero]; exact ha) (by rw [mul_zero, pow_zero]; exact hb)
      (pow_one c3).symm (by rw [pow_zero]; exact habb)
    have hψ : Function.Surjective ψ := by
      rw [← MonoidHom.range_eq_top, hψr, eq_top_iff, ← closure_gens3]
      refine closure_mono fun g hg => ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
      rcases hg with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    exact nonempty_mulEquiv_of_cover hq φ hφ (by omega) (PresentedGroup.of 2) hcen ψ hψ
      (by rw [hψc, orderOf_c3, hZ]) (by rw [hZ]; norm_num)
  · exact (false_of_cover_abel (Group.isPerfect_def.mp hq.1) φ hφ (by omega) χ hχ).elim

theorem nonempty_mulEquiv_model6
    {K : Type} [Group K] [Finite K] (hq : CFSG.IsQuasisimple K) (hZ : Nat.card (center K) = 6)
    (hA : IsAlt (K ⧸ center K) 6) : Nonempty (K ≃* model6) := by
  have hn6 : CFSG.CGT.T75JM.A6Nodup := Certificates.certificate14984.2.1
  obtain ⟨i, j, k, l, -, hi, hj, hk, hl, φ, hφ, hcen⟩ :=
    exists_surjective_coverHom hn6 (Or.inr rfl) hZ hA
  have hKcard : Nat.card K = 2160 := by rw [card_eq_of_isAlt6_quot hA, hZ]
  obtain ⟨hfin, hcases⟩ := coverPG6_cases i j k l hi hj hk hl
  have hge : Nat.card K ≤ Nat.card (CoverPG 6 i j k l) := Nat.card_le_card_of_surjective φ hφ
  rcases hcases with hlt | ⟨hle, hbase | ⟨χ, hχ⟩⟩
  · omega
  · obtain ⟨rfl, rfl, rfl, rfl⟩ := hbase
    obtain ⟨-, ha, hb, habb, hc⟩ := model6_facts
    obtain ⟨ψ, -, -, hψc, hψr⟩ := exists_coverHom 6 1 1 1 0 a6 b6 c6
      (orderOf_c6 ▸ pow_orderOf_eq_one c6) (mem_center_iff.mp hc a6) (mem_center_iff.mp hc b6)
      (by rw [mul_one]; exact ha) (by rw [mul_one]; exact hb)
      (pow_one c6).symm (by rw [pow_zero]; exact habb)
    have hψ : Function.Surjective ψ := by
      rw [← MonoidHom.range_eq_top, hψr, eq_top_iff, ← closure_gens6]
      refine closure_mono fun g hg => ?_
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg ⊢
      rcases hg with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    exact nonempty_mulEquiv_of_cover hq φ hφ (by omega) (PresentedGroup.of 2) hcen ψ hψ
      (by rw [hψc, orderOf_c6, hZ]) (by rw [hZ]; norm_num)
  · exact (false_of_cover_abel (Group.isPerfect_def.mp hq.1) φ hφ (by omega) χ hχ).elim

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs
