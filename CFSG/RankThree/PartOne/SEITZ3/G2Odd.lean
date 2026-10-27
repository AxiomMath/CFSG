module

public import CFSG.RankThree.PartOne.SEITZ3.MaxDefs
public import CFSG.RankThree.PartOne.K128.G2Syl
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartOne.SEITZ3

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open TauCeti
  CFSG.Timmesfeld.ExceptionalOrders CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.K1214 CFSG.ComponentClassification.UnbalancedCatalog
open CFSG.RankThree.PartOne.Census3 (IsoLie)

section Sylow

theorem pRank_le_one_G2_odd
    (K : Type) [Field K] [Finite K]
    (hK : Odd (Nat.card K)) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpQ : ¬ p ∣ Nat.card K)
    (hdvd : p ∣ Nat.card (adjointGroup .G2 K)) (hnd : ¬ p ∣ Nat.card K ^ 2 - 1) :
    CFSG.pRank p (adjointGroup .G2 K) ≤ 1 := by
  have hQ : 2 ≤ Nat.card K := Finite.one_lt_card
  have hy : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ (by omega)
  rw [card_adjointGroup_G2] at hdvd
  have h6 : p ∣ Nat.card K ^ 6 - 1 := by
    unfold ordG2 at hdvd
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact absurd (hp.dvd_of_dvd_pow h) hpQ
      · exact h
    · exact absurd h hnd
  have hfac : Nat.card K ^ 6 - 1 =
      (Nat.card K ^ 2 - 1) * ((Nat.card K ^ 2) ^ 2 + Nat.card K ^ 2 + 1) := by
    have := CFSG.RankThree.PartOne.K128.pow3_sub_one (Nat.card K ^ 2) hy
    rwa [← pow_mul] at this
  rw [hfac] at h6
  have hΦ : p ∣ (Nat.card K ^ 2) ^ 2 + Nat.card K ^ 2 + 1 :=
    ((Nat.Prime.dvd_mul hp).1 h6).resolve_left hnd
  have hle : Nat.card K ≤ Nat.card K ^ 2 := Nat.le_self_pow (by norm_num) _
  have hΦfac : (Nat.card K ^ 2) ^ 2 + Nat.card K ^ 2 + 1 =
      (Nat.card K ^ 2 + Nat.card K + 1) * (Nat.card K ^ 2 - Nat.card K + 1) := by
    zify [hle]
    ring
  rw [hΦfac] at hΦ
  rcases (Nat.Prime.dvd_mul hp).1 hΦ with h | h
  · obtain ⟨T₀, -, -, -, hcyc, -⟩ := odd_G2_cyclotomic_three_six_tori_and_prime_centralizers K hK 1
      (Or.inr rfl) (Nat.card K ^ 2 + Nat.card K + 1) (by push_cast; ring) hp (by omega) h
    exact CFSG.RankThree.PartOne.K128.pRank_le_one_of_cyclic_pSubgroups hp hcyc
  · obtain ⟨T₀, -, -, -, hcyc, -⟩ := odd_G2_cyclotomic_three_six_tori_and_prime_centralizers K hK
      (-1) (Or.inl rfl) (Nat.card K ^ 2 - Nat.card K + 1) (by push_cast [Nat.cast_sub hle]; ring) hp
      (by omega) h
    exact CFSG.RankThree.PartOne.K128.pRank_le_one_of_cyclic_pSubgroups hp hcyc

end Sylow

section Generation

variable {K : Type} [Field K]

theorem mem_center_of_a1a1Hom_eq_one
    {A B : Matrix.SpecialLinearGroup (Fin 2) K}
    (h : a1a1Hom K (A, B) = 1) :
    A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) ∧
      B ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
  have hprod : rootSL2 .G2 K g2a A * rootSL2 .G2 K g2v B = 1 := by
    have h' : ((a1a1Hom K (A, B) : adjointGroup .G2 K) : ModGL .G2 K) = 1 := by
      rw [h]; rfl
    rwa [a1a1Hom_apply] at h'
  have hAinv : rootSL2 .G2 K g2a A = (rootSL2 .G2 K g2v B)⁻¹ := eq_inv_of_mul_eq_one_left hprod
  have hBinv : rootSL2 .G2 K g2v B = (rootSL2 .G2 K g2a A)⁻¹ := eq_inv_of_mul_eq_one_right hprod
  constructor
  · rw [Subgroup.mem_center_iff]
    intro A'
    apply rootSL2_injective_of_field (τ := .G2) (K := K) g2a
    rw [map_mul, map_mul, hAinv]
    have hc := rootSL2_g2v_mul_rootSL2_g2a (L := K) B A'
    calc rootSL2 .G2 K g2a A' * (rootSL2 .G2 K g2v B)⁻¹
        = (rootSL2 .G2 K g2v B)⁻¹ * (rootSL2 .G2 K g2v B * rootSL2 .G2 K g2a A') *
            (rootSL2 .G2 K g2v B)⁻¹ := by group
      _ = (rootSL2 .G2 K g2v B)⁻¹ * (rootSL2 .G2 K g2a A' * rootSL2 .G2 K g2v B) *
            (rootSL2 .G2 K g2v B)⁻¹ := by rw [hc]
      _ = (rootSL2 .G2 K g2v B)⁻¹ * rootSL2 .G2 K g2a A' := by group
  · rw [Subgroup.mem_center_iff]
    intro B'
    apply rootSL2_injective_of_field (τ := .G2) (K := K) g2v
    rw [map_mul, map_mul, hBinv]
    have hc := rootSL2_g2v_mul_rootSL2_g2a (L := K) B' A
    calc rootSL2 .G2 K g2v B' * (rootSL2 .G2 K g2a A)⁻¹
        = (rootSL2 .G2 K g2a A)⁻¹ * (rootSL2 .G2 K g2a A * rootSL2 .G2 K g2v B') *
            (rootSL2 .G2 K g2a A)⁻¹ := by group
      _ = (rootSL2 .G2 K g2a A)⁻¹ * (rootSL2 .G2 K g2v B' * rootSL2 .G2 K g2a A) *
            (rootSL2 .G2 K g2a A)⁻¹ := by rw [← hc]
      _ = (rootSL2 .G2 K g2a A)⁻¹ * rootSL2 .G2 K g2v B' := by group

theorem sq_eq_one_of_mem_center {A : Matrix.SpecialLinearGroup (Fin 2) K}
    (hA : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) : A ^ 2 = 1 := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  have h2 : r ^ 2 = 1 := by simpa using hr
  ext i j
  have : ((A ^ 2 : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (Matrix.scalar (Fin 2) r) ^ 2 := by
    rw [Matrix.SpecialLinearGroup.coe_pow, hrA]
  rw [this, ← map_pow, h2, map_one]
  rfl

theorem sq_eq_one_of_a1a1Hom_eq_one
    {x : Matrix.SpecialLinearGroup (Fin 2) K ×
    Matrix.SpecialLinearGroup (Fin 2) K} (h : a1a1Hom K x = 1) : x ^ 2 = 1 := by
  obtain ⟨A, B⟩ := x
  obtain ⟨hA, hB⟩ := mem_center_of_a1a1Hom_eq_one h
  show (A, B) ^ 2 = 1
  have hab : (A, B) ^ 2 = (A ^ 2, B ^ 2) := rfl
  rw [hab, sq_eq_one_of_mem_center hA, sq_eq_one_of_mem_center hB]
  rfl

end Generation

end CFSG.RankThree.PartOne.SEITZ3
