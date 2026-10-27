module

public import CFSG.RankThree.PartOne.TCX.G2.Sector
public import CFSG.RankThree.PartOne.TCX.G2.PlaneSplit
public import CFSG.RankThree.PartOne.TCX.Generator
public import CFSG.RankThree.PartOne.KLC.G2

public section

namespace CFSG.RankThree.PartOne.TCX.G2

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.TCX
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.Sec66T (exists_canonical_generator)

open CFSG.RankThree.PartOne.KLC (dvd_sub_one_or_dvd_add_one)

open CFSG.RankThree.PartOne.K128 (dvd_card_of_pRank_pos pRank_le_one_G2)


section Numeric

theorem not_dvd_sector2 {Q : ℕ} (hQ : 4 ≤ Q) : ¬ (Q - 1 ∣ Q + 1) := by
  intro h
  have h1 : ((Q - 1 : ℕ) : ℤ) ∣ (Q : ℤ) + 1 := by exact_mod_cast h
  have hc : ((Q - 1 : ℕ) : ℤ) = (Q : ℤ) - 1 := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  rw [hc] at h1
  have e : (Q : ℤ) + 1 = ((Q : ℤ) - 1) * 1 + 2 := by ring
  rw [e] at h1
  have h2 : (Q : ℤ) - 1 ∣ 2 :=
    (dvd_add_right (Dvd.intro _ rfl : (Q : ℤ) - 1 ∣ ((Q : ℤ) - 1) * 1)).1 h1
  have h4 := Int.le_of_dvd (by norm_num) h2
  have h5 : (4 : ℤ) ≤ (Q : ℤ) := by exact_mod_cast hQ
  omega

end Numeric

section Main


theorem g2_group_cases {K : Type} [Field K] [Finite K] {p f₀ : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hf₀ : 1 ≤ f₀) (hK : Nat.card K = 2 ^ (p * f₀)) {σ : K ≃+* K} (hσord : orderOf σ = p)
    (hpr : 2 ≤ CFSG.pRank p (adjointGroup Tag.G2 K))
    {x : adjointGroup Tag.G2 K} (hxp : x ^ p = 1) (hx1 : x ≠ 1)
    (hxσ : entrywiseAdjointAut Tag.G2 σ x = x) :
    (∃ R U : Subgroup (adjointGroup Tag.G2 K),
        IsElementaryAbelian p ↥R ∧ Nat.card ↥R = p ^ 2 ∧
          (∀ r ∈ R, entrywiseAdjointAut Tag.G2 σ r = r) ∧ U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧
          (∀ u ∈ U, entrywiseAdjointAut Tag.G2 σ u ∈ U) ∧
          R ≤ Subgroup.normalizer (U : Set (adjointGroup Tag.G2 K))) ∨
    ((∀ a ∈ Subgroup.centralizer ({x} : Set (adjointGroup Tag.G2 K)),
        ∀ b ∈ Subgroup.centralizer ({x} : Set (adjointGroup Tag.G2 K)), a * b = b * a) ∧
      ∃ N : ℕ, ¬ (Nat.card K - 1 ∣ N) ∧
        ∀ y ∈ Subgroup.centralizer ({x} : Set (adjointGroup Tag.G2 K)), y ^ N = 1) ∨
    SingleLayerData p (entrywiseAdjointAut Tag.G2 σ)
      (Subgroup.centralizer ({x} : Set (adjointGroup Tag.G2 K))) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 < p := by omega
  have hpf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hpf hK
  have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hdvdG : p ∣ Nat.card (adjointGroup Tag.G2 K) := dvd_card_of_pRank_pos hp (by omega)
  have hd : p ∣ Nat.card K ^ 2 - 1 := by
    by_contra hnd
    have := pRank_le_one_G2 K hp hp5 hK hpf hdvdG hnd
    omega
  have hQ1 : 1 ≤ Nat.card K := Nat.card_pos
  have hQ4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (p * f₀) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hQq : ((Nat.card K : ℕ) : ZMod p) = ((2 ^ f₀ : ℕ) : ZMod p) := by
    rw [hK, mul_comm, pow_mul]
    push_cast
    exact ZMod.pow_card _
  have hq1 : 1 ≤ 2 ^ f₀ := Nat.one_le_two_pow
  rcases dvd_sub_one_or_dvd_add_one hp hQ1 hd with h1 | h2
  ·
    left
    have h1' : ((Nat.card K - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h1
    rw [Nat.cast_sub hQ1, hQq, Nat.cast_one] at h1'
    have : (((2 ^ f₀ - 1 : ℕ)) : ZMod p) = 0 := by
      rw [Nat.cast_sub hq1, Nat.cast_one]
      exact h1'
    exact g2_plane_split hp hf₀ hK hσord ((ZMod.natCast_eq_zero_iff _ _).1 this)
  ·
    right
    have h2' : ((Nat.card K + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h2
    have hΦ : ((2 ^ f₀ : ℕ) : ZMod p) + 1 = 0 := by
      rw [← hQq]
      push_cast at h2'
      exact h2'
    obtain ⟨σ₀, hσ₀, hzp⟩ := exists_canonical_generator hpf hK hσord hp.pos rfl
    have hord₀ : orderOf σ₀ = p := by
      have h1 : Nat.card (Subgroup.zpowers σ) = p := by rw [Nat.card_zpowers, hσord]
      rw [hzp, Nat.card_zpowers] at h1
      exact h1
    have hzpG : Subgroup.zpowers (entrywiseAdjointAut Tag.G2 σ) =
        Subgroup.zpowers (entrywiseAdjointAut Tag.G2 σ₀) := zpowers_entrywiseAdjointAut_eq hzp
    have hxσ₀ : entrywiseAdjointAut Tag.G2 σ₀ x = x := fixed_of_zpowers_eq hzpG.symm hxσ
    have hβp : (entrywiseAdjointAut Tag.G2 σ₀) ^ p = 1 := by
      have h1 : σ₀ ^ p = 1 := by rw [← hord₀]; exact pow_orderOf_eq_one σ₀
      have := map_pow (entrywiseAdjointAutHom (τ := Tag.G2) (K := K)) σ₀ p
      rw [h1, map_one] at this
      exact this.symm
    rcases g2_sector_qplus hp hp5 hf₀ hK (σ := σ₀) hord₀ hσ₀ hΦ hxp hx1 hxσ₀ with ⟨hab, hexp⟩ | hlay
    · exact Or.inl ⟨hab, _, not_dvd_sector2 hQ4, hexp⟩
    · exact Or.inr (singleLayerData_of_zpowers_eq hp.pos hzpG hβp hlay)

end Main

end CFSG.RankThree.PartOne.TCX.G2
