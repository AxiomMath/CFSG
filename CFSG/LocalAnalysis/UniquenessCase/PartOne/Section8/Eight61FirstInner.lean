module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ConjRank857Final
public import CFSG.GroupTheory.FixedPointQuotientCard
import CFSG.LocalAnalysis.AGLEmbedding.EscapeRankBar
import CFSG.LocalAnalysis.UniquenessCase.UC22S213CovSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem two_le_pRank_autFixedSubgroup_conj {K : Type} [Group K] [Finite K] {k : K}
    (hk : k ^ 3 = 1) (hK : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup K)) :
    2 ≤ CFSG.Open.pRank 3 (CFSG.autFixedSubgroup (MulAut.conj k)) := by
  rcases eq_or_ne k 1 with rfl | hk1
  · have htop : CFSG.autFixedSubgroup (MulAut.conj (1 : K)) = ⊤ := by
      ext x
      simp [CFSG.mem_autFixedSubgroup]
    rw [htop]
    exact hK
  · have hkord : orderOf k = 3 := orderOf_eq_prime hk hk1
    have hfix : CFSG.autFixedSubgroup (MulAut.conj k) =
        Subgroup.centralizer ({k} : Set K) := by
      ext x
      rw [CFSG.mem_autFixedSubgroup, Subgroup.mem_centralizer_singleton_iff]
      simp only [MulAut.conj_apply]
      constructor
      · intro h
        rw [mul_inv_eq_iff_eq_mul] at h
        exact h.symm
      · intro h
        rw [mul_inv_eq_iff_eq_mul]
        exact h.symm
    have h := CFSG.AGLEmbedding.two_le_pRank_inf_centralizer_of_two_le
      (p := 3) Nat.prime_three (by decide) (A := (⊤ : Subgroup K)) hK
      (Subgroup.mem_top k) hkord
    simpa [hfix] using h

theorem exists_pow_three_eq_one_of_inner_list857
    {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hL : L ∈ calC M) (hlist : List857 (Bar2 L)) {φ : MulAut (Bar2 L)}
    (hφ : φ ∈ inner (Bar2 L)) (hφ3 : φ ^ 3 = 1) :
    ∃ k : Bar2 L, k ^ 3 = 1 ∧ MulAut.conj k = φ := by
  have hφ' : ∃ k₀ : Bar2 L, MulAut.conj k₀ = φ := by
    rw [CFSG.ComponentClassification.OuterAutomorphisms.inner] at hφ
    exact MonoidHom.mem_range.mp hφ
  obtain ⟨k₀, hk₀⟩ := hφ'
  let m : ℕ := ordCompl[3] (orderOf k₀)
  let a : ℕ := (orderOf k₀).factorization 3
  set k₁ : Bar2 L := k₀ ^ (m ^ 2) with hk₁def
  have hfin : IsOfFinOrder k₀ := isOfFinOrder_of_finite k₀
  have hn : orderOf k₀ ≠ 0 := orderOf_ne_zero_iff.mpr hfin
  have hm_not_dvd : ¬ 3 ∣ m := by
    change ¬ 3 ∣ ordCompl[3] (orderOf k₀)
    exact Nat.not_dvd_ordCompl Nat.prime_three hn
  have hm_mod : m % 3 = 1 ∨ m % 3 = 2 := by
    have hne : m % 3 ≠ 0 := fun h => hm_not_dvd (Nat.dvd_of_mod_eq_zero h)
    have hlt : m % 3 < 3 := Nat.mod_lt m (by norm_num)
    omega
  have hm_sq : m ^ 2 % 3 = 1 := by
    have hm1 : m ≡ 1 [MOD 3] ∨ m ≡ 2 [MOD 3] := by
      rcases hm_mod with h | h
      · exact Or.inl (by simpa [Nat.ModEq] using h)
      · exact Or.inr (by simpa [Nat.ModEq] using h)
    rcases hm1 with h | h
    · have hp := h.pow 2
      norm_num [Nat.ModEq] at hp
      exact hp
    · have hp := h.pow 2
      norm_num [Nat.ModEq] at hp
      exact hp
  have hφord : orderOf φ ∣ 3 := orderOf_dvd_of_pow_eq_one hφ3
  have hmod_ord : m ^ 2 % orderOf φ = 1 % orderOf φ := by
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three (orderOf φ) hφord with h | h
    · rw [h]; exact Nat.mod_one _
    · rw [h]; simpa using hm_sq
  have hpowφ : φ ^ (m ^ 2) = φ := by
    calc φ ^ (m ^ 2) = φ ^ (m ^ 2 % orderOf φ) := (pow_mod_orderOf φ (m ^ 2)).symm
      _ = φ ^ (1 % orderOf φ) := by rw [hmod_ord]
      _ = φ ^ 1 := pow_mod_orderOf φ 1
      _ = φ := pow_one φ
  have hconj_k1 : MulAut.conj k₁ = φ := by
    rw [hk₁def, map_pow, hk₀]
    exact hpowφ
  have hn_eq : 3 ^ a * m = orderOf k₀ := by
    change ordProj[3] (orderOf k₀) * ordCompl[3] (orderOf k₀) = orderOf k₀
    exact Nat.ordProj_mul_ordCompl_eq_self (orderOf k₀) 3
  have hk1_pow : k₁ ^ (3 ^ a) = 1 := by
    rw [hk₁def, ← pow_mul]
    have hmul : m ^ 2 * 3 ^ a = m * orderOf k₀ := by rw [← hn_eq]; ring
    rw [hmul, mul_comm m (orderOf k₀), pow_mul, pow_orderOf_eq_one, one_pow]
  have horder_k1 : orderOf k₁ ∣ 3 ^ a := orderOf_dvd_of_pow_eq_one hk1_pow
  have hpg : IsPGroup 3 (Subgroup.zpowers k₁) := by
    apply IsPGroup.of_card_dvd_pow (n := a)
    rw [Nat.card_zpowers]
    exact horder_k1
  have hz_conj : MulAut.conj (k₁ ^ 3) = 1 := by
    rw [map_pow, hconj_k1, hφ3]
  have hz_center : k₁ ^ 3 ∈ Subgroup.center (Bar2 L) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have h := DFunLike.congr_fun hz_conj x
    rw [MulAut.conj_apply] at h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hk1_3 : k₁ ^ 3 = 1 := by
    by_cases h3 : 3 ∣ Nat.card (Subgroup.center (Bar2 L))
    · have hcov := center_three_imp_of_list857 hL hlist h3
      obtain ⟨R, hR⟩ := hpg.exists_le_sylow
      have hk1R : k₁ ∈ (R : Subgroup (Bar2 L)) := hR (Subgroup.mem_zpowers k₁)
      exact (uc22s213_sylow_of_cover hcov R).2 k₁ hk1R
    · by_contra hne
      have hz_three : IsPGroup 3 (Subgroup.zpowers (k₁ ^ 3)) := by
        apply IsPGroup.of_card_dvd_pow (n := a)
        rw [Nat.card_zpowers]
        exact (orderOf_pow_dvd (x := k₁) 3).trans horder_k1
      have h3dvd : 3 ∣ orderOf (k₁ ^ 3) := by
        have hg : (⟨k₁ ^ 3, Subgroup.mem_zpowers (k₁ ^ 3)⟩ :
            Subgroup.zpowers (k₁ ^ 3)) ≠ 1 := by
          intro h
          exact hne (by simpa using congrArg Subtype.val h)
        simpa using IsPGroup.dvd_orderOf hz_three hg
      exact h3 (h3dvd.trans
        (Subgroup.orderOf_dvd_natCard (Subgroup.center (Bar2 L)) hz_center))
  exact ⟨k₁, hk1_3, hconj_k1⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
