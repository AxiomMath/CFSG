module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432SylowCenter
public import CFSG.RankThree.PartTwo.Sec4.RonanK432Sylow

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

theorem exists_unit_ne_one_ne_neg_one_of_four_le {K : Type} [Field K] [Finite K]
    (h : 4 ≤ Nat.card K) : ∃ μ : Kˣ, (μ : K) ≠ 1 ∧ (μ : K) ≠ -1 := by
  classical
  haveI := Fintype.ofFinite K
  by_contra hcon
  push Not at hcon
  have hsub : (Finset.univ : Finset K) ⊆ {0, 1, -1} := by
    intro x _
    by_cases hx : x = 0
    · simp [hx]
    · by_cases hx1 : x = 1
      · simp [hx1]
      · have := hcon (Units.mk0 x hx) hx1
        simp only [Units.val_mk0] at this
        simp [this]
  have hle : Fintype.card K ≤ 3 :=
    Finset.card_univ (α := K) ▸ (Finset.card_le_card hsub).trans Finset.card_le_three
  rw [Nat.card_eq_fintype_card] at h
  omega

theorem card_sylow_three_eq {S : Type} [Group S] [Finite S] (P : Sylow 3 S) {n : ℕ}
    (h1 : 3 ^ n ∣ Nat.card S) (h2 : ¬ 3 ^ (n + 1) ∣ Nat.card S) : Nat.card P = 3 ^ n := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : Nat.card S ≠ 0 := Nat.card_pos.ne'
  have a := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).mp h1
  have b : ¬ n + 1 ≤ (Nat.card S).factorization 3 := fun h =>
    h2 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).mpr h)
  rw [Sylow.card_eq_multiplicity P]
  congr 1
  omega

theorem listRow_of_sylow_center_field {S : Type} [Group S] [Finite S] {K : Type} [Field K]
    [Finite K] (hK : 4 ≤ Nat.card K) (φ : Multiplicative K →* S) (hφ : Function.Injective φ)
    (n : ℕ) (Q : Subgroup S) (hQ : Nat.card Q = 3 ^ n) (hS : ¬ 3 ^ (n + 1) ∣ Nat.card S)
    (hZ : ∀ u ∈ Q, (∀ q ∈ Q, q * u = u * q) → u ∈ φ.range)
    (hmul : ∀ μ : Kˣ, ∃ g : S, ∀ c : K,
      g * φ (Multiplicative.ofAdd c) * g⁻¹ = φ (Multiplicative.ofAdd ((μ : K) * c))) :
    ListRow S := by
  refine listRow_of_sylow_center n Q hQ hS ?_
  intro u hu ho hc
  obtain ⟨c, rfl⟩ := hZ u hu hc
  obtain ⟨μ, hμ1, hμ2⟩ := exists_unit_ne_one_ne_neg_one_of_four_le hK
  obtain ⟨g, hg⟩ := hmul μ
  have hg' : g * φ c * g⁻¹ = φ (Multiplicative.ofAdd ((μ : K) * Multiplicative.toAdd c)) :=
    hg (Multiplicative.toAdd c)
  have h3 : (φ c) ^ 3 = 1 := by
    rw [← ho]
    exact pow_orderOf_eq_one _
  have hc1 : c ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at ho
    omega
  have hc0 : Multiplicative.toAdd c ≠ 0 := fun h => hc1 (toAdd_eq_zero.mp h)
  refine ⟨g, ?_, ?_⟩
  · rw [hg']
    exact (((Commute.all (Multiplicative.ofAdd ((μ : K) * Multiplicative.toAdd c)) c).map φ)).eq
  · rw [hg']
    intro hmem
    rcases mem_zpowers_cases_of_pow_three h3 hmem with h | h | h
    · have h' := hφ (h.trans (map_one φ).symm)
      have h'' : (μ : K) * Multiplicative.toAdd c = 0 := ofAdd_eq_one.mp h'
      rcases mul_eq_zero.mp h'' with h4 | h4
      · exact μ.ne_zero h4
      · exact hc0 h4
    · have h' := hφ h
      have h'' : (μ : K) * Multiplicative.toAdd c = Multiplicative.toAdd c := by
        simpa using congrArg Multiplicative.toAdd h'
      have : ((μ : K) - 1) * Multiplicative.toAdd c = 0 := by
        rw [sub_mul, h'', one_mul, sub_self]
      rcases mul_eq_zero.mp this with h4 | h4
      · exact hμ1 (sub_eq_zero.mp h4)
      · exact hc0 h4
    · have h' := hφ (h.trans (map_inv φ c).symm)
      have h'' : (μ : K) * Multiplicative.toAdd c = -Multiplicative.toAdd c := by
        simpa using congrArg Multiplicative.toAdd h'
      have : ((μ : K) + 1) * Multiplicative.toAdd c = 0 := by
        rw [add_mul, h'', one_mul, neg_add_cancel]
      rcases mul_eq_zero.mp this with h4 | h4
      · exact hμ2 (eq_neg_of_add_eq_zero_left h4)
      · exact hc0 h4

end CFSG.RankThree.PartTwo.Sec4.RonanK432
