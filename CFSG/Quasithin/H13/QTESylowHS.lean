module

public import CFSG.Quasithin.H13.QTESylowJ2
public import Certificates.Certificate7087
public import CFSG.RankThree.Native.HSMcLSmallData

public section

namespace CFSG.Quasithin.H13.QTESylow

open CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.K1.SporadicPerm CFSG.RankThree.Native
  CFSG.Blueprint
open scoped Pointwise

theorem hs_sylow_overgroup_orders :
    ∃ R : Subgroup NativeSporadic.HS, Nat.card R = 2 ^ 9 ∧ ∀ W : Subgroup NativeSporadic.HS,
      R ≤ W → ∃ s : ℕ, (s = 1 ∨ 3 ∣ s) ∧ Nat.card W = 2 ^ 9 * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow 2 NativeSporadic.HS))
  have hmem := Certificates.certificate7087 T
  refine ⟨T, ?_, fun W hW => ?_⟩
  · obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp T.isPGroup'
    have h := hmem T le_rfl
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h | h | h
    · rw [h]
      norm_num
    all_goals
      exfalso
      have h3 : 3 ∣ 2 ^ k := by
        rw [← hk, h]
        norm_num
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  · have h := hmem W hW
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h | h | h
    · exact ⟨1, Or.inl rfl, by rw [h]; norm_num⟩
    · exact ⟨3, Or.inr dvd_rfl, by rw [h]; norm_num⟩
    · exact ⟨15, Or.inr (by norm_num), by rw [h]; norm_num⟩
    · exact ⟨21, Or.inr (by norm_num), by rw [h]; norm_num⟩
    · exact ⟨86625, Or.inr (by norm_num), by rw [h]; norm_num⟩

theorem hs_three_free_sylow_product_rigidity
    {K : Type*} [Group K] [Finite K]
    (e : K ≃* NativeSporadic.HS) (S : Sylow 2 K) :
    (∀ A : Subgroup K, ¬ 3 ∣ Nat.card A →
      (A : Set K) * (S : Set K) = (S : Set K) * (A : Set K) → A ≤ S) ∧
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ P : Subgroup K, IsPGroup p P → P ≠ ⊥ →
      (P : Set K) * (S : Set K) ≠ (S : Set K) * (P : Set K) :=
  three_free_rigidity_of_orders (@overgroup_orders_of_mulEquiv K NativeSporadic.HS inferInstance
    inferInstance e 9 hs_sylow_overgroup_orders) S

theorem j2_hs_three_free_sylow_product_rigidity
    {K : Type*} [Group K] [Finite K]
    (hK : Nonempty (K ≃* NativeSporadic.J2) ∨ Nonempty (K ≃* NativeSporadic.HS))
    (S : Sylow 2 K) :
    (∀ A : Subgroup K, ¬ 3 ∣ Nat.card A →
      (A : Set K) * (S : Set K) = (S : Set K) * (A : Set K) → A ≤ S) ∧
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ P : Subgroup K, IsPGroup p P → P ≠ ⊥ →
      (P : Set K) * (S : Set K) ≠ (S : Set K) * (P : Set K) := by
  rcases hK with h | h
  · obtain ⟨e⟩ := h
    exact j2_three_free_sylow_product_rigidity e S
  · obtain ⟨e⟩ := h
    exact hs_three_free_sylow_product_rigidity e S

end CFSG.Quasithin.H13.QTESylow
