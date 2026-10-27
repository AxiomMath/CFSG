module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

@[expose] def HeSubO2_kz : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.Carrier .He) →
    ∀ U : Subgroup Q, Nat.card U = 2 ^ 10 * 3 ^ 2 →
      ∃ Y : Subgroup Q, Y ≤ U ∧ (Y.subgroupOf U).Normal ∧ Nat.card Y = 2 ^ 6 * 3 ∧
        Y ≤ oTwoUpper U

theorem card_dvd_two_pow_ten_of_isPGroup_kz {Q : Type} [Group Q] [Finite Q]
    (hQ : Nat.card Q = 4030387200) (R : Subgroup Q) (hR : IsPGroup 2 R) :
    Nat.card R ∣ 2 ^ 10 := by
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  have hdvd : Nat.card R ∣ Nat.card Q := Subgroup.card_subgroup_dvd_card R
  rw [hQ, hk] at hdvd
  have hodd : Nat.Coprime (2 ^ k) 3935925 := Nat.Coprime.pow_left k (by norm_num)
  have h2 : 2 ^ k ∣ 2 ^ 10 * 3935925 := by
    rw [show (4030387200 : ℕ) = 2 ^ 10 * 3935925 by norm_num] at hdvd
    exact hdvd
  rw [hk]
  exact hodd.dvd_of_dvd_mul_right h2

theorem mem_sup_of_le_normalizer_he_kz {Q : Type} [Group Q] {X S : Subgroup Q}
    (hS : S ≤ Subgroup.normalizer (X : Set Q)) {x : Q} :
    x ∈ X ⊔ S ↔ ∃ y ∈ X, ∃ z ∈ S, y * z = x := by
  have hconj : ∀ z ∈ S, ∀ y ∈ X, z * y * z⁻¹ ∈ X := fun z hz y hy =>
    (Subgroup.mem_normalizer_iff.mp (hS hz) y).mp hy
  constructor
  · intro hx
    rw [Subgroup.sup_eq_closure] at hx
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
    · rintro x (hx | hx)
      · exact ⟨x, hx, 1, S.one_mem, by simp⟩
      · exact ⟨1, X.one_mem, x, hx, by simp⟩
    · exact ⟨1, X.one_mem, 1, S.one_mem, by simp⟩
    · rintro _ _ _ _ ⟨y₁, hy₁, z₁, hz₁, rfl⟩ ⟨y₂, hy₂, z₂, hz₂, rfl⟩
      exact ⟨y₁ * (z₁ * y₂ * z₁⁻¹), X.mul_mem hy₁ (hconj z₁ hz₁ y₂ hy₂), z₁ * z₂,
        S.mul_mem hz₁ hz₂, by group⟩
    · rintro _ _ ⟨y, hy, z, hz, rfl⟩
      exact ⟨z⁻¹ * y⁻¹ * z, by simpa using hconj z⁻¹ (S.inv_mem hz) y⁻¹ (X.inv_mem hy), z⁻¹,
        S.inv_mem hz, by group⟩
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact Subgroup.mul_mem_sup hy hz

theorem card_le_of_two_pow_dvd_nine_mul_kz {b a : ℕ} (h : 2 ^ b ∣ 9 * 2 ^ a) : 2 ^ b ≤ 2 ^ a := by
  have hc : Nat.Coprime (2 ^ b) 9 := Nat.Coprime.pow_left b (by norm_num)
  exact Nat.le_of_dvd (by positivity) (hc.dvd_of_dvd_mul_left h)

end CFSG.Quasithin.H13
