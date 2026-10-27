module

public import CFSG.RankThree.GF2n.Smith81.S81E7Basic
public import CFSG.LieType.Universal.RootData

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.S81Z

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
  CFSG.RankThree.GF2n.Smith81.E7Model


theorem abs_toWeight_le_two {α : Fin (Tag.rank .E7) → ℤ} (hα : IsRoot .E7 α) (i : Fin (Tag.rank .E7)) :
    |MinData.toWeight α i| ≤ 2 := by
  revert i
  refine (forall_isRoot_iff fun γ => ∀ i, |MinData.toWeight γ i| ≤ 2).2 ?_ α hα
  decide +kernel

theorem forall_isRoot_iff₂ (P : (Fin (Tag.rank .E7) → ℤ) → (Fin (Tag.rank .E7) → ℤ) → Prop) :
    (∀ γ, IsRoot .E7 γ → ∀ δ, IsRoot .E7 δ → P γ δ) ↔
      ∀ k l : Fin 126, P ((Tag.rootCertificate .E7).root k) ((Tag.rootCertificate .E7).root l) :=
  (forall_isRoot_iff fun γ => ∀ δ, IsRoot .E7 δ → P γ δ).trans
    (forall_congr' fun k => forall_isRoot_iff (P ((Tag.rootCertificate .E7).root k)))

set_option maxRecDepth 20000 in
theorem exps_two_check : ∀ j : Fin 2, ∀ k l : Fin 126,
    0 < ht ((Tag.rootCertificate .E7).root k) → 0 < ht ((Tag.rootCertificate .E7).root l) →
    (∀ i, (3 : ℤ) ∣ MinData.toWeight ((Tag.rootCertificate .E7).root l) i
      - 2 ^ (j : ℕ) * MinData.toWeight ((Tag.rootCertificate .E7).root k) i) →
    (Tag.rootCertificate .E7).root k = (Tag.rootCertificate .E7).root l := by
  decide +kernel

theorem exps_equal_two {j : ℕ} (hj : j < 2) {α β : Fin (Tag.rank .E7) → ℤ}
    (hα : IsRoot .E7 α) (hαp : 0 < ht α) (hβ : IsRoot .E7 β) (hβp : 0 < ht β)
    (h : ∀ i, (3 : ℤ) ∣ MinData.toWeight β i - 2 ^ j * MinData.toWeight α i) : α = β := by
  have H := (forall_isRoot_iff₂ fun γ δ => 0 < ht γ → 0 < ht δ →
    (∀ i, (3 : ℤ) ∣ MinData.toWeight δ i - 2 ^ j * MinData.toWeight γ i) → γ = δ).2
    (fun k l => exps_two_check ⟨j, hj⟩ k l)
  exact H α hα β hβ hαp hβp h

theorem exps_equal_small {f j : ℕ} (hf : 3 ≤ f) (hj : j + 2 ≤ f) {α β : Fin (Tag.rank .E7) → ℤ}
    (hα : IsRoot .E7 α) (hαp : 0 < ht α) (hβ : IsRoot .E7 β) (hβp : 0 < ht β)
    (h : ∀ i, ((2 : ℤ) ^ f - 1) ∣ MinData.toWeight β i - 2 ^ j * MinData.toWeight α i) : α = β := by
  have hpow1 : (2 : ℤ) ^ (j + 2) ≤ 2 ^ f := pow_le_pow_right₀ (by norm_num) hj
  have hpow2 : (8 : ℤ) ≤ 2 ^ f := by
    calc (8 : ℤ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := pow_le_pow_right₀ (by norm_num) hf
  have e4 : (2 : ℤ) ^ (j + 2) = 4 * 2 ^ j := by ring
  have hpos : (0 : ℤ) ≤ 2 ^ j := by positivity
  have hkey : (3 : ℤ) + 2 * 2 ^ j < 2 ^ f := by linarith
  have hzero : ∀ i, MinData.toWeight β i = 2 ^ j * MinData.toWeight α i := by
    intro i
    have hb := abs_le.1 (abs_toWeight_le_two hβ i)
    have ha := abs_le.1 (abs_toWeight_le_two hα i)
    have h1 : 0 ≤ (2 : ℤ) ^ j * (2 - MinData.toWeight α i) :=
      mul_nonneg hpos (by linarith [ha.2])
    have h2 : 0 ≤ (2 : ℤ) ^ j * (MinData.toWeight α i + 2) :=
      mul_nonneg hpos (by linarith [ha.1])
    have hd : |MinData.toWeight β i - 2 ^ j * MinData.toWeight α i| < 2 ^ f - 1 := by
      rw [abs_lt]
      constructor <;> nlinarith [hb.1, hb.2]
    have := Int.eq_zero_of_abs_lt_dvd (h i) hd
    linarith
  rcases Nat.eq_zero_or_pos j with rfl | hjpos
  ·
    have hw : MinData.toWeight β = MinData.toWeight α := by
      funext i
      rw [hzero i, pow_zero, one_mul]
    exact (toWeight_injective posDef_cartan_E7 hw).symm
  ·
    exfalso
    have hw : MinData.toWeight β = (2 : ℤ) ^ j • MinData.toWeight α := by
      funext i
      rw [hzero i, Pi.smul_apply, smul_eq_mul]
    have hB := form_self_root posDef_cartan_E7 hβ
    have hA := form_self_root posDef_cartan_E7 hα
    have hsymm := form_comm posDef_cartan_E7 β α
    rw [hw, smul_dotProduct, smul_eq_mul, hA] at hsymm
    rw [hw, smul_dotProduct, smul_eq_mul] at hB
    have hx : (2 : ℤ) ≤ 2 ^ j := by
      calc (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ j := pow_le_pow_right₀ (by norm_num) (by omega)
    rw [← hsymm] at hB
    nlinarith

theorem exps_equal {f j : ℕ} (hf : 2 ≤ f) (hj : j < f) {α β : Fin (Tag.rank .E7) → ℤ}
    (hα : IsRoot .E7 α) (hαp : 0 < ht α) (hβ : IsRoot .E7 β) (hβp : 0 < ht β)
    (h : ∀ i, ((2 : ℤ) ^ f - 1) ∣ MinData.toWeight β i - 2 ^ j * MinData.toWeight α i) : α = β := by
  rcases Nat.lt_or_ge f 3 with hf3 | hf3
  ·
    have hf2 : f = 2 := by omega
    subst hf2
    have h3 : ∀ i, (3 : ℤ) ∣ MinData.toWeight β i - 2 ^ j * MinData.toWeight α i := by
      intro i
      have hi := h i
      rwa [show ((2 : ℤ) ^ 2 - 1) = 3 by norm_num] at hi
    exact exps_equal_two hj hα hαp hβ hβp h3
  · by_cases hjf : j + 2 ≤ f
    · exact exps_equal_small hf3 hjf hα hαp hβ hβp h
    ·
      have hfj : f = j + 1 := by omega
      subst hfj
      have h' : ∀ i, ((2 : ℤ) ^ (j + 1) - 1) ∣
          MinData.toWeight α i - 2 ^ 1 * MinData.toWeight β i := by
        intro i
        obtain ⟨k, hk⟩ := h i
        exact ⟨-2 * k - MinData.toWeight α i, by linear_combination (-2 : ℤ) * hk⟩
      exact (exps_equal_small (j := 1) hf3 (by omega) hβ hβp hα hαp h').symm

end CFSG.RankThree.GF2n.Smith81.S81Z
