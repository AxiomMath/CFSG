module

public import CFSG.Quasithin.EmptyFaithful.S153E58H
public import CFSG.Quasithin.Background.D2Thirteen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S153E58

theorem input15358Solv :
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
      ∀ (H P : Subgroup (MulAut W)) (a : MulAut W) (p : ℕ), p.Prime → 3 < p →
        a ∈ H → a ≠ 1 → a ^ 2 = 1 → Nat.card ↥(commV (Subgroup.zpowers a)) = 2 ^ 2 →
        P ≤ H → (∀ h ∈ H, ∀ x ∈ P, h * x * h⁻¹ ∈ P) → IsPGroup p ↥P → (∀ x ∈ P, ∀ y ∈ P, x * y = y * x) →
        ⁅P, Subgroup.zpowers a⁆ ≠ ⊥ → Nat.card ↥⁅P, Subgroup.zpowers a⁆ = 5 := by
  intro W _ _ hW H P a p hp hp3 haH ha1 ha2 hc4 hPH hPn hPp hPab hact
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hrk : rk (commV (Subgroup.zpowers a)) = 2 := by
    rw [rk, hc4, padicValNat.prime_pow]
  have ht : a ∈ TInv H := ⟨haH, ha1, ha2, hrk.le⟩
  have hact' : ∃ y ∈ P, a * y ≠ y * a := by
    by_contra hcon
    push Not at hcon
    apply hact
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.commutator_def] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨y, hy, b, hb, rfl⟩ := hx
      have hyb : y * b = b * y := by
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
        exact (Commute.zpow_right (show Commute y a from (hcon y hy).symm) m).eq
      exact commutatorElement_eq_one_iff_mul_comm.2 hyb
    | one => rfl
    | mul x y _ _ ihx ihy => rw [ihx, ihy, one_mul]
    | inv x _ ih => rw [ih, inv_one]
  obtain ⟨hp35, -, hY⟩ := core_involution hW ht hp2 hPH hPp hPn hact'
  have hp5 : p = 5 := by omega
  obtain ⟨Y, hYmem, -, hYall, -⟩ := hY (by rw [hrk, hp5])
  have ha' : a⁻¹ = a := by rw [inv_eq_iff_mul_eq_one, ← pow_two, ha2]
  have ha2' : a * a = 1 := by rw [← pow_two, ha2]
  have hgen : ∀ y ∈ P, ∀ b ∈ Subgroup.zpowers a, ⁅y, b⁆ ∈ P ∧ a * ⁅y, b⁆ * a⁻¹ = ⁅y, b⁆⁻¹ := by
    intro y hy b hb
    rcases zpowers_involution_cases ha2 hb with hb1 | hba
    · rw [hb1]
      simp
    · rw [hba]
      refine ⟨?_, ?_⟩
      · have h1 : a * y⁻¹ * a⁻¹ ∈ P := hPn a haH y⁻¹ (P.inv_mem hy)
        have : ⁅y, a⁆ = y * (a * y⁻¹ * a⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [this]
        exact P.mul_mem hy h1
      · have e1 : a * ⁅y, a⁆ * a⁻¹ = a * y * a * y⁻¹ * (a⁻¹ * a⁻¹) := by
          simp only [commutatorElement_def]
          group
        have e2 : a⁻¹ * a⁻¹ = 1 := by rw [ha']; exact ha2'
        have e3 : ⁅y, a⁆⁻¹ = a * y * a⁻¹ * y⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e1, e2, e3, mul_one]
        rw [ha']
  have hle : ⁅P, Subgroup.zpowers a⁆ ≤ Y :=
    Subgroup.commutator_le.2 fun y hy b hb =>
      hYall _ (hgen y hy b hb).1 (by rw [(hgen y hy b hb).2])
  have hY5 : Nat.card ↥Y = 5 := by
    rw [hYmem.2.1, hrk]
  have hdvd : Nat.card ↥⁅P, Subgroup.zpowers a⁆ ∣ 5 := hY5 ▸ Subgroup.card_dvd_of_le hle
  have hne1 : Nat.card ↥⁅P, Subgroup.zpowers a⁆ ≠ 1 := fun h1 => hact (Subgroup.card_eq_one.1 h1)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).1 hdvd with h | h
  · exact absurd h hne1
  · exact h

end S153E58

end CFSG.Quasithin
