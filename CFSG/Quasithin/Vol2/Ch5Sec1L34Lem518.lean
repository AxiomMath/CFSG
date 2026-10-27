module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs518
public import CFSG.Quasithin.Vol2.Ch5Sec1Borel
public import CFSG.Quasithin.Vol2.Ch5StatementsB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

section General

variable {G : Type} [Group G] [Finite G]

theorem le_of_dvd_card_inf {D X : Subgroup G} (h : Nat.card D ∣ Nat.card ↥(D ⊓ X)) : D ≤ X := by
  have hle : Nat.card D ≤ Nat.card ↥(D ⊓ X) := Nat.le_of_dvd Nat.card_pos h
  have heq : D ⊓ X = D := Subgroup.eq_of_le_of_card_ge inf_le_left hle
  exact heq ▸ inf_le_right

omit [Finite G] in
theorem dvd_card_inf_of_le {D X P : Subgroup G} {p : ℕ} (hPD : P ≤ D) (hPX : P ≤ X)
    (hP : Nat.card P = p) : p ∣ Nat.card ↥(D ⊓ X) :=
  hP ▸ Subgroup.card_dvd_of_le (le_inf hPD hPX)

theorem exists_le_card_eq_prime {D : Subgroup G} {p : ℕ} (hp : p.Prime) (hpD : p ∣ Nat.card D) :
    ∃ P : Subgroup G, P ≤ D ∧ Nat.card P = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) p hpD
  refine ⟨Subgroup.zpowers (x : G), (Subgroup.zpowers_le (G := G)).mpr x.2, ?_⟩
  rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]

end General

theorem stmt5_1_18_of_inputs (hF : L2TorusFact) (h515 : Stmt5_1_15) (h5114 : Stmt5_1_14_first)
    (h517 : Stmt5_1_17) (hDL : Stmt5_1_18_DL) (hD5 : Stmt5_1_18_D5) : Stmt5_1_18 := by
  intro G _ _ T M L V H B D n hyp hN hV hK D₃ hD₃ h3 hD₃M
  have h : Hyp5_1_14 G T M L V H B D n := ⟨hyp, hN, hV, hK⟩
  have hev : Even n := h517 G T M L V H B D n hyp hN hV hK
  obtain ⟨-, hcardD⟩ := hyp.toHyp5_0_1.isCyclic_card_of_isHall hF hN.2.1
  set Mp := Subgroup.normalizer (oTwoUpper H : Set G) with hMp
  have h3D : 3 ∣ Nat.card ↥(D ⊓ Mp) := dvd_card_inf_of_le hD₃ hD₃M h3
  have hB : D₃ = B := by
    by_contra hne
    have hDM := hDL G T M L V H B D n h hev D₃ hD₃ h3 hD₃M hne
    have hn2 : n ≠ 2 := by
      rintro rfl
      exact hDM (le_of_dvd_card_inf (by rw [hcardD]; exact h3D))
    have h15 : n = 4 → (∀ D₅ : Subgroup G, D₅ ≤ D → Nat.card D₅ = 5 → D₅ ≤ Mp) → False := by
      rintro rfl hD₅
      obtain ⟨D₅, hD₅D, hD₅5⟩ := exists_le_card_eq_prime (by norm_num : Nat.Prime 5)
        (by rw [hcardD]; norm_num)
      have h5D := dvd_card_inf_of_le hD₅D (hD₅ D₅ hD₅D hD₅5) hD₅5
      exact hDM (le_of_dvd_card_inf (by
        rw [hcardD, show 2 ^ 4 - 1 = 3 * 5 by norm_num]
        exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3D h5D))
    rcases h515 G T M L V H B D n hyp hN hV hK with hD | ⟨h2, -⟩ | ⟨h24, -⟩ |
        ⟨h48, -, hDm⟩
    · exact hDM hD
    · exact hn2 h2
    · rcases h24 with h2 | rfl
      · exact hn2 h2
      · exact h15 rfl fun D₅ hD₅D hD₅5 =>
          hD5 G T M L V H B D 4 h (Or.inl rfl) D₃ hD₃ h3 hD₃M hne hDM D₅ hD₅D hD₅5
    · rcases h48 with rfl | rfl
      · exact h15 rfl fun D₅ hD₅D hD₅5 => hDm D₅ hD₅D (by rw [hD₅5]; norm_num)
      · obtain ⟨D₅, hD₅D, hD₅5⟩ := exists_le_card_eq_prime (by norm_num : Nat.Prime 5)
          (by rw [hcardD]; norm_num)
        obtain ⟨D₁₇, hD₁₇D, hD₁₇⟩ := exists_le_card_eq_prime (by norm_num : Nat.Prime 17)
          (by rw [hcardD]; norm_num)
        have h5D := dvd_card_inf_of_le hD₅D
          (hD5 G T M L V H B D 8 h (Or.inr rfl) D₃ hD₃ h3 hD₃M hne hDM D₅ hD₅D hD₅5) hD₅5
        have h17D := dvd_card_inf_of_le hD₁₇D (hDm D₁₇ hD₁₇D (by rw [hD₁₇]; norm_num)) hD₁₇
        exact hDM (le_of_dvd_card_inf (by
          rw [hcardD, show 2 ^ 8 - 1 = 3 * 5 * 17 by norm_num]
          exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num)
            (Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3D h5D) h17D))
  refine ⟨hB, ?_⟩
  have hZH : ⁅quasithinOmegaOneCenter T, H⁆ = ⊥ :=
    (h5114 G T M L V H B D n hyp hN hV hK).2.1.1
  have hBH : B ≤ H := hN.1.1.trans inf_le_right
  rw [hB, eq_bot_iff, ← hZH]
  exact Subgroup.commutator_mono le_rfl hBH

end CFSG.Quasithin.H13
