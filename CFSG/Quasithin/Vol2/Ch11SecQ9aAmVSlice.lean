module

import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.EmptyFaithful.S1421F112
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace F112L24G2

variable {G : Type} [Group G]

private theorem eq_two_of_isL2Quot_card_sixty {f : ℕ} (hf : 1 ≤ f) {X : Type*} [Group X]
    (h : IsL2Quot f X) (hX : Nat.card X = 60) : f = 2 := by
  have hc := h.card hf
  rw [hX] at hc
  by_contra hne
  rcases Nat.lt_or_ge f 2 with h1 | h2
  · obtain rfl : f = 1 := by omega
    norm_num at hc
  · have h3 : 3 ≤ f := by omega
    have h8 : 8 ≤ 2 ^ f := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h3
    have h64 : 64 ≤ 4 ^ f := by
      calc 64 = 4 ^ 3 := by norm_num
        _ ≤ 4 ^ f := Nat.pow_le_pow_right (by norm_num) h3
    have : 8 * 63 ≤ 2 ^ f * (4 ^ f - 1) := Nat.mul_le_mul h8 (by omega)
    omega

private theorem sixty_dvd_card {L : Subgroup G} (h60 : Nat.card (oTwoQuot ↥L) = 60) :
    60 ∣ Nat.card ↥L := by
  rw [← h60, (CFSG.Open.pCore 2 ↥L).card_eq_card_quotient_mul_card_subgroup]
  exact Nat.dvd_mul_right _ _

theorem isG2_of_f112List {L1 L2 S : Subgroup G} (h : F112List L1 L2 S)
    (h₁ : Nat.card (oTwoQuot ↥L1) = 60) (h₂ : Nat.card (oTwoQuot ↥L2) = 60)
    (hb : ¬ IsShort2 L1 ∨ ¬ IsShort2 L2) :
    IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups (L1 ⊔ bigB L1 L2 S) (L2 ⊔ bigB L1 L2 S))
      (IsG2Over 2) := by
  have hb' : ¬ (IsShort2 L1 ∧ IsShort2 L2) := fun ⟨a, b⟩ => hb.elim (· a) (· b)
  rcases h with ⟨f, hf, -, ⟨-, hB1, -, hB2, -⟩ | ⟨-, ⟨e⟩, -⟩⟩ |
    ⟨f, hf, -, ⟨-, hB1, -, hB2, -⟩ | ⟨-, ⟨e⟩, -⟩⟩ |
    ⟨f, hf, hα, hq1, -, -, -⟩ | ⟨f, hf, -, hq1, -, hq2, -⟩ | ⟨a, -, -, -, hq2, -⟩ |
    ⟨f, hf, -, hq1, -, -, hq2, -⟩ | ⟨-, -, -, hq2, -⟩ | ⟨-, hq1, -⟩ | ⟨-, -, -, hq2, -⟩ |
    ⟨-, -, -, hq2, -⟩ | ⟨-, -, -, ⟨e⟩, -⟩ | ⟨-, hq1, -⟩ | ⟨-, hq1, -⟩
  · exact absurd ⟨hB1.1, hB2.1⟩ hb'
  · have h24 : Nat.card ↥(L1 ⊔ S) = 24 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    have := (sixty_dvd_card h₁).trans (Subgroup.card_dvd_of_le (le_sup_left : L1 ≤ L1 ⊔ S))
    rw [h24] at this
    norm_num at this
  · exact absurd ⟨hB1.1, hB2.1⟩ hb'
  · have h48 : Nat.card ↥(L1 ⊔ S) = 48 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm]
      simp [Nat.card_eq_fintype_card, Nat.factorial]
    have := (sixty_dvd_card h₁).trans (Subgroup.card_dvd_of_le (le_sup_left : L1 ≤ L1 ⊔ S))
    rw [h48] at this
    norm_num at this
  · obtain rfl := eq_two_of_isL2Quot_card_sixty hf hq1 h₁
    exact hα
  · have e1 := eq_two_of_isL2Quot_card_sixty (by omega) hq1 h₁
    omega
  · have := eq_two_of_isL2Quot_card_sixty (by omega) hq2 h₂
    omega
  · have e1 := eq_two_of_isL2Quot_card_sixty hf hq1 h₁
    have e2 := eq_two_of_isL2Quot_card_sixty (by omega) hq2 h₂
    omega
  · exact absurd (eq_two_of_isL2Quot_card_sixty (by norm_num) hq2 h₂) (by norm_num)
  · exact absurd (eq_two_of_isL2Quot_card_sixty le_rfl hq1 h₁) (by norm_num)
  · exact absurd (eq_two_of_isL2Quot_card_sixty le_rfl hq2 h₂) (by norm_num)
  · exact absurd (eq_two_of_isL2Quot_card_sixty le_rfl hq2 h₂) (by norm_num)
  · have := Nat.card_congr e.toEquiv
    rw [h₂, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at this
    norm_num [Nat.factorial] at this
  · exact absurd (eq_two_of_isL2Quot_card_sixty le_rfl hq1 h₁) (by norm_num)
  · exact absurd (eq_two_of_isL2Quot_card_sixty le_rfl hq1 h₁) (by norm_num)

end F112L24G2

end CFSG.Quasithin
