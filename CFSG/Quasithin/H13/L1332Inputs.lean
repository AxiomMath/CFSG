module

public import CFSG.Quasithin.H13.FiveMenu
import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

@[expose] def FiveQuotientOddIndexSolvable : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], QT13Five Q → ∀ X : Subgroup Q, ¬ 2 ∣ X.index → X ≠ ⊤ →
    Group.IsSolvable X

@[expose] def L32NoIrrFour : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) → Nat.card V = 2 ^ 4 →
    ∀ H : Subgroup (MulAut V), Nonempty (↥H ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) →
      ∃ W : Subgroup V, W ≠ ⊥ ∧ W ≠ ⊤ ∧ ∀ h ∈ H, ∀ w ∈ W, (h : MulAut V) w ∈ W

theorem card_sl_zmod_two (n : ℕ) [NeZero n] :
    Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = ∏ i : Fin n, (2 ^ n - 2 ^ (i : ℕ)) := by
  have h := Matrix.card_SL_mul_card_units (n := Fin n) (R := ZMod 2)
  have hu : Nat.card (ZMod 2)ˣ = 1 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  rw [hu, mul_one, Matrix.card_GL_field] at h
  rw [h, ZMod.card]

theorem card_sl_four_zmod_two : Nat.card (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) = 20160 := by
  rw [card_sl_zmod_two]
  decide

theorem card_sl_five_zmod_two :
    Nat.card (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) = 9999360 := by
  rw [card_sl_zmod_two]
  decide

theorem card_sl_three_zmod_two : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := by
  rw [card_sl_zmod_two]
  decide

theorem card_alternatingGroup_fin (n : ℕ) (hn : 2 ≤ n) :
    Nat.card (alternatingGroup (Fin n)) = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  rw [nat_card_alternatingGroup, Nat.card_fin]

theorem card_of_statedClassicalModel_psu_three_three {X : Type} [Group X]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 3 1) : Nat.card X = 6048 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three h

theorem card_of_qt13Five {Q : Type} [Group Q] [Finite Q] (h : QT13Five Q) :
    Nat.card Q = 60 ∨ Nat.card Q = 168 ∨ Nat.card Q = 360 ∨ Nat.card Q = 1080 ∨
      Nat.card Q = 6048 := by
  rcases h with ⟨⟨e⟩⟩ | h | ⟨⟨e⟩⟩ | ⟨-, hZ, ⟨e⟩⟩ | h
  · left
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup_fin 5 (by norm_num)]
    decide
  · right; left
    obtain ⟨e⟩ := nonempty_mulEquiv_sl_two_of_lieModel h
    rw [Nat.card_congr e.toEquiv, card_sl_three_zmod_two]
  · right; right; left
    rw [Nat.card_congr e.toEquiv, card_alternatingGroup_fin 6 (by norm_num)]
    decide
  · right; right; right; left
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q),
      Nat.card_congr e.toEquiv, card_alternatingGroup_fin 6 (by norm_num), hZ]
    decide
  · right; right; right; right
    exact card_of_statedClassicalModel_psu_three_three
      (LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) h)

theorem card_le_of_qt13Five {Q : Type} [Group Q] [Finite Q] (h : QT13Five Q) :
    Nat.card Q ≤ 6048 := by
  rcases card_of_qt13Five h with h | h | h | h | h <;> rw [h] <;> norm_num

theorem not_mulEquiv_sl_of_qt13Five {Q : Type} [Group Q] [Finite Q] (h : QT13Five Q) {n : ℕ}
    (hn : n = 4 ∨ n = 5) : ¬ Nonempty (Q ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
  rintro ⟨e⟩
  have hc := card_le_of_qt13Five h
  rw [Nat.card_congr e.toEquiv] at hc
  rcases hn with rfl | rfl
  · rw [card_sl_four_zmod_two] at hc
    omega
  · rw [card_sl_five_zmod_two] at hc
    omega

theorem not_surjective_alternating_of_qt13Five {Q : Type} [Group Q] [Finite Q] (h : QT13Five Q)
    {n : ℕ} (hn : n = 7 ∨ n = 8) (ψ : Q →* alternatingGroup (Fin n)) :
    ¬ Function.Surjective ψ := by
  intro hψ
  have hdvd : Nat.card (alternatingGroup (Fin n)) ∣ Nat.card Q := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  rw [card_alternatingGroup_fin n (by omega)] at hdvd
  rcases hn with rfl | rfl <;>
    rcases card_of_qt13Five h with h | h | h | h | h <;> rw [h] at hdvd <;> revert hdvd <;> decide

end CFSG.Quasithin.H13
