module

public import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.Card
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Notation.Pi.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.StandardType

private theorem shape_level {k : ℕ} {β : Type} [DecidableEq β] (u : Fin k → β)
    {a₁ a₂ : Fin k} (h12 : u a₁ ≠ u a₂)
    (hE : (k - 1) * (k - 2) ≤
      (Finset.univ.offDiag.filter fun q : Fin k × Fin k => u q.1 = u q.2).card) :
    ∃ a₀, ∀ b, b ≠ a₀ → u b ≠ u a₀ ∧ ∀ c, c ≠ a₀ → u b = u c := by
  have hS : (Finset.univ.filter fun c => u c = u a₁).card +
      (Finset.univ.filter fun c => ¬ u c = u a₁).card = k := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ, Fintype.card_fin]
  have h1 : a₁ ∈ Finset.univ.filter fun c => u c = u a₁ := by simp
  have h2 : a₂ ∈ Finset.univ.filter fun c => ¬ u c = u a₁ := by simp [Ne.symm h12]
  have hPS : (Finset.univ.offDiag.filter fun q : Fin k × Fin k => u q.1 = u q.2) ⊆
      (Finset.univ.filter fun c => u c = u a₁).offDiag ∪
        (Finset.univ.filter fun c => ¬ u c = u a₁).offDiag := by
    intro q hq
    obtain ⟨hq, hu⟩ := Finset.mem_filter.mp hq
    obtain ⟨-, -, hne⟩ := Finset.mem_offDiag.mp hq
    by_cases h : u q.1 = u a₁
    · exact Finset.mem_union_left _ (Finset.mem_offDiag.mpr ⟨by simp [h], by simp [← hu, h], hne⟩)
    · exact Finset.mem_union_right _ (Finset.mem_offDiag.mpr ⟨by simp [h], by simp [← hu, h], hne⟩)
  have hle := (Finset.card_le_card hPS).trans (Finset.card_union_le _ _)
  rw [Finset.offDiag_card, Finset.offDiag_card, ← Nat.mul_sub_one, ← Nat.mul_sub_one] at hle
  obtain ⟨i, hi⟩ : ∃ i, (Finset.univ.filter fun c => u c = u a₁).card = i + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr ⟨_, h1⟩)).symm⟩
  obtain ⟨j, hj⟩ : ∃ j, (Finset.univ.filter fun c => ¬ u c = u a₁).card = j + 1 :=
    ⟨_, (Nat.succ_pred_eq_of_pos (Finset.card_pos.mpr ⟨_, h2⟩)).symm⟩
  rw [hi, hj, Nat.add_sub_cancel, Nat.add_sub_cancel] at hle
  have hij : i = 0 ∨ j = 0 := by
    rw [show k - 1 = i + j + 1 by omega, show k - 2 = i + j by omega] at hE
    by_contra h
    push Not at h
    have : 1 ≤ i * j := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero h.1 h.2)
    nlinarith
  rcases hij with rfl | rfl
  ·
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hi
    have hS1 : ∀ c, u c = u a₁ → c = a₁ := fun c hc => by
      have hc' : c ∈ Finset.univ.filter fun c => u c = u a₁ := by simp [hc]
      rw [ha] at hc' h1
      exact (Finset.mem_singleton.mp hc').trans (Finset.mem_singleton.mp h1).symm
    refine ⟨a₁, fun b hb => ⟨fun h => hb (hS1 b h), fun c hc => ?_⟩⟩
    by_cases hbc : b = c
    · rw [hbc]
    have hsub : (Finset.univ.offDiag.filter fun q : Fin k × Fin k => u q.1 = u q.2) ⊆
        (Finset.univ.erase a₁).offDiag := by
      intro q hq
      obtain ⟨hq, hu⟩ := Finset.mem_filter.mp hq
      obtain ⟨-, -, hne⟩ := Finset.mem_offDiag.mp hq
      refine Finset.mem_offDiag.mpr ⟨Finset.mem_erase.mpr ⟨fun h => ?_, Finset.mem_univ _⟩,
        Finset.mem_erase.mpr ⟨fun h => ?_, Finset.mem_univ _⟩, hne⟩
      · exact hne (h.trans (hS1 q.2 (hu.symm.trans (congrArg u h))).symm)
      · exact hne ((hS1 q.1 (hu.trans (congrArg u h))).trans h.symm)
    have hcard : (Finset.univ.erase a₁).offDiag.card ≤
        (Finset.univ.offDiag.filter fun q : Fin k × Fin k => u q.1 = u q.2).card := by
      rw [Finset.offDiag_card, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        Fintype.card_fin, ← Nat.mul_sub_one, show k - 1 - 1 = k - 2 by omega]
      exact hE
    have hbc' : (b, c) ∈ Finset.univ.offDiag.filter fun q : Fin k × Fin k => u q.1 = u q.2 := by
      rw [Finset.eq_of_subset_of_card_le hsub hcard]
      exact Finset.mem_offDiag.mpr ⟨Finset.mem_erase.mpr ⟨hb, Finset.mem_univ _⟩,
        Finset.mem_erase.mpr ⟨hc, Finset.mem_univ _⟩, hbc⟩
    exact (Finset.mem_filter.mp hbc').2
  ·
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp hj
    have hS2 : ∀ c, ¬ u c = u a₁ → c = a₂ := fun c hc => by
      have hc' : c ∈ Finset.univ.filter fun c => ¬ u c = u a₁ := by simp [hc]
      rw [ha] at hc' h2
      exact (Finset.mem_singleton.mp hc').trans (Finset.mem_singleton.mp h2).symm
    refine ⟨a₂, fun b hb => ?_⟩
    have hb1 : u b = u a₁ := by_contra fun h => hb (hS2 b h)
    refine ⟨fun h => h12 (hb1.symm.trans h), fun c hc => ?_⟩
    rw [hb1, by_contra fun h => hc (hS2 c h)]

theorem ggDk_signedA_off_of_card {k : ℕ} {ε : Fin k → ℤ}
    (hε : ∀ a, ε a = 1 ∨ ε a = -1) {β : Type} (u : Fin k → β) (hu : ∃ a b, u a ≠ u b)
    {Φ : Set (Fin k → ℤ)}
    (hΦ : ∀ η ∈ Φ, ∃ a b, a ≠ b ∧ u a = u b ∧ η = Pi.single a (ε a) - Pi.single b (ε b))
    {T : Finset (Fin k → ℤ)} (hT : ↑T ⊆ Φ) (hTc : (k - 1) * (k - 2) ≤ T.card) :
    ∃ a₀, (∀ b, b ≠ a₀ → u b ≠ u a₀ ∧ ∀ c, c ≠ a₀ → u b = u c) ∧
      ∀ η, η ∈ Φ ↔ (∃ a b, a ≠ b ∧ η = Pi.single a (ε a) - Pi.single b (ε b)) ∧ η a₀ = 0 := by
  classical
  have hε0 : ∀ a, ε a ≠ 0 := fun a => by rcases hε a with h | h <;> omega
  have hg1 : ∀ {a b : Fin k}, a ≠ b →
      (Pi.single a (ε a) - Pi.single b (ε b) : Fin k → ℤ) a = ε a :=
    fun hab => by rw [Pi.sub_apply, Pi.single_eq_same, Pi.single_eq_of_ne hab, sub_zero]
  have hg2 : ∀ {a b : Fin k}, a ≠ b →
      (Pi.single a (ε a) - Pi.single b (ε b) : Fin k → ℤ) b = -ε b :=
    fun hab => by rw [Pi.sub_apply, Pi.single_eq_of_ne hab.symm, Pi.single_eq_same, zero_sub]
  have hg0 : ∀ {a b c : Fin k}, c ≠ a → c ≠ b →
      (Pi.single a (ε a) - Pi.single b (ε b) : Fin k → ℤ) c = 0 :=
    fun hca hcb => by rw [Pi.sub_apply, Pi.single_eq_of_ne hca, Pi.single_eq_of_ne hcb, sub_zero]
  have hinj : ∀ s : Finset (Fin k), Set.InjOn
      (fun q : Fin k × Fin k => (Pi.single q.1 (ε q.1) - Pi.single q.2 (ε q.2) : Fin k → ℤ))
      ↑s.offDiag := by
    rintro s ⟨a, b⟩ hab ⟨a', b'⟩ hab' h
    have hab := (Finset.mem_offDiag.mp hab).2.2
    have hab' := (Finset.mem_offDiag.mp hab').2.2
    have ha := congrFun h a
    have hb := congrFun h b
    simp only at ha hb hab hab'
    rw [hg1 hab] at ha
    rw [hg2 hab] at hb
    have h1 : a = a' := by
      by_contra h1
      by_cases h2 : a = b'
      · subst h2
        rw [hg2 hab'] at ha
        exact hε0 a (by omega)
      · rw [hg0 h1 h2] at ha
        exact hε0 a ha
    subst h1
    by_contra h2
    rw [hg0 hab.symm (fun h => h2 (Prod.ext rfl h))] at hb
    exact hε0 b (by omega)
  have hTP : T ⊆ (Finset.univ.offDiag.filter fun q : Fin k × Fin k => u q.1 = u q.2).image
      fun q => (Pi.single q.1 (ε q.1) - Pi.single q.2 (ε q.2) : Fin k → ℤ) := fun η hη => by
    obtain ⟨a, b, hab, huab, rfl⟩ := hΦ η (hT hη)
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_filter.mpr
      ⟨Finset.mem_offDiag.mpr ⟨Finset.mem_univ _, Finset.mem_univ _, hab⟩, huab⟩, rfl⟩
  obtain ⟨a₁, a₂, h12⟩ := hu
  obtain ⟨a₀, hsh⟩ :=
    shape_level u h12 (hTc.trans ((Finset.card_le_card hTP).trans Finset.card_image_le))
  have hoff : ∀ {a b : Fin k}, a ≠ b →
      (Pi.single a (ε a) - Pi.single b (ε b) : Fin k → ℤ) a₀ = 0 → a ≠ a₀ ∧ b ≠ a₀ :=
    fun {a b} hab h0 => ⟨fun h => hε0 a (by subst h; rw [← hg1 hab]; exact h0),
      fun h => hε0 b (by subst h; rw [← neg_eq_zero, ← hg2 hab]; exact h0)⟩
  have hfwd : ∀ η ∈ Φ, (∃ a b, a ≠ b ∧ η = Pi.single a (ε a) - Pi.single b (ε b)) ∧ η a₀ = 0 :=
    fun η hη => by
      obtain ⟨a, b, hab, huab, rfl⟩ := hΦ η hη
      have ha : a ≠ a₀ := fun h => (hsh b fun hb => hab (h.trans hb.symm)).1 (by rw [← huab, h])
      have hb : b ≠ a₀ := fun h => (hsh a fun ha => hab (ha.trans h.symm)).1 (by rw [huab, h])
      exact ⟨⟨a, b, hab, rfl⟩, hg0 (Ne.symm ha) (Ne.symm hb)⟩
  refine ⟨a₀, hsh, fun η => ⟨hfwd η, ?_⟩⟩
  rintro ⟨⟨a, b, hab, rfl⟩, h0⟩
  have hTQ : T ⊆ (Finset.univ.erase a₀).offDiag.image
      fun q => (Pi.single q.1 (ε q.1) - Pi.single q.2 (ε q.2) : Fin k → ℤ) := fun η hη => by
    obtain ⟨⟨a', b', hab', rfl⟩, h0'⟩ := hfwd η (hT hη)
    obtain ⟨ha', hb'⟩ := hoff hab' h0'
    exact Finset.mem_image.mpr ⟨(a', b'), Finset.mem_offDiag.mpr ⟨Finset.mem_erase.mpr
      ⟨ha', Finset.mem_univ _⟩, Finset.mem_erase.mpr ⟨hb', Finset.mem_univ _⟩, hab'⟩, rfl⟩
  have hQc : ((Finset.univ.erase a₀).offDiag.image
      fun q => (Pi.single q.1 (ε q.1) - Pi.single q.2 (ε q.2) : Fin k → ℤ)).card ≤ T.card := by
    rw [Finset.card_image_of_injOn (hinj _), Finset.offDiag_card,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      ← Nat.mul_sub_one, show k - 1 - 1 = k - 2 by omega]
    exact hTc
  obtain ⟨ha, hb⟩ := hoff hab h0
  apply hT
  rw [Finset.mem_coe, Finset.eq_of_subset_of_card_le hTQ hQc]
  exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_offDiag.mpr ⟨Finset.mem_erase.mpr
    ⟨ha, Finset.mem_univ _⟩, Finset.mem_erase.mpr ⟨hb, Finset.mem_univ _⟩, hab⟩, rfl⟩

end CFSG.StandardType

end
