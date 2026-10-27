module

public import CFSG.Open.LocalVocabulary

import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.SupCommute

@[expose] public section

namespace CFSG.ThreeCopiesNormalizer

theorem exists_three_copies {Y J : Type} [Group Y] [Finite Y] [Group J]
    (hJ : ∃ E T : Subgroup J, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 9 ∧ T ≠ ⊥ ∧
      IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set J))
    {S₀ S₁ S₂ : Subgroup Y} (h₀ : Nonempty (↥S₀ ≃* J)) (h₁ : Nonempty (↥S₁ ≃* J))
    (h₂ : Nonempty (↥S₂ ≃* J)) (h01 : ∀ x ∈ S₀, ∀ y ∈ S₁, x * y = y * x)
    (h02 : ∀ x ∈ S₀, ∀ y ∈ S₂, x * y = y * x) (h12 : ∀ x ∈ S₁, ∀ y ∈ S₂, x * y = y * x)
    (hi01 : S₀ ⊓ S₁ = ⊥) (hi012 : (S₀ ⊔ S₁) ⊓ S₂ = ⊥) :
    ∃ E T : Subgroup Y, CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 6 ∧ T ≠ ⊥ ∧
      IsPGroup 2 T ∧ E ≤ Subgroup.normalizer (T : Set Y) := by
  obtain ⟨E, T, hE, hEcard, hTne, hT2, hET⟩ := hJ
  obtain ⟨e0⟩ := h₀
  obtain ⟨e1⟩ := h₁
  obtain ⟨e2⟩ := h₂
  let φ0 : J →* Y := S₀.subtype.comp e0.symm.toMonoidHom
  let φ1 : J →* Y := S₁.subtype.comp e1.symm.toMonoidHom
  let φ2 : J →* Y := S₂.subtype.comp e2.symm.toMonoidHom
  let E0 : Subgroup Y := E.map φ0
  let E1 : Subgroup Y := E.map φ1
  let E2 : Subgroup Y := E.map φ2
  let T0 : Subgroup Y := T.map φ0
  have hφ0 : Function.Injective φ0 := by
    intro a b h
    exact e0.symm.injective (Subtype.coe_injective (by simpa [φ0] using h))
  have hφ1 : Function.Injective φ1 := by
    intro a b h
    exact e1.symm.injective (Subtype.coe_injective (by simpa [φ1] using h))
  have hφ2 : Function.Injective φ2 := by
    intro a b h
    exact e2.symm.injective (Subtype.coe_injective (by simpa [φ2] using h))
  have hE0S : E0 ≤ S₀ := by
    intro x hx
    change x ∈ E.map φ0 at hx
    obtain ⟨e, _, rfl⟩ := hx
    exact (e0.symm e).2
  have hE1S : E1 ≤ S₁ := by
    intro x hx
    change x ∈ E.map φ1 at hx
    obtain ⟨e, _, rfl⟩ := hx
    exact (e1.symm e).2
  have hE2S : E2 ≤ S₂ := by
    intro x hx
    change x ∈ E.map φ2 at hx
    obtain ⟨e, _, rfl⟩ := hx
    exact (e2.symm e).2
  have hT0S : T0 ≤ S₀ := by
    intro x hx
    change x ∈ T.map φ0 at hx
    obtain ⟨t, _, rfl⟩ := hx
    exact (e0.symm t).2
  have hE0 : CFSG.Open.IsElemAbelian 3 E0 := CFSG.Open.IsElemAbelian.map hE φ0
  have hE1 : CFSG.Open.IsElemAbelian 3 E1 := CFSG.Open.IsElemAbelian.map hE φ1
  have hE2 : CFSG.Open.IsElemAbelian 3 E2 := CFSG.Open.IsElemAbelian.map hE φ2
  have hEcard0 : Nat.card E0 = 9 := by
    change Nat.card (E.map φ0) = 9
    rw [Subgroup.card_map_of_injective hφ0, hEcard]
  have hEcard1 : Nat.card E1 = 9 := by
    change Nat.card (E.map φ1) = 9
    rw [Subgroup.card_map_of_injective hφ1, hEcard]
  have hEcard2 : Nat.card E2 = 9 := by
    change Nat.card (E.map φ2) = 9
    rw [Subgroup.card_map_of_injective hφ2, hEcard]
  have hcomm01 : ∀ a ∈ E0, ∀ b ∈ E1, Commute a b :=
    fun a ha b hb => h01 a (hE0S ha) b (hE1S hb)
  have hcomm02 : ∀ a ∈ E0, ∀ b ∈ E2, Commute a b :=
    fun a ha b hb => h02 a (hE0S ha) b (hE2S hb)
  have hcomm12 : ∀ a ∈ E1, ∀ b ∈ E2, Commute a b :=
    fun a ha b hb => h12 a (hE1S ha) b (hE2S hb)
  have hcomm012 : ∀ a ∈ E0 ⊔ E1, ∀ b ∈ E2, Commute a b := by
    intro a ha b hb
    rw [CFSG.mem_sup_of_commute hcomm01] at ha
    obtain ⟨a0, ha0, a1, ha1, rfl⟩ := ha
    exact (hcomm02 a0 ha0 b hb).mul_left (hcomm12 a1 ha1 b hb)
  have hdisj01 : E0 ⊓ E1 = ⊥ := by
    rw [← le_bot_iff]
    exact (inf_le_inf hE0S hE1S).trans_eq hi01
  have hE01S : E0 ⊔ E1 ≤ S₀ ⊔ S₁ :=
    sup_le (hE0S.trans le_sup_left) (hE1S.trans le_sup_right)
  have hdisj012 : (E0 ⊔ E1) ⊓ E2 = ⊥ := by
    rw [← le_bot_iff]
    have hsub : (E0 ⊔ E1) ⊓ E2 ≤ (S₀ ⊔ S₁) ⊓ S₂ := by
      apply le_inf
      · exact inf_le_left.trans hE01S
      · exact inf_le_right.trans hE2S
    exact hsub.trans_eq hi012
  have hE01 : CFSG.Open.IsElemAbelian 3 (E0 ⊔ E1) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hE0 hE1 hcomm01
  have hE012 : CFSG.Open.IsElemAbelian 3 ((E0 ⊔ E1) ⊔ E2) :=
    CFSG.Open.IsElemAbelian.sup_of_commute hE01 hE2 hcomm012
  have hcardE01 : Nat.card ↥(E0 ⊔ E1) = 9 * 9 := by
    rw [CFSG.card_sup_eq_mul_of_commute E0 E1 hcomm01 hdisj01, hEcard0, hEcard1]
  have hcardE012 : Nat.card ↥((E0 ⊔ E1) ⊔ E2) = 3 ^ 6 := by
    rw [CFSG.card_sup_eq_mul_of_commute (E0 ⊔ E1) E2 hcomm012 hdisj012,
      hcardE01, hEcard2]
    norm_num
  have hT0ne : T0 ≠ ⊥ := by
    intro hbot
    apply hTne
    have hmap : T.map φ0 = (⊥ : Subgroup J).map φ0 := by
      simpa [T0] using hbot
    exact (Subgroup.map_injective hφ0) hmap
  have hT02 : IsPGroup 2 T0 := hT2.map φ0
  have hE0N : E0 ≤ Subgroup.normalizer (T0 : Set Y) := by
    have h := (Subgroup.map_mono (f := φ0) hET).trans
      (Subgroup.le_normalizer_map (H := T) φ0)
    simpa [E0, T0] using h
  have hE1N : E1 ≤ Subgroup.normalizer (T0 : Set Y) := by
    have hcent : E1 ≤ Subgroup.centralizer (T0 : Set Y) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact h01 t (hT0S ht) x (hE1S hx)
    exact hcent.trans (Subgroup.centralizer_le_normalizer (T0 : Set Y))
  have hE2N : E2 ≤ Subgroup.normalizer (T0 : Set Y) := by
    have hcent : E2 ≤ Subgroup.centralizer (T0 : Set Y) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact h02 t (hT0S ht) x (hE2S hx)
    exact hcent.trans (Subgroup.centralizer_le_normalizer (T0 : Set Y))
  exact ⟨(E0 ⊔ E1) ⊔ E2, T0, hE012, hcardE012, hT0ne, hT02,
    sup_le (sup_le hE0N hE1N) hE2N⟩

end CFSG.ThreeCopiesNormalizer

end
