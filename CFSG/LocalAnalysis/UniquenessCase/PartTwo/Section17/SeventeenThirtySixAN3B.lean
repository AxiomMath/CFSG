module

public import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.GroupTheory.CommutingProductFixedSubgroup
public import CFSG.GroupTheory.ElemAbelianRank
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

variable {G : Type} [Group G] [Finite G]

theorem pRank_four_of_three_commuting_squares {r : ℕ} (hr : r.Prime)
    {E₁ E₂ E₃ : Subgroup G}
    (h₁ : IsElemAbelian r E₁) (h₂ : IsElemAbelian r E₂) (h₃ : IsElemAbelian r E₃)
    (hcard₁ : Nat.card E₁ = r ^ 2) (hcard₂ : Nat.card E₂ = r ^ 2)
    (hcard₃ : Nat.card E₃ = r ^ 2)
    (hc₁₂ : ∀ a : G, a ∈ E₁ → ∀ b : G, b ∈ E₂ → a * b = b * a)
    (hc₁₃ : ∀ a : G, a ∈ E₁ → ∀ b : G, b ∈ E₃ → a * b = b * a)
    (hc₂₃ : ∀ a : G, a ∈ E₂ → ∀ b : G, b ∈ E₃ → a * b = b * a)
    (hint₂ : Nat.card ↥(E₂ ⊓ (E₁ ⊔ E₃)) ≤ r)
    (hint₁ : Nat.card ↥(E₁ ⊓ (E₂ ⊔ E₃)) ≤ r) :
    4 ≤ CFSG.Open.pRank r (E₁ ⊔ E₂ ⊔ E₃) := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hrpos : 0 < r := hr.pos
  have hcent₂₃ : E₂ ≤ Subgroup.centralizer (E₃ : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => (hc₂₃ x hx y hy).symm
  have hnorm₂₃ : E₂ ≤ Subgroup.normalizer (E₃ : Set G) :=
    hcent₂₃.trans (Subgroup.centralizer_le_normalizer (E₃ : Set G))
  have hB_ea : IsElemAbelian r (E₂ ⊔ E₃) := h₂.sup_of_commute h₃ hc₂₃
  have hcard_inf₂₃ : Nat.card ↥(E₂ ⊓ E₃) ≤ r := by
    have hle : E₂ ⊓ E₃ ≤ E₂ ⊓ (E₁ ⊔ E₃) :=
      inf_le_inf_left E₂ (le_sup_right : E₃ ≤ E₁ ⊔ E₃)
    exact (Nat.le_of_dvd (Nat.card_pos) (Subgroup.card_dvd_of_le hle)).trans hint₂
  have hBcard : r ^ 3 ≤ Nat.card ↥(E₂ ⊔ E₃) := by
    have hmul : Nat.card ↥(E₂ ⊔ E₃) * Nat.card ↥(E₂ ⊓ E₃) = r ^ 4 := by
      rw [card_sup_mul_card_inf hnorm₂₃, hcard₂, hcard₃, ← pow_add]
    have h : r ^ 3 * r ≤ Nat.card ↥(E₂ ⊔ E₃) * r := by
      calc r ^ 3 * r = r ^ 4 := by ring
        _ = Nat.card ↥(E₂ ⊔ E₃) * Nat.card ↥(E₂ ⊓ E₃) := hmul.symm
        _ ≤ Nat.card ↥(E₂ ⊔ E₃) * r := Nat.mul_le_mul_left _ hcard_inf₂₃
    exact Nat.le_of_mul_le_mul_right h hrpos
  have hcomm₁B : ∀ a : G, a ∈ E₁ → ∀ b : G, b ∈ E₂ ⊔ E₃ → a * b = b * a := by
    intro a ha b hb
    obtain ⟨b₂, hb₂, b₃, hb₃, rfl⟩ :=
      CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hc₂₃ hb
    calc a * (b₂ * b₃) = (a * b₂) * b₃ := by rw [mul_assoc]
      _ = (b₂ * a) * b₃ := by rw [hc₁₂ a ha b₂ hb₂]
      _ = b₂ * (a * b₃) := by rw [mul_assoc]
      _ = b₂ * (b₃ * a) := by rw [hc₁₃ a ha b₃ hb₃]
      _ = b₂ * b₃ * a := (mul_assoc b₂ b₃ a).symm
  have hcent₁B : E₁ ≤ Subgroup.centralizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => (hcomm₁B x hx y hy).symm
  have hnorm₁B : E₁ ≤ Subgroup.normalizer ((E₂ ⊔ E₃ : Subgroup G) : Set G) :=
    hcent₁B.trans (Subgroup.centralizer_le_normalizer ((E₂ ⊔ E₃ : Subgroup G) : Set G))
  have hE₁B_ea : IsElemAbelian r (E₁ ⊔ (E₂ ⊔ E₃)) :=
    h₁.sup_of_commute hB_ea hcomm₁B
  have hcard : r ^ 4 ≤ Nat.card ↥(E₁ ⊔ (E₂ ⊔ E₃)) := by
    have hmul : Nat.card ↥(E₁ ⊔ (E₂ ⊔ E₃)) * Nat.card ↥(E₁ ⊓ (E₂ ⊔ E₃)) =
        r ^ 2 * Nat.card ↥(E₂ ⊔ E₃) := by
      rw [card_sup_mul_card_inf hnorm₁B, hcard₁]
    have h : r ^ 4 * r ≤ Nat.card ↥(E₁ ⊔ (E₂ ⊔ E₃)) * r := by
      calc r ^ 4 * r = r ^ 2 * r ^ 3 := by ring
        _ ≤ r ^ 2 * Nat.card ↥(E₂ ⊔ E₃) := Nat.mul_le_mul_left _ hBcard
        _ = Nat.card ↥(E₁ ⊔ (E₂ ⊔ E₃)) * Nat.card ↥(E₁ ⊓ (E₂ ⊔ E₃)) := hmul.symm
        _ ≤ Nat.card ↥(E₁ ⊔ (E₂ ⊔ E₃)) * r := Nat.mul_le_mul_left _ hint₁
    exact Nat.le_of_mul_le_mul_right h hrpos
  have hEq : E₁ ⊔ (E₂ ⊔ E₃) = E₁ ⊔ E₂ ⊔ E₃ := by
    rw [sup_assoc]
  have hE_ea : IsElemAbelian r (E₁ ⊔ E₂ ⊔ E₃) := by
    rw [← hEq]; exact hE₁B_ea
  have hcard' : r ^ 4 ≤ Nat.card ↥(E₁ ⊔ E₂ ⊔ E₃) := by
    rw [← hEq]; exact hcard
  have hpow := CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hr hE_ea
  have hle : r ^ 4 ≤ r ^ CFSG.Open.pRank r (E₁ ⊔ E₂ ⊔ E₃) := hcard'.trans_eq hpow
  exact (Nat.pow_le_pow_iff_right hr.one_lt).mp hle

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
