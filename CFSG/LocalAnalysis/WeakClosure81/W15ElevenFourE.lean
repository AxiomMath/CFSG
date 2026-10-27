module

public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenFourA
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenFourB
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenFourC
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenFourD
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenSeven
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenNum

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def W15Eleven4Bar (G : Type) [Group G] [Finite G] : Prop :=
  ∀ M V₀ V U S H P Q₀ : Subgroup G, ∀ p : ℕ, Cfg1511 M V₀ V U S H P Q₀ p →
    ∀ (X : Subgroup G) (v : G), XData15 V₀ U H Q₀ p X v → Nat.card ↥X = p ^ 3 →
    ∀ Y B : Subgroup G, Y ≤ X → Nat.card ↥Y = p → (∀ y ∈ Y, ∀ x ∈ X, y * x = x * y) →
      B ≤ tSub15 M V₀ V U P → IsElemAbelian 2 B → ⁅B, Y⁆ ≤ iHull15 V₀ U H →
      ∃ B₀ : Subgroup G, B₀ ≤ B ∧ B₀.relIndex B ≤ 2 ∧
        ∀ b ∈ B₀, ∀ k ∈ kHull15 V₀ H, ⁅k, b⁆ ∈ iHull15 V₀ U H

namespace Cfg1511

variable {M V₀ V U S H P Q₀ R X : Subgroup G} {p : ℕ} {v : G}

theorem not_le_P (h4 : W15Eleven4Bar G)
    (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v)
    (hR : IsSylowIn 2 R (F11.CTilde M V₀ V)) : ¬ R ≤ P := by
  intro hRP
  have hCV := c.inf_centralizer_kHull15_eq_bot hX hR hRP
  have hcard := c.card_eq_pow_three hX hCV
  obtain ⟨B, hBT, hBe, hBcard, hBU, hBx⟩ := c.exists_B hR hRP
  obtain ⟨Y, hYX, hYM, hXM, hYp, hYc, -, -, hYC⟩ := c.exists_Y hX hCV hcard
  have hXC : X ⊓ F11.CTilde M V₀ V = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxX, hxC⟩
    have : x ∈ Y ⊓ F11.CTilde M V₀ V := ⟨hXM ⟨hxX, cTilde_le_M M V₀ V hxC⟩, hxC⟩
    rw [hYC] at this
    exact this
  have hTY := c.commutator_tSub15_le hX hXC hYX hYM
  have hBY : ⁅B, Y⁆ ≤ iHull15 V₀ U H :=
    (Subgroup.commutator_mono hBT le_rfl).trans hTY
  obtain ⟨B₀, hB₀B, hB₀idx, hB₀K⟩ :=
    h4 M V₀ V U S H P Q₀ p c X v hX hcard Y B hYX hYp hYc hBT hBe hBY
  have hB₀Q : B₀ ≤ qSub15 M V₀ V U H P := fun b hb =>
    c.mem_qSub15_of_commutator_mem hX (hBT (hB₀B hb)) (hB₀K b hb)
  have hcardB : 4 ≤ Nat.card ↥B := hBcard ▸ c.four_le_card_v1Sub15 hX hcard
  have hB₀ne : B₀ ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.relIndex_bot_left] at hB₀idx
    omega
  obtain ⟨⟨x, hxB₀⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hB₀ne
  have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hxQ : x ∈ qSub15 M V₀ V U H P := hB₀Q hxB₀
  have hUx : U ≤ centralizer ({x} : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have hUQ : U ≤ centralizer (qSub15 M V₀ V U H P : Set G) :=
      le_sup_left.trans (XData15.sup_le_centralizer_qSub15 c hX)
    exact Subgroup.mem_centralizer_iff.1 (hUQ hu) h hxQ
  exact hBU ((le_inf c.cex.le hUx).trans (hBx x (hB₀B hxB₀) hx1'))

end Cfg1511

end CFSG.LocalAnalysis.WeakClosure81
