module

public import CFSG.Timmesfeld.Transvection.RankTwoRelPair
public import CFSG.Timmesfeld.Transvection.ShortRootHyp

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.Timmesfeld.ARS.NaturalModule CFSG.Timmesfeld.RankOne
open CFSG.LieType.BorelTits

variable {G : Type*} [Group G] {Δ : Set (Subgroup G)}

namespace PairFrame

variable [Finite G] {A E D E' : Subgroup G} (F : PairFrame Δ A E D E') (hΔ : IsTransvectionClass Δ)
  (hpts : PointsDetermined Δ) (hml : MeetsLines Δ) (hthick : ThickLines Δ)
  (hq : 4 ≤ Nat.card A) {k : ℕ} (φ₀ : SL2Coords A E k) (φ₁ : SL2Coords D E' k)
include F hΔ hpts hml hthick hq

theorem exists_aligned_of_meetsLines :
    ∃ τ : GaloisField 2 k ≃+* GaloisField 2 k, φ₀.Aligned Δ (φ₁.map τ) :=
  F.exists_aligned hΔ φ₀ hpts hq (F.shortRootFieldHyp_of_meetsLines hΔ hpts hml hq) φ₁
    (F.exists_ne_one_of_thickLines hΔ hpts hml hq hthick)

theorem exists_pairRelations (hal : φ₀.Aligned Δ φ₁) :
    (Nat.card ↥(shortRootGroup Δ E A D E') = 2 ^ k ∧
      ∃ β : GaloisField 2 k → G, PairRelations (RingEquiv.refl _) (RingHom.id _) Δ A E D E'
        (fun t => φ₀.elt (lowerElt _ t)) (fun t => φ₁.elt (lowerElt _ t)) (φ₀.elt (weylElt _))
        (φ₁.elt (weylElt _)) φ₀.torusElt φ₁.torusElt β) ∨
    (Nat.card ↥(shortRootGroup Δ E A D E') = (2 ^ k) ^ 2 ∧
      ∀ ι : GaloisField 2 k →+* GaloisField 2 (2 * k),
        (∀ z, unitaryInvolution (GaloisField 2 (2 * k)) 2 k z = z ↔ ∃ c, ι c = z) →
        ∃ β : GaloisField 2 (2 * k) → G,
          PairRelations (unitaryInvolution (GaloisField 2 (2 * k)) 2 k) ι Δ A E D E'
            (fun t => φ₀.elt (lowerElt _ t)) (fun t => φ₁.elt (lowerElt _ t))
            (φ₀.elt (weylElt _)) (φ₁.elt (weylElt _)) φ₀.torusElt φ₁.torusElt β) := by
  have hX := F.shortRootFieldHyp_of_meetsLines hΔ hpts hml hq
  have hX' := F.shortRootFieldHyp_swap hΔ hpts hml hq
  have hY := F.exists_conjSub_eq_swap hΔ hpts hml hq
  have hX1 := F.exists_ne_one_of_thickLines hΔ hpts hml hq hthick
  rcases F.exists_normBase hΔ φ₀ hpts hq hX φ₁ hal hX1 with ⟨hc, β, hβ⟩ | ⟨hc, h⟩
  · exact Or.inl ⟨hc, β, F.pairRelations hΔ φ₀ φ₁ hpts hq hX hX' hY hal (RingEquiv.refl _)
      (RingHom.id _) (fun _ => rfl) (fun _ => rfl) hβ⟩
  · refine Or.inr ⟨hc, fun ι hι => ?_⟩
    obtain ⟨β, hβ⟩ := h ι hι
    have hk : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · have := φ₀.card_eq
        rw [h0, pow_zero] at this
        omega
      · exact h0
    have hF : Nat.card (GaloisField 2 (2 * k)) = (2 ^ k) ^ 2 := by
      rw [GaloisField.card 2 (2 * k) (by omega), ← pow_mul, mul_comm]
    exact ⟨β, F.pairRelations hΔ φ₀ φ₁ hpts hq hX hX' hY hal _ ι
      (unitaryInvolution_involutive hF) (fun c => (hι (ι c)).2 ⟨c, rfl⟩) hβ⟩

end PairFrame

end CFSG.Timmesfeld.Transvection
