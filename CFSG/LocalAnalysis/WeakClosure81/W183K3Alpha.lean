module

public import CFSG.LocalAnalysis.WeakClosure81.W183K3AlphaA6
public import CFSG.LocalAnalysis.WeakClosure81.W183K3L34
import CFSG.LocalAnalysis.WeakClosure81.W183K3Sup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL3 IsAlt)
open W183K3

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L₁ L₂ A : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

theorem br3_alpha_false (rows : Br3Rows) (h : Assumption131 Y Γ VA i)
    (hVfix : ∀ B ∈ Γ, VA B ≤ fixSub B) (htwo : Br3TwoComp Y T L₁ L₂) (hA : A ∈ Γ)
    (hr : mRank A ≤ i) (hcard : Nat.card ↥A = 4)
    (hn₁ : A ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)))
    (hker₁ : A ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) = ⊥)
    (hcent₂ : A ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)))
    (hshape : IsL3 (↥L₁ ⧸ Subgroup.center ↥L₁) 2 ∨ IsAlt (↥L₁ ⧸ Subgroup.center ↥L₁) 6)
    (hτ : ∃ τ ∈ Y, ActsOnDynkinMod (quasiCentre L₁) L₁ τ) : False := by
  rcases hshape with h34 | h6
  · have hAY : A ≤ Y := h.le_G A hA
    haveI : Finite (LGL 2 V) :=
      Finite.of_injective (fun e : LGL 2 V => fun v : V => e v)
        (fun e f h => LinearEquiv.ext (congrFun h))
    have hcommZ : ∀ a ∈ quasiCentre L₁, ∀ b ∈ quasiCentre L₂, a * b = b * a :=
      fun a ha b hb => htwo.comm a (quasiCentre_le L₁ ha) b (quasiCentre_le L₂ hb)
    have hZ₁ : Odd (Nat.card ↥(quasiCentre L₁)) := by
      have : Nat.card ↥(quasiCentre L₁) = Nat.card ↥(Subgroup.center ↥L₁) :=
        Subgroup.card_map_of_injective Subtype.val_injective
      rw [this]; exact htwo.odd₁
    have hZ₂ : Odd (Nat.card ↥(quasiCentre L₂)) := by
      have : Nat.card ↥(quasiCentre L₂) = Nat.card ↥(Subgroup.center ↥L₂) :=
        Subgroup.card_map_of_injective Subtype.val_injective
      rw [this]; exact htwo.odd₂
    have hsupN : A ⊔ L₁ ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)) :=
      sup_le hn₁ Subgroup.le_normalizer
    have hsupC : A ⊔ L₁ ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)) :=
      sup_le hcent₂ (fun l hl => by
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact (htwo.comm l hl b hb).symm)
    have hc : QuasiCore (A ⊔ L₁) L₁ (quasiCentre L₁ ⊔ quasiCentre L₂) :=
      { le := le_sup_right
        normal := fun y hy l hl => (Subgroup.mem_normalizer_iff.mp (hsupN hy) l).mp hl
        quasi := htwo.quasi₁
        odd := w183k3_odd_card_sup hcommZ hZ₁ hZ₂
        cent := by
          intro y hy hyc
          have hyY : y ∈ Y := sup_le hAY htwo.le₁ hy
          have hy₂ : ∀ l ∈ L₂, y * l = l * y := fun l hl =>
            ((Subgroup.mem_centralizer_iff.mp (hsupC hy)) l hl).symm
          obtain ⟨l₁, hl₁, l₂, hl₂, hy12⟩ :=
            w183k3_exists_mul_of_mem_sup htwo.comm (htwo.cent y hyY hyc hy₂)
          have h1 : l₁ ∈ quasiCentre L₁ := by
            refine mem_quasiCentre.mpr ⟨hl₁, fun l hl => ?_⟩
            have e1 := hyc l hl
            have e2 := htwo.comm l hl l₂ hl₂
            rw [← hy12] at e1
            calc l₁ * l = (l₁ * l * l₂) * l₂⁻¹ := by group
              _ = (l * l₁ * l₂) * l₂⁻¹ := by
                rw [show l₁ * l * l₂ = l₁ * (l * l₂) by group, e2,
                  show l₁ * (l₂ * l) = (l₁ * l₂) * l by group, e1]
                group
              _ = l * l₁ := by group
          have h2 : l₂ ∈ quasiCentre L₂ := by
            refine mem_quasiCentre.mpr ⟨hl₂, fun l hl => ?_⟩
            have e1 := hy₂ l hl
            have e2 := htwo.comm l₁ hl₁ l hl
            rw [← hy12] at e1
            calc l₂ * l = l₁⁻¹ * (l₁ * l₂ * l) := by group
              _ = l₁⁻¹ * (l * (l₁ * l₂)) := by rw [e1]
              _ = l₁⁻¹ * ((l * l₁) * l₂) := by group
              _ = l₁⁻¹ * ((l₁ * l) * l₂) := by rw [e2]
              _ = l * l₂ := by group
          rw [← hy12]
          exact Subgroup.mul_mem_sup h1 h2 }
    exact w183k3_false_of_L34_core rows.h65f rows.g1syl h hVfix hc h34 htwo.le₁ hA hr hcard
  · exact w183k3_alpha_false_A6 rows.a6 h htwo hA hr hcard hn₁ hker₁ hcent₂ h6 hτ

end CFSG.LocalAnalysis.WeakClosure81

end
