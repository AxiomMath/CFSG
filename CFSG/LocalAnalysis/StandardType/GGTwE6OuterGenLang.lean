module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeToralityTw

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.StandardType.TwE6OuterGen

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


variable {L : Type} [Field L] [IsAlgClosed L] (ℓ : ℕ) [Fact ℓ.Prime] [CharP L ℓ]

theorem exists_lang_frame_conj_eq_twisted (t : TwistTag) (f : ℕ) (hf : 1 ≤ f)
    {A : Subgroup (ModGL t.tag L)}
    (hFix : ∀ x ∈ A, twistHom t L (iterateFrobenius L ℓ f) x = x) {g : ModGL t.tag L}
    (hg : g ∈ adjointGroup t.tag L) (hgA : ∀ x ∈ A, g⁻¹ * x * g ∈ torusGroup t.tag L) :
    ∃ v : WeylGroup t.tag, ∃ g0 ∈ adjointGroup t.tag L,
      twistHom t L (iterateFrobenius L ℓ f) g0 = g0 * canonicalRep (coxeterSystem t.tag) L v ∧
      ∀ x ∈ A, g0⁻¹ * x * g0 = g⁻¹ * x * g := by
  classical
  choose a ha using fun x : A => exists_rootDiagUnit_eq_of_mem_torusGroup (hgA x x.2)
  have hn : ∀ x : A, (g⁻¹ * twistHom t L (iterateFrobenius L ℓ f) g) *
      twistHom t L (iterateFrobenius L ℓ f) (rootDiagUnit t.tag (a x)) *
      (g⁻¹ * twistHom t L (iterateFrobenius L ℓ f) g)⁻¹ = rootDiagUnit t.tag (a x) := by
    intro x
    rw [← ha x, map_mul, map_mul, map_inv, hFix x x.2]
    group
  obtain ⟨w', z, hz, hlang⟩ := exists_lang_datum_of_plane_twisted ℓ t f hf a hg hn
  obtain ⟨hzG, hzcomm⟩ := mem_familyCentralizer.1 (familyGroup_le_familyCentralizer (K := L) a hz)
  refine ⟨w', g * z, mul_mem hg hzG, inv_mul_eq_iff_eq_mul.1 hlang, fun x hx => ?_⟩
  have hzd : z⁻¹ * rootDiagUnit t.tag (a ⟨x, hx⟩) * z = rootDiagUnit t.tag (a ⟨x, hx⟩) := by
    have h := hzcomm ⟨x, hx⟩
    rw [mul_inv_eq_iff_eq_mul] at h
    calc z⁻¹ * rootDiagUnit t.tag (a ⟨x, hx⟩) * z
        = z⁻¹ * (rootDiagUnit t.tag (a ⟨x, hx⟩) * z) := by group
      _ = z⁻¹ * (z * rootDiagUnit t.tag (a ⟨x, hx⟩)) := by rw [h]
      _ = rootDiagUnit t.tag (a ⟨x, hx⟩) := by group
  calc (g * z)⁻¹ * x * (g * z) = z⁻¹ * (g⁻¹ * x * g) * z := by group
    _ = g⁻¹ * x * g := by rw [ha ⟨x, hx⟩, hzd]

end CFSG.StandardType.TwE6OuterGen
