module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.Defs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs28
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNoTransv.CoreLinear
import CFSG.HardMathSupport.Solomon.Coordinator.I28_5

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv

open CFSG.HardMathSupport.Solomon

theorem exists_mcLaughlin_quotient {B : Type} [CommGroup B] [Finite B] (hB : ∀ b : B, b ^ 2 = 1)
    {H : Subgroup (MulAut B)} (hH : ⁅H, H⁆ = H) (hH1 : H ≠ ⊥) {s : MulAut B}
    (hs : UniquenessMaximal.IsTransvection s) (hsN : s ∈ Subgroup.normalizer (H : Set (MulAut B)))
    (hgen : H ≤ conjClosure H s) :
    ∃ (T : Type) (_ : Group T) (_ : IsSimpleGroup T) (ψ : ↥H →* T),
      Function.Surjective ψ ∧ (∀ h ∈ ψ.ker, h ^ 4 = 1) ∧ (∃ a b : T, a * b ≠ b * a) ∧
      ∃ (W : Type) (_ : Group W) (_ : Finite W) (c : ℕ),
        UniquenessMaximal.IsMcLaughlinGroup W ∧ (c = 1 ∨ c = 2) ∧ Nat.card T * c = Nat.card W ∧
        ∀ n : ℕ, Nonempty (W ≃* Equiv.Perm (Fin n)) → c = 2 := by
  let _ : Module (ZMod 2) (Additive B) := AddCommGroup.zmodModule fun x => by
    rw [two_nsmul]
    apply Additive.toMul.injective
    rw [toMul_add, toMul_zero]
    simpa [pow_two] using hB (Additive.toMul x)
  haveI : Finite (Additive B) := inferInstanceAs (Finite B)
  set Φ := Coordinator.i285_Φ (V := B)
  have hV : UniquenessMaximal.IsElemAbelianTwo B := fun b => by
    simpa [pow_two] using hB b
  have hH' : ⁅H.map Φ.toMonoidHom, H.map Φ.toMonoidHom⁆ = H.map Φ.toMonoidHom := by
    rw [← Subgroup.map_commutator, hH]
  have hH1' : H.map Φ.toMonoidHom ≠ ⊥ := fun h =>
    hH1 ((Subgroup.map_eq_bot_iff_of_injective H Φ.injective).mp h)
  have hτ : CFSG.ComponentClassification.OutcomeLocal.IsF2Transvection (Φ s) :=
    Coordinator.i285_isF2Transvection_Φ hV hs
  have hτN' : Φ s ∈ Subgroup.normalizer (H.map Φ.toMonoidHom : Set _) := by
    rw [← Subgroup.map_equiv_normalizer_eq H Φ]
    exact ⟨s, hsN, rfl⟩
  have hgen' : H.map Φ.toMonoidHom ≤ conjClosure (H.map Φ.toMonoidHom) (Φ s) := by
    have hmapgen : (conjClosure H s).map Φ.toMonoidHom =
        conjClosure (H.map Φ.toMonoidHom) (Φ s) := by
      rw [conjClosure, MonoidHom.map_closure, conjClosure]
      congr 1
      ext y
      constructor
      · rintro ⟨x, ⟨g, hg, rfl⟩, rfl⟩
        exact ⟨Φ g, ⟨g, hg, rfl⟩, by simp⟩
      · rintro ⟨y', ⟨g, hg, rfl⟩, rfl⟩
        exact ⟨g⁻¹ * s * g, ⟨g, hg, rfl⟩, by simp⟩
    simpa only [hmapgen] using Subgroup.map_mono (f := Φ.toMonoidHom) hgen
  obtain ⟨T, hT, hTs, ψ', hψ'surj, hψ'ker, hnab, W, hW, hWfin, c, hMc, hc12, hcard, hc2⟩ :=
    exists_mcLaughlin_quotient_linear (M := Additive B) hH' hH1' hτ hτN' hgen'
  let e : ↥H ≃* ↥(H.map Φ.toMonoidHom) :=
    Subgroup.equivMapOfInjective H Φ.toMonoidHom Φ.injective
  refine ⟨T, hT, hTs, ψ'.comp e.toMonoidHom, ?_, ?_, hnab, W, hW, hWfin, c, hMc, hc12,
    hcard, hc2⟩
  · intro t
    obtain ⟨x, rfl⟩ := hψ'surj t
    obtain ⟨h, rfl⟩ := e.surjective x
    exact ⟨h, rfl⟩
  · intro h hh
    have h4 : (e h) ^ 4 = 1 := hψ'ker (e h) hh
    have : e (h ^ 4) = e 1 := by
      rw [map_pow, map_one]
      exact h4
    exact e.injective this

end CFSG.LocalAnalysis.UniquenessCase.UC22.NoTransv
