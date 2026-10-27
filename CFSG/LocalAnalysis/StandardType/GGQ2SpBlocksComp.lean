module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpStatements
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompPSp
import CFSG.LocalAnalysis.StandardType.GGHalfCentGroup
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates

public section

namespace CFSG.StandardType.GGQ2Frame.SpBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition Matrix
open CFSG.Open (StatedSp)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem torusSet_commute {K : Type} [Field K]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ)
    (U : Submodule (ZMod 3) (PlaneRaw.V m)) :
    ∀ s ∈ torusSet ζ m U, ∀ s' ∈ torusSet ζ m U, Commute s s' := by
  rintro _ ⟨u, -, rfl⟩ _ ⟨v, -, rfl⟩
  have h : tau ζ m u * tau ζ m v = tau ζ m v * tau ζ m u := by
    simp only [tau]
    rw [← map_mul, ← map_mul, mul_comm]
  change ((tau ζ m u : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) * (tau ζ m v : ↥(StatedSp m K)) =
    ((tau ζ m v : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) * (tau ζ m u : ↥(StatedSp m K))
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, h]

theorem support_nonempty_of_admissible {m : ℕ} {c : PlaneRaw.Code m}
    (hc : PlaneRaw.admissible .symplectic c) : c.support.Nonempty := by
  cases c with
  | zero S =>
    have h : 2 ≤ S.card := hc
    exact Finset.card_pos.mp (show 0 < S.card by omega)
  | extension e =>
    have h : 4 ≤ (PlaneRaw.Code.extSupport e).card := hc.2
    exact Finset.card_pos.mp (show 0 < (PlaneRaw.Code.extSupport e).card by omega)

theorem spIsComponentOfCentralizerTorusSetIff_of (h5 : SpExistsCodeOfIsPrimAdjIdemIn)
    (h6a : SpGlBlockCentralizerPlaneIdem) (h6b : SpNormalYcode) (h6c : SpYcodeLeCentralizer)
    (h7a : SpIsQuasisimpleYcode) (h7b : SpNotIsComponentOfYcode) :
    SpIsComponentOfCentralizerTorusSetIff := by
  intro K _ _ _ ζ m hK hζ U X
  constructor
  · intro hX
    obtain ⟨ε, hε, hXε⟩ := exists_isComponentOf_glBlockCentralizer_PSp m K (torusSet ζ m U)
      (torusSet_commute ζ m U) hX
    obtain ⟨c, hocc, hne, rfl⟩ := h5 ζ m hK hζ U hε
    rw [h6a ζ m hK hζ U c hocc hne] at hXε
    by_cases hadm : PlaneRaw.admissible .symplectic c
    · exact ⟨c, hadm, hocc, GGHalf.eq_of_isComponentOf_isQuasisimple
        ((ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2
          (h7a ζ m hK hζ c hadm)) hXε⟩
    · exact (h7b ζ m hK hζ c hadm X hXε).elim
  · rintro ⟨c, hadm, hocc, rfl⟩
    have hne := support_nonempty_of_admissible hadm
    have hle := h6c ζ m hK hζ U c hocc hne
    exact ⟨hle, IsSubnormal.step hle (h6b ζ m hK hζ U c hocc hne) (IsSubnormal.refl _),
      (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2
        (h7a ζ m hK hζ c hadm)⟩

end CFSG.StandardType.GGQ2Frame.SpBlocks

end
