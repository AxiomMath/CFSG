module

public import CFSG.LocalAnalysis.StandardType.GGQ2LinStatements
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompGL
import CFSG.LocalAnalysis.StandardType.GGHalfCentGroup
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates

public section

namespace CFSG.StandardType.GGQ2Frame.LinBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.ClassicalPosition Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem torusSet_commute {K : Type} [Field K]
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2)
    (U : Submodule (ZMod 3) (PlaneRaw.V t)) :
    ∀ s ∈ torusSet ζ t ε U, ∀ s' ∈ torusSet ζ t ε U, Commute s s' := by
  rintro _ ⟨u, -, rfl⟩ _ ⟨v, -, rfl⟩
  show tau ζ t ε u * tau ζ t ε v = tau ζ t ε v * tau ζ t ε u
  simp only [tau]
  rw [← map_mul, ← map_mul, mul_comm]

theorem keyDim_pos_of_admissible {t : ℕ} {ε : Fin 2} {c : PlaneRaw.Code t}
    (hc : PlaneRaw.admissible (.linear ε) c) : 0 < keyDim ε c := by
  cases c with
  | zero S =>
    have h : 3 ≤ 2 * S.card + ε.val := hc
    simp only [keyDim]
    omega
  | extension e =>
    have h : 2 ≤ (PlaneRaw.Code.extSupport e).card := hc.2
    simp only [keyDim]
    omega

theorem linIsComponentOfCentralizerTorusSetIff_of (h5 : LinExistsCodeOfIsPrimIdemIn)
    (h6a : LinGlBlockCentralizerKeyIdem) (h6b : LinNormalYcode) (h6c : LinYcodeLeCentralizer)
    (h7a : LinIsQuasisimpleYcode) (h7b : LinNotIsComponentOfYcode) :
    LinIsComponentOfCentralizerTorusSetIff := by
  intro K _ _ _ ζ t ε hK hζ U X
  constructor
  · intro hX
    obtain ⟨e, he, hXe⟩ := exists_isComponentOf_glBlockCentralizer_GL (torusSet ζ t ε U)
      (torusSet_commute ζ t ε U) hX
    obtain ⟨c, hocc, hne, rfl⟩ := h5 ζ t ε hK hζ U he
    rw [h6a ζ t ε hK hζ U c hocc hne] at hXe
    by_cases hadm : PlaneRaw.admissible (.linear ε) c
    · exact ⟨c, hadm, hocc, GGHalf.eq_of_isComponentOf_isQuasisimple
        ((ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2
          (h7a ζ t ε hK hζ c hadm)) hXe⟩
    · exact (h7b ζ t ε hK hζ c hadm X hXe).elim
  · rintro ⟨c, hadm, hocc, rfl⟩
    have hne := keyDim_pos_of_admissible hadm
    have hle := h6c ζ t ε hK hζ U c hocc hne
    exact ⟨hle, IsSubnormal.step hle (h6b ζ t ε hK hζ U c hocc hne) (IsSubnormal.refl _),
      (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2
        (h7a ζ t ε hK hζ c hadm)⟩

end CFSG.StandardType.GGQ2Frame.LinBlocks

end
