module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthBlocksGroup
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksComp
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksIdem
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompPSp
import CFSG.LocalAnalysis.StandardType.GGHalfCentGroup
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates

public section

namespace CFSG.StandardType.GGQ2Frame.OrthBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition Matrix
open CFSG.Open (StatedSp)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma liftSupport_nonempty_of_admissible {t : ℕ} {δ : Fin 2} {c : PlaneRaw.Code t}
    (hc : PlaneRaw.admissible (.orthogonal δ) c) : (liftCode t δ c).support.Nonempty := by
  cases c with
  | zero S =>
    have hδ : δ.val < 2 := δ.isLt
    have hpos : 0 < S.card := by
      rcases hc with ⟨-, h3⟩ | ⟨hodd, h2⟩
      · omega
      · obtain ⟨k, hk⟩ := hodd
        omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    refine ⟨Fin.castAdd δ.val i, ?_⟩
    rw [liftCode, PlaneRaw.Code.support]
    exact Finset.mem_union_left _ (Finset.mem_map.mpr ⟨i, hi, rfl⟩)
  | extension e =>
    have h4 : 4 ≤ (PlaneRaw.Code.extSupport e).card := hc.2
    obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < (PlaneRaw.Code.extSupport e).card by omega)
    refine ⟨Fin.castAdd δ.val i, ?_⟩
    rw [liftCode, PlaneRaw.Code.support, PlaneRaw.mem_extSupport, liftV_apply_castAdd]
    exact (Finset.mem_filter.mp hi).2

theorem orthIsComponentOfCentralizerTorusSetIff_of (hC : OrthIsComponentOfGlBlockCentralizer)
    (h7a : OrthIsQuasisimpleYcode) (h7b : OrthNotIsComponentOfYcode) :
    OrthIsComponentOfCentralizerTorusSetIff := by
  intro K _ _ _ ζ t δ hK hζ U X
  constructor
  · intro hX
    obtain ⟨ε, hε, hXε⟩ := hC (K := K) t δ (oTorusSet ζ t δ U)
      (SpBlocks.torusSet_commute ζ (t + δ.val) (U.map (liftV t δ))) hX
    obtain ⟨c', hocc', hne', rfl⟩ :=
      SpBlocks.spExistsCodeOfIsPrimAdjIdemIn_holds ζ (t + δ.val) hK hζ
        (U.map (liftV t δ)) hε
    obtain ⟨c, rfl⟩ := orthExistsLift_holds t δ U c' hocc'
    have hocc : PlaneRaw.occurs U c :=
      (orthOccursLiftIff_holds t δ U c).mpr hocc'
    rw [orthGlBlockCentralizerPlaneIdem_holds ζ t δ hK hζ U c hocc hne'] at hXε
    by_cases hadm : PlaneRaw.admissible (.orthogonal δ) c
    · exact ⟨c, hadm, hocc, GGHalf.eq_of_isComponentOf_isQuasisimple
        ((ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2
          (h7a ζ t δ hK hζ c hadm)) hXε⟩
    · exact (h7b ζ t δ hK hζ c hadm X hXε).elim
  · rintro ⟨c, hadm, hocc, rfl⟩
    have hne := liftSupport_nonempty_of_admissible hadm
    have hle := orthYcodeLeCentralizer_holds ζ t δ hK hζ U c hocc hne
    exact ⟨hle, IsSubnormal.step hle (orthNormalYcode_holds ζ t δ hK hζ U c hocc hne)
        (IsSubnormal.refl _),
      (ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2
        (h7a ζ t δ hK hζ c hadm)⟩

end CFSG.StandardType.GGQ2Frame.OrthBlocks
