
module

public import CFSG.Sporadic.Bridge.RuSurjBase
import all CFSG.Sporadic.Bridge.RuSurjBase

public import CFSG.Sporadic.Ru
public import CFSG.Sporadic.Bridge.VecSurj
public import CFSG.Sporadic.Presentation.RuExact
public import Certificates.Data.CFSGNative.Bridge.SurjD
public meta import Certificates.Data.CFSGNative.Bridge.SurjD
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Sporadic.Presentation.RuExactInputs
public import Certificates.Certificate9218
public import Certificates.Data.CFSGNative.Ru.Data
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Sporadic.Bridge.Ru

open CFSG.Sporadic.SmallF2 CFSG.Sporadic.Bridge.SurjD.Native TauCeti

open CFSG.Sporadic.Bridge.VecSurj in
theorem bridge_facts :
    (∀ v ∈ Sporadic.ruPresentation.relatorLetters,
      wordProd (img ruSpec (seedG CFSG.Sporadic.Ru.Native.ruData)) v = 1) ∧
    (∀ i < 2, ∀ z ∈ ruSpec.surjWords[i]!, z ≠ 0 ∧ z.natAbs ≤ 3) ∧
    CFSG.Sporadic.Th.wordG (imgG ruSpec (seedG CFSG.Sporadic.Ru.Native.ruData))
      ruSpec.surjWords[0]! = a CFSG.Sporadic.Ru.Native.ruData ∧
    CFSG.Sporadic.Th.wordG (imgG ruSpec (seedG CFSG.Sporadic.Ru.Native.ruData))
      ruSpec.surjWords[1]! = b CFSG.Sporadic.Ru.Native.ruData :=
  Certificates.certificate9218

theorem presHom_surjective
    (hrel : ∀ v ∈ Sporadic.ruPresentation.relatorLetters, wordProd
      (CFSG.Sporadic.Bridge.VecSurj.img ruSpec
        (CFSG.Sporadic.Bridge.VecSurj.seedG CFSG.Sporadic.Ru.Native.ruData)) v = 1) :
    Function.Surjective (presHom Sporadic.ruPresentation
      (CFSG.Sporadic.Bridge.VecSurj.img ruSpec
        (CFSG.Sporadic.Bridge.VecSurj.seedG CFSG.Sporadic.Ru.Native.ruData)) hrel) := by
  obtain ⟨-, hlet, hA, hB⟩ := bridge_facts
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_ab CFSG.Sporadic.Ru.Native.ruData,
    Subgroup.closure_le]
  rintro x (rfl | rfl)
  · rw [← hA]
    exact CFSG.Sporadic.Bridge.VecSurj.wordG_imgG_mem _ _ generatorCount_eq hrel
      (hlet 0 (by decide))
  · rw [← hB]
    exact CFSG.Sporadic.Bridge.VecSurj.wordG_imgG_mem _ _ generatorCount_eq hrel
      (hlet 1 (by decide))

theorem nonempty_mulEquiv_of_card_le
    (hfin : Finite SporadicName.Ru.Group)
    (hcard : Nat.card SporadicName.Ru.Group ≤ 145926144000) :
    Nonempty (Blueprint.NativeSporadic.Ru ≃* SporadicName.Ru.Group) := by
  revert hfin hcard
  show Finite SporadicName.Ru.presentation.Group →
    Nat.card SporadicName.Ru.presentation.Group ≤ 145926144000 →
    Nonempty (Blueprint.NativeSporadic.Ru ≃* SporadicName.Ru.presentation.Group)
  rw [presentation_eq]
  intro hfin hcard
  obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective _ (presHom_surjective bridge_facts.1) hcard
    (le_of_eq card_J.symm)
  exact ⟨nativeEquiv.trans e⟩

theorem nonempty_mulEquiv :
    Nonempty (Blueprint.NativeSporadic.Ru ≃* SporadicName.Ru.Group) :=
  nonempty_mulEquiv_of_card_le Presentation.Ru.finite_card_le.1 Presentation.Ru.finite_card_le.2

end CFSG.Sporadic.Bridge.Ru
