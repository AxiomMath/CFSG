module

public import CFSG.Sporadic.Ly
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Presentation.Ly
public meta import CFSG.Sporadic.Bridge.LyData
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Certificate9120
public import Certificates.Certificate9213
public import Certificates.Certificate3085
public import CFSG.Sporadic.Bridge.HomSurj
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Certificates.CosetTableShort
public import CFSG.Sporadic.HN.LevelChainSpec
public import CFSG.Sporadic.Ly.ActionBase
public import CFSG.Sporadic.Ly.CertificateBase
public import CFSG.Sporadic.Ly.FaithSpec
public import CFSG.Sporadic.Ly.OrbitSpec
public import CFSG.Sporadic.Ly.Simple
public import CFSG.Sporadic.LyBase
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Schreier.LyChain11
public import CFSG.Sporadic.Th.F2Spec
public import CFSG.Sporadic.Th.OrbitSpec
public import Certificates.Certificate3085Base
public import Certificates.Certificate9213Base

public section

namespace CFSG.Sporadic.Bridge.Ly

open CFSG.Sporadic.Ly CFSG.Sporadic.Bridge.SurjD.Native TauCeti

theorem bridge_hom :
    ∃ φ : Sporadic.Lyons.presentation.Group →* GL (Fin 111) (ZMod 5),
      ∀ g : GL (Fin 111) (ZMod 5), g.val = mA ∨ g.val = mB → g ∈ φ.range :=
  Certificates.certificate9213

private theorem presentation_eq :
    SporadicName.Ly.presentation = Sporadic.Lyons.presentation := rfl

theorem generatorCount_eq : Sporadic.Lyons.presentation.generatorCount = lySpec.m := by
  simp [GroupPresentation.generatorCount, lySpec]

theorem relatorLetters_eq : Sporadic.Lyons.presentation.relatorLetters = lySpec.rels := by
  simp only [lySpec, lyRels, GroupPresentation.relatorLetters_def,
    GroupPresentation.relators_def, Sporadic.Lyons.presentation_transcribed, Relator.commInvInv,
    Relator.conj, Relator.div, List.map_cons, List.map_nil, Relator.toWord_gen,
    Relator.toWord_inv, Relator.toWord_mul, Relator.toWord_pow, Relator.toWord_comm]
  rfl

theorem nonempty_mulEquiv_of_card_le
    (hfin : Finite SporadicName.Ly.Group)
    (hcard : Nat.card SporadicName.Ly.Group ≤ 51765179004000000) :
    Nonempty (Blueprint.NativeSporadic.Ly ≃* SporadicName.Ly.Group) := by
  revert hfin hcard
  show Finite SporadicName.Ly.presentation.Group →
    Nat.card SporadicName.Ly.presentation.Group ≤ 51765179004000000 →
    Nonempty (Blueprint.NativeSporadic.Ly ≃* SporadicName.Ly.presentation.Group)
  rw [presentation_eq]
  intro hfin hcard
  obtain ⟨φ, hφ⟩ := bridge_hom
  have hJ : J ≤ φ.range := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    exacts [hφ _ (Or.inl rfl), hφ _ (Or.inr rfl)]
  obtain ⟨e⟩ := nonempty_mulEquiv_of_le_range φ hJ hcard (le_of_eq card_J.symm)
  exact ⟨lyEquivJ.trans e⟩

theorem nonempty_mulEquiv :
    Nonempty (Blueprint.NativeSporadic.Ly ≃* SporadicName.Ly.Group) :=
  nonempty_mulEquiv_of_card_le Presentation.Ly.finite_card_le.1 Presentation.Ly.finite_card_le.2

end CFSG.Sporadic.Bridge.Ly
