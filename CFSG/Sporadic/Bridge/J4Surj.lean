module

public import CFSG.Sporadic.J4
public import CFSG.Sporadic.Bridge.Common
public import CFSG.Sporadic.Bridge.J4Data
public import CFSG.Sporadic.Presentation.J4
public meta import CFSG.Sporadic.Bridge.J4Data
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Sporadic.Bridge.J4SurjInputs
public import Certificates.Certificate9212
public import Certificates.Certificate3017
public import Certificates.Certificate3084
public import Certificates.Certificate9123
public import Certificates.Certificate10095
public import Certificates.Certificate9215
public import Certificates.Certificate9357
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Sporadic.Bridge.TwoGen
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.M24Exact
public import Certificates.Certificate10095Base

public section

namespace CFSG.Sporadic.Bridge.J4

open CFSG.Sporadic.J4 TauCeti

private theorem presentation_eq : SporadicName.J4.presentation = Sporadic.j4Presentation := rfl

@[expose] noncomputable def img : ℕ → J :=
  Classical.choose Certificates.certificate9212

theorem hrel :
    ∀ v ∈ (Sporadic.j4Presentation).relatorLetters, CFSG.Sporadic.Bridge.wordProd img v = 1 :=
  (Classical.choose_spec Certificates.certificate9212).1

theorem closure_img : Subgroup.closure {img 0, img 1, img 2} = ⊤ :=
  (Classical.choose_spec Certificates.certificate9212).2

noncomputable def φ : (Sporadic.j4Presentation).Group →* J :=
  presHom _ img hrel

theorem generatorCount_eq : (Sporadic.j4Presentation).generatorCount = 3 := by
  simp [GroupPresentation.generatorCount]

theorem φ_surjective : Function.Surjective φ := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← closure_img, Subgroup.closure_le]
  have hk : ∀ k < 3, img k ∈ φ.range := fun k hk =>
    ⟨presGen _ k, presHom_presGen _ _ _ (by rw [generatorCount_eq]; exact hk)⟩
  rintro _ (rfl | rfl | rfl)
  · exact hk 0 (by omega)
  · exact hk 1 (by omega)
  · exact hk 2 (by omega)

theorem card_J : Nat.card J = 86775571046077562880 := by
  rw [← Nat.card_congr (seedEquiv j4Facts.mat).toEquiv, card_J4]

theorem nonempty_mulEquiv_of_card_le
    (hfin : Finite SporadicName.J4.Group)
    (hcard : Nat.card SporadicName.J4.Group ≤ 86775571046077562880) :
    Nonempty (Blueprint.NativeSporadic.J4 ≃* SporadicName.J4.Group) := by
  revert hfin hcard
  change Finite SporadicName.J4.presentation.Group →
    Nat.card SporadicName.J4.presentation.Group ≤ 86775571046077562880 →
    Nonempty (Blueprint.NativeSporadic.J4 ≃* SporadicName.J4.presentation.Group)
  rw [presentation_eq]
  intro hfin hcard
  obtain ⟨e⟩ := nonempty_mulEquiv_of_surjective φ φ_surjective hcard card_J.symm.le
  exact ⟨(seedEquiv j4Facts.mat).trans e⟩

theorem nonempty_mulEquiv :
    Nonempty (Blueprint.NativeSporadic.J4 ≃* SporadicName.J4.Group) :=
  nonempty_mulEquiv_of_card_le Presentation.J4.finite_card_le.1 Presentation.J4.finite_card_le.2

end CFSG.Sporadic.Bridge.J4
