module

public import CFSG.Sporadic.Fi24.Simple
public import CFSG.Sporadic.Presentation.Fi24PrimeExact
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.Bridge.Fi24Data
public meta import CFSG.Sporadic.Bridge.Fi24Data
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Certificate9113
public import Certificates.Certificate9207
public import Certificates.Certificate1016
public import CFSG.Sporadic.Bridge.HomSurj
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Sporadic.Fi24.Faithful
public import CFSG.Sporadic.Fi24.SepSpec
public import Certificates.Certificate1016Base

public section

namespace CFSG.Sporadic.Bridge.Fi24

open CFSG.Sporadic.Fi24 TauCeti

theorem bridge_x :
    ∃ x : ℕ → GL (Fin 781) (ZMod 3),
      (∀ k < 11, (x k : Matrix (Fin 781) (Fin 781) (ZMod 3)) = CFSG.KD.Fi24Img.img k) ∧
      (∀ k, 11 ≤ k → x k = 1) ∧
      (∀ v ∈ Sporadic.fi24PrimePresentation.relatorLetters, wordProd x v = 1) ∧
      ∀ g : GL (Fin 781) (ZMod 3), g.val = mA ∨ g.val = mB →
        g ∈ Subgroup.closure (x '' Set.Iio 11) :=
  Certificates.certificate9207

theorem generatorCount_eq : Sporadic.fi24PrimePresentation.generatorCount = 11 := by
  simp [GroupPresentation.generatorCount, Sporadic.fi24PrimePresentation_generatorNames]

theorem closure_le_range {x : ℕ → GL (Fin 781) (ZMod 3)}
    (hrel : ∀ v ∈ Sporadic.fi24PrimePresentation.relatorLetters, wordProd x v = 1) :
    Subgroup.closure (x '' Set.Iio 11) ≤ (presHom _ x hrel).range := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact ⟨presGen _ k, presHom_presGen _ _ _ (by rw [generatorCount_eq]; exact hk)⟩

theorem bridge_hom :
    ∃ φ : Sporadic.fi24PrimePresentation.Group →* GL (Fin 781) (ZMod 3),
      ∀ g : GL (Fin 781) (ZMod 3), g.val = mA ∨ g.val = mB → g ∈ φ.range := by
  obtain ⟨x, -, -, hrel, hcl⟩ := bridge_x
  exact ⟨presHom _ x hrel, fun g hg => closure_le_range hrel (hcl g hg)⟩

private theorem presentation_eq :
    SporadicName.Fi24Prime.presentation = Sporadic.fi24PrimePresentation := rfl

theorem J_le_range
    {φ : Sporadic.fi24PrimePresentation.Group →* GL (Fin 781) (ZMod 3)}
    (hφ : ∀ g : GL (Fin 781) (ZMod 3), g.val = mA ∨ g.val = mB → g ∈ φ.range) : J ≤ φ.range := by
  change Subgroup.closure {gA, gB} ≤ φ.range
  rw [Subgroup.closure_le]
  rintro x (rfl | rfl)
  · exact hφ _ (Or.inl (by simp))
  · exact hφ _ (Or.inr (by simp))

theorem nonempty_mulEquiv_of_card_le
    (hfin : Finite SporadicName.Fi24Prime.Group)
    (hcard : Nat.card SporadicName.Fi24Prime.Group ≤ 1255205709190661721292800) :
    Nonempty (Blueprint.NativeSporadic.Fi24prime ≃* SporadicName.Fi24Prime.Group) := by
  revert hfin hcard
  show Finite SporadicName.Fi24Prime.presentation.Group →
    Nat.card SporadicName.Fi24Prime.presentation.Group ≤ 1255205709190661721292800 →
    Nonempty (Blueprint.NativeSporadic.Fi24prime ≃* SporadicName.Fi24Prime.presentation.Group)
  rw [presentation_eq]
  intro hfin hcard
  obtain ⟨φ, hφ⟩ := bridge_hom
  obtain ⟨e⟩ := nonempty_mulEquiv_of_le_range φ (J_le_range hφ) hcard (le_of_eq card_J.symm)
  exact ⟨fi24EquivJ.trans e⟩

theorem nonempty_mulEquiv :
    Nonempty (Blueprint.NativeSporadic.Fi24prime ≃* SporadicName.Fi24Prime.Group) :=
  nonempty_mulEquiv_of_card_le Presentation.Fi24Prime.finite_card_le_exact.1
    Presentation.Fi24Prime.finite_card_le_exact.2

end CFSG.Sporadic.Bridge.Fi24
