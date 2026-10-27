module

public import CFSG.Monster.Generated.FiniteSimple
public import CFSG.YGroups.Y443.CentralProjection
public import CFSG.YGroups.Y443.Native.Hom

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster.Generated CFSG.Open

theorem fM_injective_of
    (hinj : Set.InjOn fM y443H) (hxL : fM y443X ∉ y443H.map fM)
    (hedge : ∀ h ∈ y443H.map fM, fM y443X * h * fM y443X ∈ y443H.map fM →
      ∃ k ∈ y443H, y443X * k * y443X ∈ y443H ∧ fM k = h)
    (htri : ∀ (v : Quotient (QuotientGroup.rightRel (y443H.map fM)))
      (p : (rcGraph (y443H.map fM) (fM y443X)).Walk v v),
      MarkedHomotopic (yTri (y443H.map fM) (fM y443X) (fM y443Y)) p SimpleGraph.Walk.nil) :
    Function.Injective fM := by
  obtain ⟨-, -, -, -, -, hT, -, hgen, hy, hxy, -, -⟩ := y443_central_quotient_source
  have hx : y443X * y443X = 1 := hT _
  exact injective_of_marked_homotopy fM hx hgen hinj hxL hedge
    (rcHom_liftsMarked_yTri fM hx hy hxy hxL) htri

noncomputable def fM_equiv_of
    (hinj : Set.InjOn fM y443H) (hxL : fM y443X ∉ y443H.map fM)
    (hedge : ∀ h ∈ y443H.map fM, fM y443X * h * fM y443X ∈ y443H.map fM →
      ∃ k ∈ y443H, y443X * k * y443X ∈ y443H ∧ fM k = h)
    (htri : ∀ (v : Quotient (QuotientGroup.rightRel (y443H.map fM)))
      (p : (rcGraph (y443H.map fM) (fM y443X)).Walk v v),
      MarkedHomotopic (yTri (y443H.map fM) (fM y443X) (fM y443Y)) p SimpleGraph.Walk.nil)
    (hsurj : Function.Surjective fM) : MonsterY443Derived ≃* Gmat :=
  MulEquiv.ofBijective fM ⟨fM_injective_of hinj hxL hedge htri, hsurj⟩

theorem fam_m_simplicity_of
    (hinj : Set.InjOn fM y443H) (hxL : fM y443X ∉ y443H.map fM)
    (hedge : ∀ h ∈ y443H.map fM, fM y443X * h * fM y443X ∈ y443H.map fM →
      ∃ k ∈ y443H, y443X * k * y443X ∈ y443H ∧ fM k = h)
    (htri : ∀ (v : Quotient (QuotientGroup.rightRel (y443H.map fM)))
      (p : (rcGraph (y443H.map fM) (fM y443X)).Walk v v),
      MarkedHomotopic (yTri (y443H.map fM) (fM y443X) (fM y443Y)) p SimpleGraph.Walk.nil)
    (hsurj : Function.Surjective fM) : IsSimpleGroup MonsterY443Derived := by
  have := generated_rational_group_finite_simple.2.1
  exact (fM_equiv_of hinj hxL hedge htri hsurj).isSimpleGroup

end CFSG.YGroups.Y443
