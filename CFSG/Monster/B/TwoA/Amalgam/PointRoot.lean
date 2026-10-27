module

public import CFSG.Monster.B.TwoA.Amalgam.StdQuot
public import CFSG.Monster.B.TwoA.Amalgam.PointRootCore

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.E6.StdF4

theorem native_F4_point_root_involution_intertwiner :
    ∃ (θ : Eam ⧸ Subgroup.zpowers cE' ≃* GStar) (f : Chamber ≃ C2E6Std.stdChamber),
      (∀ (i : Fin Tag.F4.rank) (x y : Chamber), chamberCS.adj i x y ↔
        stdDistanceF4 (f x) (f y) = 1 ∨ stdDistanceF4 (f x) (f y) = (coxeterSystem .F4).simple i) ∧
      (∀ δ : Chamber → Chamber → WeylGroup .F4, IsWeylDistanceBuilding (coxeterSystem .F4) δ →
        (∀ (i : Fin Tag.F4.rank) (x y : Chamber),
          chamberCS.adj i x y ↔ δ x y = 1 ∨ δ x y = (coxeterSystem .F4).simple i) →
        ∀ x y, stdDistanceF4 (f x) (f y) = δ x y) ∧
      (∀ (z : Chamber) (e : Eam), f (chamberMul z e⁻¹) = θ (QuotientGroup.mk e) • f z) ∧
      f '' vtx 0 baseChamber = residue ncs stdDistance firstJ c₀ ∧
      θ (QuotientGroup.mk xhatEam) = rootStar ∧
      (∀ e : Eam, ∃ R : typeOneVertex, (R : Set C2E6Std.stdChamber) = f '' vtx 0 (chamberOf e) ∧
        SemidirectProduct.inl (vertexRoot R) = θ (QuotientGroup.mk (e⁻¹ * xhatEam * e))) ∧
      (∀ e e' : Eam, vtx 0 (chamberOf e) = vtx 0 (chamberOf e') ↔
        (QuotientGroup.mk (e⁻¹ * xhatEam * e) : Eam ⧸ Subgroup.zpowers cE') =
          QuotientGroup.mk (e'⁻¹ * xhatEam * e')) ∧
      ∀ e e' : Eam,
        ((∃ x, (vtx 0 (chamberOf e) ∩ vtx 3 x).Nonempty ∧
            (vtx 0 (chamberOf e') ∩ vtx 3 x).Nonempty) ↔
          Commute (QuotientGroup.mk (e⁻¹ * xhatEam * e) : Eam ⧸ Subgroup.zpowers cE')
            (QuotientGroup.mk (e'⁻¹ * xhatEam * e'))) := by
  obtain ⟨θ₁, f₁, h1, h2, h3⟩ := short_F4_standard_twisted_E6_quotient
  exact point_root_of_quotient θ₁ f₁ h1 h2 h3

end CFSG.Monster.B.TwoA.Amalgam
