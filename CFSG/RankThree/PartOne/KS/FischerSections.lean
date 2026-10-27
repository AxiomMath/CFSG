module

public import CFSG.RankThree.PartOne.KP.SectionTransfer
public import CFSG.Sporadic.Fi23.Centralizer
public import CFSG.Sporadic.Fi24.ExtFi23

public section

namespace CFSG.RankThree.PartOne

open CFSG.Blueprint.NativeSporadic (Carrier)

theorem hasSection_of_mulEquiv {X X' Y Y' : Type} [Group X] [Group X'] [Group Y] [Group Y']
    (eX : X ≃* X') (eY : Y' ≃* Y) (h : HasSection X' Y') : HasSection X Y := by
  obtain ⟨A', N', hN', ⟨φ⟩⟩ := h
  let ψ : A' ≃* A'.map eX.symm.toMonoidHom := eX.symm.subgroupMap A'
  have hN : (N'.map ψ.toMonoidHom).Normal := hN'.map ψ.toMonoidHom ψ.surjective
  exact ⟨A'.map eX.symm.toMonoidHom, N'.map ψ.toMonoidHom, hN,
    ⟨(QuotientGroup.congr N' (N'.map ψ.toMonoidHom) ψ rfl).symm.trans (φ.trans eY)⟩⟩

theorem hasSection_fi23J_fi22J : HasSection CFSG.Sporadic.Fi23.J CFSG.Sporadic.Fi22.J :=
  ⟨Subgroup.centralizer ({CFSG.Sporadic.Fi23.d} : Set CFSG.Sporadic.Fi23.J),
    Subgroup.center _, inferInstance, ⟨CFSG.Sporadic.Fi23.quotCenterEquiv⟩⟩

theorem hasSection_fi24J_fi23M : HasSection CFSG.Sporadic.Fi24.J CFSG.Sporadic.Fi24.M :=
  ⟨CFSG.Sporadic.Fi24.M, ⊥, inferInstance, ⟨QuotientGroup.quotientBot⟩⟩

theorem hasSection_fi23_fi22_native :
    @HasSection CFSG.Blueprint.NativeSporadic.Fi23 CFSG.Blueprint.NativeSporadic.Fi22
      inferInstance inferInstance :=
  @hasSection_of_mulEquiv CFSG.Blueprint.NativeSporadic.Fi23 CFSG.Sporadic.Fi23.J
    CFSG.Blueprint.NativeSporadic.Fi22 CFSG.Sporadic.Fi22.J inferInstance inferInstance
    inferInstance inferInstance CFSG.Sporadic.Fi23.fi23EquivJ CFSG.Sporadic.Fi22.fi22EquivJ.symm
    hasSection_fi23J_fi22J

theorem hasSection_fi24prime_fi23_native :
    @HasSection CFSG.Blueprint.NativeSporadic.Fi24prime CFSG.Blueprint.NativeSporadic.Fi23
      inferInstance inferInstance :=
  @hasSection_of_mulEquiv CFSG.Blueprint.NativeSporadic.Fi24prime CFSG.Sporadic.Fi24.J
    CFSG.Blueprint.NativeSporadic.Fi23 CFSG.Sporadic.Fi24.M inferInstance inferInstance
    inferInstance inferInstance CFSG.Sporadic.Fi24.fi24EquivJ CFSG.Sporadic.Fi24.fi23Equiv
    hasSection_fi24J_fi23M

theorem hasSection_fi23_fi22 : HasSection (Carrier .Fi23) (Carrier .Fi22) :=
  hasSection_fi23_fi22_native

theorem hasSection_fi24prime_fi23 : HasSection (Carrier .Fi24Prime) (Carrier .Fi23) :=
  hasSection_fi24prime_fi23_native

end CFSG.RankThree.PartOne
