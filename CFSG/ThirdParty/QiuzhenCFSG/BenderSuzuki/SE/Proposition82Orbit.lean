module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Interfaces

namespace CFSG
end CFSG
open CFSG

/-!
# Orbit and point-stabilizer coset transport for Proposition 8.2

This file identifies the source-facing `F`-orbit of a chosen point with the
canonical left cosets of its point stabilizer.  The final theorem transports
double transitivity on the orbit to the two-pretransitivity statement used by
Theorem 2.
-/

noncomputable section

namespace CFSG.BenderSuzuki

universe u v

/-- The source-facing orbit of `alpha` is canonically equivalent to the left
cosets of its stabilizer inside `F`. -/
public noncomputable def inOrbitEquivQuotientPointStabilizer
    {X : Type u} {Omega : Type v} [Group X] [MulAction X Omega]
    (F : Subgroup X) (alpha : Omega) :
    {omega : Omega // InOrbit F alpha omega} ≃
      F ⧸ pointStabilizerIn F alpha := by
  letI : MulAction F Omega := MulAction.compHom Omega F.subtype
  have hstab : MulAction.stabilizer F alpha = pointStabilizerIn F alpha := by
    ext f
    change (f : X) • alpha = alpha ↔ (f : X) • alpha = alpha
    rfl
  change {omega : Omega // omega ∈ MulAction.orbit F alpha} ≃
    F ⧸ MulAction.stabilizer F alpha
  exact MulAction.orbitEquivQuotientStabilizer F alpha

/-- The inverse orbit/coset equivalence commutes with the `F`-action, after
forgetting the orbit-membership proof. -/
@[simp] public theorem inOrbitEquivQuotientPointStabilizer_symm_smul_val
    {X : Type u} {Omega : Type v} [Group X] [MulAction X Omega]
    (F : Subgroup X) (alpha : Omega) (f : F)
    (q : F ⧸ pointStabilizerIn F alpha) :
    (((inOrbitEquivQuotientPointStabilizer F alpha).symm
        (f • q) : {omega : Omega // InOrbit F alpha omega}) : Omega) =
      (f : X) •
        (((inOrbitEquivQuotientPointStabilizer F alpha).symm q :
          {omega : Omega // InOrbit F alpha omega}) : Omega) := by
  letI : MulAction F Omega := MulAction.compHom Omega F.subtype
  change MulAction.ofQuotientStabilizer F alpha (f • q) =
    (f : X) • MulAction.ofQuotientStabilizer F alpha q
  exact MulAction.ofQuotientStabilizer_smul F alpha f q

/-- Source-facing double transitivity on the orbit of `alpha` gives the
two-pretransitive point-stabilizer coset action required by Theorem 2. -/
public theorem coset_isTwoPretransitive_of_isTwoTransitiveOn_orbit
    {X : Type u} {Omega : Type v} [Group X] [MulAction X Omega]
    (F : Subgroup X) (alpha : Omega)
    (htwo : IsTwoTransitiveOn F {omega : Omega | InOrbit F alpha omega}) :
    MulAction.IsMultiplyPretransitive F
      (F ⧸ pointStabilizerIn F alpha) 2 := by
  rw [MulAction.is_two_pretransitive_iff]
  intro a b c d hab hcd
  let e := inOrbitEquivQuotientPointStabilizer F alpha
  let ao := e.symm a
  let bo := e.symm b
  let co := e.symm c
  let d_o := e.symm d
  have habo : (ao : Omega) ≠ (bo : Omega) := by
    intro h
    apply hab
    apply e.symm.injective
    exact Subtype.ext h
  have hcdo : (co : Omega) ≠ (d_o : Omega) := by
    intro h
    apply hcd
    apply e.symm.injective
    exact Subtype.ext h
  obtain ⟨f, hfac, hfbd⟩ :=
    htwo ao.property bo.property co.property d_o.property habo hcdo
  refine ⟨f, ?_, ?_⟩
  · apply e.symm.injective
    apply Subtype.ext
    simpa [e, ao, co] using hfac
  · apply e.symm.injective
    apply Subtype.ext
    simpa [e, bo, d_o] using hfbd

end CFSG.BenderSuzuki
