module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.Open

@[expose] def ggTorusRootKer {U : Type*} [Group U] (Δ : UniversalRootDatum U) (p : ℕ)
    (γ : Fin Δ.rank → ℤ) : Set U :=
  {h | h ∈ ggTorus Δ ∧ h ^ p = 1 ∧ Δ.rootGroup γ ≤ Subgroup.centralizer {h}}

@[expose] def GGRootKerStmt :
    Prop :=
  ∀ (t : StatedLieTag) (n f : ℕ), StatedLieAdmissible t n 2 f → 3 ≤ bnRank t n →
    (t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ 2 ^ f - 1 →
    ∀ ν : GGWeyl (ggU t n f).D →* (ggU t n f).K, GGWeylLift (ggU t n f).D ν →
    ∀ (u : GGWeyl (ggU t n f).D) (i : Fin (ggU t n f).D.rank),
      (∀ β ∈ (ggU t n f).D.roots, (ggU t n f).D.rootGroup β ≤
          Subgroup.centralizer (ggTorusRootKer (ggU t n f).D p
            (weylAction (ggU t n f).D.isFiniteType u (Pi.single i 1))) →
        β = weylAction (ggU t n f).D.isFiniteType u (Pi.single i 1) ∨
          β = -weylAction (ggU t n f).D.isFiniteType u (Pi.single i 1)) ∧
      ∀ w : GGWeyl (ggU t n f).D, (∀ h ∈ ggTorusRootKer (ggU t n f).D p
          (weylAction (ggU t n f).D.isFiniteType u (Pi.single i 1)),
          ν w * h * (ν w)⁻¹ * h⁻¹ ∈ Subgroup.center (ggU t n f).K) →
        w = 1 ∨ w = u * (coxeterMatrix (ggU t n f).D.isFiniteType).simple i * u⁻¹

end CFSG.StandardType

end
