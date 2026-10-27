module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP5RC0Input
public import CFSG.LocalAnalysis.StandardType.GGNTPlaneDichotomy

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def ntpNormalForm
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀)
    (D : Subgroup (ModGL .E6 L)) (a : Fin Tag.E6.rank → Lˣ) (n : ModGL .E6 L) : Prop :=
  (∀ i, a i ^ 3 = 1) ∧ rootDiagUnit .E6 a ∈ S.D.torus ∧ rootDiagUnit .E6 a ≠ 1 ∧
    D ≤ S.D.model ∧ n ^ 3 = 1 ∧ rootDiagUnit .E6 a * n = n * rootDiagUnit .E6 a ∧
    D = Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers n ∧
    ∃ (C m : ModGL .E6 L) (hm : m ∈ monomialSubgroup .E6 L),
      C ∈ adjointGroup .E6 L ∧ C * n * C⁻¹ = m ∧
        C * rootDiagUnit .E6 a * C⁻¹ = rootDiagUnit .E6 a ∧
        weylQuotientHom .E6 L ⟨m, hm⟩ ∈ rootCharStabilizerSubgroup a ∧
        weylQuotientHom .E6 L ⟨m, hm⟩ ∉ kernelReflectionGroup a

end CFSG.StandardType.NTPlane

end
