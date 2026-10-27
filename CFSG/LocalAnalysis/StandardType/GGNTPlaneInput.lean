module

public import CFSG.LocalAnalysis.StandardType.GGNTPlaneNormalForm
public import CFSG.LocalAnalysis.StandardType.MarkingDict

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

@[expose] def OrderThreeOutsideConnected
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup .E6 L p₀) (a : Fin Tag.E6.rank → Lˣ) (n : ModGL .E6 L) : Prop :=
  (∀ i, a i ^ 3 = 1) ∧ rootDiagUnit .E6 a ∈ S.D.torus ∧ rootDiagUnit .E6 a ≠ 1 ∧
    n ∈ S.D.model ∧ n ^ 3 = 1 ∧ rootDiagUnit .E6 a * n = n * rootDiagUnit .E6 a ∧
    ∃ (C m : ModGL .E6 L) (hm : m ∈ monomialSubgroup .E6 L),
      C ∈ adjointGroup .E6 L ∧ C * n * C⁻¹ = m ∧
        C * rootDiagUnit .E6 a * C⁻¹ = rootDiagUnit .E6 a ∧
        weylQuotientHom .E6 L ⟨m, hm⟩ ∈ rootCharStabilizerSubgroup a ∧
        weylQuotientHom .E6 L ⟨m, hm⟩ ∉ kernelReflectionGroup a

@[expose] def LangNontoralStructure :
    Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup .E6 L p₀)
    (a : Fin Tag.E6.rank → Lˣ) (n : ModGL .E6 L),
    OrderThreeOutsideConnected S a n → (rootCharKernel a).ncard = 18 →
      Nat.card (KernelComponent (rootCharHom a)) = 3 ∧
        ∃ σ : Equiv.Perm (KernelComponent (rootCharHom a)), σ ≠ 1 ∧ σ ^ 3 = 1 ∧
          (∀ i, (componentRootSpan L (rootCharHom a) i).map (MulAut.conj n).toMonoidHom =
            componentRootSpan L (rootCharHom a) (σ i)) ∧
          (∀ i j, ⇑S.ρ '' componentRoots (rootCharHom a) i = componentRoots (rootCharHom a) j →
            ⇑S.ρ '' componentRoots (rootCharHom a) (σ i) =
              componentRoots (rootCharHom a) (σ j)) ∧
          (∀ J : Subgroup (ModGL .E6 L),
            J ≤ S.Γ ⊓ Subgroup.centralizer ({rootDiagUnit .E6 a} : Set (ModGL .E6 L)) →
              CFSG.IsQuasisimple ↥J →
                J ≤ ⨆ i, rationalComponent S.ρ S.Γ (rootCharHom a) i)

@[expose] def LangNontoralA2Descent :
    Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup .E6 L p₀)
    (a : Fin Tag.E6.rank → Lˣ) (n : ModGL .E6 L),
    OrderThreeOutsideConnected S a n → (rootCharKernel a).ncard = 18 →
      (∀ i : KernelComponent (rootCharHom a),
        componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 3) →
      ∀ K : Subgroup (ModGL .E6 L),
        IsComponentOf K (S.Γ ⊓ Subgroup.centralizer
          ((Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers n : Subgroup (ModGL .E6 L)) :
            Set (ModGL .E6 L))) →
        GGCompFieldAt S.D.q K

@[expose] def LangNontoralD4Fixed :
    Prop :=
  ∀ (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup .E6 L p₀)
    (a : Fin Tag.E6.rank → Lˣ) (n : ModGL .E6 L),
    OrderThreeOutsideConnected S a n → (rootCharKernel a).ncard = 24 →
      ∀ K : Subgroup (ModGL .E6 L),
        IsComponentOf K (S.Γ ⊓ Subgroup.centralizer
          ((Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers n : Subgroup (ModGL .E6 L)) :
            Set (ModGL .E6 L))) →
        (S.D.q ≠ 2 → ∃ f : ℕ, 2 ^ f = S.D.q ∧
          (LieModel (↥K ⧸ Subgroup.center ↥K) .G2 0 2 f ∨
            LieModel (↥K ⧸ Subgroup.center ↥K) .PSL 3 2 f ∨
            LieModel (↥K ⧸ Subgroup.center ↥K) .PSU 3 2 f)) ∧
        (S.D.q = 2 → Nat.card K = 6048 ∧ Nat.card (↥K ⧸ Subgroup.center ↥K) = 6048)

@[expose] def LangNontoralCentralizerInput :
    Prop :=
  LangNontoralStructure ∧ LangNontoralA2Descent ∧ LangNontoralD4Fixed

theorem OrderThreeOutsideConnected.of_ntpNormalForm
    {L : Type} [Field L]
    [IsAlgClosed L] {p₀ : ℕ} {S : LangSetup .E6 L p₀} {D : Subgroup (ModGL .E6 L)}
    {a : Fin Tag.E6.rank → Lˣ} {n : ModGL .E6 L} (h : ntpNormalForm S D a n) :
    OrderThreeOutsideConnected S a n ∧
      D = Subgroup.zpowers (rootDiagUnit .E6 a) ⊔ Subgroup.zpowers n := by
  obtain ⟨h3, hT, h1, hD, hn3, hcomm, hDeq, C, m, hm, hC, hCn, hCd, hW1, hW2⟩ := h
  refine ⟨⟨h3, hT, h1, ?_, hn3, hcomm, C, m, hm, hC, hCn, hCd, hW1, hW2⟩, hDeq⟩
  apply hD
  rw [hDeq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers n)

end CFSG.StandardType.NTPlane

end
