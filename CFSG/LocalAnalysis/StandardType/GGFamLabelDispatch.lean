module

public import CFSG.LocalAnalysis.StandardType.GGFamFieldDispatch
public import CFSG.LocalAnalysis.StandardType.GGFamLabelDefs

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

@[expose] def TypeALabelLane : Prop :=
  ∀
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1) (i : KernelComponent (famCharHom a))
    (hA : 1 ≤ compRank (componentRoots (famCharHom a) i) ∧
      (componentRoots (famCharHom a) i).ncard = compRank (componentRoots (famCharHom a) i) *
        (compRank (componentRoots (famCharHom a) i) + 1))
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)),
    FamLabelAt S (famCharHom a) i

@[expose] def InnerLabelLane : Prop :=
  ∀
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1) (i : KernelComponent (famCharHom a))
    (hnA : ¬ (1 ≤ compRank (componentRoots (famCharHom a) i) ∧
      (componentRoots (famCharHom a) i).ncard = compRank (componentRoots (famCharHom a) i) *
        (compRank (componentRoots (famCharHom a) i) + 1)))
    (hinner : twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (famCharHom a) i)]))
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)),
    FamLabelAt S (famCharHom a) i

@[expose] def OuterDHighLabelLane : Prop :=
  ∀
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1) (i : KernelComponent (famCharHom a))
    (hD : 5 ≤ compRank (componentRoots (famCharHom a) i) ∧
      (componentRoots (famCharHom a) i).ncard =
        2 * compRank (componentRoots (famCharHom a) i) *
          (compRank (componentRoots (famCharHom a) i) - 1))
    (hout : ¬ twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (famCharHom a) i)]))
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)),
    FamLabelAt S (famCharHom a) i

@[expose] def OuterDFourLabelLane : Prop :=
  ∀
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2)
    {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (i : KernelComponent (famCharHom a))
    (hr : compRank (componentRoots (famCharHom a) i) = 4)
    (hc : (componentRoots (famCharHom a) i).ncard = 24)
    (hout : ¬ twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (famCharHom a) i)]))
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)),
    FamLabelAt S (famCharHom a) i

@[expose] def OuterELabelLane : Prop :=
  ∀
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2)
    {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (i : KernelComponent (famCharHom a))
    (hE : 6 ≤ compRank (componentRoots (famCharHom a) i) ∧
      (componentRoots (famCharHom a) i).ncard =
        eRootCount (compRank (componentRoots (famCharHom a) i)))
    (hout : ¬ twistInner (componentRoots (famCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
        (componentRoots (famCharHom a) i)]))
    (hq : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i)),
    FamLabelAt S (famCharHom a) i

theorem langFamRatLabel_of_lanes
    (hTypeA : TypeALabelLane) (hInner : InnerLabelLane) (hDHigh : OuterDHighLabelLane)
    (hDFour : OuterDFourLabelLane) (hE : OuterELabelLane) :
    ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] (p₀ : ℕ) (S : LangSetup τ L p₀),
      (τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
      ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (ι : Type) (a : ι → Fin τ.rank → Lˣ),
        (∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) → (∀ u j, a u j ^ p = 1) →
        (∃ u, rootDiagUnit τ (a u) ≠ 1) → ∀ i : KernelComponent (famCharHom a),
          CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) →
          FamLabelAt S (famCharHom a) i := by
  intro τ L _ _ _ p₀ S hτ p hp hp2 ι a hT hap h1 i hq
  rcases fam_lane_cases hτ S hp hp2 hT hap h1 i with
    ⟨hA⟩ | ⟨hnA, hinner⟩ | ⟨hD, hout⟩ | ⟨hr, hc, hout⟩ | ⟨hτ', hE', hout⟩
  · exact hTypeA hτ S hp hT hap h1 i hA hq
  · exact hInner hτ S hp hT hap h1 i hnA hinner hq
  · exact hDHigh hτ S hp hT hap h1 i hD hout hq
  · exact hDFour hτ S hp hp2 hT hap i hr hc hout hq
  · exact hE hτ' S hp hp2 hT hap i hE' hout hq

end CFSG.StandardType.TableCRes
