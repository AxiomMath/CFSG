module

public import CFSG.LocalAnalysis.StandardType.GGFamTame
public import CFSG.LocalAnalysis.StandardType.GGFamLabelDispatch
public import CFSG.LocalAnalysis.StandardType.GGFamLabelTypeA
public import CFSG.LocalAnalysis.StandardType.GGFamLabelInner
public import CFSG.LocalAnalysis.StandardType.GGFamLabelOuterDHigh
public import CFSG.LocalAnalysis.StandardType.GGFamLabelOuterDFour
public import CFSG.LocalAnalysis.StandardType.GGFamLabelOuterE
public import CFSG.LocalAnalysis.StandardType.GGFamLabelIndex
public import CFSG.LocalAnalysis.StandardType.GGFamLabelTrivial

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp

theorem rationalComponentM_eq_of_rationalRootsM_eq
    {τ : Tag} {L : Type} [Field L] {M : Type*} [CommGroup M]
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (Γ : Subgroup (ModGL τ L))
    (χ : Multiplicative (Fin τ.rank → ℤ) →* M) (i j : KernelComponent χ)
    (h : rationalRootsM ρ χ i = rationalRootsM ρ χ j) :
    rationalComponentM ρ Γ χ i = rationalComponentM ρ Γ χ j := by
  unfold rationalComponentM rationalSpanM
  rw [h]

theorem langFamilyCompLabel_exc
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime) (hp2 : p ≠ 2)
    {ι : Type} (a : ι → Fin τ.rank → Lˣ) (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus)
    (hap : ∀ u j, a u j ^ p = 1) {K : Subgroup (ModGL τ L)}
    (hK : IsComponentOf K (S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u))))
    (i : KernelComponent (Pi.monoidHom fun u => rootCharHom (a u)))
    (hKspan : K ≤ rootSpan τ L {γ | ∃ (k : ℕ) (δ : Fin τ.rank → ℤ),
      δ ∈ componentRoots (Pi.monoidHom fun u => rootCharHom (a u)) i ∧
        γ = (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] δ}) :
    ∃ n : ℕ, 2 ^ n = S.D.q ^ componentOrbitLength S.ρ
        (componentRoots (Pi.monoidHom fun u => rootCharHom (a u)) i) ∧
      GGCompLabelAt
        (componentLabel
          (compRank (componentRoots (Pi.monoidHom fun u => rootCharHom (a u)) i))
          (componentRoots (Pi.monoidHom fun u => rootCharHom (a u)) i).ncard
          (twistKindOf S.ρ (componentRoots (Pi.monoidHom fun u => rootCharHom (a u)) i)) n) K := by
  by_cases h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1
  · have hTame : ∀ i : KernelComponent (famCharHom a),
        CFSG.IsQuasisimple (rationalComponentM S.ρ S.Γ (famCharHom a) i) ∨
          Group.IsSolvable (rationalComponentM S.ρ S.Γ (famCharHom a) i) :=
      fun i => langFamTame_of_prime hτ S hp hp2 hT hap h1 i
    obtain ⟨j, hKj, hq⟩ :=
      exists_eq_rationalComponentM_of_isComponentOf S hp hτ hp2 hT hap h1 hTame hK
    have hKq : CFSG.IsQuasisimple ↥K := hKj ▸ hq
    have hjspan : K ≤ rootSpan τ L (rationalRootsM S.ρ (famCharHom a) j) := by
      rw [hKj]
      exact (Subgroup.commutator_le_self _).trans inf_le_left
    have hR := rationalRootsM_eq_of_quasisimple_le_rootSpan S hT i j hKq hKspan hjspan
    have hM := rationalComponentM_eq_of_rationalRootsM_eq S.ρ S.Γ (famCharHom a) i j hR
    have hqi : CFSG.IsQuasisimple ↥(rationalComponentM S.ρ S.Γ (famCharHom a) i) := by
      rw [hM, ← hKj]; exact hKq
    have hKi : K = rationalComponentM S.ρ S.Γ (famCharHom a) i := hKj.trans hM.symm
    exact langFamilyCompLabel_conclusion_of_famLabelAt S i hKi
      (langFamRatLabel_of_lanes langFamRatLabel_typeA langFamRatLabel_inner
        langFamRatLabel_outerD_high langFamRatLabel_outerD_four langFamRatLabel_outerE
        τ L p₀ S hτ p hp hp2 ι a hT hap h1 i hqi)
  · push Not at h1
    exact langFamilyCompLabel_trivial hτ S a h1 i hK

theorem langFamilyCompLabel_holds :
    LangFamilyCompLabel := by
  intro τ L _ _ _ p₀ p S hτ hp hp2 ι a hT hap K hK i hKspan
  exact langFamilyCompLabel_exc (hτ.elim Or.inl fun h => Or.inr (Or.inr h)) S hp hp2 a hT hap hK
    i hKspan

end CFSG.StandardType.TableCRes
