module

public import CFSG.LocalAnalysis.StandardType.GGFamRatComp
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Inputs
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ULang
public import CFSG.LocalAnalysis.StandardType.GGExcCompSLDefs
public import CFSG.LocalAnalysis.StandardType.GGLangFamily
public import CFSG.LocalAnalysis.StandardType.GGLangAlgebraicRestriction
public import CFSG.LocalAnalysis.StandardType.GGFamTrivialRoots
public import CFSG.LocalAnalysis.StandardType.GGFamTrivialGamma
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6FCover

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (isComponentOf_eq_of_isQuasisimple)

theorem langFamilyCompFieldSL_trivial
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ : ℕ} (S : LangSetup τ L p₀) {ι : Type} (a : ι → Fin τ.rank → Lˣ)
    (h1 : ∀ u, rootDiagUnit τ (a u) = 1) (K : Subgroup (ModGL τ L))
    (hK : IsComponentOf K
      (S.Γ ⊓ Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u)))) :
    ∃ i : KernelComponent (famCharHom a),
      K ≤ rootSpan τ L (rationalRootsM S.ρ (famCharHom a) i) ∧
        CFSG.StandardType.GGCompFieldAtSL
          (S.D.q ^ componentOrbitLength S.ρ (componentRoots (famCharHom a) i)) K := by
  classical
  have ha1 : ∀ u, a u = 1 := fun u => rootDiagUnit_injective (by rw [h1 u, rootDiagUnit_one])
  have hχ : ∀ γ : Fin τ.rank → ℤ, famCharHom a (Multiplicative.ofAdd γ) = 1 := by
    intro γ
    funext u
    change rootChar (a u) γ = 1
    rw [ha1 u, rootChar_one_tuple']
  have hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus := fun u => by
    rw [h1 u]
    exact Subgroup.one_mem _
  have hap : ∀ u j, a u j ^ 3 = 1 := fun u j => by rw [ha1 u]; simp
  have h3L : ((3 : ℕ) : L) ≠ 0 := by
    intro h
    have h2 : (2 : ℕ) ∣ 3 := (CharP.cast_eq_zero_iff L 2 3).1 h
    norm_num at h2
  obtain ⟨i, hi⟩ := CFSG.StandardType.LangRat.langFamilyComponentsInRootSpan
    τ L p₀ 3 S (Or.inr hτ) Nat.prime_three (by norm_num) h3L ι a hT hap K hK
  refine ⟨i, hi, ?_⟩
  have hcent : Subgroup.centralizer (Set.range fun u => rootDiagUnit τ (a u)) = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    rw [Subgroup.mem_centralizer_iff]
    rintro y ⟨u, rfl⟩
    simp [h1 u]
  have hK' : IsComponentOf K S.Γ := by simpa [hcent] using hK
  obtain ⟨t, f, -, -, hqΓ, -⟩ := famTrivial_Γ_data hτ S
  have hKΓ : K = S.Γ := isComponentOf_eq_of_isQuasisimple hK' hqΓ
  rw [famTrivial_componentOrbitLength_eq_one hτ S.ρ (fun γ => S.frob.isRoot_iff γ)
    (famCharHom a) hχ i, pow_one, hKΓ]
  exact famTrivial_ggCompFieldAtSL_Γ hτ S

end CFSG.StandardType.TableCRes
