module

public import CFSG.LocalAnalysis.StandardType.GGFamComponent
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.OddKernelOrbit

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem famF4_orbit
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {p₀ p : ℕ} (S : LangSetup Tag.F4 L p₀)
    (hp : p.Prime) (hp2 : p ≠ 2) {ι : Type} {a : ι → Fin Tag.F4.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit Tag.F4 (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (i : KernelComponent (famCharHom a)) :
    (S.ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
        (componentRoots (famCharHom a) i) = componentRoots (famCharHom a) i ∧
      componentOrbitLength S.ρ (componentRoots (famCharHom a) i) = 1 := by
  have himg : (S.ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
      (componentRoots (famCharHom a) i) = componentRoots (famCharHom a) i := by
    refine CFSG.StandardType.F4ExplicitPos.OddKernelOrbit.componentRoots_image_eq_of_odd_torsion
      (χ := famCharHom a) (hp.odd_of_ne_two hp2) ?_ S.frob.isRoot_iff S.frob.iform_eq ?_ i
    · intro γ _
      funext u
      exact rootChar_pow_eq_one_of_forall (hap u) γ
    · intro γ hγ
      exact rho_mem_kernelRoots_famChar S a hT hγ
  exact ⟨himg,
    CFSG.StandardType.F4ExplicitPos.OddKernelOrbit.componentOrbitLength_eq_one_of_image_eq himg⟩

end CFSG.StandardType.TableCRes
