module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UFrameO

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem exists_family_dataO
    {τ : Tag} (hField : UFieldInput τ)
    {X : Type} [Group X] {G₀ B D J : Subgroup X} {f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Type} [Field K] [Finite K] [CharP K 2] (S₁ : LangSetup τ (AlgebraicClosure K) 5)
    (hq : S₁.D.q = 2 ^ f) (fr₁ : GGTCUFrameO G₀ B (ModGL τ (AlgebraicClosure K)))
    (hΘ : fr₁.Θ.range = S₁.Γ) (hDT : fr₁.DimgO D ≤ S₁.D.torus)
    (hBN : B ≤ Subgroup.normalizer (G₀ : Set X))
    (hBel : IsElemAbelian p B) (hDB : D ≤ B) (hJG : J ≤ G₀)
    (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)))
    (hF : ∃ (t' : StatedLieTag) (m f' : ℕ), f < f' ∧
      LieModel (↥J ⧸ Subgroup.center ↥J) t' m 2 f') :
    ∃ (a : ↥(fr₁.DimgO D) → Fin τ.rank → (AlgebraicClosure K)ˣ)
      (i : KernelComponent (famCharHom a)),
      (∀ u : ↥(fr₁.DimgO D), (u : ModGL τ (AlgebraicClosure K)) = rootDiagUnit τ (a u)) ∧
      (∀ u j, a u j ^ p = 1) ∧
      fr₁.JimgO J ≤ rootSpan τ (AlgebraicClosure K) (famOrbit S₁.ρ a i) ∧
      2 ≤ componentOrbitLength S₁.ρ (componentRoots (famCharHom a) i) := by
  classical
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hBel₁ : IsElemAbelian p fr₁.BimgO := fr₁.isElemAbelian_BimgO hBel
  have : NeZero p := ⟨hp.ne_zero⟩
  have hD₁B : fr₁.DimgO D ≤ fr₁.BimgO := fr₁.DimgO_le_BimgO
  have hpar : ∀ u : fr₁.DimgO D, ∃ c : Fin τ.rank → (AlgebraicClosure K)ˣ,
      (u : ModGL τ (AlgebraicClosure K)) = rootDiagUnit τ c ∧ ∀ j, c j ^ p = 1 := fun u =>
    exists_param_of_torus (hDT u.2).1 (hBel₁.2 _ (hD₁B u.2))
  choose a ha hap using hpar
  have haT : ∀ u, rootDiagUnit τ (a u) ∈ S₁.D.torus := fun u => (ha u) ▸ hDT u.2
  have hrange : (Set.range fun u : fr₁.DimgO D => rootDiagUnit τ (a u)) =
      ((fr₁.DimgO D : Subgroup (ModGL τ (AlgebraicClosure K))) :
        Set (ModGL τ (AlgebraicClosure K))) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      show rootDiagUnit τ (a u) ∈ (fr₁.DimgO D : Set (ModGL τ (AlgebraicClosure K)))
      rw [← ha u]
      exact u.2
    · intro hx
      exact ⟨⟨x, hx⟩, (ha ⟨x, hx⟩).symm⟩
  have hcomp : IsComponentOf (fr₁.JimgO J) (S₁.Γ ⊓ Subgroup.centralizer
      (Set.range fun u : fr₁.DimgO D => rootDiagUnit τ (a u))) := by
    rw [hrange, ← hΘ]
    exact fr₁.isComponentOf_JimgO hBN hDB hJG hJ
  obtain ⟨i, hspan, hfield⟩ :=
    hField (AlgebraicClosure K) 5 p S₁ hp hp2 (fr₁.DimgO D) a haT hap (fr₁.JimgO J) hcomp
  rw [hq, ← pow_mul] at hfield
  have h2 : 2 ≤ componentOrbitLength S₁.ρ (componentRoots (famCharHom a) i) :=
    two_le_of_fieldExt hJ.2.2 (fr₁.nonempty_equiv_JimgO hJG hJ.2.2).some hfield hF
  exact ⟨a, i, ha, hap, hspan, h2⟩

end CFSG.StandardType.TableCRes

end
