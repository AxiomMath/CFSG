module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UFrameD
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4UData

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Blueprint CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem uframe_dataD
    {τ : Tag} (hField : UFieldInput τ) (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {X : Type} [Group X] {G₀ B D J : Subgroup X} {f p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hmod : UntwistedChevalleyModel (↥G₀ ⧸ Subgroup.center ↥G₀) τ (2 ^ f))
    (hBN : B ≤ Subgroup.normalizer (G₀ : Set X))
    (hin : ∀ b ∈ B, ∃ g ∈ G₀, b * g ∈ Subgroup.centralizer (G₀ : Set X))
    (hfaith : B ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥) (hBel : IsElemAbelian p B)
    (hDB : D ≤ B) (hDcard : Nat.card D = p ^ 2) (hJG : J ≤ G₀)
    (hJ : IsComponentOf J (G₀ ⊓ Subgroup.centralizer (D : Set X)))
    (hF : ∃ (t' : StatedLieTag) (m f' : ℕ), f < f' ∧
      LieModel (↥J ⧸ Subgroup.center ↥J) t' m 2 f')
    (htorD : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f → UPlaneToralAt τ p K) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (S₁ : LangSetup τ (AlgebraicClosure K) 5) (fr₁ : GGTCUFrame S₁.Γ G₀ B),
      S₁.D.q = 2 ^ f ∧ fr₁.DLang D ≤ S₁.D.torus ∧
      (∃ w : WeylGroup τ, ∀ γ, IsRoot τ γ → S₁.ρ γ = w • γ) ∧
      ∃ (a : ↥(fr₁.DLang D) → Fin τ.rank → (AlgebraicClosure K)ˣ)
        (i : KernelComponent (famCharHom a)),
        (∀ u : ↥(fr₁.DLang D), (u : ModGL τ (AlgebraicClosure K)) = rootDiagUnit τ (a u)) ∧
        (∀ u j, a u j ^ p = 1) ∧
        fr₁.JLang J ≤ rootSpan τ (AlgebraicClosure K) (famOrbit S₁.ρ a i) ∧
        2 ≤ componentOrbitLength S₁.ρ (componentRoots (famCharHom a) i) := by
  classical
  obtain ⟨K, instF, instFin, instChar, S₁, fr₁, hqq, ⟨w, hρ⟩, hDT⟩ :=
    exists_uframe_untwD hτ hp hp2 hmod hBN hin hfaith hBel hDB hDcard htorD
  have : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have hBel₁ : IsElemAbelian p fr₁.BLang := fr₁.isElemAbelian_BLang hBel
  have : NeZero p := ⟨hp.ne_zero⟩
  have hD₁B : fr₁.DLang D ≤ fr₁.BLang := fr₁.DLang_le_BLang
  have hpar : ∀ u : fr₁.DLang D, ∃ c : Fin τ.rank → (AlgebraicClosure K)ˣ,
      (u : ModGL τ (AlgebraicClosure K)) = rootDiagUnit τ c ∧ ∀ j, c j ^ p = 1 := fun u =>
    exists_param_of_torus (hDT u.2).1 (hBel₁.2 _ (hD₁B u.2))
  choose a ha hap using hpar
  have haT : ∀ u, rootDiagUnit τ (a u) ∈ S₁.D.torus := fun u => (ha u) ▸ hDT u.2
  have hrange : (Set.range fun u : fr₁.DLang D => rootDiagUnit τ (a u)) =
      ((fr₁.DLang D : Subgroup (ModGL τ (AlgebraicClosure K))) :
        Set (ModGL τ (AlgebraicClosure K))) := by
    ext x
    constructor
    · rintro ⟨u, rfl⟩
      show rootDiagUnit τ (a u) ∈ (fr₁.DLang D : Set (ModGL τ (AlgebraicClosure K)))
      rw [← ha u]
      exact u.2
    · intro hx
      exact ⟨⟨x, hx⟩, (ha ⟨x, hx⟩).symm⟩
  have hcomp : IsComponentOf (fr₁.JLang J) (S₁.Γ ⊓ Subgroup.centralizer
      (Set.range fun u : fr₁.DLang D => rootDiagUnit τ (a u))) := by
    rw [hrange]
    exact fr₁.isComponentOf_JLang hDB hJG hJ
  obtain ⟨i, hspan, hfield⟩ :=
    hField (AlgebraicClosure K) 5 p S₁ hp hp2 (fr₁.DLang D) a haT hap (fr₁.JLang J) hcomp
  rw [hqq, ← pow_mul] at hfield
  have h2 : 2 ≤ componentOrbitLength S₁.ρ (componentRoots (famCharHom a) i) :=
    two_le_of_fieldExt hJ.2.2 (fr₁.nonempty_equiv_JLang hJG hJ.2.2).some hfield hF
  exact ⟨K, instF, instFin, instChar, S₁, fr₁, hqq, hDT, ⟨w, hρ⟩, a, i, ha, hap, hspan, h2⟩

end CFSG.StandardType.TableCRes

end
