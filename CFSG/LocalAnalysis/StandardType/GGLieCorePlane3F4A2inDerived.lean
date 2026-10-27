module

public import CFSG.LocalAnalysis.StandardType.GGLieCorePlane3F4Defs
public import CFSG.LocalAnalysis.StandardType.GGFamLabelAssembly
public import CFSG.LocalAnalysis.StandardType.GGFamAssembly

public section

namespace CFSG.StandardType.LieCore

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag)

private theorem l10lG7_ratOrbit_eq_of_image_eq {τ : Tag}
    {ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ)} {Ψ : Set (Fin τ.rank → ℤ)}
    (h : ρ '' Ψ = Ψ) : ratOrbit ρ Ψ = Ψ := by
  ext γ
  constructor
  · rintro ⟨k, δ, hδ, rfl⟩
    have himg : ∀ x, x ∈ Ψ → ρ x ∈ Ψ := by
      intro x hx
      rw [← h]
      exact ⟨x, hx, rfl⟩
    have hk : ∀ k : ℕ, ρ^[k] δ ∈ Ψ := by
      intro k
      induction k with
      | zero => simpa using hδ
      | succ k ih =>
        rw [Function.iterate_succ_apply']
        exact himg _ ih
    exact hk k
  · intro hγ
    exact ⟨0, γ, hγ, rfl⟩

theorem ggLieF4A2in_derived
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] {D : LangDatum Tag.F4 L}
    {ρ : Equiv.Perm (Fin Tag.F4.rank → ℤ)} {a₁ a₂ : Fin Tag.F4.rank → Lˣ}
    (h : GGLieF4PlaneHyp D ρ a₁ a₂)
    {f : ℕ} (hf : 1 ≤ f) (hqf : D.q = 2 ^ f) (i : KernelComponent (jointChar a₁ a₂))
    (hρΨ : (ρ : (Fin Tag.F4.rank → ℤ) → (Fin Tag.F4.rank → ℤ)) ''
      componentRoots (jointChar a₁ a₂) i = componentRoots (jointChar a₁ a₂) i)
    (hΓ : D.Γ = D.model)
    (hmodel : GGLieSL3Model ↥(rootSpan Tag.F4 L (componentRoots (jointChar a₁ a₂) i) ⊓ D.model) f) :
    Group.IsSolvable ↥(GGLieF4PlaneRat D ρ a₁ a₂ i) ∨
      LieModel (↥(GGLieF4PlaneRat D ρ a₁ a₂ i) ⧸
        Subgroup.center ↥(GGLieF4PlaneRat D ρ a₁ a₂ i)) .PSL 3 2 f := by
  let Ψ : Set (Fin Tag.F4.rank → ℤ) := componentRoots (jointChar a₁ a₂) i
  let M : Subgroup (ModGL Tag.F4 L) := rootSpan Tag.F4 L Ψ ⊓ D.model
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨eM⟩⟩ := hmodel
  let : Field K := hKfield
  let : Finite K := hKfinite
  let eSL := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K
  let e : Matrix.SpecialLinearGroup (Fin 3) K ≃* ↥M := eSL.trans eM.symm
  have hperfSL : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (K := K) (n := 3) (by norm_num)
  have hperfM : Group.IsPerfect ↥M :=
    Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hcomm : ⁅(M : Subgroup (ModGL Tag.F4 L)), (M : Subgroup (ModGL Tag.F4 L))⁆ = M := by
    have : Group.IsPerfect ↥M := hperfM
    exact Subgroup.commutator_eq_self
  have hrat : GGLieF4PlaneRat D ρ a₁ a₂ i = ⁅(M : Subgroup (ModGL Tag.F4 L)), M⁆ := by
    unfold GGLieF4PlaneRat ratComp
    rw [hΓ, l10lG7_ratOrbit_eq_of_image_eq hρΨ]
  have hgker : e.toMonoidHom.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
    rw [(MonoidHom.ker_eq_bot_iff e.toMonoidHom).2 e.injective]
    exact bot_le
  have hLM : LieModel (↥M ⧸ Subgroup.center ↥M) .PSL 3 2 f :=
    CFSG.StandardType.TableCRes.lieModel_of_slCover (G := ModGL Tag.F4 L) (X := M)
      (K := K) (ν := 3) (f := f) hf hKcard (by norm_num)
      (by intro h; exact absurd h (by norm_num)) e.toMonoidHom e.surjective hgker
  refine Or.inr ?_
  rw [hrat, hcomm]
  exact hLM

end CFSG.StandardType.LieCore
