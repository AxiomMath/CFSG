module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabel
import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang
import CFSG.LieType.Chevalley.OrthogonalUnionBruhat

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Certificates

private theorem rationalRoots_ne_of_iterate_image_ne
    {L : Type} [Field L] [IsAlgClosed L]
    {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀) {a : Fin Tag.E6.rank → Lˣ}
    (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (i i' : KernelComponent (rootCharHom a))
    (hno : ∀ k : ℕ, (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k] ''
      componentRoots (rootCharHom a) i ≠ componentRoots (rootCharHom a) i') :
    rationalRoots S.ρ (rootCharHom a) i ≠ rationalRoots S.ρ (rootCharHom a) i' := by
  intro heq
  obtain ⟨x, hx⟩ := Quotient.exists_rep i'
  have hxmem : (x : Fin Tag.E6.rank → ℤ) ∈ componentRoots (rootCharHom a) i' :=
    ⟨x.2, hx⟩
  have hxrat' : (x : Fin Tag.E6.rank → ℤ) ∈ rationalRoots S.ρ (rootCharHom a) i' :=
    ⟨0, x.1, hxmem, rfl⟩
  have hxrat : (x : Fin Tag.E6.rank → ℤ) ∈ rationalRoots S.ρ (rootCharHom a) i := by
    rw [heq]
    exact hxrat'
  obtain ⟨k, y, hy, hky⟩ := hxrat
  obtain ⟨j, hj⟩ := outer_iterate_image_component S hT i k
  have hmemj : (x : Fin Tag.E6.rank → ℤ) ∈ componentRoots (rootCharHom a) j := by
    rw [hj]
    exact ⟨y, hy, hky.symm⟩
  have hji : j = i' := eq_of_mem_componentRoots hmemj hxmem
  exact hno k (by rw [← hj, hji])

theorem rationalComponent_ne_of_not_orbit
    {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup Tag.E6 L p₀)
    {a : Fin Tag.E6.rank → Lˣ} (hT : rootDiagUnit Tag.E6 a ∈ S.D.torus)
    (i i' : KernelComponent (rootCharHom a))
    (hno : ∀ k : ℕ, (S.ρ : (Fin Tag.E6.rank → ℤ) → (Fin Tag.E6.rank → ℤ))^[k] ''
      componentRoots (rootCharHom a) i ≠ componentRoots (rootCharHom a) i')
    (hQS : CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) :
    rationalComponent S.ρ S.Γ (rootCharHom a) i ≠ rationalComponent S.ρ S.Γ (rootCharHom a) i' := by
  have hker := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.rho_mem_kernelRoots_of_mem_torus S hT
  have hform : ∀ γ δ : Fin Tag.E6.rank → ℤ,
      CFSG.LieType.Steinberg.Adjoint.iform (S.ρ γ) (S.ρ δ) =
        CFSG.LieType.Steinberg.Adjoint.iform γ δ := fun γ δ => S.frob.iform_eq γ δ
  have hratne : rationalRoots S.ρ (rootCharHom a) i ≠ rationalRoots S.ρ (rootCharHom a) i' :=
    rationalRoots_ne_of_iterate_image_ne S hT i i' hno
  have hcomm :=
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.commute_rootSpan_rationalRoots
      (τ := Tag.E6) (L := L) hker hform hratne
  intro heq
  have hle : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      rootSpan Tag.E6 L (rationalRoots S.ρ (rootCharHom a) i) :=
    (commutator_le_self_of_subgroup _).trans inf_le_left
  have hle' : rationalComponent S.ρ S.Γ (rootCharHom a) i' ≤
      rootSpan Tag.E6 L (rationalRoots S.ρ (rootCharHom a) i') :=
    (commutator_le_self_of_subgroup _).trans inf_le_left
  have habel : ∀ x y : ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i),
      x * y = y * x := by
    intro x y
    have hx : (x : ModGL Tag.E6 L) ∈
        rootSpan Tag.E6 L (rationalRoots S.ρ (rootCharHom a) i) :=
      hle x.2
    have hy : (y : ModGL Tag.E6 L) ∈
        rootSpan Tag.E6 L (rationalRoots S.ρ (rootCharHom a) i') :=
      hle' (by rw [← heq]; exact y.2)
    exact Subtype.ext (hcomm (x : ModGL Tag.E6 L) hx (y : ModGL Tag.E6 L) hy).eq
  obtain ⟨u, v, huv⟩ := hQS.2.2
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) u
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
    (Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) v
  rw [← hx, ← hy] at huv
  exact huv (by rw [← map_mul, ← map_mul, habel x y])

end Certificates

end CFSG.StandardType.TablePThreeKG

end
