module

public import CFSG.LocalAnalysis.StandardType.GGExcCompSLDefs
public import CFSG.LocalAnalysis.StandardType.GGJ4dOrthogonalRank
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExc
import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
import CFSG.RankThree.PartOne.KE.E8D4Family

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups


private theorem q2cOrb_rho_add {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) (x y : Fin τ.rank → ℤ) :
    S.ρ (x + y) = S.ρ x + S.ρ y := by
  have h : ∀ z, iform (S.ρ (x + y) - S.ρ x - S.ρ y) (S.ρ z) = 0 := by
    intro z
    rw [iform_sub_left, iform_sub_left, S.frob.iform_eq, S.frob.iform_eq, S.frob.iform_eq,
      iform_add_left]
    ring
  have h0 := h (S.ρ.symm (S.ρ (x + y) - S.ρ x - S.ρ y))
  rw [Equiv.apply_symm_apply] at h0
  have h1 : S.ρ (x + y) - S.ρ x - S.ρ y = 0 := by
    by_contra hne
    exact (iform_self_pos hne).ne' h0
  rw [sub_sub, sub_eq_zero] at h1
  exact h1

private noncomputable def q2cOrb_rhoLinMap {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ : ℕ} (S : LangSetup τ L p₀) :
    (Fin τ.rank → ℤ) →ₗ[ℤ] (Fin τ.rank → ℤ) :=
  (AddMonoidHom.mk' (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))
    (q2cOrb_rho_add S)).toIntLinearMap

private theorem q2cOrb_finrank_span_eq_compRank {τ : Tag} (Ψ : Set (Fin τ.rank → ℤ))
    (hΨ : Ψ.Finite) : Module.finrank ℤ (Submodule.span ℤ Ψ) = compRank Ψ := by
  let g : (Fin τ.rank → ℤ) → (Fin τ.rank → ℚ) := fun v i => (v i : ℚ)
  let f : (Fin τ.rank → ℤ) →ₗ[ℤ] (Fin τ.rank → ℚ) :=
    { toFun := g
      map_add' := by intro a b; funext i; simp [g]
      map_smul' := by intro a b; funext i; simp [g] }
  have hfinj : Function.Injective f := by
    intro a b h
    funext i
    have h' := congrFun h i
    exact Int.cast_injective h'
  have : Module.Finite ℤ (Submodule.span ℤ (f '' Ψ)) :=
    Module.Finite.span_of_finite ℤ (hΨ.image f)
  have hmap : (Submodule.span ℤ Ψ).map f = Submodule.span ℤ (f '' Ψ) := by
    rw [Submodule.map_span]
  have heq : Module.finrank ℤ (Submodule.span ℤ Ψ) =
      Module.finrank ℤ (Submodule.span ℤ (f '' Ψ)) := by
    rw [← hmap]
    exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective f hfinj (Submodule.span ℤ Ψ))
  have hM : Module.finrank ℚ (Submodule.span ℚ (f '' Ψ)) =
      Module.finrank ℤ (Submodule.span ℤ (f '' Ψ)) :=
    Submodule.finrank_span_eq_finrank_span ℤ ℚ (f '' Ψ)
  have hcomp : compRank Ψ = Module.finrank ℚ (Submodule.span ℚ (f '' Ψ)) := by
    rw [compRank]
    rfl
  rw [hcomp, hM]
  exact heq

private theorem q2cOrb_compRank_rho_image {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ : ℕ} (S : LangSetup τ L p₀) {Ψ : Set (Fin τ.rank → ℤ)} (hfin : Ψ.Finite) :
    compRank (S.ρ '' Ψ) = compRank Ψ := by
  have h1 : Module.finrank ℤ (Submodule.span ℤ (S.ρ '' Ψ)) =
      Module.finrank ℤ (Submodule.span ℤ Ψ) := by
    have hmap : Submodule.span ℤ (S.ρ '' Ψ) =
        Submodule.map (q2cOrb_rhoLinMap S) (Submodule.span ℤ Ψ) := by
      rw [Submodule.map_span]
      rfl
    rw [hmap]
    exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _
      (fun x y hxy => S.ρ.injective hxy) _)).symm
  rw [← q2cOrb_finrank_span_eq_compRank (S.ρ '' Ψ) (hfin.image S.ρ),
    ← q2cOrb_finrank_span_eq_compRank Ψ hfin]
  exact h1

private theorem q2cOrb_compRank_iterate {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ : ℕ} (S : LangSetup τ L p₀) {Ψ : Set (Fin τ.rank → ℤ)} (hfin : Ψ.Finite) (k : ℕ) :
    compRank ((S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] '' Ψ) = compRank Ψ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ', Set.image_comp,
      q2cOrb_compRank_rho_image S (hfin.image ((S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k]))]
    exact ih

private theorem q2cOrb_orth_iterate {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    {p₀ : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a))
    {k l s : ℕ} (hkl : k < l)
    (hmin : ∀ m, 0 < m → m < s →
      (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[m] '' componentRoots (rootCharHom a) i ≠
        componentRoots (rootCharHom a) i)
    (hl : l < s) :
    ∀ x ∈ (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] '' componentRoots (rootCharHom a) i,
      ∀ y ∈ (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[l] '' componentRoots (rootCharHom a) i,
        iform x y = 0 := by
  intro x hx y hy
  obtain ⟨jk, hjk⟩ := outer_iterate_image_component S hT i k
  obtain ⟨jl, hjl⟩ := outer_iterate_image_component S hT i l
  have hxk : x ∈ componentRoots (rootCharHom a) jk := hjk.symm ▸ hx
  have hyl : y ∈ componentRoots (rootCharHom a) jl := hjl.symm ▸ hy
  have hne : jk ≠ jl := by
    intro h
    subst h
    have h1 : (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] ''
          componentRoots (rootCharHom a) i =
        (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[l] ''
          componentRoots (rootCharHom a) i := hjk.symm.trans hjl
    have h2 : (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[l] ''
          componentRoots (rootCharHom a) i =
        (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] ''
          ((S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[l - k] ''
            componentRoots (rootCharHom a) i) := by
      rw [Set.image_image]
      refine Set.image_congr fun z _ => ?_
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    rw [h2] at h1
    have h3 := (Set.image_injective.2 (S.ρ.injective.iterate k)) h1
    exact hmin (l - k) (by omega) (by omega) h3.symm
  exact iform_eq_zero_of_mem_componentRoots hne hxk hyl

theorem componentOrbitLength_mul_compRank_le {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] {p₀ : ℕ} (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) (i : KernelComponent (rootCharHom a)) :
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) *
      compRank (componentRoots (rootCharHom a) i) ≤ τ.rank := by
  classical
  obtain ⟨hs0, hsper, hmin⟩ := outer_componentOrbitLength_spec S hT i
  set Ψ : Set (Fin τ.rank → ℤ) := componentRoots (rootCharHom a) i with hΨdef
  set s : ℕ := componentOrbitLength S.ρ Ψ with hsdef
  have hfin : Ψ.Finite := (finite_setOf_isRoot τ).subset fun γ hγ => hγ.1.1
  have hrank : ∀ k, compRank ((S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] '' Ψ) =
      compRank Ψ := fun k => q2cOrb_compRank_iterate S hfin k
  have horth : ∀ k ∈ Finset.range s, ∀ l ∈ Finset.range s, k ≠ l →
      ∀ x ∈ (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] '' Ψ,
      ∀ y ∈ (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[l] '' Ψ, iform x y = 0 := by
    intro k hk l hl hkl x hx y hy
    rcases lt_or_gt_of_ne hkl with h | h
    · exact q2cOrb_orth_iterate S hT i h hmin (Finset.mem_range.1 hl) x hx y hy
    · rw [iform_comm]
      exact q2cOrb_orth_iterate S hT i h hmin (Finset.mem_range.1 hk) y hy x hx
  have hsum := compRank_iUnion_finset_eq_sum (Finset.range s)
    (fun k => (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] '' Ψ) horth
  have hle := compRank_le_rank (⋃ k ∈ Finset.range s,
    (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] '' Ψ)
  have hsum_eq : (∑ k ∈ Finset.range s,
      compRank ((S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] '' Ψ)) =
      s * compRank Ψ := by
    rw [Finset.sum_congr rfl (fun k _ => hrank k)]
    simp [Finset.sum_const, Finset.card_range]
  calc s * compRank Ψ = ∑ k ∈ Finset.range s,
        compRank ((S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] '' Ψ) := hsum_eq.symm
    _ = compRank (⋃ k ∈ Finset.range s,
        (S.ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))^[k] '' Ψ) := hsum.symm
    _ ≤ τ.rank := hle

end CFSG.StandardType.LangRat
