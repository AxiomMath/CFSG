module

public import CFSG.LocalAnalysis.StandardType.GGFamTameOrbit
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimple

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

private theorem famRange_Afix_le_model
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots χ i = componentRoots χ i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots χ i ≠ componentRoots χ i) :
    ∀ g ∈ (famOrbitFamily S hρ i hs hmin).Afix, g ∈ S.D.model := by
  intro g hg
  refine ⟨?_, hg.2⟩
  have hA : (famOrbitFamily S hρ i hs hmin).A ≤ adjointGroup τ L := by
    refine iSup_le fun k => iSup₂_le fun γ _ => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    exact pinnedX_mem_adjointGroup _ _
  exact hA hg.1

private theorem famRange_outer_norm_mem_rationalComponent
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots χ i = componentRoots χ i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots χ i ≠ componentRoots χ i)
    {C : Type*} [Group C] (hC : Group.IsPerfect C)
    (θ₀ : C →* (famOrbitFamily S hρ i hs hmin).S 0)
    (hfix : ∀ x, iterHom S.D.step s
      ((θ₀ x : (famOrbitFamily S hρ i hs hmin).S 0) : ModGL τ L) = θ₀ x) (x : C) :
    (famOrbitFamily S hρ i hs hmin).norm (θ₀ x) ∈ rationalComponentM S.ρ S.Γ χ i := by
  let f : C →* ModGL τ L := (famOrbitFamily S hρ i hs hmin).norm.comp θ₀
  have hfA : ∀ x : C, f x ∈ (famOrbitFamily S hρ i hs hmin).Afix := fun x =>
    (famOrbitFamily S hρ i hs hmin).norm_mem_Afix (hfix x)
  have hAmodel := famRange_Afix_le_model S hρ i hs hmin
  have hM : ∀ x : C, f x ∈ S.D.model := fun x => hAmodel _ (hfA x)
  have hΓ : ∀ x : C, f x ∈ S.Γ := map_mem_commutator_of_perfect hC f _ hM
  have hRS : ∀ x : C, f x ∈ rationalSpanM S.ρ S.Γ χ i := by
    intro x
    refine Subgroup.mem_inf.2 ⟨?_, hΓ x⟩
    have := (hfA x).1
    rw [famOrbitFamily_A] at this
    exact this
  unfold rationalComponentM
  exact map_mem_commutator_of_perfect hC f _ hRS x

theorem fam_rationalComponent_eq_range_of_hom_le
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ)
    {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots χ i = componentRoots χ i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots χ i ≠ componentRoots χ i)
    {C : Type*} [Group C] (θ : C →* ModGL τ L)
    (hθS : ∀ c, θ c ∈ rootSpan τ L (componentRoots χ i))
    (hθfix : ∀ c, iterHom S.D.step s (θ c) = θ c)
    (hθY : ∀ g g' : ModGL τ L, g ∈ rootSpan τ L (componentRoots χ i) →
      g' ∈ rootSpan τ L (componentRoots χ i) →
      iterHom S.D.step s g * g⁻¹ ∈ (famOrbitFamily S hρ i hs hmin).Z →
      iterHom S.D.step s g' * g'⁻¹ ∈ (famOrbitFamily S hρ i hs hmin).Z → ⁅g, g'⁆ ∈ θ.range)
    (hθZ : ∀ c, θ c ∈ (famOrbitFamily S hρ i hs hmin).Z → c ∈ Subgroup.center C) :
    ∃ f : C →* ModGL τ L, rationalComponentM S.ρ S.Γ χ i ≤ f.range ∧
      f.ker ≤ Subgroup.center C ∧
      (Group.IsPerfect C → f.range ≤ rationalComponentM S.ρ S.Γ χ i) ∧
      f.range ≤ rootSpan τ L (rationalRootsM S.ρ χ i) ⊓ S.D.model := by
  classical
  set P := famOrbitFamily S hρ i hs hmin with hP
  set Ψ := componentRoots χ i with hΨ
  have hP0 : P.S 0 = rootSpan τ L Ψ := by
    rw [hP, famOrbitFamily_S, ZMod.val_zero]
    simp only [Function.iterate_zero, id_eq, Set.image_id']
    rfl
  let θ₀ : C →* P.S 0 := θ.codRestrict (P.S 0) fun c => by
    rw [hP0]
    exact hθS c
  have hθ₀ : ∀ c, ((θ₀ c : P.S 0) : ModGL τ L) = θ c := fun c => rfl
  let f : C →* ModGL τ L := P.norm.comp θ₀
  have hfix : ∀ c, iterHom S.D.step s ((θ₀ c : P.S 0) : ModGL τ L) = θ₀ c := fun c => by
    rw [hθ₀]; exact hθfix c
  have hYW : ⁅P.Y, P.Y⁆ ≤ θ.range := by
    rw [Subgroup.commutator_le]
    intro u hu u' hu'
    obtain ⟨hu0, huZ⟩ := P.mem_Y.1 hu
    obtain ⟨hu0', huZ'⟩ := P.mem_Y.1 hu'
    rw [hP0] at hu0 hu0'
    exact hθY u u' hu0 hu0' huZ huZ'
  have hΓM : S.Γ ≤ S.D.model := Subgroup.commutator_le_self S.D.model
  have hrsA : rationalSpanM S.ρ S.Γ χ i ≤ P.Afix := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.1 hx
    refine ⟨?_, (hΓM hx2).2⟩
    rw [hP, famOrbitFamily_A]
    exact hx1
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro g hg
    have h1 := P.commutator_Afix_le (Subgroup.commutator_mono hrsA hrsA hg)
    obtain ⟨y, hyY, rfl⟩ := P.mem_normImage.1 h1
    obtain ⟨c, hc⟩ := hYW hyY
    refine ⟨c, ?_⟩
    change P.norm (θ₀ c) = P.norm y
    congr 1
    exact Subtype.ext hc
  · intro c hc
    have h1 : P.norm (θ₀ c) = 1 := hc
    exact hθZ c (P.mem_Z_of_norm_eq_one h1)
  · intro hperf
    rintro _ ⟨x, rfl⟩
    exact famRange_outer_norm_mem_rationalComponent S hρ i hs hmin hperf θ₀ hfix x
  · rintro _ ⟨c, rfl⟩
    have hfc : f c ∈ P.Afix := P.norm_mem_Afix (hfix c)
    refine ⟨?_, famRange_Afix_le_model S hρ i hs hmin _ hfc⟩
    have h1 := hfc.1
    rw [hP, famOrbitFamily_A] at h1
    exact h1

theorem fam_rationalComponent_eq_range_of_hom
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ)
    {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots χ i = componentRoots χ i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots χ i ≠ componentRoots χ i)
    {C : Type*} [Group C] (θ : C →* ModGL τ L)
    (hθS : ∀ c, θ c ∈ rootSpan τ L (componentRoots χ i))
    (hθfix : ∀ c, iterHom S.D.step s (θ c) = θ c)
    (hθY : ∀ g g' : ModGL τ L, g ∈ rootSpan τ L (componentRoots χ i) →
      g' ∈ rootSpan τ L (componentRoots χ i) →
      iterHom S.D.step s g * g⁻¹ ∈ (famOrbitFamily S hρ i hs hmin).Z →
      iterHom S.D.step s g' * g'⁻¹ ∈ (famOrbitFamily S hρ i hs hmin).Z → ⁅g, g'⁆ ∈ θ.range)
    (hθZ : ∀ c, θ c ∈ (famOrbitFamily S hρ i hs hmin).Z → c ∈ Subgroup.center C) :
    ∃ f : C →* ModGL τ L, rationalComponentM S.ρ S.Γ χ i ≤ f.range ∧
      f.ker ≤ Subgroup.center C ∧
      (Group.IsPerfect C → f.range ≤ rationalComponentM S.ρ S.Γ χ i) := by
  obtain ⟨f, h1, h2, h3, -⟩ :=
    fam_rationalComponent_eq_range_of_hom_le S hρ i hs hmin θ hθS hθfix hθY hθZ
  exact ⟨f, h1, h2, h3⟩

end CFSG.StandardType.TableCRes
