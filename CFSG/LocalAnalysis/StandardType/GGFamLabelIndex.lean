module

public import CFSG.LocalAnalysis.StandardType.GGFamComponent
public import CFSG.LocalAnalysis.StandardType.GGFamTameOrbit

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint Matrix

section Generic

theorem famLabelIndex_rationalRootsM_mapsTo {τ : Tag} {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ) :
    Set.MapsTo (ρ : (Fin τ.rank → ℤ) → _) (rationalRootsM ρ χ i) (rationalRootsM ρ χ i) := by
  rintro _ ⟨k, δ, hδ, rfl⟩
  exact ⟨k + 1, δ, hδ, by rw [Function.iterate_succ_apply']⟩

theorem famLabelIndex_rationalRootsM_of_apply_mem
    {τ : Tag} {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ) (i : KernelComponent χ)
    {δ : Fin τ.rank → ℤ} (h : ρ δ ∈ rationalRootsM ρ χ i) :
    δ ∈ rationalRootsM ρ χ i := by
  have hfin : (rationalRootsM ρ χ i).Finite :=
    ((finite_setOf_isRoot τ).subset fun α hα => hα.1 : (kernelRoots χ).Finite).subset
      (famComp_rationalRootsM_subset_kernelRoots hker i)
  have hbij := (hfin.injOn_iff_bijOn_of_mapsTo (famLabelIndex_rationalRootsM_mapsTo i)).1
    ρ.injective.injOn
  obtain ⟨γ, hγ, hγδ⟩ := hbij.surjOn h
  exact ρ.injective hγδ ▸ hγ

theorem famLabelIndex_rationalRootsM_of_iterate_mem
    {τ : Tag} {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) (n : ℕ)
    {δ : Fin τ.rank → ℤ} (h : (ρ : (Fin τ.rank → ℤ) → _)^[n] δ ∈ rationalRootsM ρ χ i) :
    δ ∈ rationalRootsM ρ χ i := by
  induction n generalizing δ with
  | zero => exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply] at h
    exact famLabelIndex_rationalRootsM_of_apply_mem hker i (ih h)

theorem famLabelIndex_iterate_mem_rationalRootsM {τ : Tag} {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ) (n : ℕ)
    {γ : Fin τ.rank → ℤ} (h : γ ∈ rationalRootsM ρ χ i) :
    (ρ : (Fin τ.rank → ℤ) → _)^[n] γ ∈ rationalRootsM ρ χ i := by
  obtain ⟨k, δ, hδ, rfl⟩ := h
  exact ⟨n + k, δ, hδ, by rw [Function.iterate_add_apply]⟩

theorem famLabelIndex_rationalRootsM_closed
    {τ : Tag} {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) (i : KernelComponent χ)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ rationalRootsM ρ χ i)
    {β : Fin τ.rank → ℤ} (hβ : β ∈ kernelRoots χ)
    (h : (⟦⟨β, hβ⟩⟧ : KernelComponent χ) =
      ⟦⟨γ, famComp_rationalRootsM_subset_kernelRoots hker i hγ⟩⟧) :
    β ∈ rationalRootsM ρ χ i := by
  classical
  have hfin : (kernelRoots χ).Finite := (finite_setOf_isRoot τ).subset fun α h => h.1
  have : Finite (kernelRoots χ) := hfin.to_subtype
  let σ : kernelRoots χ → kernelRoots χ := fun x => ⟨ρ x, hker x x.2⟩
  have hσinj : Function.Injective σ := fun x y h =>
    Subtype.ext (ρ.injective (congrArg Subtype.val h))
  let e : Equiv.Perm (kernelRoots χ) := Equiv.ofBijective σ (Finite.injective_iff_bijective.1 hσinj)
  have he_iter : ∀ (k : ℕ) (x : kernelRoots χ),
      (((e ^ k) x : kernelRoots χ) : Fin τ.rank → ℤ) = (ρ : (Fin τ.rank → ℤ) → _)^[k] x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ', Equiv.Perm.mul_apply]
      show ρ (((e ^ k) x : kernelRoots χ) : Fin τ.rank → ℤ) = _
      rw [ih, Function.iterate_succ_apply']
  have hr : ∀ (k : ℕ) (x y : kernelRoots χ),
      (((e ^ k) x : kernelRoots χ) : Fin τ.rank → ℤ) ⬝ᵥ
          (τ.symmetrizedCartan *ᵥ (((e ^ k) y : kernelRoots χ) : Fin τ.rank → ℤ)) ≠ 0 ↔
        (x : Fin τ.rank → ℤ) ⬝ᵥ (τ.symmetrizedCartan *ᵥ (y : Fin τ.rank → ℤ)) ≠ 0 := by
    intro k x y
    rw [dotProduct_mulVec_eq_iform, dotProduct_mulVec_eq_iform, he_iter, he_iter,
      iform_iterate hform]
  obtain ⟨k, δ, ⟨hδ, hδi⟩, rfl⟩ := hγ
  set y : kernelRoots χ := (e ^ k)⁻¹ ⟨β, hβ⟩ with hy
  have hey : (e ^ k) y = ⟨β, hβ⟩ := by simp [hy]
  have hex : (e ^ k) ⟨δ, hδ⟩ =
      ⟨(ρ : (Fin τ.rank → ℤ) → _)^[k] δ, famComp_iterate_mem_kernelRoots hker k hδ⟩ :=
    Subtype.ext (he_iter k ⟨δ, hδ⟩)
  have hyx : (⟦y⟧ : KernelComponent χ) = ⟦⟨δ, hδ⟩⟧ := by
    rw [Quotient.eq]
    refine (eqvGen_equiv_iff (e ^ k) (hr k) y ⟨δ, hδ⟩).1 ?_
    rw [hey, hex]
    exact (Quotient.eq).1 h
  refine ⟨k, y, ⟨y.2, hyx.trans hδi⟩, ?_⟩
  have := congrArg Subtype.val hey
  rw [he_iter] at this
  exact this.symm

theorem famLabelIndex_rationalRootsM_subset_of_mem_inter
    {τ : Tag} {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) {i j : KernelComponent χ}
    {δ : Fin τ.rank → ℤ} (hi : δ ∈ rationalRootsM ρ χ i) (hj : δ ∈ rationalRootsM ρ χ j) :
    rationalRootsM ρ χ j ⊆ rationalRootsM ρ χ i := by
  obtain ⟨n, δ₂, ⟨hδ₂, hδ₂j⟩, rfl⟩ := hj
  have hδ₂i : δ₂ ∈ rationalRootsM ρ χ i :=
    famLabelIndex_rationalRootsM_of_iterate_mem hker i n hi
  rintro _ ⟨l, ε₂, ⟨hε₂, hε₂j⟩, rfl⟩
  exact famLabelIndex_iterate_mem_rationalRootsM i l
    (famLabelIndex_rationalRootsM_closed hker hform i hδ₂i hε₂ (hε₂j.trans hδ₂j.symm))

theorem famLabelIndex_rationalRootsM_eq_of_mem_inter
    {τ : Tag} {M : Type*} [CommGroup M]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) {i j : KernelComponent χ}
    {δ : Fin τ.rank → ℤ} (hi : δ ∈ rationalRootsM ρ χ i) (hj : δ ∈ rationalRootsM ρ χ j) :
    rationalRootsM ρ χ i = rationalRootsM ρ χ j :=
  le_antisymm (famLabelIndex_rationalRootsM_subset_of_mem_inter hker hform hj hi)
    (famLabelIndex_rationalRootsM_subset_of_mem_inter hker hform hi hj)

theorem famLabelIndex_commute_rootSpan_rationalRootsM
    {τ : Tag} {M : Type*} [CommGroup M]
    {L : Type} [Field L]
    {ρ : Equiv.Perm (Fin τ.rank → ℤ)} {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hker : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) {i j : KernelComponent χ}
    (hij : rationalRootsM ρ χ i ≠ rationalRootsM ρ χ j) :
    ∀ x ∈ rootSpan τ L (rationalRootsM ρ χ i), ∀ y ∈ rootSpan τ L (rationalRootsM ρ χ j),
      x * y = y * x := by
  have hle : rootSpan τ L (rationalRootsM ρ χ i) ≤
      Subgroup.centralizer (rootSpan τ L (rationalRootsM ρ χ j) : Set (ModGL τ L)) := by
    refine iSup₂_le fun γ hγ => ?_
    rw [Subgroup.le_centralizer_iff]
    refine iSup₂_le fun δ hδ => ?_
    rw [Subgroup.le_centralizer_iff]
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hγk := famComp_rationalRootsM_subset_kernelRoots hker i hγ
    have hδk := famComp_rationalRootsM_subset_kernelRoots hker j hδ
    have hne : (⟦⟨γ, hγk⟩⟧ : KernelComponent χ) ≠ ⟦⟨δ, hδk⟩⟧ := fun h =>
      hij (famLabelIndex_rationalRootsM_eq_of_mem_inter hker hform
        (famLabelIndex_rationalRootsM_closed hker hform i hγ hδk h.symm) hδ)
    exact (commute_of_mk_ne hne L y hy x hx).eq.symm
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.1 (hle hx) y hy).symm

end Generic

theorem rationalRootsM_eq_of_quasisimple_le_rootSpan
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (i j : KernelComponent (famCharHom a))
    {K : Subgroup (ModGL τ L)} (hK : CFSG.IsQuasisimple ↥K)
    (hi : K ≤ rootSpan τ L (rationalRootsM S.ρ (famCharHom a) i))
    (hj : K ≤ rootSpan τ L (rationalRootsM S.ρ (famCharHom a) j)) :
    rationalRootsM S.ρ (famCharHom a) i = rationalRootsM S.ρ (famCharHom a) j := by
  by_contra hne
  have hker : ∀ γ ∈ kernelRoots (famCharHom a), S.ρ γ ∈ kernelRoots (famCharHom a) :=
    fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ
  have hcomm := famLabelIndex_commute_rootSpan_rationalRootsM (L := L) (ρ := S.ρ)
    (χ := famCharHom a) hker S.frob.iform_eq hne
  obtain ⟨x, y, hxy⟩ :=
    CFSG.ComponentClassification.GSThmB.exists_noncomm_of_isQuasisimple (Y := ↥K) hK
  exact hxy (Subtype.ext (hcomm x (hi x.2) y (hj y.2)))

end CFSG.StandardType.TableCRes

end
