module

public import CFSG.LocalAnalysis.StandardType.GGFamRatComp
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4ULang
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleOrbit

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement Matrix

private theorem famOrbit_exists_period
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) :
    ∃ s : ℕ, 0 < s ∧ (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots χ i =
      componentRoots χ i := by
  have hfin : (kernelRoots χ).Finite := (finite_setOf_isRoot τ).subset fun α hα => hα.1
  obtain ⟨d, hd, hfix⟩ := exists_iterate_eq_of_mapsTo hfin
    (fun γ hγ => hρ γ hγ) S.ρ.injective.injOn
  refine ⟨d, hd, ?_⟩
  ext δ
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    rw [hfix γ hγ.1]
    exact hγ
  · intro hδ
    exact ⟨δ, hδ, hfix δ hδ.1⟩

private theorem famOrbit_isRoot_of_mem_iterate_image
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (i : KernelComponent χ) (k : ℕ) {γ : Fin τ.rank → ℤ}
    (hγ : γ ∈ (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots χ i) : IsRoot τ γ := by
  obtain ⟨δ, hδ, rfl⟩ := hγ
  exact S.iterate_isRoot k (isRoot_of_mem_componentRoots hδ)

theorem fam_componentOrbitLength_spec
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) :
    0 < componentOrbitLength S.ρ (componentRoots χ i) ∧
      (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots χ i)] ''
        componentRoots χ i = componentRoots χ i ∧
      ∀ k, 0 < k → k < componentOrbitLength S.ρ (componentRoots χ i) →
        (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots χ i ≠ componentRoots χ i := by
  have hne : {s : ℕ | 0 < s ∧
      (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots χ i =
        componentRoots χ i}.Nonempty := famOrbit_exists_period S hρ i
  have hmem := Nat.sInf_mem hne
  refine ⟨hmem.1, hmem.2, fun k hk hks h => ?_⟩
  exact Nat.notMem_of_lt_sInf hks ⟨hk, h⟩

theorem fam_iterate_image_component
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) (k : ℕ) :
    ∃ j : KernelComponent χ, componentRoots χ j =
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots χ i := by
  induction k with
  | zero => exact ⟨i, by simp⟩
  | succ k ih =>
    obtain ⟨j, hj⟩ := ih
    obtain ⟨j', hj'⟩ := exists_image_component_of_stable χ hρ S.frob.iform_eq j
    refine ⟨j', ?_⟩
    rw [← hj', hj, Function.iterate_succ', Set.image_comp]

private theorem famOrbit_commute_orbit_lt
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) {s : ℕ}
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots χ i ≠ componentRoots χ i)
    {k l : ℕ} (hkl : k < l) (hl : l < s) :
    ∀ x ∈ rootSpan τ L ((S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots χ i),
      ∀ y ∈ rootSpan τ L ((S.ρ : (Fin τ.rank → ℤ) → _)^[l] '' componentRoots χ i),
        x * y = y * x := by
  obtain ⟨j, hj⟩ := fam_iterate_image_component S hρ i k
  obtain ⟨j', hj'⟩ := fam_iterate_image_component S hρ i l
  have hne : j ≠ j' := by
    intro h
    subst h
    have h1 : (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots χ i =
        (S.ρ : (Fin τ.rank → ℤ) → _)^[l] '' componentRoots χ i := hj.symm.trans hj'
    have h2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[l] '' componentRoots χ i =
        (S.ρ : (Fin τ.rank → ℤ) → _)^[k] ''
          ((S.ρ : (Fin τ.rank → ℤ) → _)^[l - k] '' componentRoots χ i) := by
      rw [Set.image_image]
      refine Set.image_congr fun x _ => ?_
      rw [← Function.iterate_add_apply]
      congr 1
      omega
    rw [h2] at h1
    have h3 := (Set.image_injective.2 (S.ρ.injective.iterate k)) h1
    exact hmin (l - k) (by omega) (by omega) h3.symm
  have hbot := (root_character_kernel_orthogonal_central_product τ L χ).2.2.1 j j' hne
  have hle := (Subgroup.commutator_eq_bot_iff_le_centralizer).1 hbot
  intro x hx y hy
  have hxS : x ∈ componentRootSpan L χ j := by
    have : componentRootSpan L χ j =
        rootSpan τ L ((S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots χ i) := by
      rw [← hj]; rfl
    rw [this]; exact hx
  have hyS : y ∈ componentRootSpan L χ j' := by
    have : componentRootSpan L χ j' =
        rootSpan τ L ((S.ρ : (Fin τ.rank → ℤ) → _)^[l] '' componentRoots χ i) := by
      rw [← hj']; rfl
    rw [this]; exact hy
  have := Subgroup.mem_centralizer_iff.1 (hle hxS) y hyS
  exact this.symm

@[expose] noncomputable def famOrbitFamily
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots χ i = componentRoots χ i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots χ i ≠ componentRoots χ i) :
    CycFamily S.D.step s where
  S k := rootSpan τ L ((S.ρ : (Fin τ.rank → ℤ) → _)^[k.val] '' componentRoots χ i)
  map_eq k := by
    rw [map_rootSpan_step S _ (fun γ hγ => famOrbit_isRoot_of_mem_iterate_image S i k.val hγ)]
    congr 1
    rw [← Set.image_comp, ← Function.iterate_succ', val_add_one_eq,
      ← iterate_image_period S hs (k.val + 1)]
  comm j k hjk x hx y hy := by
    have hne : j.val ≠ k.val := fun h => hjk (ZMod.val_injective s h)
    rcases lt_or_gt_of_ne hne with h | h
    · exact famOrbit_commute_orbit_lt S hρ i hmin h (ZMod.val_lt k) x hx y hy
    · exact (famOrbit_commute_orbit_lt S hρ i hmin h (ZMod.val_lt j) y hy x hx).symm

theorem famOrbitFamily_S
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots χ i = componentRoots χ i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots χ i ≠ componentRoots χ i)
    (k : ZMod s) :
    (famOrbitFamily S hρ i hs hmin).S k =
      rootSpan τ L ((S.ρ : (Fin τ.rank → ℤ) → _)^[k.val] '' componentRoots χ i) :=
  rfl

theorem famOrbitFamily_A
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) {s : ℕ} [NeZero s]
    (hs : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots χ i = componentRoots χ i)
    (hmin : ∀ k, 0 < k → k < s →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[k] '' componentRoots χ i ≠ componentRoots χ i) :
    (famOrbitFamily S hρ i hs hmin).A = rootSpan τ L (rationalRootsM S.ρ χ i) := by
  apply le_antisymm
  · refine iSup_le fun k => ?_
    refine rootSpan_mono ?_
    rintro _ ⟨δ, hδ, rfl⟩
    exact ⟨k.val, δ, hδ, rfl⟩
  · refine iSup₂_le fun γ hγ => ?_
    obtain ⟨m, δ, hδ, rfl⟩ := hγ
    have hk : (S.ρ : (Fin τ.rank → ℤ) → _)^[m] δ ∈
        (S.ρ : (Fin τ.rank → ℤ) → _)^[(m : ZMod s).val] '' componentRoots χ i := by
      rw [ZMod.val_natCast, ← iterate_image_period S hs m]
      exact ⟨δ, hδ, rfl⟩
    exact le_trans (show rootSubgroup τ L ((S.ρ : (Fin τ.rank → ℤ) → _)^[m] δ) ≤
      rootSpan τ L ((S.ρ : (Fin τ.rank → ℤ) → _)^[(m : ZMod s).val] ''
        componentRoots χ i) from le_iSup₂_of_le _ hk le_rfl)
      (le_iSup (fun k : ZMod s => (famOrbitFamily S hρ i hs hmin).S k) (m : ZMod s))

end CFSG.StandardType.TableCRes
