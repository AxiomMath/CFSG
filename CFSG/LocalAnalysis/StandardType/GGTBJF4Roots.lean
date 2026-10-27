module

public import CFSG.LocalAnalysis.StandardType.GGTBJF4Defs
public import CFSG.LocalAnalysis.StandardType.GGTBJF4Weyl
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LieType.Chevalley.F4FieldTwoEuclid
public import CFSG.LocalAnalysis.StandardType.GGTBJF4RootsAux

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

theorem ggTBJ_f4_abs_corootPair_le
    {β γ : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β)
    (hγ : IsRoot Tag.F4 γ) : |corootPair γ β| ≤ 2 := by
  obtain ⟨k, rfl⟩ := isRoot_f4_iff.1 hβ
  obtain ⟨l, rfl⟩ := isRoot_f4_iff.1 hγ
  exact ggTBJ_f4_corootPair_le_fin k l

theorem ggTBJ_f4_corootPair_ne_zero_zmod
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {β γ : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β) (hγ : IsRoot Tag.F4 γ)
    (h : iform β γ ≠ 0) : (corootPair γ β : ZMod p) ≠ 0 := by
  have hγβ : iform γ β ≠ 0 := by rw [iform_comm]; exact h
  have hmul : corootPair γ β * iform γ γ = 2 * iform γ β := corootPair_mul hγ β
  have hcne : corootPair γ β ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    exact hγβ (by omega)
  exact ggTBJ_zmod_intCast_ne_zero_of_abs_le_two hp hp2
    (ggTBJ_f4_abs_corootPair_le hβ hγ) hcne

theorem ggTBJ_fun_vec
    (p : ℕ) [Fact p.Prime] {β γ : Fin 4 → ℤ} (hγ : IsRoot Tag.F4 γ) :
    ggTBJFun p β (ggTBJVec p γ) = (corootPair (τ := Tag.F4) γ β : ZMod p) := by
  rw [ggTBJFun_apply]
  simp only [ggTBJVec]
  rw [show (∑ i : Fin 4, (β i : ZMod p) *
        (corootPair (τ := Tag.F4) γ (Pi.single i 1) : ZMod p)) =
      ((∑ i : Fin 4, β i * corootPair (τ := Tag.F4) γ (Pi.single i 1) : ℤ) : ZMod p) by
    rw [Int.cast_sum]
    exact Finset.sum_congr rfl fun i _ => (Int.cast_mul (β i)
      (corootPair (τ := Tag.F4) γ (Pi.single i 1))).symm]
  rw [ggTBJ_corootPair_expand Tag.F4 hγ β]
  rfl

theorem ggTBJ_fun_vec_self
    (p : ℕ) [Fact p.Prime] {β : Fin 4 → ℤ} (hβ : IsRoot Tag.F4 β) :
    ggTBJFun p β (ggTBJVec p β) = 2 := by
  rw [ggTBJ_fun_vec p hβ, ggTBJ_corootPair_self Tag.F4 hβ]
  norm_num

theorem ggTBJ_f4_connected
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin Tag.F4.rank → ℤ) →* M} (i : KernelComponent χ)
    (S : Set (Fin Tag.F4.rank → ℤ)) (hS : S ⊆ componentRoots χ i) (hne : S.Nonempty)
    (hclosed : ∀ β ∈ componentRoots χ i, ∀ γ ∈ componentRoots χ i,
      ((corootPair γ β : ZMod p) ≠ 0 ∨ (corootPair β γ : ZMod p) ≠ 0) → (β ∈ S ↔ γ ∈ S)) :
    S = componentRoots χ i := by
  apply Set.Subset.antisymm hS
  have hstep : ∀ a c : kernelRoots χ,
      (a : Fin Tag.F4.rank → ℤ) ⬝ᵥ
        (Matrix.mulVec Tag.F4.symmetrizedCartan (c : Fin Tag.F4.rank → ℤ)) ≠ 0 →
      (a : Fin Tag.F4.rank → ℤ) ∈ S → (c : Fin Tag.F4.rank → ℤ) ∈ S := by
    intro a c hgen haS
    have hiform : iform (a : Fin Tag.F4.rank → ℤ) (c : Fin Tag.F4.rank → ℤ) ≠ 0 := by
      rw [← dotProduct_mulVec_eq_iform]
      exact hgen
    have haM : (a : Fin Tag.F4.rank → ℤ) ∈ componentRoots χ i := hS haS
    have hcM : (c : Fin Tag.F4.rank → ℤ) ∈ componentRoots χ i := by
      refine ⟨c.2, ?_⟩
      exact (mk_eq_of_iform_ne_zero (α := a) (β := c) hiform).symm.trans haM.2
    have hpair : (corootPair (τ := Tag.F4) (c : Fin Tag.F4.rank → ℤ)
        (a : Fin Tag.F4.rank → ℤ) : ZMod p) ≠ 0 :=
      ggTBJ_f4_corootPair_ne_zero_zmod hp hp2 a.2.1 c.2.1 hiform
    exact (hclosed (a : Fin Tag.F4.rank → ℤ) haM (c : Fin Tag.F4.rank → ℤ) hcM
      (Or.inl hpair)).1 haS
  have hstep' : ∀ a c : kernelRoots χ,
      (a : Fin Tag.F4.rank → ℤ) ⬝ᵥ
        (Matrix.mulVec Tag.F4.symmetrizedCartan (c : Fin Tag.F4.rank → ℤ)) ≠ 0 →
      (c : Fin Tag.F4.rank → ℤ) ∈ S → (a : Fin Tag.F4.rank → ℤ) ∈ S := by
    intro a c hgen hcS
    have hiform : iform (a : Fin Tag.F4.rank → ℤ) (c : Fin Tag.F4.rank → ℤ) ≠ 0 := by
      rw [← dotProduct_mulVec_eq_iform]
      exact hgen
    have hiform' : iform (c : Fin Tag.F4.rank → ℤ) (a : Fin Tag.F4.rank → ℤ) ≠ 0 := by
      rwa [iform_comm] at hiform
    exact hstep c a (by rwa [dotProduct_mulVec_eq_iform]) hcS
  have hkey : ∀ a c : kernelRoots χ, (kernelRootSetoid χ).r a c →
      ((a : Fin Tag.F4.rank → ℤ) ∈ S ↔ (c : Fin Tag.F4.rank → ℤ) ∈ S) := by
    intro a c h
    induction h with
    | refl => exact Iff.rfl
    | rel x y hxy => exact ⟨hstep x y hxy, hstep' x y hxy⟩
    | symm x y _ ih => exact ih.symm
    | trans x y z _ _ ihxy ihyz => exact ihxy.trans ihyz
  intro γ hγ
  obtain ⟨hγk, hγi⟩ := hγ
  obtain ⟨b, hbS⟩ := hne
  obtain ⟨hbk, hbi⟩ := hS hbS
  have hb0 : (⟦(⟨b, hbk⟩ : kernelRoots χ)⟧ : KernelComponent χ) = i := hbi
  have hg0 : (⟦(⟨γ, hγk⟩ : kernelRoots χ)⟧ : KernelComponent χ) = i := hγi
  exact (hkey ⟨b, hbk⟩ ⟨γ, hγk⟩ (Quotient.exact (hb0.trans hg0.symm))).1 hbS

end CFSG.StandardType

end
