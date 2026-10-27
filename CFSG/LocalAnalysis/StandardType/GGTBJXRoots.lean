module

public import CFSG.LocalAnalysis.StandardType.GGTBJXDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJF4Weyl
public import CFSG.LocalAnalysis.StandardType.GGTBJF4RootsAux
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E8KilledPlaneBlocksGeo
public import CFSG.HardMathSupport.Timmesfeld.Torality.LangAssembly

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.NonToralCore

theorem ggTBJX_abs_corootPair_le
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hγ : IsRoot τ γ) : |corootPair γ β| ≤ 2 := by
  have hτ' : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h <;> simp [h]
  have hγγ : iform γ γ = 2 := iform_self_eq_two_of_isRoot_simplyLaced hτ' hγ
  have hmul := corootPair_mul hγ β
  rw [hγγ] at hmul
  have hcy : corootPair γ β = iform γ β := by linarith
  rw [hcy]
  exact abs_iform_le_two_of_isRoot_simplyLaced hτ' hγ hβ

theorem ggTBJX_corootPair_ne_zero_zmod
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ)
    (h : iform β γ ≠ 0) : (corootPair γ β : ZMod p) ≠ 0 := by
  have hγβ : iform γ β ≠ 0 := by rw [iform_comm]; exact h
  have hmul : corootPair γ β * iform γ γ = 2 * iform γ β := corootPair_mul hγ β
  have hcne : corootPair γ β ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    exact hγβ (by omega)
  exact ggTBJ_zmod_intCast_ne_zero_of_abs_le_two hp hp2
    (ggTBJX_abs_corootPair_le hτ hβ hγ) hcne

theorem ggTBJX_fun_vec
    (p : ℕ) [Fact p.Prime] {τ : Tag} {β γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ggTBJXFun p τ β (ggTBJXVec p τ γ) = (corootPair (τ := τ) γ β : ZMod p) := by
  rw [ggTBJXFun_apply]
  simp only [ggTBJXVec]
  rw [show (∑ i : Fin τ.rank, (β i : ZMod p) *
        (corootPair (τ := τ) γ (Pi.single i 1) : ZMod p)) =
      ((∑ i : Fin τ.rank, β i * corootPair (τ := τ) γ (Pi.single i 1) : ℤ) : ZMod p) by
    rw [Int.cast_sum]
    exact Finset.sum_congr rfl fun i _ => (Int.cast_mul (β i)
      (corootPair (τ := τ) γ (Pi.single i 1))).symm]
  rw [ggTBJ_corootPair_expand τ hγ β]

theorem ggTBJX_fun_vec_self
    (p : ℕ) [Fact p.Prime] {τ : Tag} {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) :
    ggTBJXFun p τ β (ggTBJXVec p τ β) = 2 := by
  rw [ggTBJX_fun_vec p hβ, ggTBJ_corootPair_self τ hβ]
  norm_num

theorem ggTBJX_connected
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ)
    (S : Set (Fin τ.rank → ℤ)) (hS : S ⊆ componentRoots χ i) (hne : S.Nonempty)
    (hclosed : ∀ β ∈ componentRoots χ i, ∀ γ ∈ componentRoots χ i,
      ((corootPair γ β : ZMod p) ≠ 0 ∨ (corootPair β γ : ZMod p) ≠ 0) → (β ∈ S ↔ γ ∈ S)) :
    S = componentRoots χ i := by
  apply Set.Subset.antisymm hS
  have hstep : ∀ a c : kernelRoots χ,
      (a : Fin τ.rank → ℤ) ⬝ᵥ
        (Matrix.mulVec τ.symmetrizedCartan (c : Fin τ.rank → ℤ)) ≠ 0 →
      (a : Fin τ.rank → ℤ) ∈ S → (c : Fin τ.rank → ℤ) ∈ S := by
    intro a c hgen haS
    have hiform : iform (a : Fin τ.rank → ℤ) (c : Fin τ.rank → ℤ) ≠ 0 := by
      rw [← dotProduct_mulVec_eq_iform]
      exact hgen
    have haM : (a : Fin τ.rank → ℤ) ∈ componentRoots χ i := hS haS
    have hcM : (c : Fin τ.rank → ℤ) ∈ componentRoots χ i := by
      refine ⟨c.2, ?_⟩
      exact (mk_eq_of_iform_ne_zero (α := a) (β := c) hiform).symm.trans haM.2
    have hpair : (corootPair (τ := τ) (c : Fin τ.rank → ℤ)
        (a : Fin τ.rank → ℤ) : ZMod p) ≠ 0 :=
      ggTBJX_corootPair_ne_zero_zmod hτ hp hp2 a.2.1 c.2.1 hiform
    exact (hclosed (a : Fin τ.rank → ℤ) haM (c : Fin τ.rank → ℤ) hcM
      (Or.inl hpair)).1 haS
  have hstep' : ∀ a c : kernelRoots χ,
      (a : Fin τ.rank → ℤ) ⬝ᵥ
        (Matrix.mulVec τ.symmetrizedCartan (c : Fin τ.rank → ℤ)) ≠ 0 →
      (c : Fin τ.rank → ℤ) ∈ S → (a : Fin τ.rank → ℤ) ∈ S := by
    intro a c hgen hcS
    have hiform : iform (a : Fin τ.rank → ℤ) (c : Fin τ.rank → ℤ) ≠ 0 := by
      rw [← dotProduct_mulVec_eq_iform]
      exact hgen
    have hiform' : iform (c : Fin τ.rank → ℤ) (a : Fin τ.rank → ℤ) ≠ 0 := by
      rwa [iform_comm] at hiform
    exact hstep c a (by rwa [dotProduct_mulVec_eq_iform]) hcS
  have hkey : ∀ a c : kernelRoots χ, (kernelRootSetoid χ).r a c →
      ((a : Fin τ.rank → ℤ) ∈ S ↔ (c : Fin τ.rank → ℤ) ∈ S) := by
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
