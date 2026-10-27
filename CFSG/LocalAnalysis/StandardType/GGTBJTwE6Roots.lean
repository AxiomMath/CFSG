module

public import CFSG.LocalAnalysis.StandardType.GGTBJF4RootsAux
public import CFSG.LocalAnalysis.StandardType.GGTBJF4Weyl
public import CFSG.LocalAnalysis.StandardType.GGExcSplitRootGenModel
public import CFSG.LieType.Chevalley.SignKernelSimpleWeyl

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

@[expose] def ggTBJTwE6Fun (p : ℕ) (β : Fin Tag.E6.rank → ℤ) (t : Fin Tag.E6.rank → ZMod p) :
    ZMod p :=
  ∑ j, (β j : ZMod p) * t j

@[expose] def ggTBJTwE6Vec (p : ℕ) (γ : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ZMod p :=
  fun i => (corootPair (τ := Tag.E6) γ (Pi.single i 1) : ZMod p)

theorem ggTBJ_e6_corootPair_le_fin
    (k l : Fin 72) :
    |corootPair (τ := Tag.E6) (Tag.E6.rootCertificate.root l)
      (Tag.E6.rootCertificate.root k)| ≤ 2 := by
  revert k l
  decide +kernel

private theorem ggTBJTwE6RootsAux_e6_rootCertificate_length :
    Tag.E6.rootCertificate.roots.length = 72 := by
  rw [Tag.rootCertificate_length]
  rfl

theorem isRoot_e6_iff_cert {v : Fin Tag.E6.rank → ℤ} :
    IsRoot .E6 v ↔ ∃ k : Fin 72, Tag.E6.rootCertificate.root k = v := by
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E6),
    ggTBJTwE6RootsAux_e6_rootCertificate_length]
  exact ⟨fun ⟨k, hk, h⟩ => ⟨⟨k, hk⟩, h⟩, fun ⟨k, h⟩ => ⟨k, k.2, h⟩⟩

theorem ggTBJ_e6_abs_corootPair_le
    {β γ : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) (hγ : IsRoot Tag.E6 γ) :
    |corootPair γ β| ≤ 2 := by
  obtain ⟨k, rfl⟩ := isRoot_e6_iff_cert.1 hβ
  obtain ⟨l, rfl⟩ := isRoot_e6_iff_cert.1 hγ
  exact ggTBJ_e6_corootPair_le_fin k l

theorem ggTBJ_e6_corootPair_ne_zero_zmod
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {β γ : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) (hγ : IsRoot Tag.E6 γ)
    (h : iform β γ ≠ 0) : (corootPair γ β : ZMod p) ≠ 0 := by
  have hγβ : iform γ β ≠ 0 := by rw [iform_comm]; exact h
  have hmul : corootPair γ β * iform γ γ = 2 * iform γ β := corootPair_mul hγ β
  have hcne : corootPair γ β ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hmul
    exact hγβ (by omega)
  exact ggTBJ_zmod_intCast_ne_zero_of_abs_le_two hp hp2
    (ggTBJ_e6_abs_corootPair_le hβ hγ) hcne

theorem ggTBJ_e6_connected
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin Tag.E6.rank → ℤ) →* M} (i : KernelComponent χ)
    (S : Set (Fin Tag.E6.rank → ℤ)) (hS : S ⊆ componentRoots χ i) (hne : S.Nonempty)
    (hclosed : ∀ β ∈ componentRoots χ i, ∀ γ ∈ componentRoots χ i,
      ((corootPair γ β : ZMod p) ≠ 0 ∨ (corootPair β γ : ZMod p) ≠ 0) → (β ∈ S ↔ γ ∈ S)) :
    S = componentRoots χ i := by
  apply Set.Subset.antisymm hS
  have hstep : ∀ a c : kernelRoots χ,
      (a : Fin Tag.E6.rank → ℤ) ⬝ᵥ
        (Matrix.mulVec Tag.E6.symmetrizedCartan (c : Fin Tag.E6.rank → ℤ)) ≠ 0 →
      (a : Fin Tag.E6.rank → ℤ) ∈ S → (c : Fin Tag.E6.rank → ℤ) ∈ S := by
    intro a c hgen haS
    have hiform : iform (a : Fin Tag.E6.rank → ℤ) (c : Fin Tag.E6.rank → ℤ) ≠ 0 := by
      rw [← dotProduct_mulVec_eq_iform]
      exact hgen
    have haM : (a : Fin Tag.E6.rank → ℤ) ∈ componentRoots χ i := hS haS
    have hcM : (c : Fin Tag.E6.rank → ℤ) ∈ componentRoots χ i := by
      refine ⟨c.2, ?_⟩
      exact (mk_eq_of_iform_ne_zero (α := a) (β := c) hiform).symm.trans haM.2
    have hpair : (corootPair (τ := Tag.E6) (c : Fin Tag.E6.rank → ℤ)
        (a : Fin Tag.E6.rank → ℤ) : ZMod p) ≠ 0 :=
      ggTBJ_e6_corootPair_ne_zero_zmod hp hp2 a.2.1 c.2.1 hiform
    exact (hclosed (a : Fin Tag.E6.rank → ℤ) haM (c : Fin Tag.E6.rank → ℤ) hcM
      (Or.inl hpair)).1 haS
  have hstep' : ∀ a c : kernelRoots χ,
      (a : Fin Tag.E6.rank → ℤ) ⬝ᵥ
        (Matrix.mulVec Tag.E6.symmetrizedCartan (c : Fin Tag.E6.rank → ℤ)) ≠ 0 →
      (c : Fin Tag.E6.rank → ℤ) ∈ S → (a : Fin Tag.E6.rank → ℤ) ∈ S := by
    intro a c hgen hcS
    have hiform : iform (a : Fin Tag.E6.rank → ℤ) (c : Fin Tag.E6.rank → ℤ) ≠ 0 := by
      rw [← dotProduct_mulVec_eq_iform]
      exact hgen
    have hiform' : iform (c : Fin Tag.E6.rank → ℤ) (a : Fin Tag.E6.rank → ℤ) ≠ 0 := by
      rwa [iform_comm] at hiform
    exact hstep c a (by rwa [dotProduct_mulVec_eq_iform]) hcS
  have hkey : ∀ a c : kernelRoots χ, (kernelRootSetoid χ).r a c →
      ((a : Fin Tag.E6.rank → ℤ) ∈ S ↔ (c : Fin Tag.E6.rank → ℤ) ∈ S) := by
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

theorem ggTBJTwE6_excRefl_eq
    {p : ℕ} {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) (t : Fin Tag.E6.rank → ZMod p) :
    ExcSplitRootGen.excRefl (p := p) γ t = t - ggTBJTwE6Fun p γ t • ggTBJTwE6Vec p γ := by
  funext i
  rw [ExcSplitRootGen.excRefl_apply (p := p) hγ]
  simp only [ggTBJTwE6Fun, ggTBJTwE6Vec, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem ggTBJTwE6_fun_vec
    (p : ℕ) {β γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    ggTBJTwE6Fun p β (ggTBJTwE6Vec p γ) = (corootPair (τ := Tag.E6) γ β : ZMod p) := by
  simp only [ggTBJTwE6Fun, ggTBJTwE6Vec]
  rw [show (∑ i : Fin Tag.E6.rank, (β i : ZMod p) *
        (corootPair (τ := Tag.E6) γ (Pi.single i 1) : ZMod p)) =
      ((∑ i : Fin Tag.E6.rank, β i * corootPair (τ := Tag.E6) γ (Pi.single i 1) : ℤ) :
        ZMod p) by
    rw [Int.cast_sum]
    exact Finset.sum_congr rfl fun i _ => (Int.cast_mul (β i)
      (corootPair (τ := Tag.E6) γ (Pi.single i 1))).symm]
  rw [ggTBJ_corootPair_expand (τ := Tag.E6) hγ β]

theorem ggTBJTwE6_fun_vec_self
    (p : ℕ) {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    ggTBJTwE6Fun p γ (ggTBJTwE6Vec p γ) = 2 := by
  rw [ggTBJTwE6_fun_vec p hγ, ggTBJ_corootPair_self Tag.E6 hγ]
  norm_num

end CFSG.StandardType

end
