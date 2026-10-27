module

public import CFSG.LocalAnalysis.StandardType.GGFamTameOrbit
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerQuasisimpleLang

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped commutatorElement

private theorem famLang_iterate_mem_kernelRoots
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (n : ℕ)
    {γ : Fin τ.rank → ℤ} (hγ : γ ∈ kernelRoots χ) :
    (S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ ∈ kernelRoots χ := by
  induction n with
  | zero => exact hγ
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact hρ _ ih

theorem fam_exists_lang
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) {s : ℕ} (hs : 0 < s) {y : ModGL τ L}
    (hy : y ∈ torusGroup τ L ⊔ rootSpan τ L (kernelRoots χ)) :
    ∃ z : ModGL τ L, iterHom S.D.step s z = z * y ∧
      ∀ j : KernelComponent χ, ∀ g : ModGL τ L,
        g ∈ rootSpan τ L (componentRoots χ j) ↔
          z * g * z⁻¹ ∈ rootSpan τ L (componentRoots χ j) := by
  obtain ⟨z, hzZ, hz⟩ := exists_lang_torus_sup_kernelRoots S hs
    (fun γ hγ => famLang_iterate_mem_kernelRoots S hρ s hγ) hy
  exact ⟨z, hz, mem_componentRootSpan_iff_conj_of_mem hzZ⟩

theorem fam_exists_untwist
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    {M : Type*} [CommGroup M] {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) {s : ℕ}
    (hs : 0 < s)
    (hinner : twistInner (componentRoots χ i) ((S.ρ : (Fin τ.rank → ℤ) → _)^[s])) :
    ∃ (σ : L ≃+* L) (z : ModGL τ L), (∀ c, σ c = c ^ (S.D.q ^ s)) ∧
      (∀ j : KernelComponent χ, ∀ g : ModGL τ L,
        g ∈ rootSpan τ L (componentRoots χ j) ↔
          z * g * z⁻¹ ∈ rootSpan τ L (componentRoots χ j)) ∧
      ∀ g ∈ rootSpan τ L (componentRoots χ i),
        iterHom S.D.step s (z * g * z⁻¹) = z * frobGL σ g * z⁻¹ := by
  classical
  obtain ⟨r, e, hr, hchar, he, hq⟩ := exists_char_pow S
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨σ, hσ⟩ := exists_ringEquiv_frob (L := L) r (e * s)
  have hσc : ∀ c, σ c = c ^ (S.D.q ^ s) := by
    intro c
    have h1 : σ c = iterateFrobenius L r (e * s) c := by
      rw [← hσ]
      rfl
    rw [h1, iterateFrobenius_def, hq, ← pow_mul]
  obtain ⟨w, hw, hwγ⟩ := hinner
  have hφpin : ∀ γ ∈ componentRoots χ i, ∃ m : L, m ≠ 0 ∧
      ∀ c : L, iterHom S.D.step s (pinnedX τ L γ c) = pinnedX τ L (w • γ) (m * σ c) := by
    intro γ hγ
    obtain ⟨μ, hμ0, hμ⟩ := iter_step_pinnedX S s (isRoot_of_mem_componentRoots hγ)
    exact ⟨μ, hμ0, fun c => by rw [iterHom_eq_iterate, hμ, hwγ γ hγ, hσc]⟩
  obtain ⟨y₁, hy₁, hpin⟩ := exists_pin i σ (iterHom S.D.step s) hw hφpin
  obtain ⟨z, hφz, hnorm⟩ :=
    fam_exists_lang S hρ hs ((sup_le_sup_left (rootSpan_mono fun γ hγ => hγ.1) _) hy₁)
  refine ⟨σ, z, hσc, hnorm, fun g hg => ?_⟩
  rw [map_mul, map_mul, map_inv, hφz]
  calc z * y₁ * iterHom S.D.step s g * (z * y₁)⁻¹ =
      z * (y₁ * iterHom S.D.step s g * y₁⁻¹) * z⁻¹ := by group
    _ = z * frobGL σ g * z⁻¹ := by rw [hpin g hg]

end CFSG.StandardType.TableCRes
