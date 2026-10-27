module

public import CFSG.LocalAnalysis.StandardType.GGFamSLRecogDefs
public import CFSG.LocalAnalysis.StandardType.GGFamRatComp
public import CFSG.LocalAnalysis.StandardType.GGFamIsolation
public import CFSG.LocalAnalysis.GLTheoremA.CatC.RationalTypeAModel

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
  CFSG.RankThree.Classical2
open scoped MatrixGroups commutatorElement

private theorem famFrames_period_of_stable
    {τ : Tag} {M : Type*} [CommGroup M]
    (ρ : Equiv.Perm (Fin τ.rank → ℤ))
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, ρ γ ∈ kernelRoots χ) (i : KernelComponent χ) :
    0 < componentOrbitLength ρ (componentRoots χ i) ∧
      (ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength ρ (componentRoots χ i)] ''
        componentRoots χ i = componentRoots χ i := by
  have hfin : (kernelRoots χ).Finite :=
    (finite_setOf_isRoot τ).subset fun α hα => hα.1
  obtain ⟨d, hd, hfix⟩ :=
    exists_iterate_eq_of_mapsTo hfin (fun γ hγ => hρ γ hγ) ρ.injective.injOn
  have hper : (ρ : (Fin τ.rank → ℤ) → _)^[d] '' componentRoots χ i =
      componentRoots χ i := by
    ext γ
    constructor
    · rintro ⟨δ, hδ, rfl⟩
      rw [hfix δ hδ.1]
      exact hδ
    · intro hγ
      exact ⟨γ, hγ, hfix γ hγ.1⟩
  have hne : {s : ℕ | 0 < s ∧
      (ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots χ i = componentRoots χ i}.Nonempty :=
    ⟨d, hd, hper⟩
  exact Nat.sInf_mem hne

theorem fam_exists_pair_of_rank_one
    {τ : Tag} {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} (i : KernelComponent χ)
    (hn : (componentRoots χ i).ncard = 2) :
    ∃ β : Fin τ.rank → ℤ, IsRoot τ β ∧ componentRoots χ i = {β, -β} := by
  classical
  obtain ⟨x, y, hxy, hxy'⟩ := Set.ncard_eq_two.1 hn
  have hΨ := isRootComponent_componentRoots (χ := χ) i
  have hx : x ∈ componentRoots χ i := by rw [hxy']; exact Set.mem_insert _ _
  have hxr : IsRoot τ x := hΨ.isRoot x hx
  have hnx : -x ∈ componentRoots χ i := hΨ.neg_mem x hx
  rw [hxy'] at hnx
  have hne : -x ≠ x := by
    intro h
    have h0 : x = 0 := by
      have h2 : (2 : ℤ) • x = 0 := by
        rw [two_smul]
        nth_rewrite 1 [← h]
        exact neg_add_cancel x
      funext j
      have := congrFun h2 j
      simp only [Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at this
      simp only [Pi.zero_apply]
      omega
    have := iform_self_pos_of_isRoot hxr
    rw [h0] at this
    simp [iform] at this
  refine ⟨x, hxr, ?_⟩
  rcases hnx with h | h
  · exact absurd h hne
  · rw [hxy', h]

theorem fam_frame_return_cases
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {M : Type*} [CommGroup M]
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M}
    (hρ : ∀ γ ∈ kernelRoots χ, S.ρ γ ∈ kernelRoots χ) (i : KernelComponent χ)
    {ν : ℕ} (hν : 3 ≤ ν) {ψ : SL(ν, L) →* ModGL τ L}
    {σ : Fin ν → Fin ν → Fin τ.rank → ℤ} (hψ : IsSLFrame ψ σ)
    {κ : ℤ} (hκ : κ ≠ 0)
    (hnorm : ∀ x y, x ≠ y → iform (σ x y) (σ x y) = 2 * κ)
    (hΨ : componentRoots χ i = frameRoots σ) :
    (∃ π : Equiv.Perm (Fin ν), ∀ x y, x ≠ y →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots χ i)]
        (σ x y) = σ (π x) (π y)) ∨
    (∃ π : Equiv.Perm (Fin ν), ∀ x y, x ≠ y →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots χ i)]
        (σ x y) = σ (π y) (π x)) := by
  classical
  obtain ⟨-, hs⟩ := famFrames_period_of_stable S.ρ (fun γ hγ => hρ γ hγ) i
  have hmaps : ∀ x y, x ≠ y →
      (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots χ i)]
        (σ x y) ∈ frameRoots σ := by
    intro x y hxy
    have h1 : σ x y ∈ componentRoots χ i := by
      rw [hΨ]
      exact ⟨x, y, hxy, rfl⟩
    have h2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots χ i)]
        (σ x y) ∈ (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots χ i)]
          '' componentRoots χ i := ⟨_, h1, rfl⟩
    rw [hs] at h2
    exact hΨ ▸ h2
  have hneg : ∀ (n : ℕ) (γ : Fin τ.rank → ℤ),
      (S.ρ : (Fin τ.rank → ℤ) → _)^[n] (-γ) = -(S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ := by
    intro n
    induction n with
    | zero => exact fun γ => rfl
    | succ n ih =>
      intro γ
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
  have hform : ∀ γ δ, iform
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots χ i)] γ)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots χ i)] δ) =
      iform γ δ := by
    intro γ δ
    induction componentOrbitLength S.ρ (componentRoots χ i) with
    | zero => rfl
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', S.frob.iform_eq, ih]
  rcases hψ.aut_cases hν hκ hnorm
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots χ i)])
      hmaps (hneg _) hform with ⟨π, hπ⟩ | ⟨π, hπ⟩
  · exact Or.inl ⟨π, hπ⟩
  · exact Or.inr ⟨π, hπ⟩

theorem fam_typeA_frame_cases
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p₀ p : ℕ} (S : LangSetup τ L p₀) (hp : p.Prime)
    {ι : Type} {a : ι → Fin τ.rank → Lˣ}
    (hT : ∀ u, rootDiagUnit τ (a u) ∈ S.D.torus) (hap : ∀ u j, a u j ^ p = 1)
    (h1 : ∃ u, rootDiagUnit τ (a u) ≠ 1)
    (i : KernelComponent (famCharHom a))
    (hA : 1 ≤ compRank (componentRoots (famCharHom a) i) ∧
      (componentRoots (famCharHom a) i).ncard = compRank (componentRoots (famCharHom a) i) *
        (compRank (componentRoots (famCharHom a) i) + 1)) :
    (compRank (componentRoots (famCharHom a) i) = 1 ∧
        (componentRoots (famCharHom a) i).ncard = 2) ∨
      (∃ (ν : ℕ) (ψ : SL(ν, L) →* ModGL τ L) (σ : Fin ν → Fin ν → Fin τ.rank → ℤ)
        (π : Equiv.Perm (Fin ν)),
        3 ≤ ν ∧ IsSLFrame ψ σ ∧ componentRoots (famCharHom a) i = frameRoots σ ∧
          ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (famCharHom a) i)] (σ x y) = σ (π x) (π y)) ∨
      (∃ (ν : ℕ) (ψ : SL(ν, L) →* ModGL τ L) (σ : Fin ν → Fin ν → Fin τ.rank → ℤ)
        (π : Equiv.Perm (Fin ν)),
        3 ≤ ν ∧ IsSLFrame ψ σ ∧ componentRoots (famCharHom a) i = frameRoots σ ∧
          ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ
            (componentRoots (famCharHom a) i)] (σ x y) = σ (π y) (π x)) := by
  classical
  obtain ⟨u, hu⟩ := h1
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp (fun j => hap u j) hu
  have hchar2 : ringChar L = 2 := ringChar.eq L 2
  have hp2 : p ≠ 2 := by
    intro hp2'
    exact hℓp (by rw [hchar2, hp2'])
  obtain ⟨N, b, j, hNprime, hN2, hbN, hjb⟩ := exists_isolating_element hτ a hp hp2 hap i
  by_cases hr1 : compRank (componentRoots (famCharHom a) i) = 1
  · exact Or.inl ⟨hr1, by rw [hA.2, hr1]⟩
  · have h2 : 2 ≤ compRank (componentRoots (famCharHom a) i) := by omega
    have hn : (componentRoots (rootCharHom b) j).ncard =
        compRank (componentRoots (rootCharHom b) j) *
          (compRank (componentRoots (rootCharHom b) j) + 1) := by
      rw [hjb]
      exact hA.2
    have h2b : 2 ≤ compRank (componentRoots (rootCharHom b) j) := by
      rw [hjb]
      exact h2
    have hNL : (N : L) ≠ 0 :=
      natCast_ne_zero_of_ringChar_ne hNprime (by rw [hchar2]; exact Ne.symm hN2)
    obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨb⟩ :=
      exists_frame_of_typeA_tag_T_of_prime g2LongA2Frame_proved S hNprime hNL hbN j h2b hn
    have hΨ : componentRoots (famCharHom a) i = frameRoots σ := hjb.symm.trans hΨb
    have hρ : ∀ γ ∈ kernelRoots (famCharHom a), S.ρ γ ∈ kernelRoots (famCharHom a) :=
      fun γ hγ => rho_mem_kernelRoots_famChar S a hT hγ
    rcases fam_frame_return_cases S hρ i hν hψ hκ hnorm hΨ with ⟨π, hπ⟩ | ⟨π, hπ⟩
    · exact Or.inr (Or.inl ⟨ν, ψ, σ, π, hν, hψ, hΨ, hπ⟩)
    · exact Or.inr (Or.inr ⟨ν, ψ, σ, π, hν, hψ, hΨ, hπ⟩)

end CFSG.StandardType.TableCRes
