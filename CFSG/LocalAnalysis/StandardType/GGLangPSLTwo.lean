module

public import CFSG.LocalAnalysis.StandardType.GGLangOrbitTwoTypeA
public import CFSG.LocalAnalysis.GLTheoremA.CatC.RationalTypeAModel
public import CFSG.LieType.SeitzGeneration.SeitzStatus

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieComp
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  CFSG.LocalAnalysis.GLTheoremA.RationalModel

theorem rationalComponent_typeA_psl_of_rho_pow_eq_id
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ p : ℕ} (S : LangSetup τ L p₀)
    (hp : p.Prime) {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus)
    (hap : ∀ j, a j ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1) (i : KernelComponent (rootCharHom a))
    (hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1))
    (hQS : CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hid : ∀ γ ∈ componentRoots (rootCharHom a) i,
      (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)] γ =
        γ) :
    ∃ ν f, 2 ≤ ν ∧ 1 ≤ f ∧
      ringChar L ^ f = S.D.q ^ componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) ∧
      StatedClassicalModel (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
        .PSL ν (ringChar L) f := by
  classical
  have hℓp : ringChar L ≠ p := ringChar_ne_of_pow_eq_one hp hap h1
  by_cases hr1 : compRank (componentRoots (rootCharHom a) i) = 1
  · obtain ⟨f, hf1, hfeq, hmodel⟩ :=
      rationalComponent_rankOne_model S hT i hr1 (by rw [hA.2, hr1]) hQS
    exact ⟨2, f, le_rfl, hf1, hfeq, hmodel⟩
  · have h2 : 2 ≤ compRank (componentRoots (rootCharHom a) i) := by omega
    have hTp := rootDiagUnit_pow_eq_one_of_forall hap
    have hpL : ((p : ℕ) : L) ≠ 0 := natCast_ne_zero_of_ringChar_ne hp hℓp
    obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨ⟩ := exists_frame_of_typeA_tag_T_of_prime
      g2LongA2Frame_proved S hp hpL hTp i h2 hA.2
    obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
    set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
    have hmaps : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈ frameRoots σ := by
      intro x y hxy
      have hm1 : σ x y ∈ componentRoots (rootCharHom a) i := by
        rw [hΨ]
        exact ⟨x, y, hxy, rfl⟩
      have hm2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈
          (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i := ⟨_, hm1, rfl⟩
      rw [hs, hΨ] at hm2
      exact hm2
    have hneg : ∀ (n : ℕ) (γ : Fin τ.rank → ℤ),
        (S.ρ : (Fin τ.rank → ℤ) → _)^[n] (-γ) = -(S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ := by
      intro n
      induction n with
      | zero => exact fun γ => rfl
      | succ n ih =>
        intro γ
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
    rcases hψ.aut_cases hν hκ hnorm ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) hmaps (hneg s)
        (iform_rho_iterate S s) with ⟨π, hπ⟩ | ⟨π, hπ⟩
    · obtain ⟨f, hf1, hfeq, hmodel⟩ :=
        rationalComponent_splitFrame_model S hT i hν hψ hΨ π hπ
      exact ⟨ν, f, by omega, hf1, hfeq, hmodel⟩
    · exfalso
      have hfix : ∀ x y, x ≠ y → σ x y = σ (π y) (π x) := by
        intro x y hxy
        have hm : σ x y ∈ componentRoots (rootCharHom a) i := by
          rw [hΨ]
          exact ⟨x, y, hxy, rfl⟩
        exact (hid _ hm).symm.trans (hπ x y hxy)
      let x0 : Fin ν := ⟨0, by omega⟩
      let x1 : Fin ν := ⟨1, by omega⟩
      let x2 : Fin ν := ⟨2, by omega⟩
      have h01 : x0 ≠ x1 := fun h => by simpa [x0, x1] using congrArg Fin.val h
      have h02 : x0 ≠ x2 := fun h => by simpa [x0, x2] using congrArg Fin.val h
      have h12 : x1 ≠ x2 := fun h => by simpa [x1, x2] using congrArg Fin.val h
      have e1 := hψ.eq_of_eq hκ hnorm h01 (π.injective.ne h01.symm) (hfix x0 x1 h01)
      have e2 := hψ.eq_of_eq hκ hnorm h02 (π.injective.ne h02.symm) (hfix x0 x2 h02)
      exact h12 (e1.2.trans e2.2.symm)

private theorem orbitTwo_charP_two
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ f : ℕ} (S : LangSetup τ L p₀)
    (hq : S.D.q = 2 ^ f) : CharP L 2 := by
  have hf0 : f ≠ 0 := by
    rintro rfl
    have h := S.hqpow.1
    rw [hq, pow_zero] at h
    exact not_isPrimePow_one h
  have h2L : ((2 : ℕ) : L) = 0 := by
    have h := S.hqpow.2
    rw [hq, Nat.cast_pow] at h
    exact (pow_eq_zero_iff hf0).1 h
  exact (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 h2L

theorem langPSLOfLengthTwo :
    ∀ (τ : Tag) (L : Type) [Field L] [IsAlgClosed L] (p₀ p f : ℕ) (S : LangSetup τ L p₀),
      (τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) → p.Prime → p ≠ 2 → (p : L) ≠ 0 →
      S.D.q = 2 ^ f → ∀ (π : Equiv.Perm (Fin τ.rank)),
        (∀ j k, τ.cartan (π j) (π k) = τ.cartan j k) → ∀ (ε : ℤ), (ε = 1 ∨ ε = -1) →
        (∀ γ, IsRoot τ γ → S.ρ γ = ε • latPerm π γ) →
        ∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ S.D.torus → (∀ i, a i ^ p = 1) →
          rootDiagUnit τ a ≠ 1 → ∀ i : KernelComponent (rootCharHom a),
            CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) →
            rationalRoots S.ρ (rootCharHom a) i ≠ componentRoots (rootCharHom a) i →
            ∃ k : ℕ, LieModel
              (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
                Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i))
              .PSL k 2 (2 * f) := by
  classical
  intro τ L _ _ p₀ p f S hτ hp _ _ hq π hπ ε hε hρ a hT hap h1 i hQS hne
  haveI : CharP L 2 := orbitTwo_charP_two S hq
  obtain ⟨-, hlen, hcases⟩ := langOrbitTwo_data S hτ π hπ hε hρ hT i hne
  have hA : 1 ≤ compRank (componentRoots (rootCharHom a) i) ∧
      (componentRoots (rootCharHom a) i).ncard = compRank (componentRoots (rootCharHom a) i) *
        (compRank (componentRoots (rootCharHom a) i) + 1) := by
    rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] <;> norm_num
  have hid : ∀ γ ∈ componentRoots (rootCharHom a) i,
      (S.ρ : (Fin τ.rank → ℤ) → _)^[componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)] γ =
        γ := by
    intro γ hγ
    rw [hlen]
    exact rho_rho_eq_of_latPerm S hτ π hπ hε hρ hγ.1.1
  obtain ⟨ν, f', -, -, hfeq, hmodel⟩ :=
    rationalComponent_typeA_psl_of_rho_pow_eq_id S hp hT hap h1 i hA hQS hid
  rw [hlen, hq, ringChar.eq L 2, ← pow_mul] at hfeq
  have hf'2 : f' = 2 * f := by
    have := Nat.pow_right_injective (le_refl 2) hfeq
    omega
  rw [ringChar.eq L 2, hf'2] at hmodel
  exact ⟨ν, Or.inl ⟨by simp [classicalTags], hmodel⟩⟩

end CFSG.StandardType.LangRat
