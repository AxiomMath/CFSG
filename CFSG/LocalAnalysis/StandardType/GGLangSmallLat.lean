module

public import CFSG.LocalAnalysis.StandardType.GGLangSolvBridge
public import CFSG.LocalAnalysis.StandardType.GGLatDefs

public section

namespace CFSG.StandardType.LangRat

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

theorem rationalRoots_eq_componentRoots_of_mapsTo {τ : Tag} {L : Type} [Field L]
    (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (χ : Multiplicative (Fin τ.rank → ℤ) →* Lˣ)
    (i : KernelComponent χ) (h : ∀ γ ∈ componentRoots χ i, ρ γ ∈ componentRoots χ i) :
    rationalRoots ρ χ i = componentRoots χ i := by
  refine Set.Subset.antisymm ?_ fun γ hγ => ⟨0, γ, hγ, rfl⟩
  rintro _ ⟨k, δ, hδ, rfl⟩
  induction k with
  | zero => exact hδ
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact h _ ih

theorem latSolv_of_langSmallSolv
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ f p : ℕ} (S : LangSetup τ L p₀)
    (hq : S.D.q = 2 ^ f) (hp : p.Prime) (hpL : (p : L) ≠ 0) (π : Equiv.Perm (Fin τ.rank))
    (ε : ℤ) (hε : ε = 1 ∨ ε = -1) (hpε : (p : ℤ) ∣ (S.D.q : ℤ) - ε)
    (hρ : ∀ γ, IsRoot τ γ → S.ρ γ = ε • latPerm π γ)
    {a : Fin τ.rank → Lˣ} (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ j, a j ^ p = 1)
    (i : KernelComponent (rootCharHom a))
    (hsmall : LangSmallSolv S.D.q S.ρ (rootCharHom a) i) :
    LatSolv (f = 1) π (rationalRoots S.ρ (rootCharHom a) i) := by
  classical
  have hΨ := isRootComponent_componentRoots (χ := rootCharHom a) i
  obtain ⟨hs0, hs, -⟩ := outer_componentOrbitLength_spec S hT i
  set s := componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) with hsdef
  have hf0 : f ≠ 0 := by
    rintro rfl
    have h := S.hqpow.1
    rw [hq, pow_zero] at h
    exact not_isPrimePow_one h
  have hnum : S.D.q ^ s ≤ 3 → f = 1 ∧ s = 1 := by
    intro h
    rw [hq, ← pow_mul] at h
    have h1 : f * s ≤ 1 := by
      by_contra hc
      have h4 : 2 ^ 2 ≤ 2 ^ (f * s) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h2 : f ≤ f * s := Nat.le_mul_of_pos_right f hs0
    have h3 : s ≤ f * s := Nat.le_mul_of_pos_left s (Nat.pos_of_ne_zero hf0)
    omega
  have hstab : s = 1 →
      ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i := by
    intro hs1 γ hγ
    rw [hs1, Function.iterate_one] at hs
    rw [← hs]
    exact ⟨γ, hγ, rfl⟩
  rcases hsmall with ⟨hq3, hn2⟩ | ⟨hq2, hk, hn6⟩
  ·
    obtain ⟨hf1, hs1⟩ := hnum hq3
    refine ⟨hf1, Or.inl ?_⟩
    obtain ⟨x, y, hxy, hC⟩ := Set.ncard_eq_two.1 hn2
    have hx : x ∈ componentRoots (rootCharHom a) i := by
      rw [hC]
      exact Set.mem_insert _ _
    have hx0 : x ≠ 0 := (hΨ.isRoot x hx).ne_zero
    have hnxy : -x = y := by
      have hnx := hΨ.neg_mem x hx
      rw [hC] at hnx
      rcases hnx with h | h
      · exfalso
        apply hx0
        funext k
        have hk := congrFun h k
        simp only [Pi.neg_apply] at hk
        simp only [Pi.zero_apply]
        omega
      · exact h
    refine ⟨x, ?_⟩
    rw [rationalRoots_eq_componentRoots_of_mapsTo S.ρ (rootCharHom a) i (hstab hs1), hC, hnxy]
  ·
    obtain ⟨hf1, hs1⟩ := hnum (hq2.le.trans (by norm_num))
    have hq2' : S.D.q = 2 := by rw [hq, hf1, pow_one]
    have hε1 : ε = -1 := by
      rcases hε with h | h
      · exfalso
        have h1 : (p : ℤ) ∣ ((1 : ℕ) : ℤ) := by
          have := hpε
          rw [h, hq2'] at this
          simpa using this
        exact hp.one_lt.ne' (Nat.dvd_one.1 (Int.natCast_dvd_natCast.1 h1))
      · exact h
    rw [rationalRoots_eq_componentRoots_of_mapsTo S.ρ (rootCharHom a) i (hstab hs1)]
    refine ⟨hf1, Or.inr ⟨hn6, ?_⟩⟩
    have hTp := rootDiagUnit_pow_eq_one_of_forall hap
    obtain ⟨h2, hn⟩ := suN_rank_ncard hk
    obtain ⟨ν, ψ, σ, κ, hν, hψ, hκ, hnorm, hΨσ⟩ :=
      exists_frame_of_typeA_tag_T_of_prime g2LongA2Frame_proved S hp hpL hTp i h2 hn
    have hout : ¬ twistInner (componentRoots (rootCharHom a) i)
        ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) := by
      intro h
      unfold twistKind at hk
      rw [ite_eq_left_iff.2 (fun h' => absurd h h')] at hk
      exact absurd hk (by decide)
    have hmaps : ∀ x y, x ≠ y → (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈ frameRoots σ := by
      intro x y hxy
      have h1 : σ x y ∈ componentRoots (rootCharHom a) i := by
        rw [hΨσ]
        exact ⟨x, y, hxy, rfl⟩
      have h2 : (S.ρ : (Fin τ.rank → ℤ) → _)^[s] (σ x y) ∈
          (S.ρ : (Fin τ.rank → ℤ) → _)^[s] '' componentRoots (rootCharHom a) i := ⟨_, h1, rfl⟩
      rw [hs, hΨσ] at h2
      exact h2
    have hneg : ∀ (n : ℕ) (γ : Fin τ.rank → ℤ),
        (S.ρ : (Fin τ.rank → ℤ) → _)^[n] (-γ) = -(S.ρ : (Fin τ.rank → ℤ) → _)^[n] γ := by
      intro n
      induction n with
      | zero => exact fun γ => rfl
      | succ n ih =>
        intro γ
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, S.frob.neg_eq]
    rcases hψ.aut_cases hν hκ hnorm ((S.ρ : (Fin τ.rank → ℤ) → _)^[s]) hmaps (hneg s)
        (iform_rho_iterate S s) with ⟨π', hπ'⟩ | ⟨π', hπ'⟩
    ·
      exfalso
      apply hout
      obtain ⟨w, hw, hwσ⟩ := hψ.exists_weyl_perm hκ hnorm π'
      refine ⟨w, ?_, fun γ hγ => ?_⟩
      · rw [hΨσ]
        exact hw
      · rw [hΨσ] at hγ
        obtain ⟨x, y, hxy, rfl⟩ := hγ
        rw [hπ' x y hxy, hwσ]
    ·
      have hlat : ∀ x y, x ≠ y → latPerm π (σ x y) = σ (π' x) (π' y) := by
        intro x y hxy
        have h1 := hπ' x y hxy
        rw [hs1, Function.iterate_one, hρ _ (hψ.isRoot x y hxy), hε1, neg_one_smul ℤ,
          hψ.neg (π' x) (π' y)] at h1
        exact neg_inj.1 h1
      let x₀ : Fin ν := ⟨0, by omega⟩
      let h : Fin ν → ℤ := fun x => height (σ x x₀)
      have hht : ∀ x y, height (σ x y) = h x - h y := by
        intro x y
        rw [hψ.eq_sub x y x₀, height_sub]
      have hperm : ∀ v : Fin τ.rank → ℤ, height (latPerm π v) = height v := by
        intro v
        exact Equiv.sum_comp π.symm v
      have hshift : ∀ x, h (π' x) = h x + (h (π' x₀) - h x₀) := by
        intro x
        by_cases hx : x = x₀
        · rw [hx]
          ring
        · have h1 := hperm (σ x x₀)
          rw [hlat x x₀ hx, hht, hht] at h1
          linarith
      have hc : h (π' x₀) - h x₀ = 0 := by
        have hsum : ∑ x, h (π' x) = ∑ x, (h x + (h (π' x₀) - h x₀)) :=
          Finset.sum_congr rfl fun x _ => hshift x
        rw [Equiv.sum_comp π' h, Finset.sum_add_distrib] at hsum
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
        have h3 : (ν : ℤ) * (h (π' x₀) - h x₀) = 0 := by linarith
        rcases mul_eq_zero.1 h3 with h4 | h4
        · exact absurd h4 (by exact_mod_cast (by omega : ν ≠ 0))
        · exact h4
      have hid : ∀ x, π' x = x := by
        intro x
        by_contra hne
        have hr := hψ.isRoot (π' x) x hne
        have h0 : height (σ (π' x) x) = 0 := by
          rw [hht, hshift x, hc]
          ring
        rcases IsRoot.height_pos_or_neg hr with h5 | h5 <;> omega
      intro α hα
      rw [hΨσ] at hα
      obtain ⟨x, y, hxy, rfl⟩ := hα
      rw [hlat x y hxy, hid, hid]

end CFSG.StandardType.LangRat
