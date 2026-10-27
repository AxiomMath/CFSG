module

public import CFSG.Quasithin.Background.HStandard

public section

namespace CFSG.Quasithin

namespace H

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

variable {K : Type} [Field K]

theorem transvection_mulVec {d : ℕ} (i j : Fin d) (c : K) (v : Fin d → K) :
    Matrix.transvection i j c *ᵥ v = v + Pi.single i (c * v j) := by
  ext k
  simp only [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.single_apply, Pi.single_apply]
  by_cases hk : k = i
  · subst hk
    simp [Finset.sum_ite_eq]
  · simp [hk, Ne.symm hk]

theorem hasScalarCommutant_statedSL {d : ℕ} (hd : 2 ≤ d) :
    HasScalarCommutant (StatedSL d K) := by
  intro f hf
  have ht : ∀ i j : Fin d, i ≠ j → ∀ c : K, ∀ v,
      f (v + Pi.single i (c * v j)) = f v + Pi.single i (c * f v j) := by
    intro i j hij c v
    have hmem : Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j c)
        (by rw [Matrix.det_transvection_of_ne i j hij c]; exact one_ne_zero) ∈ StatedSL d K :=
      Subgroup.subset_closure (by
        change (Matrix.transvection i j c).det = 1
        exact Matrix.det_transvection_of_ne i j hij c)
    have := hf _ hmem v
    simpa [Matrix.GeneralLinearGroup.mkOfDetNeZero, transvection_mulVec] using this
  have hne : ∀ j : Fin d, ∃ i : Fin d, i ≠ j := by
    intro j
    by_cases h : j = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, by rw [h]; simp [Fin.ext_iff]⟩
    · exact ⟨⟨0, by omega⟩, Ne.symm h⟩
  have hline : ∀ k : Fin d, ∀ a : K, ∀ j : Fin d, j ≠ k → f (Pi.single k a) j = 0 := by
    intro k a j hjk
    obtain ⟨i, hij⟩ := hne j
    have h1 := ht i j hij 1 (Pi.single k a)
    rw [Pi.single_apply, ite_eq_right hjk, mul_zero, Pi.single_zero, add_zero, one_mul] at h1
    have h2 := congrFun h1 i
    simpa using h2.symm
  set φ : Fin d → K → K := fun k a => f (Pi.single k a) k with hφ
  have hf1 : ∀ k a, f (Pi.single k a) = Pi.single k (φ k a) := by
    intro k a
    ext j
    by_cases hj : j = k
    · subst hj
      simp [hφ]
    · rw [hline k a j hj, Pi.single_apply, ite_eq_right hj]
  have hrel : ∀ i k : Fin d, i ≠ k → ∀ c a : K, φ i (c * a) = c * φ k a := by
    intro i k hik c a
    have h1 := ht i k hik c (Pi.single k a)
    simp only [Pi.single_eq_same, map_add, hf1] at h1
    have h2 := congrFun h1 i
    simpa [Pi.single_apply, hik] using h2
  set i₀ : Fin d := ⟨0, by omega⟩
  set D := φ i₀ 1 with hD
  have hall : ∀ k : Fin d, φ k 1 = D := by
    intro k
    by_cases hk : k = i₀
    · rw [hk]
    · have := hrel k i₀ hk 1 1
      rwa [one_mul, one_mul] at this
  have hφD : ∀ k : Fin d, ∀ c : K, φ k c = c * D := by
    intro k c
    obtain ⟨i, hik⟩ := hne k
    have := hrel k i (Ne.symm hik) c 1
    rw [mul_one, hall i] at this
    exact this
  refine ⟨D, fun v => ?_⟩
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  simp_rw [hf1, hφD]
  ext j
  simp [Finset.sum_apply, Pi.single_apply, mul_comm]

theorem eq_bot_or_eq_top_of_transvection_inv {d : ℕ} (hd : 2 ≤ d)
    (U : AddSubgroup (Fin d → K))
    (hU : ∀ i j : Fin d, i ≠ j → ∀ c : K, ∀ u ∈ U, Matrix.transvection i j c *ᵥ u ∈ U) :
    U = ⊥ ∨ U = ⊤ := by
  by_cases h : U = ⊥
  · exact Or.inl h
  right
  obtain ⟨⟨v, hv⟩, hv0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).mp h
  have hv0' : v ≠ 0 := fun h' => hv0 (Subtype.ext h')
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv0' (funext hcon)
  have hne : ∀ k : Fin d, ∃ i : Fin d, i ≠ k := by
    intro k
    by_cases h : k = ⟨0, by omega⟩
    · exact ⟨⟨1, by omega⟩, by rw [h]; simp [Fin.ext_iff]⟩
    · exact ⟨⟨0, by omega⟩, Ne.symm h⟩
  have hsub : ∀ i j : Fin d, i ≠ j → ∀ c : K, ∀ u ∈ U, Pi.single i (c * u j) ∈ U := by
    intro i j hij c u hu
    have h1 := U.sub_mem (hU i j hij c u hu) hu
    rwa [transvection_mulVec, add_sub_cancel_left] at h1
  have h1 : ∀ i : Fin d, i ≠ j → ∀ c : K, Pi.single i c ∈ U := by
    intro i hij c
    have := hsub i j hij (c / v j) v hv
    rwa [div_mul_cancel₀ c hj] at this
  have h2 : ∀ k : Fin d, ∀ c : K, Pi.single k c ∈ U := by
    intro k c
    by_cases hk : k = j
    · subst hk
      obtain ⟨i, hik⟩ := hne k
      have := hsub k i (Ne.symm hik) c (Pi.single i 1) (h1 i hik 1)
      simpa using this
    · exact h1 k hk c
  rw [eq_top_iff]
  intro w _
  rw [← Finset.univ_sum_single w]
  exact AddSubgroup.sum_mem _ fun k _ => h2 k (w k)

section GL3

variable {F : Type} [Field F]

theorem finrank_range_le_one_of_sq_eq_zero {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hV : Module.finrank F V = 3) {N : V →ₗ[F] V} (hN : N ∘ₗ N = 0) :
    Module.finrank F (LinearMap.range N) ≤ 1 := by
  have h1 := LinearMap.finrank_range_add_finrank_ker N
  have h2 : LinearMap.range N ≤ LinearMap.ker N := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker]
    exact LinearMap.congr_fun hN v
  have h3 := Submodule.finrank_mono h2
  omega

theorem comp_eq_zero_of_sq_eq_zero {V : Type*} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (hV : Module.finrank F V = 3) {M N : V →ₗ[F] V}
    (hM : M ∘ₗ M = 0) (hN : N ∘ₗ N = 0) (hMN : M ∘ₗ N = N ∘ₗ M) : M ∘ₗ N = 0 := by
  have hr := finrank_range_le_one_of_sq_eq_zero hV hN
  ext v
  have hmem : N v ∈ LinearMap.range N := ⟨v, rfl⟩
  have hMmem : M (N v) ∈ LinearMap.range N := by
    have : M (N v) = N (M v) := LinearMap.congr_fun hMN v
    rw [this]
    exact ⟨M v, rfl⟩
  by_cases hNv : N v = 0
  · simp [hNv]
  · have hline : ∃ c : F, M (N v) = c • N v := by
      have hspan : LinearMap.range N = Submodule.span F {N v} := by
        apply (Submodule.eq_of_le_of_finrank_le (Submodule.span_le.mpr (by simp [hmem]))
          ?_).symm
        rw [finrank_span_singleton hNv]
        exact hr
      rw [hspan] at hMmem
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hMmem
      exact ⟨c, hc.symm⟩
    obtain ⟨c, hc⟩ := hline
    have h2 : M (M (N v)) = c ^ 2 • N v := by
      rw [hc, map_smul, hc, smul_smul, sq]
    have h3 : M (M (N v)) = 0 := LinearMap.congr_fun hM (N v)
    rw [h3] at h2
    have hc0 : c ^ 2 = 0 := by
      by_contra hc0
      exact hNv (by
        have := h2.symm
        rwa [smul_eq_zero, or_iff_right hc0] at this)
    have : c = 0 := pow_eq_zero_iff (by norm_num) |>.mp hc0
    simp [hc, this]

@[expose] noncomputable def nOf (A : GL (Fin 3) F) : (Fin 3 → F) →ₗ[F] (Fin 3 → F) :=
  Matrix.toLin' ((A : Matrix (Fin 3) (Fin 3) F) - 1)

theorem matrix_add_self [CharP F 2] (X : Matrix (Fin 3) (Fin 3) F) : X + X = 0 := by
  ext i j
  rw [Matrix.add_apply, CharTwo.add_self_eq_zero, Matrix.zero_apply]

theorem nOf_sq [CharP F 2] {A : GL (Fin 3) F} (hA : A * A = 1) : nOf A ∘ₗ nOf A = 0 := by
  have hA' : (A : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul, hA, Units.val_one]
  have h1 : ((A : Matrix (Fin 3) (Fin 3) F) - 1) * ((A : Matrix (Fin 3) (Fin 3) F) - 1) = 0 := by
    calc ((A : Matrix (Fin 3) (Fin 3) F) - 1) * ((A : Matrix (Fin 3) (Fin 3) F) - 1)
        = ((A : Matrix (Fin 3) (Fin 3) F) * A + 1) - (A + A) := by noncomm_ring
      _ = (1 + 1) - 0 := by rw [hA', matrix_add_self (A : Matrix (Fin 3) (Fin 3) F)]
      _ = 0 := by rw [matrix_add_self, sub_zero]
  unfold nOf
  rw [← Matrix.toLin'_mul, h1, map_zero]

theorem nOf_comm {A B : GL (Fin 3) F} (h : A * B = B * A) :
    nOf A ∘ₗ nOf B = nOf B ∘ₗ nOf A := by
  unfold nOf
  rw [← Matrix.toLin'_mul, ← Matrix.toLin'_mul]
  congr 1
  have h' : (A : Matrix (Fin 3) (Fin 3) F) * B = B * A := by
    rw [← Units.val_mul, h, Units.val_mul]
  simp only [sub_mul, mul_sub, one_mul, mul_one, h']
  abel

@[expose] noncomputable def fixSp (E : Subgroup (GL (Fin 3) F)) : Submodule F (Fin 3 → F) :=
  ⨅ A : E, LinearMap.ker (nOf (A : GL (Fin 3) F))

@[expose] noncomputable def commSp (E : Subgroup (GL (Fin 3) F)) : Submodule F (Fin 3 → F) :=
  ⨆ A : E, LinearMap.range (nOf (A : GL (Fin 3) F))

theorem card_le_of_elemAbelian_GL3' [CharP F 2] [Finite F] (E : Subgroup (GL (Fin 3) F))
    (hsq : ∀ A ∈ E, A * A = 1) (hcomm : ∀ A ∈ E, ∀ B ∈ E, A * B = B * A) :
    commSp E ≤ fixSp E ∧ Nat.card E ≤
      Nat.card F ^ ((3 - Module.finrank F (fixSp E)) * Module.finrank F (commSp E)) := by
  classical
  have hV : Module.finrank F (Fin 3 → F) = 3 := Module.finrank_fin_fun F
  have hNN : ∀ A ∈ E, ∀ B ∈ E, nOf A ∘ₗ nOf B = 0 := fun A hA B hB =>
    comp_eq_zero_of_sq_eq_zero hV (nOf_sq (hsq A hA)) (nOf_sq (hsq B hB))
      (nOf_comm (hcomm A hA B hB))
  set C := fixSp E with hC
  set R := commSp E with hR
  have hRC : R ≤ C := by
    rw [hR, commSp, iSup_le_iff]
    rintro A _ ⟨v, rfl⟩
    simp only [hC, fixSp, Submodule.mem_iInf, LinearMap.mem_ker]
    intro B
    exact LinearMap.congr_fun (hNN B B.2 A A.2) v
  refine ⟨hRC, ?_⟩
  have hrange : ∀ A : E, ∀ v, nOf (A : GL (Fin 3) F) v ∈ R := fun A v =>
    (le_iSup (fun A : E => LinearMap.range (nOf (A : GL (Fin 3) F))) A) ⟨v, rfl⟩
  obtain ⟨D, hCD⟩ := Submodule.exists_isCompl C
  let Φ : E → (D →ₗ[F] R) := fun A =>
    ((nOf (A : GL (Fin 3) F)).domRestrict D).codRestrict R (fun d => hrange A d)
  have hΦ : Function.Injective Φ := by
    intro A B hAB
    have hN : nOf (A : GL (Fin 3) F) = nOf (B : GL (Fin 3) F) := by
      apply LinearMap.ext
      intro v
      have hv : v ∈ C ⊔ D := by rw [hCD.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨c, hc, d, hd, rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add, map_add]
      have hcA : nOf (A : GL (Fin 3) F) c = 0 := (Submodule.mem_iInf _).mp hc A
      have hcB : nOf (B : GL (Fin 3) F) c = 0 := (Submodule.mem_iInf _).mp hc B
      rw [hcA, hcB]
      have := congrArg (fun φ : D →ₗ[F] R => ((φ ⟨d, hd⟩ : R) : Fin 3 → F)) hAB
      exact congrArg (0 + ·) this
    apply Subtype.ext
    apply Units.ext
    have := congrArg LinearMap.toMatrix' hN
    simp only [nOf, LinearMap.toMatrix'_toLin'] at this
    exact sub_left_injective this
  have : Finite (D →ₗ[F] R) := Module.finite_of_finite F
  have hcard := Nat.card_le_card_of_injective Φ hΦ
  have hdim : Module.finrank F C + Module.finrank F D = 3 := by
    have := Submodule.finrank_add_eq_of_isCompl hCD
    rw [hV] at this
    exact this
  have hHom : Nat.card (D →ₗ[F] R) =
      Nat.card F ^ (Module.finrank F D * Module.finrank F R) := by
    rw [Module.natCard_eq_pow_finrank (K := F), Module.finrank_linearMap]
  rw [hHom] at hcard
  have hD : Module.finrank F D = 3 - Module.finrank F C := by omega
  rwa [hD] at hcard

theorem card_le_of_elemAbelian_GL3 [CharP F 2] [Finite F] (E : Subgroup (GL (Fin 3) F))
    (hsq : ∀ A ∈ E, A * A = 1) (hcomm : ∀ A ∈ E, ∀ B ∈ E, A * B = B * A) :
    Nat.card E ≤ Nat.card F ^ 2 := by
  obtain ⟨hRC, hcard⟩ := card_le_of_elemAbelian_GL3' E hsq hcomm
  refine hcard.trans (Nat.pow_le_pow_right Nat.card_pos ?_)
  have h1 := Submodule.finrank_mono hRC
  have h2 : Module.finrank F (fixSp E) ≤ 3 := by
    have := Submodule.finrank_le (fixSp E)
    rwa [Module.finrank_fin_fun] at this
  generalize Module.finrank F (fixSp E) = c at h1 h2
  generalize Module.finrank F (commSp E) = r at h1
  interval_cases c <;> interval_cases r <;> omega

end GL3

end H

end CFSG.Quasithin
