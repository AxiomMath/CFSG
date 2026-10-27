module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2FinL4Two14Inner

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.WeakClosure81

open Module Matrix CFSG.LargeExtraspecial.SL4Mod CFSG.LargeExtraspecial.SL4Mod.Native
  CFSG.Sporadic.SmallF2.Native CFSG.LieType.SpecialLinear

@[expose] def l4UWord : Array (List ℕ) :=
  #[
    [], [0], [3, 1, 3], [1, 0, 1], [3, 4, 2, 4, 3], [5, 1, 0, 1, 5], [3, 2, 1, 3, 2],
    [2, 1, 0, 1, 2], [1], [1, 0], [0, 1, 0], [0, 1], [3, 4, 2, 4, 3, 1], [2, 1, 0, 1, 2, 1],
    [3, 2, 1, 3, 2, 1], [5, 1, 0, 1, 5, 1], [4, 2, 4], [4, 2, 4, 0], [4, 2, 0, 4],
    [4, 2, 0, 4, 0], [0, 4, 2, 4, 0], [0, 4, 2, 4], [1, 2, 0, 1, 2, 0], [1, 2, 0, 1, 2],
    [2, 1, 2], [2, 1, 2, 0], [4, 2, 0, 4, 1], [4, 2, 4, 0, 1], [1, 0, 4, 2, 4, 0],
    [1, 0, 4, 2, 4], [2, 0, 1, 2, 0], [2, 0, 1, 2], [2], [2, 0], [3, 2, 1, 3], [2, 1, 0, 1],
    [3, 1, 2, 1, 3], [3, 1, 2, 1, 3, 0], [3, 1, 3, 2], [1, 0, 1, 2], [2, 1], [2, 1, 0],
    [2, 0, 1, 0], [2, 0, 1], [1, 0, 1, 2, 1, 0], [1, 0, 1, 2, 1], [3, 1, 3, 2, 1],
    [3, 1, 3, 2, 1, 0], [1, 2, 1], [1, 2, 1, 0], [1, 2, 0, 1, 0], [1, 2, 0, 1], [0, 1, 2, 1, 0],
    [0, 1, 2, 1], [0, 1, 2, 0, 1], [0, 1, 2, 0, 1, 0], [1, 2], [1, 2, 0], [1, 3, 2, 1, 3],
    [1, 2, 1, 0, 1], [0, 1, 2, 1, 0, 1], [0, 1, 3, 2, 1, 3], [0, 1, 2, 0], [0, 1, 2]]

@[expose] def l4T14 : Array ℕ := #[1, 4, 2, 32, 16, 8, 256, 128, 64, 872, 4096, 2048, 1024, 8192]

@[expose] def l4OuterX14 : Array (Array ℕ) :=
  #[
    #[2, 8, 64, 1024], #[2, 6, 8, 18], #[2, 8, 40, 64], #[2, 6, 8, 18], #[2, 8, 64, 584],
    #[2, 6, 8, 18], #[2, 8, 40, 64], #[2, 6, 8, 18], #[2, 10, 64, 128], #[2, 6, 10, 18],
    #[2, 10, 42, 64], #[2, 6, 10, 18], #[2, 10, 64, 128], #[2, 6, 10, 18], #[2, 10, 42, 64],
    #[2, 6, 10, 18], #[2, 8, 40, 64], #[2, 6, 14, 18], #[2, 8, 64, 1026], #[2, 6, 14, 18],
    #[2, 8, 40, 64], #[2, 6, 14, 18], #[2, 8, 64, 586], #[2, 6, 14, 18], #[2, 10, 42, 64],
    #[2, 6, 12, 18], #[2, 10, 64, 136], #[2, 6, 12, 18], #[2, 10, 42, 64], #[2, 6, 12, 18],
    #[2, 10, 64, 136], #[2, 6, 12, 18], #[2, 6, 8, 16], #[2, 8, 72, 1024], #[2, 6, 8, 16],
    #[2, 8, 40, 74], #[2, 6, 8, 16], #[2, 8, 72, 330], #[2, 6, 8, 16], #[2, 8, 40, 98],
    #[2, 6, 10, 16], #[2, 10, 72, 128], #[2, 6, 10, 16], #[2, 10, 42, 74], #[2, 6, 10, 16],
    #[2, 10, 72, 128], #[2, 6, 10, 16], #[2, 10, 42, 96], #[2, 6, 14, 16], #[2, 8, 40, 72],
    #[2, 6, 14, 16], #[2, 8, 74, 1088], #[2, 6, 14, 16], #[2, 8, 40, 96], #[2, 6, 14, 16],
    #[2, 8, 74, 328], #[2, 6, 12, 16], #[2, 10, 42, 72], #[2, 6, 12, 16], #[2, 10, 74, 136],
    #[2, 6, 12, 16], #[2, 10, 42, 98], #[2, 6, 12, 16], #[2, 10, 74, 136]]

@[expose] def l4OuterP14 : Array (Array ℕ) :=
  #[
    #[2, 5, 8, 12], #[2, 0, 5, 1], #[2, 5, 0, 8], #[2, 0, 5, 1], #[2, 5, 8, 0], #[2, 0, 5, 1],
    #[2, 5, 0, 8], #[2, 0, 5, 1], #[2, 5, 8, 11], #[2, 0, 5, 1], #[2, 5, 0, 8], #[2, 0, 5, 1],
    #[2, 5, 8, 11], #[2, 0, 5, 1], #[2, 5, 0, 8], #[2, 0, 5, 1], #[2, 5, 0, 8], #[2, 0, 5, 1],
    #[2, 5, 8, 12], #[2, 0, 5, 1], #[2, 5, 0, 8], #[2, 0, 5, 1], #[2, 5, 8, 0], #[2, 0, 5, 1],
    #[2, 5, 0, 8], #[2, 0, 5, 1], #[2, 5, 8, 11], #[2, 0, 5, 1], #[2, 5, 0, 8], #[2, 0, 5, 1],
    #[2, 5, 8, 11], #[2, 0, 5, 1], #[2, 0, 5, 1], #[2, 5, 9, 12], #[2, 0, 5, 1], #[2, 5, 0, 9],
    #[2, 0, 5, 1], #[2, 5, 9, 0], #[2, 0, 5, 1], #[2, 5, 0, 9], #[2, 0, 5, 1], #[2, 5, 9, 11],
    #[2, 0, 5, 1], #[2, 5, 0, 9], #[2, 0, 5, 1], #[2, 5, 9, 11], #[2, 0, 5, 1], #[2, 5, 0, 9],
    #[2, 0, 5, 1], #[2, 5, 0, 9], #[2, 0, 5, 1], #[2, 5, 9, 12], #[2, 0, 5, 1], #[2, 5, 0, 9],
    #[2, 0, 5, 1], #[2, 5, 9, 0], #[2, 0, 5, 1], #[2, 5, 0, 9], #[2, 0, 5, 1], #[2, 5, 9, 11],
    #[2, 0, 5, 1], #[2, 5, 0, 9], #[2, 0, 5, 1], #[2, 5, 9, 11]]


theorem wordCode_l4UWord : ∀ k < 64, wordCode (l4UWord[k]!) = uCode k := by decide +kernel

theorem lt_six_of_mem_l4UWord : ∀ k < 64, ∀ s ∈ l4UWord[k]!, s < 6 := by decide +kernel

theorem uSL_eq_wordProd_l4UWord {k : ℕ} (hk : k < 64) : uSL k = wordProd (l4UWord[k]!) :=
  (hasCode_uSL k).eq (hasCode_wordProd _) (wordCode_l4UWord k hk).symm

theorem colMul_l4T14_self : colMul 14 l4T14 l4T14 = idRows 14 := by decide +kernel

theorem colMul_l4T14_gen :
    ∀ s < 6, colMul 14 l4T14 (pkGen14 s) = colMul 14 (pkGen14 (graphIdx s)) l4T14 := by
  decide +kernel

theorem pivChk_outer_fourteen : ∀ k < 64,
    pivChk 14 4 (colSubOne 14 (colMul 14 (colWord 14 pkGen14 (l4UWord[k]!)) l4T14))
      (l4OuterX14[k]!) (l4OuterP14[k]!) = true := by decide +kernel


theorem outerRankFour_fourteen : OuterRankFour 14 := by
  intro V _ _ _ hV ρ hirr B hB τ d hdd hdy
  haveI : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hV]; norm_num)
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  obtain ⟨e, he⟩ := classify_fourteen hV hirr
  obtain ⟨k, hk, hkB⟩ := exists_uSL_of_isUpperGL hB
  have hM : ∀ s < 6, ∀ v, e (ρ (genN s) v) = l4Gen14 s *ᵥ e v := fun s hs v => by
    rw [l4Gen14_eq hs]
    exact he ⟨s, hs⟩ v
  let Tm : Matrix (Fin 14) (Fin 14) (ZMod 2) := refMat 14 l4T14
  have hTT : Tm * Tm = 1 := by
    have h := congrArg (refMat 14) colMul_l4T14_self
    rwa [refMat_colMul, refMat_idRows] at h
  have hTgen : ∀ s < 6, Tm * l4Gen14 s = l4Gen14 (graphIdx s) * Tm := by
    intro s hs
    have h := congrArg (refMat 14) (colMul_l4T14_gen s hs)
    rwa [refMat_colMul, refMat_colMul] at h
  let TV0 : V →ₗ[ZMod 2] V := (e.symm : (Fin 14 → ZMod 2) →ₗ[ZMod 2] V) ∘ₗ Tm.mulVecLin ∘ₗ
    (e : V →ₗ[ZMod 2] (Fin 14 → ZMod 2))
  have hTV0 : ∀ v, e (TV0 v) = Tm *ᵥ e v := fun v => by simp [TV0]
  have hinvol : Function.Involutive TV0 := by
    intro v
    apply e.injective
    rw [hTV0, hTV0, Matrix.mulVec_mulVec, hTT, Matrix.one_mulVec]
  let TV : V ≃ₗ[ZMod 2] V := LinearEquiv.ofInvolutive TV0 hinvol
  have hTV : ∀ v, e (TV v) = Tm *ᵥ e v := hTV0
  have hgen : ∀ s < 6, ∀ v, TV (ρ (genN s) v) = ρ (borelGraph 4 (ZMod 2) (genN s)) (TV v) := by
    intro s hs v
    apply e.injective
    rw [borelGraph_genN hs]
    have h1 : e (TV (ρ (genN s) v)) = (Tm * l4Gen14 s) *ᵥ e v := by
      rw [hTV, hM s hs, Matrix.mulVec_mulVec]
    have h2 : e (ρ (genN (graphIdx s)) (TV v)) = (l4Gen14 (graphIdx s) * Tm) *ᵥ e v := by
      rw [hM _ (graphIdx_lt hs), hTV, Matrix.mulVec_mulVec]
    rw [h1, h2, hTgen s hs]
  have hTall := intertwine_of_gen ρ (borelGraph 4 (ZMod 2)) TV hgen
  let S : V ≃ₗ[ZMod 2] V := TV.trans (ρ (uSL k))
  have hSapp : ∀ v, S v = ρ (uSL k) (TV v) := fun v => rfl
  have hS : ∀ (y : SL4) (v : V), S (ρ y v) = ρ (borelStd 4 (ZMod 2) B τ 1 y) (S v) := by
    intro y v
    rw [borelStd_eq_conj hkB τ y, hSapp, hSapp, hTall, ← act_mul, ← act_mul, inv_mul_cancel_right]
  have hcomm : ∀ (y : SL4) (u : V), S.symm (ρ (borelStd 4 (ZMod 2) B τ 1 y) u) =
      ρ y (S.symm u) := by
    intro y u
    apply S.injective
    rw [LinearEquiv.apply_symm_apply, hS, LinearEquiv.apply_symm_apply]
  let Φ : V →ₗ[ZMod 2] V := (S.symm : V →ₗ[ZMod 2] V) ∘ₗ (d : V →ₗ[ZMod 2] V)
  have hΦ : ∀ s : Fin 6, ∀ v, Φ (ρ (genN s.val) v) = ρ (genN s.val) (Φ v) := by
    intro s v
    show S.symm (d (ρ (genN s.val) v)) = ρ (genN s.val) (S.symm (d v))
    rw [hdy, hcomm]
  rcases commutant_eq_zero_or_one hirr Φ hΦ with h0 | h1
  · exfalso
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h : S.symm (d v) = 0 := LinearMap.congr_fun h0 v
    have hdv : d v = 0 := by simpa using h
    exact hv (d.injective (by rw [hdv, map_zero]))
  · have hdS : ∀ v, d v = S v := fun v => by
      have h : S.symm (d v) = v := LinearMap.congr_fun h1 v
      exact S.symm_apply_eq.mp h
    have hbword : uSL k = wordProd (l4UWord[k]!) := uSL_eq_wordProd_l4UWord hk
    have hrel : ∀ v, e (d v) = (((l4UWord[k]!).map l4Gen14).prod * Tm) *ᵥ e v := by
      intro v
      rw [hdS, hSapp, hbword, equiv_act_wordProd ρ e l4Gen14 hM _
        (lt_six_of_mem_l4UWord k hk), hTV, Matrix.mulVec_mulVec]
    rw [finrank_range_sub_one_eq e d _ hrel]
    have hp := le_finrank_range_of_pivChk (pivChk_outer_fourteen k hk)
    rw [refMat_colSubOne, refMat_colMul, refMat_colWord] at hp
    exact hp

end CFSG.LocalAnalysis.WeakClosure81
