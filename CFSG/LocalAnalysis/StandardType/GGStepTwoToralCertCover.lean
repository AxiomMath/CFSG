module

public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertEnc
public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertWeyl
public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertRoots
public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertAlcove
public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralCertLin

public section

namespace CFSG.StandardType.StepTwoToralCert

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.CrossChar

variable {τ : Tag} {p n : ℕ}

theorem tcEnt_map_mod (a : Array ℤ) (i : ℕ) :
    tcEnt (a.map (· % (p : ℤ))) i = tcEnt a i % (p : ℤ) := by
  simp only [tcEnt, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases a[i]? <;> simp

theorem tcVec_map_mod (a : Array ℤ) : tcVec p n (a.map (· % (p : ℤ))) = tcVec p n a := by
  funext i
  simp only [tcVec, tcEnt_map_mod, ZMod.intCast_mod]

theorem tcCombo_mem (basis : List (Array ℤ)) (t : ℕ) :
    tcVec p n (tcCombo p n basis t) ∈
      Submodule.span (ZMod p) {f | ∃ g ∈ basis, f = tcVec p n g} := by
  rw [tcCombo, tcVec_map_mod]
  exact tcVec_tcLinComb_mem _ _

theorem tcCombo_ne_zero {basis : List (Array ℤ)} {t : ℕ}
    (h : tcIsZero p n (tcCombo p n basis t) = false) : tcVec p n (tcCombo p n basis t) ≠ 0 := by
  intro h0
  have := tcIsZero_iff.mpr h0
  rw [h] at this
  exact Bool.false_ne_true this

section Rows


theorem tcFun_ofFn (g : Fin n → ℤ) (f : Fin n → ZMod p) :
    tcFun p n (Array.ofFn g) f = latChar p f g := by
  simp only [tcFun, latChar, tcEnt_ofFn]

theorem tcKerSub_roots_eq (O : List ℕ) :
    tcKerSub p τ.rank (O.map fun i => (tcRoots τ ()).getD i #[]) =
      annSub p (tcRootSet τ O) := by
  ext f
  simp only [mem_tcKerSub, List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  constructor
  · intro h α hα
    obtain ⟨j, hj, hjl, rfl⟩ := hα
    have := h j hj
    rwa [tcRoots_getD τ hjl, tcFun_ofFn] at this
  · intro h j hj
    by_cases hjl : j < τ.rootCertificate.roots.length
    · rw [tcRoots_getD τ hjl, tcFun_ofFn]
      exact h _ ⟨j, hj, hjl, rfl⟩
    · have : (tcRoots τ ()).getD j #[] = #[] := by
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none (by rw [tcRoots_size]; omega)]
        rfl
      rw [this]
      simp [tcFun, tcEnt]

theorem tcKerSub_rows_eq (L : List (Array ℤ)) (O : List ℕ) :
    tcKerSub p τ.rank (L ++ O.map fun i => (tcRoots τ ()).getD i #[]) =
      tcKerSub p τ.rank L ⊓ annSub p (tcRootSet τ O) := by
  rw [tcKerSub_append, tcKerSub_roots_eq]

end Rows

section CoverSound


theorem tcCoverOK_sound (hp : p.Prime) {L : List (Array ℤ)} {gens : Array (List ℕ)}
    {basis : List (Array ℤ)}
    (h : tcCoverOK (tcEnv τ p L gens) (tcAlcove τ p) basis = true)
    {d : Fin τ.rank → ZMod p} (hd : d ≠ 0) :
    ∃ s ∈ Submodule.span (ZMod p) {f | ∃ g ∈ basis, f = tcVec p τ.rank g}, s ≠ 0 ∧
      ∃ u : WeylGroup τ, cowAct u s = d := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨w, μ, hw, hμ⟩ :=
    (kacOf τ).exists_normal p hp.pos (fun i => (((d i).val : ℕ) : ℤ))
  have h1 : cowAct w⁻¹ (modP p μ) = d := by
    funext i
    have h2 := hw (Pi.single i 1)
    simp only [cowAct, inv_inv]
    have hc : latChar p (modP p μ) (w • Pi.single i 1) =
        (((w • (Pi.single i 1 : Fin τ.rank → ℤ)) ⬝ᵥ μ : ℤ) : ZMod p) := by
      simp [latChar, modP, dotProduct]
    rw [hc]
    have h3 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h2
    rw [Int.cast_sub, sub_eq_zero] at h3
    rw [h3]
    simp [single_dotProduct]
  have hμ0 : modP p μ ≠ 0 := by
    intro h0
    apply hd
    rw [← h1, h0]
    exact cowAct_zero _
  have hmem : Array.ofFn μ ∈ tcAlcove τ p := mem_tcAlcove hμ
  have hmz : tcIsZero p τ.rank (Array.ofFn μ) = false := by
    by_contra hcon
    have h4 : tcIsZero p τ.rank (Array.ofFn μ) = true := by simpa using hcon
    have h5 := tcIsZero_iff.mp h4
    rw [tcVec_ofFn] at h5
    exact hμ0 h5
  simp only [tcCoverOK, tcEnv, List.all_eq_true, List.any_eq_true, List.mem_filter,
    Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨t, -, hz, heq⟩ := h (Array.ofFn μ) ⟨hmem, hmz⟩
  have hs := tcEqMod_iff.mp heq
  rw [tcWord_cast, tcVec_ofFn] at hs
  refine ⟨tcVec p τ.rank (tcCombo p τ.rank basis t.1), tcCombo_mem basis t.1,
    tcCombo_ne_zero hz, w⁻¹ * tcWordElt τ t.2, ?_⟩
  rw [cowAct_mul, hs]
  exact h1

end CoverSound

end CFSG.StandardType.StepTwoToralCert
