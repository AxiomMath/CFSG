module

public import CFSG.LocalAnalysis.StandardType.FS81.N6MainMat
public import CFSG.LocalAnalysis.StandardType.FS81.WtTwo

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

variable {k : ℕ}

theorem wt_smul_single {c : ZMod 3} (hc : c ≠ 0) (a : Fin k) : wt (c • Pi.single a 1) = 1 := by
  rw [wt_smul hc]
  unfold wt
  rw [Finset.card_eq_one]
  refine ⟨a, ?_⟩
  ext i
  by_cases hi : i = a
  · subst hi
    simp
  · simp [hi, Pi.single_eq_of_ne hi]

theorem wt_smul_single_sub_smul {a b : Fin k} (hab : a ≠ b) {c δ : ZMod 3} (hc : c ≠ 0)
    (hδ : δ ≠ 0) : wt (c • (Pi.single a 1 - δ • Pi.single b 1)) = 2 := by
  rw [wt_smul hc]
  have hδe : (δ • Pi.single b (1 : ZMod 3) : Fin k → ZMod 3) = Pi.single b δ := by
    rw [← Pi.single_smul]
    simp
  rw [hδe]
  exact wt_single_sub_single hab one_ne_zero hδ

theorem sign_mul_ne_zero {a b : ZMod 3} (ha : a = 1 ∨ a = -1) (hb : b ≠ 0) : a * b ≠ 0 := by
  revert a b
  decide

theorem wt_spMat_mulVec {σ : Equiv.Perm (Fin k)} {s : Fin k → ZMod 3} (hs : IsSign s)
    (v : Fin k → ZMod 3) : wt (spMat σ s *ᵥ v) = wt v := by
  rw [spMat_mulVec]
  unfold wt
  refine Finset.card_bij (fun i _ => σ.symm i) (fun i hi => ?_)
    (fun i _ j _ h => σ.symm.injective h) (fun j hj => ⟨σ j, ?_, by simp⟩)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact fun h0 => hi (by rw [h0, mul_zero])
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.symm_apply_apply] at hj ⊢
    exact sign_mul_ne_zero (hs j) hj

theorem exists_spMat_mulVec_eq {v w : Fin k → ZMod 3} (h : wt v = wt w) :
    ∃ σ s, IsSign s ∧ spMat σ s *ᵥ v = w := by
  classical
  let S : Finset (Fin k) := Finset.univ.filter fun i => v i ≠ 0
  let T : Finset (Fin k) := Finset.univ.filter fun i => w i ≠ 0
  have hScard : S.card = wt v := rfl
  have hTcard : T.card = wt w := rfl
  have hcard : S.card = T.card := by rw [hScard, hTcard, h]
  let e : {x : Fin k // x ∈ S} ≃ {x : Fin k // x ∈ T} :=
    Fintype.equivOfCardEq (by rw [Fintype.card_coe S, Fintype.card_coe T, hcard])
  let σ : Equiv.Perm (Fin k) := e.extendSubtype
  have hσS : ∀ x, x ∈ S → σ x ∈ T := by
    intro x hx
    simpa [σ] using Equiv.extendSubtype_mem e x hx
  have hσnot : ∀ x, x ∉ S → σ x ∉ T := by
    intro x hx
    simpa [σ] using Equiv.extendSubtype_not_mem e x hx
  let s : Fin k → ZMod 3 := fun j => if v j = 0 then 1 else w (σ j) * v j
  have hs : IsSign s := by
    intro j
    by_cases h0 : v j = 0
    · exact Or.inl (by simp [s, h0])
    · have hmem : j ∈ S := by simp [S, h0]
      have hwj : w (σ j) ≠ 0 := by
        have := hσS j hmem
        simpa [T] using this
      exact eq_one_or_of_ne_zero (by simpa [s, h0] using mul_ne_zero hwj h0)
  refine ⟨σ, s, hs, ?_⟩
  rw [spMat_mulVec]
  funext i
  set j : Fin k := σ.symm i with hj
  have hσj : σ j = i := by rw [hj, Equiv.apply_symm_apply]
  change (if v j = 0 then (1 : ZMod 3) else w (σ j) * v j) * v j = w i
  by_cases h0 : v j = 0
  · have hnotS : j ∉ S := by simp [S, h0]
    have hwj : w (σ j) = 0 := by
      by_contra hne
      exact hσnot j hnotS (by simpa [T] using hne)
    rw [if_pos h0, h0, mul_zero, ← hσj, hwj]
  · have hmem : j ∈ S := by simp [S, h0]
    have hwj : w (σ j) ≠ 0 := by
      have := hσS j hmem
      simpa [T] using this
    rw [if_neg h0, hσj, mul_assoc, mul_self_of_ne_zero h0, mul_one]

theorem exists_spMat_mulVec_eq_fix {v w : Fin k → ZMod 3} (h : wt v = wt w) {p : Fin k}
    (hv : v p = 0) (hw : w p = 0) : ∃ σ s, IsSign s ∧ σ p = p ∧ spMat σ s *ᵥ v = w := by
  obtain ⟨σ, s, hs, hsw⟩ := exists_spMat_mulVec_eq h
  let q : Fin k := σ p
  have hwq : w q = 0 := by
    have hq := congrFun hsw q
    rw [spMat_mulVec] at hq
    change s (σ.symm q) * v (σ.symm q) = w q at hq
    have hsym : σ.symm q = p := by
      rw [show q = σ p from rfl, Equiv.symm_apply_apply]
    rw [hsym, hv, mul_zero] at hq
    exact hq.symm
  let τ : Equiv.Perm (Fin k) := Equiv.swap q p
  have hτsymm : τ.symm = τ := by
    simp [τ, Equiv.swap_inv]
  have hτw : ∀ i, w (τ i) = w i := by
    intro i
    rw [Equiv.swap_apply_def]
    by_cases hiq : i = q
    · subst hiq
      rw [if_pos rfl, hwq, hw]
    · rw [if_neg hiq]
      by_cases hip : i = p
      · subst hip
        rw [if_pos rfl, hwq, hw]
      · rw [if_neg hip]
  have hτmul : spMat τ (fun _ => (1 : ZMod 3)) *ᵥ w = w := by
    rw [spMat_mulVec, hτsymm]
    funext i
    simpa using hτw i
  refine ⟨τ * σ, s, hs, ?_, ?_⟩
  · show τ (σ p) = p
    rw [show σ p = q from rfl, Equiv.swap_apply_left]
  · have hsp : spMat (τ * σ) s = spMat τ (fun _ => (1 : ZMod 3)) * spMat σ s := by
      rw [spMat_mul]
      congr 1
      funext j
      simp
    rw [hsp, ← Matrix.mulVec_mulVec, hsw, hτmul]

theorem mem_spSet_of_wt_col {A : GL (Fin k) (ZMod 3)}
    (h : ∀ m : Fin k, wt ((A : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ Pi.single m 1) = 1) :
    (A : Matrix (Fin k) (Fin k) (ZMod 3)) ∈ spSet fun _ _ => True := by
  classical
  have hcol : ∀ m : Fin k, wt (fun i => (A : Matrix (Fin k) (Fin k) (ZMod 3)) i m) = 1 := by
    intro m
    simpa [Matrix.mulVec_single_one, Matrix.col_apply'] using h m
  have hex : ∀ m : Fin k,
      ∃! i : Fin k, (A : Matrix (Fin k) (Fin k) (ZMod 3)) i m ≠ 0 := by
    intro m
    have hm := hcol m
    unfold wt at hm
    rw [Finset.card_eq_one] at hm
    obtain ⟨i, hi⟩ := hm
    refine ⟨i, ?_, ?_⟩
    · have hmem : i ∈ Finset.univ.filter
          (fun i : Fin k => (A : Matrix (Fin k) (Fin k) (ZMod 3)) i m ≠ 0) := by
        rw [hi]
        simp
      simpa using hmem
    · intro j hj
      have hmem : j ∈ Finset.univ.filter
          (fun i : Fin k => (A : Matrix (Fin k) (Fin k) (ZMod 3)) i m ≠ 0) := by
        simp [hj]
      rw [hi] at hmem
      simpa using hmem
  let τ : Fin k → Fin k := fun m => (hex m).choose
  have hτ : ∀ m : Fin k, (A : Matrix (Fin k) (Fin k) (ZMod 3)) (τ m) m ≠ 0 :=
    fun m => ((hex m).choose_spec).1
  have huniq : ∀ (m i : Fin k),
      (A : Matrix (Fin k) (Fin k) (ZMod 3)) i m ≠ 0 → i = τ m :=
    fun m i hi => ((hex m).choose_spec).2 i hi
  have hzero : ∀ (m i : Fin k), i ≠ τ m →
      (A : Matrix (Fin k) (Fin k) (ZMod 3)) i m = 0 := by
    intro m i hi
    by_contra hne
    exact hi (huniq m i hne)
  have hτ_inj : Function.Injective τ := by
    intro m m' hmm'
    by_contra hne
    let t : Fin k := τ m
    let c : Fin k → ZMod 3 := fun m => (A : Matrix (Fin k) (Fin k) (ZMod 3)) (τ m) m
    let z : Fin k → ZMod 3 := c m' • Pi.single m 1 - c m • Pi.single m' 1
    have hz_ne : z ≠ 0 := by
      intro hz0
      have hm := congrFun hz0 m
      have hcm' : c m' = 0 := by
        change (A : Matrix (Fin k) (Fin k) (ZMod 3)) (τ m') m' = 0
        have h := hm
        simp [z, c, hne, Pi.single_eq_of_ne hne] at h
        exact sub_eq_zero.mp h
      exact hτ m' hcm'
    have hAz : (A : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ z = 0 := by
      change (A : Matrix (Fin k) (Fin k) (ZMod 3)) *ᵥ
        (c m' • Pi.single m 1 - c m • Pi.single m' 1) = 0
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul,
        Matrix.mulVec_single_one, Matrix.mulVec_single_one]
      funext i
      by_cases hit : i = t
      · subst hit
        have h1 : (A : Matrix (Fin k) (Fin k) (ZMod 3)) (τ m) m = c m := rfl
        have h2 : (A : Matrix (Fin k) (Fin k) (ZMod 3)) (τ m) m' = c m' := by
          rw [hmm']
        simp only [Pi.sub_apply, Pi.smul_apply, Matrix.col_apply, smul_eq_mul]
        change c m' * (A : Matrix (Fin k) (Fin k) (ZMod 3)) (τ m) m -
          c m * (A : Matrix (Fin k) (Fin k) (ZMod 3)) (τ m) m' = 0
        rw [h1, h2]
        ring
      · have h1 : (A : Matrix (Fin k) (Fin k) (ZMod 3)) i m = 0 := hzero m i hit
        have h2 : (A : Matrix (Fin k) (Fin k) (ZMod 3)) i m' = 0 := by
          apply hzero m' i
          rw [← hmm']
          exact hit
        simp [h1, h2]
    exact (gl_mulVec_ne_zero A hz_ne) hAz
  let σ : Equiv.Perm (Fin k) :=
    Equiv.ofBijective τ (Finite.injective_iff_bijective.mp hτ_inj)
  let c : Fin k → ZMod 3 := fun m => (A : Matrix (Fin k) (Fin k) (ZMod 3)) (τ m) m
  have hc : IsSign c := fun m => eq_one_or_of_ne_zero (hτ m)
  refine ⟨σ, c, hc, trivial, ?_⟩
  ext i j
  rw [spMat_apply]
  have hσj : σ j = τ j := Equiv.ofBijective_apply τ _ j
  by_cases hij : i = σ j
  · rw [if_pos hij, hij, hσj]
  · rw [if_neg hij]
    apply hzero j i
    rw [← hσj]
    exact hij

end CFSG.StandardType.FrameRoute.FS81
