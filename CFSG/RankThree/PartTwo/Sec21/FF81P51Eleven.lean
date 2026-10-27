module

public import CFSG.RankThree.PartTwo.Sec21.FF81P51Ten

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.P51

open Matrix

@[expose] def psiQ8 : V := ![1, 2, 2, 2]

@[expose] def rQ8 : Mat := 1 + vecMulVec (rep 6) psiQ8

@[expose] def hbarM : Mat := !![0, 0, 2, 1; 0, 1, 0, 0; 1, 0, 2, 2; 2, 0, 2, 2]

@[expose] def Swap23 : Mat := !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0]

@[expose] def rhoM : Mat := !![1, 2, 2, 2; 2, 0, 2, 2; 2, 2, 0, 2; 2, 2, 2, 0]

private theorem pat_bad : Pat mD ![1, 1, 1, 2] ∧ ¬ Pat mD ![2, 2, 2, 0] ∧ Pat mD (e 2 + e 3) ∧
    ¬ Pat mD ![2, 2, 0, 0] := by
  decide +kernel

private theorem mulVec_bad1 :
    (1 + vecMulVec (rep 6) ![1, 0, 0, 0] : Mat) *ᵥ ![1, 1, 1, 2] = ![2, 2, 2, 0] := by
  decide +kernel

private theorem mulVec_bad2 :
    (1 + vecMulVec (rep 6) ![1, 1, 1, 1] : Mat) *ᵥ (e 2 + e 3) = ![2, 2, 0, 0] := by
  decide +kernel

private theorem okL_six : okL 6 = [![1, 0, 0, 0], ![1, 1, 1, 1], ![1, 2, 2, 2]] := rfl

private theorem hbar_word :
    mm (mm (mm (mm (mm (mm (mm (mm Tau S1) rQ8) Tau) S1) rQ8) Tau) S1) Tau = hbarM := by
  decide +kernel

theorem hbar_sq : hbarM * hbarM = 1 := by decide +kernel

theorem hbar_T0 : hbarM * T0 * hbarM = Swap23 := by decide +kernel

theorem hbar_Cyc : hbarM * Cyc * hbarM = rhoM := by decide +kernel

theorem T0_rho : T0 * rhoM * T0 * rhoM = 1 := by decide +kernel

theorem swap23_cols : Swap23 *ᵥ e 0 = e 0 ∧ Swap23 *ᵥ e 1 = e 1 ∧ Swap23 *ᵥ e 2 = e 3 ∧
    Swap23 *ᵥ e 3 = e 2 := by
  decide +kernel

theorem refl_e23_cols : (1 + vecMulVec (e 2 + e 3) ![0, 0, 2, 2] : Mat) *ᵥ e 0 = e 0 ∧
    (1 + vecMulVec (e 2 + e 3) ![0, 0, 2, 2] : Mat) *ᵥ e 1 = e 1 ∧
    (1 + vecMulVec (e 2 + e 3) ![0, 0, 2, 2] : Mat) *ᵥ e 2 = -e 3 ∧
    (1 + vecMulVec (e 2 + e 3) ![0, 0, 2, 2] : Mat) *ᵥ e 3 = -e 2 := by
  decide +kernel

variable {Γ : Subgroup GL4}

theorem real_Q8 (h : Hyp Γ) (hD : (cfgOf Γ).1 = mD) : Real Γ (rep 6) psiQ8 := by
  have hm : rep 6 ∈ Om Γ := (cfgOf_fst h 6).1 (by rw [hD]; rfl)
  have hr := cfgOf_snd h 6 hm
  have hopt := cfgOf_opt h 6 (by decide)
  rw [(cfgOf_fst h 6).2 hm, optL, if_pos rfl, okL_six] at hopt
  have hOm := mem_Om_iff_pat h hD
  obtain ⟨r, hrΓ, hr1, -⟩ := real_refl h hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hopt
  rcases hopt with h1 | h1 | h1
  · have hv := (hOm _).2 pat_bad.1
    have := mulVec_mem_Om (coe_mem_GM hrΓ) hv
    rw [hr1, h1, mulVec_bad1] at this
    exact absurd ((hOm _).1 this) pat_bad.2.1
  · have hv := (hOm _).2 pat_bad.2.2.1
    have := mulVec_mem_Om (coe_mem_GM hrΓ) hv
    rw [hr1, h1, mulVec_bad2] at this
    exact absurd ((hOm _).1 this) pat_bad.2.2.2
  · rw [h1] at hr
    exact hr

theorem rQ8_mem (h : Hyp Γ) (hD : (cfgOf Γ).1 = mD) : rQ8 ∈ GM Γ := by
  obtain ⟨r, hrΓ, hr1, -⟩ := real_refl h (real_Q8 h hD)
  exact mem_GM.2 ⟨r, hrΓ, hr1⟩

theorem hbar_mem (h : Hyp Γ) (hD : (cfgOf Γ).1 = mD) : hbarM ∈ GM Γ := by
  obtain ⟨t, ht, htT⟩ := h.tau
  obtain ⟨s, hs, hsS⟩ := h.s1
  have hT : Tau ∈ GM Γ := mem_GM.2 ⟨t, ht, htT⟩
  have hS : S1 ∈ GM Γ := mem_GM.2 ⟨s, hs, hsS⟩
  have hR := rQ8_mem h hD
  have hm : ∀ {A B : Mat}, A ∈ GM Γ → B ∈ GM Γ → A * B ∈ GM Γ := fun hA hB =>
    (GM Γ).mul_mem hA hB
  rw [← hbar_word]
  simp only [mm_eq]
  exact hm (hm (hm (hm (hm (hm (hm (hm hT hS) hR) hT) hS) hR) hT) hS) hT

theorem real_e23 (h : Hyp Γ) (hD : (cfgOf Γ).1 = mD) : Real Γ (e 2 + e 3) ![0, 0, 2, 2] := by
  have h2 : rep 2 = e 2 + e 3 := by decide +kernel
  have hm : rep 2 ∈ Om Γ := (cfgOf_fst h 2).1 (by rw [hD]; rfl)
  have hr := cfgOf_snd h 2 hm
  have hopt := cfgOf_opt h 2 (by decide)
  rw [(cfgOf_fst h 2).2 hm, optL, if_pos rfl] at hopt
  have hk : okL 2 = [![0, 0, 2, 2]] := rfl
  rw [hk, List.mem_singleton] at hopt
  rw [hopt, h2] at hr
  exact hr

end CFSG.RankThree.PartTwo.Sec21.FF81.P51

end
