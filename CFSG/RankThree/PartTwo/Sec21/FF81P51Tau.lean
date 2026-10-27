module

public import CFSG.RankThree.PartTwo.Sec21.FF81P51Ten

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.P51

open Matrix

private theorem pat_tau : Pat mB ![1, 1, 2, 2] ∧ ¬ Pat mB ![2, 2, 0, 0] ∧ Pat mB (e 1) ∧
    ¬ Pat mB ![2, 0, 2, 2] := by
  decide +kernel

private theorem mulVec_tau1 :
    (1 + vecMulVec (rep 6) ![1, 0, 0, 0] : Mat) *ᵥ ![1, 1, 2, 2] = ![2, 2, 0, 0] := by
  decide +kernel

private theorem mulVec_tau2 :
    (1 + vecMulVec (rep 6) ![1, 2, 2, 2] : Mat) *ᵥ e 1 = ![2, 0, 2, 2] := by
  decide +kernel

private theorem T0_zeta : T0 *ᵥ (e 1 + e 2 + e 3) = e 1 + e 2 + e 3 := by decide +kernel

private theorem refl_zeta :
    (1 + vecMulVec (rep 6) ![1, 1, 1, 1] : Mat) *ᵥ (e 1 + e 2 + e 3) = e 1 + e 2 + e 3 := by
  decide +kernel

private theorem refl_e0 :
    (1 + vecMulVec (rep 6) ![1, 1, 1, 1] : Mat) *ᵥ (T0 *ᵥ e 0) = e 0 - (e 1 + e 2 + e 3) := by
  decide +kernel

private theorem okL_six_eq : okL 6 = [![1, 0, 0, 0], ![1, 1, 1, 1], ![1, 2, 2, 2]] := rfl

theorem exists_tau_of_mB {Γ : Subgroup GL4} (h : Hyp Γ)
    (hB : (cfgOf Γ).1 = mB) :
    ∃ g ∈ Γ, (g : Mat) *ᵥ (e 1 + e 2 + e 3) = e 1 + e 2 + e 3 ∧
      (g : Mat) *ᵥ e 0 = e 0 - (e 1 + e 2 + e 3) := by
  have hm : rep 6 ∈ Om Γ := (cfgOf_fst h 6).1 (by rw [hB]; rfl)
  have hr := cfgOf_snd h 6 hm
  have hopt := cfgOf_opt h 6 (by decide)
  rw [(cfgOf_fst h 6).2 hm, optL, if_pos rfl, okL_six_eq] at hopt
  have hOm := mem_Om_iff_pat h hB
  obtain ⟨r, hrΓ, hr1, -⟩ := real_refl h hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hopt
  rcases hopt with h1 | h1 | h1
  · exfalso
    have := mulVec_mem_Om (coe_mem_GM hrΓ) ((hOm _).2 pat_tau.1)
    rw [hr1, h1, mulVec_tau1] at this
    exact pat_tau.2.1 ((hOm _).1 this)
  · obtain ⟨t, htΓ, htT⟩ := h.t0
    refine ⟨r * t, Γ.mul_mem hrΓ htΓ, ?_, ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, htT, T0_zeta, hr1, h1]
      exact refl_zeta
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec, htT, hr1, h1]
      exact refl_e0
  · exfalso
    have := mulVec_mem_Om (coe_mem_GM hrΓ) ((hOm _).2 pat_tau.2.2.1)
    rw [hr1, h1, mulVec_tau2] at this
    exact pat_tau.2.2.2 ((hOm _).1 this)

end CFSG.RankThree.PartTwo.Sec21.FF81.P51

end
