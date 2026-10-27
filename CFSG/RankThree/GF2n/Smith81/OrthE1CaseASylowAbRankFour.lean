module

public import CFSG.RankThree.GF2n.Smith81.OrthE1CtStructure
public import CFSG.RankThree.GF2n.Smith81.OrthE1CaseASylowAbRank

public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1.CaseASylowAb

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

theorem finrank_range_sub_eq_four {K : Type} [Field K] (S : QSpace K)
    (h8 : Module.finrank K S.E = 8) {V : Submodule K S.E} {β : S.E →ₗ[K] S.E}
    (hβ : BetaProps S V β) {ι : Type} [Fintype ι] [DecidableEq ι]
    (cV : V ≃ₗ[K] (ι → K)) (hcard : Fintype.card ι = 4)
    (σ : V →ₗ[K] S.E) (hσ : ∀ v : V, β (σ v) = v)
    (T : S.E ≃ₗ[K] S.E) (hTβ : ∀ e, T (β e) = β (T e)) (hTT : T * T = 1)
    (A : Matrix ι ι K)
    (hA : ∀ (v : S.E) (hv : v ∈ V), ∃ hw : T v ∈ V, cV ⟨T v, hw⟩ = A *ᵥ cV ⟨v, hv⟩)
    (hA1 : A = 1 → ∃ c : K, c ≠ 0 ∧ ∀ e, T e = e + c • β e)
    (hAeven : A ≠ 1 → Even (A - 1).rank) :
    Module.finrank K (LinearMap.range ((T : S.E →ₗ[K] S.E) - 1)) = 4 := by
  have hsymm : ∀ e f : S.E, S.B e f = S.B f e := by
    intro e f
    have h1 := S.Qf_add e f
    have h2 := S.Qf_add f e
    rw [add_comm f e] at h2
    linear_combination h2 - h1
  have hB2 : ∀ e f : S.E, (2 : K) * S.B e f = 0 := by
    intro e f
    have h := S.alt (e + f)
    simp only [map_add, LinearMap.add_apply, S.alt e, S.alt f] at h
    linear_combination h + hsymm e f
  have h2K : (2 : K) = 0 := by
    obtain ⟨e0, he0⟩ : ∃ e : S.E, e ≠ 0 :=
      (Module.finrank_pos_iff_exists_ne_zero (R := K)).mp (by rw [h8]; norm_num)
    obtain ⟨f0, hf0⟩ : ∃ f : S.E, S.B e0 f ≠ 0 := by
      by_contra hcon
      exact he0 (S.nondeg e0 fun f => not_not.mp (not_exists.mp hcon f))
    exact (mul_eq_zero.mp (hB2 e0 f0)).resolve_right hf0
  have hdouble : ∀ x : S.E, x + x = 0 := fun x => by
    rw [← two_smul K x, h2K, zero_smul]
  have hT2 : ∀ e : S.E, T (T e) = e := fun e => by
    have h := congrArg (fun g : S.E ≃ₗ[K] S.E => g e) hTT
    simpa [LinearEquiv.mul_apply] using h
  have hNN : ((T : S.E →ₗ[K] S.E) - 1) * ((T : S.E →ₗ[K] S.E) - 1) = 0 := by
    apply LinearMap.ext
    intro e
    simp only [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      LinearMap.zero_apply, LinearEquiv.coe_coe, map_sub, hT2]
    have hab : ∀ x y : S.E, x - y - (y - x) = (x - y) + (x - y) := fun x y => by abel
    rw [hab]
    exact hdouble _
  have hle4 := rank_le_four S h8 (T : S.E →ₗ[K] S.E) hNN
  have hV4 : Module.finrank K V = 4 := by
    rw [LinearEquiv.finrank_eq cV, Module.finrank_fintype_fun_eq_card, hcard]
  by_cases hA1' : A = 1
  · obtain ⟨c, hc0, hc⟩ := hA1 hA1'
    have hN : (T : S.E →ₗ[K] S.E) - 1 = c • β := by
      apply LinearMap.ext
      intro e
      simp only [LinearMap.sub_apply, Module.End.one_apply, LinearMap.smul_apply,
        LinearEquiv.coe_coe]
      rw [hc e]
      abel
    rw [hN, LinearMap.range_smul β c hc0, ctS_beta_range_eq S h8 hV4 hβ]
    exact hV4
  · have hlow := two_mul_rank_le S hβ σ hσ (T : S.E →ₗ[K] S.E) hTβ
    have hdim := finrank_map_sub_eq_rank S cV (T : S.E →ₗ[K] S.E) A hA
    have hr0 : (A - 1).rank ≠ 0 := by
      intro h0
      apply hA1'
      have h0' : Module.finrank K (LinearMap.range (A - 1).mulVecLin) = 0 := h0
      rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h0'
      have h3 : Matrix.toLin' (A - 1) = 0 := h0'
      exact sub_eq_zero.mp (Matrix.toLin'.map_eq_zero_iff.mp h3)
    obtain ⟨k, hk⟩ := hAeven hA1'
    omega

end CFSG.RankThree.GF2n.Smith81.Smith23E1.CaseASylowAb

end
