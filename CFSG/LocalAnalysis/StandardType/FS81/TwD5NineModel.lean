module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NinePieces
public import CFSG.LocalAnalysis.StandardType.FS81.TwD5NineModelSteps

public section

namespace CFSG.StandardType.FrameRoute.FS81

open QuadraticMap Module CFSG.Open CFSG.Assembly CFSG.SignalizerFunctorTheorem
  CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.RankThree.OrthogonalInvolutions
  CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.OrthBlk
  CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open scoped Matrix commutatorElement

theorem t5NineModel_holds : T5NineModel := by
  intro G _ _ b₀ K E hstd B hB hrec t ht2 htN ht1 htj
  obtain ⟨φ, B', F, j, hB', hjinj, hj, heven, hU, hφB'⟩ :=
    exists_frame_coordinates_of_recOutTwD5 hstd hB hrec
  let A : Subgroup (V5 ≃ₗ[ZMod 2] V5) :=
    ((E ⊓ K).subgroupOf K).map ((orthDerived Q5).subtype.comp φ.toMonoidHom)
  have hAΩ : A ≤ orthDerived Q5 := by
    rintro _ ⟨y, -, rfl⟩
    exact (φ y).2
  let β : MulAut ↥(orthDerived Q5) :=
    MulAut.congr φ (Subgroup.normalizerMonoidHom K ⟨t, htN⟩)
  have hβ2 : β * β = 1 := by
    have htt : t * t = 1 := by
      have h2 : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
      simpa [pow_two] using h2
    have htn : (⟨t, htN⟩ : ↥(Subgroup.normalizer (K : Set G))) * ⟨t, htN⟩ = 1 := by
      apply Subtype.ext
      simpa [pow_two] using htt
    have hn : (Subgroup.normalizerMonoidHom K ⟨t, htN⟩) *
        (Subgroup.normalizerMonoidHom K ⟨t, htN⟩) = 1 := by
      rw [← map_mul]
      simpa using congrArg (Subgroup.normalizerMonoidHom K) htn
    have heq : β = MulAut.congr φ (Subgroup.normalizerMonoidHom K ⟨t, htN⟩) := rfl
    rw [heq, ← map_mul, hn, map_one]
  obtain ⟨h, hhO, hhconj⟩ := omegaAutIsometric_quadMinus (n := 4) (by norm_num) β
  have hh2 : h * h = 1 := isometry_mul_self_eq_one hAΩ F hβ2 hhO hhconj
  have hconj : ∀ k : Fin 5, h * frameRot F k * h⁻¹ =
      if k = j 0 then (frameRot F k)⁻¹ else frameRot F k :=
    conj_frameRot_of_mulAut_congr htN ht1 htj hB' hjinj hj hφB' (β := β) rfl hhconj
  obtain ⟨u, huU, huQ, hrefl⟩ :=
    exists_eq_reflect_of_conj_frameRot hAΩ F hU (j 0) hhO hh2 hconj
  let U : Submodule (ZMod 2) V5 := F.U (j 1)
  have h01 : j 0 ≠ j 1 := by
    intro h
    have := hjinj h
    exact absurd this (by decide)
  have huW : u ∈ perpOf Q5 U := by
    rw [perpOf, LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    change polar Q5 w u = 0
    rw [polar_comm]
    exact F.orth (j 0) (j 1) h01 u huU w hw
  have hU' : PolarNondegOn Q5 U := fun u hu huv => F.nondeg (j 1) u hu fun v hv => by
    rw [polar_comm]
    exact huv v hv
  have hU2 : finrank (ZMod 2) U = 2 := hU (j 1)
  have hUc : IsCompl U (perpOf Q5 U) := isCompl_perp hU'
  have hdimV : finrank (ZMod 2) V5 = 10 := by
    simp [Module.finrank_fintype_fun_eq_card, Fintype.card_sum]
  have hdimW : finrank (ZMod 2) (perpOf Q5 U) = 8 := by
    have := Submodule.finrank_add_eq_of_isCompl hUc
    rw [hU2, hdimV] at this
    omega
  have hdim : finrank (ZMod 2) (perpOf Q5 U) = 2 * 4 := by omega
  have hv : (Q5.restrict (perpOf Q5 U)) ⟨u, huW⟩ = 1 := by
    rw [restrict_apply]
    exact huQ
  let a : G := B.b ((1 : Fin 5).succ)
  have ha : a ∈ K := hB.2.2 _ (Fin.succ_ne_zero (1 : Fin 5))
  have hx : ((φ ⟨a, ha⟩ : ↥(orthDerived Q5)) : V5 ≃ₗ[ZMod 2] V5) =
      frameRot F (j 1) ∨ ((φ ⟨a, ha⟩ : ↥(orthDerived Q5)) :
        V5 ≃ₗ[ZMod 2] V5) = (frameRot F (j 1))⁻¹ :=
    phi_eq_or_eq_inv_frameRot hB' hj hφB' (1 : Fin 5) ha
  obtain ⟨hx3, hxU, hxfix⟩ := frameRot_facts_of_eq_or_eq_inv F (j 1) hx
  have hTperp : ∃ T : Submodule (ZMod 2) (perpOf Q5 U), finrank (ZMod 2) T = 3 ∧
      ∀ v ∈ T, (Q5.restrict (perpOf Q5 U)) v = 0 :=
    perp_exists_ts_three nondegenerate_Q5 hU' (by rw [hdimW])
  have h6 : 6 ≤ finrank (ZMod 2) (perpOf Q5 U) := by omega
  have hJleK : nineJ K a ≤ K := (Subgroup.commutator_le_self _).trans inf_le_left
  obtain ⟨Ψ, hΨrestrict, hΨfixU⟩ :=
    nineJ_equiv_restrict φ ha hJleK hU' hU2 hTperp h6 hx3 hxU hxfix
  have hΨ := commute_transport htN φ rfl hhconj hrefl hUc huW hJleK hΨrestrict hΨfixU
  obtain ⟨⟨e⟩, htrans⟩ := inf_centralizer_transport Ψ hΨ
  have hSp := orthDerived_inf_centralizer_reflect (W := ↥(perpOf Q5 U))
    (Q := Q5.restrict (perpOf Q5 U))
    (perp_polarBilin_nondegenerate nondegenerate_Q5 hU') (m := 4) hdim (le_refl 4) hv
  have hsimple : IsSimpleGroup ↥(orthDerived (Q5.restrict (perpOf Q5 U)) ⊓
      Subgroup.centralizer ({reflect (Q5.restrict (perpOf Q5 U)) ⟨u, huW⟩} :
        Set (perpOf Q5 U ≃ₗ[ZMod 2] perpOf Q5 U))) := hSp.1
  have ha2 : a = B.b 2 := rfl
  rw [← ha2]
  refine ⟨nineJ_simple_of_recOutTwD5 hstd hB hrec, ?_, ?_, ?_⟩
  · exact @MulEquiv.isSimpleGroup _ _ _ _ hsimple e
  · rw [Nat.card_congr e.toEquiv]
    exact hSp.2.1
  · exact htrans hSp.2.2

end CFSG.StandardType.FrameRoute.FS81

end
