module

public import CFSG.LocalAnalysis.StandardType.GGLangTwoPairAux
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.InnerSmallF4Const
public import CFSG.GroupTheory.CommuteOfSqEqOne


public section

namespace CFSG.StandardType.LangRat

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open scoped commutatorElement



private theorem j4d_commute_pinnedX
    {τ : Tag} {L : Type} [Field L] [CharP L 2]
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {γ β : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hβ : IsRoot τ β)
    (horth : iform γ β = 0) (hne : γ ≠ β) (c d : L) :
    pinnedX τ L γ c * pinnedX τ L β d = pinnedX τ L β d * pinnedX τ L γ c := by
  have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
  have hne' : γ ≠ -β := by
    intro h
    rw [h] at horth
    rw [iform_neg_left] at horth
    have hp := iform_self_pos_of_isRoot hβ
    omega
  by_cases hF : τ = .F4
  · subst hF
    by_cases hsum : IsRoot Tag.F4 (γ + β)
    · have hγcases := iform_self_cases noG2_F4 hγ
      have hβcases := iform_self_cases noG2_F4 hβ
      have hδcases := iform_self_cases noG2_F4 hsum
      have hsum_norm : iform (γ + β) (γ + β) = iform γ γ + iform β β := by
        rw [iform_add_left, iform_add_right, iform_add_right, horth, iform_comm β γ, horth]
        ring
      have hshort : iform γ γ = 2 ∧ iform β β = 2 := by
        rcases hγcases with hγ2 | hγ4
        · rcases hβcases with hβ2 | hβ4
          · exact ⟨hγ2, hβ2⟩
          · rw [hsum_norm, hγ2, hβ4] at hδcases
            rcases hδcases with hδc | hδc <;> omega
        · rcases hβcases with hβ2 | hβ4
          · rw [hsum_norm, hγ4, hβ2] at hδcases
            rcases hδcases with hδc | hδc <;> omega
          · rw [hsum_norm, hγ4, hβ4] at hδcases
            rcases hδcases with hδc | hδc <;> omega
      obtain ⟨hγ2, hβ2⟩ := hshort
      have hcoroot : corootPair γ (γ + β) = 2 := by
        rw [corootPair, iform_add_right, horth, add_zero, hγ2]
        norm_num
      have hroot : IsRoot Tag.F4 (β - γ) := by
        have h := IsRoot.smul hsum (rootReflection γ)
        rwa [rootReflection_smul hγ (γ + β), hcoroot,
          show (γ + β) - (2 : ℤ) • γ = β - γ by abel] at h
      obtain ⟨C, hCabs, hform⟩ := exists_pinnedX_commFormula_F4_exact hγ hβ hne hne'
      have hcp : commPairs Tag.F4 γ β = [(1, 1)] := by
        refine list_eq_singleton_of_forall_eq ?_ (commPairs_nodup γ β) ?_
        · intro p hp
          obtain ⟨h1, h2, hr⟩ :=
            (mem_commPairs_iff_of_isRoot hγ hβ hne hne' p).1 hp
          rcases exponent_pair_cases noG2_F4 hγ hβ hne hne' (by omega) (by omega) hr with
            h | h | h
          · exact Prod.ext h.1 h.2
          · obtain ⟨-, -, hgg, -, -⟩ := h
            rw [hgg] at hγ2
            omega
          · obtain ⟨-, -, -, hbb, -⟩ := h
            rw [hbb] at hβ2
            omega
        · rw [mem_commPairs_iff_of_isRoot hγ hβ hne hne']
          exact ⟨by norm_num, by norm_num, by simpa using hsum⟩
      have hmem11 : ((1, 1) : ℕ × ℕ) ∈ commPairs Tag.F4 γ β := by
        rw [hcp]
        exact List.mem_singleton_self _
      have hC11 : |C (1, 1)| = 2 := by
        have := hCabs (1, 1) hmem11
        simpa [hroot] using this
      have hC2 : C (1, 1) = 2 ∨ C (1, 1) = -2 := by
        rcases abs_eq (by norm_num : (0 : ℤ) ≤ 2) |>.1 hC11 with h | h
        · exact Or.inl h
        · exact Or.inr h
      have hcoef : ((C (1, 1) : ℤ) : L) = 0 := by
        rcases hC2 with h | h
        · rw [h, Int.cast_ofNat, h2]
        · rw [h, Int.cast_neg, Int.cast_ofNat, h2, neg_zero]
      have hformula := hform L c d
      rw [hcp] at hformula
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
        one_smul, pow_one] at hformula
      rw [hcoef] at hformula
      simp only [zero_mul, pinnedX_zero] at hformula
      have ha : pinnedX Tag.F4 L γ c * pinnedX Tag.F4 L γ c = 1 := by
        rw [← pinnedX_add, show c + c = 0 by rw [← two_mul, h2, zero_mul], pinnedX_zero]
      have hb : pinnedX Tag.F4 L β d * pinnedX Tag.F4 L β d = 1 := by
        rw [← pinnedX_add, show d + d = 0 by rw [← two_mul, h2, zero_mul], pinnedX_zero]
      rw [CharTwo.neg_eq c, CharTwo.neg_eq d] at hformula
      have ha2 : (pinnedX Tag.F4 L γ c) ^ 2 = 1 := by
        rw [pow_two]
        exact ha
      have hb2 : (pinnedX Tag.F4 L β d) ^ 2 = 1 := by
        rw [pow_two]
        exact hb
      have hab2 : (pinnedX Tag.F4 L γ c * pinnedX Tag.F4 L β d) ^ 2 = 1 := by
        rw [pow_two]
        simpa only [mul_assoc] using hformula
      exact CFSG.commute_of_sq_eq_one ha2 hb2 hab2
    · exact pinnedX_commute_of_iform_eq_zero L hγ hβ horth hsum c d
  · have hτ' : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
      rcases hτ with h | h | h | h
      · exact absurd h hF
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    have hsym : ∀ i, τ.symmetrizer i i = 1 := by
      rcases hτ' with rfl | rfl | rfl <;> intro i <;>
        simp [CFSG.Blueprint.Chevalley.Tag.symmetrizer]
    have hself : ∀ {δ : Fin τ.rank → ℤ}, IsRoot τ δ → iform δ δ = 2 := by
      intro δ hδ
      obtain ⟨j, hj⟩ := iform_self_of_isRoot hδ
      rw [hj, hsym j, mul_one]
    have hnr : ¬ IsRoot τ (γ + β) := by
      intro hr
      have h4 := hself hr
      rw [iform_add_left, iform_add_right, iform_add_right, hself hγ, hself hβ, horth,
        iform_comm β γ, horth] at h4
      omega
    exact pinnedX_commute_of_iform_eq_zero L hγ hβ horth hnr c d

theorem j4d_pair_detects_same
    {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ} (S : LangSetup τ L p₀)
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hq : S.D.q = 2) (hAlg : S.IsAlgebraic)
    {a b : Fin τ.rank → Lˣ} (i : KernelComponent (rootCharHom a))
    (hle : rationalComponent S.ρ S.Γ (rootCharHom a) i ≤
      Subgroup.centralizer {rootDiagUnit τ b})
    {γ β : Fin τ.rank → ℤ}
    (hγcomp : γ ∈ componentRoots (rootCharHom a) i)
    (hβcomp : β ∈ componentRoots (rootCharHom a) i)
    (hγr : IsRoot τ γ) (hβr : IsRoot τ β)
    (hργ : S.ρ γ = β) (hρβ : S.ρ β = γ) (horth : iform γ β = 0) (hne : γ ≠ β) :
    rootChar b γ = 1 ∧ rootChar b β = 1 := by
  classical
  haveI : CharP L 2 := charP_two_of_langSetup_q_eq_two_pow (f := 1) S (by rw [hq]; norm_num)
  have h2L : (2 : L) = 0 := CharP.cast_eq_zero L 2
  obtain ⟨w, hw⟩ := j4e_exists_cubeRoot h2L
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; norm_num at hw
  let ω : Lˣ := Units.mk0 w hw0
  have hωcoe : (ω : L) = w := rfl
  have hω0 : (ω : L) ≠ 0 := by rw [hωcoe]; exact hw0
  have hω2ne : ((ω ^ 2 : Lˣ) : L) ≠ 0 := by
    rw [Units.val_pow_eq_pow_val]
    exact pow_ne_zero 2 hω0
  have hωa : (ω : L) ^ 2 + 1 = (ω : L) := by
    rw [hωcoe]
    have h : w ^ 2 + 1 - w = 0 := by linear_combination hw - w * h2L
    exact sub_eq_zero.1 h
  have hωb : (ω : L) + 1 = (ω : L) ^ 2 := by
    rw [hωcoe]
    have h : w + 1 - w ^ 2 = 0 := by linear_combination hw - w ^ 2 * h2L
    exact sub_eq_zero.1 h
  have hω3 : ω ^ 3 = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hωcoe, Units.val_one]
    have h : w ^ 3 - 1 = (w - 1) * (w ^ 2 + w + 1) := by ring
    rw [hw, mul_zero] at h
    exact sub_eq_zero.1 h
  have hω23 : (ω ^ 2) ^ 3 = 1 := by
    rw [← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hω3, one_pow]
  have hω4 : (ω ^ 2) ^ 2 = ω := by
    rw [← pow_mul]
    norm_num
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, hω3, one_mul]
  have hβrat : β ∈ rationalRoots S.ρ (rootCharHom a) i := by
    refine ⟨1, γ, hγcomp, ?_⟩
    rw [Function.iterate_one, hργ]
  have hq1 : S.D.q = 2 ^ 1 := by rw [hq]; norm_num
  have hstepα : S.D.step (rootSL2 τ L γ (HSL ω)) = rootSL2 τ L β (HSL (ω ^ 2)) := by
    rw [j4e_step_rootSL2_HSL_swap S hq hγr ω, hργ]
  have hstepβ : S.D.step (rootSL2 τ L β (HSL (ω ^ 2))) = rootSL2 τ L γ (HSL ω) := by
    rw [j4e_step_rootSL2_HSL_swap S hq hβr (ω ^ 2), hρβ, hω4]
  have hstepWα : S.D.step (rootSL2 τ L γ WSL) = rootSL2 τ L β WSL := by
    rw [step_rootSL2_WSL_of_charTwo S hγr, hργ]
  have hstepWβ : S.D.step (rootSL2 τ L β WSL) = rootSL2 τ L γ WSL := by
    rw [step_rootSL2_WSL_of_charTwo S hβr, hρβ]
  have hdR : rootDiagUnit τ (fun k => ω ^ corootPair γ (Pi.single k 1) *
      (ω ^ 2) ^ corootPair β (Pi.single k 1)) ∈
      rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    rootDiagUnit_mul_corootPair_mem_rationalComponent_of_step S hτ hq1 hAlg i hγcomp hβrat horth
      (t := ω) (t' := ω ^ 2) (m := 3) (by norm_num) hω3 hω23 hstepα hstepβ hstepWα hstepWβ
  let x : ModGL τ L := rootSL2 τ L γ (HSL ω)
  let y : ModGL τ L := rootSL2 τ L β (HSL (ω ^ 2))
  have hx : x = rootDiagUnit τ (fun k => ω ^ corootPair γ (Pi.single k 1)) :=
    j4e_rootSL2_HSL_eq_rootDiagUnit hγr ω
  have hy : y = rootDiagUnit τ (fun k => (ω ^ 2) ^ corootPair β (Pi.single k 1)) :=
    j4e_rootSL2_HSL_eq_rootDiagUnit hβr (ω ^ 2)
  have hhR : x * y ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i := by
    rw [hx, hy, ← rootDiagUnit_mul]
    exact hdR
  have hhH : x * y ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i :=
    (Subgroup.commutator_le_self (rationalSpan S.ρ S.Γ (rootCharHom a) i)) hhR
  let Xγ : L → ModGL τ L := pinnedX τ L γ
  let Xβ : L → ModGL τ L := pinnedX τ L β
  have hcommXY : Commute (Xγ 1) (Xβ 1) :=
    (commute_iff_eq _ _).2 (j4d_commute_pinnedX hτ hγr hβr horth hne 1 1)
  let e1 : ModGL τ L := Xγ 1 * Xβ 1
  have hγrat : γ ∈ rationalRoots S.ρ (rootCharHom a) i := ⟨0, γ, hγcomp, rfl⟩
  have he1rootSpan : e1 ∈ rootSpan τ L (rationalRoots S.ρ (rootCharHom a) i) := by
    refine mul_mem ?_ ?_
    · exact pinnedX_mem_rootSpan hγrat 1
    · exact pinnedX_mem_rootSpan hβrat 1
  have he1M : e1 ∈ S.D.model := by
    refine ⟨?_, ?_⟩
    · exact mul_mem (pinnedX_mem_adjointGroup γ 1) (pinnedX_mem_adjointGroup β 1)
    · change S.D.step (Xγ 1 * Xβ 1) = Xγ 1 * Xβ 1
      rw [map_mul, j4e_step_pinnedX_of_q_two S hq hγr 1,
        j4e_step_pinnedX_of_q_two S hq hβr 1, hργ, hρβ]
      simpa using hcommXY.eq.symm
  have he1sq : e1 ^ 2 = 1 := by
    have hX : Xγ 1 * Xγ 1 = 1 := by
      rw [← pinnedX_add, show (1 : L) + 1 = 0 by rw [← two_mul, h2L, zero_mul], pinnedX_zero]
    have hY : Xβ 1 * Xβ 1 = 1 := by
      rw [← pinnedX_add, show (1 : L) + 1 = 0 by rw [← two_mul, h2L, zero_mul], pinnedX_zero]
    simp only [e1, pow_two]
    calc (Xγ 1 * Xβ 1) * (Xγ 1 * Xβ 1)
        = Xγ 1 * (Xβ 1 * Xγ 1) * Xβ 1 := by group
      _ = Xγ 1 * (Xγ 1 * Xβ 1) * Xβ 1 := by rw [hcommXY.eq]
      _ = (Xγ 1 * Xγ 1) * (Xβ 1 * Xβ 1) := by group
      _ = 1 := by rw [hX, hY, one_mul]
  have he1Γ : e1 ∈ S.Γ :=
    langModel_mem_Γ_of_sq_mem S hτ hq1 hAlg he1M (by rw [he1sq]; exact one_mem _)
  have he1H : e1 ∈ rationalSpan S.ρ S.Γ (rootCharHom a) i := ⟨he1rootSpan, he1Γ⟩
  have hω4L : (((ω : L) ^ 2) ^ 2) = (ω : L) := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, hω4]
  have hx_self : x * Xγ 1 * x⁻¹ = Xγ (ω ^ 2) := by
    have h := j4e_rootSL2_HSL_conj_pinnedX_self hγr ω 1
    simpa [mul_one] using h
  have hx_orth : ∀ c : L, x * Xβ c * x⁻¹ = Xβ c := fun c =>
    j4e_rootSL2_HSL_conj_pinnedX_of_orthogonal hγr hβr horth ω c
  have horth' : iform β γ = 0 := by rw [iform_comm]; exact horth
  have hy_self : y * Xβ 1 * y⁻¹ = Xβ (ω : L) := by
    have h := j4e_rootSL2_HSL_conj_pinnedX_self hβr (ω ^ 2) 1
    simpa [hω4L, mul_one] using h
  have hy_orth : ∀ c : L, y * Xγ c * y⁻¹ = Xγ c := fun c =>
    j4e_rootSL2_HSL_conj_pinnedX_of_orthogonal hβr hγr horth' (ω ^ 2) c
  have hyconj : y * e1 * y⁻¹ = Xγ 1 * Xβ (ω : L) := by
    rw [show y * e1 * y⁻¹ = (y * Xγ 1 * y⁻¹) * (y * Xβ 1 * y⁻¹) by
      simp only [e1]; group]
    rw [hy_orth, hy_self]
  have hxconj : x * (Xγ 1 * Xβ (ω : L)) * x⁻¹ = Xγ (ω ^ 2) * Xβ (ω : L) := by
    rw [show x * (Xγ 1 * Xβ (ω : L)) * x⁻¹ =
      (x * Xγ 1 * x⁻¹) * (x * Xβ (ω : L) * x⁻¹) by group]
    rw [hx_self, hx_orth]
  have hconj : (x * y) * e1 * (x * y)⁻¹ = Xγ (ω ^ 2) * Xβ (ω : L) := by
    calc (x * y) * e1 * (x * y)⁻¹ = x * (y * e1 * y⁻¹) * x⁻¹ := by group
      _ = x * (Xγ 1 * Xβ (ω : L)) * x⁻¹ := by rw [hyconj]
      _ = Xγ (ω ^ 2) * Xβ (ω : L) := hxconj
  have he1inv : e1⁻¹ = e1 := by
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact he1sq)
  have hcommEq : ⁅x * y, e1⁆ = Xγ (ω : L) * Xβ ((ω ^ 2 : Lˣ) : L) := by
    rw [commutatorElement_def, hconj, he1inv]
    simp only [e1]
    have hc : Commute (Xβ (ω : L)) (Xγ 1) :=
      (commute_iff_eq _ _).2 (j4d_commute_pinnedX hτ hβr hγr
        (by rw [iform_comm]; exact horth) hne.symm (ω : L) 1)
    calc Xγ (ω ^ 2) * Xβ (ω : L) * (Xγ 1 * Xβ 1)
        = Xγ (ω ^ 2) * (Xβ (ω : L) * Xγ 1) * Xβ 1 := by group
      _ = Xγ (ω ^ 2) * (Xγ 1 * Xβ (ω : L)) * Xβ 1 := by rw [hc.eq]
      _ = (Xγ (ω ^ 2) * Xγ 1) * (Xβ (ω : L) * Xβ 1) := by group
      _ = Xγ ((ω : L) ^ 2 + 1) * Xβ ((ω : L) + 1) := by
          rw [← pinnedX_add, ← pinnedX_add]
      _ = Xγ (ω : L) * Xβ ((ω ^ 2 : Lˣ) : L) := by
          rw [hωa, hωb, Units.val_pow_eq_pow_val]
  have hmem : ⁅x * y, e1⁆ ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i :=
    Subgroup.commutator_mem_commutator hhH he1H
  rw [hcommEq] at hmem
  have hdcomm : Commute (rootDiagUnit τ b) (Xγ (ω : L) * Xβ ((ω ^ 2 : Lˣ) : L)) :=
    (Subgroup.mem_centralizer_singleton_iff.1 (hle hmem)).symm
  have hfixed : rootDiagUnit τ b * (Xγ (ω : L) * Xβ ((ω ^ 2 : Lˣ) : L)) *
      (rootDiagUnit τ b)⁻¹ = Xγ (ω : L) * Xβ ((ω ^ 2 : Lˣ) : L) := by
    rw [hdcomm.eq]
    group
  have hEq : Xγ ((rootChar b γ : L) * (ω : L)) *
      Xβ ((rootChar b β : L) * ((ω ^ 2 : Lˣ) : L)) =
      Xγ (ω : L) * Xβ ((ω ^ 2 : Lˣ) : L) := by
    calc Xγ ((rootChar b γ : L) * (ω : L)) *
          Xβ ((rootChar b β : L) * ((ω ^ 2 : Lˣ) : L))
        = (rootDiagUnit τ b * Xγ (ω : L) * (rootDiagUnit τ b)⁻¹) *
            (rootDiagUnit τ b * Xβ ((ω ^ 2 : Lˣ) : L) * (rootDiagUnit τ b)⁻¹) := by
          rw [rootDiagUnit_conj_pinnedX b hγr (ω : L),
            rootDiagUnit_conj_pinnedX b hβr ((ω ^ 2 : Lˣ) : L)]
      _ = rootDiagUnit τ b * (Xγ (ω : L) * Xβ ((ω ^ 2 : Lˣ) : L)) *
            (rootDiagUnit τ b)⁻¹ := by group
      _ = Xγ (ω : L) * Xβ ((ω ^ 2 : Lˣ) : L) := hfixed
  have hlin : LinIndepPair γ β := j4e_linIndepPair_of_orthogonal hγr hβr horth
  have huniq := j4e_pinnedX_mul_injective_of_linIndep h2L hγr hβr hlin hEq
  constructor
  · have hval : (rootChar b γ : L) = 1 := by
      apply mul_right_cancel₀ hω0
      simpa using huniq.1
    exact Units.ext hval
  · have hval : (rootChar b β : L) = 1 := by
      apply mul_right_cancel₀ hω2ne
      simpa using huniq.2
    exact Units.ext hval

end CFSG.StandardType.LangRat

end

