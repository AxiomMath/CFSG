module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenTwentyThreeInputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusSingTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusPointStab
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusEvenClause

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus)

theorem singConcl_pointStabilizer_std {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ} (hcard : Nat.card F = 2 ^ n) :
    SingConcl (Gom (quadMinus 3 F b c)) n
      (pointStabilizer (quadMinus 3 F b c) (stdP0 F b c).e) := by
  have hQ := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite
    (n := 3) (K := F) hirr
  have h4 : 4 ≤ Module.finrank F (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F) := by simp
  exact ⟨isParabolicTwo_pointStabilizer hQ h4 (stdP0 F b c).e_ne_zero (stdP0 F b c).Q_e,
    pCoreOf_pointStabilizer_ne_bot hQ h4 (stdP0 F b c).e_ne_zero (stdP0 F b c).Q_e,
    isL2_bar2_derInf_std hcard hirr (leviSub_le_pointStabilizer _) le_rfl,
    pCoreOf_derInf_pointStabilizer_std_ne_bot hirr, fun hn => even_clause hirr hcard hn⟩

theorem singConcl_pointStabilizer {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {n : ℕ} (hcard : Nat.card F = 2 ^ n)
    {w : Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2 → F} (hw : w ≠ 0) (hQw : quadMinus 3 F b c w = 0) :
    SingConcl (Gom (quadMinus 3 F b c)) n (pointStabilizer (quadMinus 3 F b c) w) := by
  have hQ := CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite
    (n := 3) (K := F) hirr
  obtain ⟨g, hg, hgw⟩ := exists_mem_elementaryGroup_apply_eq hQ (stdP0_orth_stdP1 F b c)
    (stdP0 F b c).e_ne_zero hw (by rw [(stdP0 F b c).Q_e, hQw])
  have h := SingConcl.map_mulEquiv (MulAut.conj (⟨g, hg⟩ : Gom (quadMinus 3 F b c)))
    (singConcl_pointStabilizer_std hirr hcard)
  have happ : Gom.app (⟨g, hg⟩ : Gom (quadMinus 3 F b c)) (stdP0 F b c).e = w := hgw
  rwa [map_conj_pointStabilizer, happ] at h

theorem k_K_Omega6Minus_singularPointStabilizer_holds :
    K_Omega6Minus_singularPointStabilizer := by
  intro F _ _ b c n hcard hirr w hw hQw
  have hn : 1 ≤ n := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp at hcard; omega
    · exact h0
  haveI : CharP F 2 := uc22p22d_charP_two hn hcard
  have hQw' : quadMinus 3 F b c w = 0 := by
    have := congrFun (coe_quadMinus 3 F b c) w
    rw [this]; exact hQw
  let e6 := statedOmegaMinusEquiv (m := 3) (K := F) (b := b) (c := c) (by norm_num) hirr
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    SingConcl.map_mulEquiv e6.symm (singConcl_pointStabilizer hirr hcard hw hQw')
  refine ⟨(pointStabilizer (quadMinus 3 F b c) w).map e6.symm.toMonoidHom, ?_, h1, h2, h3, h4, h5⟩
  intro g hg
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
  obtain ⟨c', hc'⟩ := hx
  have h := statedOmegaMinusEquiv_symm_app (by norm_num) hirr x w
  rw [hc'] at h
  exact h ▸ Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

end
