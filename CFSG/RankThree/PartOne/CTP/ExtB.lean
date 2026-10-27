module

public import CFSG.RankThree.PartOne.CTP.ExtSp
public import CFSG.RankThree.PartOne.CTP.SuEdge
public import CFSG.RankThree.PartOne.CTP.SuSpin
public import CFSG.RankThree.PartOne.CTP.SpinCenterEven
public import CFSG.LieType.Universal.IrreducibleQuadratic
public import CFSG.RankThree.PartOne.CTP.SU4EvenBridge

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieAdmissible StatedSU StatedProj
  StatedScalars)
open CFSG.ClassicalInvolution.Models.TwistedPairs (TwistedB2BlockStandardPair minusLongBlock
  shortBlock finOne)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.Universal.Unitary (SUid SUid_eq_statedSU isQuasisimple_statedSU_of_card
  map_center_mulEquiv conjEquiv)
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.RankThree.PartOne.CTP.SU4Even (exists_kleinDataEven map_minusLongBlock_eq_lbEmb
  map_shortBlock_eq_sbEmb minusLongBlock_injective)
open CFSG.LieType.Universal.Spin (quadMinus)
open scoped MatrixGroups

section Models

theorem nonempty_suid_four_equiv_of_psu_model {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (h : UnitaryFieldData 2 f K) (hq : 4 ≤ 2 ^ f) {X : Type} [Group X]
    (e : X ≃* StatedProj (StatedSU 4 (2 ^ f) K)) :
    Nonempty (SUid (unitaryInvolution K 2 f) 4 ≃* X) := by
  have hK : Nat.card K = (2 ^ f) ^ 2 := h.card_eq_sq
  have hnq : ((4 : ℕ), 2 ^ f) ≠ (3, 2) := by
    intro h'
    have := congrArg Prod.fst h'
    simp at this
  obtain ⟨-, hZ⟩ := isQuasisimple_statedSU_of_card (p := 2) (f := f) hK (by norm_num : 3 ≤ 4) hnq
  let Ξ : SUid (unitaryInvolution K 2 f) 4 ≃* ↥(StatedSU 4 (2 ^ f) K) :=
    MulEquiv.subgroupCongr (SUid_eq_statedSU hK 4)
  have hZbot : Subgroup.center ↥(StatedSU 4 (2 ^ f) K) = ⊥ := by
    rw [← map_center_mulEquiv Ξ, center_suid_four_eq_bot h hq, Subgroup.map_bot]
  have hN : (StatedScalars (Fin 4) K).subgroupOf (StatedSU 4 (2 ^ f) K) = ⊥ := by
    rw [← hZ, hZbot]
  exact ⟨(Ξ.trans (QuotientGroup.quotientBot.symm.trans
    (QuotientGroup.quotientMulEquivOfEq hN.symm))).trans e.symm⟩

theorem statedClassicalModel_pOmegaMinus_of_mulEquiv {G G' : Type} [Group G] [Group G']
    (e : G ≃* G') {n f : ℕ} (h : StatedClassicalModel G' .POmegaMinus n 2 f) :
    StatedClassicalModel G .POmegaMinus n 2 f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm h

end Models

theorem extCurtisTitsBThree : ExtCurtisTitsBThree := by
  intro G _ _ f p K₁ K₂ K₃ E hf hp hpq hE hgen h₁ h₂ h₃ hcomm₁₃ hL3 hSU htor hz
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hSU
  have : CharP K 2 := charP_two_of_card_eq_two_pow (f := 2 * f) (by rw [hK]; ring)
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hfd : UnitaryFieldData 2 f K := ⟨Nat.prime_two, by omega, by rw [hK]; ring⟩
  obtain ⟨ψ⟩ := nonempty_suid_four_equiv_of_psu_model hfd hq4 e
  let θ : SUid (unitaryInvolution K 2 f) 4 →* G := (K₂ ⊔ K₃).subtype.comp ψ.toMonoidHom
  have hθinj : Function.Injective θ := (Subgroup.subtype_injective _).comp ψ.injective
  have hθrange : θ.range = K₂ ⊔ K₃ := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ψ.surjective, Subgroup.map_top,
      Subgroup.range_subtype]
  have hθker : θ.ker ≤ Subgroup.center (SUid (unitaryInvolution K 2 f) 4) := by
    rw [(MonoidHom.ker_eq_bot_iff θ).mpr hθinj]
    exact bot_le
  have hE₂₃ : EdgeTorus p E K₂ K₃ :=
    ⟨(htor.1 1).1, (htor.1 1).2, (htor.1 2).1, (htor.1 2).2, htor.2 1 2 (by decide)⟩
  have hE₁₂ : EdgeTorus p E K₁ K₂ :=
    ⟨(htor.1 0).1, (htor.1 0).2, (htor.1 1).1, (htor.1 1).2, htor.2 0 1 (by decide)⟩
  obtain ⟨F, _, _, _, hF, ⟨ρ₂⟩⟩ := exists_sl2_equiv_of_model h₂
  obtain ⟨L₃, _, _, _, hL₃, ⟨ρ₃⟩⟩ := exists_sl2_equiv_of_model h₃
  have hL₃' : Nat.card L₃ = (2 ^ f) ^ 2 := by rw [hL₃]; ring
  obtain ⟨Q, hQ, hA, hB⟩ := su_edge_pair hfd hf θ hθker hp hpq hE₂₃ hθrange.symm hF hL₃' ρ₂ ρ₃ hz
  obtain ⟨b, c, hirr⟩ := CFSG.LieType.Universal.exists_irreducible_quadratic F
  have := CFSG.LieType.Universal.Spin.Twisted.fact_shortField hirr
  obtain ⟨inst, ⟨D⟩⟩ := exists_kleinDataEven hF hK hirr
  have hK₂le : K₂ ≤ θ.range := by rw [hθrange]; exact le_sup_left
  have hK₃le : K₃ ≤ θ.range := by rw [hθrange]; exact le_sup_right
  let Θ : spinGroup (quadMinus 3 F b c) →* G :=
    (θ.comp (conjEquiv Q hQ).toMonoidHom).comp (D.PhiSUEven hirr)
  have hΘinj : Function.Injective Θ :=
    hθinj.comp ((conjEquiv Q hQ).injective.comp (D.PhiSUEven_injective hirr))
  have hΘrange : Θ.range = K₂ ⊔ K₃ := by
    rw [MonoidHom.range_comp, D.range_PhiSUEven_eq_top hK hirr, Subgroup.map_top,
      MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (conjEquiv Q hQ).surjective,
      Subgroup.map_top, hθrange]
  have hT : ∃ W, TwistedB2BlockStandardPair hirr W K₂ K₃ := by
    refine ⟨K₂ ⊔ K₃, Θ, hΘrange, ?_, ?_, ?_, ?_, ?_⟩
    · rw [(MonoidHom.ker_eq_bot_iff Θ).mpr hΘinj]
      exact bot_le
    · exact hΘinj.comp minusLongBlock_injective
    · exact hΘinj.comp (shortBlock_injective_even hirr 3 finOne)
    · calc (minusLongBlock b c).range.map Θ
          = (((minusLongBlock b c).range.map (D.PhiSUEven hirr)).map
              (conjEquiv Q hQ).toMonoidHom).map θ := by
            rw [Subgroup.map_map, Subgroup.map_map]
        _ = ((lbEmb (unitaryInvolution K 2 f)).range.map (conjEquiv Q hQ).toMonoidHom).map θ := by
            rw [map_minusLongBlock_eq_lbEmb D hF hK hirr]
        _ = (K₂.comap θ).map θ := by rw [hA]
        _ = K₂ := by rw [Subgroup.map_comap_eq, inf_of_le_right hK₂le]
    · calc (shortBlock hirr 3 finOne).range.map Θ
          = (((shortBlock hirr 3 finOne).range.map (D.PhiSUEven hirr)).map
              (conjEquiv Q hQ).toMonoidHom).map θ := by
            rw [Subgroup.map_map, Subgroup.map_map]
        _ = ((sbEmb (unitaryInvolution K 2 f)
              (unitaryInvolution_involutive hK)).range.map (conjEquiv Q hQ).toMonoidHom).map θ := by
            rw [map_shortBlock_eq_sbEmb D hF hK hirr]
        _ = (K₃.comap θ).map θ := by rw [hB]
        _ = K₃ := by rw [Subgroup.map_comap_eq, inf_of_le_right hK₃le]
  have hpair : ∃ W, LinearBlockStandardPair F W K₁ K₂ :=
    exists_linearBlockStandardPair hf hp hpq hE₁₂ h₁ h₂ hL3 hF
  have hadm : StatedLieAdmissible .POmegaMinus 4 2 f := ⟨Nat.prime_two, by omega, le_rfl⟩
  have hgen' : (⨆ k : Fin 3, (![K₁, K₂, K₃] : Fin 3 → Subgroup G) k) = ⊤ := by
    rw [← hgen]
    refine le_antisymm (iSup_le fun k => ?_) ?_
    · fin_cases k
      · exact le_sup_of_le_left le_sup_left
      · exact le_sup_of_le_left le_sup_right
      · exact le_sup_right
    · exact sup_le (sup_le (le_iSup (fun k : Fin 3 => (![K₁, K₂, K₃] : Fin 3 → Subgroup G) k) 0)
        (le_iSup (fun k : Fin 3 => (![K₁, K₂, K₃] : Fin 3 → Subgroup G) k) 1))
        (le_iSup (fun k : Fin 3 => (![K₁, K₂, K₃] : Fin 3 → Subgroup G) k) 2)
  obtain ⟨Ψ, -, -, -, hcenter, hmodel, -⟩ := weakCT_spinMinus_even (n := 4) (f := f) hadm hF
    (by rw [hF]; exact hq4) hirr (U := ![K₁, K₂, K₃]) hgen'
    (fun i j hij a ha b hb => by
      fin_cases i <;> fin_cases j <;> simp at hij
      exact (Subgroup.mem_centralizer_iff.mp (hcomm₁₃.1 ha) b hb).symm)
    (fun i j hij hj => by
      fin_cases i <;> fin_cases j <;> simp at hij hj
      exact hpair)
    (fun i j hi hj => by
      fin_cases i <;> fin_cases j <;> simp at hi hj
      exact hT)
  have hcen : Subgroup.center G = ⊥ := by
    rw [hcenter, center_spinGroup_quadMinus_eq_bot (by norm_num : 4 ≤ 4) hirr,
      Subgroup.map_bot]
  have hLie := CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel
    (by decide : CFSG.Assembly.LowTwoRank.StatedLieTag.POmegaMinus ∈ CFSG.Blueprint.classicalTags)
    hmodel
  exact statedClassicalModel_pOmegaMinus_of_mulEquiv
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hcen.symm)) hLie

end CFSG.RankThree.PartOne.CTP
