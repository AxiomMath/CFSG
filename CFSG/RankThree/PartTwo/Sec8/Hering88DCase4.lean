module

public import CFSG.RankThree.PartTwo.Sec8.Hering88DCommon
public import CFSG.RankThree.PartTwo.Sec8.Hering88DDiag
public import CFSG.RankThree.PartTwo.Sec8.Hering88DPSU
public import CFSG.RankThree.PartTwo.Sec8.Hering88CL2
public import CFSG.RankThree.PartTwo.Sec8.Hering88COdd

public section

namespace CFSG.RankThree.PartTwo.Sec8

namespace Hering88D

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedSU)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.KFacts (psuConj suConj unitaryIsom3 coe_suConj psuConj_mk
  conj_mk_eq_psuConj unitarySU_le_unitaryIsom3 inducedAutHom)
open Matrix


theorem kF88StepDCaseFourOdd_of
    (h45 : Sec4.Item4_5) (h84 : Pair84A) (hC : KF88SwapCent) (hF : KF84Field)
    (hAut : Sec4.K419AutThree) (hT : Hering88C.KF89JCentType419)
    (h47 : Sec4.Inputs47ClassesD4) : KF88StepDCaseFourOdd := by
  rintro G _ _ A c L a b X n h Y hY hIJ x hx hxY ⟨A₀, d', m, hodd, ⟨e₁⟩, -, -⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm1 : 1 ≤ m := hodd.pos
  have h3m : 1 ≤ 3 * m := by omega
  set K := GaloisField 2 (2 * (3 * m)) with hKdef
  have hU : UnitaryFieldData 2 (3 * m) K := Sec4.unitaryFieldData_galoisField 2 (3 * m) h3m
  have hFin : Finite K := hU.finite
  have hq2 : 2 < 2 ^ (3 * m) :=
    lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ 3 * m))
  have hQ := Sec6.isQuasisimple_of_mem_thetaComponentsAt hY
  have hOTC : KFacts.OutThreeCyclic (Y ⧸ aschbacherSolvableCore 3 Y) :=
    KFacts.outThreeCyclic_of_projSU hQ h3m e₁
  set E₀ : Y ⧸ aschbacherSolvableCore 3 Y ≃* unitaryPSU hU 3 :=
    e₁.trans (Sec4.projSUEquivUnitaryPSU 2 (3 * m) hU) with hE₀
  obtain ⟨d, hdcl, hdx, hdA, hd3, hdN, hin, hne, E, hEA, hdE, hInv⟩ :=
    exists_inner_d_two_local h45 h84 hC hF hAut hT h hY hIJ hx hxY hOTC
  obtain ⟨wb, hwb⟩ : ∃ wb : unitaryPSU hU 3,
      inducedAutHom Y E₀ ⟨d, hdN⟩ = MulAut.conj wb := by
    obtain ⟨wb, hwb⟩ := (KFacts.isInnerAut_congr E₀ _).mpr hin
    exact ⟨wb, hwb.symm⟩
  obtain ⟨w, hw⟩ := unitaryProj_surjective hU 3 wb
  set Aw : unitaryIsom3 hU := ⟨(w : GL (Fin 3) K), unitarySU_le_unitaryIsom3 w.2⟩ with hAw
  have hdA' : inducedAutHom Y E₀ ⟨d, hdN⟩ = psuConj hU Aw := by
    rw [hwb, ← hw]
    exact conj_mk_eq_psuConj w
  have hne' : inducedAutHom Y E₀ ⟨d, hdN⟩ ≠ 1 := by
    intro h1
    apply hne
    have h2 : MulAut.congr E₀ (Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩)) = 1 := h1
    exact (MulAut.congr E₀).injective (h2.trans (map_one _).symm)
  have hZ : Subgroup.center (unitaryPSU hU 3) = ⊥ := KFacts.center_unitaryPSU_three_eq_bot hU hq2
  have hw3c : w ^ 3 ∈ unitaryScalars hU 3 := by
    rw [← ker_unitaryProj hU 3, MonoidHom.mem_ker]
    have h1 : MulAut.conj (unitaryProj hU 3 (w ^ 3)) = 1 := by
      rw [map_pow, hw, map_pow, ← hwb]
      exact KFacts.inducedAutHom_pow_eq_one Y E₀ hdN hd3
    have h2 : unitaryProj hU 3 (w ^ 3) ∈ Subgroup.center (unitaryPSU hU 3) :=
      Item83Proof.mem_center_of_conj_eq_one h1
    rwa [hZ, Subgroup.mem_bot] at h2
  have hw3cen : w ^ 3 ∈ Subgroup.center (unitarySU 2 (3 * m) K 3) :=
    unitaryScalars_le_center hU 3 hw3c
  have hws : ∀ c : K, ((w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ c • 1 := by
    intro c' hc'
    apply hne'
    have hcen : w ∈ Subgroup.center (unitarySU 2 (3 * m) K 3) := by
      rw [Subgroup.mem_center_iff]
      intro z
      apply Subtype.ext
      apply Units.ext
      change ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((w : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
      rw [hc', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    have hwbcen : wb ∈ Subgroup.center (unitaryPSU hU 3) := by
      rw [← hw, Subgroup.mem_center_iff]
      intro y
      obtain ⟨z, rfl⟩ := unitaryProj_surjective hU 3 y
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hcen z)]
    rw [hwb]
    ext z
    rw [MulAut.conj_apply, MulAut.one_apply, (Subgroup.mem_center_iff.mp hwbcen z).symm,
      mul_inv_cancel_right]
  have hmod : Sec4.ModThree false (2 ^ (3 * m)) := by
    have := KFacts.three_dvd_two_pow_three_mul_add_one hodd
    change 2 ^ (3 * m) % 3 = 2
    omega
  have hw3 : w ^ 3 ≠ 1 := by
    intro hw3
    obtain ⟨Xb, hXb1, hXb2, hXbinv⟩ := hInv
    have hτ : Sec4.thetaQuotMulAut Y (Y.normalizerMonoidHom ⟨d, hdN⟩) ∈ Sec4.autThetaQuot E Y :=
      Sec4.mem_autThetaQuot_iff.2 ⟨d, hdN, hdE, rfl⟩
    have hX' : Xb.map E₀.toMonoidHom = ⊥ :=
      eq_bot_of_normalizes_psu hU hmod hw3 hws (hXb2.map E₀.toMonoidHom) (by
        rintro _ ⟨y, hy, rfl⟩
        refine ⟨_, hXbinv _ hτ y hy, ?_⟩
        have h1 : psuConj hU Aw (E₀ y) = E₀ (Sec4.thetaQuotMulAut Y (Y.normalizerMonoidHom
            ⟨d, hdN⟩) y) := by
          rw [← hdA']
          change E₀ ((Sec4.thetaQuotMulAut Y (Sec4.compAction Y ⟨d, hdN⟩))
            (E₀.symm (E₀ y))) = _
          rw [MulEquiv.symm_apply_apply]
          rfl
        exact h1.symm)
    apply hXb1
    rw [eq_bot_iff]
    intro y hy
    have : E₀.toMonoidHom y ∈ Xb.map E₀.toMonoidHom := ⟨y, hy, rfl⟩
    rw [hX', Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact E₀.injective (by simpa using this)
  obtain ⟨φ, l, m', hlm, hφ⟩ := exists_suConj_diagonal hodd hU w hw3cen hw3
  set A' : unitaryIsom3 hU := φ * Aw * φ⁻¹ with hA'def
  have hA' : ((A' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ![l, l, m'] := by
    rw [← hφ]
    rfl
  set e' : Y ⧸ aschbacherSolvableCore 3 Y ≃* unitaryPSU hU 3 := E₀.trans (psuConj hU φ) with he'
  have hdA'' : inducedAutHom Y e' ⟨d, hdN⟩ = psuConj hU A' := by
    have h1 := KFacts.inducedAutHom_eq_conj Y E₀ e' ⟨d, hdN⟩
    have h2 : E₀.symm.trans e' = psuConj hU φ := by
      ext z
      simp [he']
    rw [h1, h2, hdA', hA'def, map_mul, map_mul, map_inv]
  have hd3' : ∃ j : ℕ, d ^ 3 ^ j = 1 := ⟨1, by rw [pow_one]; exact hd3⟩
  obtain ⟨⟨κ⟩, -⟩ := KFacts.imageModTheta_mulEquiv_projSL_of_psu3 hU (by omega) e' hdN hd3' hlm
    hA' hdA''
  obtain ⟨hAc, hA3⟩ := Hering88C.pair_commute_pow_three h
  have hxA : x ∈ A := by
    rcases hx with rfl | rfl
    · exact h.mem_A
    · exact (Item87Proof.isGammaIndex_cases h.isGammaIndex).1
  exact ⟨d, hdcl, hdx, Hering88C.good88_of_l2 h47 hodd hxY (hA3 x hxA) (hAc d hdA x hxA)
    (Or.inr (Or.inr (Or.inl ⟨e₁⟩))) κ⟩

end Hering88D

end CFSG.RankThree.PartTwo.Sec8
