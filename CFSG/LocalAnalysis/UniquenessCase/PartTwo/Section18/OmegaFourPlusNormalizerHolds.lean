module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSeventeenK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165OrdB
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcClOrth
public import CFSG.RankThree.PartOne.KFR4.At
public import CFSG.GH74.GLS.Balance.Bender.Aux2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourteenK
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaFourPlusSmallCommHolds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.OmegaSixMinusSmallCommHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.OmegaModel
open scoped Pointwise commutatorElement

theorem k_OmegaFourPlusNormalizer_pRank_holds :
    K_OmegaFourPlusNormalizer_pRank := by
  intro W _ _ H Y p n hn2 _hO hNat hp hp2 hcong hHY hYN hOpY
  classical
  obtain ⟨S, hSω, hSK⟩ := exists_omegaModel_of_natOmegaPlus (W := W) (H := H) hn2 hNat
  have hHY' : S.omega ≤ Y := by
    simpa [← hSω] using hHY
  have hYN' : Y ≤ omegaNorm S := by
    simpa [omegaNorm, ← hSω] using hYN
  have hq : Nat.card S.K = 2 ^ n := hSK
  have hq1 : 1 ≤ Nat.card S.K := Nat.one_le_iff_ne_zero.mpr (Nat.card_pos.ne')
  have hp_dvd_succ : p ∣ Nat.card S.K + 1 := by
    have h1 : (p : ℤ) ∣ (2 : ℤ) ^ n - -1 := Int.ModEq.dvd hcong.symm
    have h2 : (p : ℤ) ∣ ((Nat.card S.K + 1 : ℕ) : ℤ) := by
      rw [hSK]
      push_cast
      simpa using h1
    exact Int.natCast_dvd_natCast.1 h2
  have hp_not_dvd_pred : ¬ p ∣ Nat.card S.K - 1 := by
    intro h
    have h2 : (p : ℤ) ∣ ((Nat.card S.K + 1 : ℕ) : ℤ) - ((Nat.card S.K - 1 : ℕ) : ℤ) :=
      dvd_sub (by exact_mod_cast hp_dvd_succ) (by exact_mod_cast h)
    have h3 : ((Nat.card S.K + 1 : ℕ) : ℤ) - ((Nat.card S.K - 1 : ℕ) : ℤ) = 2 := by
      push_cast [hq1]
      ring
    have h4 : (p : ℤ) ∣ 2 := by rwa [h3] at h2
    have h5 : p ∣ 2 := Int.natCast_dvd_natCast.1 h4
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h5)
  have hcop_p : Nat.Coprime p (Nat.card S.K - 1) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr hp_not_dvd_pred
  have key : ∀ E : Subgroup (MulAut W), E ≤ Y → IsElemAbelian p E → E ≤ S.omega := by
    intro E hEY hE
    have hEN : E ≤ omegaNorm S := hEY.trans hYN'
    have hElin : E ≤ linSub S := by
      obtain ⟨θ, hθspec, hθker⟩ := exists_twistHom S
      let ψ : ↥Y →* (S.K ≃+* S.K) := θ.comp (Subgroup.inclusion hYN')
      have hfact2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hcyc : IsCyclic (S.K ≃+* S.K) :=
        @CFSG.AGLEmbedding.UnitaryModel.isCyclic_ringEquiv S.K _ _ 2 hfact2 S.charTwo
      have hcommRing : IsMulCommutative (S.K ≃+* S.K) :=
        @IsCyclic.isMulCommutative (S.K ≃+* S.K) _ hcyc
      let P : Subgroup (S.K ≃+* S.K) :=
        { carrier := {a | Nat.Coprime (orderOf a) p}
          one_mem' := by simp
          mul_mem' := by
            intro a b ha hb
            have hcomm : Commute a b := hcommRing.is_comm.comm a b
            exact Nat.Coprime.coprime_dvd_left
              (hcomm.orderOf_mul_dvd_lcm.trans (Nat.lcm_dvd_mul _ _))
              (Nat.coprime_mul_iff_left.mpr ⟨ha, hb⟩)
          inv_mem' := by
            intro a ha
            simpa [orderOf_inv] using ha }
      have hYres : CFSG.GH74.GLS.oResidual p ↥Y = ⊤ :=
        (CFSG.GH74.GLS.Balance.BenderExt.oResidual_eq_top_iff (p := p) Y).mpr (by
          change (CFSG.GH74.GLS.oResidual p ↥Y).map Y.subtype = Y
          rw [← UC6.opRes_eq_map_oResidual_uc6 hp Y, hOpY])
      have hco : CFSG.GH74.GLS.oResidual p ↥Y ≤ P.comap ψ := by
        rw [CFSG.GH74.GLS.oResidual, Subgroup.closure_le]
        intro x hx
        exact Nat.Coprime.coprime_dvd_left (orderOf_map_dvd ψ x) hx
      have hψrange : ψ.range ≤ P := by
        rw [hYres] at hco
        rintro a ⟨x, rfl⟩
        exact hco (Subgroup.mem_top x)
      intro e he
      have heY : e ∈ Y := hEY he
      have heN : e ∈ omegaNorm S := hYN' heY
      let x : ↥Y := ⟨e, heY⟩
      have hψP : ψ x ∈ P := hψrange ⟨x, rfl⟩
      have hψpow : ψ x ^ p = 1 := by
        have hxp : x ^ p = 1 := Subtype.ext (hE.2 e he)
        calc ψ x ^ p = ψ (x ^ p) := (map_pow ψ x p).symm
          _ = ψ 1 := by rw [hxp]
          _ = 1 := map_one ψ
      have hψdvd : orderOf (ψ x) ∣ p := orderOf_dvd_of_pow_eq_one hψpow
      have hψcop : Nat.Coprime (orderOf (ψ x)) p := hψP
      have hψord : orderOf (ψ x) = 1 := Nat.Coprime.eq_one_of_dvd hψcop hψdvd
      have hψ1 : ψ x = 1 := orderOf_eq_one_iff.mp hψord
      have hθ1 : θ ⟨e, heN⟩ = 1 := by
        have hx : (Subgroup.inclusion hYN' x : ↥(omegaNorm S)) = ⟨e, heN⟩ := rfl
        rw [← hx]
        exact hψ1
      exact (hθker ⟨e, heN⟩).mp hθ1
    have hENlin : E ≤ omegaNorm S ⊓ linSub S := le_inf hEN hElin
    have hEZ : E ≤ scalarSub S ⊔ isoSub S :=
      hENlin.trans (omegaNorm_inf_linSub_le_sup S)
    have hEO : E ≤ isoSub S := by
      intro e he
      obtain ⟨z, hz, h, hh, rfl⟩ := (mem_scalarSub_sup_isoSub_iff S).mp (hEZ he)
      have hhlin : h ∈ linSub S := ((mem_isoSub_iff S).mp hh).1
      have hcomm : Commute z h := scalarSub_commute S hz hhlin
      have h1 : z ^ p * h ^ p = 1 := by
        rw [← hcomm.mul_pow]
        exact hE.2 (z * h) he
      have h2 : z ^ p = (h ^ p)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have hzp_bot : z ^ p ∈ (⊥ : Subgroup (MulAut W)) := by
        rw [← scalarSub_inf_isoSub S]
        exact ⟨Subgroup.pow_mem _ hz p, h2 ▸ Subgroup.inv_mem _ (Subgroup.pow_mem _ hh p)⟩
      have hzp1 : z ^ p = 1 := Subgroup.mem_bot.mp hzp_bot
      obtain ⟨c, hc⟩ := hz
      have hc1 : c ^ (Nat.card S.K - 1) = 1 := by
        rw [← Nat.card_units S.K]
        exact pow_card_eq_one'
      have hzq : z ^ (Nat.card S.K - 1) = 1 := by
        rw [← hc, ← map_pow, hc1, map_one]
      have hzp_dvd : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzp1
      have hzq_dvd : orderOf z ∣ Nat.card S.K - 1 := orderOf_dvd_of_pow_eq_one hzq
      have hcop_ord : Nat.Coprime (orderOf z) (Nat.card S.K - 1) :=
        Nat.Coprime.coprime_dvd_left hzp_dvd hcop_p
      have hzord : orderOf z = 1 := Nat.Coprime.eq_one_of_dvd hcop_ord hzq_dvd
      have hz1 : z = 1 := orderOf_eq_one_iff.mp hzord
      rw [hz1, one_mul]
      exact hh
    have hcardSL : Nat.card (Matrix.SpecialLinearGroup (Fin 2) S.K) =
        Nat.card S.K * (Nat.card S.K ^ 2 - 1) := by
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (K := S.K) (n := 2)
        (by norm_num)]
      norm_num
    have hcardOmega : Nat.card S.omega = Nat.card S.K ^ 2 * (Nat.card S.K ^ 2 - 1) ^ 2 := by
      have hmap : Nat.card S.omega = Nat.card (StatedOmega (StatedQuadPlus 2 S.K)) := by
        change Nat.card ((StatedOmega (StatedQuadPlus 2 S.K)).map S.actHom) =
          Nat.card (StatedOmega (StatedQuadPlus 2 S.K))
        exact Subgroup.card_map_of_injective S.actHom_injective
      rw [hmap]
      obtain ⟨eSL⟩ := uc22p22d_omegaPlus4_equiv (F := S.K) S.four_le
      calc Nat.card (StatedOmega (StatedQuadPlus 2 S.K))
          = Nat.card (Matrix.SpecialLinearGroup (Fin 2) S.K ×
              Matrix.SpecialLinearGroup (Fin 2) S.K) := (Nat.card_congr eSL.toEquiv).symm
        _ = Nat.card S.K ^ 2 * (Nat.card S.K ^ 2 - 1) ^ 2 := by
            rw [Nat.card_prod, hcardSL]
            ring
    have hcardIso : Nat.card (isoSub S) =
        2 * (Nat.card S.K ^ 2 * (Nat.card S.K ^ 2 - 1) ^ 2) := by
      have hmap : Nat.card (isoSub S) =
          Nat.card (CFSG.MatrixModel.isometryCore (StatedQuadPlus 2 S.K)) := by
        rw [isoSub]
        exact Subgroup.card_map_of_injective S.actHom_injective
      rw [hmap]
      have h := CFSG.LocalAnalysis.RankFourTheoremC.crossExcCl_card_isoPlus
        (K := S.K) 1
      rw [show (1 + 1 : ℕ) = 2 by norm_num] at h
      rw [h]
      norm_num
      ring
    have hωO : S.omega ≤ isoSub S := omega_le_isoSub S
    have hrel2 : (S.omega).relIndex (isoSub S) = 2 := by
      have hmul := Subgroup.relIndex_mul_card (H := S.omega) (K := isoSub S)
      rw [inf_of_le_left hωO] at hmul
      rw [hcardOmega, hcardIso] at hmul
      have hpos : 0 < Nat.card S.K ^ 2 * (Nat.card S.K ^ 2 - 1) ^ 2 := by
        have h16 : 16 ≤ Nat.card S.K ^ 2 := by
          calc 16 = 4 ^ 2 := by norm_num
            _ ≤ Nat.card S.K ^ 2 := Nat.pow_le_pow_left S.four_le 2
        have h2 : 0 < Nat.card S.K ^ 2 - 1 := by omega
        exact mul_pos (Nat.pow_pos (by omega : 0 < Nat.card S.K)) (pow_pos h2 2)
      exact Nat.eq_of_mul_eq_mul_right hpos hmul
    have hPω : E ≤ S.omega := by
      have hP : IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE
      obtain ⟨k, hk⟩ := @IsPGroup.exists_card_eq p ↥E _ ⟨hp⟩ _ hP
      have hrle : (E ⊓ S.omega).relIndex E ≤ 2 := by
        have h1 : (E ⊓ S.omega).relIndex E ≤ (S.omega).relIndex E := by
          have := Subgroup.relIndex_inf_le (H := S.omega) (K := E) (L := E)
          simpa [inf_comm] using this
        have h2 : (S.omega).relIndex E ≤ (S.omega).relIndex (isoSub S) :=
          Subgroup.relIndex_le_of_le_right hEO (by rw [hrel2]; norm_num)
        exact h1.trans (by simpa [hrel2] using h2)
      have hrdvd : (E ⊓ S.omega).relIndex E ∣ p ^ k := by
        rw [← hk]
        exact Subgroup.relIndex_dvd_card (E ⊓ S.omega) E
      have hrpos : 0 < (E ⊓ S.omega).relIndex E := by
        rcases Nat.eq_zero_or_pos ((E ⊓ S.omega).relIndex E) with h0 | hpos
        · exfalso
          rw [h0] at hrdvd
          exact (Nat.pow_pos hp.pos).ne' (Nat.eq_zero_of_zero_dvd hrdvd)
        · exact hpos
      have hr12 : (E ⊓ S.omega).relIndex E = 1 ∨ (E ⊓ S.omega).relIndex E = 2 := by omega
      rcases hr12 with h1 | h2
      · have hle : E ≤ E ⊓ S.omega := Subgroup.relIndex_eq_one.mp h1
        exact hle.trans inf_le_right
      · exfalso
        have h2dvd : 2 ∣ p ^ k := by rwa [h2] at hrdvd
        have hcop : Nat.Coprime (p ^ k) 2 :=
          Nat.Coprime.pow_left k ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
        exact (by norm_num : (2 : ℕ) ≠ 1)
          (Nat.Coprime.eq_one_of_dvd hcop.symm h2dvd)
    exact hPω
  have hrankY : CFSG.Open.pRank p Y ≤ CFSG.Open.pRank p S.omega := by
    refine CFSG.SectionRank.pRank_le hp.one_lt (fun E hEY hE => ?_)
    have hEH : E ≤ S.omega := key E hEY hE
    obtain ⟨k, hk⟩ :=
      @IsPGroup.exists_card_eq p ↥E _ ⟨hp⟩ _ (CFSG.Open.IsElemAbelian.isPGroup hE)
    have hk_le : k ≤ CFSG.Open.pRank p S.omega :=
      CFSG.SectionRank.le_pRank hp.one_lt hEH hE hk
    rw [hk]
    exact Nat.pow_le_pow_right hp.pos hk_le
  have hrankOmega : CFSG.Open.pRank p S.omega ≤ 2 := by
    let eH : ↥(StatedOmega (StatedQuadPlus 2 S.K)) ≃* ↥S.omega :=
      Subgroup.equivMapOfInjective (StatedOmega (StatedQuadPlus 2 S.K)) S.actHom
        S.actHom_injective
    obtain ⟨eSL⟩ := uc22p22d_omegaPlus4_equiv (F := S.K) S.four_le
    let e : Matrix.SpecialLinearGroup (Fin 2) S.K × Matrix.SpecialLinearGroup (Fin 2) S.K ≃*
        ↥S.omega := eSL.trans eH
    have htrans : CFSG.Open.pRank p S.omega =
        CFSG.pRank p (Matrix.SpecialLinearGroup (Fin 2) S.K ×
          Matrix.SpecialLinearGroup (Fin 2) S.K) := by
      calc CFSG.Open.pRank p S.omega
          = CFSG.Open.pRank p (⊤ : Subgroup ↥S.omega) :=
              CFSG.SectionRank.pRank_eq_pRank_top_subgroup (S.omega)
        _ = CFSG.Open.pRank p (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) S.K ×
              Matrix.SpecialLinearGroup (Fin 2) S.K)) :=
              (CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e).symm
        _ = CFSG.pRank p (Matrix.SpecialLinearGroup (Fin 2) S.K ×
              Matrix.SpecialLinearGroup (Fin 2) S.K) :=
              (CFSG.SectionRank.pRank_eq_open_pRank_top p _).symm
    rw [htrans]
    have hprod : CFSG.pRank p (Matrix.SpecialLinearGroup (Fin 2) S.K ×
        Matrix.SpecialLinearGroup (Fin 2) S.K) =
        CFSG.pRank p (Matrix.SpecialLinearGroup (Fin 2) S.K) +
          CFSG.pRank p (Matrix.SpecialLinearGroup (Fin 2) S.K) :=
      CFSG.Quasithin.H13.NQBlock.pRank_prod_eq hp
    rw [hprod]
    have hSL : CFSG.pRank p (Matrix.SpecialLinearGroup (Fin 2) S.K) ≤ 1 :=
      CFSG.RankThree.PartOne.KFR4.pRank_le_one_of_equiv_sl2 hp hp2 (MulEquiv.refl _)
    omega
  exact hrankY.trans hrankOmega

section Certified

variable {G : Type} [Group G] [Finite G]


theorem eighteen_seventeen_holds (D : Data G)
    (V₀ V : Subgroup G) (p : ℕ) (L : Subgroup G) (h : Hyp18 D V₀ V p L)
    (h61 : UC6.R6_1 D) (hSg : UC6S846.SigmaStd D)
    (hIso : K_Omega6Minus_natIsoMod)
    (h638 : UC6.R6_38 D) (h1742 : S17.R17_42At D V₀ V) :
    R18_17At D V₀ V p L h :=
  eighteen_seventeen_of_K D V₀ V p L h h61 hSg (k_K_Omega6Minus_smallComm_holds_of hIso)
    k_K_Omega4Plus_smallComm_holds k_OmegaFourPlusNormalizer_pRank_holds h638 h1742

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
