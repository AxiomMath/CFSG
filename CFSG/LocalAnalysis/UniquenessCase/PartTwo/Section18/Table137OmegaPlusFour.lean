module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenFourteenK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.Table137Opp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Stab
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RModel
public import CFSG.Quasithin.Background.P3OrthoOm4
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95DTor
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214Rk
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQSL2
public import CFSG.GroupTheory.PElementSubgroup
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.LargeReeInvolutionTwoCentralizers
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafOddB
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOAut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOEightSwap
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOKlein
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOPlusLevi
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.RankThree.GF2n.Stroth80.FrobClause
public import CFSG.RankThree.GF2n.Stroth80.Sec12Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec310Nt
public import CFSG.RankThree.GF2n.Stroth80.Sec310Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec4Rt
public import CFSG.RankThree.GF2n.Stroth80.Sec4Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec5Main
public import CFSG.RankThree.GF2n.Stroth80.Sec6Stmt
public import CFSG.RankThree.GF2n.SupIndepDecomp
public import CFSG.RankThree.GF2n.Tim79CentC
public import CFSG.RankThree.GF2n.Tim79CentL
public import CFSG.RankThree.GF2n.Tim79Mod
public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearBridge
public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515S17
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsQuot
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsS17
public import CFSG.RankThree.PartTwo.Sec15.Item158Res2ProofInner
public import CFSG.RankThree.PartTwo.Sec15.Item15Res2ProofHJ
public import CFSG.RankThree.PartTwo.Sec15.Item15Res4ProofDefs
public import CFSG.RankThree.PartTwo.Sec17.Item175Proof
public import CFSG.RankThree.PartTwo.Sec17.Item17ParaHJ
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement Matrix

open CFSG.LocalAnalysis.UniquenessCase.PartTwo (OmegaModel OmI ptCent)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.OmegaModel (toMat ofMat toMat_ofMat ofMat_toMat)
open scoped MatrixGroups

theorem k_Table13_7_Omega4Plus_holds :
    ∀ {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (p n : ℕ),
      2 ≤ n → IsOmegaPlus ↥H 4 n → p.Prime → (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] →
        ∀ (F : Type) [Field F] [Finite F], Nat.card F = 2 ^ n →
          ∀ (ε : ↥H ≃* ↥(StatedOmega (StatedQuadPlus 2 F)))
            (ψ : W ≃* Multiplicative (Fin 2 ⊕ Fin 2 → F)),
            NatCoordsOmegaPlus H F ε ψ → ∀ v : W, v ≠ 1 →
              (StatedQuadPlus 2 F (Multiplicative.toAdd (ψ v)) = 0 →
                  Opp p (centVec H v) = ⊥) ∧
                (StatedQuadPlus 2 F (Multiplicative.toAdd (ψ v)) ≠ 0 →
                  IsL2 (Bar2 (Opp p (centVec H v))) n) := by
  classical
  intro W _ _ H p n hn _ hp hcong F _ _ hF ε ψ hψ v hv
  have : CharP F 2 := CFSG.ABGLocalTools.SL2Facts.charP_of_card_eq_prime_pow Nat.prime_two hF
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  let S : OmegaModel W := { K := F, four_le := h4, e := ψ }
  have hl : ∀ l : ↥H, (l : MulAut W) = S.actHom (ε l : GL (Fin 2 ⊕ Fin 2) F) := by
    intro l
    ext w
    apply S.vec_injective
    refine Eq.trans ?_ (S.actHom_vec _ w).symm
    show Multiplicative.toAdd (ψ ((l : MulAut W) w)) = _
    rw [hψ l w, toAdd_ofAdd]
    rfl
  have hHω : H = S.omega := by
    ext x
    constructor
    · intro hx
      exact ⟨(ε ⟨x, hx⟩ : GL (Fin 2 ⊕ Fin 2) F), (ε ⟨x, hx⟩).2, (hl ⟨x, hx⟩).symm⟩
    · rintro ⟨γ, hγ, rfl⟩
      have h := hl (ε.symm ⟨γ, hγ⟩)
      rw [MulEquiv.apply_symm_apply] at h
      exact h ▸ (ε.symm ⟨γ, hγ⟩).2
  have hcard : Nat.card S.omega = (Nat.card S.K * (Nat.card S.K ^ 2 - 1)) ^ 2 := by
    obtain ⟨e⟩ := CFSG.Quasithin.G11.P3Ortho.Om4.iso_of_card F h4
    rw [← hHω, Nat.card_congr (ε.toEquiv.trans e.toEquiv), Nat.card_prod,
      CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two F, ← sq]
  have hH0 : H = S.omega0 := hHω.trans (S.omega_eq_omega0_of_card hcard)
  have hC : centVec H v = ptCent S.omega0 v := by
    ext x
    rw [centVec.mem_centVec, ptCent, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, hH0]
    rfl
  have hpq : p ∣ Nat.card F + 1 := by
    rw [hF]
    exact CFSG.LocalAnalysis.UniquenessCase.UC22.P2214R.dvd_of_cong hcong
  constructor
  · intro hsing
    set w : Fin 2 ⊕ Fin 2 → F := Multiplicative.toAdd (ψ v) with hwdef
    have hiff : ∀ l : ↥H, (l : MulAut W) v = v ↔
        ((ε l : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w = w := by
      intro l
      rw [← ψ.injective.eq_iff, hψ l v]
      constructor
      · intro h
        exact congrArg Multiplicative.toAdd h
      · intro h
        rw [h]
        rfl
    have hw0 : w ≠ 0 := by
      intro h0
      apply hv
      apply ψ.injective
      rw [map_one]
      exact congrArg Multiplicative.ofAdd h0
    have hodd : Odd (Nat.card F + 1) := by
      rw [hF]
      exact Even.add_one (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    have hpodd : Odd p := Odd.of_dvd_nat hodd hpq
    have hpq' : ¬ p ∣ Nat.card F - 1 := by
      intro h
      have h1 : 1 ≤ Nat.card F := Nat.card_pos
      have h2 : p ∣ (Nat.card F + 1) - (Nat.card F - 1) := Nat.dvd_sub hpq h
      rw [show Nat.card F + 1 - (Nat.card F - 1) = 2 by omega] at h2
      have := Nat.le_of_dvd (by norm_num) h2
      rcases (Nat.le_succ_iff.mp this) with h3 | h3
      · have := hp.two_le
        omega
      · rw [h3] at hpodd
        exact absurd hpodd (by decide)
    refine opp_centVec_eq_bot_of_vecStab ε v w hiff (fun g k hk => ?_)
    haveI := Fintype.ofFinite F
    have hroots : ∀ a : F, a ^ (p ^ k) = 1 → a = 1 := by
      intro a ha
      have ha0 : a ≠ 0 := by
        rintro rfl
        rw [zero_pow (pow_ne_zero k hp.ne_zero)] at ha
        exact zero_ne_one ha
      have hq : a ^ (Fintype.card F - 1) = 1 := FiniteField.pow_card_sub_one_eq_one a ha0
      have hcop : (p ^ k).Coprime (Nat.card F - 1) :=
        Nat.Coprime.pow_left k ((hp.coprime_iff_not_dvd).mpr hpq')
      have h := pow_gcd_eq_one.mpr ⟨ha, hq⟩
      rwa [← Nat.card_eq_fintype_card, hcop.gcd_eq_one, pow_one] at h
    have hgpow : ((g : ↥(StatedOmega (StatedQuadPlus 2 F))) : GL (Fin 2 ⊕ Fin 2) F) ^ (p ^ k)
        = 1 := by
      have h1 : g ^ (p ^ k) = 1 := hk ▸ pow_orderOf_eq_one g
      have h2 := congrArg (fun z : ↥(KTabC.vecStab (StatedOmega (StatedQuadPlus 2 F)).subtype w) =>
        ((z : ↥(StatedOmega (StatedQuadPlus 2 F))) : GL (Fin 2 ⊕ Fin 2) F)) h1
      simpa using h2
    have hg1 := CFSG.RankThree.GF2n.Stroth80.HS9.eq_one_of_fix_singular95 h4
      (g : ↥(StatedOmega (StatedQuadPlus 2 F))).2 hpodd.pow hgpow hroots hw0 hsing
      (mem_vecStab_subtype.mp g.2)
    exact Subtype.ext (Subtype.ext hg1)
  · intro hns
    obtain ⟨φ, hφinj, hφr⟩ := S.exists_hom_ptCent_omega0 (w := v) hns
    let eC : ↥(centVec H v) ≃* SL(2, F) :=
      (MulEquiv.subgroupCongr (hC.trans hφr.symm)).trans (MonoidHom.ofInjective hφinj).symm
    obtain ⟨hSq, hS2, x, hx, hxp⟩ := sl2_inputs h4 hp hpq
    obtain ⟨e⟩ := nonempty_bar2_opp_equiv_of_surjective hp (centVec H v) eC.toMonoidHom
      eC.surjective (IsPGroup.ker_isPGroup_of_injective eC.injective) hSq hS2 hx hxp
    haveI := Fintype.ofFinite F
    exact CFSG.CGT.PushingUpLit.CGT6K1.lieModel_PSL_two_of_mulEquiv_SL_two hn
      (by rw [← Nat.card_eq_fintype_card, hF]) e

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
