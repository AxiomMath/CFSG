module

public import CFSG.LocalAnalysis.StandardType.GGKGTag
public import CFSG.LocalAnalysis.StandardType.GGKGOrd
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynClassical

public section

namespace CFSG.StandardType.KG

open CFSG.Open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.Y10GField CFSG.LocalAnalysis.GLTheoremA.Y10F
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)

private def kgs_Fsp (N n : ℕ) : ℕ :=
  2 ^ (n * N ^ 2) * ∏ i ∈ Finset.Icc 1 N, (2 ^ (2 * n * i) - 1)

private theorem kgs_Fsp_pos {N n : ℕ} (hn : 1 ≤ n) : 0 < kgs_Fsp N n := by
  rw [kgs_Fsp]
  refine Nat.mul_pos (pow_pos (by norm_num) _) ?_
  refine Finset.prod_pos ?_
  intro i hi
  have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
  have hne : 2 * n * i ≠ 0 :=
    Nat.mul_ne_zero (Nat.mul_ne_zero (by norm_num) (by omega)) (by omega)
  exact Nat.sub_pos_of_lt (Nat.one_lt_pow hne (by norm_num))

private theorem kgs_Fsp_succ {N n : ℕ} (hn : 1 ≤ n) :
    kgs_Fsp N n < kgs_Fsp (N + 1) n := by
  rw [kgs_Fsp, kgs_Fsp, Finset.prod_Icc_succ_top (show 1 ≤ N + 1 by omega)]
  have hPpos : 0 < ∏ i ∈ Finset.Icc 1 N, (2 ^ (2 * n * i) - 1) := by
    refine Finset.prod_pos ?_
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have hne : 2 * n * i ≠ 0 :=
      Nat.mul_ne_zero (Nat.mul_ne_zero (by norm_num) (by omega)) (by omega)
    exact Nat.sub_pos_of_lt (Nat.one_lt_pow hne (by norm_num))
  have hApos : 0 < 2 ^ (n * N ^ 2) := pow_pos (by norm_num) _
  have hC2 : 2 ≤ 2 ^ (n * (2 * N + 1)) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n * (2 * N + 1)) :=
        Nat.pow_le_pow_right (by norm_num) (by nlinarith [hn, Nat.zero_le N])
  have hQ2 : 2 ≤ 2 ^ (2 * n * (N + 1)) - 1 := by
    have h4 : 4 ≤ 2 ^ (2 * n * (N + 1)) := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * n * (N + 1)) :=
          Nat.pow_le_pow_right (by norm_num) (by nlinarith [hn, Nat.zero_le N])
    omega
  have hlt : 1 < 2 ^ (n * (2 * N + 1)) * (2 ^ (2 * n * (N + 1)) - 1) := by
    nlinarith
  calc 2 ^ (n * N ^ 2) * ∏ i ∈ Finset.Icc 1 N, (2 ^ (2 * n * i) - 1)
      < 2 ^ (n * N ^ 2) * (∏ i ∈ Finset.Icc 1 N, (2 ^ (2 * n * i) - 1)) *
          (2 ^ (n * (2 * N + 1)) * (2 ^ (2 * n * (N + 1)) - 1)) := by
        rw [Nat.lt_mul_iff_one_lt_right (Nat.mul_pos hApos hPpos)]
        exact hlt
    _ = 2 ^ (n * (N + 1) ^ 2) *
          ((∏ i ∈ Finset.Icc 1 N, (2 ^ (2 * n * i) - 1)) *
            (2 ^ (2 * n * (N + 1)) - 1)) := by
        rw [show n * (N + 1) ^ 2 = n * N ^ 2 + n * (2 * N + 1) by ring, pow_add]
        ring

private theorem kgs_Fsp_strictMono {n : ℕ} (hn : 1 ≤ n) :
    StrictMono (fun N => kgs_Fsp N n) :=
  strictMono_nat_of_lt_succ fun N => kgs_Fsp_succ (N := N) hn

private theorem kgs_ggHasLabel_of_mulEquiv {lab : LargeEvenLabel} {R R' : Type}
    [Group R] [Group R'] (e : R ≃* R') (h : GGHasLabel lab R) : GGHasLabel lab R' :=
  CFSG.StandardType.largeEvenRawDatum_mono (fun _ _ _ _ ⟨f⟩ => ⟨e.symm.trans f⟩) h

private theorem kgs_b2der_eq {lab : LargeEvenLabel} (hl : LargeEvenInLambda2 lab)
    (hb : lab.tag = .B2der) : lab = ⟨.B2der, 0, 1⟩ := by
  obtain ⟨t, r, n⟩ := lab
  dsimp only at hb
  subst hb
  simp only [LargeEvenInLambda2] at hl
  obtain ⟨-, hr, hn⟩ := hl
  subst hr hn
  rfl

theorem kgSymp_holds :
    KGSimpleOn FamSymp := by
  intro p hp hp2 S _ _ lab α K hF hlab hcen hin hαp hα1 hK k f hk hlabK
  have hS : HasLabel S (fun l : GLALabel => l = lab) :=
    CFSG.StandardType.Canonical.largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hin
  have hSgg : GGHasLabel lab (S ⧸ Subgroup.center S) :=
    (CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.ggHasLabel_of_hasLabel hS).2.2
  have hfix_eq : ggFixSub α = fixSubgroup α := Subgroup.ext fun _ => Iff.rfl
  have hKfix : CFSG.Open.IsComponentOf K (fixSubgroup α) := by
    rw [hfix_eq] at hK
    exact CFSG.Assembly.isComponentOf_iff_open.mp hK
  by_cases ht : lab.tag = .B ∨ lab.tag = .C
  ·
    obtain ⟨F, hFfield, hFfin, r, hr, hn, hcard, h2, e, A, hαA⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.I141F.Cls.compType_symp_data hcen ht hin
    letI := hFfield
    letI := hFfin
    obtain ⟨x, hx⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnSympRed.exists_conjAut_eq_conj h2 A
    have hMEq : MulAut.congr e α = MulAut.conj (proj r F x) := by
      rw [← hx]
      ext z
      have h1 := hαA (e.symm z)
      rw [MulEquiv.apply_symm_apply] at h1
      exact h1
    have hZ : Subgroup.center (StatedProj (StatedSp r F)) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have hz' : e.symm z ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff] at hz ⊢
        intro g
        apply e.injective
        simp only [map_mul, MulEquiv.apply_symm_apply]
        exact hz (e g)
      rw [hcen, Subgroup.mem_bot] at hz'
      rw [Subgroup.mem_bot]
      simpa using congrArg e hz'
    have hpow : MulAut.conj (proj r F x) ^ p = 1 := by
      rw [← hMEq, ← map_pow, hαp, map_one]
    have hxp : x ^ p = 1 :=
      CFSG.LocalAnalysis.GLTheoremA.Y10GInnSympRed.pow_eq_one_of_conj_pow_eq_one h2 hZ hpow
    have hK' := CFSG.LocalAnalysis.GLTheoremA.CanonTriL.isComponentOf_transport e α hKfix
    rw [hMEq] at hK'
    let eqJ : ↥K ≃* ↥(K.map e.toMonoidHom) :=
      K.equivMapOfInjective e.toMonoidHom e.injective
    let eQ : ↥K ⧸ Subgroup.center ↥K ≃*
        ↥(K.map e.toMonoidHom) ⧸ Subgroup.center ↥(K.map e.toMonoidHom) :=
      QuotientGroup.congr _ _ eqJ (Subgroup.map_center_eq eqJ)
    have hlabK' : GGHasLabel ⟨.C, k, f⟩
        (↥(K.map e.toMonoidHom) ⧸ Subgroup.center ↥(K.map e.toMonoidHom)) :=
      kgs_ggHasLabel_of_mulEquiv eQ hlabK
    obtain ⟨-, hcomp⟩ :=
      CFSG.HardMathSupport.Solomon.Coordinator.LieComp.lieCompsCore_conj_sp_card (a6 := False)
        CFSG.HardMathSupport.Solomon.Coordinator.LieComp.slFactorFacts_holds
        CFSG.HardMathSupport.Solomon.Coordinator.LieComp.suFactorFacts_holds
        CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFactorFacts_holds
        CFSG.HardMathSupport.Solomon.Coordinator.LieComp.spFourTwoFacts_holds
        (fun h => h.elim) (fun h => h.elim) (fun h => h.elim)
        hp hp2 Nat.prime_two hn hcard (by omega) hp2 (fun h => h.elim) x hxp
    obtain ⟨X, inst, hXfin, ⟨hXLie, -⟩, hfac, fX, hfX, hker⟩ := hcomp _ hK'
    letI := inst
    obtain ⟨eJ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.center_quot_equiv_of_surjective
      hXLie.perfect fX hfX hker
    unfold CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SpFactorOver at hfac
    rcases hfac with hSL | hSU | hSp | hSp42
    · rw [hcard] at hSL
      obtain ⟨b, kk, E, _, _, hb, hE, -, hφ⟩ :=
        CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.linCase_of_factor eJ hSL
      exact (kg_false_of_quot_sl hK'.2.2 hb hE hφ hk hlabK').elim
    · rw [hcard] at hSU
      obtain ⟨b, kk, E, _, _, τ, hτ, hb, hτk, hE, -, hφ⟩ :=
        CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.uniCase_of_factor eJ hSU
      exact (kg_false_of_quot_su hK'.2.2 τ hτ hb hτk hE hφ hk hlabK').elim
    ·
      obtain ⟨-, -, s, hs2, hne, ⟨eX⟩⟩ := hSp
      have hne' : ¬(s = 2 ∧ Nat.card F = 2) := fun h => hne (by rw [h.1, h.2])
      have hchar : CharP F 2 := CFSG.RankThree.PartOne.charP_two_of_card_eq_pow hcard
      obtain ⟨eXZ⟩ := CFSG.LocalAnalysis.GLTheoremA.Y10GCenterQuot.nonempty_centerQuot_sp
        (s := s) hs2 hne' hchar eX
      obtain ⟨-, hnf⟩ := kg_sp_of_quot_sp hs2 hcard hne' (eJ.trans eXZ) hk hlabK'
      have hcardK : Nat.card (K ⧸ Subgroup.center K) = kgs_Fsp k f :=
        kg_card_BC (kg_inLambda2_C hk hlabK) (Or.inr rfl) hlabK
      have hcardS_eq : Nat.card S = Nat.card (S ⧸ Subgroup.center S) := by
        rw [hcen]
        exact (Nat.card_congr (QuotientGroup.quotientBot (G := S)).toEquiv).symm
      have hcardS : Nat.card S = kgs_Fsp lab.rank lab.n := by
        rw [hcardS_eq]
        exact kg_card_BC hlab ht hSgg
      have hdiv1 : Nat.card (K ⧸ Subgroup.center K) ∣ Nat.card K :=
        Subgroup.index_dvd_card (Subgroup.center K)
      have hdiv2 : Nat.card K ∣ Nat.card S := Subgroup.card_subgroup_dvd_card K
      have hSpos : 0 < Nat.card S := by
        rw [hcardS]
        exact kgs_Fsp_pos hlab.1
      have hle : kgs_Fsp k f ≤ kgs_Fsp lab.rank lab.n := by
        rw [← hcardK, ← hcardS]
        exact Nat.le_of_dvd hSpos (hdiv1.trans hdiv2)
      have hkN : k ≤ lab.rank := by
        by_contra hcon
        have hlt : lab.rank < k := Nat.lt_of_not_le hcon
        have hstrict := (kgs_Fsp_strictMono hlab.1) hlt
        rw [← hnf] at hle
        exact absurd hstrict (not_lt.mpr hle)
      have hklt : k < lab.rank := by
        rcases lt_or_ge k lab.rank with h | h
        · exact h
        · exfalso
          have hkE : k = lab.rank := le_antisymm hkN h
          have hcardKQ : Nat.card (K ⧸ Subgroup.center K) = Nat.card S := by
            simp only [hcardK, hcardS, hkE, hnf]
          have hKpos : 0 < Nat.card K := Nat.card_pos
          have hcardK_eq : Nat.card K = Nat.card S := by
            refine le_antisymm ?_ ?_
            · exact Nat.le_of_dvd hSpos hdiv2
            · rw [← hcardKQ]
              exact Nat.le_of_dvd hKpos hdiv1
          have hKtop : K = ⊤ := (Subgroup.card_eq_iff_eq_top K).mp hcardK_eq
          have hfix_top : fixSubgroup α = ⊤ := by
            have hle' : K ≤ fixSubgroup α := hKfix.1
            rw [hKtop] at hle'
            exact top_le_iff.mp hle'
          have hα_eq_one : α = 1 := by
            ext y
            have hy : y ∈ fixSubgroup α := by
              rw [hfix_top]
              exact Subgroup.mem_top y
            have hy' : α y = y := mem_fixSubgroup.mp hy
            simpa using hy'
          exact absurd hα_eq_one hα1
      exact Or.inl ⟨ht, hklt, hnf⟩
    ·
      obtain ⟨-, -, hK2, ⟨eX⟩⟩ := hSp42
      have h360 : Nat.card (X ⧸ Subgroup.center X) = 360 :=
        CFSG.LocalAnalysis.GLTheoremA.I141F.Cls.card_quot_center_eq_360_of_sp42 hK2 eX.symm
      have h7X : 7 ∣ Nat.card (X ⧸ Subgroup.center X) :=
        kg_seven_dvd_card_C hk (kgs_ggHasLabel_of_mulEquiv eJ hlabK')
      have h7360 : 7 ∣ 360 := by
        rw [← h360]
        exact h7X
      obtain ⟨c, hc⟩ := h7360
      omega
  ·
    exfalso
    have hB2 : lab.tag = .B2der := by
      rcases hF with h | h | h
      · exact absurd (Or.inl h) ht
      · exact absurd (Or.inr h) ht
      · exact h
    have hlab_eq : lab = ⟨.B2der, 0, 1⟩ := kgs_b2der_eq hlab hB2
    rw [hlab_eq] at hS
    have hM : MarkedModel ⟨.B2der, 0, 1⟩ (S ⧸ Subgroup.center S) :=
      CFSG.LocalAnalysis.GLTheoremA.CanonSubcomp.markedModel_of_hasLabel hS
    have hcardQ : Nat.card (S ⧸ Subgroup.center S) = 360 :=
      CFSG.LocalAnalysis.GLTheoremA.card_of_B2der hM
    have hcardS : Nat.card S = 360 := by
      rw [hcen] at hcardQ
      rwa [Nat.card_congr (QuotientGroup.quotientBot (G := S)).toEquiv] at hcardQ
    have h7K : 7 ∣ Nat.card (K ⧸ Subgroup.center K) := kg_seven_dvd_card_C hk hlabK
    have hdiv : Nat.card (K ⧸ Subgroup.center K) ∣ Nat.card S :=
      (Subgroup.index_dvd_card (Subgroup.center K)).trans
        (Subgroup.card_subgroup_dvd_card K)
    have h7360 : 7 ∣ 360 := by
      rw [← hcardS]
      exact h7K.trans hdiv
    obtain ⟨c, hc⟩ := h7360
    omega

end CFSG.StandardType.KG

end
