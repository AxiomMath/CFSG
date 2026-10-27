module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Main
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BBarSevenSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsSevenSevenHolds
public import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.LocalAnalysis.SeitzReduction.RankOneLinearData
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiStart
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KMinDegLow.Rep
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.Structure
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rk
public import CFSG.Quasithin.Background.E3AParamCard

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.GH74.Uniqueness.Bender
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

theorem aCandidate_le_of_benderType {H : Type} [Group H]
    [Finite H] {n i e : ℕ} (hB : BenderType H n i e) (hi : i ≠ 3) {k : ℕ}
    (c : ACandidate H k) : k ≤ n := by
  classical
  letI := c.commGroup
  letI := c.finiteW
  haveI : Finite (MulAut c.W) :=
    Finite.of_injective (fun φ : MulAut c.W => (φ : c.W → c.W)) DFunLike.coe_injective
  haveI : Finite ↥c.Y := Subtype.finite
  haveI := hB.isSimple
  have hft : fstarTop H = ⊤ := by
    haveI := c.hLn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (fstarTop H) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ :=
        CFSG.LocalAnalysis.UniquenessCase.UC22.MinDegLow.nontrivial_of_isQuasisimple
          ((CFSG.Quasithin.A3.isQuasisimple_iff_open).1 c.hLq)
      apply hab
      have key : ∀ x : H, x ∈ fstarTop H → x = 1 := by
        intro x hx
        rw [h] at hx
        exact Subgroup.mem_bot.mp hx
      exact Subtype.ext ((key _ a.2).trans (key _ b.2).symm)
    · exact h
  let eTop : ↥(fstarTop H) ≃* H := (MulEquiv.subgroupCongr hft).trans (Subgroup.topEquiv (G := H))
  have hBtop : BenderType ↥(fstarTop H) n i e := hB.of_mulEquiv eTop.symm
  obtain ⟨Z₀, hZ₀, hZ₀c, ⟨e₀⟩⟩ := c.central_factor
  letI : Z₀.Normal := hZ₀
  have hZ₀bot : Z₀ = ⊥ := le_bot_iff.mp (hBtop.center_eq_bot ▸ hZ₀c)
  let eF : ↥(fstarTop H) ≃* ↥(fstarSubOf c.Y) :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ₀bot.symm)).trans
      e₀.symm
  have hBF : BenderType ↥(fstarSubOf c.Y) n i e := hBtop.of_mulEquiv eF
  have hFstar : fstarSubOf c.Y = genFittingFStar ↥c.Y := by
    rw [fstarSubOf, CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar,
      CFSG.subgroupOf_map_subtype_eq]
  have hcent : Subgroup.centralizer ((fstarSubOf c.Y : Subgroup ↥c.Y) : Set ↥c.Y) ≤
      fstarSubOf c.Y := by
    rw [hFstar]
    exact CFSG.Adapters.generalized_fitting_self_centralizing ↥c.Y
  letI : (fstarSubOf c.Y).Normal := c.hLgn
  let ρ : ↥c.Y →* MulAut ↥(fstarSubOf c.Y) := MulAut.conjNormal
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have hyc : y ∈ Subgroup.centralizer ((fstarSubOf c.Y : Subgroup ↥c.Y) : Set ↥c.Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have h1 := congrArg
        (fun σ : MulAut ↥(fstarSubOf c.Y) => ((σ ⟨f, hf⟩ : ↥(fstarSubOf c.Y)) : ↥c.Y)) hy
      simp only [ρ, MulAut.conjNormal_apply, MulAut.one_apply] at h1
      calc f * y = (y * f * y⁻¹) * y := by rw [h1]
        _ = y * f := by group
    have hyF : y ∈ fstarSubOf c.Y := hcent hyc
    have hz : (⟨y, hyF⟩ : ↥(fstarSubOf c.Y)) ∈ Subgroup.center ↥(fstarSubOf c.Y) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hyc g g.2
    rw [hBF.center_eq_bot, Subgroup.mem_bot] at hz
    exact congrArg Subtype.val hz
  rw [c.eq_n]
  refine CFSG.Quasithin.E3.aParam_le_of_card_le c.Y (fun A hAY hA2 => ?_)
  have hE := (hBF.card_le_of_sq_eq_one_aut ((A.subgroupOf c.Y).map ρ) (by
    rintro _ ⟨a, ha, rfl⟩
    have ha1 : a * a = 1 := by
      apply Subtype.ext
      have h2 := hA2 (a : MulAut c.W) ha
      simpa [sq] using h2
    rw [← map_mul, ha1, map_one])).2 hi
  have hcardE : Nat.card ((A.subgroupOf c.Y).map ρ) = Nat.card A := by
    rw [Subgroup.card_map_of_injective hρ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY).toEquiv
  omega

theorem bParam_le_of_benderType {W : Type} [CommGroup W]
    [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {Y L X : Subgroup (MulAut W)}
    (hL : IsComponentOf L Y) (hX : X = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom)
    {n i e : ℕ} (hB : BenderType ↥L n i e) (hi : i ≠ 3) : bParam X Y ≤ n := by
  refine CFSG.LocalAnalysis.UniquenessCase.PartTwo.bParam_le_of_isComponentOf hW
    Inputs1719.w4Lem7_7_holds (𝒦 := CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y)
    (fun K hK => (CFSG.LocalAnalysis.WeakClosure81.conjSet_facts hL rfl hK).1) ?_ ?_
  · have h := CFSG.LocalAnalysis.WeakClosure81.iSup_conjSet_eq_biSup_conj L Y
    rw [hX, ← h]
  · rintro K ⟨g, hg, rfl⟩ k ⟨c⟩
    exact aCandidate_le_of_benderType
      (hB.of_mulEquiv (L.equivMapOfInjective _ (MulAut.conj g).injective)) hi c

theorem dMinDeg_eq_six_of_isL2_three {L : Type} [Group L] (h : UC22.IsL2 L 3) :
    dMinDeg L = 6 := by
  obtain ⟨e⟩ := CFSG.SeitzReduction.RankOne.nonempty_mulEquiv_psl2_of_lieModel h
  have := CFSG.LocalAnalysis.WeakClosure81.dMinDeg_eq_of_mulEquiv_sl2 (n := 3) (by norm_num)
    (e.trans (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 3)))
  simpa using this

theorem twenty_le_dMinDeg_of_isSz_five {L : Type} [Group L]
    [Finite L] (h : UC22.IsSz L 5) : 20 ≤ dMinDeg L := by
  haveI hs : IsSimpleGroup L := UC22.uc22p22r_lieModel_isSimple_twistedB2 h
  have hcard : Nat.card L = CFSG.Open.ordSuzuki (2 ^ 5) :=
    CFSG.LocalAnalysis.EvenBN.GMSK.card_eq_ordSuzuki_of_lieModel_twistedB2 h
  have h41 : 41 ∣ Nat.card L := by
    rw [hcard]
    unfold CFSG.Open.ordSuzuki
    norm_num
  haveI : Fact (Nat.Prime 41) := ⟨by norm_num⟩
  obtain ⟨s, hs41⟩ := exists_prime_orderOf_dvd_card' (G := L) 41 h41
  refine CFSG.LocalAnalysis.UniquenessCase.UC22.MinDegLow.le_dMinDeg (fun d f hf => ?_)
  have hker : f.ker = ⊥ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top f.ker with hk | hk
    · exact hk
    · exact absurd (MonoidHom.ker_eq_top_iff.mp hk) hf
  have hinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).mp hker
  have hord : orderOf (f s) = 41 := by rw [orderOf_injective f hinj s, hs41]
  exact CFSG.LocalAnalysis.UniquenessCase.UC22.MinDegLow.le_of_orderOf_eq_ppd (k := 20)
    ⟨by norm_num, by norm_num, by intro j hj0 hj; interval_cases j <;> norm_num⟩ (by norm_num)
    (f s) hord

theorem exists_benderType {L : Type} [Group L] {n : ℕ}
    (hshape : (UC22.IsL2 L 3 ∧ n = 3) ∨ (UC22.IsSz L 5 ∧ n = 5)) :
    ∃ i e, BenderType L n i e ∧ i ≠ 3 := by
  rcases hshape with ⟨h3, rfl⟩ | ⟨h5, rfl⟩
  · obtain ⟨e⟩ := CFSG.SeitzReduction.RankOne.nonempty_mulEquiv_psl2_of_lieModel h3
    exact ⟨1, 1, BenderType.linear 3 (by norm_num) e, by norm_num⟩
  · obtain ⟨a, -, -, hb⟩ := CFSG.SeitzReduction.RankOne.exists_benderType_of_lieModel_twistedB2 h5
    exact ⟨2, 1, hb, by norm_num⟩

theorem case2_of_hyps {W : Type}
    [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {Y L X : Subgroup (MulAut W)}
    (hO2 : O2Trivial Y) (hB : IsBasicModule Y) (hL : IsComponentOf L Y)
    (hX : X = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom) (hfix : fixV X = ⊥) {n : ℕ}
    (hshape : (UC22.IsL2 ↥L 3 ∧ n = 3) ∨ (UC22.IsSz ↥L 5 ∧ n = 5))
    (hm : 3 < E3.mParam Y) (hle : E3.mParam Y ≤ bParam X Y + 2) :
    E3.mParam Y ≤ n + 2 ∧
      IsDirSumOver (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y)
        (fun X' => commV (autQuot X' (⊥ : Subgroup W))) ∧
      ∃ I ∈ irrSet L,
        (E3.mParam (autSub Y I) : ℚ) * ((rk ↥(commV L) : ℚ) / (rk ↥I : ℚ)) ≤
          E3.mParam Y := by
  obtain ⟨i, e, hBe, hi⟩ := exists_benderType hshape
  have hb : bParam X Y ≤ n := bParam_le_of_benderType hW hL hX hBe hi
  have hmn : E3.mParam Y ≤ n + 2 := by omega
  refine ⟨hmn, ?_⟩
  have hHX : (⨆ X' ∈ CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y, X') = X := by
    rw [CFSG.LocalAnalysis.WeakClosure81.iSup_conjSet_eq_biSup_conj, hX]
  have hfixH : fixV (⨆ X' ∈ CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y, X') = ⊥ := by
    rw [hHX]
    exact hfix
  rcases CFSG.LocalAnalysis.WeakClosure81.w4Lem12_8_holds W hW Y hO2 hB L hL _ rfl with
    h1 | ⟨hsum, I, hI, hIm⟩ | ⟨R, e', -, -, -, -, hRm, hRd⟩
  · exfalso
    rcases hshape with ⟨h3, rfl⟩ | ⟨h5, rfl⟩
    · rw [dMinDeg_eq_six_of_isL2_three h3] at h1
      omega
    · have := twenty_le_dMinDeg_of_isSz_five h5
      omega
  ·
    have key : ∀ N : Subgroup W, N = ⊥ →
        IsDirSumOver (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y)
          (fun X' => commV (autQuot X' N)) →
        (E3.mParam (autSub (autQuot Y N) (I.map (QuotientGroup.mk' N))) : ℚ) *
            ((rk ↥(commV (autQuot L N)) : ℚ) / (rk ↥(I.map (QuotientGroup.mk' N)) : ℚ)) ≤
          E3.mParam Y →
        IsDirSumOver (CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSet L Y)
            (fun X' => commV (autQuot X' (⊥ : Subgroup W))) ∧
          (E3.mParam (autSub Y I) : ℚ) * ((rk ↥(commV L) : ℚ) / (rk ↥I : ℚ)) ≤
            E3.mParam Y := by
      rintro N rfl hs hi
      refine ⟨hs, ?_⟩
      rwa [Thm14_5.mParam_autSub_autQuot_bot, Thm14_5.rk_commV_autQuot_bot,
        Thm14_5.rk_map_mk_bot] at hi
    obtain ⟨hs, hi⟩ := key _ hfixH hsum hIm
    exact ⟨hs, I, hI, hi⟩
  · exfalso
    rcases hshape with ⟨h3, rfl⟩ | ⟨h5, rfl⟩
    · rw [dMinDeg_eq_six_of_isL2_three h3] at hRd
      omega
    · have := twenty_le_dMinDeg_of_isSz_five h5
      omega


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
