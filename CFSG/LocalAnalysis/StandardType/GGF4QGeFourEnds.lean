module

public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourInputs
public import CFSG.LocalAnalysis.StandardType.GGF4OriginalTypes
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteCard
public import CFSG.LocalAnalysis.StandardType.GGSecFiveMaxJoin
public import CFSG.LocalAnalysis.StandardType.GGF4H1Coverage
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Lift
public import CFSG.LocalAnalysis.StandardType.GGF4LabelH1
public import CFSG.LocalAnalysis.StandardType.GGF4H1Rows
import CFSG.LocalAnalysis.StandardType.GGTBXDatumOfTor
import CFSG.LocalAnalysis.StandardType.GGTBTorD

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Assembly

theorem ggF4QGeFourEnds_bstar_types
    (hX : GGResXDichotomyInput) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hNb : GGNbr p B x D J y K)
    (hRC : GGSecFiveRouteCfg p B Bs x L D J {K}) (hT1 : ¬ GGSecFiveTier1Region p B Bs x L D J)
    (hWK : GGWeylOfType p CoxeterMatrix.F₄ (ggAutomizer L Bs ⊔ ggAutomizer K Bs)) :
    (GGWeylOfType p (CoxeterMatrix.A 3) (ggAutomizer L Bs) ∨
        GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer L Bs)) ∧
      Nat.card Bs = p ^ 4 ∧ B = Bs ∧ twoLocalPrimeRank p G = 4 := by
  have hJ : ggAutomizerJoin L Bs {K} = ggAutomizer L Bs ⊔ ggAutomizer K Bs :=
    ggAutomizerJoin_singleton L Bs K
  obtain ⟨e, he⟩ := hWK
  let e' : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizerJoin L Bs {K}) :=
    e.trans (MulEquiv.subgroupCongr hJ.symm)
  have hP : GGCoxeterPres p (ggAutomizerJoin L Bs {K}) CoxeterMatrix.F₄ e' :=
    ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _,
      (ggCoxeterMatrix_reindex_refl _).symm⟩)))), fun i => he i⟩
  have hF4 : GGIsWeylMatrixF4 CoxeterMatrix.F₄ :=
    ⟨Equiv.refl _, (ggCoxeterMatrix_reindex_refl _).symm⟩
  exact ⟨ggSecFiveF4OriginalTypesInput_holds hX hTCJ hRig hTBF hWI G p B Bs x L D J {K} hRC hT1
      (Finset.singleton_nonempty K) (Fin 4) CoxeterMatrix.F₄ e' hP hF4,
    FrameRoute.bstar_eq_of_weylAt_F4 hTBF hWI hRC.1 hRC.2.1 ⟨y, K, hNb, ⟨e, he⟩⟩⟩

section O3


theorem ggF4Ends_no_residual_label
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hT : GGNoTransvection p Bs) (hcard : Nat.card Bs = p ^ 4)
    (hq : ¬ GGInnerDiagOnLabel GGLabQTwo p Bs L)
    (hM : GGInnerDiagOnLabel (fun p lab => LargeEvenSplit p lab ∧ ¬ GGTBTorCov p lab)
      p Bs L) : False := by
  have hp : p.Prime := hcfg.tableB_facts.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨hperf, lab, hlab, hraw⟩ := ggF4H1_residual_marking hcfg hM
  obtain ⟨R, _, I, F, -, -, θ, hS, hN, hInd⟩ := largeEvenRawDatum_exists hraw
  have hmark : ∀ (T : ℕ → LargeEvenLabel → Prop), T p lab →
      GGInnerDiagOnLabel T p Bs L := by
    intro T ht
    refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    intro R _ I F hQ
    obtain ⟨hs, hna, θ, hP⟩ := hQ
    exact ⟨hs, hna, θ, ht, hP.2⟩
  by_cases hU : GGUnitDvd63Label p lab
  · exact no_original_unitSix_at_card_four hcfg (hmark _ hU) hcard
  have hrest : GGTBWeylRowResRest p lab := by
    refine ⟨hS.2, ?_⟩
    rintro ⟨ht, hr, hp3, hd⟩
    apply hU
    refine ⟨⟨ht, by omega, by simpa [hp3] using hd, ?_⟩, hr, hp3⟩
    rw [hr, hp3]
    norm_num
  by_cases hsmall : GGTBResSmallLabel p lab
  · exact ggTBWeylRowResRest_small_false_L hcfg (hmark _ ⟨hrest, hsmall⟩)
  have hcases := ggTBWeylRowResRest2_cases hp hp2 hlab ⟨hrest, hsmall⟩
  rcases hcases with hlin | hF4 | hE6 | htw | htw
  · exact hq (hmark GGLabQTwo (show lab.n < 2 by have := hlin.2.2.1; omega))
  · exact no_original_f4Three_at_card_four hcfg hT (hmark _ hF4) hcard
  · exact hq (hmark GGLabQTwo (show lab.n < 2 by have := hE6.2.1; omega))
  · exact ggF4H1_not_twE6_sub hp hp2 htw.1 hS.1 (by simpa [htw.2.1] using htw.2.2)
  · refine false_of_original_torusLift_ge_four hcfg hcard (hmark GGTwE6BadLabel htw) ?_
    intro lab' hlab' htw'
    have hd : p ∣ 2 ^ lab'.n + 1 := by simpa [htw'.2.1] using htw'.2.2
    exact (largeEvenLabelAll_torusLift_twE6Add_holds hp hlab' ⟨htw'.1, hd⟩).mono
      (fun _ _ _ _ h => ⟨TwE6Delta.liftRank p, by
        simp [htw'.2.1, TwE6Delta.liftRank_three], h⟩)

theorem ggF4Ends_original_torCov
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hT : GGNoTransvection p Bs) (hcard : Nat.card Bs = p ^ 4)
    (hq : ¬ GGInnerDiagOnLabel GGLabQTwo p Bs L) :
    GGInnerDiagOnLabel (fun p lab => (LargeEvenSplit p lab ∧ 2 ≤ lab.n) ∧ GGTBTorCov p lab)
      p Bs L := by
  have hmk := ggF4H1_original_marking hcfg hcard
  rcases ggInnerDiagOnLabel_split
      (T := fun p lab => (LargeEvenSplit p lab ∧ 2 ≤ lab.n) ∧ GGTBTorCov p lab) hmk with
    hres | htor
  · exfalso
    obtain ⟨hperf, lab, hlab, hraw⟩ := hres
    obtain ⟨R, _, I, F, -, -, θ, ⟨hsp, hnot⟩, -⟩ := largeEvenRawDatum_exists hraw
    by_cases hn : 2 ≤ lab.n
    · refine ggF4Ends_no_residual_label hcfg hT hcard hq ⟨hperf, lab, hlab,
        largeEvenRawDatum_mono ?_ hraw⟩
      intro R _ I F hQ
      obtain ⟨hs, hna, θ, ⟨hsp', hnot'⟩, hP⟩ := hQ
      exact ⟨hs, hna, θ, ⟨hsp', fun hc => hnot' ⟨⟨hsp', hn⟩, hc⟩⟩, hP⟩
    · refine hq ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
      intro R _ I F hQ
      obtain ⟨hs, hna, θ, -, hP⟩ := hQ
      exact ⟨hs, hna, θ, show lab.n < 2 by omega, hP⟩
  · exact htor

end O3

theorem ggF4Ends_card_coxeterA_ne (n : ℕ) : Nat.card (CoxeterMatrix.A n).Group ≠ 48 := by
  rw [l05nK3a_card_coxeterA]
  intro h
  rcases (show n + 1 ≤ 4 ∨ 5 ≤ n + 1 by omega) with hle | hge
  · have h1 := Nat.factorial_le hle
    have h24 : Nat.factorial 4 = 24 := by decide
    omega
  · have h1 := Nat.factorial_le hge
    have h120 : Nat.factorial 5 = 120 := by decide
    omega

theorem ggF4Ends_rank_eq_three_of_card_coxeterB {n : ℕ} (hn : 1 ≤ n)
    (h : Nat.card (CoxeterMatrix.B n).Group = 48) : n = 3 := by
  rcases n with _ | k
  · omega
  rcases k with _ | k
  · have hBA : CoxeterMatrix.B 1 = CoxeterMatrix.A 1 := by
      apply CoxeterMatrix.ext
      ext i j
      fin_cases i
      fin_cases j
      decide
    rw [hBA, l05nK3a_card_coxeterA] at h
    norm_num at h
  · rw [ggCoxeterB_card (k + 2) (by omega)] at h
    have hdvd : 2 ^ (k + 2) ∣ 48 := ⟨(k + 2).factorial, h.symm⟩
    have hle : 2 ^ (k + 2) ≤ 48 := Nat.le_of_dvd (by norm_num) hdvd
    have hk : k + 2 ≤ 5 := by
      by_contra hc
      have h6 : 6 ≤ k + 2 := by omega
      have h64 : 64 ≤ 2 ^ (k + 2) := by
        calc 64 = 2 ^ 6 := by norm_num
          _ ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by norm_num) h6
      omega
    have hk3 : k ≤ 3 := by omega
    interval_cases k <;> first | rfl | (norm_num [Nat.factorial] at h)

theorem ggF4Ends_card_coxeterD_ne {n : ℕ} (hn : 3 ≤ n) :
    Nat.card (ggCoxeterMatrixD n).Group ≠ 48 := by
  intro h
  rcases (show n = 3 ∨ 4 ≤ n by omega) with rfl | h4
  · rw [← coxeterA_three_reindex_swap,
      Nat.card_congr ((CoxeterMatrix.A 3).reindexGroupEquiv (Equiv.swap (0 : Fin 3) 1)).toEquiv,
      l05nK3a_card_coxeterA] at h
    norm_num [Nat.factorial] at h
  · rw [OrthF3.card_coxeterD_eq n h4] at h
    have h8 : 8 ≤ 2 ^ (n - 1) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h24 : Nat.factorial 4 ≤ Nat.factorial n := Nat.factorial_le h4
    have hbig : 192 ≤ 2 ^ (n - 1) * n.factorial := by
      calc 192 = 8 * Nat.factorial 4 := by norm_num
        _ ≤ 2 ^ (n - 1) * n.factorial := Nat.mul_le_mul h8 h24
    omega

theorem ggF4Ends_row_metadata48
    {p : ℕ} {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    {r m N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hrow : GGTBTorRowAt p lab r m N C M) (hM : Nat.card M.Group = 48) :
    ((lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 3) ∨ (lab.tag = .twD ∧ lab.rank = 4) ∨
      (lab.rank = 5 ∧ ((lab.tag = .A ∧ p ∣ 2 ^ lab.n + 1) ∨
        (lab.tag = .twA ∧ p ∣ 2 ^ lab.n - 1))) := by
  cases hrow with
  | aDep _ _ _ _ _ => exact absurd hM (ggF4Ends_card_coxeterA_ne _)
  | e6Three _ _ _ => exact absurd hM (by rw [card_coxeterE6_group]; norm_num)
  | e8Three _ _ => exact absurd hM (by rw [card_coxeterE8_group]; norm_num)
  | aInd _ _ _ => exact absurd hM (ggF4Ends_card_coxeterA_ne _)
  | c htag _ =>
      have h2 : 2 ≤ lab.rank := by
        rcases htag with htag | htag <;>
          · have h := hlab.2
            rw [htag] at h
            exact h.1
      exact Or.inl ⟨htag, ggF4Ends_rank_eq_three_of_card_coxeterB (by omega) hM⟩
  | d hdisj =>
      have h3 : 3 ≤ lab.rank := by
        rcases hdisj with ⟨hD, -⟩ | ⟨htwD, -, hodd⟩
        · have h := hlab.2
          rw [hD] at h
          exact h
        · have h := hlab.2
          rw [htwD] at h
          obtain ⟨k, hk⟩ := hodd
          omega
      exact absurd hM (ggF4Ends_card_coxeterD_ne h3)
  | e6Ind _ _ _ => exact absurd hM (by rw [card_coxeterE6_group]; norm_num)
  | e7 _ _ => exact absurd hM (by rw [card_coxeterE7_group]; norm_num)
  | e8Ind _ _ _ => exact absurd hM (by rw [card_coxeterE8_group]; norm_num)
  | f4 _ _ _ => exact absurd hM (by rw [l04fFRC_ord_card_coxeterF4]; norm_num)
  | g2 _ _ => exact absurd hM (by rw [l04fFRC_card_coxeterG2]; norm_num)
  | relD hdisj =>
      have hk : 1 ≤ lab.rank - 1 := by
        rcases hdisj with ⟨hD, -⟩ | ⟨htwD, -⟩
        · have h := hlab.2
          rw [hD] at h
          omega
        · have h := hlab.2
          rw [htwD] at h
          omega
      have h3 := ggF4Ends_rank_eq_three_of_card_coxeterB hk hM
      rcases hdisj with ⟨-, -, hodd⟩ | ⟨htwD, -⟩
      · obtain ⟨k, hk'⟩ := hodd
        omega
      · exact Or.inr (Or.inl ⟨htwD, by omega⟩)
  | relE6 _ _ => exact absurd hM (by rw [l04fFRC_ord_card_coxeterF4]; norm_num)
  | relA5 h5 hd => exact Or.inr (Or.inr ⟨h5, hd⟩)

theorem ggF4Ends_row_at_L (hW : GGTBTorWRows) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hM : GGInnerDiagOnLabel GGTBTorCov p Bs L)
    (hB3 : GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer L Bs)) :
    ∃ (lab : LargeEvenLabel) (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
      (M : CoxeterMatrix (Fin N)),
      LargeEvenInLambda2 lab ∧ GGHasLabel lab (L ⧸ Subgroup.center L) ∧
        GGTBTorRowAt p lab r m N C M ∧ Nat.card M.Group = 48 := by
  have hp : p.Prime := hcfg.tableB_facts.1
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨lab, r, m, N, C, M, R, _instR, θ, I, hN, hperf, hlab, hrow, -, hBsI, hlift,
    hTorW, hHas⟩ := l05nPlQ_marking_with hW hLift hp2 (fun _ _ _ _ _ => True) (by
      refine largeEvenMarking_mono ?_ hM
      intro lab R _ I F θ h
      obtain ⟨r, m, N, C, M, hrow⟩ := h.1
      exact ⟨⟨r, m, N, C, M, hrow, trivial⟩, h.2⟩)
  obtain ⟨w, hw⟩ := hTorW L (ggQuotHom θ) (ggGamma L hN).range
    (ggTorusTBGroup_of_L hcfg hperf θ hN hBsI hlift)
  obtain ⟨hm, hpm, -, -⟩ := l05nPlP1_row_facts hp hp2 hlab hrow
  obtain ⟨hnk, -⟩ := ggTD_core hm hpm hcfg.tableB_facts.2.1 hcfg.2.1.2.2.2 hN w hw
  obtain ⟨e, -⟩ := ggTD_weyl hN hw hp2 hcfg.tableB_facts.2.1 hnk
  refine ⟨lab, r, m, N, C, M, hlab, hHas, hrow, ?_⟩
  rw [Nat.card_congr e.toEquiv]
  obtain ⟨eB, -⟩ := hB3
  rw [← Nat.card_congr eB.toEquiv, ggCoxeterB_card 3 (by norm_num)]
  decide

theorem ggF4Ends_not_dvd_both {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h₁ : p ∣ 2 ^ n - 1)
    (h₂ : p ∣ 2 ^ n + 1) : False := by
  have h := Nat.dvd_sub h₂ h₁
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  rw [show 2 ^ n + 1 - (2 ^ n - 1) = 2 by omega] at h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)

theorem ggF4Ends_labelIso_eq {lab lab' : LargeEvenLabel} (h : GGLabelIso lab lab')
    (hr : 4 ≤ lab'.rank) (hbc : lab'.tag ≠ .B ∧ lab'.tag ≠ .C) : lab = lab' := by
  rcases h with h | ⟨-, h, -, -⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · exact h
  · rcases h with h | h
    · exact absurd h hbc.1
    · exact absurd h hbc.2
  all_goals (rw [h] at hr; simp at hr)

theorem ggF4Ends_labelIso_BC {lab lab' : LargeEvenLabel} (h : GGLabelIso lab lab')
    (htag : lab'.tag = .B ∨ lab'.tag = .C) (hr : lab'.rank = 3) :
    (lab.tag = .B ∨ lab.tag = .C) ∧ lab.rank = 3 ∧ lab.n = lab'.n := by
  rcases h with rfl | ⟨h1, -, h3, h4⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, -⟩
  · exact ⟨htag, hr, rfl⟩
  · exact ⟨h1, h3.trans hr, h4⟩
  all_goals (rw [h] at htag; simp at htag)

section Label


theorem ggF4Ends_original_label_B3 (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hT : GGNoTransvection p Bs) (hcard : Nat.card Bs = p ^ 4)
    (hq : ¬ GGInnerDiagOnLabel GGLabQTwo p Bs L)
    (hB3 : GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer L Bs)) :
    ∃ f, 2 ≤ f ∧
      ((p ∣ 2 ^ f - 1 ∧ (GGHasLabel ⟨.B, 3, f⟩ (L ⧸ Subgroup.center L) ∨
          GGHasLabel ⟨.C, 3, f⟩ (L ⧸ Subgroup.center L))) ∨
        ((p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) ∧ GGHasLabel ⟨.twD, 4, f⟩ (L ⧸ Subgroup.center L))) := by
  have hp : p.Prime := hcfg.tableB_facts.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨hperf, labs, hlabs, hraw⟩ := ggF4Ends_original_torCov hcfg hT hcard hq
  obtain ⟨R, _, I, F, -, -, θ, ⟨⟨hsp, hn⟩, -⟩, -⟩ := largeEvenRawDatum_exists hraw
  have hHs : GGHasLabel labs (L ⧸ Subgroup.center L) :=
    largeEvenRawDatum_mono (fun R _ I F hQ => by
      obtain ⟨-, -, θ, -⟩ := hQ
      exact ⟨θ⟩) hraw
  have hM : GGInnerDiagOnLabel GGTBTorCov p Bs L :=
    ⟨hperf, labs, hlabs, largeEvenRawDatum_mono (fun R _ I F hQ => by
      obtain ⟨hs, hna, θ, hP⟩ := hQ
      exact ⟨hs, hna, θ, hP.1.2, hP.2⟩) hraw⟩
  obtain ⟨labr, r, m, N, C, M, hlabr, hHr, hrow, h48⟩ :=
    ggF4Ends_row_at_L (ggTBTorWRows_of_all (ggTBTorAll_of_remaining trivial))
      ggTBTorLiftRows_holds hcfg hM hB3
  have hiso := hRig labs labr (L ⧸ Subgroup.center L) hlabs hlabr hHs hHr
  have hmeta := ggF4Ends_row_metadata48 hlabr hrow h48
  have hsplit : (LargeEvenUntwisted labs.tag ∧ p ∣ 2 ^ labs.n - 1) ∨
      (¬ LargeEvenUntwisted labs.tag ∧ labs.tag ≠ .triD4 ∧ p ∣ 2 ^ labs.n + 1) ∨
      ((labs.tag = .twD ∨ labs.tag = .triD4) ∧ p ∣ 2 ^ labs.n - 1) := by
    rcases hsp with h | h | h | ⟨h1, -⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
    · omega
  rcases hmeta with ⟨htr, hlr⟩ | ⟨htr, hlr⟩ | ⟨hlr, htr⟩
  ·
    obtain ⟨hts, -, hns⟩ := ggF4Ends_labelIso_BC hiso htr hlr
    have hpd : p ∣ 2 ^ labs.n - 1 := by
      rcases hsplit with ⟨-, h⟩ | ⟨hu, -, -⟩ | ⟨htw, -⟩
      · exact h
      · rcases hts with h | h <;> rw [h] at hu <;> exact absurd trivial hu
      · rcases hts with h | h <;> rcases htw with h' | h' <;> rw [h] at h' <;>
          exact absurd h' (by decide)
    refine ⟨labr.n, by omega, Or.inl ⟨hns ▸ hpd, ?_⟩⟩
    obtain ⟨tr, lr, nr⟩ := labr
    dsimp only at htr hlr ⊢
    subst hlr
    rcases htr with rfl | rfl
    · exact Or.inl hHr
    · exact Or.inr hHr
  ·
    have heq := ggF4Ends_labelIso_eq hiso (by omega) (by rw [htr]; exact ⟨by decide, by decide⟩)
    subst heq
    have hsign : p ∣ 2 ^ labs.n - 1 ∨ p ∣ 2 ^ labs.n + 1 := by
      rcases hsplit with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
      · exact Or.inl h
    refine ⟨labs.n, hn, Or.inr ⟨hsign, ?_⟩⟩
    obtain ⟨ts, ls, ns⟩ := labs
    dsimp only at htr hlr ⊢
    subst htr hlr
    exact hHr
  ·
    exfalso
    have heq := ggF4Ends_labelIso_eq hiso (by omega)
      (by rcases htr with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h] <;> exact ⟨by decide, by decide⟩)
    subst heq
    rcases htr with ⟨ht, hd⟩ | ⟨ht, hd⟩
    · rcases hsplit with ⟨-, h⟩ | ⟨hu, -, -⟩ | ⟨htw, -⟩
      · exact ggF4Ends_not_dvd_both hp hp2 h hd
      · rw [ht] at hu
        exact hu trivial
      · rw [ht] at htw
        rcases htw with h | h <;> exact absurd h (by decide)
    · rcases hsplit with ⟨hu, -⟩ | ⟨-, -, h⟩ | ⟨htw, -⟩
      · rw [ht] at hu
        exact hu
      · exact ggF4Ends_not_dvd_both hp hp2 hd h
      · rw [ht] at htw
        rcases htw with h | h <;> exact absurd h (by decide)

end Label

end CFSG.StandardType

end
