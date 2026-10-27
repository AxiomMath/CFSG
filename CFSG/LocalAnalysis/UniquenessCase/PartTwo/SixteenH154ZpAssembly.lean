module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ThirdP
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExc
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154ChiOne

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem s16h_zpRow_of_conc4_133 {W : Type} [CommGroup W]
    {A L : Subgroup (MulAut W)} {t : MulAut W} {p : ℕ}
    (hp : p.Prime) (hL : Nat.card ↥L = p) (h : Conc4_133 A t L) :
    s16h_ZpRow p (rk ↥(commSub (⊤ : Subgroup W) L)) := by
  obtain ⟨q, -, -, -, -, hrows⟩ := h
  unfold s16h_ZpRow
  rcases hrows with ⟨hcyc, hr⟩ | ⟨hcyc, hr⟩ | ⟨hP, hr⟩ | ⟨hE, hr, -, -⟩ | ⟨hcyc, hr⟩ |
    ⟨r, m, -, hr2, hE, -, -⟩ | ⟨hE, hr, -⟩
  · exact Or.inl ⟨hL.symm.trans hcyc.2, hr⟩
  · exact Or.inr (Or.inl ⟨hL.symm.trans hcyc.2, hr⟩)
  · exfalso
    have h3p : 3 ^ 3 = p := hP.2.1.symm.trans hL
    exact absurd (hp.pow_eq_iff.mp h3p).2 (by norm_num)
  · exfalso
    have h32p : 3 ^ 2 = p := (s16h_dc_card_of_elem hE).symm.trans hL
    exact absurd (hp.pow_eq_iff.mp h32p).2 (by norm_num)
  · exact Or.inr (Or.inr ⟨hL.symm.trans hcyc.2, hr⟩)
  · exfalso
    have hqp : q ^ r = p := (s16h_dc_card_of_elem hE).symm.trans hL
    have hr1 : r = 1 := (hp.pow_eq_iff.mp hqp).2
    omega
  · exfalso
    have h32p : 3 ^ 2 = p := (s16h_dc_card_of_elem hE).symm.trans hL
    exact absurd (hp.pow_eq_iff.mp h32p).2 (by norm_num)

private theorem s16h_v1Sub_eq_of_odd_card (D : Data G) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hodd : Odd (Nat.card ↥(lBar V₀ V hV L))) :
    v1Sub D.M V₀ V hV L = V₀ := by
  by_cases h0 : V₀ = ⊥
  · subst h0
    exact s16c167_v1Sub_eq_bot_of_inf_fixV D hV rfl
      (s16c167_wTil_inf_fixV_eq_bot_of_odd hV L hodd)
  · exact v1Sub_of_ne_bot D.M V₀ V hV L h0

theorem s16h_hyp154_of_cyclic (D : Data G) (S : s16h_Std D)
    (h4 : 3 < CFSG.Open.evenRank G) (hσ : D.sig = D.sig1)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hc : Conc4_136 D V₀ V h.hyp151.isElemAbelian L)
    (hs : 1 < s15 D.M V₀ V h.hyp151.isElemAbelian L)
    (hnot : ¬ Concl164 D V₀ V h.hyp151.isElemAbelian L)
    (hδ : s15 D.M V₀ V h.hyp151.isElemAbelian L = 2 →
      delta15 D.M V₀ V h.hyp151.isElemAbelian L <
        gamma15 D.M V₀ V h.hyp151.isElemAbelian L - 1)
    {p : ℕ} (hp : p.Prime) (hLp : IsCyclicOrd ↥(lBar V₀ V h.hyp151.isElemAbelian L) p) :
    Hyp154 D V₀ V L := by
  have hV := h.hyp151.isElemAbelian
  have hc0 := hc
  obtain ⟨t, -, -, -, -, hW⟩ := hc0
  have hrow : s16h_ZpRow p (rk ↥(commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L))) :=
    s16h_zpRow_of_conc4_133 hp hLp.2 (s16h_conc4_133_of_prime_card hp hLp.2 hW)
  have hp2 : p ≠ 2 := by
    rcases hrow with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have hodd : Odd (Nat.card ↥(lBar V₀ V hV L)) := by
    rw [hLp.2]
    exact hp.odd_of_ne_two hp2
  have hv1 : v1Sub D.M V₀ V hV L ≤ V₀ := (s16h_v1Sub_eq_of_odd_card D hV hodd).le
  have hfix : commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) ⊓
      fixV (lBar V₀ V hV L) = ⊥ :=
    s16c167_wTil_inf_fixV_eq_bot_of_odd hV L hodd
  have hdvd : p ∣ Nat.card ↥(lBar V₀ V hV L) := by
    rw [hLp.2]
  have hqL : p ∣ Nat.card ↥(barSub V₀ V hV L) := by
    rw [show Nat.card ↥(barSub V₀ V hV L) = p from hLp.2]
  have hσ3 : ∃ q ∈ D.sig, 3 ≤ CFSG.Open.pRank q D.M := by
    obtain ⟨q, hq⟩ := S.hx.sig_nonempty
    exact ⟨q, hq, S.hSig.three_le q hq⟩
  by_cases hχ : ∀ n ∈ Mbar D.M V₀ V hV,
      n ∈ normalizer ((lBar V₀ V hV L : Subgroup _) : Set _) →
        ∀ l ∈ lBar V₀ V hV L, n * l = l * n
  · have hγ : gamma15 D.M V₀ V hV L ≤ 3 :=
      s16h_gamma_le_three_of_chi_eq_one D h hc hp hLp hχ
    have hsne : s15 D.M V₀ V hV L ≠ 2 := fun hs2 => hnot ⟨hs2, Or.inl hγ⟩
    have hs3 : 3 ≤ s15 D.M V₀ V hV L := by omega
    obtain ⟨hp37, hUcard⟩ := s16h_card_wTil_of_chi_eq_one D h hc hp hLp hχ
    by_cases hpσ : p ∈ D.sig
    · have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
        S.hSig.sig1_sp p (hσ ▸ hpσ)
      have hU₂ : s16h_CondU2 D V₀ V L hV :=
        s16h_condU2_of_dvd D h hc hp hdvd (fun w hwV hw0 P hPp hPc hPC =>
          s16c34_uniqueMax_cent_of_cElt D S.h61 S.h127 h.hyp16 hpσ hPp hPc hwV hw0 hPC)
      exact s16h_hyp154_of_condU2_dvd D S.h61 S.h127 h hσ3 hU₂ (by omega)
        hp hp2 hsp hqL
    · have hp2' : p ≠ 2 := by rcases hp37 with h | h <;> omega
      have hUc : s16h_CondU D V₀ V L hV :=
        s16h_condU_of_chiOne D S.hx S.hSig S.h61 S.h63 S.h77 S.h869 S.h111 S.h112 S.hThin
          S.hCyc S.h127 h4 h hc hp hp2' hpσ hLp hUcard hχ hs3
      exact s16h_hyp154_of_condU D S.h61 h hσ3 hUc hs hδ
  · have hU₂ : s16h_CondU2 D V₀ V L hV :=
      s16h_condU2_of_chi_ne D S.hSig S.h61 S.h63 S.h77 S.h869 S.h111 S.h112 S.hThin
        S.hCyc S.h127 hσ h hc hp hp2 hLp hχ
    by_cases hs2 : s15 D.M V₀ V hV L = 2
    · have hδ2 : delta15 D.M V₀ V hV L < gamma15 D.M V₀ V hV L - 1 := hδ hs2
      by_cases hQ : ∃ q ∈ D.sig, q ≠ 3
      · obtain ⟨q, hq, hq3⟩ := hQ
        have hBB : s16h_BlockBound (Mbar D.M V₀ V hV) (lBar V₀ V hV L) q 2 :=
          s16h_blockBound_two_of_cyclic (s15_Infra_vtil_sq_eq_one V₀ V hV) hp
            (D.sig_prime q hq).1 hp2 (D.sig_prime q hq).2 hLp.1 hLp.2 hfix hrow
            (fun hex => hq3 hex.2.2)
        have hW1 : ∀ w ∈ wSub V₀ V hV L, w ≠ 1 →
            UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) :=
          s16h_uniqueMax_of_blockBound_two D S.h61 S.h127 h (by omega) hq
            (S.hx.four_le h4 q hq) hBB
        exact s16h_hyp154_of_unique₁_two D h.hyp151 hs2
          (s16h_unique₁_of_wSub D h.hyp151 hv1 hW1) hδ2
      · have hall : ∀ q ∈ D.sig, q = 3 := by
          intro q hq
          by_contra hq3
          exact hQ ⟨q, hq, hq3⟩
        have h3mem : 3 ∈ D.sig := by
          obtain ⟨q, hq⟩ := S.hx.sig_nonempty
          exact (hall q hq) ▸ hq
        have h3 : D.sig = {3} :=
          Set.eq_singleton_iff_unique_mem.2 ⟨h3mem, fun q hq => hall q hq⟩
        by_cases hZC : p = 3 ∧ rk ↥(wTil V₀ V hV L) = 6
        · obtain ⟨hp3, hrk6⟩ := hZC
          exact s16h_hyp154_of_unique₁_two D h.hyp151 hs2
            (s16h_unique₁_of_Z3_six_two D S h4 hσ h hc (hp3 ▸ hLp) hrk6 hs2 h3) hδ2
        · have hBB : s16h_BlockBound (Mbar D.M V₀ V hV) (lBar V₀ V hV L) 3 2 :=
            s16h_blockBound_two_of_cyclic (s15_Infra_vtil_sq_eq_one V₀ V hV) hp
              (D.sig_prime 3 h3mem).1 hp2 (D.sig_prime 3 h3mem).2 hLp.1 hLp.2 hfix hrow
              (fun hx => hZC ⟨hx.1, hx.2.1⟩)
          have hW1 : ∀ w ∈ wSub V₀ V hV L, w ≠ 1 →
              UniqueMax D.M (D.M ⊓ centralizer ({w} : Set G)) :=
            s16h_uniqueMax_of_blockBound_two D S.h61 S.h127 h (by omega) h3mem
              (S.hx.four_le h4 3 h3mem) hBB
          exact s16h_hyp154_of_unique₁_two D h.hyp151 hs2
            (s16h_unique₁_of_wSub D h.hyp151 hv1 hW1) hδ2
    · have hs3le : 3 ≤ s15 D.M V₀ V hV L := by omega
      by_cases hs4 : 3 < s15 D.M V₀ V hV L
      · exact s16h_hyp154_of_condU2 D S.h61 h hσ3 hU₂ hs4
      · have hs_eq3 : s15 D.M V₀ V hV L = 3 := by omega
        by_cases hpσ : p ∈ D.sig
        · have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
            S.hSig.sig1_sp p (hσ ▸ hpσ)
          have hσ3p : ∃ q ∈ D.sig, 3 ≤ CFSG.Open.pRank q D.M :=
            ⟨p, hpσ, S.hSig.three_le p hpσ⟩
          exact s16h_hyp154_of_condU2_dvd D S.h61 S.h127 h hσ3p hU₂ (by omega)
            hp ((D.sig_prime p hpσ).2) hsp hqL
        · by_cases hQ : ∃ q ∈ D.sig, q ≠ 3
          · obtain ⟨q, hq, hq3⟩ := hQ
            have hqp : q ≠ p := fun h => hpσ (h ▸ hq)
            have hBB : s16h_BlockBound (Mbar D.M V₀ V hV) (lBar V₀ V hV L) q 1 :=
              s16h_blockBound_one_of_cyclic (s15_Infra_vtil_sq_eq_one V₀ V hV) hp
                (D.sig_prime q hq).1 hp2 (D.sig_prime q hq).2 hqp hLp.1 hLp.2 hfix hrow
                (fun hex => hq3 hex.2.2)
            exact s16h_hyp154_of_blockBound_one D S.h61 S.h127 h hs_eq3 hq
              (S.hSig.sig1_sp q (hσ ▸ hq)) (S.hx.four_le h4 q hq) hv1 hBB
          · have hall : ∀ q ∈ D.sig, q = 3 := by
              intro q hq
              by_contra hq3
              exact hQ ⟨q, hq, hq3⟩
            have h3mem : 3 ∈ D.sig := by
              obtain ⟨q, hq⟩ := S.hx.sig_nonempty
              exact (hall q hq) ▸ hq
            have h3 : D.sig = {3} :=
              Set.eq_singleton_iff_unique_mem.2 ⟨h3mem, fun q hq => hall q hq⟩
            by_cases hZC : p = 7 ∧ rk ↥(wTil V₀ V hV L) = 6
            · obtain ⟨hp7, hrk6⟩ := hZC
              exact (s16h_false_of_Z7_six_three D S hσ h hc (hp7 ▸ hLp) hrk6 hs_eq3 h3).elim
            · have hBB : s16h_BlockBound (Mbar D.M V₀ V hV) (lBar V₀ V hV L) 3 1 :=
                s16h_blockBound_one_of_cyclic (s15_Infra_vtil_sq_eq_one V₀ V hV) hp
                  (D.sig_prime 3 h3mem).1 hp2 (D.sig_prime 3 h3mem).2
                  (fun h => hpσ (h ▸ h3mem)) hLp.1 hLp.2 hfix hrow
                  (fun hx => hZC ⟨hx.1, hx.2.1⟩)
              exact s16h_hyp154_of_blockBound_one D S.h61 S.h127 h hs_eq3 h3mem
                (S.hSig.sig1_sp 3 (hσ ▸ h3mem)) (S.hx.four_le h4 3 h3mem) hv1 hBB

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
