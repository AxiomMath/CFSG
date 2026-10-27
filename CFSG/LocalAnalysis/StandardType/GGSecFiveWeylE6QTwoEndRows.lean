module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoEndFacts
public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrRankDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthWeylOrdD
public import CFSG.LocalAnalysis.StandardType.GGNSJoinBaseLabel

public section

namespace CFSG.StandardType

open CFSG.Assembly

private lemma not_dvd_51840_of_seven_dvd {d : ℕ} (h : 7 ∣ d) : ¬ d ∣ 51840 := by
  intro hd
  have h7 : 7 ∣ 51840 := h.trans hd
  rw [Nat.dvd_iff_mod_eq_zero] at h7
  norm_num at h7

private lemma not_dvd_51840_of_two_pow_nine_dvd {d : ℕ} (h : 2 ^ 9 ∣ d) :
    ¬ d ∣ 51840 := by
  intro hd
  have h512 : 2 ^ 9 ∣ 51840 := h.trans hd
  rw [Nat.dvd_iff_mod_eq_zero] at h512
  norm_num at h512

private lemma not_dvd_51840_of_gt {d : ℕ} (h : 51840 < d) : ¬ d ∣ 51840 := by
  intro hd
  have hle := Nat.le_of_dvd (by norm_num : 0 < 51840) hd
  omega

private lemma seven_dvd_card_coxeterA {r : ℕ} (hr : 6 ≤ r) :
    7 ∣ Nat.card (CoxeterMatrix.A r).Group := by
  rw [l05nK3a_card_coxeterA]
  exact Nat.dvd_factorial (by norm_num) (by omega)

private lemma seven_dvd_card_coxeterD {r : ℕ} (hr : 7 ≤ r) :
    7 ∣ Nat.card (ggCoxeterMatrixD r).Group := by
  rw [OrthF3.card_coxeterD_eq r (by omega)]
  exact dvd_mul_of_dvd_right (Nat.dvd_factorial (by norm_num) (by omega)) _

private lemma two_pow_nine_dvd_card_coxeterD_six :
    2 ^ 9 ∣ Nat.card (ggCoxeterMatrixD 6).Group := by
  rw [OrthF3.card_coxeterD_eq 6 (by norm_num)]
  exact ⟨45, by norm_num⟩

theorem E6QTwo.endLabel_cases
    {lab : LargeEvenLabel} (hn : lab.n = 1)
    (h : ggRowP_ESU 3 lab ∨ ggRowP_EOmM 3 lab ∨ ggRowP_ETwE6 3 lab ∨ ggRowP_EOmP 3 lab ∨
      ggRowP_EE7 3 lab ∨ ggRowP_EE8 3 lab ∨ ggRowP_NF4 3 lab) :
    (((lab.tag = .twA ∧ lab.rank = 5) ∨ (lab.tag = .D ∧ lab.rank = 4) ∨
        (lab.tag = .twD ∧ lab.rank = 5)) ∧ lab.n = 1) ∨
      (∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ) (M : CoxeterMatrix (Fin N)),
        GGTBTorRowAt 3 lab r m N C M ∧ (N ≤ 3 ∨ ¬ Nat.card M.Group ∣ 51840)) ∨
      (lab.tag = .twA ∧ lab.rank = 4 ∧ lab.n = 1) ∨ GGF4ThreeLabel 3 lab ∨
      GGTwE6BadLabel 3 lab := by
  obtain ⟨t, r, n⟩ := lab
  simp only at hn
  subst hn
  dsimp only at *
  simp only [ggRowP_ESU, ggRowP_EOmM, ggRowP_ETwE6, ggRowP_EOmP, ggRowP_EE7, ggRowP_EE8,
    ggRowP_NF4] at h
  rcases h with h | h | h | h | h | h | h
  ·
    obtain ⟨h1, -⟩ := h
    rcases h1 with ⟨ht, hr⟩ | ⟨ht, hr3⟩
    ·
      by_cases hr3 : r = 3
      · subst hr3
        refine Or.inr (Or.inl ⟨_, _, 3, _, _, GGTBTorRowAt.aInd (Or.inr ht) (by norm_num) ?_,
          Or.inl le_rfl⟩)
        simp [ggTorM, ht]
      · by_cases hr4 : r = 4
        · subst hr4
          exact Or.inr (Or.inr (Or.inl ⟨ht, rfl, rfl⟩))
        · by_cases hr5 : r = 5
          · subst hr5
            exact Or.inl ⟨Or.inl ⟨ht, rfl⟩, rfl⟩
          · have hr6 : 6 ≤ r := by omega
            by_cases h3 : 3 ∣ r + 1
            · refine Or.inr (Or.inl ⟨_, _, r, _, _, GGTBTorRowAt.aDep (Or.inr ht)
                (by dsimp only; omega) h3 ?_ (by dsimp only; rintro ⟨-, rfl, -⟩; omega),
                Or.inr ?_⟩)
              · simp [ggTorM, ht]
              · exact not_dvd_51840_of_seven_dvd (seven_dvd_card_coxeterA hr6)
            · refine Or.inr (Or.inl ⟨_, _, r, _, _, GGTBTorRowAt.aInd (Or.inr ht) h3 ?_,
                Or.inr ?_⟩)
              · simp [ggTorM, ht]
              · exact not_dvd_51840_of_seven_dvd (seven_dvd_card_coxeterA hr6)
    ·
      subst hr3
      refine Or.inr (Or.inl ⟨_, _, 3, _, _, GGTBTorRowAt.d (Or.inr ⟨ht, ?_, ?_⟩),
        Or.inl le_rfl⟩)
      · norm_num
      · exact ⟨1, by norm_num⟩
  ·
    obtain ⟨ht, hr, hodd, hpn⟩ := h
    by_cases hr5 : r = 5
    · subst hr5
      exact Or.inl ⟨Or.inr (Or.inr ⟨ht, rfl⟩), rfl⟩
    · have hr7 : 7 ≤ r := by
        rcases hodd with ⟨k, hk⟩
        omega
      refine Or.inr (Or.inl ⟨_, _, r, _, _, GGTBTorRowAt.d (Or.inr ⟨ht, hpn, hodd⟩),
        Or.inr ?_⟩)
      exact not_dvd_51840_of_seven_dvd (seven_dvd_card_coxeterD hr7)
  ·
    obtain ⟨ht, -⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨ht, rfl, by norm_num⟩)))
  ·
    obtain ⟨ht, hr, hev, hpn⟩ := h
    by_cases hr4 : r = 4
    · subst hr4
      exact Or.inl ⟨Or.inr (Or.inl ⟨ht, rfl⟩), rfl⟩
    · have hr6 : 6 ≤ r := by
        rcases hev with ⟨k, hk⟩
        omega
      refine Or.inr (Or.inl ⟨_, _, r, _, _, GGTBTorRowAt.d (Or.inl ⟨ht, Or.inr ⟨hpn, hev⟩⟩),
        Or.inr ?_⟩)
      rcases eq_or_lt_of_le hr6 with h6 | h7
      · subst h6
        exact not_dvd_51840_of_two_pow_nine_dvd two_pow_nine_dvd_card_coxeterD_six
      · exact not_dvd_51840_of_seven_dvd (seven_dvd_card_coxeterD (by dsimp only; omega))
  ·
    obtain ⟨ht, -⟩ := h
    refine Or.inr (Or.inl ⟨_, _, 7, _, _, GGTBTorRowAt.e7 ht ?_, Or.inr ?_⟩)
    · norm_num
    · exact not_dvd_51840_of_gt (by rw [card_coxeterE7_group]; norm_num)
  ·
    obtain ⟨ht, -⟩ := h
    refine Or.inr (Or.inl ⟨_, _, 8, _, _, GGTBTorRowAt.e8Three ht rfl, Or.inr ?_⟩)
    exact not_dvd_51840_of_gt (by rw [card_coxeterE8_group]; norm_num)
  ·
    obtain ⟨ht, -⟩ := h
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨ht, rfl, by norm_num⟩)))

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem GGSecFiveE6QTwoCfg.false_of_endRow
    (hW : GGTBTorWRows) (hLift : GGTBTorLiftRows) (hTBF : GGTBFixInput)
    (hC : GGSecFiveE6QTwoCfg 3 B Bs x L D J)
    (hL : GGInnerDiagOnLabel (fun p lab => ∃ (r m N : ℕ) (C : Matrix (Fin N) (Fin N) ℤ)
      (M : CoxeterMatrix (Fin N)), GGTBTorRowAt p lab r m N C M ∧
        (N ≤ 3 ∨ ¬ Nat.card M.Group ∣ 51840)) 3 Bs L) :
    False := by
  classical
  obtain ⟨hRest, -, -, hBs, -, -, horderx, -, hstar, -, -⟩ := e6QTwo_config_facts hC
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨lab, r, m, N, C, M, R, _instR, θ, I, hN, hperf, hlab, hrow, hP, hBsI, hlift, hT, -⟩ :=
    l05nPlQ_marking_with hW hLift (by norm_num : (3 : ℕ) ≠ 2)
      (fun _ _ N _ M => N ≤ 3 ∨ ¬ Nat.card M.Group ∣ 51840) hL
  obtain ⟨hom, hpm, -, hMC⟩ :=
    l05nPlP1_row_facts (p := 3) Nat.prime_three (by norm_num) hlab hrow
  have hTor : GGTorusTorData m N C M ↥L (ggGamma L hN).range :=
    hT ↥L (ggQuotHom θ) (ggGamma L hN).range
      (ggTorusTBGroup_of_L hRest.1 hperf θ hN hBsI hlift)
  have hWeyl : GGWeylOfType 3 M (ggAutomizer L Bs) :=
    NSJoin.weylOfType_of_torData (by norm_num : (3 : ℕ) ≠ 2) hom hpm hMC hBs hstar hN hTor
  have hFix := GGSecFiveE6QTwoCfg.fix hTBF hC
  rcases hP with hN3 | hndvd
  · let F₀ : Subgroup ↥Bs := (Subgroup.zpowers x).subgroupOf Bs
    have hfix : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer L Bs, ψ b = b) → b ∈ F₀ := by
      intro b hb
      exact Subgroup.mem_subgroupOf.mpr (hFix b hb)
    have hle := card_le_pow_mul_card_of_weylOfType hWeyl F₀ hfix
    rw [Fintype.card_fin] at hle
    have hF : Nat.card F₀ ≤ 3 := by
      rw [← horderx, ← Nat.card_zpowers]
      exact Nat.card_le_card_of_injective
        (fun b => (⟨((b : ↥Bs) : G), Subgroup.mem_subgroupOf.mp b.2⟩ : Subgroup.zpowers x))
        fun a b h => by
          have h' := congrArg Subtype.val h
          exact Subtype.ext (Subtype.ext h')
    have h4 : Nat.card Bs ≤ 3 ^ 4 := by
      calc Nat.card Bs ≤ 3 ^ N * Nat.card F₀ := hle
        _ ≤ 3 ^ 3 * 3 := Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hN3) hF
        _ = 3 ^ 4 := by norm_num
    have h5 := GGSecFiveE6QTwoCfg.three_pow_five_le_card hC
    omega
  · obtain ⟨A₀, hLle, -, -, hcardA₀, -⟩ := GGSecFiveE6QTwoCfg.exists_join hC
    obtain ⟨e, -⟩ := hWeyl
    have hdvd : Nat.card M.Group ∣ 51840 := by
      rw [Nat.card_congr e.toEquiv, ← hcardA₀]
      exact Subgroup.card_dvd_of_le hLle
    exact hndvd hdvd

end CFSG.StandardType

end
