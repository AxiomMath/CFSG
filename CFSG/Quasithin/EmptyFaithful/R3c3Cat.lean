module

public import CFSG.Quasithin.EmptyFaithful.R3c3Base
public import CFSG.Quasithin.EmptyFaithful.R3c3Rank
public import CFSG.Quasithin.EmptyFaithful.R3c3Lie
public import CFSG.Quasithin.EmptyFaithful.R3c3Spor
public import CFSG.Quasithin.EmptyFaithful.R3c3L2p
public import CFSG.Quasithin.EmptyFaithful.SzN2Main
public import CFSG.RankThree.PartTwo.Sec3.OrderThreeFixedPointFreeModule
public import CFSG.RankThree.PartTwo.Sec4.LThreePiKind
public import CFSG.Quasithin.EmptyFaithful.R3c2List
public import CFSG.Quasithin.EmptyFaithful.T1515eE

public section

namespace CFSG.Quasithin.R3c3

open CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.R3c2
open scoped MatrixGroups

theorem isSz_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {f : ℕ} (h : IsSz f Y) :
    IsSz f X := by
  obtain ⟨hp, a, ha, K, _, _, hf, hK, ⟨e'⟩⟩ := h
  exact ⟨hp, a, ha, K, inferInstance, inferInstance, hf, hK, ⟨e.trans e'⟩⟩

theorem fermat_mersenne_cases {p : ℕ} (hFM : Ch1.IsFermatOrMersennePrime p) (h3 : p ≠ 3) :
    p = 5 ∨ p = 7 ∨ 17 ≤ p := by
  obtain ⟨hp, hform⟩ := hFM
  rcases hform with ⟨k, hk⟩ | ⟨k, hk2, hk⟩
  · rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · simp at hk
        omega
      · left
        simpa using hk
    · right
      right
      have h4 : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      have h16 : 2 ^ 4 ≤ 2 ^ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h4
      omega
  · rcases Nat.lt_or_ge k 5 with hk5 | hk5
    · interval_cases k
      · simp at hk
        omega
      · right
        left
        simpa using hk
      · simp at hk
        subst hk
        exact absurd hp (by norm_num)
    · right
      right
      have h32 : 2 ^ 5 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk5
      have hpos : 1 ≤ 2 ^ k := Nat.one_le_two_pow
      omega

section CaseA

variable {G : Type} [Group G] [Finite G]

theorem rankOne_of_lemma115LieCharTwo {L P Q : Subgroup G} (hs : IsSimpleGroup ↥L)
    (hp : Group.IsPerfect ↥L) (hnoSz : ¬ ∃ e : ℕ, IsSz e ↥L) (hrk : CFSG.Open.pRank 3 L = 1)
    (hQL : Q ≤ L) (hQs : Group.IsSolvable ↥Q) (hP : IsSylowTwoOf P L) (hPQ : P ≤ Q)
    (h3Q : 3 ∣ Nat.card ↥Q) (hlie : Lemma115LieCharTwo ↥L) : RankOneConcl ↥L := by
  have hE9 : ∀ {Y : Type} [Group Y] [Finite Y], (↥L ≃* Y) →
      2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup Y) → RankOneConcl ↥L := fun e h =>
    (false_of_two_le_top hrk e h).elim
  rcases hlie with ((⟨f, hfam⟩ | hTits) | ⟨n, hn, hPSL⟩) | ⟨⟨e⟩⟩ | hU33
  · rcases hfam with ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ | ⟨hf, hm⟩ |
      ⟨hodd, hf, hm⟩ | ⟨hodd, hf, hm⟩
    ·
      rcases Nat.even_or_odd f with hev | hodd
      · exact Or.inl ⟨f, hev, hm⟩
      · exfalso
        have hf3 : 3 ≤ f := by
          obtain ⟨k, hk⟩ := hodd
          omega
        obtain ⟨-, K, _, hKfin, hK, ⟨e⟩⟩ := hm
        have : Fintype K := Fintype.ofFinite K
        have : CharP K 2 := R3c.charP_two_of_natCard_eq_two_pow hK
        have hscal : ∀ c : Kˣ, c ^ 2 = 1 → c = 1 := fun c hc => eq_one_of_sq_eq_one_charTwo hc
        let eSL : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
          (quotPCoreEquivOfSimple hs hp).trans
            (e.trans ((statedProjStatedSLEquiv hscal).trans
              (CFSG.RankThree.PartTwo.Sec4.statedSLEquiv 2 K)))
        exact solvOvergroupsThreePrime_holds G L P Q
          ⟨f, K, inferInstance, inferInstance, hodd, hf3,
            by rw [← Nat.card_eq_fintype_card, hK], Or.inl ⟨eSL⟩⟩ hP hPQ hQL hQs h3Q
    ·
      by_cases hf1 : f = 1
      · subst hf1
        exact Or.inr (Or.inr hm)
      · have hf2 : 2 ≤ f := by omega
        rcases Nat.even_or_odd f with hev | hodd
        · exact hE9 (MulEquiv.refl _) (two_le_pRank_three_isPSL_three_two_even hev hm)
        · exfalso
          have hf3 : 3 ≤ f := by
            obtain ⟨k, hk⟩ := hodd
            omega
          obtain ⟨-, K, _, hKfin, hK, ⟨e⟩⟩ := hm
          have : Fintype K := Fintype.ofFinite K
          have h3 : ¬ 3 ∣ Nat.card K - 1 := by
            rw [hK]
            have := R3c.two_pow_mod_three_of_odd hodd
            omega
          have hscal : ∀ c : Kˣ, c ^ 3 = 1 → c = 1 := fun c hc =>
            eq_one_of_cube_eq_one_of_not_dvd h3 hc
          let eSL : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(StatedSL 3 K) :=
            (quotPCoreEquivOfSimple hs hp).trans (e.trans (statedProjStatedSLEquiv hscal))
          exact solvOvergroupsThreePrime_holds G L P Q
            ⟨f, K, inferInstance, inferInstance, hodd, hf3,
              by rw [← Nat.card_eq_fintype_card, hK], Or.inr ⟨eSL⟩⟩ hP hPQ hQL hQs h3Q
    ·
      rcases Nat.even_or_odd f with hev | hodd
      · exact Or.inr (Or.inl ⟨f, hev, hm⟩)
      · exact hE9 (MulEquiv.refl _) (two_le_pRank_three_isPSU_two_odd hodd hm)
    · exact hE9 (MulEquiv.refl _) (two_le_pRank_three_isPSp_two hm)
    · exact hE9 (MulEquiv.refl _) (two_le_pRank_three_isG2 hm)
    · exact hE9 (MulEquiv.refl _) (two_le_pRank_three_is3D4 hm)
    · exact hE9 (MulEquiv.refl _) (two_le_pRank_three_is2F4 hm)
    · exact (hnoSz ⟨f, hm⟩).elim
  · exact hE9 (MulEquiv.refl _) (two_le_pRank_three_isTits hTits)
  · exact hE9 (MulEquiv.refl _) (two_le_pRank_three_isPSL_two_one hn hPSL)
  · exact hE9 (MulEquiv.refl _) (two_le_pRank_three_alt (by norm_num) e)
  · exact hE9 (MulEquiv.refl _) (CFSG.Quasithin.two_le_pRank_of_isPSU_three_three1515e hU33)

end CaseA

section CaseE

variable {G : Type} [Group G] [Finite G]

theorem rankOne_of_lemma115CaseE {L P Q : Subgroup G} (hp : Group.IsPerfect ↥L)
    (hrk : CFSG.Open.pRank 3 L = 1) (hQL : Q ≤ L) (hQs : Group.IsSolvable ↥Q)
    (hP : IsSylowTwoOf P L) (hPQ : P ≤ Q) (h3Q : 3 ∣ Nat.card ↥Q)
    (hE : StatedClassicalModel ↥L .PSL 3 3 1 ∨
      ∃ p : ℕ, Ch1.IsFermatOrMersennePrime p ∧ StatedClassicalModel ↥L .PSL 2 p 1) :
    RankOneConcl (↥L ⧸ Subgroup.center ↥L) := by
  rcases hE with hL33 | ⟨p, hFM, hm⟩
  · exact (false_of_two_le_top hrk (MulEquiv.refl _)
      (two_le_pRank_three_isPSL_three_three hL33)).elim
  · have hp3 : p ≠ 3 := by
      rintro rfl
      obtain ⟨⟨-, -, -, -, h23⟩, -⟩ := hm
      exact h23 (by simp)
    have hcases := fermat_mersenne_cases hFM hp3
    have hp2 : p ≠ 2 := by omega
    obtain ⟨K, _, _, _, e, hcard, -, -⟩ := CFSG.QuasithinUnique.K1.psl2_model_data hp2 hm
    have : Finite K := Finite.of_fintype K
    have hK : Nat.card K = p := by rw [Nat.card_eq_fintype_card, hcard, pow_one]
    rcases hcases with rfl | rfl | h17
    · have hs : IsSimpleGroup ↥L :=
        have : IsSimpleGroup PSL(2, K) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
          (by omega)
        e.isSimpleGroup
      exact RankOneConcl.of_mulEquiv (quotCenterEquivOfSimple hs hp).symm (Or.inl ⟨2, even_two,
        CFSG.RankThree.PartTwo.Sec3.statedClassicalModel_psl_two_four_of_five hm
          (by norm_num)⟩)
    · have hs : IsSimpleGroup ↥L :=
        have : IsSimpleGroup PSL(2, K) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
          (by omega)
        e.isSimpleGroup
      exact RankOneConcl.of_mulEquiv (quotCenterEquivOfSimple hs hp).symm (Or.inr (Or.inr
        (CFSG.RankThree.PartTwo.Sec3.statedClassicalModel_psl_three_two_of_seven hm
          (by norm_num))))
    · exfalso
      have : Fact p.Prime := ⟨hFM.1⟩
      have H : Unc25Small.L2pHyp K p :=
        ⟨by omega, hK, Unc25K1.fermat_or_mersenne_pow hFM (by omega)⟩
      exact not_three_dvd_of_solvable_sylow_of_mulEquiv H h17 e hP hPQ hQL hQs h3Q

end CaseE

section Main

theorem rankOneListCatalogue_holds : RankOneListCatalogue := by
  intro G _ _ L z hcases hq hcen hnoSz hrk ⟨Q, hQL, hQs, ⟨P, hP, hPQ⟩, h3Q⟩
  rcases hcases with ⟨hs, hlie, -⟩ | ⟨-, -, hL34, -⟩ | ⟨φ, σ, -, -, -⟩ | ⟨φ, σ, -, -, -⟩ |
    ⟨hE, -⟩ | ⟨⟨s, hs, ⟨e⟩⟩, -⟩
  ·
    have hp : Group.IsPerfect ↥L := hq.1
    let eC := quotCenterEquivOfSimple hs hp
    have hnoSz' : ¬ ∃ e : ℕ, IsSz e ↥L := fun ⟨e, he⟩ => hnoSz ⟨e, isSz_of_mulEquiv eC he⟩
    exact RankOneConcl.of_mulEquiv eC.symm
      (rankOne_of_lemma115LieCharTwo hs hp hnoSz' hrk hQL hQs hP hPQ h3Q hlie)
  ·
    exfalso
    rw [R3c.pRank_three_eq_pCore_quotient L] at hrk
    rcases hL34 with hm | hm
    · have := two_le_pRank_three_isPSL_three_two_even (n := 2) ⟨1, rfl⟩ hm
      omega
    · have := two_le_pRank_three_isG2 hm
      omega
  ·
    exact (false_of_two_le_quotient hcen hrk φ (two_le_pRank_three_alt (n := 6) (by norm_num)
      (MulEquiv.refl _))).elim
  ·
    exact (false_of_two_le_quotient hcen hrk φ (two_le_pRank_three_alt (n := 7) (by norm_num)
      (MulEquiv.refl _))).elim
  ·
    exact rankOne_of_lemma115CaseE hq.1 hrk hQL hQs hP hPQ h3Q hE
  ·
    exfalso
    rw [R3c.pRank_three_eq_pCore_quotient L] at hrk
    have := two_le_pRank_three_of_lemma115SporadicName hs e
    omega

end Main

end CFSG.Quasithin.R3c3
