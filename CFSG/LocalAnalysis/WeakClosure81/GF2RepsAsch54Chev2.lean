module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2Defs
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Chev2L0
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC

import CFSG.LocalAnalysis.QuasithinUnique.K1.Glue
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CalL0
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54BorelRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanRankLargeHolds
import CFSG.Quasithin.H13.KGFact22Tor
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54Defs
import CFSG.Blueprint.LieModelAPI

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

theorem pRank_normalizerQuotient_le_normalizer {X : Type} [Group X] [Finite X]
    (S : Subgroup X) (hS : IsPGroup 2 S) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient S)) ≤
      CFSG.Open.pRank p (Subgroup.normalizer (S : Set X)) := by
  classical
  let B : Subgroup X := Subgroup.normalizer (S : Set X)
  let Ssub : Subgroup B := S.subgroupOf B
  let f : B →* TauCeti.Subgroup.normalizerQuotient S :=
    TauCeti.Subgroup.normalizerQuotientMk S
  have hker : f.ker = Ssub := TauCeti.Subgroup.normalizerQuotientMk_ker S
  have hsurj : Function.Surjective f := TauCeti.Subgroup.normalizerQuotientMk_surjective S
  have hsub : IsPGroup 2 Ssub :=
    hS.of_equiv (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := S))).symm
  have hcard : Nat.card Ssub = Nat.card S :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer (H := S))).toEquiv
  have hnd : ¬ p ∣ Nat.card Ssub := by
    rw [hcard]
    exact CFSG.QuasithinUnique.K1.not_dvd_card_of_isPGroup_two hS hp hp2
  let e : TauCeti.Subgroup.normalizerQuotient S ≃* (B ⧸ Ssub) :=
    ((QuotientGroup.quotientMulEquivOfEq hker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective f hsurj)).symm
  calc CFSG.Open.pRank p (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient S))
      = CFSG.Open.pRank p (⊤ : Subgroup (B ⧸ Ssub)) :=
        CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e
    _ ≤ CFSG.Open.pRank p B :=
        CFSG.QuasithinUnique.K1.pRank_top_quotient_le B Ssub hp hnd
    _ = CFSG.Open.pRank p (Subgroup.normalizer (S : Set X)) := rfl

theorem admissible_two_parameter_cases {t : CFSG.Open.StatedLieTag} {n f : ℕ}
    (hadm : CFSG.Open.StatedLieAdmissible t n 2 f) :
    (3 ≤ f ∨ t = .trialityD4 ∨
      f = 2 ∧ (t = .PSU ∧ (n = 4 ∨ n = 5) ∨ t = .POmegaMinus ∧ n = 4)) ∨
    Asch58Parabolic t n f ∨
    (f = 2 ∧ (t = .PSU ∧ 8 ≤ n ∨ t = .POmegaMinus ∧ 5 ≤ n ∨ t = .twistedE6)) ∨
    (f = 2 ∧ t = .PSU ∧ (n = 6 ∨ n = 7)) := by
  rcases hadm with ⟨-, hf1, hadm⟩
  by_cases hf3 : 3 ≤ f
  · exact Or.inl (Or.inl hf3)
  have hf12 : f = 1 ∨ f = 2 := by omega
  cases t with
  | PSL =>
      rcases hf12 with rfl | rfl
      · exact Or.inr (Or.inl (by simp [Asch58Parabolic]))
      · exact Or.inr (Or.inl (by simp [Asch58Parabolic]))
  | PSU =>
      have hn3 : 3 ≤ n := hadm.1
      rcases hf12 with rfl | rfl
      · exact Or.inr (Or.inl (by simp [Asch58Parabolic]))
      · by_cases hn4 : n ≤ 3
        · have hn : n = 3 := by omega
          exact Or.inr (Or.inl (by simp [Asch58Parabolic, hn]))
        · by_cases hn6 : n ≤ 5
          · exact Or.inl (Or.inr (Or.inr ⟨rfl, Or.inl ⟨rfl, by omega⟩⟩))
          · by_cases hn8 : n ≤ 7
            · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl, by omega⟩))
            · exact Or.inr (Or.inr (Or.inl
                ⟨rfl, Or.inl ⟨rfl, by omega⟩⟩))
  | PSp =>
      rcases hf12 with rfl | rfl
      · exact Or.inr (Or.inl (by simp [Asch58Parabolic]))
      · exact Or.inr (Or.inl (by simp [Asch58Parabolic]))
  | POmegaOdd =>
      exact absurd rfl hadm.2
  | POmegaPlus =>
      rcases hf12 with rfl | rfl
      · exact Or.inr (Or.inl (by simp [Asch58Parabolic]))
      · exact Or.inr (Or.inl (by simp [Asch58Parabolic]))
  | POmegaMinus =>
      have hn4 : 4 ≤ n := hadm
      rcases hf12 with rfl | rfl
      · exact Or.inr (Or.inl (by simp [Asch58Parabolic]))
      · by_cases hn : n = 4
        · exact Or.inl (Or.inr (Or.inr ⟨rfl, Or.inr ⟨rfl, hn⟩⟩))
        · exact Or.inr (Or.inr (Or.inl
            ⟨rfl, Or.inr (Or.inl ⟨rfl, by omega⟩)⟩))
  | G2 =>
      rcases hf12 with rfl | rfl
      · exact Or.inr (Or.inl (by simp [Asch58Parabolic]))
      · exact Or.inr (Or.inl (by simp [Asch58Parabolic]))
  | F4 =>
      rcases hf12 with rfl | rfl
      · exact Or.inr (Or.inl (by simp [Asch58Parabolic]))
      · exact Or.inr (Or.inl (by simp [Asch58Parabolic]))
  | E6 =>
      rcases hf12 with rfl | rfl
      · exact Or.inr (Or.inl (by simp [Asch58Parabolic]))
      · exact Or.inr (Or.inl (by simp [Asch58Parabolic]))
  | E7 =>
      rcases hf12 with rfl | rfl
      · exact Or.inr (Or.inl (by simp [Asch58Parabolic]))
      · exact Or.inr (Or.inl (by simp [Asch58Parabolic]))
  | E8 =>
      rcases hf12 with rfl | rfl
      · exact Or.inr (Or.inl (by simp [Asch58Parabolic]))
      · exact Or.inr (Or.inl (by simp [Asch58Parabolic]))
  | twistedE6 =>
      rcases hf12 with rfl | rfl
      · exact Or.inr (Or.inl (by simp [Asch58Parabolic]))
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr rfl)⟩))
  | trialityD4 =>
      exact Or.inl (Or.inr (Or.inl rfl))
  | twistedB2 =>
      exact absurd hadm.2.2.2 hf3
  | twistedG2 =>
      exact absurd hadm.2.1 (by norm_num)
  | twistedF4 =>
      exact absurd hadm.2.2.2 hf3
  | Tits =>
      exact Or.inr (Or.inl (by simp [Asch58Parabolic, hadm.2.2]))


theorem pRank_three_normalizer_of_rank {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) {t : StatedLieTag} {n : ℕ}
    (hm : CFSG.Models.LieModel X t n 2 2) (htneq : t ≠ .Tits)
    (hrank : 4 ≤ CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank t n) :
    3 < CFSG.Open.pRank 3 (⊤ : Subgroup X) ∧
      ∀ S : Sylow 2 X, 3 < CFSG.Open.pRank 3 (Subgroup.normalizer ((S : Subgroup X) : Set X)) := by
  have hbm : CFSG.Blueprint.LieModel X t n 2 2 :=
    blueprintLieModel_of_models_of_ne_tits hm htneq
  obtain ⟨hq, hZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup (Q := X) hnab
  have hq' : CFSG.Open.IsQuasisimple X :=
    ⟨Group.isPerfect_def.mp hq.1, hq.2.1⟩
  have hL : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) t n 2 2 :=
    CFSG.Blueprint.LieModel.quotient_center hZ hbm
  have hodd : Odd (Nat.card (Subgroup.center X)) := by
    rw [hZ]
    simp
  have hsum : ∀ S : Sylow 2 X,
      3 < CFSG.Open.pRank 3 (Subgroup.normalizer ((S : Subgroup X) : Set X)) := by
    intro S
    have hS : CFSG.QuasithinUnique.IsSylowTwoOf (S : Subgroup X) ⊤ :=
      CFSG.Quasithin.H13.KG22.isSylowTwoOf_of_sylow S
    obtain ⟨r, hrp, hr2, hrdvd, hbig⟩ :=
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.k_CartanRankLarge_holds
        X t n 2 hm.1 (by norm_num : 2 < 2 ^ 2) hL hq' hodd (S : Subgroup X) hS hrank
    have hdvd3 : r ∣ 3 := by
      norm_num at hrdvd ⊢
      exact hrdvd
    have hr3 : r = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h | h
      · exact absurd h hrp.ne_one
      · exact h
    rw [hr3] at hbig
    have hlift := pRank_normalizerQuotient_le_normalizer (S := (S : Subgroup X))
      S.isPGroup' (p := 3) Nat.prime_three (by norm_num)
    exact lt_of_lt_of_le hbig hlift
  have htop : 3 < CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
    obtain ⟨S₀⟩ := Sylow.nonempty (p := 2) (G := X)
    exact lt_of_lt_of_le (hsum S₀)
      (CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) le_top)
  exact ⟨htop, hsum⟩

theorem pRank_three_normalizer_of_cartanRankLarge {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a) {t : StatedLieTag} {n : ℕ}
    (hm : CFSG.Models.LieModel X t n 2 2)
    (ht : t = .PSU ∧ 8 ≤ n ∨ t = .POmegaMinus ∧ 5 ≤ n ∨ t = .twistedE6) :
    3 < CFSG.Open.pRank 3 (⊤ : Subgroup X) ∧
      ∀ S : Sylow 2 X, 3 < CFSG.Open.pRank 3 (Subgroup.normalizer ((S : Subgroup X) : Set X)) := by
  refine pRank_three_normalizer_of_rank hnab hm ?_ ?_
  · rintro rfl
    simp at ht
  · rcases ht with ⟨rfl, hn⟩ | ⟨rfl, hn⟩ | rfl
    · simp [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank]
      omega
    · simp [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank]
      omega
    · simp [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank]

theorem asch54Chev2_of (hS : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hPar : Asch54Case fun X _ =>
      ∃ t n f, CFSG.Models.LieModel X t n 2 f ∧ Asch58Parabolic t n f)
    (hU : Asch58UnitaryFive) : Asch54Chev2 := by
  intro Q _ _ L T hKQ hLn hLs hLnab hC hP hL0 hT hnu
  have hL0facts : ∀ (L : Type) [Group L], IsCalL0 L →
      ∃ _ : Finite L, 3 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup L) ∧
        ∃ a b : L, a * b ≠ b * a :=
    fun X _ hX => CFSG.LocalAnalysis.UniquenessCase.UC22.uc22lb_listB_facts
      CFSG.LocalAnalysis.UniquenessCase.UC22.listBExceptionalFacts
      ((isCalL0_iff_asc1930ListB X).1 hX)
  obtain ⟨t, n, f, hm⟩ := hP
  have hadm : CFSG.Open.StatedLieAdmissible t n 2 f := hm.1
  rcases admissible_two_parameter_cases hadm with hA | hB | hC | hD
  · exact absurd (isCalL0_of_lieModel_two hm hA) hL0
  · exact hPar Q L T hKQ hLn hLs hLnab hC ⟨t, n, f, hm, hB⟩ hL0 hT hnu
  · obtain ⟨hf, ht⟩ := hC
    subst f
    refine asch54Case_of_pRank_normalizer hS hL0facts (P := fun X _ =>
      (∃ t n f, CFSG.Models.LieModel X t n 2 f ∧
        (f = 2 ∧ (t = .PSU ∧ 8 ≤ n ∨ t = .POmegaMinus ∧ 5 ≤ n ∨ t = .twistedE6))) ∧
        IsSimpleGroup X ∧ ∃ a b : X, a * b ≠ b * a) ?_ Q L T hKQ hLn hLs hLnab hC
      ⟨⟨t, n, 2, hm, ⟨rfl, ht⟩⟩, hLs, hLnab⟩ hL0 hT hnu
    intro X _ _ ⟨⟨t', n', f', hmX, hf', ht'⟩, hsimpleX, hnabX⟩
    subst f'
    have h :=
      letI : IsSimpleGroup X := hsimpleX
      pRank_three_normalizer_of_cartanRankLarge hnabX hmX ht'
    exact ⟨3, Nat.prime_three, by norm_num, h.1,
      fun S => lt_trans (by norm_num : 1 < 3) (h.2 S)⟩
  · obtain ⟨hf, ht, hn⟩ := hD
    subst f
    subst t
    refine asch54Case_of_pRank_normalizer hS hL0facts (P := fun X _ =>
      ∃ n : ℕ, (n = 6 ∨ n = 7) ∧ CFSG.Models.LieModel X .PSU n 2 2) ?_ Q L T hKQ hLn
      hLs hLnab hC ⟨n, hn, hm⟩ hL0 hT hnu
    intro X _ _ ⟨n', hn', hmX⟩
    exact ⟨5, by norm_num, by norm_num, hU X n' hn' hmX⟩

end CFSG.LocalAnalysis.WeakClosure81
