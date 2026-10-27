module

public import CFSG.RankThree.PartOne.FLM.OrdSmall
public import CFSG.RankThree.PartOne.S12K.Rigidity
public import CFSG.RankThree.PartOne.S12.InputsEleven
public import CFSG.RankThree.PartOne.KF.ClsCenter
public import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.RankThree.PartOne.FLM

open CFSG CFSG.Assembly.LowTwoRank CFSG.RankThree.PerfectCover CFSG.Timmesfeld
open CFSG.RankThree.PartOne.S12K (charTwoOrder card_of_lieModel_two)

theorem center_eq_bot_of_psl_two {E : Type} [Group E] {m : ℕ} (hm : m = 3 ∨ m = 4)
    (h : StatedClassicalModel E .PSL m 2 1) : Subgroup.center E = ⊥ := by
  obtain ⟨-, hs⟩ := CFSG.LieType.Simplicity.fam_PSL_simplicity E m 2 1 h
  have hcard : Nat.card E = CFSG.Open.ordA (m - 1) (2 ^ 1) :=
    (card_statedClassicalModel_two h).1 rfl
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center E) with h0 | h0
  · exact h0
  · exfalso
    have hc : IsMulCommutative E := Subgroup.center_eq_top_iff.1 h0
    have hp := Group.is_simple_iff_prime_card.1 hs
    rcases hm with rfl | rfl
    · rw [hcard, show CFSG.Open.ordA (3 - 1) (2 ^ 1) = 168 from ordA_two_one] at hp
      exact absurd hp (by norm_num)
    · rw [hcard, show CFSG.Open.ordA (4 - 1) (2 ^ 1) = 20160 from ordA_three_one] at hp
      exact absurd hp (by norm_num)

theorem statedClassicalModel_psl_of_mulEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B)
    {n p f : ℕ} (h : StatedClassicalModel B .PSL n p f) : StatedClassicalModel A .PSL n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm h

theorem card_multiplier_psl_four_one :
    Nat.card (Blueprint.Multiplier.generic .PSL 4 2 1 ×
      Blueprint.Multiplier.exceptional .PSL 4 2 1) = 2 := by
  have hgen : Blueprint.Multiplier.genericOrders .PSL 4 2 1 = (1, 1) := by
    change (Nat.gcd 4 (2 ^ 1 - 1), 1) = (1, 1)
    decide
  have hexc : Blueprint.Multiplier.exceptionalOrders .PSL 4 2 1 = (2, 1) := rfl
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp

theorem card_multiplier_psl_three_two :
    Nat.card (Blueprint.Multiplier.generic .PSL 3 2 2 ×
      Blueprint.Multiplier.exceptional .PSL 3 2 2) = 48 := by
  have hgen : Blueprint.Multiplier.genericOrders .PSL 3 2 2 = (3, 1) := by
    change (Nat.gcd 3 (2 ^ 2 - 1), 1) = (3, 1)
    decide
  have hexc : Blueprint.Multiplier.exceptionalOrders .PSL 3 2 2 = (4, 4) := rfl
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp

theorem card_multiplier_psl_seven {m : ℕ} (hm : m = 3 ∨ m = 4) :
    Nat.card (Blueprint.Multiplier.generic .PSL m 2 7 ×
      Blueprint.Multiplier.exceptional .PSL m 2 7) = 1 := by
  have hgen : Blueprint.Multiplier.genericOrders .PSL m 2 7 = (1, 1) := by
    change (Nat.gcd m (2 ^ 7 - 1), 1) = (1, 1)
    rcases hm with rfl | rfl <;> decide
  have hexc : Blueprint.Multiplier.exceptionalOrders .PSL m 2 7 = (1, 1) := by
    rcases hm with rfl | rfl <;> rfl
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hgen, hexc]
  simp

theorem center_eq_bot_of_psl_seven
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {X : Type} [Group X] [Finite X] {m : ℕ} (hm : m = 3 ∨ m = 4) (hperf : Group.IsPerfect X)
    (hmodel : StatedClassicalModel (X ⧸ Subgroup.center X) .PSL m 2 7) :
    Subgroup.center X = ⊥ := by
  have hm' : Models.LieModel (X ⧸ Subgroup.center X) .PSL m 2 7 := ⟨hmodel.1, .inl hmodel⟩
  obtain ⟨hperf', hcard⟩ := card_hopfMultiplier_of_model hGA hm'
  have hd := card_ker_dvd_card_hopfMultiplier hperf' hperf (QuotientGroup.mk' (Subgroup.center X))
    (QuotientGroup.mk'_surjective _) (by rw [QuotientGroup.ker_mk'])
  rw [QuotientGroup.ker_mk', hcard, card_multiplier_psl_seven hm] at hd
  rw [← Subgroup.card_eq_one]
  exact Nat.dvd_one.1 hd

theorem center_specialLinear_eq_bot {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2 ^ 7)
    {m : ℕ} (hm : m = 3 ∨ m = 4) :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin m) F) = ⊥ := by
  have := Fintype.ofFinite F
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    rcases hm with rfl | rfl <;> simp at hr
  have h127 : r ^ 127 = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one r hr0
    rwa [Fintype.card_eq_nat_card, hF] at h
  have hr1 : r = 1 := by
    have hg : r ^ Nat.gcd m 127 = 1 := pow_gcd_eq_one.2 ⟨hr, h127⟩
    rcases hm with rfl | rfl <;> simpa using hg
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hrA, hr1]
  simp

theorem nonempty_projectiveSL_equiv_specialLinear {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ 7) {m : ℕ} (hm : m = 3 ∨ m = 4) :
    Nonempty
      (Matrix.ProjectiveSpecialLinearGroup (Fin m) F ≃* Matrix.SpecialLinearGroup (Fin m) F) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq (center_specialLinear_eq_bot hF hm)).trans
    QuotientGroup.quotientBot⟩

theorem ordTits_ne_small : CFSG.Open.ordTits ≠ 168 ∧ CFSG.Open.ordTits ≠ 20160 := by
  unfold CFSG.Open.ordTits
  decide

section Main


theorem field_lm_model_core
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {G : Type} [Group G] [Finite G] (K E : Subgroup G) {m : ℕ} (hm : m = 3 ∨ m = 4)
    (hK : CFSG.IsQuasisimple ↥K) (t : StatedLieTag) (n f : ℕ)
    (hKm : Blueprint.LieModel (↥K ⧸ Subgroup.center ↥K) t n 2 (7 * f))
    (hEm : Blueprint.LieModel (↥E ⧸ Subgroup.center ↥E) t n 2 f ∨
      (t = .twistedF4 ∧ n = 0 ∧ f = 1 ∧
        Blueprint.LieModel (↥E ⧸ Subgroup.center ↥E) .Tits 0 2 1))
    (hmod : StatedClassicalModel ↥E .PSL m 2 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ 7 ∧
      Nonempty (↥K ≃* Matrix.SpecialLinearGroup (Fin m) F) := by
  have hZE : Subgroup.center ↥E = ⊥ := center_eq_bot_of_psl_two hm hmod
  let eE : ↥E ⧸ Subgroup.center ↥E ≃* ↥E :=
    (QuotientGroup.quotientMulEquivOfEq hZE).trans QuotientGroup.quotientBot
  have hcardE : Nat.card (↥E ⧸ Subgroup.center ↥E) = charTwoOrder .PSL m 1 := by
    rw [Nat.card_congr eE.toEquiv]
    exact (card_statedClassicalModel_two hmod).1 rfl
  have hsmall : charTwoOrder .PSL m 1 = 168 ∨ charTwoOrder .PSL m 1 = 20160 := by
    rcases hm with rfl | rfl
    · exact Or.inl charTwoOrder_psl_three_one
    · exact Or.inr charTwoOrder_psl_four_one
  have hadmord : StatedLieAdmissible t n 2 f ∧ charTwoOrder t n f = charTwoOrder .PSL m 1 := by
    rcases hEm with hEm | ⟨rfl, rfl, rfl, hT⟩
    · obtain ⟨hadm, hc⟩ := card_of_lieModel_two hEm
      exact ⟨hadm, hc.symm.trans hcardE⟩
    · exfalso
      have hc := (card_of_lieModel_two hT).2
      have h2 : CFSG.Open.ordTits = charTwoOrder .PSL m 1 := hc.symm.trans hcardE
      rcases hsmall with h | h
      · exact ordTits_ne_small.1 (h2.trans h)
      · exact ordTits_ne_small.2 (h2.trans h)
  obtain ⟨hadm, hord⟩ := hadmord
  have h2 : charTwoOrder t n f = 168 ∨ charTwoOrder t n f = 20160 := by
    rw [hord]
    exact hsmall
  have hmain : t = .PSL ∧ n = m ∧ f = 1 := by
    rcases small_of_charTwoOrder hadm h2 with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · rcases hm with rfl | rfl
      · exact ⟨rfl, rfl, rfl⟩
      · exfalso
        rw [charTwoOrder_psl_three_one, charTwoOrder_psl_four_one] at hord
        exact absurd hord (by norm_num)
    · rcases hm with rfl | rfl
      · exfalso
        rw [charTwoOrder_psl_four_one, charTwoOrder_psl_three_one] at hord
        exact absurd hord (by norm_num)
      · exact ⟨rfl, rfl, rfl⟩
    · exfalso
      rcases hm with rfl | rfl
      · rw [charTwoOrder_psl_three_two, charTwoOrder_psl_three_one] at hord
        exact absurd hord (by norm_num)
      · have hc : StatedClassicalModel (↥E ⧸ Subgroup.center ↥E) .PSL 3 2 2 := by
          rcases hEm with hEm | ⟨h, -⟩
          · rcases hEm with ⟨-, hc⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
            · exact hc
            all_goals exact absurd h (by norm_num)
          · cases h
        have hc' : StatedClassicalModel ↥E .PSL 3 2 2 :=
          statedClassicalModel_psl_of_mulEquiv eE.symm hc
        have h1 : Models.LieModel ↥E .PSL 4 2 1 := ⟨hmod.1, .inl hmod⟩
        have h3 : Models.LieModel ↥E .PSL 3 2 2 := ⟨hc'.1, .inl hc'⟩
        have c1 := (card_hopfMultiplier_of_model hGA h1).2
        have c2 := (card_hopfMultiplier_of_model hGA h3).2
        rw [card_multiplier_psl_four_one] at c1
        rw [card_multiplier_psl_three_two] at c2
        omega
  obtain ⟨rfl, hn, rfl⟩ := hmain
  rw [hn] at hKm
  have hKmodel : StatedClassicalModel (↥K ⧸ Subgroup.center ↥K) .PSL m 2 7 := by
    rcases hKm with ⟨-, hc⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · simpa using hc
    all_goals omega
  have hZK : Subgroup.center ↥K = ⊥ := center_eq_bot_of_psl_seven hGA hm hK.1 hKmodel
  obtain ⟨-, F, hFfield, hFfin, hFcard, ⟨e⟩⟩ := hKmodel
  obtain ⟨e2⟩ := nonempty_projectiveSL_equiv_specialLinear hFcard hm
  let eK : ↥K ⧸ Subgroup.center ↥K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hZK).trans QuotientGroup.quotientBot
  exact ⟨F, hFfield, hFfin, hFcard, ⟨eK.symm.trans (e.trans
    ((projectiveSpecialLinearGroupEquivStatedProj m F).symm.trans e2))⟩⟩

theorem field_lm_model_aux
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {G : Type} [Group G] [Finite G] (c : G) (K : Subgroup G) {m : ℕ} (hm : m = 3 ∨ m = 4)
    (hK : CFSG.IsQuasisimple ↥K) (hind : InducesFieldAut 7 c K)
    (hmod : StatedClassicalModel
      ↥(inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({c} : Set G))) .PSL m 2 1) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ 7 ∧
      Nonempty (↥K ≃* Matrix.SpecialLinearGroup (Fin m) F) := by
  obtain ⟨-, -, -, t, n, f, -, hKm, hEm⟩ := hind
  exact field_lm_model_core hGA K _ hm hK t n f hKm hEm hmod

end Main

end CFSG.RankThree.PartOne.FLM
