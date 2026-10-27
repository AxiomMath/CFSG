module

public import CFSG.StandardComponent.AschbacherSeitz.BenderNF
public import CFSG.StandardComponent.AschbacherSeitz.SpClassical
public import CFSG.LocalAnalysis.ComponentClassification.AS81Open

public noncomputable section

namespace CFSG.StandardComponent.AschbacherSeitz

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.ComponentInitial LinearFlag
  FieldFourCover CFSG.LieType.Chevalley CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoSporadic
open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.RankTwoL3Even
open CFSG.ComponentClassification
open scoped MatrixGroups

section


theorem l3_part_one_of_foundationNF (h3 : AS76b.Section3Config) (h32 : AS76b.Lemma32)
    (h4 : AS76b.Asc75Theorem4) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHypNF G A → ∀ m : ℕ, 3 ≤ m →
      StatedClassicalModel (rankTwoQuot A) .PSL 3 2 m →
        standardComponentOddCore G = ⊥ → False := by
  intro G _ _ A hH m hm hQ hO
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, K, _, _, hK, ⟨e₀⟩⟩ := id hQ
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  have h4K : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : Group.IsPerfect (SL2 K) := isPerfect_SL2 h4K
  have : IsSimpleGroup (SL2 K) := RankTwoHypIIL3.isSimpleGroup_SL2 h4K
  let e : ↥A ⧸ center ↥A ≃* projectiveSL 3 K :=
    e₀.trans ((projectiveSpecialLinearGroupEquivStatedProj 3 K).symm.trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K))
  obtain ⟨ψ, hψ⟩ := exists_isActionHom
    (RankTwoHypIIY.autModel_mulAut (RankTwoHypIIL3.center_projectiveSL_three_eq_bot K))
    hH.standard.1.1 e
  have hA := hH.standard
  have hA31 : AS76b.Hyp31 A := ⟨hA, RankTwoHypIIL3.hypII_L3 hA.1.1 hm hQ, hO,
    lt_of_lt_of_le one_lt_two hH.rank, hH.not_normal⟩
  have hZ : Odd (Nat.card (A ⊓ centralizer (A : Set G) : Subgroup G)) := by
    rw [card_inf_centralizer_eq]
    exact odd_card_center_of_psl3 hA.1.1 hm hQ
  have hKey := odd_card_inf_rightConjugate_centralizer hA hψ hZ (h32 G A hA31) hm hK
  obtain ⟨g, hg, R, T, hR, hT, hTN, hRN, hTR, -, -⟩ := h3 G A hA31
  have htight := AS76b.tightlyEmbedded_centralizer hA
  have hR1 : R ≠ ⊥ := AS76b.isSylowOf_ne_bot_of_even hR htight.1
  have hT1 : T ≠ ⊥ :=
    AS76b.isSylowOf_ne_bot_of_even hT (by rw [rightConjugate_card]; exact htight.1)
  have hTR' : Nat.card T = Nat.card R := by rw [hT.card_eq, hR.card_eq, rightConjugate_card]
  have hTNR : T ≤ normalizer (R : Set G) :=
    (commutator_eq_bot_iff_le_centralizer.1 hTR).trans (Subgroup.centralizer_le_normalizer _)
  have hTAK : T ≤ A ⊔ centralizer (A : Set G) :=
    AS76b.lemma33Two_of h32 h4 AS76b.asc08Lemma34 G A hA31 R hR g hg T
      (hT.of_le (le_inf hT.le hTN) inf_le_left) hT1 hTNR hT
  have hTe := AS76b.isElemAbelian_of_isSylowOf_rightConjugate h32 hA31 hT
  obtain ⟨t₀, ht₀, ht₀1⟩ := T.bot_or_exists_ne_one.resolve_left hT1
  obtain ⟨γ, l, w, hwA, hl, hγ, hwψ, hwodd, hwt₀, hTc⟩ :=
    exists_frame hA hψ hZ hm hK hKey hg hT.le hTN hTAK hTe ht₀ ht₀1
  have : IsSimpleGroup (leviA γ) := isSimpleGroup_leviA γ
  have hZS : center (leviA γ) = ⊥ := center_leviA exists_mul_ne_mul_SL2 γ
  have hL : CFSG.Open.IsQuasisimple (leviLift ψ (leviA γ)) :=
    isQuasisimple_leviLift hψ (leviA_le_innerP γ) (commutator_leviA γ) hZS
  have hLA := leviLift_le_inf_centralizer hψ hwA hwψ
  have hRT := not_le_normalizer hA hψ hZ hm hK hKey hg hT.le hTN hTAK hTe hR hR1 hRN ht₀ ht₀1
    hwA hl hγ hwψ hwodd hwt₀
  obtain ⟨hstd, hnn⟩ := AS76b.lemma38_of_noConj_of_le h4 h32 AS76b.asc08Lemma34 hA31 hR
    ((zpowers_le).2 hwA) hL hLA (normalizer_inf_centralizer_le hwA hwψ hl)
    (isSylowOf_inf_centralizer hψ hwA hwψ hl hA hR hR1)
    (le_sup_leviLift hψ hZ hTN hTAK hTe hTR hR hTc)
    (le_bot_iff.1 ((inf_le_inf_left T leviLift_le).trans
      (inf_eq_bot_of_le_rightConjugate (hKey g) hT.isPGroup hT.le).le))
    hTR' hRT
    (fun U hU hU1 c hle => not_conj_le_of_le hKey (hR.isPGroup.to_le hU) (hU.trans hR.le) hU1 c
      (hle.trans leviLift_le))
  have hLW : leviLift ψ (leviA γ) ≤ centralizer (zpowers w : Set G) := hLA.trans inf_le_right
  have hH' : RankTwoHypNF (centralizer (zpowers w : Set G))
      ((leviLift ψ (leviA γ)).subgroupOf (centralizer (zpowers w : Set G))) :=
    ⟨hstd, hnn, two_le_pRank_centralizer_subgroupOf ((zpowers_le).2 hwA) leviLift_le hH.rank⟩
  obtain ⟨B, hB', hO', ⟨f⟩⟩ := RankTwoClassical.exists_rankTwoHypNF_quotient hH'
  let eL : rankTwoQuot ((leviLift ψ (leviA γ)).subgroupOf (centralizer (zpowers w : Set G))) ≃*
      SL2 K :=
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hLW) (Subgroup.map_center_eq _)).trans
      ((leviLiftQuotEquiv hψ (leviA_le_innerP γ) (commutator_leviA γ) hZS).trans
        (leviAEquiv γ).symm)
  have hSz := (rankTwoBenderStandardNF _ B hB' hO' (Or.inl ⟨m, hm,
    statedClassicalModel_of_mulEquiv_SL2 hm hK (f.symm.trans eL)⟩)).1
  apply not_three_dvd_card_of_suzukiModel_three hSz
  rw [Nat.card_congr (f.symm.trans eL).toEquiv]
  exact three_dvd_card_SL2

theorem l3_first_conjunct_of_foundationNF (h3 : AS76b.Section3Config) (h32 : AS76b.Lemma32)
    (h4 : AS76b.Asc75Theorem4) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHypNF G A → ∀ m : ℕ, 2 ≤ m →
      StatedClassicalModel (rankTwoQuot A) .PSL 3 2 m →
        standardComponentOddCore G = ⊥ → m = 2 := by
  intro G _ _ A hH m hm hQ hO
  by_contra hm2
  exact l3_part_one_of_foundationNF h3 h32 h4 G A hH m (by omega) hQ hO

theorem rankTwoL3EvenStandardNF :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), RankTwoHypNF G A →
      ∀ m : ℕ, 2 ≤ m → StatedClassicalModel (rankTwoQuot A) .PSL 3 2 m →
      (standardComponentOddCore G = ⊥ → m = 2) ∧
      (m = 2 →
        (NativeSporadic.IsSporadic (rankTwoX A ⧸ Subgroup.center (rankTwoX A)) .Suz ∧
          Nat.card (Subgroup.center (rankTwoX A)) ∣ 3) ∨
        (Nonempty (Subgroup.center A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
          NativeSporadic.IsSporadic (rankTwoX A) .He)) ∧
      (standardComponentOddCore G = ⊥ →
        NativeSporadic.IsSporadic (rankTwoX A) .Suz ∨
          (Nonempty (Subgroup.center A ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ∧
            NativeSporadic.IsSporadic (rankTwoX A) .He)) := by
  intro G _ _ A hH m hm hL
  have h3 := RankTwoFoundation.section3Config
  have h32 := RankTwoFoundation.lemma32
  have h4 := RankTwoFoundation.asc75Theorem4
  have hi : standardComponentOddCore G = ⊥ → m = 2 := fun hO =>
    l3_first_conjunct_of_foundationNF h3 h32 h4 G A hH m hm hL hO
  refine ⟨hi, fun hm2 => ?_, fun hO => ?_⟩
  · subst hm2
    exact AS81.l34GeneralNF G A hH hL
  · obtain rfl := hi hO
    exact RankTwoL3Four.oddCoreFreeConclusion_of_l34Conclusion hO
      (AS81.l34GeneralNF G A hH hL)

end

end CFSG.StandardComponent.AschbacherSeitz
