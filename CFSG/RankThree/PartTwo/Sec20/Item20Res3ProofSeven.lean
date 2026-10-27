module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res2ProofSeven
public import CFSG.RankThree.PartTwo.Sec18.Statements
public import CFSG.RankThree.PartTwo.Sec18.SimsItem186HStatement
import CFSG.RankThree.PartTwo.Sec18.Item182
import CFSG.RankThree.PartTwo.Sec20.OneBasics
public import CFSG.RankThree.PartTwo.Sec20.Alt20

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

@[expose] def Step207K0Sub : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → T ≤ N →
    ¬ kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N →
    ⁅zTwenty T, normalClosureIn (kTwenty M c ⊓ N) c⁆ ≠ ⊥ →
    L ≤ Subgroup.centralizer
      ((⁅zTwenty T, normalClosureIn (kTwenty M c ⊓ N) c⁆ : Subgroup G) : Set G) →
    ∀ H ∈ scriptHStar A M, L = inSubgroup perfectResidual H →
      ∃ K₀ X : Subgroup G, K₀ ≤ kTwenty M c ∧
        kTwenty M c ≤ K₀ ⊔ CFSG.Open.pCoreOf 2 (kTwenty M c) ∧
        X ≠ ⊤ ∧ H ≤ X ∧ K₀ ≤ X

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_kTwenty_le_N_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (hTN : T ≤ N) :
    CFSG.Open.pCoreOf 2 (kTwenty M c) ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM : kTwenty M c ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hMK : M ≤ Subgroup.normalizer (kTwenty M c : Set G) := le_normalizer_normalClosureIn M c
  have hTM : T ≤ M := hT.sylow.le
  have hQT : CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T) ≤ T :=
    pCoreOf_le_of_isSylowOf (hT.sylow.of_le le_sup_right (sup_le hKM hTM))
  refine (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 (kTwenty M c)).trans le_sup_left) ?_
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (kTwenty M c))).trans (hQT.trans hTN)
  exact sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (kTwenty M c))
    ((hTM.trans hMK).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (kTwenty M c)))

theorem pCoreOf_kTwenty_le_N {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20One G A M L N c T) (hTN : T ≤ N) :
    CFSG.Open.pCoreOf 2 (kTwenty M c) ≤ N :=
  pCoreOf_kTwenty_le_N_core hT.toCtx20 hTN

theorem step207K0_of_sub (h186 : Sec18.Item186H) (hsub : Step207K0Sub) : Step207K0 := by
  intro G _ _ A M L N c T hT hTN hne hE hLE
  obtain ⟨H, hH18, h7, hL, hN⟩ := exists_sec18H_of_ctx20One hT
  obtain ⟨K₀, X, -, hKK₀, hXtop, hHX, hK₀X⟩ := hsub G A M L N c T hT hTN hne hE hLE H h7.1 hL
  obtain ⟨-, -, hscriptN, -⟩ := h186 G A M H c hH18 h7
  obtain ⟨Y, hY, hXY⟩ := (eq_top_or_exists_le_coatom X).resolve_left hXtop
  have hYN : Y = N := by
    have hmem : Y ∈ scriptN (H : Set G) := ⟨hY, fun h hh => hXY (hHX hh)⟩
    rw [hscriptN, Set.mem_singleton_iff] at hmem
    rw [hmem, hN, hL]
  rw [hYN] at hXY
  exact hKK₀.trans (sup_le (hK₀X.trans hXY) (pCoreOf_kTwenty_le_N hT hTN))

end CFSG.RankThree.PartTwo.Sec20
