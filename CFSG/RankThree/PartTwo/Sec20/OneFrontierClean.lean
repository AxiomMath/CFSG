module

public import CFSG.RankThree.PartTwo.Sec20.OneFrontierCleanStatements
public import CFSG.RankThree.PartTwo.Sec20.Item204OneProof
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_of_item202One (h202 : Item202One) {A M L N : Subgroup G} {c : G}
    (h : Hyp201One G A M L N c) {R' : Subgroup G} (hR'1 : R' ≠ ⊥) (hR'2 : IsPGroup 2 R')
    (hAK : A ⊔ kTwenty M c ≤ Subgroup.normalizer (R' : Set G)) :
    Subgroup.normalizer (R' : Set G) ≤ M := by
  obtain ⟨M', hM', hNM'⟩ := exists_mem_scriptM_of_isTwoLocal
    (X := ((A ⊔ kTwenty M c : Subgroup G) : Set G)) ⟨R', hR'1, hR'2, rfl⟩ hAK
  rw [h202 G A M L N c h] at hM'
  rw [← hM']
  exact hNM'

theorem item204One_of_steps_clean (h202 : Item202One) (h2031 : Item203One1)
    (h2032 : Item203One2) (h184_5 : Sec18.Item184_5) (h184_6 : Sec18.Item184_6)
    (h189 : Sec18.Item189) (h1810 : Sec18.Item1810Hyp) (hnormal : Step204Normal)
    (hrest : Step204Rest) : Item204One := by
  intro G _ _ A M L N c T hT
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := kTwenty M c with hKdef
  set R := CFSG.Open.pCoreOf 2 (K ⊔ T) with hRdef
  have hKM : K ≤ M := kTwenty_le_of_hyp201 hT.toHyp201
  have hMK : M ≤ Subgroup.normalizer (K : Set G) := le_normalizer_normalClosureIn M c
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hB := h2031 G A M L N c hT.hyp201One
  have hQ8 := h2032 G A M L N c hT.hyp201One
  obtain ⟨i, j, hij, hi3, hj3, hi1, hj1, hi, hj⟩ := hnormal G A M L N c T hT hB hQ8
  have hAK : ∀ k : Fin 4, K ⊔ A ⊔ T ≤ Subgroup.normalizer (Sec18.fourChar R k : Set G) →
      A ⊔ K ≤ Subgroup.normalizer (Sec18.fourChar R k : Set G) := fun k hk =>
    (sup_le (le_sup_right.trans le_sup_left) (le_sup_left.trans le_sup_left)).trans hk
  have hNi := normalizer_le_of_item202One h202 hT.hyp201One hi1
    (hR2.to_le (fourChar_le R i)) (hAK i hi)
  have hNj := normalizer_le_of_item202One h202 hT.hyp201One hj1
    (hR2.to_le (fourChar_le R j)) (hAK j hj)
  have hmax := pCoreOf_mem_maxInvariant hT.toCtx20 hNi
  have hNR : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    ((normalizer_le_normalizer_fourChar R i).trans hNi).trans hMK
  obtain ⟨H, hH18, hH187, hL, hN⟩ := exists_sec18H_of_ctx20One hT
  obtain ⟨⟨hKC, hKN⟩, hWc, hcase⟩ := h189 G A M H c hH18 hH187
  rw [← hL, ← hN] at hKN hcase
  have hkType : (∃ n : ℕ, Odd n ∧ Nonempty (K ⧸ CFSG.pCore 2 K ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n))) ∨
      (∃ n : ℕ, Even n ∧ 0 < n ∧ Nonempty (K ⧸ CFSG.pCore 2 K ≃*
        CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n))) := by
    rcases hcase with ⟨n, hn, hiso, -⟩ | ⟨n, hn, hn0, hiso, -⟩
    · exact Or.inl ⟨n, hn, hiso⟩
    · exact Or.inr ⟨n, hn, hn0, hiso⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 (Subgroup.normalizer (A : Set G))
  have hPG := h184_6 G A M H c hH18 P hP
  have hconj := h1810 G A M H c hH18 hH187 P hP
  have hcA : c ∈ A := mem_of_hyp201 hT.toHyp201
  rcases h184_5 G A M H c hH18 P hP with ⟨-, homega, hfrat⟩ | ⟨-, h9, hAP, -, -⟩
  · have hset : Setting204 G A M L N c T i j P :=
      { toCtx20 := hT.toCtx20
        one_of_L2 := fun _ => hT.one
        ne := hij
        ne_three_left := hi3
        ne_three_right := hj3
        normal_left := hi
        normal_right := hj
        normalizer_left := hNi
        normalizer_right := hNj
        maxInvariant := hmax
        normalizer_le := hNR
        mem_oTwoComponentsIn := hKC
        not_le := hKN
        kType := hkType
        sylow_normalizer := hP
        sylow_top := hPG
        conjugatesIn_eq := hconj
        normalizer_A := hWc
        omegaOne := homega
        not_mem_frattini := hfrat }
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hT.mem_scriptM.1, ?_⟩, ?_⟩
    · intro x hx
      exact sup_le hKM hT.sylow.le hx
    · exact hrest G A M L N c T i j P hset
  · exact (not_case_two hcA hconj hAP h9).elim

theorem item209One_of_steps_clean (h207 : Item207One) (h208 : Item208One) (hV : Step209V)
    (hL : Step209L) : Item209One := by
  intro G _ _ A M L N c T hT hTN
  have h7 := h207 G A M L N c T hT hTN
  have h8 := h208 G A M L N c T hT hTN
  have hVX := hV G A M L N c T hT hTN h7 h8
  have hLX := hL G A M L N c T hT hTN h7 h8
  exact le_bot_iff.mp (hLX ▸ Subgroup.commutator_mono le_rfl hVX)

end CFSG.RankThree.PartTwo.Sec20
