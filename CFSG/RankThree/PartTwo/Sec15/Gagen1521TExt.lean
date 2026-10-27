module

public import CFSG.RankThree.PartTwo.Sec15.Gagen1521TDefs
public import CFSG.RankThree.PartTwo.Sec15.Ronan152StellIIIKP
import CFSG.RankThree.PartTwo.Sec16.Item165ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1521T

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank
  CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

theorem exists_ext1521 {A : Subgroup G} (hsimp : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {P X₁ : Subgroup G} (hX₁ : X₁ ∈ scriptY2 A)
    (hPX₁ : P ≤ X₁) : ∃ X T : Subgroup G, Ext1521 A P X T := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Set (Subgroup G × Subgroup G) :=
    {q | q.1 ∈ scriptY2 A ∧ P ≤ q.1 ∧ q.2 ∈ scriptQPi A (lB A) q.1 (piOf 2)}
  have hSfin : S.Finite := Set.toFinite S
  have hbotQ : (⊥ : Subgroup G) ∈ scriptQ A (lB A) :=
    ⟨bot_mem_invariantPiSubgroups ⊤ A (piCompl 3), fun _ _ => by simp⟩
  have hbotPi : IsPiSubgroup (piOf 2) (⊥ : Subgroup G) :=
    (bot_mem_invariantPiSubgroups ⊤ A (piOf 2)).2.1
  have hSne : S.Nonempty :=
    ⟨(X₁, ⊥), hX₁, hPX₁, ⟨⟨hbotQ, bot_le⟩, hbotPi⟩⟩
  obtain ⟨⟨X₀, T₀⟩, hS₀, hmax₀⟩ :=
    Set.exists_max_image S (fun q => Nat.card q.2) hSfin hSne
  let S' : Set (Subgroup G × Subgroup G) := {q ∈ S | Nat.card q.2 = Nat.card T₀}
  have hS'fin : S'.Finite := hSfin.subset (fun _ hq => hq.1)
  have hS'ne : S'.Nonempty := ⟨(X₀, T₀), hS₀, rfl⟩
  obtain ⟨⟨X, T⟩, hS', hmax'⟩ :=
    Set.exists_max_image S' (fun q => Nat.card q.1) hS'fin hS'ne
  have hX : X ∈ scriptY2 A := hS'.1.1
  have hPX : P ≤ X := hS'.1.2.1
  have hT : T ∈ scriptQPi A (lB A) X (piOf 2) := hS'.1.2.2
  have hcardT : Nat.card T = Nat.card T₀ := hS'.2
  refine ⟨X, T, hX, hPX, hT, ?_, ?_⟩
  ·
    intro X' hX' hPX' T' hT'
    simpa only [hcardT] using hmax₀ (X', T') (show (X', T') ∈ S from ⟨hX', hPX', hT'⟩)
  ·
    set V : Subgroup G := CFSG.Open.pCoreOf 2 X with hVdef
    have hVne : V ≠ ⊥ := by rw [hVdef]; exact hX.2
    have hV2 : IsPGroup 2 V := by
      rw [hVdef]; exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
    have hXX' : X ≤ Subgroup.normalizer (V : Set G) := by
      rw [hVdef]; exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
    have hAV : A ≤ Subgroup.normalizer (V : Set G) :=
      hX.1.2.trans (by
        rw [hVdef]; exact CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
    have hX'ne : Subgroup.normalizer (V : Set G) ≠ ⊤ :=
      normalizer_ne_top_of_isPGroup hsimp hnab hVne hV2
    have hAX' : A ≤ Subgroup.normalizer (Subgroup.normalizer (V : Set G) : Set G) :=
      hAV.trans Subgroup.le_normalizer
    have hVle : V ≤ Subgroup.normalizer (V : Set G) := Subgroup.le_normalizer
    have hVcore : V ≤ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (V : Set G)) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVle le_rfl hV2
    have hcore : CFSG.Open.pCoreOf 2 (Subgroup.normalizer (V : Set G)) ≠ ⊥ := by
      intro h0
      rw [h0] at hVcore
      exact hVne (le_bot_iff.mp hVcore)
    have hX'mem : Subgroup.normalizer (V : Set G) ∈ scriptY2 A :=
      ⟨⟨hX'ne, hAX'⟩, hcore⟩
    have hPX' : P ≤ Subgroup.normalizer (V : Set G) := hPX.trans hXX'
    have hT' : T ∈ scriptQPi A (lB A) (Subgroup.normalizer (V : Set G)) (piOf 2) :=
      ⟨⟨hT.1.1, hT.1.2.trans hXX'⟩, hT.2⟩
    have hcardX' : Nat.card (Subgroup.normalizer (V : Set G)) ≤ Nat.card X :=
      hmax' (Subgroup.normalizer (V : Set G), T)
        ⟨show (Subgroup.normalizer (V : Set G), T) ∈ S from ⟨hX'mem, hPX', hT'⟩, hcardT⟩
    have heq : X = Subgroup.normalizer (V : Set G) :=
      Subgroup.eq_of_le_of_card_ge hXX' hcardX'
    exact le_of_eq heq.symm

theorem mem_scriptQPiStar_top_of_ext1521 (hst : StellmacherKP) (hR : TheoremFourHyp G)
    {A : Subgroup G} (hsimp : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    {P X T : Subgroup G} (hE : Ext1521 A P X T) (hT1 : T ≠ ⊥)
    (hTsyl : CFSG.Open.fusionIsSylowIn 2 T (P ⊔ T)) (h3 : ¬ 3 ∣ Nat.card ↥(P ⊔ T))
    (hchar : IsCharacteristicP 2 ↥(P ⊔ T)) :
    T ∈ scriptQPiStar A (lB A) ⊤ (piOf 2) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := isPGroup_of_mem_scriptQPi Nat.prime_two hE.mem_t
  set C : Subgroup G := CFSG.RankThree.PartTwo.Sec16.Proof165.stellmacherSub T with hCdef
  have hspec := CFSG.RankThree.PartTwo.Sec16.Proof165.stellmacherSub_spec hst hR hT2 hT1
  rw [← hCdef] at hspec
  obtain ⟨hCT, hC1, hNTC, hU⟩ := hspec
  have hPTC : P ⊔ T ≤ Subgroup.normalizer (C : Set G) :=
    hU (P ⊔ T) le_sup_right h3 hTsyl hchar
  have hPC : P ≤ Subgroup.normalizer (C : Set G) := (le_sup_left : P ≤ P ⊔ T).trans hPTC
  have hTC : T ≤ Subgroup.normalizer (C : Set G) := (le_sup_right : T ≤ P ⊔ T).trans hPTC
  have hC2 : IsPGroup 2 C := hT2.to_le hCT
  have hCne : Subgroup.normalizer (C : Set G) ≠ ⊤ :=
    normalizer_ne_top_of_isPGroup hsimp hnab hC1 hC2
  have hAC : A ≤ Subgroup.normalizer (Subgroup.normalizer (C : Set G) : Set G) :=
    (hE.mem_t.1.1.1.2.2.trans hNTC).trans Subgroup.le_normalizer
  have hCcore : C ≤ CFSG.Open.pCoreOf 2 (Subgroup.normalizer (C : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hC2
  have hcore : CFSG.Open.pCoreOf 2 (Subgroup.normalizer (C : Set G)) ≠ ⊥ := by
    intro h0
    rw [h0] at hCcore
    exact hC1 (le_bot_iff.mp hCcore)
  have hX'mem : Subgroup.normalizer (C : Set G) ∈ scriptY2 A :=
    ⟨⟨hCne, hAC⟩, hcore⟩
  have hT'X' : T ∈ scriptQPi A (lB A) (Subgroup.normalizer (C : Set G)) (piOf 2) :=
    ⟨⟨hE.mem_t.1.1, hTC⟩, hE.mem_t.2⟩
  refine ⟨⟨⟨hE.mem_t.1.1, le_top⟩, hE.mem_t.2⟩, ?_⟩
  intro T' hT' hTT'
  by_contra hnot
  have hlt : T < T' := lt_of_le_of_ne hTT' fun h => hnot (le_of_eq h.symm)
  have hT'2 : IsPGroup 2 T' := isPGroup_of_mem_scriptQPi Nat.prime_two hT'
  obtain ⟨x, hxT', hxT, hxN⟩ := exists_mem_normalizer_not_mem_of_lt hT'2 hlt
  let N : Subgroup G := T' ⊓ Subgroup.normalizer (T : Set G)
  have hTN : T ≤ N := le_inf hTT' Subgroup.le_normalizer
  have hxN' : x ∈ N := ⟨hxT', hxN⟩
  have hltN : T < N := by
    refine lt_of_le_of_ne hTN fun h => ?_
    rw [← h] at hxN'
    exact hxT hxN'
  have hNle : N ≤ T' := inf_le_left
  have hNQ : N ∈ scriptQ A (lB A) := by
    refine mem_scriptQ_of_le hT'.1.1 hNle ?_
    have hAT' : A ≤ Subgroup.normalizer (T' : Set G) := hT'.1.1.1.2.2
    have hANT : A ≤ Subgroup.normalizer (Subgroup.normalizer (T : Set G) : Set G) :=
      hE.mem_t.1.1.1.2.2.trans Subgroup.le_normalizer
    exact (le_inf hAT' hANT).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hN2 : IsPGroup 2 N := hT'2.to_le hNle
  have hNpi : IsPiSubgroup (piOf 2) N :=
    (isPiSubgroup_piOf_iff Nat.prime_two N).mpr hN2
  have hNle' : N ≤ Subgroup.normalizer (C : Set G) :=
    (inf_le_right : N ≤ Subgroup.normalizer (T : Set G)).trans hNTC
  have hNmem : N ∈ scriptQPi A (lB A) (Subgroup.normalizer (C : Set G)) (piOf 2) :=
    ⟨⟨hNQ, hNle'⟩, hNpi⟩
  have hcardN : Nat.card N ≤ Nat.card T := hE.card_le _ hX'mem hPC N hNmem
  exact absurd hcardN (not_le.mpr (Subgroup.card_lt_of_lt hltN))

end CFSG.RankThree.PartTwo.Sec15.Proof1521T
