module

public import CFSG.RankThree.PartTwo.Sec20.Item2012
public import CFSG.RankThree.PartTwo.Sec20.Contra

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

@[expose] def Item204Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20 G A M L N c T → Hyp1921 G A M N L →
      scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G) = {M}

@[expose] def Item205Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20 G A M L N c T → Hyp1921 G A M N L →
      ¬ CFSG.ABGLocalTools.IsSylowOf 2 T ⊤ ∧
      (∀ C : Subgroup T, C.Characteristic → C ≠ ⊥ →
        ¬ kTwenty M c ⊔ T ≤ Subgroup.normalizer ((C.map T.subtype : Subgroup G) : Set G)) ∧
      (∃ n : ℕ, Odd n ∧ Nonempty (kTwenty M c ⧸ CFSG.pCore 2 (kTwenty M c) ≃*
        CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n))) ∧
      ¬ 2 ∣ (M ⊓ N).relIndex M ∧
      ∃ T' : Subgroup G, Ctx20 G A M L N c T' ∧ T' ≤ N

@[expose] def Item208Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20 G A M L N c T → Hyp1921 G A M N L → T ≤ N →
      IsBlock M (kTwenty M c) ∧ vTwenty M c T = CFSG.Open.pCoreOf 2 (kTwenty M c) ∧
        ∃ n : ℕ, Odd n ∧ IsNaturalL3Module (kTwenty M c) (vTwenty M c T) n

@[expose] def Item209Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20 G A M L N c T → Hyp1921 G A M N L → T ≤ N → ⁅L, vTwenty M c T⁆ = ⊥

variable {G : Type} [Group G] [Finite G]

theorem false_of_ctx20_of_not_le {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (h204 : scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G) = {M})
    (h208 : IsBlock M (kTwenty M c) ∧ vTwenty M c T = CFSG.Open.pCoreOf 2 (kTwenty M c) ∧
      ∃ n : ℕ, Odd n ∧ IsNaturalL3Module (kTwenty M c) (vTwenty M c T) n)
    (h209 : ⁅L, vTwenty M c T⁆ = ⊥) (hLM : ¬ L ≤ M) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hVeq, n, -, -, F, _, _, hF, -, -, -, β, -⟩ := h208
  have hV2 : IsPGroup 2 (vTwenty M c T) :=
    hVeq ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (kTwenty M c)
  have hV1 : vTwenty M c T ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card (Multiplicative (Fin 3 → F)) = Nat.card (vTwenty M c T) :=
      Nat.card_congr β.symm.toEquiv
    rw [hbot, Subgroup.card_bot] at hcard
    have h3 : Nat.card (Multiplicative (Fin 3 → F)) = (2 ^ n) ^ 3 := by
      rw [Nat.card_congr Multiplicative.ofAdd.symm, Nat.card_eq_fintype_card,
        Fintype.card_fun, Fintype.card_fin, hF]
    rw [h3] at hcard
    have h1 : 1 < (2 ^ n) ^ 3 :=
      Nat.one_lt_pow (by norm_num) (Nat.one_lt_two_pow_iff.mpr (by
        rintro rfl
        have : Fintype.card F = 1 := by rw [hF, pow_zero]
        exact absurd this (Fintype.one_lt_card).ne'))
    omega
  have hKT : kTwenty M c ⊔ T ≤ Subgroup.normalizer (vTwenty M c T : Set G) := by
    rw [hVeq]
    refine (sup_le ?_ (hT.sylow.le.trans (le_normalizer_normalClosureIn M c))).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
    exact Subgroup.le_normalizer
  obtain ⟨M', hM', hNM'⟩ := exists_mem_scriptM_of_isTwoLocal (X := ((kTwenty M c ⊔ T :
    Subgroup G) : Set G)) ⟨_, hV1, hV2, rfl⟩ hKT
  rw [h204, Set.mem_singleton_iff] at hM'
  have hLN : L ≤ Subgroup.normalizer (vTwenty M c T : Set G) :=
    le_trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h209)
      (Subgroup.centralizer_le_normalizer _)
  exact hLM (hM' ▸ hLN.trans hNM')

theorem false_of_hyp201_of_hyp1921 (h204 : Item204Two) (h205 : Item205Two) (h208 : Item208Two)
    (h209 : Item209Two) {A M L N : Subgroup G} {c : G} (h : Hyp201 G A M L N c)
    (hyp : Hyp1921 G A M N L) (hLM : ¬ L ≤ M) : False := by
  obtain ⟨T₀, hT₀⟩ := exists_ctx20 h
  obtain ⟨-, -, -, -, T, hT, hTN⟩ := h205 G A M L N c T₀ hT₀ hyp
  exact false_of_ctx20_of_not_le hT (h204 G A M L N c T hT hyp) (h208 G A M L N c T hT hyp hTN)
    (h209 G A M L N c T hT hyp hTN) hLM

theorem not_hyp1921_of_two (h204 : Item204Two) (h205 : Item205Two) (h208 : Item208Two)
    (h209 : Item209Two) (h1922 : Item1922) {A M N L : Subgroup G} :
    ¬ Hyp1921 G A M N L := fun hyp => by
  obtain ⟨⟨c, hc⟩, hLM⟩ := h1922 G A M N L hyp
  exact false_of_hyp201_of_hyp1921 h204 h205 h208 h209 (L := L) (N := N) (c := c)
    { toPartTwoStanding := hyp.toPartTwoStanding
      partTwoS_eq := hyp.partTwoS_eq
      mem_partTwoE := hyp.mem_partTwoE
      mem_scriptM := hyp.mem_scriptM
      cases := Or.inr hyp
      centralizer_eq := hc } hyp hLM

end CFSG.RankThree.PartTwo.Sec20
