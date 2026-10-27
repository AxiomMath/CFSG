module

public import CFSG.RankThree.PartTwo.Sec18.Item189Glue
import CFSG.RankThree.PartTwo.Late.Item2010
import CFSG.RankThree.PartTwo.Sec19.O2Centralizer

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

@[expose] def Step189O2BoundSplit : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Sec18H G A M H c →
    Hyp187 A M H c → CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)) = ⊥ →
    inSubgroup (CFSG.pPrimeCore 3) (Subgroup.centralizer ({c} : Set G)) ≠
      inSubgroup (CFSG.pPrimeCore 3) (Subgroup.centralizer ({c} : Set G) ⊓ M) →
    ∀ L₁ ∈ oTwoComponentsIn (Subgroup.centralizer ({c} : Set G)), ∀ S₁ : Subgroup G,
      CFSG.ABGLocalTools.IsSylowOf 2 S₁
        (inSubgroup (CFSG.pPrimeCore 3) (Subgroup.centralizer ({c} : Set G) ⊓ M)) →
      L₁ ⊔ A ⊔ S₁ ∈ scriptH A M →
        Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({c} : Set G)) ≤ 2

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_inf_centralizer_eq_bot189 {M : Subgroup G} {a : G}
    (hbot : CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({a} : Set G)) = ⊥)
    (heq : inSubgroup (CFSG.pPrimeCore 3) (Subgroup.centralizer ({a} : Set G)) =
      inSubgroup (CFSG.pPrimeCore 3) (Subgroup.centralizer ({a} : Set G) ⊓ M)) :
    CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer ({a} : Set G) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := Subgroup.centralizer ({a} : Set G) with hX
  set R := CFSG.Open.pCoreOf 2 M ⊓ X with hRdef
  have hR2 : IsPGroup 2 R := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_left
  have hRXM : R ≤ X ⊓ M :=
    le_inf inf_le_right (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 M))
  have hXMR : X ⊓ M ≤ Subgroup.normalizer (R : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hx.2, Subgroup.le_normalizer hx.1⟩
  have hcop : Nat.Coprime 3 (Nat.card R) := by
    obtain ⟨k, hk⟩ := hR2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hRY : R ≤ inSubgroup (CFSG.pPrimeCore 3) (X ⊓ M) :=
    le_inSubgroup_pPrimeCore_of hcop hRXM hXMR
  set Y := inSubgroup (CFSG.pPrimeCore 3) X with hY
  have hRY' : R ≤ Y := heq ▸ hRY
  have hYXM : Y ≤ X ⊓ M := heq ▸ Subgroup.map_subtype_le _
  have hRO : R ≤ CFSG.Open.pCoreOf 2 Y :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRY' (hYXM.trans hXMR) hR2
  have hOY : CFSG.Open.pCoreOf 2 Y ≤ CFSG.Open.pCoreOf 2 X :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans (Subgroup.map_subtype_le _))
      ((le_normalizer_inSubgroup_pPrimeCore 3 X).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
  exact le_bot_iff.mp (hbot ▸ hRO.trans hOY)

theorem step189O2Bound_of (h181 : Item181_1) (h184 : Item184_1)
    (hsplit : Step189O2BoundSplit) : Step189O2Bound := by
  intro G _ _ A M H c h h7 hbot
  by_cases heq : inSubgroup (CFSG.pPrimeCore 3) (Subgroup.centralizer ({c} : Set G)) =
      inSubgroup (CFSG.pPrimeCore 3) (Subgroup.centralizer ({c} : Set G) ⊓ M)
  · rw [pCoreOf_inf_centralizer_eq_bot189 hbot heq, Subgroup.card_bot]
    norm_num
  · have : IsSimpleGroup G := h.isSimpleGroup
    have hA := isE27_of_mem_partTwoE h.mem_partTwoE
    have hcA := mem_of_sec18H189 h
    have hAX : A ≤ Subgroup.centralizer ({c} : Set G) := Sec19.le_centralizer_of_mem hA.1.1 hcA
    have hc1 : c ≠ 1 := by
      rintro rfl
      obtain ⟨c', hc'3, hc'⟩ := (h184 G A M h.toSec18Std H h.mem_scriptH).2
      have hmem : c' ∈ (Subgroup.zpowers (1 : G) : Set G) := by
        rw [← h.centralizer_eq, hc']
        exact Subgroup.mem_zpowers c'
      rw [Subgroup.zpowers_one_eq_bot, SetLike.mem_coe, Subgroup.mem_bot] at hmem
      rw [hmem, orderOf_one] at hc'3
      exact absurd hc'3 (by norm_num)
    have hXtop : Subgroup.centralizer ({c} : Set G) ≠ ⊤ :=
      Sec19.centralizer_ne_top h.nonabelian hc1
    obtain ⟨L₁, hL₁, S₁, hS₁, hH₁⟩ := h181 G A M h.toSec18Std _ hAX hXtop heq
    exact hsplit G A M H c h h7 hbot heq L₁ hL₁ S₁ hS₁ hH₁

end CFSG.RankThree.PartTwo.Sec18
