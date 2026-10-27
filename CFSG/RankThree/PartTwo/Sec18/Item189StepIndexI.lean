module

public import CFSG.RankThree.PartTwo.Sec18.Item189StepL4
import CFSG.RankThree.PartTwo.Sec18.Item189StepProofOddL2

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def Step189MKTwoI : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Setting189 G A M H c →
    Case189i M H c → CFSG.Open.pCoreOf 2 (Subgroup.centralizer ({c} : Set G)) = ⊥ →
    (∃ n : ℕ, Nonempty (↥(kAlpha189 M H c) ≃* projSL 2 (GaloisField 2 n))) →
      ¬ 4 ∣ (normalClosureIn M c ⊔ (M ⊓ n189 H)).relIndex M

variable {G : Type} [Group G] [Finite G]

theorem odd_relIndex_of_case189i (h186 : Item186H) (h187 : Item187) {A M H : Subgroup G} {c : G}
    (h : Sec18H G A M H c) (h7 : Hyp187 A M H c) (hi : Case189i M H c) :
    ¬ 2 ∣ (normalClosureIn M c ⊓ n189 H).relIndex (normalClosureIn M c) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [relIndex_inf_n189_eq_index189 (theta189_le_n189 h187 h h7)]
  set J := ((normalClosureIn M c ⊓ n189 H).subgroupOf (sk189 M H c)).map (alpha189 M H c)
  have hsyl := (hi : CFSG.ABGLocalTools.IsSylowOf 2 (sAlpha189 M H c) ⊤).inf_of_le_normalizer
    le_top (Subgroup.normalizer_eq_top_iff.mpr (kAlpha189_normal M H c)).ge
  obtain ⟨Q, hQ⟩ := hsyl.exists_sylow_eq_subgroupOf
  have hle : ((sAlpha189 M H c ⊓ kAlpha189 M H c).subgroupOf (kAlpha189 M H c)) ≤
      J.subgroupOf (kAlpha189 M H c) := by
    intro y hy
    have hyS : (y : SKAlpha189 M H c) ∈ sAlpha189 M H c := hy.1
    exact kAlpha_inf_normalizer_le189
      (fun x hx => mem_n189_of_mem_normalizer_sAlpha h186 h187 h h7 hx)
      ⟨y.2, Subgroup.le_normalizer hyS⟩
  rw [← hQ] at hle
  exact fun h2 => Q.not_dvd_index (h2.trans (Subgroup.index_dvd_of_le hle))

theorem step189IndexI_of (h186 : Item186H) (h187 : Item187) (hMK : Step189MKTwoI) :
    Step189IndexI := by
  intro G _ _ A M H c hset hi hO hL2
  have h := hset.toSec18H
  have h7 := hset.hyp187
  rw [relIndex_inf_eq_mul189 (normalClosureIn_le_of_sec18H189 h)
    (Sec20.le_normalizer_normalClosureIn M c)]
  have hMK4 := hMK G A M H c hset hi hO hL2
  have hodd := odd_relIndex_of_case189i h186 h187 h h7 hi
  intro h4
  have hcop : Nat.Coprime 4 ((normalClosureIn M c ⊓ n189 H).relIndex (normalClosureIn M c)) :=
    Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  exact hMK4 (hcop.dvd_of_dvd_mul_right h4)

end CFSG.RankThree.PartTwo.Sec18
