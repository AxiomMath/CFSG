module

public import CFSG.RankThree.PartTwo.Sec19.Hyp1921Basic
public import CFSG.RankThree.PartTwo.Sec19.Hyp1921Quot
public import CFSG.RankThree.PartTwo.Sec19.Hyp1921Normal
public import CFSG.RankThree.PartTwo.Sec19.Hyp1921Sylow
public import CFSG.RankThree.PartTwo.Sec19.Hyp1921Centralizer
public import CFSG.RankThree.PartTwo.Sec19.Hyp1921Coprime
public import CFSG.RankThree.PartTwo.Sec19.Hyp1921Frattini
public import CFSG.RankThree.PartTwo.Sec20.Item2012
import CFSG.RankThree.PartTwo.Sec18.Tools
public import CFSG.RankThree.PartTwo.Late.GammaZero

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type} [Group G] [Finite G] {A M N L : Subgroup G}

theorem Hyp1921.le_normalizer (h : Hyp1921 G A M N L) : N ≤ Subgroup.normalizer (L : Set G) :=
  h.le_normalizer_of h.exists_elemAbelian_card_nine fun _ hx hc =>
    h.mem_pCoreOf_of_commutator_mem hx hc

theorem Hyp1921.normalizer_eq (h : Hyp1921 G A M N L) :
    Subgroup.normalizer (L : Set G) = N :=
  h.normalizer_eq_of h.le_normalizer

theorem Hyp1921.pCoreOf_le_M (h : Hyp1921 G A M N L) : CFSG.Open.pCoreOf 2 L ≤ M :=
  h.pCoreOf_le_M_of h.le_normalizer

theorem Hyp1921.le_normalizer_A (h : Hyp1921 G A M N L) : A ≤ Subgroup.normalizer (L : Set G) :=
  h.le_N.trans h.le_normalizer

theorem Hyp1921.isSylowOf_inf_Q (h : Hyp1921 G A M N L) {Q : Subgroup G}
    (hQ : IsSylowOf 3 Q N) : IsSylowOf 3 (Q ⊓ L) L :=
  h.isSylowOf_inf_Q_of h.le_normalizer hQ

theorem Hyp1921.card_inf_Q (h : Hyp1921 G A M N L) {Q : Subgroup G} (hQ : IsSylowOf 3 Q N) :
    Nat.card (Q ⊓ L : Subgroup G) = 9 :=
  h.card_inf_Q_of h.le_normalizer hQ

theorem Hyp1921.isElemAbelian_inf_Q (h : Hyp1921 G A M N L) {Q : Subgroup G}
    (hQ : IsSylowOf 3 Q N) : CFSG.Open.IsElemAbelian 3 (Q ⊓ L : Subgroup G) :=
  h.isElemAbelian_of_card_eq_nine inf_le_right (h.card_inf_Q hQ)

theorem Hyp1921.exists_ne_one_mem_sectionCentralizer (h : Hyp1921 G A M N L) :
    ∃ c ∈ sectionCentralizer A L (CFSG.Open.pCoreOf 2 L), c ≠ 1 :=
  h.exists_ne_one_mem_sectionCentralizer_of h.le_normalizer_A

theorem Hyp1921.orderOf_eq_three (h : Hyp1921 G A M N L) {c : G}
    (hc : sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) = (Subgroup.zpowers c : Set G)) :
    orderOf c = 3 :=
  h.orderOf_eq_three_of h.le_normalizer_A hc

theorem Hyp1921.le_M_of_rank_two (h : Hyp1921 G A M N L) {X : Subgroup G} (hXA : X ≤ A)
    (hX2 : 2 ≤ CFSG.Open.pRank 3 X)
    (hXc : ∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L) : L ≤ M :=
  h.le_M_of_rank_two_of h.le_normalizer h.pCoreOf_le_M hXA hX2 hXc

theorem Hyp1921.not_mem_of_mem_sectionCentralizer (h : Hyp1921 G A M N L) {c : G}
    (hc : c ∈ sectionCentralizer A L (CFSG.Open.pCoreOf 2 L)) (hc1 : c ≠ 1) : c ∉ L :=
  h.not_mem_of_mem_sectionCentralizer_of (fun _ hx hx' => h.mem_pCoreOf_of_commutator_mem hx hx')
    hc hc1

theorem Hyp1921.isE27_inf_Q_sup_zpowers (h : Hyp1921 G A M N L) {Q : Subgroup G}
    (hQ : IsSylowOf 3 Q N) (hAQ : A ≤ Q) {c : G}
    (hc : c ∈ sectionCentralizer A L (CFSG.Open.pCoreOf 2 L)) (hc1 : c ≠ 1) :
    IsE27 ((Q ⊓ L : Subgroup G) ⊔ Subgroup.zpowers c) ∧
      (Q ⊓ L : Subgroup G) ⊔ Subgroup.zpowers c ≤ Q :=
  h.isE27_inf_Q_sup_zpowers_of h.le_normalizer hQ hAQ (h.card_inf_Q hQ) (h.isElemAbelian_inf_Q hQ)
    (h.inf_pCoreOf_eq_bot_Q hQ) hc (h.not_mem_of_mem_sectionCentralizer hc hc1)

theorem Hyp1921.normalizer_inf_Q_le (hET : partTwoE G ⊆ partTwoT G) (h : Hyp1921 G A M N L)
    {Q : Subgroup G} (hQ : IsSylowOf 3 Q N) (hAQ : A ≤ Q) {c : G}
    (hc : c ∈ sectionCentralizer A L (CFSG.Open.pCoreOf 2 L)) (hc1 : c ≠ 1) :
    Subgroup.normalizer ((Q ⊓ L : Subgroup G) : Set G) ≤ M :=
  have hE := h.isE27_inf_Q_sup_zpowers hQ hAQ hc hc1
  h.normalizer_inf_Q_le_of hET hQ hAQ (h.card_inf_Q hQ) (h.isElemAbelian_inf_Q hQ) hE.1 hE.2

theorem Hyp1921.sup_inf_eq (hET : partTwoE G ⊆ partTwoT G) (h : Hyp1921 G A M N L) :
    L ⊔ (N ⊓ M) = N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ, hAQ⟩ := h.exists_isSylowOf_ge
  obtain ⟨c, hc, hc1⟩ := h.exists_ne_one_mem_sectionCentralizer
  have hNB := h.normalizer_inf_Q_le hET hQ hAQ hc hc1
  refine le_antisymm (sup_le h.L_le_N inf_le_left) ?_
  intro n hn
  obtain ⟨l, hl, m, hm, rfl⟩ :=
    Sec18.exists_mul_of_isSylowOf (h.isSylowOf_inf_Q hQ) (K := N) h.le_normalizer hn
  have hmN : m ∈ N := by
    have : m = l⁻¹ * (l * m) := by group
    rw [this]
    exact N.mul_mem (N.inv_mem (h.L_le_N hl)) hn
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right ⟨hmN, hNB hm⟩)

theorem Hyp1921.not_le_M (hET : partTwoE G ⊆ partTwoT G) (h : Hyp1921 G A M N L) :
    ¬ L ≤ M := by
  intro hLM
  have hNM : N ≤ M := by
    rw [← h.sup_inf_eq hET]
    exact sup_le hLM inf_le_right
  exact h.mem_scriptM_N.1.2 M (lt_of_le_of_ne hNM h.ne) h.mem_scriptM.1.1

theorem Hyp1921.exists_zpowers_eq (hET : partTwoE G ⊆ partTwoT G) (h : Hyp1921 G A M N L) :
    ∃ c : G, sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) = (Subgroup.zpowers c : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hKA, hK⟩ := exists_subgroup_sectionCentralizer h.le_normalizer_A
  obtain ⟨c, hc, hc1⟩ := h.exists_ne_one_mem_sectionCentralizer
  have hcK : c ∈ K := by rw [← SetLike.mem_coe, hK]; exact hc
  have hA := h.isE27
  have hKE : CFSG.Open.IsElemAbelian 3 K := Late.isElemAbelian_of_le hA.1 hKA
  have hK3 : IsPGroup 3 K := fun x => ⟨1, Subtype.ext (by simpa using hKE.2 x x.2)⟩
  have hlt : Nat.card K < 9 := by
    by_contra hge
    push Not at hge
    refine h.not_le_M hET (h.le_M_of_rank_two hKA (two_le_pRank_of_elemAbelian hKE hge) ?_)
    intro x hx
    have hx' : x ∈ sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) := by
      rw [← hK]; exact hx
    exact hx'.2
  have hord : orderOf c = 3 := orderOf_eq_prime (hA.1.2 c (hKA hcK)) hc1
  have hzle : Subgroup.zpowers c ≤ K := Subgroup.zpowers_le.mpr hcK
  have hKc : Subgroup.zpowers c = K := by
    refine Subgroup.eq_of_le_of_card_ge hzle ?_
    obtain ⟨k, hk⟩ := hK3.exists_card_eq
    rw [Nat.card_zpowers, hord, hk]
    rw [hk, show (9 : ℕ) = 3 ^ 2 by norm_num] at hlt
    have hk2 : k < 2 := (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
    calc 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 3 := by norm_num
  exact ⟨c, by rw [← hK, ← hKc]⟩

end CFSG.RankThree.PartTwo.Late

namespace CFSG.RankThree.PartTwo

theorem item1922_of_item1912 (h1912 : Late.Item1912) : Item1922 :=
  fun G _ _ _ _ _ _ h =>
    ⟨h.exists_zpowers_eq (h1912 G h.toSec19Std), h.not_le_M (h1912 G h.toSec19Std)⟩

end CFSG.RankThree.PartTwo
