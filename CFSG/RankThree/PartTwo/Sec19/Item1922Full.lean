module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartTwo.Late.Glue
public import CFSG.RankThree.PartTwo.Sec18.Notation
import CFSG.RankThree.PartTwo.Sec19.Hyp1921NotLeM
import CFSG.RankThree.PartTwo.Sec19.Hyp1921OmegaOne
import CFSG.RankThree.PartTwo.Sec19.Hyp1921Structure

public section

namespace CFSG.RankThree.PartTwo

open CFSG.ABGLocalTools (IsSylowOf)

@[expose] def Item1922Full : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M N L : Subgroup G), Late.Hyp1921 G A M N L →
    N ≤ Subgroup.normalizer (L : Set G) ∧ Subgroup.normalizer (L : Set G) = N ∧
    (∃ c : G, orderOf c = 3 ∧
      Late.sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) = (Subgroup.zpowers c : Set G) ∧
      A = Subgroup.zpowers c ⊔ (A ⊓ L)) ∧
    IsSylowOf 3 (A ⊓ L) L ∧ Nat.card (A ⊓ L : Subgroup G) = 9 ∧
    (∀ Q : Subgroup G, IsSylowOf 3 Q N → A ≤ Q → Sec18.omegaOneThree Q = A) ∧
    L ⊔ (N ⊓ M) = N ∧ ¬ L ≤ M ∧ CFSG.Open.pCoreOf 2 L ≤ M ∧
    Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ≤ M

theorem item1922Full_of_item1912
    (h1912 : Late.Item1912) : Item1922Full := by
  intro G _ _ A M N L h
  have hET := h1912 G h.toSec19Std
  obtain ⟨c, hc⟩ := h.exists_zpowers_eq hET
  have hc9 := h.card_inf hET hc
  exact ⟨h.le_normalizer, h.normalizer_eq,
    ⟨c, h.orderOf_eq_three hc, hc, h.eq_zpowers_sup_inf hET hc⟩, h.isSylowOf_inf hET hc, hc9,
    fun _ hQ hAQ => h.omegaOneThree_eq hET hc hQ hAQ, h.sup_inf_eq hET, h.not_le_M hET,
    h.pCoreOf_le_M, h.normalizer_inf_le hc9⟩

end CFSG.RankThree.PartTwo
