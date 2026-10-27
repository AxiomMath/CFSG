module

public import CFSG.StronglyEmbedded.UniqueCosetZD
public import CFSG.GH74.Uniqueness.Section165GapFinal

public section

namespace CFSG.StronglyEmbedded.UniqueCoset

variable {G : Type} [Group G] [Finite G] {H : Subgroup G} {z : G}

theorem lemma_3_9 (hH : H ≠ ⊤) (hz : orderOf z = 2) (h1 : ∃! c : G ⧸ H, z • c = c)
    (h2 : ∀ g : G, g⁻¹ * z * g ≠ z → z * (g⁻¹ * z * g) = g⁻¹ * z * g * z →
      ∃! c : G ⧸ H, (z * (g⁻¹ * z * g)) • c = c)
    {F : Subgroup G} [F.Normal] (hFs : IsSimpleGroup ↥F)
    (hFnab : ∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x) (hFc : Subgroup.centralizer (F : Set G) = ⊥) :
    Subgroup.normalClosure ({z} : Set G) = F ∧ BenderSuzuki.IsBenderGroup ↥F ∧
      BenderSuzuki.IsStronglyEmbeddedOrder
        (H.subgroupOf (Subgroup.normalClosure ({z} : Set G))) :=
  lemma_3_9_of_ZD GH74.Uniqueness.S_ZD_unconditional hH hz h1 h2 hFs hFnab hFc

theorem lemma_3_9_simple [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hH : H ≠ ⊤)
    (hz : orderOf z = 2) (h1 : ∃! c : G ⧸ H, z • c = c)
    (h2 : ∀ g : G, g⁻¹ * z * g ≠ z → z * (g⁻¹ * z * g) = g⁻¹ * z * g * z →
      ∃! c : G ⧸ H, (z * (g⁻¹ * z * g)) • c = c) :
    BenderSuzuki.IsBenderGroup G ∧ BenderSuzuki.IsStronglyEmbeddedOrder H :=
  lemma_3_9_simple_of_ZD GH74.Uniqueness.S_ZD_unconditional hnab hH hz h1 h2

end CFSG.StronglyEmbedded.UniqueCoset
