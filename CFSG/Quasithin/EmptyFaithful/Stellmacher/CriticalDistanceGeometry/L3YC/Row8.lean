module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.RowEight
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.L3YC.BarSplit
import CFSG.LieType.Simplicity.Classical

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

namespace Stellmacher.CD.L3YC

variable {G : Type} [Group G] [Finite G]

theorem false_row8 {H S L L₁ : Subgroup G} (hS : IsSylowTwoOf S H) (hLH : L ≤ H) (hLL₁ : L ≤ L₁)
    (hN : (L₁.subgroupOf H).Normal)
    (hsplit : ∀ s ∈ S, ∃ p ∈ S ⊓ L, ∃ c ∈ S,
      (∀ x ∈ L, ∃ m ∈ pCoreOf 2 L, c * x * c⁻¹ = x * m) ∧ s = p * c)
    (h8 : IsPSL 2 7 1 ↥(modO2Image H L)) (h49 : IsPSL 2 7 2 ↥(modO2Image H L₁)) : False := by
  have hsim : IsSimpleGroup ↥(modO2Image H L) :=
    (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 7 1 h8).2
  have hn : ¬ IsPGroup 2 ↥(modO2Image H L) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    intro hp
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
    have h168 := card_psl_two_seven h8
    rw [hk] at h168
    have : (7 : ℕ) ∣ 2 ^ k := by rw [h168]; norm_num
    have h7 : 7 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) this
    omega
  have hSb : IsSylowTwoOf ((S.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hS)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) (QuotientGroup.mk'_surjective _)
  have hN1 : (modO2Image H L₁).Normal :=
    Subgroup.Normal.map hN _ (QuotientGroup.mk'_surjective _)
  have hLL : modO2Image H L ≤ modO2Image H L₁ := Subgroup.map_mono fun _ hx => hLL₁ hx
  exact false_psl7_psl49 hSb hN1 hLL h8 h49 (split_bar hS.1 hLH hsplit hsim hn)

end Stellmacher.CD.L3YC

end CFSG.Quasithin
