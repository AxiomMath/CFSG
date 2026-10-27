module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B42A57E7
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S152L27C
public import CFSG.Quasithin.EmptyFaithful.S152N2Lin
public import CFSG.Quasithin.EmptyFaithful.S152NAbs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S152N CFSG.Quasithin.S152N2
open scoped Pointwise

section Count

variable {G : Type*} [Group G] [Finite G]

theorem card_sup_le_mul152 {Vc ZS L : Subgroup G} (k : ℕ) (hZVc : ZS ≤ Vc) (hZL : ZS ≤ L)
    (hn : Vc ≤ Subgroup.normalizer (L : Set G)) (hcard : Nat.card Vc ≤ k * Nat.card ZS) :
    Nat.card ↥(Vc ⊔ L) ≤ k * Nat.card L := by
  have hprod : ((Vc ⊔ L : Subgroup G) : Set G) = (Vc : Set G) * (L : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right Vc L hn
  have hmul := Subgroup.card_mul_eq_card_subgroup_mul_card_quotient L (Vc : Set G)
  rw [← hprod] at hmul
  have hc : Nat.card ↥(Vc ⊔ L) =
      Nat.card L * Nat.card (((Vc : Set G).image (↑) : Set (G ⧸ L))) := hmul
  have himg : Nat.card (((Vc : Set G).image (↑) : Set (G ⧸ L))) ≤ k := by
    let Z' : Subgroup Vc := ZS.subgroupOf Vc
    have key : ∀ a b : Vc, a⁻¹ * b ∈ Z' → ((a : G) : G ⧸ L) = ((b : G) : G ⧸ L) := by
      intro a b hab
      rw [QuotientGroup.eq]
      exact hZL (Subgroup.mem_subgroupOf.mp hab)
    let f : Vc ⧸ Z' → ((Vc : Set G).image (↑) : Set (G ⧸ L)) :=
      Quotient.lift (fun v : Vc => (⟨((v : G) : G ⧸ L), ⟨v, v.2, rfl⟩⟩ :
          ((Vc : Set G).image (↑) : Set (G ⧸ L))))
        (fun a b hab => Subtype.ext (key a b (QuotientGroup.leftRel_apply.mp hab)))
    have hsurj : Function.Surjective f := by
      rintro ⟨_, v, hv, rfl⟩
      exact ⟨QuotientGroup.mk ⟨v, hv⟩, rfl⟩
    have h1 := Nat.card_le_card_of_surjective f hsurj
    have h2 : Nat.card (Vc ⧸ Z') * Nat.card Z' = Nat.card Vc :=
      (Subgroup.card_eq_card_quotient_mul_card_subgroup Z').symm
    have h3 : Nat.card Z' = Nat.card ZS :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZVc).toEquiv
    have hZpos : 0 < Nat.card ZS := Nat.card_pos
    have h4 : Nat.card (Vc ⧸ Z') * Nat.card ZS ≤ k * Nat.card ZS := by
      rw [← h3, h2, h3]; exact hcard
    exact h1.trans (Nat.le_of_mul_le_mul_right h4 hZpos)
  rw [hc, mul_comm]
  exact Nat.mul_le_mul_right _ himg

end Count

end CFSG.Quasithin
