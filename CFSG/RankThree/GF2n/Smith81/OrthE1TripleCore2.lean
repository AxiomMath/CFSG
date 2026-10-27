module

public import CFSG.RankThree.GF2n.Smith81.OrthE1TripleLevi2

public section

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1

namespace Triple

variable {K : Type} [Field K] {κ : K} {γ : T3E K} {𝔸 : Subgroup (T3E K)}

theorem triple_core_free [Finite K] [CharP K 2] (hKF11a : Sp4InvolutionStatement)
    (hK : 4 ≤ Nat.card K) (D : CoreData κ γ 𝔸)
    (hbound : ∀ 𝒰 : Subgroup (T3E K), 𝒰 ≤ Ok κ → (∀ u ∈ 𝒰, ∀ g ∈ colG, u * g = g * u) →
      (∀ u ∈ 𝒰, ∀ l ∈ lineG, u * l = l * u) →
      𝒰 ≤ Subgroup.closure ((𝔸 : Set (T3E K)) ∪
        ((rowG (K := K) : Subgroup (T3E K)) : Set (T3E K))) →
      (∀ u ∈ 𝒰, u * u = 1) → Nat.card 𝒰 ≤ 2 * Nat.card K ^ 2) :
    κ = 0 ∧ lineG.map (cjH γ) ≤ rowG ∧ lineG ≤ 𝔸 ∧ 𝔸 = slotG := by
  obtain ⟨hκ, hN'row⟩ := D.claimB hKF11a hK
  have hline := D.claimC hKF11a hK
  subst hκ
  haveI := D.hAsimple
  have hcomm := ct2_free hK 𝔸 D.hAO D.hAc (fun 𝒦 h1 h2 => fu_eq_bot_or_eq h1 h2) D.hy hline
    D.hAcard hbound
  refine ⟨rfl, hN'row, hline, ?_⟩
  have hle : 𝔸 ≤ slotG := fun a ha =>
    ct3 a (D.hAO ha) (fun h hh => hcomm a ha h hh) (fun h hh => D.hAc a ha h hh)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_slotG, D.hAcard])

end Triple

end CFSG.RankThree.GF2n.Smith81.Smith23E1
