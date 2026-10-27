module

public import CFSG.RankThree.GF2n.Parrott.Lemma16SecondParagraph

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory

variable {G : Type} [Group G] [Finite G] {z : G}

theorem false_of_conj_of_fusion_subgroup {L X K A B : Subgroup G} {x : G}
    (hXS : IsSylowOf 2 X (L ⊓ H z ⊓ Subgroup.centralizer ({x} : Set G)))
    (hKX : K ≤ X)
    (hNXK : Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (K : Set G))
    (hK : IsElemAbelian 2 K) (hxK : x ∈ K)
    (hAK : A ≤ K) (hzA : z ∈ A) (hxA : x ∉ A)
    (hfus : ∀ k ∈ K, IsConj z k → k = z ∨ x⁻¹ * k ∈ A)
    (hdvd : 2 ∣ (L ⊓ H z ⊓ Subgroup.centralizer ({x} : Set G)).relIndex (L ⊓ H z))
    (hconj : ∃ c ∈ L, c * z * c⁻¹ = x)
    (hBA : B ≤ A) (hzB : z ∈ B) (hB : 2 < Nat.card B)
    (hidx : ∀ a ∈ A, ∀ a' ∈ A, a ∉ B → a' ∉ B → a * a' ∈ B)
    (hQ : ∀ a ∈ A, ∀ b ∈ B, IsConj (x * a) (x * (a * b))) :
    False := by
  obtain ⟨c, hcL, hcz⟩ := hconj
  have hzx : IsConj z x := isConj_iff.mpr ⟨c, hcz⟩
  have hS1 : ∀ a ∈ A, IsConj z (x * a) → ∀ b ∈ B, IsConj z (x * (a * b)) :=
    fun a ha hS b hb => hS.trans (hQ a ha b hb)
  have hSB : ∀ b ∈ B, IsConj z (x * b) := fun b hb => by
    have := hS1 1 A.one_mem (by rw [mul_one]; exact hzx) b hb
    rwa [one_mul] at this
  let A' : Subgroup G :=
    { carrier := {a | a ∈ A ∧ IsConj z (x * a)}
      one_mem' := ⟨A.one_mem, by rw [mul_one]; exact hzx⟩
      mul_mem' := fun {a a'} ha ha' => by
        refine ⟨A.mul_mem ha.1 ha'.1, ?_⟩
        by_cases hb : a' ∈ B
        · exact hS1 a ha.1 ha.2 a' hb
        · by_cases hb' : a ∈ B
          · have hcomm : a * a' = a' * a := hK.comm (hAK ha.1) (hAK ha'.1)
            rw [hcomm]
            exact hS1 a' ha'.1 ha'.2 a hb'
          · exact hSB _ (hidx a ha.1 a' ha'.1 hb' hb)
      inv_mem' := fun {a} ha => by
        have haa : a * a = 1 := hK.mul_self_eq_one (hAK ha.1)
        have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
        rw [hinv]
        exact ha }
  have hBA' : B ≤ A' := fun b hb => ⟨hBA hb, hSB b hb⟩
  have hA'K : A' ≤ K := fun a ha => hAK ha.1
  have hzA' : z ∈ A' := ⟨hzA, hSB z hzB⟩
  have hxA' : x ∉ A' := fun hx => hxA hx.1
  have hA'card : 2 < Nat.card ↥A' := lt_of_lt_of_le hB (Subgroup.card_le_of_le hBA')
  have hfus' : ∀ k ∈ K, IsConj z k → k = z ∨ x⁻¹ * k ∈ A' := by
    intro k hk hzk
    rcases hfus k hk hzk with h1 | h1
    · exact Or.inl h1
    · refine Or.inr ⟨h1, ?_⟩
      rw [mul_inv_cancel_left]
      exact hzk
  exact false_of_conj_of_isElemAbelian (z := z) hXS hKX hNXK hK hxK hA'K hzA' hxA' hA'card hfus'
    hdvd (fun hex => by
      obtain ⟨a, ha, hna⟩ := hex
      exact absurd ha.2 hna) ⟨c, hcL, hcz⟩

end CFSG.RankThree.GF2n.Parrott
