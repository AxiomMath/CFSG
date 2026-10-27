module

public import CFSG.RankThree.GF2n.Parrott.Section5Lemma53

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.ABGLocalTools Subgroup
open CFSG.GH74.GLS.C3.Layer1.Back (card_conjugate' isSylowOf_conjugate
  conjugate_centralizer_singleton)
open CFSG.GroupTheory (centralizer_zpowers_eq)

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
private theorem conjugate_centralizer_singleton_eq_of_conjugate_zpowers {a b g : G}
    (h : CFSG.conjugate (Subgroup.zpowers a) g = Subgroup.zpowers b) :
    CFSG.conjugate (Subgroup.centralizer ({a} : Set G)) g =
      Subgroup.centralizer ({b} : Set G) := by
  have hzp : Subgroup.zpowers (g⁻¹ * a * g) = Subgroup.zpowers b := by
    rw [← h, CFSG.conjugate, MonoidHom.map_zpowers]
    congr 1
    change g⁻¹ * a * g = MulAut.conj g⁻¹ a
    rw [MulAut.conj_apply, inv_inv]
  rw [conjugate_centralizer_singleton,
    ← centralizer_zpowers_eq (g⁻¹ * a * g), ← centralizer_zpowers_eq b, hzp]

theorem conjugate_zpowers_ne_of_elementaryAbelian_or_card {a b : G} {Ta : Subgroup G}
    (hTa : IsSylowOf 2 Ta (centralizer ({a} : Set G))) (hTac : Nat.card Ta = 2 ^ 7)
    (hnoE : ∀ F : Subgroup G, F ≤ Ta → Nat.card F = 16 →
      ¬ ((∀ x ∈ F, ∀ y ∈ F, x * y = y * x) ∧ ∀ x ∈ F, x * x = 1))
    (hb : (∃ E : Subgroup G, E ≤ centralizer ({b} : Set G) ∧ Nat.card E = 16 ∧
        (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ ∀ x ∈ E, x * x = 1) ∨
      ∃ T : Subgroup G, IsSylowOf 2 T (centralizer ({b} : Set G)) ∧ Nat.card T = 2 ^ 5)
    (g : G) : CFSG.conjugate (zpowers a) g ≠ zpowers b := by
  rcases hb with ⟨E, hEb, hEc, hEab, hE2⟩ | ⟨T, hT, hTc⟩
  · exact conjugate_zpowers_ne_of_elementaryAbelian hTa hnoE hEb hEc hEab hE2 g
  · intro hconj
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hS : IsSylowOf 2 (CFSG.conjugate Ta g) (centralizer ({b} : Set G)) := by
      rw [← conjugate_centralizer_singleton_eq_of_conjugate_zpowers hconj]
      exact isSylowOf_conjugate hTa g
    have h7 : (2 : ℕ) ^ 7 = 2 ^ 5 := by
      rw [← hTac, ← card_conjugate' Ta g, hS.card_eq, ← hT.card_eq, hTc]
    norm_num at h7

end CFSG.RankThree.GF2n.Parrott
