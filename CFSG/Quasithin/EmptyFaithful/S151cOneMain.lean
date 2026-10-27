module

public import CFSG.Quasithin.EmptyFaithful.S151cShapeNine
public import CFSG.Quasithin.EmptyFaithful.S151cShapeE27
public import CFSG.Quasithin.EmptyFaithful.S151cShapeOmega
public import CFSG.Quasithin.EmptyFaithful.S151cOneAux
public import CFSG.Quasithin.EmptyFaithful.S151cOm4b

public section

namespace CFSG.Quasithin

open CFSG.Open

section OneMain151c

variable {V : Type} [CommGroup V] [Finite V] {X Tb Xc J : Subgroup (MulAut V)} {r : ℚ}

theorem oneBlock_cases (B : OneBlock151c X Tb Xc J r) (hCE1 : Nat.card V ≠ 4) :
    CaseI151c X Tb J := by
  have hcardJ3 : ∀ (e : Nonempty (↥J ≃* DihedralGroup 3)), Nat.card J = 2 * 3 := fun e =>
    card_of_dihedral e
  obtain ⟨-, hD⟩ := B.d217
  rcases hD with ⟨⟨e⟩, hrk, hr⟩ | ⟨⟨e⟩, hrk, hr⟩ | ⟨hE, hF9, ht, hrk, hr⟩ |
      ⟨hF27, hexp, hnc, ht, hrk, hr⟩ | ⟨hrk, hΩ, ⟨eΩ⟩, hr⟩ | h6
  · rcases hr with hr1 | hr2
    · exfalso
      apply hCE1
      have h2 : rk V = 2 := by
        have : (rk V : ℚ) = 2 := by rw [hrk, hr1]; norm_num
        exact_mod_cast this
      rw [card_eq_two_pow_rk B.sq, h2]
      norm_num
    · have hrk4 : rk V = 4 := by
        have : (rk V : ℚ) = 4 := by rw [hrk, hr2]; norm_num
        exact_mod_cast this
      obtain ⟨h | h, hn⟩ := shape_S3 B ⟨e⟩ hr2 hrk4
      · have hX : Nat.card X = 2 * 3 := by rw [h.2.1, hcardJ3 ⟨e⟩]
        refine ⟨Or.inl h, hn, B.genTop_S3 e hrk4 (by decide : Odd 3) hX, ?_⟩
        exact Or.inl (B.qdata_two hr2 (by decide : Odd 3) (hcardJ3 ⟨e⟩))
      · have hX : Nat.card X = 2 * 9 := by
          obtain ⟨-, -, ⟨e'⟩⟩ := h
          rw [Nat.card_congr e'.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
          norm_num
        refine ⟨Or.inr (Or.inl h), hn, B.genTop_S3 e hrk4 (by decide : Odd 9) hX, ?_⟩
        exact Or.inl (B.qdata_two hr2 (by decide : Odd 3) (hcardJ3 ⟨e⟩))
  · obtain ⟨h, hn⟩ := shape_D10 B ⟨e⟩ hr hrk
    have hcard : Nat.card J = 2 * 5 := card_of_dihedral ⟨e⟩
    have hnot : ¬ (Nonempty (↥J ≃* DihedralGroup 3) ∧ rk V = 4) := fun hc => by
      have := hcardJ3 hc.1
      omega
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))), hn, B.genTop_of_not_S3 hnot,
      Or.inl (B.qdata_two hr (by decide : Odd 5) hcard)⟩
  · have h := shape_Nine B hE hF9 ht hr hrk
    have hn : TwoNilpAut X := twoNilp_of_oTwoUpper_odd (by
      rw [h.2.1.2.1]
      exact ⟨4, rfl⟩)
    have hcard : Nat.card J = 2 * 9 := card_J_nine hE hF9 ht
    have hnot : ¬ (Nonempty (↥J ≃* DihedralGroup 3) ∧ rk V = 4) := fun hc => by
      have := hcardJ3 hc.1
      omega
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inl h))), hn, B.genTop_of_not_S3 hnot,
      Or.inl (B.qdata_two hr (by decide : Odd 9) hcard)⟩
  · have h := shape_E27 B hF27 hexp hnc ht hr hrk
    have hn : TwoNilpAut X := twoNilp_of_oTwoUpper_odd (by
      rw [h.2.1.2.1]
      exact Odd.pow (by decide))
    have hcard : Nat.card J = 2 * 27 := card_J_E27 hF27 hexp ht
    have hnot : ¬ (Nonempty (↥J ≃* DihedralGroup 3) ∧ rk V = 4) := fun hc => by
      have := hcardJ3 hc.1
      omega
    exact ⟨Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))), hn,
      B.genTop_of_not_S3 hnot, Or.inl (B.qdata_two hr (by decide : Odd 27) hcard)⟩
  · have h := shape_Omega B hΩ hr hrk
    have hnot : ¬ (Nonempty (↥J ≃* DihedralGroup 3) ∧ rk V = 4) := fun hc => by
      have h1 := hcardJ3 hc.1
      have h2 : Nat.card J = 6 * 6 := by
        rw [Nat.card_congr eΩ.toEquiv, Nat.card_prod, DihedralGroup.nat_card]
      omega
    refine ⟨Or.inr (Or.inr (Or.inl h)), isOmegaFourPlus_twoNilp h.2.2,
      B.genTop_of_not_S3 hnot, Or.inr ⟨h, ?_, qOf_eq_of_isOmegaFourPlus h.2.2⟩⟩
    rw [← hr]
    exact B.qhat
  · exact absurd (oneBlock_not_shape6 B h6) id

end OneMain151c

end CFSG.Quasithin
