module

public import CFSG.Sporadic.SchreierLemmas.OuterAlternatingSix
public import CFSG.Quasithin.Background.A318POutCheap
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.ComponentClassification.CatalogueSchreierAlternating
  (outer_card_dvd_two_of_equiv_outside_six)

theorem outer_finite_of_finite_group (S : Type) [Group S] [Finite S] : Finite (Outer S) := by
  haveI : Finite (MulAut S) := Finite.of_injective (fun f : MulAut S => (f : S → S))
    DFunLike.coe_injective
  infer_instance

theorem card_outer_le_four_of_alternating {S : Type} [Group S] {k : ℕ} (hk6 : 6 ≤ k)
    (hk9 : k ≤ 9) (e : S ≃* alternatingGroup (Fin k)) : Nat.card (Outer S) ≤ 4 := by
  rcases (show k = 6 ∨ 7 ≤ k by omega) with rfl | hk7
  · rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact CFSG.Sporadic.SchreierLemmas.outer_alternating_six.1
  · have hd := outer_card_dvd_two_of_equiv_outside_six (Or.inr hk7) e
    exact (Nat.le_of_dvd (by norm_num) hd).trans (by norm_num)

theorem card_outer_le_two_m22
    {S : Type} [Group S] [Finite S] (e : S ≃* Blueprint.NativeSporadic.Carrier .M22) :
    Nat.card (Outer S) ≤ 2 := by
  have : Finite (Blueprint.NativeSporadic.Carrier .M22) := Finite.of_equiv S e.toEquiv
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  exact CFSG.Quasithin.A318P.card_outer_le_two_of_card_mulAut_le
    CFSG.Sporadic.Schreier.m22_center_eq_bot' CFSG.Sporadic.Schreier.m22_mulAut_card

theorem card_outer_le_two_m23
    {S : Type} [Group S] (e : S ≃* Blueprint.NativeSporadic.Carrier .M23) :
    Nat.card (Outer S) ≤ 2 := by
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  exact CFSG.Sporadic.Schreier.at_m23_schreier.1

theorem card_outer_le_two_m24
    {S : Type} [Group S] [Finite S] (e : S ≃* Blueprint.NativeSporadic.Carrier .M24) :
    Nat.card (Outer S) ≤ 2 := by
  have : Finite (Blueprint.NativeSporadic.Carrier .M24) := Finite.of_equiv S e.toEquiv
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
  exact CFSG.Quasithin.A318P.card_outer_le_two_of_card_mulAut_le
    CFSG.Sporadic.Schreier.m24_center_eq_bot'
    (CFSG.Sporadic.Schreier.m24_mulAut_card.trans (Nat.le_mul_of_pos_left _ (by norm_num)))

theorem listOutBound_alt {S : Type} [Group S] [Finite S] {k : ℕ} (hk6 : 6 ≤ k) (hk9 : k ≤ 9)
    (e : S ≃* alternatingGroup (Fin k)) (A : Subgroup (Outer S)) : Nat.card A ≤ 4 := by
  haveI := outer_finite_of_finite_group S
  exact (Subgroup.card_le_card_group A).trans (card_outer_le_four_of_alternating hk6 hk9 e)

theorem listOutBound_m22
    {S : Type} [Group S] [Finite S] (e : S ≃* Blueprint.NativeSporadic.Carrier .M22)
    (A : Subgroup (Outer S)) : Nat.card A ≤ 4 := by
  haveI := outer_finite_of_finite_group S
  exact (Subgroup.card_le_card_group A).trans ((card_outer_le_two_m22 e).trans (by norm_num))

theorem listOutBound_m23
    {S : Type} [Group S] [Finite S] (e : S ≃* Blueprint.NativeSporadic.Carrier .M23)
    (A : Subgroup (Outer S)) : Nat.card A ≤ 4 := by
  haveI := outer_finite_of_finite_group S
  exact (Subgroup.card_le_card_group A).trans ((card_outer_le_two_m23 e).trans (by norm_num))

theorem listOutBound_m24
    {S : Type} [Group S] [Finite S] (e : S ≃* Blueprint.NativeSporadic.Carrier .M24)
    (A : Subgroup (Outer S)) : Nat.card A ≤ 4 := by
  haveI := outer_finite_of_finite_group S
  exact (Subgroup.card_le_card_group A).trans ((card_outer_le_two_m24 e).trans (by norm_num))

end CFSG.RankThree.GF2n.Stroth80
