module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.Parity
import CFSG.Sporadic.Schreier.PairMcLOut
import CFSG.Sporadic.Schreier.J4SOuter
import CFSG.Sporadic.Schreier.RuAutInner
import CFSG.Sporadic.Schreier.Co1CatalogSchreier
import CFSG.Sporadic.Co2Schreier.Model
import CFSG.Sporadic.FischerOddCore.Fi23Aut
import CFSG.LocalAnalysis.ComponentClassification.CatalogueOuterTwoPartSporadicCases
import CFSG.RankThree.SteinbergCBONOuterPrimes
import CFSG.RankThree.PartOne.KP.Co3Aut
import CFSG.Sporadic.NativeFinite
import CFSG.Sporadic.ON
public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoSporadic
public import CFSG.Sporadic.Mathieu.M22
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.Schreier.M12
public import CFSG.Sporadic.Schreier.RuDefs

public section

open CFSG CFSG.Open CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem finite_carrier (s : TauCeti.SporadicName) (hs : s ≠ .M := by decide) :
    Finite (NativeSporadic.Carrier s) :=
  Sporadic.finite_carrier_of_ne_M s hs

theorem noOddOuter_M11
    : NoOddOuter (NativeSporadic.Carrier .M11) := by
  have := finite_carrier .M11
  exact
  NoOddOuter.of_card_outer_le_two Sporadic.Schreier.at_m11_schreier.1

theorem noOddOuter_M12
    : NoOddOuter (NativeSporadic.Carrier .M12) := by
  have := finite_carrier .M12
  exact
  NoOddOuter.of_card_outer_le (N := 4) Sporadic.Schreier.at_m12_schreier.1 fun q hq hq2 hq4 => by
    have : q = 3 := by
      have := hq.two_le
      have h4 : q ≠ 4 := fun h => by subst h; norm_num at hq
      omega
    subst this
    show 3 ∣ Nat.card NativeSporadic.M12
    rw [Sporadic.Mathieu.card_M12]
    norm_num

theorem noOddOuter_M22
    : NoOddOuter (NativeSporadic.Carrier .M22) := by
  have := finite_carrier .M22
  exact
  NoOddOuter.of_card_outer_le (N := 4) Sporadic.Schreier.at_m22_schreier.1 fun q hq hq2 hq4 => by
    have : q = 3 := by
      have := hq.two_le
      have h4 : q ≠ 4 := fun h => by subst h; norm_num at hq
      omega
    subst this
    show 3 ∣ Nat.card NativeSporadic.M22
    rw [Sporadic.Mathieu.card_M22]
    norm_num

theorem noOddOuter_M23 :
    NoOddOuter (NativeSporadic.Carrier .M23) := by
  have := finite_carrier .M23
  exact
  NoOddOuter.of_card_outer_le_two Sporadic.Schreier.at_m23_schreier.1

theorem noOddOuter_M24
    : NoOddOuter (NativeSporadic.Carrier .M24) := by
  have := finite_carrier .M24
  exact
  NoOddOuter.of_card_outer_le (N := 4) Sporadic.Schreier.at_m24_schreier.1 fun q hq hq2 hq4 => by
    have : q = 3 := by
      have := hq.two_le
      have h4 : q ≠ 4 := fun h => by subst h; norm_num at hq
      omega
    subst this
    show 3 ∣ Nat.card NativeSporadic.M24
    rw [Sporadic.Mathieu.card_M24]
    norm_num

theorem noOddOuter_J1
    : NoOddOuter (NativeSporadic.Carrier .J1) := by
  have := finite_carrier .J1
  exact
  NoOddOuter.of_card_outer_le_two (Sporadic.Schreier.at_j1_schreier.1.le.trans (by norm_num))

theorem noOddOuter_J2
    : NoOddOuter (NativeSporadic.Carrier .J2) := by
  have := finite_carrier .J2
  exact
  NoOddOuter.of_card_outer_le_two Sporadic.Schreier.AT_J2_Schreier.1

theorem noOddOuter_J3 :
    NoOddOuter (NativeSporadic.Carrier .J3) := by
  have := finite_carrier .J3
  exact
  NoOddOuter.of_card_outer_le (N := 6) Sporadic.Schreier.AT_J3_Schreier.1 fun q hq hq2 hq6 => by
    have : q = 3 ∨ q = 5 := by
      have := hq.two_le
      have h4 : q ≠ 4 := fun h => by subst h; norm_num at hq
      have h6 : q ≠ 6 := fun h => by subst h; norm_num at hq
      omega
    show q ∣ Nat.card NativeSporadic.J3
    rw [Sporadic.J3.card_J3]
    rcases this with rfl | rfl <;> norm_num

theorem noOddOuter_J4 :
    NoOddOuter (NativeSporadic.Carrier .J4) := by
  have := finite_carrier .J4
  refine NoOddOuter.of_no_large_prime (fun q hq hq5 hdvd => ?_) ?_
  · have hJ4 : Nonempty (NativeSporadic.Carrier .J4 ≃* NativeSporadic.J4) := ⟨MulEquiv.refl _⟩
    rcases (Sporadic.J4Schreier.R3E_J4_outer_automorphism_group_no_large_primes
      (T := NativeSporadic.Carrier .J4) hJ4).1 q hq hdvd with rfl | rfl <;> omega
  · show 3 ∣ Nat.card NativeSporadic.J4
    rw [Sporadic.J4.card_J4]
    norm_num

theorem noOddOuter_ONan :
    NoOddOuter (NativeSporadic.Carrier .ONan) := by
  have := finite_carrier .ONan
  refine NoOddOuter.of_no_large_prime (fun q hq hq5 hdvd => ?_) ?_
  · rcases Quasithin.SteinbergCB.ON_large_prime_outer_automorphisms_absent q hq hdvd
      with rfl | rfl <;> omega
  · show 3 ∣ Nat.card NativeSporadic.ON
    rw [Sporadic.ON.card_ON]
    norm_num

theorem noOddOuter_McL :
    NoOddOuter (NativeSporadic.Carrier .McL) := by
  have := finite_carrier .McL
  exact NoOddOuter.of_card_outer_le_two Sporadic.Schreier.McL_outer_card_le_two.1

theorem noOddOuter_He
    : NoOddOuter (NativeSporadic.Carrier .He) := by
  have := finite_carrier .He
  exact NoOddOuter.of_card_outer_le_two Sporadic.Schreier.AT_He_Schreier.1

theorem noOddOuter_Suz
    : NoOddOuter (NativeSporadic.Carrier .Suz) := by
  have := finite_carrier .Suz
  exact NoOddOuter.of_card_outer_le_two Sporadic.SuzOddCore.outer_carrier_suz.1.le

theorem noOddOuter_Ru :
    NoOddOuter (NativeSporadic.Carrier .Ru) := by
  have := finite_carrier .Ru
  refine NoOddOuter.of_card_outer_le_two ?_
  rw [show Nat.card (Outer (NativeSporadic.Carrier .Ru)) =
      Nat.card (Outer Sporadic.RuSchreier.ruP) from
    card_outer_eq_of_mulEquiv Sporadic.RuSchreier.ruEquivP,
    Sporadic.RuSchreier.card_outer_ruP]
  norm_num

theorem noOddOuter_Co1 :
    NoOddOuter (NativeSporadic.Carrier .Co1) := by
  have := finite_carrier .Co1
  have h := (Sporadic.Co1Schreier.catalog_schreier_of_inputs.{0}
    fun K _ e => Sporadic.Co2Schreier.AT_Co2_model_Schreier K e).2.2.1
  exact NoOddOuter.of_isPGroup_two h

theorem noOddOuter_Co2
    : NoOddOuter (NativeSporadic.Carrier .Co2) := by
  have := finite_carrier .Co2
  obtain ⟨e⟩ : Nonempty (NativeSporadic.Carrier .Co2 ≃* NativeSporadic.Co2) :=
    ⟨MulEquiv.refl _⟩
  exact NoOddOuter.of_isPGroup_two (Sporadic.Co2Schreier.AT_Co2_model_Schreier _ e).2.1

theorem noOddOuter_Co3 :
    NoOddOuter (NativeSporadic.Carrier .Co3) := by
  have := finite_carrier .Co3
  have h : Nat.card (Outer NativeSporadic.Co3) = 1 :=
    CFSG.RankThree.PartOne.CTUC_Co3_all_automorphisms_inner.{0}.2.2.2.1
  exact NoOddOuter.of_card_outer_le_two (h.le.trans (by norm_num))

theorem noOddOuter_Fi22
    : NoOddOuter (NativeSporadic.Carrier .Fi22) := by
  have := finite_carrier .Fi22
  exact NoOddOuter.of_card_outer_le_two
    ComponentClassification.CatalogueOuterTwoPart.card_outer_fi22.le

theorem noOddOuter_Fi23 :
    NoOddOuter (NativeSporadic.Carrier .Fi23) := by
  have := finite_carrier .Fi23
  exact NoOddOuter.of_card_outer_le_two
    (Sporadic.FischerOddCore.card_outer_fi23.le.trans (by norm_num))

theorem noOddOuter_Fi24Prime
    : NoOddOuter (NativeSporadic.Carrier .Fi24Prime) := by
  have := finite_carrier .Fi24Prime
  exact NoOddOuter.of_card_outer_le_two Sporadic.Schreier.Fi24.card_outer_fi24prime.le

theorem noOddOuter_sporadic
    (hHS : Nat.card (Outer (NativeSporadic.Carrier .HS)) ≤ 2) (s : TauCeti.SporadicName)
    (hfin : Finite (NativeSporadic.Carrier s))
    (hnot : ¬ (s = .Co1 ∨ s = .Co2 ∨ s = .HN ∨ s = .Ly ∨ s = .Th ∨ s = .B ∨ s = .M)) :
    NoOddOuter (NativeSporadic.Carrier s) := by
  cases s
  · exact noOddOuter_M11
  · exact noOddOuter_M12
  · exact noOddOuter_M22
  · exact noOddOuter_M23
  · exact noOddOuter_M24
  · exact noOddOuter_J1
  · exact noOddOuter_J2
  · exact noOddOuter_J3
  · exact noOddOuter_J4
  · exact NoOddOuter.of_card_outer_le_two hHS
  · exact noOddOuter_McL
  · exact noOddOuter_He
  · exact noOddOuter_Ru
  · exact noOddOuter_Suz
  · exact noOddOuter_ONan
  · exact absurd (Or.inl rfl) hnot
  · exact absurd (Or.inr (Or.inl rfl)) hnot
  · exact noOddOuter_Co3
  · exact noOddOuter_Fi22
  · exact noOddOuter_Fi23
  · exact noOddOuter_Fi24Prime
  · exact absurd (Or.inr (Or.inr (Or.inl rfl))) hnot
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hnot
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hnot
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) hnot
  · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))) hnot

theorem hypothesisA_sporadic
    (hHS : Nat.card (Outer (NativeSporadic.Carrier .HS)) ≤ 2)
    (hopen : CFSG.RankThree.PartOne.SporadicOuterOrderLeTwoSimple) {X : Type} [Group X] [Finite X]
    (hsimple : IsSimpleGroup X) (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hrep : NativeSporadic.SporadicRep X) {p : ℕ} (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card X)) : signalizerMcBrideHypothesisA p X := by
  obtain ⟨s, ⟨e⟩⟩ := hrep
  have hfin : Finite (NativeSporadic.Carrier s) := Finite.of_equiv X e.toEquiv
  have : IsSimpleGroup X := hsimple
  by_cases hs : s = .Co1 ∨ s = .Co2 ∨ s = .HN ∨ s = .Ly ∨ s = .Th ∨ s = .B ∨ s = .M
  · exact hypothesisA_of_noOddOuter
      (NoOddOuter.of_card_outer_le_two (hopen s hs X hnonab ⟨e⟩)) hsimple hnonab hp hcop
  · exact hypothesisA_of_noOddOuter
      (NoOddOuter.of_mulEquiv e (noOddOuter_sporadic hHS s hfin hs)) hsimple hnonab hp hcop

end CFSG.SignalizerFunctorTheorem.CatalogBridge
