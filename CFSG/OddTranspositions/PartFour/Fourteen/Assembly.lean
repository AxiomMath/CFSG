module

public import CFSG.OddTranspositions.PartFour.Fourteen.Steps
public import CFSG.OddTranspositions.PartFour.Fourteen.TheoremFour
public import CFSG.OddTranspositions.PartFour.Fourteen.TheoremFive
public import CFSG.OddTranspositions.PartThree.EightEight.Statement
import CFSG.OddTranspositions.PartFour.Fourteen.ModelBender
import CFSG.OddTranspositions.PartFour.Fourteen.ModelWreath
import CFSG.OddTranspositions.PartFour.Fourteen.ModelO4Minus5
import CFSG.OddTranspositions.PartFour.Fourteen.ModelO4Plus
import CFSG.OddTranspositions.TheoremTwo.Assembly

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Bridge.OddTransp

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem hypEShape_of_ascList {X : Type} [Group X] [Finite X] {E : Set X} (hS : Setup X E)
    (hder : derivedSeries X 1 = derivedSeries X 2) (hL : AscList X E)
    (h3 : ¬ ∀ d ∈ E, ∀ e ∈ E, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) : HypEShape X E := by
  obtain ⟨s, hs⟩ := hS.nonempty
  have hs2 : s * s = 1 := hS.oddT.mul_self_eq_one hs
  have hs1 : s ≠ 1 := hS.oddT.ne_one hs
  have psl2 : ∀ f, 2 ≤ f → (X ≃* CFSG.Theory.Comparator.PSL2Model f) → HypEShape X E :=
    fun f hf e => Or.inl ⟨s, hs, 2, f, le_rfl, hf,
      Or.inl (isSymplecticTransvection_of_mulEquiv_psl2Model hf e hs2 hs1)⟩
  rcases hL with h | h | h | ⟨f, n, hf, ⟨e⟩⟩ | h | hB | hO
  · exact absurd h h3
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rcases (show n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with
      rfl | rfl | rfl | rfl | rfl | hn
    · exact absurd (eq_one_of_mulEquiv_l2Wreath_zero e s) hs1
    · obtain ⟨e'⟩ := nonempty_mulEquiv_psl2Model_of_l2Wreath_one e
      exact psl2 f hf e'
    · obtain ⟨t, ht, hO⟩ := exists_isOrthReflection_of_mulEquiv_l2Wreath_two hS hf e
      exact Or.inl ⟨t, ht, 4, f, by norm_num, hf, Or.inr (Or.inr hO)⟩
    · exact absurd hder (derivedSeries_one_ne_two_of_mulEquiv_l2Wreath (Or.inl rfl) e)
    · exact absurd hder (derivedSeries_one_ne_two_of_mulEquiv_l2Wreath (Or.inr rfl) e)
    · obtain ⟨t, ht, hW⟩ := exists_isWreathTransposition_of_mulEquiv_l2Wreath hS hf hn e
      exact Or.inr (Or.inr (Or.inl ⟨t, ht, f, n, hn, hW⟩))
  · exact Or.inr (Or.inr (Or.inr h))
  · rcases hB with ⟨f, hf, e⟩ | ⟨f, hf, e⟩ | ⟨f, hf, e⟩
    · exact psl2 f hf e
    · exact Or.inr (Or.inr (Or.inr ⟨_, isSz_of_mulEquiv_szModel hf e⟩))
    · exact Or.inl ⟨s, hs, 3, f, by norm_num, hf,
        Or.inr (Or.inl (isUnitaryTransvection_of_mulEquiv_psu3Model hf e hs2 hs1))⟩
  · obtain ⟨b, hb1, hb2, hb3⟩ := fischerModel_of_isO4Minus5Pair hO
    exact Or.inr (Or.inl ⟨4, le_rfl, b, hb1, hb2, hb3⟩)

theorem hypothesisE_of_ascList (hC : HypothesisC D) (hHns : ¬ Group.IsSolvable (Halpha D hC.alpha))
    (hder : derivedSeries (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 1 =
      derivedSeries (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) 2)
    (hL : AscList (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)) (imageClass hC))
    (h3 : ¬ ∀ d ∈ imageClass hC, ∀ e ∈ imageClass hC, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) :
    HypothesisE hC :=
  hypEShape_of_ascList (setup_quotient hC hHns) hder hL h3

theorem ascMainTheorem_of_inputs (h1 : TheoremOne) (h2 : AschbacherTheoremTwo)
    (h88 : PartThree.Theorem8_8Quot) (h4 : Theorem4List) (h5 : Theorem5List) :
    AscMainTheorem := by
  suffices h : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G] (D : Set G), Nat.card G = n →
      Setup G D → (∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) →
      derivedSeries G 1 = derivedSeries G 2 → AscList G D by
    intro G _ _ D hS hrad hder
    exact h _ G D rfl hS hrad hder
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ D hn hS hrad hder
  by_cases h3T : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)
  · exact Or.inl h3T
  by_cases hdis : CFSG.Timmesfeld.Connectivity.Disconnected D
  · exact ascList_of_disconnected h1 hS hdis hrad hder
  obtain ⟨hC⟩ := nonempty_hypothesisC hS hdis hrad
  by_cases hsolv : Group.IsSolvable (Halpha D hC.alpha)
  · exact ascList_of_isSolvable_Halpha h2 hC hrad hsolv
  rcases h88 G D hC hrad h3T hsolv with hder' | ⟨f, m, hf, ⟨e⟩⟩
  swap
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨f, m, hf, ⟨e⟩⟩)))
  have hrad' : ∀ N : Subgroup (Halpha D hC.alpha ⧸ CFSG.solvableRadical (Halpha D hC.alpha)),
      N.Normal → Group.IsSolvable N → N = ⊥ := fun N hN hNs => by
    have h := le_solvableRadical hN hNs
    rw [solvableRadical_quotient_H hC] at h
    exact le_bot_iff.mp h
  have hL' := ih _ ((natCard_quotient_Halpha_lt hC hrad).trans_eq hn) _ (imageClass hC) rfl
    (setup_quotient hC hsolv) hrad' hder'
  by_cases h3' : ∀ d ∈ imageClass hC, ∀ e ∈ imageClass hC, orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)
  · rcases h2 G D hS hC (localSecond_of_threeTransp_imageClass hC h3') hrad with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  have hE := hypothesisE_of_ascList hC hsolv hder' hL' h3'
  by_cases hMZ : CFSG.solvableRadical (Halpha D hC.alpha) ≤ Subgroup.center (Halpha D hC.alpha)
  · exact h4 G D hC hrad hE hMZ
  by_cases hW : ∃ f n : ℕ, 2 ≤ f ∧ Nonempty (G ≃* L2Wreath f n)
  · exact Or.inr (Or.inr (Or.inr (Or.inl hW)))
  · exact h5 G D hC hrad hW hE hMZ

theorem noSqE1OrThreeTranspositions_of_main (hM : AscMainTheorem) (hT : AscListTable) :
    NoSqE1OrThreeTranspositions := by
  intro G _ _ D hcls hodd hgen hrad hcomm h2 hsq hE1
  have hS : Setup G D := ⟨hcls, hodd, hgen⟩
  have h1 : derivedSeries G 1 = layer G := by
    rw [derivedSeries_one]
    exact hcomm
  have hder : derivedSeries G 1 = derivedSeries G 2 := by
    show derivedSeries G 1 = derivedSeries G (1 + 1)
    rw [derivedSeries_succ G 1, h1, CFSG.LocalCores.layer_perfect]
  exact hT G D hS hrad hcomm h2 hsq hE1 (hM G D hS hrad hder)

end CFSG.OddTranspositions.PartFour
