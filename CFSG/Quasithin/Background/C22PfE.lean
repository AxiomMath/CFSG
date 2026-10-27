module

public import CFSG.Quasithin.Background.SmithC27RLieA6

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Blueprint CFSG.Assembly.LowTwoRank

@[expose] def TitsSylowSelfNormalizing : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n f : ℕ), LieModel X .Tits n 2 f →
    ∀ S : Sylow 2 X, Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ S

@[expose] def RadicalParabolicU33 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsPSU 3 3 1 X →
    SmithC27.IsRadicalParabolic (⊤ : Subgroup X)

namespace C22Pf

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem holds_of_holdsTits (h : HoldsTits X 2)
    (hN : ∀ S : Sylow 2 X, Subgroup.normalizer ((S : Subgroup X) : Set X) ≤ S) : Holds X 2 := by
  intro U hU hU2
  obtain ⟨S, P, hP, hNP, hcore, hUP, hSP⟩ := h U hU hU2
  exact ⟨S, P, hP, hNP, hcore, hUP, (hN S).trans hSP⟩

omit [Finite X] in
theorem isRadicalParabolic_of_isAlt6 (h : IsAlt 6 X) :
    SmithC27.IsRadicalParabolic (⊤ : Subgroup X) := by
  obtain ⟨e⟩ := h
  exact (SmithC27.isRadicalParabolic_congr (SmithC27.topMulEquivOfMulEquiv e)).mpr
    SmithC27.isRadicalParabolic_alt6

theorem isRadicalParabolic_c224
    (hBT : ∀ (X : Type) [Group X] (t : StatedLieTag) (n f : ℕ), LieModel X t n 2 f →
      t ≠ .Tits → Holds X 2)
    (hBTT : ∀ (X : Type) [Group X] (n f : ℕ), LieModel X .Tits n 2 f → HoldsTits X 2)
    (hTN : TitsSylowSelfNormalizing) (hU33 : RadicalParabolicU33)
    (hX : EvenLieType X ∨ IsAlt 6 X ∨ IsPSU 3 3 1 X) :
    SmithC27.IsRadicalParabolic (⊤ : Subgroup X) := by
  rcases hX with ⟨t, n, f, -, hm⟩ | h6 | h33
  · by_cases ht : t = .Tits
    · subst ht
      exact SmithC27.isRadicalParabolic_top_of_holds
        (holds_of_holdsTits (hBTT X n f hm) (hTN X n f hm))
    · exact SmithC27.isRadicalParabolic_top_of_holds (hBT X t n f hm ht)
  · exact isRadicalParabolic_of_isAlt6 h6
  · exact hU33 X h33

end C22Pf

end CFSG.Quasithin
