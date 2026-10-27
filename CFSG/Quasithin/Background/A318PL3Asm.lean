module

public import CFSG.Quasithin.Background.A3Structure318Defs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Background.A318PL3Core

public section

namespace CFSG.Quasithin

namespace A318P

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem frame_trichotomy {X : Type} [Group X] [Finite X] {S : Subgroup X} [S.Normal]
    (hC : ∀ c : X, (∀ s ∈ S, c * s = s * c) → c = 1) [IsSimpleGroup ↥S] (h3S : 3 ∣ Nat.card S)
    {C : Type} [Group C] [IsCyclic C] (F : L3Frame ↥S C)
    (hX3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2) :
    oPrimeResidualOf 3 (⊤ : Subgroup X) = S ∨
      Nonempty (↥(oPrimeResidualOf 3 (⊤ : Subgroup X)) ≃* ↥F.D) ∨
      ((∃ c : C, orderOf c = 3) ∧
        Nat.card (↥(oPrimeResidualOf 3 (⊤ : Subgroup X)) ⧸
          S.subgroupOf (oPrimeResidualOf 3 (⊤ : Subgroup X))) = 3 ∧
        ∀ a ∈ oPrimeResidualOf 3 (⊤ : Subgroup X), orderOf a = 3 → a ∈ S) := by
  by_cases hx : ∃ x : X, x ∉ S ∧ ∃ k : ℕ, orderOf x = 3 ^ k
  · rcases l3_core hC h3S F hX3 hx with h | ⟨h1, h2, h3⟩
    · exact Or.inr (Or.inl ⟨(Subgroup.equivMapOfInjective _ _ (conjNormal_injective hC)).trans
        (MulEquiv.subgroupCongr h)⟩)
    · exact Or.inr (Or.inr ⟨h3, h1, h2⟩)
  · refine Or.inl (oPrimeResidualOf_eq_of_forall Nat.prime_three h3S fun x k hk => ?_)
    by_contra hxS
    exact hx ⟨x, hxS, k, hk⟩

theorem isPSLEps3_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {s : Bool}
    {p n : ℕ} (h : IsPSLEps3 s p n Y) : IsPSLEps3 s p n X := by
  cases s
  · obtain ⟨hadm, K, hK, hKf, hcard, ⟨e'⟩⟩ := h
    exact ⟨hadm, K, hK, hKf, hcard, ⟨e.trans e'⟩⟩
  · obtain ⟨hadm, K, hK, hKf, hcard, ⟨e'⟩⟩ := h
    exact ⟨hadm, K, hK, hKf, hcard, ⟨e.trans e'⟩⟩

theorem a318Case2_of_frame {X : Type} [Group X] [Finite X] {S : Subgroup X} [S.Normal]
    (hC : ∀ c : X, (∀ s ∈ S, c * s = s * c) → c = 1) [IsSimpleGroup ↥S] (h3S : 3 ∣ Nat.card S)
    {C : Type} [Group C] [IsCyclic C] (F : L3Frame ↥S C)
    (hX3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 2) {s : Bool} {q : ℕ}
    (hmod : Int.ModEq 3 (q : ℤ) (if s then 1 else -1)) (hq : IsPSLEps3q s q ↥S)
    (hPGL : ∀ (T : Type) [Group T], Nonempty (T ≃* ↥F.D) → IsPGLEps3 s q T)
    (hcirc : (∃ c : C, orderOf c = 3) → ∃ m : ℕ, q = 2 ^ (3 * m) ∧ IsPSLEps3 s 2 (3 * m) ↥S) :
    oPrimeResidualOf 3 (⊤ : Subgroup X) = S ∨ A318Case2 S := by
  rcases frame_trichotomy hC h3S F hX3 with h | e | ⟨hc, hidx, hnoA⟩
  · exact Or.inl h
  · exact Or.inr ⟨s, q, hmod, hq, Or.inl (hPGL _ e)⟩
  · obtain ⟨m, hqm, hmodel⟩ := hcirc hc
    refine Or.inr ⟨s, q, hmod, hq, Or.inr ⟨m, hqm, 3 * m, S.subgroupOf (oPrimeResidualOf 3 ⊤),
      inferInstance, hqm, ?_, hidx, ?_, ?_⟩⟩
    · exact isPSLEps3_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (le_oPrimeResidualOf_of_isSimpleGroup Nat.prime_three h3S))
        hmodel
    · intro x hx
      apply Subtype.ext
      apply hC
      intro t ht
      have h1 := hx ⟨t, le_oPrimeResidualOf_of_isSimpleGroup Nat.prime_three h3S ht⟩ ht
      exact congrArg Subtype.val h1
    · intro a ha
      exact hnoA a a.2 ((Subgroup.orderOf_coe a).trans ha)

end A318P

end CFSG.Quasithin
