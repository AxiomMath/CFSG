module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4KcAct
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223W21

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace S15223P4.Kc

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_self_le (K : Subgroup G) : ⁅K, K⁆ ≤ K :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem ha hb) (K.inv_mem ha)) (K.inv_mem hb)

omit [Finite G] in
theorem perfect_sup {A B : Subgroup G} (hA : ⁅A, A⁆ = A) (hB : ⁅B, B⁆ = B) :
    ⁅A ⊔ B, A ⊔ B⁆ = A ⊔ B :=
  le_antisymm (commutator_self_le _) (sup_le
    (calc A = ⁅A, A⁆ := hA.symm
      _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := Subgroup.commutator_mono le_sup_left le_sup_left)
    (calc B = ⁅B, B⁆ := hB.symm
      _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := Subgroup.commutator_mono le_sup_right le_sup_right))

omit [Finite G] in
theorem perfect_conjSub {A : Subgroup G} (hA : ⁅A, A⁆ = A) (g : G) :
    ⁅conjSub g A, conjSub g A⁆ = conjSub g A := by
  unfold conjSub
  rw [← Subgroup.map_commutator, hA]

omit [Finite G] in
theorem perfect_of_cases {T Mc Kc : Subgroup G}
    (h : Case15212ii T Mc Kc ∨ Case15212iii T Mc Kc ∨ Case15212He T Mc Kc) : ⁅Kc, Kc⁆ = Kc := by
  rcases h with h | h | h
  · exact h.2.1.2.1
  · obtain ⟨L, t, -, hL, -, -, rfl, -⟩ := h
    exact perfect_sup hL.2.1 (perfect_conjSub hL.2.1 t)
  · exact h.2.1.2.1

variable {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

theorem isThreePrimeGroup_cv (c : P4Ctx T Mc M H B₀ I X) (hN : D1.P4N1 T Mc M H B₀ I X)
    (hq : IsLnTwoQuot X 3) (he : ∃ e ∈ oTwoUpper H ⊓ X, orderOf e = 3)
    (hred : ¬ IsIrredOnSection (sOf152 T Mc M B₀) (oTwoUpper H) (pCoreOf 2 (oTwoUpper H)))
    (h21 : ∀ H₁ H₂ : Subgroup G, IsHPair H (V154 T Mc M) H₁ H₂ →
      Lemma15221ConclW T Mc M H H₁ H₂ B₀ I)
    (h12 : He12.StageLemma15212W) :
    IsThreePrimeGroup (M ⊓ Subgroup.centralizer (V154 T Mc M : Set G)) := by
  obtain ⟨H₁, H₂, hpair⟩ := c.inputs.hN.pair
  have h21' := h21 H₁ H₂ hpair
  have hKcle : conjClosure (oTwoUpper H) Mc ≤ Mc ⊓ I :=
    ((h21'.one hred).2.2.1).trans (centralizer_zS_le_inf152 c.inputs)
  obtain ⟨e, heKX, he3⟩ := he
  have hKc : conjClosure (oTwoUpper H) Mc = oTwoUpper H := by
    obtain ⟨B, hB⟩ := c.inputs.hN.sigmaPrime_nonempty
    rcases (h12 G T Mc M c.setting H c.hstar B hB).cases with h | h | h | h
    · exact h
    all_goals
      exact (false_of_perfect c hN hq hKcle (perfect_of_cases (by tauto))
        (le_conjClosure _ _ heKX.1) heKX.2 he3).elim
  exact h21'.two hKc

end S15223P4.Kc

end CFSG.Quasithin
