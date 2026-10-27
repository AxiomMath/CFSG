module

public import CFSG.Timmesfeld.Reduction.RootClass
public import CFSG.Timmesfeld.Final.Conclusion

public section

namespace CFSG.Timmesfeld

open CFSG.Blueprint CFSG.Open

@[expose] def RootSetInput : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → RootClosure D ∧ SpecialClosure D

@[expose] def MoufangInput : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D →
    RootMoufang D ∨ Nonempty (G ≃* alternatingGroup (Fin 6)) ∨ NativeSporadic.IsSporadic G .J2

@[expose] def ARSInput : Prop :=
  ∀ (G : Type) [Group G] (R : Set (Subgroup G)), ARS.Hyp G R → Outcome G

theorem outcome_of_inputs (hR : RootSetInput) (hM : MoufangInput) (hA : ARSInput)
    {G : Type} [Group G] {D : Set G} (h : Hyp G D) : Outcome G := by
  obtain ⟨hc, hs⟩ := hR G D h
  rcases hM G D h with hm | he | hj
  · exact hA G (rootClass D) (arsHyp_rootClass h hc hs hm)
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inl he))))))
  · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr hj))))))

theorem conclusions_of_inputs (hR : RootSetInput) (hM : MoufangInput) (hA : ARSInput)
    (G : Type) [Group G] [Finite G] (D : Set G)
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hinv : ∀ d ∈ D, orderOf d = 2)
    (hgen : Subgroup.closure D = ⊤)
    (hodd : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥)
    (hprod : ∀ d ∈ D, ∀ e ∈ D,
      orderOf (d * e) = 2 ∨ orderOf (d * e) = 4 ∨ Odd (orderOf (d * e)))
    (hfour : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) = 4 → (d * e) ^ 2 ∈ D)
    (hnondeg : ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4) :
    (IsSimpleGroup G ∧
      ((Nat.card G ∈ lieOrdersChar 2 ∧
          (∀ n f : ℕ, 2 ≤ n → 1 ≤ f → Nat.card G ≠ ordTwistedA n (2 ^ f)) ∧
          (∀ f : ℕ, 1 ≤ f → Nat.card G ≠ ordBC 2 (2 ^ f))) ∨
        Nonempty (G ≃* PSU3 3 1) ∨
        Nonempty (G ≃* alternatingGroup (Fin 6)) ∨
        Nat.card G = 2 ^ 7 * 3 ^ 3 * 5 ^ 2 * 7)) ∧
    ((EvenLieType G ∧
      (∀ n f : ℕ, 3 ≤ n → 1 ≤ f → ¬ LieModel G .PSU n 2 f) ∧
      (∀ f : ℕ, 1 ≤ f → ¬ LieModel G .PSp 2 2 f)) ∨
    LieModel G .PSU 3 3 1 ∨ Nonempty (G ≃* alternatingGroup (Fin 6)) ∨
      NativeSporadic.IsSporadic G .J2) := by
  have h : Hyp G D := ⟨inferInstance, hclass, ⟨hinv, hprod, hfour⟩, hgen, hodd, hO2, hnondeg⟩
  have ho := outcome_of_inputs hR hM hA h
  exact ⟨decl1_of_outcome ho, decl2_of_outcome ho⟩

end CFSG.Timmesfeld
