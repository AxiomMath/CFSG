module

public import CFSG.LocalAnalysis.StandardType.GGSummandStructBasic
public import CFSG.LocalAnalysis.StandardType.GGD4OddCentVocab

public section

namespace CFSG.StandardType

open CFSG.Assembly

open scoped commutatorElement

section Layer

variable {X : Type} [Group X] [Finite X]

theorem ggPerfect_le_sSup_components {Y H₀ N P : Subgroup X} (hH₀ : IsSubnormal H₀ Y)
    (hN : IsSubnormal N Y) (hPN : P ≤ N) (hperf : ⁅P, P⁆ = P)
    (hP : P ≤ sSup {S | IsComponentOf S H₀}) :
    P ≤ sSup {S | IsComponentOf S H₀ ∧ S ≤ N} := by
  have hdich : ∀ S, IsComponentOf S H₀ → S ≤ N ∨ S ≤ Subgroup.centralizer (N : Set X) := by
    intro S hS
    rcases isComponentOf_le_or_commutator_eq_bot
      (isComponentOf_of_isSubnormal_of_isComponentOf hS hH₀) hN with h | h
    · exact Or.inl h
    · exact Or.inr (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)
  refine ggPerfect_le_of_split (A := N) (T₂ := sSup {S | IsComponentOf S H₀ ∧ ¬ S ≤ N})
    (sSup_le fun S hS => hS.2) ?_ hPN hperf ?_
  · refine sSup_le fun S hS => ?_
    rcases hdich S hS.1 with h | h
    · exact absurd h hS.2
    · exact h
  · refine hP.trans (sSup_le fun S hS => ?_)
    by_cases h : S ≤ N
    · exact le_sup_of_le_left (le_sSup ⟨hS, h⟩)
    · exact le_sup_of_le_right (le_sSup ⟨hS, h⟩)

end Layer

section Bot

variable {X : Type} [Group X]

@[expose] noncomputable def ggQuotBotEquiv (S : Subgroup X) :
    ↥S ⧸ (⊥ : Subgroup X).subgroupOf S ≃* ↥S :=
  (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf (H := S))).trans
    QuotientGroup.quotientBot

theorem ggQuotBotEquiv_mk (S : Subgroup X) (s : ↥S) :
    ggQuotBotEquiv S (QuotientGroup.mk s) = s := rfl

theorem ggQuasisimple_quot_bot {S : Subgroup X} (h : CFSG.Assembly.IsQuasisimple ↥S) :
    CFSG.Assembly.IsQuasisimple (↥S ⧸ (⊥ : Subgroup X).subgroupOf S) := by
  have hperf : Group.IsPerfect ↥S := ⟨h.1⟩
  refine ⟨?_, ?_⟩
  · exact (Group.IsPerfect.ofSurjective (f := (ggQuotBotEquiv S).symm.toMonoidHom)
      (ggQuotBotEquiv S).symm.surjective).commutator_eq_top
  · exact (MulEquiv.isSimpleGroup_congr (centerQuotCongr (ggQuotBotEquiv S))).mpr h.2

theorem ggMarking_quot_bot {S E : Subgroup X}
    (h : LargeEvenMarking ↥S (fun lab _ _ I _ θ => GGChevStTag lab ∧ ∀ ε ∈ E, ∃ φ ∈ I,
      LargeEvenInduces θ (fun l l' : ↥S => (l' : X) = ε⁻¹ * l * ε) φ)) :
    LargeEvenMarking (↥S ⧸ (⊥ : Subgroup X).subgroupOf S) (fun lab _ _ I _ θ => GGChevStTag lab ∧
      ∀ ε ∈ E, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => ∃ s s' : ↥S,
        QuotientGroup.mk s = l ∧ QuotientGroup.mk s' = l' ∧ (s' : X) = ε⁻¹ * s * ε) φ) := by
  refine largeEvenMarking_congr (ggQuotBotEquiv S)
    (fun lab R _ I F θ hθ => ⟨hθ.1, fun ε hε => ?_⟩) h
  obtain ⟨φ, hφI, hφ⟩ := hθ.2 ε hε
  refine ⟨φ, hφI, ?_⟩
  rintro l l' ⟨s, s', rfl, rfl, hss'⟩
  have := hφ s s' hss'
  simpa [centerQuotCongr_mk, ggQuotBotEquiv_mk] using this

theorem isElemAbelian_zpowers_of_mem {p : ℕ} {A : Subgroup X} (hA : IsElemAbelian p A) {b : X}
    (hb : b ∈ A) : IsElemAbelian p (Subgroup.zpowers b) := by
  refine ⟨?_, ?_⟩
  · infer_instance
  · intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h1 : b ^ p = 1 := hA.2 b hb
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h1, one_zpow]

theorem centralizer_zpowers_eq (b : X) :
    Subgroup.centralizer ((Subgroup.zpowers b : Subgroup X) : Set X) =
      Subgroup.centralizer {b} := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

end Bot

end CFSG.StandardType
