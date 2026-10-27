module

public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
public import CFSG.Quasithin.EmptyFaithful.S1414Defs
public import CFSG.Quasithin.EmptyFaithfulMultiple.Input311Solvable

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem theorem311_of_theoremC58 (hC : TheoremC58) : Theorem311 :=
  theorem311Stmt_of_C58 hC

theorem theoremC58_of_theorem311 (h : Theorem311) : TheoremC58 := by
  intro G _ _ T hs hnab hK hT H M₀ R hC hR
  have hTH : T ≤ H := hC.sylow_TH.1
  have hRT : R ≤ T := hC.R_le
  have hR2 : IsPGroup 2 R := hT.1.to_le hRT
  have hRM₀ : R ≤ M₀ := hRT.trans hC.TH_le
  have hM₀ : InH T M₀ := by
    refine ⟨hC.TH_le, fun h0 => hR (le_bot_iff.mp ?_)⟩
    rw [← h0]
    exact le_pCoreOf_of_le_normalizer 2 hRM₀ hC.normal_R hR2
  have hH : InH T H := by
    refine ⟨hTH, fun h0 => hR (le_bot_iff.mp ?_)⟩
    have hHb : H ≤ ⊥ := by
      have := hC.charTwo_H
      unfold CharTwo at this
      rw [h0] at this
      intro x hx
      exact this ⟨hx, by simp [Subgroup.mem_centralizer_iff]⟩
    exact (hRT.trans hTH).trans hHb
  exact h G T hs hnab hK hT M₀ H R hM₀ hH hC.unique_max hR hRT hC.sylow_R hC.normal_R

@[expose] def Theorem311Nonsolvable : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → quasithinIsQTKECat G → quasithinIsSylowTwo T →
    ∀ M₀ H R : Subgroup G, InH T M₀ → InH T H → ¬ Group.IsSolvable H →
      (∃ N : Subgroup G, IsUniqueMaxOver H T N) →
      R ≠ ⊥ → R ≤ T → IsSylowTwoOf R (oTwoUpper H ⊔ R) →
      M₀ ≤ Subgroup.normalizer (R : Set G) →
      ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ R ∧ M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G)

theorem theorem311_of_solvable_nonsolvable (hS : EmptyFaithfulMultiple.Input311Solvable)
    (hN : Theorem311Nonsolvable) : Theorem311 := by
  intro G _ _ T hs hnab hK hT M₀ H R hM₀ hH hu hR1 hRT hRS hRn
  by_cases hsolv : Group.IsSolvable H
  · exact hS G T hs hnab hK hT M₀ H R hM₀ hH hsolv hu hR1 hRT hRS hRn
  · exact hN G T hs hnab hK hT M₀ H R hM₀ hH hsolv hu hR1 hRT hRS hRn

theorem theoremC58_of_solvable_nonsolvable (hS : EmptyFaithfulMultiple.Input311Solvable)
    (hN : Theorem311Nonsolvable) : TheoremC58 :=
  theoremC58_of_theorem311 (theorem311_of_solvable_nonsolvable hS hN)

end CFSG.Quasithin
