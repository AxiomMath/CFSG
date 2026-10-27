module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec6Split
public import CFSG.RankThree.GF2n.Stroth80.HeringSec6Proved

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

namespace HS6


@[expose] def Stroth65XNormalStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Stroth6Hyp hc n t → ∀ m : ℕ, 3 ≤ m → n = 2 * m →
    (OmegaPlusNat hc t m ∨ OmegaMinusNat hc t m) → ∀ X : Subgroup G,
      Q ≤ X → X ≤ Rt M (LB M Q B) t → hc.CN t ⊔ X = Rt M (LB M Q B) t → hc.CN t ⊓ X = Q →
      (∀ a ∈ hc.CN t, ∀ x ∈ X, ⁅a, x⁆ ∈ Q) →
      ((OmegaPlusNat hc t m ∧ QuotSat X Q (IsOmegaPlus m (Nat.card Z))) ∨
        (OmegaMinusNat hc t m ∧ QuotSat X Q (IsOmegaMinus m (Nat.card Z)))) →
      (X.subgroupOf M).Normal ∧ ∃ C : Subgroup G,
        (∀ h, h ∈ C ↔ h ∈ H0 M Z ∧ ∀ x ∈ X, ⁅h, x⁆ ∈ Q) ∧ Lgen M (hc.CN t) = C ∧ C ⊓ X = Q ∧
        QuotSat C Q (IsSLModel 2 (Nat.card Z))

theorem stroth65X_of_split_normal (hS : Stroth65XSplitStatement)
    (hN : Stroth65XNormalStatement) : Stroth65XStatement := by
  intro G _ _ M Q Z B hc n t hs m hm hn hΩ
  obtain ⟨X, hQX, hXR, hNX, hNXQ, hcom, hsat⟩ := hS G M Q Z B hc n t hs m hm hn hΩ
  obtain ⟨hnorm, C, hC, hLC, hCX, hCsat⟩ :=
    hN G M Q Z B hc n t hs m hm hn hΩ X hQX hXR hNX hNXQ hcom hsat
  exact ⟨X, C, hQX, hXR, hNX, hNXQ, hcom, hnorm, hsat, hC, hLC, hCX, hCsat⟩

end HS6

section Certs

theorem stroth65XSplit_holds : HS6.Stroth65XSplitStatement :=
  HS6.stroth65XSplit_of_inputs stroth34Statement_unconditional
    (stroth310Root_of_34 stroth34Statement_unconditional) stroth51Statement_unconditional
    (griessCoverStatement_of_table
      CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement
      griessSL34Statement_holds)

theorem stroth65Statement_of_normal (h54 : Stroth54Statement)
    (hN : HS6.Stroth65XNormalStatement) : Stroth65Statement :=
  stroth_6_5 stroth34Statement_unconditional stroth310Statement_unconditional h54
    (stroth_6_1 stroth34Statement_unconditional stroth6LBStatement_holds
      stroth6SLDimStatement_holds)
    (stroth_6_2 stroth34Statement_unconditional stroth6LBStatement_holds)
    (stroth_6_3a stroth34Statement_unconditional stroth6LBStatement_holds)
    (HS6.stroth65X_of_split_normal stroth65XSplit_holds hN)

end Certs

end CFSG.RankThree.GF2n.Stroth80
