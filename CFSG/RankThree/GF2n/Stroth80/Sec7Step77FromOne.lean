module

public import CFSG.RankThree.GF2n.Stroth80.Sec7GStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


@[expose] def Step77FromOneCoreStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaMinusNat hc t 2 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ g ∈ M, ∀ s : G, s * (g * t * g⁻¹)⁻¹ ∈ Q → ⁅s, t⁆ ∈ Q → s ∉ Z0 →
    ∃ g' ∈ M, ∃ s' : G, s' * (g' * t * g'⁻¹)⁻¹ ∈ Q ∧ ⁅s', t⁆ ∈ Q ∧ s' ∉ Z0 ∧
      Vt M (LB M Q B) B Z t ⊓ conjSubgroup g' (Vt M (LB M Q B) B Z t) ≠ Z

theorem step77FromOne_of_core (hcore : Step77FromOneCoreStatement) :
    Step77FromOneStatement := by
  intro G _ _ M Q Z B hc n t hs hno hom Z0 hZ0 hH g hgM s hs1 hs2 hs3
  obtain ⟨g', hg'M, s', hs'1, hs'2, hs'3, hne⟩ :=
    hcore G M Q Z B hc n t hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3
  exact hne (hH g' hg'M s' hs'1 hs'2 hs'3)

end CFSG.RankThree.GF2n.Stroth80
