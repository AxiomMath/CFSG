module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Step77PairModel
public import CFSG.RankThree.GF2n.Stroth80.Sec7Step77One

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


@[expose] def Step77OneWildCaseStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaMinusNat hc t 2 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ g ∈ M, ∀ s : G, s * (g * t * g⁻¹)⁻¹ ∈ Q → ⁅s, t⁆ ∈ Q → s ∉ Z0 →
    conjSubgroup g (Vt M (LB M Q B) B Z t) ≠ Vt M (LB M Q B) B Z t →
    (∃ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅s, w⁆ ∉ Vt M (LB M Q B) B Z t) →
    Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t) = Z

@[expose] def Step77OneTameD2Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaMinusNat hc t 2 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ g ∈ M, ∀ s : G, s * (g * t * g⁻¹)⁻¹ ∈ Q → ⁅s, t⁆ ∈ Q → s ∉ Z0 →
    (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅s, w⁆ ∈ Vt M (LB M Q B) B Z t) →
    Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t)) =
      Nat.card Z ^ 3 → False

@[expose] def Step77OneTameD3Statement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaMinusNat hc t 2 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ g ∈ M, ∀ s : G, s * (g * t * g⁻¹)⁻¹ ∈ Q → ⁅s, t⁆ ∈ Q → s ∉ Z0 →
    (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅s, w⁆ ∈ Vt M (LB M Q B) B Z t) →
    Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t)) =
      Nat.card Z ^ 4 → False

theorem step77OneNotNorm_of_cases (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement)
    (hZcard : Sec7ZCardStatement) (hWild : Step77OneWildCaseStatement)
    (hD2 : Step77OneTameD2Statement) (hD3 : Step77OneTameD3Statement) :
    Step77OneNotNormStatement := by
  intro G _ _ M Q Z B hc n t hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3 hV
  by_cases hw : ∃ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅s, w⁆ ∉ Vt M (LB M Q B) B Z t
  · exact hWild G M Q Z B hc n t hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3 hV hw
  · exfalso
    have htame : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅s, w⁆ ∈ Vt M (LB M Q B) B Z t := by
      intro w hwW
      by_contra hn
      exact hw ⟨w, hwW, hn⟩
    obtain ⟨d, hd4, hcard, hd, hge⟩ :=
      step77OneMeet_facts_of_inputs h34 hRoot h310chi hZc hZV hZcard G M Q Z B hc n t hs hom Z0
        hZ0 g hgM s hs1
    have hd2 : 2 ≤ d := hge htame
    have hd3 : d ≤ 3 := by
      by_contra h
      exact hV (hd (by omega))
    have hq : 1 < Nat.card Z := by
      have := hc.hyp.q4
      omega
    rcases (by omega : d = 2 ∨ d = 3) with h | h
    · refine hD2 G M Q Z B hc n t hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3 htame ?_
      rw [hcard, h]
    · refine hD3 G M Q Z B hc n t hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3 htame ?_
      rw [hcard, h]

end CFSG.RankThree.GF2n.Stroth80
