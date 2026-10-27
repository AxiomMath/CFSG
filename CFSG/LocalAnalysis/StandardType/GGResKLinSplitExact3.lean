module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeLinear
public import CFSG.LocalAnalysis.StandardType.GGResFixedWeylCentralizer
import CFSG.LocalAnalysis.StandardType.GGResSingularAExactTwo
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpBstar
import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem GGResHyp.not_exactThree_K_of_linear_split_K
    (hLB : GGLBalanceInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hA : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .A ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1) p Bs K) :
    ¬ GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny := by
  classical
  intro hD
  obtain ⟨hperf, lab, hlab, hraw⟩ := hA
  obtain ⟨-, -, -, -, -, -, -, ⟨htag, hr, hpq⟩, -, -⟩ := largeEvenRawDatum_exists hraw
  have hlabeq : lab = ⟨.A, lab.rank, lab.n⟩ := by
    cases lab
    simp_all
  have hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = ⟨.A, lab.rank, lab.n⟩) p Bs K := by
    refine ⟨hperf, lab, hlab, ?_⟩
    exact largeEvenRawDatum_mono (fun _ _ _ _ hq => by
      obtain ⟨hs, hn, θ, _, hN, hact⟩ := hq
      exact ⟨hs, hn, θ, hlabeq, hN, hact⟩) hraw
  have hfwd := hH.fix_mem_centralizer_J_of_typeA_marking_K_exactThree hr hpq hmark hLB hD
  have hcent := (ggResExact3_typed_dichotomy_K_base_of_fixed hH hfwd hD).2
  have hlt : B < Bs := hH.1.B_lt_Bs_of_centralizer_J_card (by
    rw [hcent]
    exact Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (by norm_num))
  obtain ⟨F, hField, -, hChar, hN, φ, -, -, hker, hdiag⟩ :=
    exists_diagonal_cover_of_large_linear_side_of_marking hH (Or.inr ⟨y, hH.2.2.2.2.1⟩)
      (by omega : 3 ≤ lab.rank) hpq hmark
  let : Field F := hField
  let : CharP F 2 := hChar
  obtain ⟨T, hT1, hT2, -, hTN⟩ := exists_isPGroup_two_normalized_of_diagonal_cover
    (by omega : 2 ≤ lab.rank + 1) hN φ hker (fun b => hdiag _ ⟨b, rfl⟩)
  exact hH.1.not_normalizes_two_of_B_lt_Bs hlt hT2 hT1 hTN

end CFSG.StandardType

end
