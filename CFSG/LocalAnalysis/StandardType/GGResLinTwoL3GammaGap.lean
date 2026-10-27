module

public import CFSG.LocalAnalysis.StandardType.GGResLinTwoGammaGap
public import CFSG.LocalAnalysis.StandardType.GGTBJLinearMinusFrame
public import CFSG.LocalAnalysis.StandardType.GGResLinTwoHighRankGeneral
public import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsHolds
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc11R
public import CFSG.LocalAnalysis.StandardType.GGResKLinTwoExact3

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem GGResHyp.false_of_exact3_either_linTwo_rank_ge9
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (lab : LargeEvenLabel) (hlab : GGLinTwoLabel 3 lab)
    (hrank : 9 ≤ lab.rank)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L)
    (hD : GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypAny) : False := by
  classical
  have hpq : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) := hH.2.2.1.1.le_normalizer
  have hL : GGInnerDiagOnLabel (fun p lab' => p = 3 ∧ lab' = lab) 3 Bs L :=
    GGInnerDiagOnLabel.mono_label (fun lab' h => ⟨rfl, h⟩) hmark
  have hlabAeq : lab = (⟨.A, lab.rank, 1⟩ : LargeEvenLabel) := by
    rcases lab with ⟨tag, r, n⟩
    rcases hlab with ⟨htag, -, hn, -⟩
    subst htag
    subst hn
    rfl
  have hmarkA : GGInnerDiagOnLabel
      (fun _ lab' => lab' = (⟨.A, lab.rank, 1⟩ : LargeEvenLabel)) 3 Bs L :=
    GGInnerDiagOnLabel.mono_label (fun lab' h => h.trans hlabAeq) hmark
  have hB : Bs = B := hH.bstar_eq_of_linMinus_side (Or.inl rfl) hpq hmarkA
  obtain ⟨s, T, hTA, hZinj, hEq, hcardE, hsd, hcardBs⟩ :=
    GGResHyp.linTwo_stable_torus hH lab hlab hN hL
  have hs5 : 5 ≤ s := by rw [hsd]; omega
  have hs2 : 2 ≤ s := by omega
  have hcardAL : Nat.card ↥(ggAutomizer L Bs) = 2 ^ s * s.factorial := by
    have h := GGResHyp.linTwo_rank_ge_five_automizerL_card hH lab hlab (by omega) hN hL
    simpa [hsd] using h
  have hWL : GGWeylTypeData s (Nat.card ↥(ggAutomizer L Bs)) 2 := by
    refine Or.inr (Or.inl ⟨hs2, ?_, rfl⟩)
    rw [hcardAL]
  have hS : LargeEvenSStar 3 B x L := hH.1.1.2.2.2.2.2.2.1
  have hcardB : Nat.card B = 3 ^ (s + 1) := by rw [← hB, hcardBs]
  have hm : LargeEvenTwoLocalRank 3 G = s + 1 := by
    apply Nat.pow_right_injective (by norm_num : 2 ≤ 3)
    exact hS.1.2.1.symm.trans hcardB
  have hm5 : 5 ≤ LargeEvenTwoLocalRank 3 G := by omega
  have hsmall : ¬ S2MathAs51642Interfaces.SmallDerived 3 lab := by
    simp [S2MathAs51642Interfaces.SmallDerived, hlab.1]
  have hgcd : ¬ 3 ∣ Nat.gcd (lab.rank + 1) (2 ^ lab.n - 1) := by
    rw [hlab.2.2.1]
    norm_num
  have hcenter : S2MathAs51642Interfaces.CenterPrimeTo 3 lab ∧ lab.tag = .A := by
    refine ⟨?_, hlab.1⟩
    simp only [S2MathAs51642Interfaces.CenterPrimeTo, hlab.1]
    exact ⟨hsmall, hgcd⟩
  have hLsel : GGInnerDiagOnLabel
      (fun p lab' => S2MathAs51642Interfaces.CenterPrimeTo p lab' ∧ lab'.tag = .A) 3 Bs L :=
    GGInnerDiagOnLabel.mono_label (fun lab' h => by
      rw [h.2]
      exact hcenter) hL
  have hJ : GGInnerDiagOn Bs J :=
    q1CenterPrimeLinear_holds G 3 B Bs x L D J hH.1 hLsel
  have hJlab : GGInnerDiagOnLabel (fun _ _ => True) 3 Bs J :=
    (GGInnerDiagOn.label (fun _ _ => True) 3 hJ).mono_label
      (fun _ _ => trivial)
  have hfwd : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
      (b : G) ∈ Subgroup.centralizer (J : Set G) := by
    rcases hH.fix_mem_centralizer_J_or_low_of_tcj
      (ggTBTorAll_of_remaining trivial) ggTBTorLiftRows_holds
      TCJ.ggTCJKnown_holds ggLabelRigidInput_holds hm5 hJlab with
      hfwd | ⟨hm5eq, hA5⟩ | ⟨hm6eq, hE6⟩
    · exact hfwd
    · omega
    · exfalso
      have hs5eq : s = 5 := by omega
      have hr10 : lab.rank ≤ 10 := by omega
      have hJ6 : GGInnerDiagOnLabel GGTableBTwE6ThreeLabel 3 Bs J :=
        hE6.mono_label (fun _ h => h.2)
      obtain ⟨labJ, hΛJ, hhasJ, _, _, _, _, _, ⟨htJ, -, -⟩, -⟩ :=
        largeEvenMarking_exists_hasLabel hJ6
      obtain ⟨labL, hΛL, hhasL, _, _, _, _, _, ⟨hp3L, hlabEq⟩, -⟩ :=
        largeEvenMarking_exists_hasLabel hL
      have htL : labL.tag = .A := by rw [hlabEq]; exact hlab.1
      have hnL : labL.n = 1 := by rw [hlabEq]; exact hlab.2.2.1
      have hrL : labL.rank ≤ 10 := by rw [hlabEq]; exact hr10
      have hJL : J ≤ L := hH.1.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
      exact ggTwE6_false_of_le_linTwo hJL hΛL hhasL htL hnL hrL hΛJ hhasJ htJ
  have hiOne : Bs ⊓ Subgroup.centralizer (J : Set G) = D :=
    hH.iOne_of_linMinus_side (Or.inl rfl) hpq hmarkA
  have hDcard : Nat.card ↥D = 3 ^ 2 := hH.1.2.2.1.2.2.1
  have hγcard : Nat.card (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range = 3 ^ (s - 1) := by
    have hprod := NbrU63.card_range_ggGamma_mul_card_inf hH.Bs_le_normalizer_J
    rw [hiOne, hDcard, hcardBs] at hprod
    have hpow : 3 ^ (s + 1) = 3 ^ (s - 1) * 3 ^ 2 := by
      rw [← pow_add]
      congr 1
      omega
    rw [hpow] at hprod
    exact Nat.mul_right_cancel (by norm_num : 0 < 3 ^ 2) hprod
  have hγ' : 3 ^ (s - 1) ≤
      Nat.card (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range := by rw [hγcard]
  exact hH.not_exactThree_either_of_weylRank_gamma_gap
    (ggTBFixInput_holds) (by omega) hWL hfwd hγ' hD

end CFSG.StandardType

end
