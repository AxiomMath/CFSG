module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.VZeroSmall17
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSevenB
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ui

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.CGT.Timmesfeld75 (IsTI)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.WeakClosure81 (Star914)

variable {G : Type} [Group G] [Finite G]

theorem card_vzero_le_four_of_w3Lem914N7_syl (hTim : CFSG.CGT.Timmesfeld75.NodeStatement)
    (hcat : ¬ CFSG.Blueprint.Catalog G) (D : Data G) (h66 : UC6.R6_6 D) (h86 : W3Lem86_1 G)
    (h88 : W3Thm88 G) (h126 : R126 D) (h914 : W3Lem914N7 G) (hstar : StarOfSylThreeStmt)
    {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hN : (L.subgroupOf (L ⊔ D.T)).Normal)
    (hLperfect : L = CFSG.Quasithin.perfectCore (L ⊔ CFSG.Open.pCoreOf 2 (L ⊔ D.T)))
    (hψ : ∃ (Z : Type) (_ : Group Z) (ψ : ↥(L ⊔ D.T) →* Z), Function.Surjective ψ ∧
      (∀ x : ↥(L ⊔ D.T), ψ x = 1 ↔ (x : G) ∈ CFSG.Open.pCoreOf 2 (L ⊔ D.T)) ∧
      CFSG.IsComponent ((L.subgroupOf (L ⊔ D.T)).map ψ))
    (hAut : ∃ (A : Type) (_ : Group A)
      (φ : ↥((L ⊔ D.T) ⊓ normalizer (L : Set G)) →* A), Function.Surjective φ ∧
      (∀ x : ↥((L ⊔ D.T) ⊓ normalizer (L : Set G)),
        φ x = 1 ↔ (x : G) ∈ centSection (L ⊔ D.T) L (oTwoThreeIn L)) ∧
      CFSG.Quasithin.F6.IsPGL2 7 A)
    (hSyl : ∀ P : Subgroup G, IsSylowIn 3 P (L ⊔ D.T) →
      P ∈ CFSG.LocalAnalysis.WeakClosure81.calP V₀)
    (hU : UniqueMax D.M (L ⊔ D.T)) : Nat.card V₀ ≤ 4 := by
  by_contra h4
  have hV₀p : IsPGroup 2 V₀ := CFSG.Open.IsElemAbelian.isPGroup h.pairFacts.elemAbelian₀
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hV₀p
  rw [hm] at h4
  have h8 : 8 ≤ Nat.card V₀ := by
    rw [hm]
    have hm3 : 3 ≤ m := by
      by_contra h
      apply h4
      have hm2 : m ≤ 2 := by omega
      calc 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hm2
        _ = 4 := by norm_num
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
  have hne : V₀ ≠ ⊥ := by
    rintro rfl
    simp at h8
  have hW : InCalV D.M V₀ := hyp125_inCalV h hne
  have hTI : IsTI V₀ := hyp125_isTI h hne
  have h9 : CFSG.LocalAnalysis.WeakClosure81.Hyp9 V₀ D.T := hyp9_of_hyp125 hTim hcat D h h8
  have hNV : normalizer (V₀ : Set G) = D.M := normalizer_eq_of_inCalV D hW
  have h1 : ¬ normalizer (E3.wClos V₀ 1 D.T : Set G) ≤ D.M :=
    twelve_seven_three_one hTim hcat D h66 h88 h.2 hW hTI h8
      (fun z hz hzc hz1 => hyp125_centralizer_le h hne hz hzc hz1)
  have hNM : L ⊔ D.T ≤ D.M := sup_le hL.1.le D.sylowM.le
  have hle : L ⊔ D.T ≤ normalizer (V₀ : Set G) := by
    rw [hNV]
    exact hNM
  have hTL : D.T ≤ normalizer (L : Set G) :=
    le_sup_right.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp hN)
  rcases h914 V₀ D.T (L ⊔ D.T) L h9 le_sup_right hle (sup_comm ..) hLperfect hTL hψ hAut
      (hstar G V₀ (L ⊔ D.T) hSyl) with h2 | h2
  · exact h1 (hNV ▸ h2)
  · exact twelve_seven_one hTim hcat D h86 h126 h.2 hW hTI h8
      (uc22p22u_uniqueMax_mono D (le_inf hNM h2) inf_le_left hU)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
