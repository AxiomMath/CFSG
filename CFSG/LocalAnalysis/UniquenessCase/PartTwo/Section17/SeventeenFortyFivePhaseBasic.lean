module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFivePhaseProps
public import CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuterSylow
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.RankThree.PartOne.CTP.OutEmbed
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15O1219Sigma

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open Subgroup CFSG.Open
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped Pointwise commutatorElement

theorem phase45_card_sup {X : Type} [Group X] [Finite X] {A₁ A₂ : Subgroup X}
    (hA1 : Nat.card A₁ = 31) (hA2 : Nat.card A₂ = 31) (hA12 : A₁ ⊓ A₂ = ⊥)
    (hA12c : A₁ ≤ centralizer (A₂ : Set X)) :
    Nat.card (A₁ ⊔ A₂ : Subgroup X) = 31 ^ 2 ∧ IsMulCommutative (A₁ ⊔ A₂ : Subgroup X) := by
  have hne : A₁ ≠ A₂ := by
    intro h
    have hbot : A₁ = ⊥ := by rw [← hA12, ← h, inf_idem]
    have hcard : Nat.card A₁ = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  have hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a := by
    intro a ha b hb
    exact ((Subgroup.mem_centralizer_iff.mp (hA12c ha)) b hb).symm
  obtain ⟨hE, hcard⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.S15.O1219SigmaProof.card_sup_eq_sq (p := 31)
      (by norm_num) hA1 hA2 hne hcomm
  exact ⟨hcard, hE.1⟩

theorem phase45_false_of_generation {X : Type} [Group X] {L A₁ A₂ B T ML C : Subgroup X}
    (hML : ML ≤ L) (hMLne : ML ≠ L) (hTML : T ⊓ L ≤ ML)
    (hC5 : ∀ C : Subgroup X, IsMulCommutative C → (A₁ ≤ C ∨ A₂ ≤ C ∨ B ≤ C) →
      L ⊓ normalizer (C : Set X) ≤ ML)
    (hCab : IsMulCommutative C) (hA1C : A₁ ≤ C)
    (hgen : L ≤ (T ⊓ L) ⊔ (L ⊓ normalizer (C : Set X))) : False := by
  have hCN : L ⊓ normalizer (C : Set X) ≤ ML := hC5 C hCab (Or.inl hA1C)
  exact hMLne (le_antisymm hML (hgen.trans (sup_le hTML hCN)))

theorem phase45_sup_le_of_isPByAbelian_outer {X : Type} [Group X] [Finite X]
    {L A₁ A₂ B : Subgroup X} (hLn : L.Normal) (hCL : centralizer (L : Set X) = ⊥)
    (hA1 : Nat.card A₁ = 31) (hA2 : Nat.card A₂ = 31) (hA12c : A₁ ≤ centralizer (A₂ : Set X))
    (hcomm : ⁅A₁ ⊔ A₂, B⁆ = A₁ ⊔ A₂)
    (hout : CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoOuter.IsPByAbelian 3 (Outer ↥L)) :
    A₁ ⊔ A₂ ≤ L := by
  haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨N, _, hN3, hNcom⟩ := hout
  let φ : X →* Outer ↥L := CFSG.RankThree.PartOne.CTP.outerHom L
  have hker : φ.ker = L := CFSG.RankThree.PartOne.CTP.ker_outerHom L hCL
  have hA1p : IsPGroup 31 A₁ := IsPGroup.of_card (n := 1) (by rw [hA1, pow_one])
  have hA2p : IsPGroup 31 A₂ := IsPGroup.of_card (n := 1) (by rw [hA2, pow_one])
  have hnorm : A₁ ≤ Subgroup.normalizer (A₂ : Set X) :=
    hA12c.trans (Subgroup.centralizer_le_normalizer (A₂ : Set X))
  have hAp : IsPGroup 31 ↥(A₁ ⊔ A₂) := IsPGroup.to_sup_of_normal_right' hA1p hA2p hnorm
  have hcommut : ⁅A₁ ⊔ A₂, B⁆ ≤ N.comap φ := by
    refine Subgroup.commutator_le.mpr ?_
    intro a ha b hb
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact hNcom (φ a) (φ b)
  rw [hcomm] at hcommut
  have hmapN : (A₁ ⊔ A₂).map φ ≤ N := Subgroup.map_le_iff_le_comap.mpr hcommut
  have hmapP : IsPGroup 31 ↥((A₁ ⊔ A₂).map φ) := hAp.map φ
  have hdisj : Disjoint ((A₁ ⊔ A₂).map φ) N :=
    IsPGroup.disjoint_of_ne 31 3 (by norm_num) _ _ hmapP hN3
  have hbot : (A₁ ⊔ A₂).map φ = ⊥ := by
    rw [disjoint_iff] at hdisj
    rwa [inf_eq_left.mpr hmapN] at hdisj
  rw [← hker, ← Subgroup.map_eq_bot_iff]
  exact hbot

theorem phase45_false_of_charTwo (hK1a : K45CharTwoNormal) (hK1b : K45CharTwoBorelGen)
    {X : Type} [Group X] [Finite X] {L A₁ A₂ B T ML : Subgroup X}
    (hc : PhaseConfig45 L A₁ A₂ B T ML) {d : TauCeti.ValidLieTypeIndex}
    (e : ↥L ≃* (TauCeti.CFSGIndex.lie d).Group) (h2 : d.1.characteristic = 2)
    (htits : d.1 ≠ .tits) : False := by
  have hAnorm : A₁ ⊔ A₂ ≤ normalizer ((T ⊓ L : Subgroup X) : Set X) :=
    hK1a X L A₁ A₂ B T d hc.hLn hc.hCL ⟨e⟩ h2 htits hc.hA1 hc.hA2 hc.hA12 hc.hA12c
      hc.hB5 hc.hBA1 hc.hBA2 hc.hcomm hc.hT hc.hAT hc.hTL
  obtain ⟨C, hCab, hA1C, hgen⟩ :=
    hK1b X L A₁ A₂ B (T ⊓ L) d hc.hLn hc.hCL ⟨e⟩ h2 htits hc.hA1 hc.hA2 hc.hA12
      hc.hA12c hc.hB5 hc.hBA1 hc.hBA2 hc.hcomm hc.hTL hAnorm
  exact phase45_false_of_generation hc.hML hc.hMLne hc.hTML hc.hC5 hCab hA1C hgen

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
