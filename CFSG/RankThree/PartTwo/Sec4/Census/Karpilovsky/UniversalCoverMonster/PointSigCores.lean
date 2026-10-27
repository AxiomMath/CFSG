module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSigSignalizers

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSig

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec14
open scoped commutatorElement

@[expose] def coreSup {X : Type} [Group X] (P Y : Subgroup X) : Subgroup X :=
  ⨆ (p : X) (_ : p ∈ P) (_ : p ∉ Subgroup.center X),
    pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({p} : Set X))

section

variable {X : Type} [Group X] {P Y : Subgroup X}

theorem coreSup_le (P Y : Subgroup X) : coreSup P Y ≤ Y :=
  iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
    (pPrimeCoreOf_le 3 _).trans inf_le_left

theorem le_normalizer_coreSup (hP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hPY : P ≤ Subgroup.normalizer (Y : Set X)) :
    P ≤ Subgroup.normalizer (coreSup P Y : Set X) := by
  refine le_normalizer_iSup fun p => le_normalizer_iSup fun hp => le_normalizer_iSup fun _ => ?_
  have hPp : P ≤ Subgroup.centralizer ({p} : Set X) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hP a ha p hp)
  exact fun a ha => normalizer_le_normalizer_pPrimeCoreOf 3 _
    (Subgroup.inf_normalizer_le_normalizer_inf ⟨hPY ha, Subgroup.le_normalizer (hPp ha)⟩)

theorem coreSup_le_iSup_core [Finite X] (P Y : Subgroup X) :
    coreSup P Y ≤ ⨆ (p : X) (_ : p ∈ P) (_ : p ∉ Subgroup.center X),
      pPrimeCoreOf 3 (coreSup P Y ⊓ Subgroup.centralizer ({p} : Set X)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine iSup_le fun p => iSup_le fun hp => iSup_le fun hpZ => ?_
  refine le_iSup_of_le p (le_iSup_of_le hp (le_iSup_of_le hpZ ?_))
  have hRT : pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({p} : Set X)) ≤ coreSup P Y :=
    le_iSup_of_le p (le_iSup_of_le hp (le_iSup_of_le hpZ le_rfl))
  refine le_pPrimeCoreOf (le_inf hRT ((pPrimeCoreOf_le 3 _).trans inf_le_right)) ?_
    (coprime_card_pPrimeCoreOf 3 _)
  intro g hg
  exact le_normalizer_pPrimeCoreOf 3 _
    (Subgroup.mem_inf.mpr ⟨coreSup_le P Y hg.1, hg.2⟩)

theorem exists_centralizer_eq [Finite X] (hP : Late.IsE27 P) {B : Subgroup X} (hB : IsHyperplane P B)
    (hZ : Nat.card (Subgroup.center X) = 3) (hZB : Subgroup.center X ≤ B) :
    ∃ p ∈ B, p ∉ Subgroup.center X ∧
      Subgroup.centralizer (B : Set X) = Subgroup.centralizer ({p} : Set X) := by
  have hBcard : Nat.card B = 9 := by
    have := hB.2
    rw [hP.2] at this
    omega
  obtain ⟨p, hpB, hpZ⟩ : ∃ p ∈ B, p ∉ Subgroup.center X := by
    by_contra hno
    push Not at hno
    have h1 : B ≤ Subgroup.center X := hno
    have := Subgroup.card_le_of_le h1
    omega
  refine ⟨p, hpB, hpZ, ?_⟩
  have hsupB : Subgroup.zpowers p ⊔ Subgroup.center X ≤ B :=
    sup_le (Subgroup.zpowers_le.mpr hpB) hZB
  have hsupcard : Nat.card ↥(Subgroup.zpowers p ⊔ Subgroup.center X) = 9 := by
    have hlt : Subgroup.center X < Subgroup.zpowers p ⊔ Subgroup.center X := by
      refine lt_of_le_of_ne le_sup_right fun h => hpZ ?_
      rw [h]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers p)
    have hdvdB : Nat.card ↥(Subgroup.zpowers p ⊔ Subgroup.center X) ∣ 9 :=
      hBcard ▸ Subgroup.card_dvd_of_le hsupB
    have hdvdZ : Nat.card (Subgroup.center X) ∣ Nat.card ↥(Subgroup.zpowers p ⊔ Subgroup.center X) :=
      Subgroup.card_dvd_of_le le_sup_right
    have hne : Nat.card ↥(Subgroup.zpowers p ⊔ Subgroup.center X) ≠ 3 := by
      intro h3
      have : Subgroup.center X = Subgroup.zpowers p ⊔ Subgroup.center X :=
        Subgroup.eq_of_le_of_card_ge le_sup_right (by omega)
      exact hlt.ne this
    have hpos : 0 < Nat.card ↥(Subgroup.zpowers p ⊔ Subgroup.center X) := Nat.card_pos
    have hd : Nat.card ↥(Subgroup.zpowers p ⊔ Subgroup.center X) ∈ Nat.divisors 9 :=
      Nat.mem_divisors.mpr ⟨hdvdB, by norm_num⟩
    have : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [this] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with h | h | h
    · rw [h, hZ] at hdvdZ
      omega
    · exact absurd h hne
    · exact h
  have hsupeq : Subgroup.zpowers p ⊔ Subgroup.center X = B :=
    Subgroup.eq_of_le_of_card_ge hsupB (by omega)
  apply le_antisymm
  · exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hpB)
  · intro g hg
    have hS : B ≤ Subgroup.centralizer ({g} : Set X) := by
      rw [← hsupeq]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hg).symm
      · intro z hz
        exact Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_center_iff.mp hz) g).symm
    refine Subgroup.mem_centralizer_iff.mpr fun b hb => ?_
    exact Subgroup.mem_centralizer_singleton_iff.mp (hS hb)

theorem le_coreSup_of_le_core [Finite X] (hP : Late.IsE27 P) {B Q : Subgroup X}
    (hB : IsHyperplane P B) (hZ : Nat.card (Subgroup.center X) = 3)
    (hZB : Subgroup.center X ≤ B)
    (hQ : Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set X))) : Q ≤ coreSup P Y := by
  obtain ⟨p, hpB, hpZ, hC⟩ := exists_centralizer_eq hP hB hZ hZB
  rw [hC] at hQ
  exact hQ.trans (le_iSup_of_le p (le_iSup_of_le (hB.1 hpB) (le_iSup_of_le hpZ le_rfl)))

end

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSig
