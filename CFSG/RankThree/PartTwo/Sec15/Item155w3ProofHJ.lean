module

public import CFSG.RankThree.PartTwo.Sec15.Item155w2ProofCases
public import CFSG.RankThree.PartTwo.Sec15.Item155w2ProofGrow
public import CFSG.RankThree.PartTwo.Sec15.Item155RProof
public import CFSG.RankThree.PartTwo.Sec14.Concl142HJ
import CFSG.RankThree.PartTwo.Sec16.Item166Res4ProofOmg
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

namespace Proof155w3

theorem isoLThreePi_of_mulEquiv {X X' : Type} [Group X] [Group X'] {p e : ℕ} [Fact p.Prime]
    (φ : X ≃* X') (h : Sec4.IsoLThreePi X p e) : Sec4.IsoLThreePi X' p e := by
  rcases h with ⟨hq, ⟨ψ⟩⟩ | ⟨hq, ⟨ψ⟩⟩
  · exact Or.inl ⟨hq, ⟨φ.symm.trans ψ⟩⟩
  · exact Or.inr ⟨hq, ⟨φ.symm.trans ψ⟩⟩

theorem isoLThreePi_two_of_projSL_even {X : Type} [Group X] (k : ℕ)
    (φ : X ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 (2 * k))) :
    Sec4.IsoLThreePi X 2 (2 * k) := by
  refine Or.inl ⟨?_, ⟨φ⟩⟩
  rw [pow_mul, Nat.pow_mod]
  norm_num

theorem not_isL3TwoPow_of_allPointsHJ {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (hHJ : AllPointsHJ A) {c' : G}
    (hc' : Subgroup.zpowers c' ∈ omegaA A) {L' : Subgroup G} (hL' : L' ∈ lA A c') :
    ¬ Sec16.IsL3TwoPow L' := by
  obtain ⟨Le, hLe, ⟨φ⟩⟩ := hHJ c' hc'
  have h3 : 3 ∣ Nat.card Le := by
    have hc := Nat.card_congr φ.toEquiv
    rw [KFacts.KS14.card_nativeJ2] at hc
    have hdvd := Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 ↥Le)
    rw [hc] at hdvd
    exact (by norm_num : (3 : ℕ) ∣ 604800).trans hdvd
  have hLeL : Le = L' := (h.chosen136.2 c' hc' L' hL').2 Le hLe.1 h3
  subst hLeL
  rintro ⟨n, -, hiso⟩
  exact KFacts.KS14.ks17J2NotList.1 2 n (isoLThreePi_of_mulEquiv φ hiso)

section Read


theorem false_of_isoLThreePi_of_allPointsHJ {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h148 : Item148 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (hHJ : AllPointsHJ A) {Y : Subgroup G}
    (hY : Y ∈ scriptY4 A (lB A)) {m : ℕ} (hm : 1 ≤ m)
    (hiso : Sec4.IsoLThreePi (↥Y ⧸ CFSG.pCore 2 ↥Y) 2 m) : False :=
  Sec16.Proof166Res4.false_of_isoLThreePi_two h148 h.toSec13Data.isElemAbelian.1 h.chosen136
    (fun _ _ hc' hL' => not_isL3TwoPow_of_allPointsHJ h hHJ hc' hL') hY
    (rank3II_15_1_lB h.isE27 hbot hY) hm hiso

theorem not_case154Two_of_allPointsHJ {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h148 : Item148 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥) (hHJ : AllPointsHJ A) {L' Y X : Subgroup G}
    (hY : Y ∈ scriptY4 A (lB A)) : ¬ Case154Two L' Y X := by
  rintro ⟨n, m, hn, hm, ⟨φ⟩, -, -⟩
  refine false_of_isoLThreePi_of_allPointsHJ h h148 hbot hHJ hY (m := 2 * (n * m)) ?_ ?_
  · have := Nat.mul_pos (by omega : 0 < n) (by omega : 0 < m)
    omega
  · rw [show 2 * n * m = 2 * (n * m) by ring] at φ
    exact isoLThreePi_two_of_projSL_even (n * m) φ

end Read

end Proof155w3

open Proof155w3

@[expose] noncomputable def Step155CasesTwoNHJW (A : Subgroup G) (c : G) (L : Subgroup G) :
    Prop :=
  Sec14Std G A c L → ¬ AllPointsHJ A → ∀ X K Y M T : Subgroup G, Ctx155 A X K Y M T →
    MaxT155 A X K T → Above155w A X → ∀ J ∈ thetaComponentsIn M, J ∈ scriptY0 A (lB A) →
    X ≤ J → (¬ ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
      L' = (L' ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L') →
    ¬ (Case154Two L J X ∧ IsLThreePi (↥X ⧸ CFSG.pCore 2 ↥X))

@[expose] noncomputable def Step155GrowAltTwoNHJW (A : Subgroup G) (c : G) (L : Subgroup G) :
    Prop :=
  Sec14Std G A c L → ¬ AllPointsHJ A → ∀ X K Y M T : Subgroup G, Ctx155 A X K Y M T →
    MaxT155 A X K T → Above155w A X → ¬ K ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 Y : Set G) →
    ⁅CFSG.Open.pCoreOf 2 K, K⁆ ≤ CFSG.Open.pCoreOf 2 Y →
    ¬ ⁅CFSG.Open.pCoreOf 2 Y, K⁆ ≤ CFSG.Open.pCoreOf 2 K →
    Case154Two L K X →
    (¬ ∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi (↥X ⧸ CFSG.pCore 2 ↥X) 2 n) →
    IsEmpty (↥X ⧸ CFSG.pCore 2 ↥X ≃* alternatingGroup (Fin 5)) →
    (¬ ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
      L' = (L' ⊓ X) ⊔ CFSG.Open.pCoreOf 2 L') →
      Claim155 A K Y

@[expose] noncomputable def Step155UpPiNHJ (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ¬ AllPointsHJ A → ∀ Y, IsY155 A Y →
    (¬ ∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi (↥(oPrimeResidualOf 3 Y) ⧸
      CFSG.pCore 2 ↥(oPrimeResidualOf 3 Y)) 2 n) →
    IsEmpty (↥(oPrimeResidualOf 3 Y) ⧸ CFSG.pCore 2 ↥(oPrimeResidualOf 3 Y) ≃*
      alternatingGroup (Fin 5)) →
    (¬ ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
      L' = (L' ⊓ oPrimeResidualOf 3 Y) ⊔ CFSG.Open.pCoreOf 2 L') →
    ∀ M ∈ CFSG.maximalTwoLocalsContaining ((A ⊔ Y : Subgroup G) : Set G),
    ∀ J ∈ thetaComponentsIn M, J ∈ scriptY0 A (lB A) → oPrimeResidualOf 3 Y < J →
    (∃ n : ℕ, 1 ≤ n ∧ Sec4.IsoLThreePi (↥J ⧸ CFSG.pCore 2 ↥J) 2 n) →
    ∀ K ∈ scriptY0Star A (lB A), J ≤ K →
      (∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ L' ∈ lA A c' ∧
        L' = (L' ⊓ J) ⊔ CFSG.Open.pCoreOf 2 L') ∨ K = J ⊔ CFSG.Open.pCoreOf 2 K

@[expose] noncomputable def Step155CasesTwoNHJWR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step155CasesTwoNHJW A c L

@[expose] noncomputable def Step155GrowAltTwoNHJWR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step155GrowAltTwoNHJW A c L

@[expose] noncomputable def Step155UpPiNHJR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step155UpPiNHJ A c L

section Provers


theorem step155CasesTwoW_of_nhj {A : Subgroup G} {c : G} {L : Subgroup G}
    (h148 : Item148 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (hres : Step155CasesTwoNHJW A c L) : Step155CasesTwoW A c L := by
  intro h X K Y M T hC hmax hab J hJM hJ0 hXJ hcl
  by_cases hHJ : AllPointsHJ A
  · exact fun ⟨htwo, _⟩ => not_case154Two_of_allPointsHJ h h148 hbot hHJ hJ0.1 htwo
  · exact hres h hHJ X K Y M T hC hmax hab J hJM hJ0 hXJ hcl

theorem step155GrowAltTwoW_of_nhj {A : Subgroup G} {c : G} {L : Subgroup G}
    (h148 : Item148 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (hres : Step155GrowAltTwoNHJW A c L) : Step155GrowAltTwoW A c L := by
  intro h X K Y M T hC hmax hab hKR hZR hRK htwo hpi ha5 hcl
  by_cases hHJ : AllPointsHJ A
  · exact (not_case154Two_of_allPointsHJ h h148 hbot hHJ hC.mem_k.prop.1 htwo).elim
  · exact hres h hHJ X K Y M T hC hmax hab hKR hZR hRK htwo hpi ha5 hcl

theorem step155UpPi_of_nhj {A : Subgroup G} {c : G} {L : Subgroup G}
    (h148 : Item148 A (lB A)) (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (hres : Step155UpPiNHJ A c L) : Step155UpPi A c L := by
  intro h Y hY hXpi hXa5 hXcl M hM J hJM hJ0 hXJ hJpi K hK hJK
  by_cases hHJ : AllPointsHJ A
  · obtain ⟨n, hn, hiso⟩ := hJpi
    exact (false_of_isoLThreePi_of_allPointsHJ h h148 hbot hHJ hJ0.1 hn hiso).elim
  · exact hres h hHJ Y hY hXpi hXa5 hXcl M hM J hJM hJ0 hXJ hJpi K hK hJK

theorem step155CasesTwoWR_of_nhj (h148 : Item148R) (hbot : Item145BotS14)
    (hres : Step155CasesTwoNHJWR) : Step155CasesTwoWR :=
  fun G _ _ A c L hR => step155CasesTwoW_of_nhj (h148 G A c L hR) (hbot G A c L hR.toSec14Std)
    (hres G A c L hR)

theorem step155GrowAltTwoWR_of_nhj (h148 : Item148R) (hbot : Item145BotS14)
    (hres : Step155GrowAltTwoNHJWR) : Step155GrowAltTwoWR :=
  fun G _ _ A c L hR => step155GrowAltTwoW_of_nhj (h148 G A c L hR)
    (hbot G A c L hR.toSec14Std) (hres G A c L hR)

theorem step155UpPiR_of_nhj (h148 : Item148R) (hbot : Item145BotS14)
    (hres : Step155UpPiNHJR) : Step155UpPiR :=
  fun G _ _ A c L hR => step155UpPi_of_nhj (h148 G A c L hR) (hbot G A c L hR.toSec14Std)
    (hres G A c L hR)

end Provers

end CFSG.RankThree.PartTwo.Sec15
