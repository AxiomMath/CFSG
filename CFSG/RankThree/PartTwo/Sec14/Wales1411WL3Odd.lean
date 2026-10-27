module

public import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJ
import CFSG.RankThree.PartTwo.Sec14.Item1413Res6ProofL3

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open scoped commutatorElement

@[expose] def KL3HessETrans2 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p e : ℕ) [Fact p.Prime], p ≠ 2 → 1 ≤ e →
    Sec4.IsoLThreePi X p e → ∀ E : Subgroup X, CFSG.Assembly.IsElemAbelian 3 E →
      Nat.card E = 9 →
      (∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
        ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁) →
      Wales1411W.ETrans2 X E

@[expose] noncomputable def Claim1411NonsolvWPointL3FieldR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
      ∀ Y : Subgroup G, Y = delta A (lB A) Y → Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
        3 ∣ Nat.card Y →
        (∀ B, IsHyperplane A B → Y ≤ Subgroup.centralizer (B : Set G) → lB A B ≠ ⊥) →
        (∀ Y' ∈ scriptY A, Nat.card Y' < Nat.card Y →
          TransOn A (lB A) (Subgroup.normalizer (A : Set G)) Y') →
        ∀ S ∈ scriptQPiStar A (lB A) Y (piOf 2), ∀ T ∈ scriptQPiStar A (lB A) Y (piOf 2),
          Y ≤ Subgroup.normalizer ((S ⊓ T : Subgroup G) : Set G) →
          (∀ S' ∈ scriptQPiStar A (lB A) Y (piOf 2), ∀ T' ∈ scriptQPiStar A (lB A) Y (piOf 2),
            Nat.card (S ⊓ T : Subgroup G) < Nat.card (S' ⊓ T' : Subgroup G) →
              IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S' T') →
          (∀ a ∈ A, a ≠ 1 → ¬ S ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
            ¬ T ⊓ Subgroup.centralizer {a} ≤ S ⊓ T → Y ≤ Subgroup.centralizer ({a} : Set G)) →
          ∀ a ∈ A, a ≠ 1 → ¬ S ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
            ¬ T ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
            (Subgroup.zpowers a ∈ omegaA A ∨
              delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ≠
                pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
                  pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) →
            (Subgroup.zpowers a ∈ omegaA A → ∀ La ∈ lA A a,
              ¬ Sec8.IsZ3PGLThreePi (lBarA a La A) ∧
                IsLThreePi (↥La ⧸ aschbacherSolvableCore 3 ↥La) ∧
                (¬ ∃ (_ : Fact (Nat.Prime 2)) (e : ℕ), 1 ≤ e ∧
                  Sec4.IsoLThreePi (↥La ⧸ aschbacherSolvableCore 3 ↥La) 2 e) ∧
                ∃ r ∈ xA A, ∃ l ∈ La, ⁅r, l⁆ ∉ inSubgroup (aschbacherSolvableCore 3) La) →
            IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S T

@[expose] noncomputable def Claim1411NonsolvWPointL3FieldOmegaR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
      ∀ Y : Subgroup G, Y = delta A (lB A) Y → Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
        3 ∣ Nat.card Y →
        (∀ B, IsHyperplane A B → Y ≤ Subgroup.centralizer (B : Set G) → lB A B ≠ ⊥) →
        (∀ Y' ∈ scriptY A, Nat.card Y' < Nat.card Y →
          TransOn A (lB A) (Subgroup.normalizer (A : Set G)) Y') →
        ∀ S ∈ scriptQPiStar A (lB A) Y (piOf 2), ∀ T ∈ scriptQPiStar A (lB A) Y (piOf 2),
          Y ≤ Subgroup.normalizer ((S ⊓ T : Subgroup G) : Set G) →
          (∀ S' ∈ scriptQPiStar A (lB A) Y (piOf 2), ∀ T' ∈ scriptQPiStar A (lB A) Y (piOf 2),
            Nat.card (S ⊓ T : Subgroup G) < Nat.card (S' ⊓ T' : Subgroup G) →
              IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S' T') →
          (∀ a ∈ A, a ≠ 1 → ¬ S ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
            ¬ T ⊓ Subgroup.centralizer {a} ≤ S ⊓ T → Y ≤ Subgroup.centralizer ({a} : Set G)) →
          ∀ a ∈ A, a ≠ 1 → ¬ S ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
            ¬ T ⊓ Subgroup.centralizer {a} ≤ S ⊓ T → Subgroup.zpowers a ∈ omegaA A →
            (∀ La ∈ lA A a,
              ¬ Sec8.IsZ3PGLThreePi (lBarA a La A) ∧
                IsLThreePi (↥La ⧸ aschbacherSolvableCore 3 ↥La) ∧
                (¬ ∃ (_ : Fact (Nat.Prime 2)) (e : ℕ), 1 ≤ e ∧
                  Sec4.IsoLThreePi (↥La ⧸ aschbacherSolvableCore 3 ↥La) 2 e) ∧
                ∃ r ∈ xA A, ∃ l ∈ La, ⁅r, l⁆ ∉ inSubgroup (aschbacherSolvableCore 3) La) →
            IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S T

@[expose] noncomputable def Claim1411NonsolvWPointHJConfR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
      ∀ Y : Subgroup G, Y = delta A (lB A) Y → Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
        3 ∣ Nat.card Y →
        (∀ B, IsHyperplane A B → Y ≤ Subgroup.centralizer (B : Set G) → lB A B ≠ ⊥) →
        (∀ Y' ∈ scriptY A, Nat.card Y' < Nat.card Y →
          TransOn A (lB A) (Subgroup.normalizer (A : Set G)) Y') →
        ∀ S ∈ scriptQPiStar A (lB A) Y (piOf 2), ∀ T ∈ scriptQPiStar A (lB A) Y (piOf 2),
          Y ≤ Subgroup.normalizer ((S ⊓ T : Subgroup G) : Set G) →
          (∀ S' ∈ scriptQPiStar A (lB A) Y (piOf 2), ∀ T' ∈ scriptQPiStar A (lB A) Y (piOf 2),
            Nat.card (S ⊓ T : Subgroup G) < Nat.card (S' ⊓ T' : Subgroup G) →
              IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S' T') →
          (∀ a ∈ A, a ≠ 1 → ¬ S ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
            ¬ T ⊓ Subgroup.centralizer {a} ≤ S ⊓ T → Y ≤ Subgroup.centralizer ({a} : Set G)) →
          ∀ a ∈ A, a ≠ 1 → ¬ S ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
            ¬ T ⊓ Subgroup.centralizer {a} ≤ S ⊓ T → Subgroup.zpowers a ∉ omegaA A →
            delta A (lB A) (Subgroup.centralizer ({a} : Set G)) ≠
              pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔
                pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) →
            IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S T

namespace Wales1411W

variable {G : Type} [Group G] [Finite G]

theorem isConjIn_of_l3odd_inner_point
    (h131 : Item131)
    (h142 : Item142AllS14) (hbot : Item145BotS14) (hKL : KL3HessETrans2)
    {A L : Subgroup G} {c : G} (hR : Sec15R G A c L) {a : G}
    (ha : Subgroup.zpowers a ∈ omegaA A) {La : Subgroup G} (hLa : La ∈ lA A a)
    (hPGL : ¬ Sec8.IsZ3PGLThreePi (lBarA a La A)) {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (he : 1 ≤ e) (hiso : Sec4.IsoLThreePi (↥La ⧸ aschbacherSolvableCore 3 ↥La) p e)
    (hcent : ∀ r ∈ xA A, ∀ l ∈ La, ⁅r, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) La)
    {Y : Subgroup G} (hY : Y ∈ scriptY A)
    (hIH : ∀ Y' ∈ scriptY A, Nat.card Y' < Nat.card Y →
      TransOn A (lB A) (Subgroup.normalizer (A : Set G)) Y')
    (hYa : Y ≤ Subgroup.centralizer ({a} : Set G))
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) Y (piOf 2))
    (hT : T ∈ scriptQPiStar A (lB A) Y (piOf 2)) :
    IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S T := by
  by_cases hYST : S ⊔ T = Y
  swap
  · exact isConjIn_of_sup_ne hY hIH hS hT hYST
  have h' : Sec14Std G A a La := Proof1413.sec14Std_at hR.toSec14Std ha hLa
  have hD := h'.toSec13Data
  obtain ⟨haL, h9, hAa, hQ⟩ :=
    Proof1413Res6.l3_point_facts h131 hD ⟨p, e, ‹_›, he, hiso⟩ hPGL
  obtain ⟨hEe, hE9, htr⟩ := Proof1413Res6.hess_of_l3_point hD haL h9 hAa hQ
  have hET := hKL _ p e hp2 he hiso _ hEe hE9 htr
  rw [← Subgroup.inf_subgroupOf_right A La] at hET
  exact isConjIn_of_etrans2_point h142 hbot hR ha hLa hAa hcent hET hY.2 hYa hS hT hYST.symm

end Wales1411W

theorem claim1411NonsolvWPointL3FieldR_of_cases (hΩ : Claim1411NonsolvWPointL3FieldOmegaR)
    (hHJ : Claim1411NonsolvWPointHJConfR) : Claim1411NonsolvWPointL3FieldR := by
  intro G _ _ A c L hR Y hYΔ hY hs h3 hBc hIH S hS T hT hD hbig hres a haA ha1 haS haT hpt hout
  by_cases ha : Subgroup.zpowers a ∈ omegaA A
  · exact hΩ G A c L hR Y hYΔ hY hs h3 hBc hIH S hS T hT hD hbig hres a haA ha1 haS haT ha
      (hout ha)
  · exact hHJ G A c L hR Y hYΔ hY hs h3 hBc hIH S hS T hT hD hbig hres a haA ha1 haS haT ha
      (hpt.resolve_left ha)

open Wales1411W in
theorem claim1411NonsolvWPointL3OddR_of_field
    (h131 : Item131)
    (h142 : Item142AllS14) (hbot : Item145BotS14) (hKL : KL3HessETrans2)
    (h : Claim1411NonsolvWPointL3FieldR) : Claim1411NonsolvWPointL3OddR := by
  intro G _ _ A c L hR Y hYΔ hY hs h3 hBc hIH S hS T hT hD hbig hres a haA ha1 haS haT hpt hout
  have hYa := hres a haA ha1 haS haT
  by_cases hl3 : Subgroup.zpowers a ∈ omegaA A ∧ ∃ La ∈ lA A a,
      IsLThreePi (↥La ⧸ aschbacherSolvableCore 3 ↥La) ∧
        ∀ r ∈ xA A, ∀ l ∈ La, ⁅r, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) La
  · obtain ⟨ha, La, hLa, ⟨p, e, hp, he, hiso⟩, hcent⟩ := hl3
    have hp2 : p ≠ 2 := by
      rintro rfl
      exact (hout ha La hLa).2.2.2.2.2.1 ⟨hp, e, he, hiso⟩
    exact isConjIn_of_l3odd_inner_point h131 h142 hbot hKL hR ha hLa (hout ha La hLa).1 hp2 he
      hiso hcent hY hIH hYa hS hT
  · refine h G A c L hR Y hYΔ hY hs h3 hBc hIH S hS T hT hD hbig hres a haA ha1 haS haT hpt
      fun ha La hLa => ?_
    obtain ⟨hPGL, -, hA7, hM22, hM12, h2, hJ2⟩ := hout ha La hLa
    have h' : Sec14Std G A a La := Proof1413.sec14Std_at hR.toSec14Std ha hLa
    have hL3 : IsLThreePi (↥La ⧸ aschbacherSolvableCore 3 ↥La) := by
      rcases (h'.chosen136.2 a ha La hLa).1 with ⟨⟨φ⟩⟩ | hL3 | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
      · exact (hJ2.false φ).elim
      · exact hL3
      · exact (hA7.false φ).elim
      · exact (hM22.false φ).elim
      · exact (hM12.false φ).elim
    refine ⟨hPGL, hL3, h2, ?_⟩
    by_contra hno
    push Not at hno
    exact hl3 ⟨ha, La, hLa, hL3, hno⟩

open Wales1411W CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 in
theorem item1411_1R_of_field
    (h131 : Item131) (h142 : Item142AllS14) (h146 : Item146S14) (hbot : Item145BotS14)
    (hJ2 : ETrans2 GJ E0) (hKL : KL3HessETrans2) (h : Claim1411NonsolvWPointL3FieldR) :
    Item1411_1R :=
  item1411_1R_of_l3odd h131 h142 h146 hbot hJ2
    (claim1411NonsolvWPointL3OddR_of_field h131 h142 hbot hKL h)

end CFSG.RankThree.PartTwo.Sec14
