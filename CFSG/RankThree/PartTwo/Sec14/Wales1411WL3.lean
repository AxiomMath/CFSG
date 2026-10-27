module

public import CFSG.RankThree.PartTwo.Sec14.Wales1411WSpor
import CFSG.RankThree.PartTwo.Sec14.Item1413Res7ProofXPt

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open scoped commutatorElement

@[expose] noncomputable def Claim1411NonsolvWPointJL3OddR : Prop :=
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
                (Subgroup.zpowers a ∈ gammaA A (lB A) ∨
                  ∃ r ∈ xA A, ∃ l ∈ La, ⁅r, l⁆ ∉ inSubgroup (aschbacherSolvableCore 3) La) ∧
                IsEmpty (↥La ⧸ aschbacherSolvableCore 3 ↥La ≃* ↥(alternatingGroup (Fin 7))) ∧
                IsEmpty (↥La ⧸ aschbacherSolvableCore 3 ↥La ≃*
                  CFSG.Blueprint.NativeSporadic.M22) ∧
                IsEmpty (↥La ⧸ aschbacherSolvableCore 3 ↥La ≃*
                  CFSG.Blueprint.NativeSporadic.M12) ∧
                ¬ ∃ (_ : Fact (Nat.Prime 2)) (e : ℕ), 1 ≤ e ∧
                  Sec4.IsoLThreePi (↥La ⧸ aschbacherSolvableCore 3 ↥La) 2 e) →
            IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S T

namespace Wales1411W

variable {G : Type} [Group G] [Finite G]

theorem isConjIn_of_l3_two_point
    (h131 : Item131) (h142All : Item142AllS14)
    (hbot : Item145BotS14) {A L : Subgroup G} {c : G} (hR : Sec15R G A c L) {a : G}
    (ha : Subgroup.zpowers a ∈ omegaA A) {La : Subgroup G} (hLa : La ∈ lA A a)
    (hPGL : ¬ Sec8.IsZ3PGLThreePi (lBarA a La A)) [Fact (Nat.Prime 2)] {e : ℕ} (he : 1 ≤ e)
    (hiso : Sec4.IsoLThreePi (↥La ⧸ aschbacherSolvableCore 3 ↥La) 2 e)
    {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hYa : Y ≤ Subgroup.centralizer ({a} : Set G)) {S T : Subgroup G}
    (hS : S ∈ scriptQPiStar A (lB A) Y (piOf 2)) (hT : T ∈ scriptQPiStar A (lB A) Y (piOf 2)) :
    IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S T := by
  have h' : Sec14Std G A a La := Proof1413.sec14Std_at hR.toSec14Std ha hLa
  have hD := h'.toSec13Data
  have hXW : xA A ≤ Subgroup.normalizer (A : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨haL, h9, hAa, hQ⟩ :=
    Proof1413Res6.l3_point_facts h131 hD ⟨2, e, ‹_›, he, hiso⟩ hPGL
  obtain ⟨hEe, hE9, htr⟩ := Proof1413Res6.hess_of_l3_point hD haL h9 hAa hQ
  have hL2 : ∀ V : Subgroup G, IsPGroup 2 V → V ≤ La →
      A ≤ Subgroup.normalizer (V : Set G) → V ≤ inSubgroup (aschbacherSolvableCore 3) La :=
    fun V hV2 hVL hAV => Proof1413Res7.le_theta_of_two he hiso hEe hE9 htr hV2 hVL hAV
  obtain ⟨hZq, -⟩ := Proof1413Res7.theta_sup_xA_mem_scriptQ h142All h'
  have hZYq : (inSubgroup (aschbacherSolvableCore 3) La ⊔ xA A) ⊓ Y ∈ scriptQ A (lB A) :=
    mem_scriptQ_of_le hZq inf_le_left (le_normalizer_inf hZq.1.2.2 hAY)
  have hle : ∀ U ∈ scriptQPiStar A (lB A) Y (piOf 2),
      U ≤ (inSubgroup (aschbacherSolvableCore 3) La ⊔ xA A) ⊓ Y := fun U hU =>
    le_inf (Proof1413Res7.le_theta_sup_xA h142All hbot h' hAa hL2
      (isPGroup_of_mem_scriptQPi Nat.prime_two hU.prop) (hU.prop.1.2.trans hYa)
      hU.prop.1.1.1.2.2) hU.prop.1.2
  exact (Proof1413Res5.isConjIn_of_le_mem_scriptQ h'.isE27 (hbot G A a La h') hZYq inf_le_right
    hS hT (hle S hS) (hle T hT)).mono (inf_le_inf_right Y hXW)

end Wales1411W

open Wales1411W in
theorem claim1411NonsolvWPointJL3R_of_odd
    (h131 : Item131)
    (h142All : Item142AllS14) (hbot : Item145BotS14) (h : Claim1411NonsolvWPointJL3OddR) :
    Claim1411NonsolvWPointJL3R := by
  intro G _ _ A c L hR Y hYΔ hY hs h3 hBc hIH S hS T hT hD hbig hres a haA ha1 haS haT hpt hout
  have hYa := hres a haA ha1 haS haT
  by_cases htwo : Subgroup.zpowers a ∈ omegaA A ∧ ∃ La ∈ lA A a,
      ∃ (_ : Fact (Nat.Prime 2)) (e : ℕ), 1 ≤ e ∧
        Sec4.IsoLThreePi (↥La ⧸ aschbacherSolvableCore 3 ↥La) 2 e
  · obtain ⟨ha, La, hLa, hp, e, he, hiso⟩ := htwo
    exact isConjIn_of_l3_two_point h131 h142All hbot hR ha hLa (hout ha La hLa).1 he hiso hY.2
      hYa hS hT
  · refine h G A c L hR Y hYΔ hY hs h3 hBc hIH S hS T hT hD hbig hres a haA ha1 haS haT hpt
      fun ha La hLa => ⟨(hout ha La hLa).1, (hout ha La hLa).2.1, (hout ha La hLa).2.2.1,
        (hout ha La hLa).2.2.2.1, (hout ha La hLa).2.2.2.2,
        fun h2 => htwo ⟨ha, La, hLa, h2⟩⟩

theorem item1411_1R_of_odd
    (h131 : Item131) (h142 : Item142AllS14) (h146 : Item146S14) (hbot : Item145BotS14)
    (h : Claim1411NonsolvWPointJL3OddR) : Item1411_1R :=
  item1411_1R_of_jl3 h131 h142 h146 hbot (claim1411NonsolvWPointJL3R_of_odd h131 h142 hbot h)

end CFSG.RankThree.PartTwo.Sec14
