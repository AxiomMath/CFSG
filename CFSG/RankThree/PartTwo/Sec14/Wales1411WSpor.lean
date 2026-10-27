module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res5ProofInner
public import CFSG.RankThree.PartTwo.Sec14.Wales1411WDefs
import CFSG.RankThree.PartTwo.Sec14.Wales1411WPoint
import CFSG.RankThree.PartTwo.Sec14.Wales1411WModels
import CFSG.RankThree.PartTwo.Sec14.Wales1411W
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open scoped commutatorElement

@[expose] noncomputable def Claim1411NonsolvWPointJL3R : Prop :=
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
                  CFSG.Blueprint.NativeSporadic.M12)) →
            IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S T

namespace Wales1411W

variable {G : Type} [Group G] [Finite G]

open Proof1413Res5 in
theorem isConjIn_of_etrans_point
    (h142 : Item142AllS14) (hbot : Item145BotS14)
    {A L : Subgroup G} {c : G} (hR : Sec15R G A c L) {a : G}
    (ha : Subgroup.zpowers a ∈ omegaA A) {La : Subgroup G} (hLa : La ∈ lA A a)
    (hAa : A = Subgroup.zpowers a ⊔ (A ⊓ La))
    (hcent : ∀ r ∈ xA A, ∀ l ∈ La, ⁅r, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) La)
    (hET : ETrans (↥La ⧸ aschbacherSolvableCore 3 ↥La)
      (((A ⊓ La).subgroupOf La).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥La))))
    {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hYa : Y ≤ Subgroup.centralizer ({a} : Set G)) (hYΔ : Y = delta A (lB A) Y)
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) Y (piOf 2))
    (hT : T ∈ scriptQPiStar A (lB A) Y (piOf 2)) :
    IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S T := by
  have h' : Sec14Std G A a La := Proof1413.sec14Std_at hR.toSec14Std ha hLa
  have hD := h'.toSec13Data
  have := ker142_normal (LB := lB A) hD.isElemAbelian.1 hD.mem_A
  have hXW : xA A ≤ Subgroup.normalizer (A : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _)
  set H := Subgroup.normalizer (Subgroup.zpowers a : Set G) with hH
  obtain ⟨Q₀, hQ₀⟩ := maxInvariantPiSubgroups_nonempty H A (piCompl 3)
  obtain ⟨hQ₀q, hQ₀b⟩ := h142 G A a La h' Q₀ hQ₀
  rcases hQ₀b with ⟨-, hQK, -, -⟩ | ⟨hK, -⟩
  ·
    have hKq : k142 A (lB A) a ∈ scriptQ A (lB A) := by
      rw [← hQK]
      exact hQ₀q.1
    have hCH : Subgroup.centralizer ({a} : Set G) ≤ H :=
      centralizer_singleton_le_normalizer_zpowers a
    have hSY : S ≤ Y := hS.prop.1.2
    have hTY : T ≤ Y := hT.prop.1.2
    have hZY : k142 A (lB A) a ⊓ Y ∈ scriptQ A (lB A) :=
      mem_scriptQ_of_le hKq inf_le_left (le_normalizer_inf hKq.1.2.2 hAY)
    exact (isConjIn_of_le_mem_scriptQ h'.isE27 (hbot G A a La h') hZY inf_le_right hS hT
      (le_inf (le_delta hS.prop.1.1 ((hSY.trans hYa).trans hCH)) hSY)
      (le_inf (le_delta hT.prop.1.1 ((hTY.trans hYa).trans hCH)) hTY)).mono
      (inf_le_inf_right Y hXW)
  · have d : Res5Types.Inner142 A a La := ⟨h', hAa, hK, hcent⟩
    exact d.isConjIn_of_etrans (h142 G A a La h') (hbot G A a La h') hET hAY hYa hYΔ hS hT

open Proof1413Res5 Res5TypesA7 Res5Types in
theorem isConjIn_of_a7_point
    (h131 : Item131) (h142 : Item142AllS14)
    (hbot : Item145BotS14) {A L : Subgroup G} {c : G} (hR : Sec15R G A c L) {a : G}
    (ha : Subgroup.zpowers a ∈ omegaA A) {La : Subgroup G} (hLa : La ∈ lA A a)
    (φ : ↥La ⧸ aschbacherSolvableCore 3 ↥La ≃* ↥(alternatingGroup (Fin 7)))
    {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hYa : Y ≤ Subgroup.centralizer ({a} : Set G)) (hYΔ : Y = delta A (lB A) Y)
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) Y (piOf 2))
    (hT : T ∈ scriptQPiStar A (lB A) Y (piOf 2)) :
    IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S T := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h' : Sec14Std G A a La := Proof1413.sec14Std_at hR.toSec14Std ha hLa
  have hspor := Sec13.sporadicModels131
  obtain ⟨-, h9, hAa⟩ := point_facts_of_inner h131 hspor h'.toSec13Data
    (center_eq_bot_of_mulEquiv φ isPerfect_center_alt7.2)
    (not_isLThreePi_of_mulEquiv φ not_isoLThreePi_alternating_seven)
  have hcard : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hfac : (Nat.card ↥(alternatingGroup (Fin 7))).factorization 3 = 2 := by
    rw [hcard]
    exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 2520 = 3 ^ 2 * 280 by norm_num) (by norm_num)
  obtain ⟨φ', hφ'E⟩ := exists_equiv_map_eq φ card_P7 (Res5Gen.card_image_inf h' h9) hfac
  exact isConjIn_of_etrans_point h142 hbot hR ha hLa hAa (cent_of_a7 h131 h' φ)
    (ETrans.of_mulEquiv φ' hφ'E etrans_A7) hAY hYa hYΔ hS hT

open Proof1413Res5 Res5Gen Res5Types Res5TypesM22 KFacts.KP4 in
theorem isConjIn_of_m22_point
    (h131 : Item131) (h142 : Item142AllS14)
    (hbot : Item145BotS14) {A L : Subgroup G} {c : G} (hR : Sec15R G A c L) {a : G}
    (ha : Subgroup.zpowers a ∈ omegaA A) {La : Subgroup G} (hLa : La ∈ lA A a)
    (φ : ↥La ⧸ aschbacherSolvableCore 3 ↥La ≃* CFSG.Blueprint.NativeSporadic.M22)
    {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hYa : Y ≤ Subgroup.centralizer ({a} : Set G)) (hYΔ : Y = delta A (lB A) Y)
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) Y (piOf 2))
    (hT : T ∈ scriptQPiStar A (lB A) Y (piOf 2)) :
    IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S T := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h' : Sec14Std G A a La := Proof1413.sec14Std_at hR.toSec14Std ha hLa
  have hspor := Sec13.sporadicModels131
  obtain ⟨-, h9, hAa⟩ := point_facts_of_inner h131 hspor h'.toSec13Data
    (center_eq_bot_of_mulEquiv φ hspor.1.2)
    (not_isLThreePi_of_mulEquiv φ KFacts.KS14.not_isoLThreePi_M22)
  set θ := aschbacherSolvableCore 3 ↥La with hθ
  set Eb := ((A ⊓ La).subgroupOf La).map (QuotientGroup.mk' θ) with hEb
  have hE9 : Nat.card Eb = 9 := card_image_inf h' h9
  have hfac : (Nat.card G22).factorization 3 = 2 := by
    rw [KFacts.KS14.card_nativeM22]
    exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 443520 = 3 ^ 2 * 49280 by norm_num) (by norm_num)
  obtain ⟨φ', hφ'E⟩ := exists_equiv_map_eq (Γ := G22) φ card_P0 hE9 hfac
  exact isConjIn_of_etrans_point h142 hbot hR ha hLa hAa (cent_of_m22 h131 h' φ)
    (ETrans.of_mulEquiv φ' hφ'E etrans_M22) hAY hYa hYΔ hS hT

open CFSG.GH74.M12.Hyp (G12) in
open Proof1413Res5 CFSG.RankThree.PartTwo.Toolkit.M12 Res5GenM12 Res5TypesM12 Res5Types in
theorem isConjIn_of_m12_point
    (h131 : Item131)
    (h142 : Item142AllS14) (hbot : Item145BotS14) {A L : Subgroup G} {c : G}
    (hR : Sec15R G A c L) {a : G} (ha : Subgroup.zpowers a ∈ omegaA A) {La : Subgroup G}
    (hLa : La ∈ lA A a)
    (φ : ↥La ⧸ aschbacherSolvableCore 3 ↥La ≃* CFSG.Blueprint.NativeSporadic.M12)
    {Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hYa : Y ≤ Subgroup.centralizer ({a} : Set G)) (hYΔ : Y = delta A (lB A) Y)
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A (lB A) Y (piOf 2))
    (hT : T ∈ scriptQPiStar A (lB A) Y (piOf 2)) :
    IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S T := by
  have h' : Sec14Std G A a La := Proof1413.sec14Std_at hR.toSec14Std ha hLa
  have hspor := Sec13.sporadicModels131
  obtain ⟨-, h9, hAa⟩ := point_facts_of_inner h131 hspor h'.toSec13Data
    (center_eq_bot_of_mulEquiv φ hspor.2.1.2)
    (not_isLThreePi_of_mulEquiv φ KFacts.KS14.not_isoLThreePi_M12)
  obtain ⟨g, hg⟩ := exists_conj_mem_A h' hAa h9 (autIn_perm_three_of_M12 h131 h' φ) φ
  obtain ⟨φ', hφ'E⟩ := exists_equiv_map_eq_of_conj φ hg
    (by rw [basisA.card, Res5Gen.card_image_inf h' h9])
  exact isConjIn_of_etrans_point h142 hbot hR ha hLa hAa (cent_of_m12 h131 h' φ)
    (ETrans.of_mulEquiv φ' hφ'E etrans_M12) hAY hYa hYΔ hS hT

end Wales1411W

open Wales1411W in
theorem claim1411NonsolvWPointOutR_of_jl3
    (h131 : Item131) (h142 : Item142AllS14) (hbot : Item145BotS14)
    (h : Claim1411NonsolvWPointJL3R) : Claim1411NonsolvWPointOutR := by
  intro G _ _ A c L hR Y hYΔ hY hs h3 hBc hIH S hS T hT hD hbig hres a haA ha1 haS haT hpt hout
  have hYa := hres a haA ha1 haS haT
  by_cases hspor : Subgroup.zpowers a ∈ omegaA A ∧ ∃ La ∈ lA A a,
      Nonempty (↥La ⧸ aschbacherSolvableCore 3 ↥La ≃* ↥(alternatingGroup (Fin 7))) ∨
        Nonempty (↥La ⧸ aschbacherSolvableCore 3 ↥La ≃* CFSG.Blueprint.NativeSporadic.M22) ∨
          Nonempty (↥La ⧸ aschbacherSolvableCore 3 ↥La ≃* CFSG.Blueprint.NativeSporadic.M12)
  · obtain ⟨ha, La, hLa, ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ := hspor
    · exact isConjIn_of_a7_point h131 h142 hbot hR ha hLa φ hY.2 hYa hYΔ hS hT
    · exact isConjIn_of_m22_point h131 h142 hbot hR ha hLa φ hY.2 hYa hYΔ hS hT
    · exact isConjIn_of_m12_point h131 h142 hbot hR ha hLa φ hY.2 hYa hYΔ hS hT
  · refine h G A c L hR Y hYΔ hY hs h3 hBc hIH S hS T hT hD hbig hres a haA ha1 haS haT hpt
      fun ha La hLa => ⟨(hout ha La hLa).1, (hout ha La hLa).2,
        ⟨fun φ => hspor ⟨ha, La, hLa, Or.inl ⟨φ⟩⟩⟩,
        ⟨fun φ => hspor ⟨ha, La, hLa, Or.inr (Or.inl ⟨φ⟩)⟩⟩,
        ⟨fun φ => hspor ⟨ha, La, hLa, Or.inr (Or.inr ⟨φ⟩)⟩⟩⟩

theorem claim1411NonsolvWR_of_jl3
    (h131 : Item131) (h142 : Item142AllS14) (h146 : Item146S14) (hbot : Item145BotS14)
    (h : Claim1411NonsolvWPointJL3R) : Claim1411NonsolvWR :=
  claim1411NonsolvWR_of_out h131 h142 h146 hbot (claim1411NonsolvWPointOutR_of_jl3 h131 h142 hbot h)

theorem item1411_1R_of_jl3
    (h131 : Item131) (h142 : Item142AllS14) (h146 : Item146S14) (hbot : Item145BotS14)
    (h : Claim1411NonsolvWPointJL3R) : Item1411_1R :=
  item1411_1R_of_W h146 hbot (claim1411NonsolvWR_of_jl3 h131 h142 h146 hbot h)

end CFSG.RankThree.PartTwo.Sec14
