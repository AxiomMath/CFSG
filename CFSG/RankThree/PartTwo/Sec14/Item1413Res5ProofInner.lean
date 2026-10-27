module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res5ProofNonsolv
import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypesA7
import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypesM12
import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypesM22
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Toolkit.M12LocalGroups

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open scoped commutatorElement

@[expose] noncomputable def Claim1411NonsolvXPointL3R : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Fail1411 A (lB A) →
      (∀ a : G, Subgroup.zpowers a ∈ omegaA A →
          TransOn A (lB A) (xA A) (Subgroup.centralizer ({a} : Set G))) →
      ∀ Y : Subgroup G, Y = delta A (lB A) Y → Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
        3 ∣ Nat.card Y →
        (∀ B, IsHyperplane A B → Y ≤ Subgroup.centralizer (B : Set G) → lB A B ≠ ⊥) →
        (∀ Y' ∈ scriptY A, Nat.card Y' < Nat.card Y → TransOn A (lB A) (xA A) Y') →
        ∀ S ∈ scriptQPiStar A (lB A) Y (piOf 2), ∀ T ∈ scriptQPiStar A (lB A) Y (piOf 2),
          Y ≤ Subgroup.normalizer ((S ⊓ T : Subgroup G) : Set G) →
          (∀ S' ∈ scriptQPiStar A (lB A) Y (piOf 2), ∀ T' ∈ scriptQPiStar A (lB A) Y (piOf 2),
            Nat.card (S ⊓ T : Subgroup G) < Nat.card (S' ⊓ T' : Subgroup G) →
              IsConjIn (xA A ⊓ Y) S' T') →
          (∀ a ∈ A, a ≠ 1 → ¬ S ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
            ¬ T ⊓ Subgroup.centralizer {a} ≤ S ⊓ T → Y ≤ Subgroup.centralizer ({a} : Set G)) →
          ∀ a ∈ A, a ≠ 1 → ¬ S ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
            ¬ T ⊓ Subgroup.centralizer {a} ≤ S ⊓ T → Subgroup.zpowers a ∈ omegaA A →
            ∀ La ∈ lA A a, IsLThreePi (↥La ⧸ aschbacherSolvableCore 3 ↥La) →
              ¬ Sec8.IsZ3PGLThreePi (lBarA a La A) →
              (∃ r ∈ xA A, ∃ l ∈ La, ⁅r, l⁆ ∉ inSubgroup (aschbacherSolvableCore 3) La) →
              IsConjIn (xA A ⊓ Y) S T

namespace Proof1413Res5

variable {G : Type} [Group G] [Finite G]

open Res5TypesA7 Res5Types in
theorem cent_of_a7
    (h131 : Item131) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L)
    (φ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) :
    ∀ r ∈ xA A, ∀ l ∈ L, ⁅r, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hspor := Sec13.sporadicModels131
  obtain ⟨-, h9, -⟩ := point_facts_of_inner h131 hspor h.toSec13Data
    (center_eq_bot_of_mulEquiv φ isPerfect_center_alt7.2)
    (not_isLThreePi_of_mulEquiv φ not_isoLThreePi_alternating_seven)
  have hcard : Nat.card ↥(alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hfac : (Nat.card ↥(alternatingGroup (Fin 7))).factorization 3 = 2 := by
    rw [hcard]
    exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 2520 = 3 ^ 2 * 280 by norm_num) (by norm_num)
  obtain ⟨φ', hφ'E⟩ := exists_equiv_map_eq φ card_P7 (Res5Gen.card_image_inf h h9) hfac
  exact cent_of_rigid h φ' hφ'E fun τ hτ n hn hτn => aut_eq_one_A7 hτ hn hτn

open CFSG.GH74.M12.Hyp (G12) in
open CFSG.RankThree.PartTwo.Toolkit.M12 CFSG.RankThree.PartTwo.Sec4.Sporadic.M12Sig Res5GenM12
  Res5TypesM12 Res5Types in
theorem cent_of_m12
    (h131 : Item131) {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (φ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12) :
    ∀ r ∈ xA A, ∀ l ∈ L, ⁅r, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  have hspor := Sec13.sporadicModels131
  obtain ⟨-, h9, hAc⟩ := point_facts_of_inner h131 hspor h.toSec13Data
    (center_eq_bot_of_mulEquiv φ hspor.2.1.2)
    (not_isLThreePi_of_mulEquiv φ KFacts.KS14.not_isoLThreePi_M12)
  obtain ⟨g, hg⟩ := exists_conj_mem_A h hAc h9 (autIn_perm_three_of_M12 h131 h φ) φ
  obtain ⟨φ', hφ'E⟩ := exists_equiv_map_eq_of_conj φ hg
    (by rw [basisA.card, Res5Gen.card_image_inf h h9])
  exact cent_of_rigid h φ' hφ'E fun τ hτ n hn hτn => aut_eq_one_M12 hτ hn hτn

open Res5Gen Res5Types Res5TypesM22 KFacts.KP4 in
theorem cent_of_m22
    (h131 : Item131) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L)
    (φ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22) :
    ∀ r ∈ xA A, ∀ l ∈ L, ⁅r, l⁆ ∈ inSubgroup (aschbacherSolvableCore 3) L := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hspor := Sec13.sporadicModels131
  have hD := h.toSec13Data
  obtain ⟨-, h9, -⟩ := point_facts_of_inner h131 hspor hD
    (center_eq_bot_of_mulEquiv φ hspor.1.2)
    (not_isLThreePi_of_mulEquiv φ KFacts.KS14.not_isoLThreePi_M22)
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set Eb := ((A ⊓ L).subgroupOf L).map (QuotientGroup.mk' θ) with hEb
  have hE9 : Nat.card Eb = 9 := card_image_inf h h9
  have hfac : (Nat.card G22).factorization 3 = 2 := by
    rw [KFacts.KS14.card_nativeM22]
    exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 443520 = 3 ^ 2 * 49280 by norm_num) (by norm_num)
  obtain ⟨g, hg⟩ := exists_conj_mem_of_card card_P0 (E' := Eb.map φ.toMonoidHom)
    (by rw [Subgroup.card_map_of_injective φ.injective, hE9]) hfac
  set φ' : (↥L ⧸ θ) ≃* G22 := φ.trans (MulAut.conj g)⁻¹ with hφ'
  have hφ'apply : ∀ x, φ' x = g⁻¹ * φ x * g := fun x => rfl
  have hφ'E : Eb.map φ'.toMonoidHom = P0 := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨e, he, rfl⟩
      obtain ⟨p, hp, hpe⟩ := hg (φ e) ⟨e, he, rfl⟩
      change φ' e ∈ P0
      rw [hφ'apply, ← hpe]
      simpa [mul_assoc] using hp
    · rw [card_P0, Subgroup.card_map_of_injective φ'.injective, hE9]
  exact cent_of_rigid h φ' hφ'E fun τ hτ n hn hτn => aut_eq_one_G22 hτ hn hτn

end Proof1413Res5

open Proof1413Res5 in
theorem claim1411NonsolvXPointFR_of_l3
    (h131 : Item131) (h : Claim1411NonsolvXPointL3R) :
    Claim1411NonsolvXPointFR := by
  intro G _ _ A c L hR hfail hloc Y hYΔ hY hs h3 hBc hIH S hS T hT hD hbig hres a haA ha1 haS
    haT ha La hLa hJ hPGL hout
  have h' : Sec14Std G A a La := Proof1413.sec14Std_at hR.toSec14Std ha hLa
  obtain ⟨r, hr, l, hl, hrl⟩ := hout
  rcases (h'.chosen136.2 a ha La hLa).1 with ⟨⟨φ⟩⟩ | hL3 | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact (hJ.false φ).elim
  · exact h G A c L hR hfail hloc Y hYΔ hY hs h3 hBc hIH S hS T hT hD hbig hres a haA ha1 haS haT
      ha La hLa hL3 hPGL ⟨r, hr, l, hl, hrl⟩
  · exact (hrl (cent_of_a7 h131 h' φ r hr l hl)).elim
  · exact (hrl (cent_of_m22 h131 h' φ r hr l hl)).elim
  · exact (hrl (cent_of_m12 h131 h' φ r hr l hl)).elim

end CFSG.RankThree.PartTwo.Sec14
