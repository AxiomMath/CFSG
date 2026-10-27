module

public import CFSG.RankThree.PartTwo.Sec14.Item1413Res6ProofOuter
import CFSG.RankThree.PartTwo.Sec14.Item1413Res3Proof1419
import CFSG.RankThree.PartTwo.Sec14.Item148PtRes2ProofUpper
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ThetaRankThree
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofLThree

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS
open scoped commutatorElement

namespace Proof1413Res6

variable {G : Type} [Group G] [Finite G]

open Proof1413Res3 in
theorem l3_point_facts
    (h131 : Item131) {A L : Subgroup G} {c : G}
    (hD : Sec13Data G A c L) (hL3 : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    (hnPGL : ¬ Sec8.IsZ3PGLThreePi (lBarA c L A)) :
    c ∉ L ∧ Nat.card (A ⊓ L : Subgroup G) = 9 ∧ A = Subgroup.zpowers c ⊔ (A ⊓ L) ∧
      (Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2) ∨
        Nonempty (Sec4.autIn L A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) := by
  have htype : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)) ∨
      IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) ∨
      Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M12) :=
    Or.inr (Or.inl hL3)
  have hcL : c ∉ L := not_mem_of_type hD (type_four_of_three htype)
  obtain ⟨h9, hAa⟩ := facts_of_type h131 hD hcL hnPGL
  refine ⟨hcL, h9, hAa, ?_⟩
  obtain ⟨⟨hM22p, hM22z⟩, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := sporadicModels131
  rcases cases131 h131 sporadicModels131 slTwoCenter hD with
      ⟨-, -, -, hcase⟩ | ⟨-, -, hcase, -⟩ | ⟨-, hP, -⟩ | ⟨hcL', -⟩
  · rcases hcase with ⟨-, hQ⟩ | ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩
    · exact hQ
    · exact absurd hL3 (not_isLThreePi_of_mulEquiv φ not_isoLThreePi_alternating_seven)
    · exact absurd hL3 (not_isLThreePi_of_mulEquiv φ KFacts.KS14.not_isoLThreePi_M22)
  · rcases hcase with hφ | hφ
    · obtain ⟨φ⟩ := hφ
      obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hM12p hM12z φ
      exact absurd hL3 (not_isLThreePi_of_mulEquiv ψ KFacts.KS14.not_isoLThreePi_M12)
    · obtain ⟨φ⟩ := hφ
      obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hJ2p hJ2z φ
      exact absurd hL3 (not_isLThreePi_of_mulEquiv ψ KFacts.KS14.ks17J2NotList.1)
  · exact absurd hP hnPGL
  · exact absurd hcL' hcL

theorem hess_of_l3_point {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L) (hcL : c ∉ L)
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) (hAa : A = Subgroup.zpowers c ⊔ (A ⊓ L))
    (hQ : Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2) ∨
      Nonempty (Sec4.autIn L A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))) :
    CFSG.Assembly.IsElemAbelian 3
        ((A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) ∧
      Nat.card ((A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))) = 9 ∧
      ∀ y₀ ∈ (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)), y₀ ≠ 1 →
        ∀ y₁ ∈ (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)),
          y₁ ≠ 1 → ∃ w ∈ Subgroup.normalizer
            (((A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) :
              Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
                Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)),
            w * y₀ * w⁻¹ = y₁ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcA : c ∈ A := hD.mem_A
  have hc3 : c ^ 3 = 1 := hD.isElemAbelian.2 c hcA
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hl)
  have hB : CFSG.Assembly.IsElemAbelian 3 (A ⊓ L) :=
    ⟨⟨⟨fun x y => Subtype.ext (hD.commute x.2.1 y.2.1)⟩⟩, fun x hx => hD.isElemAbelian.2 x hx.1⟩
  set θ := aschbacherSolvableCore 3 ↥L with hθ
  set π := QuotientGroup.mk' θ with hπ
  set Ebar := (A.subgroupOf L).map π with hEbar
  have hE9 : Nat.card Ebar = 9 := by rw [hEbar, card_map_mk_subgroupOf hD.isElemAbelian, h9]
  have hEe : CFSG.Assembly.IsElemAbelian 3 Ebar :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 π (A.subgroupOf L)
      (CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_subgroupOf 3 A L
        hD.isElemAbelian)
  have hpt : ∀ z ∈ Ebar, z ≠ 1 → ∃ y ∈ A ⊓ L, y ≠ 1 ∧ ∃ hyL : y ∈ L, π ⟨y, hyL⟩ = z := by
    rintro z ⟨y', hy', rfl⟩ hz1
    refine ⟨y', ⟨Subgroup.mem_subgroupOf.mp hy', y'.2⟩, fun hy1 => hz1 ?_, y'.2, rfl⟩
    have : y' = 1 := Subtype.ext hy1
    rw [this, map_one]
  refine ⟨hEe, hE9, ?_⟩
  intro z₀ hz₀ hz₀1 z₁ hz₁ hz₁1
  obtain ⟨y₀, hy₀, hy₀1, hy₀L, rfl⟩ := hpt z₀ hz₀ hz₀1
  obtain ⟨y₁, hy₁, hy₁1, hy₁L, rfl⟩ := hpt z₁ hz₁ hz₁1
  obtain ⟨w, hwL, hwN, hw⟩ :=
    exists_conj_eq_of_autIn hc3 hcL hLc hAa hB h9 hQ hy₀ hy₁ hy₀1 hy₁1
  refine ⟨π ⟨w, hwL⟩, ?_, ?_⟩
  · have hwN' : (⟨w, hwL⟩ : ↥L) ∈ Subgroup.normalizer
        (((A ⊓ L).subgroupOf L : Subgroup ↥L) : Set ↥L) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_normalizer_iff.mp hwN (x : G)
    have hEq : (A ⊓ L).subgroupOf L = A.subgroupOf L := by
      rw [Subgroup.inf_subgroupOf_right]
    rw [hEq] at hwN'
    exact Subgroup.le_normalizer_map π ⟨_, hwN', rfl⟩
  · rw [← map_mul, ← map_inv, ← map_mul]
    congr 1
    exact Subtype.ext hw

theorem aut_fix_of_mem {A L : Subgroup G} {x : G} (hxA : x ∈ Subgroup.centralizer (A : Set G))
    (hxN : x ∈ Subgroup.normalizer (L : Set G)) :
    ∀ b ∈ (A.subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)),
      Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨x, hxN⟩) b = b := by
  rintro _ ⟨y, hy, rfl⟩
  rw [QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk]
  congr 1
  apply Subtype.ext
  have hyA : (y : G) ∈ A := Subgroup.mem_subgroupOf.mp hy
  have h1 := Subgroup.mem_centralizer_iff.mp hxA (y : G) hyA
  change x * (y : G) * x⁻¹ = y
  rw [← h1, mul_inv_cancel_right]

end Proof1413Res6

open Proof1413Res6 in
theorem not_two_dvd_centralizer_of_gamma_all
    (h131 : Item131)
    (h142All : Item142AllS14) (hbot : Item145BotS14) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Fail1411 A (lB A) →
        ∀ c' : G, Subgroup.zpowers c' ∈ gammaA A (lB A) → ∀ L' ∈ lA A c',
          ¬ 2 ∣ Nat.card ↥(Subgroup.centralizer ({c'} : Set G) ⊓
            Sec4.thetaQuotCentralizer L') := by
  intro G _ _ A c L hR hfail c' hc' L' hL'
  have h' : Sec14Std G A c' L' := Proof1413.sec14Std_at hR.toSec14Std hc'.1 hL'
  have hD := h'.toSec13Data
  have hnotPGL := item1412NotPGLR_of h131 h142All hbot G A c L hR hfail c' hc' L' hL'
  obtain ⟨hcL, h9⟩ : c' ∉ L' ∧ Nat.card (A ⊓ L' : Subgroup G) = 9 := by
    rcases cases131 h131 sporadicModels131 slTwoCenter hD with
        ⟨hcL, h9, -⟩ | ⟨hcL, h9, -⟩ | ⟨-, hPGL, -⟩ | ⟨hcL', -⟩
    · exact ⟨hcL, h9⟩
    · exact ⟨hcL, h9⟩
    · exact (hnotPGL hPGL).elim
    · exact (Sec13.not_mem_of_center_eq_bot hD
        (Item148PtRes2.center_eq_bot_of_sec14 sporadicModels131 h') hcL').elim
  exact not_two_dvd_centralizer_of_gamma' sporadicModels131 h142All hbot hR hfail hc' hL'
    (Item148PtRes2.eq_zpowers_sup_of_card hD hcL h9)

end CFSG.RankThree.PartTwo.Sec14
