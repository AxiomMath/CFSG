module

public import CFSG.RankThree.PartTwo.Sec14.Item1413ProofTools
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec14.Item1413ProofDefs
public import CFSG.Sporadic.J2
public import CFSG.Sporadic.Mathieu.M12

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

namespace Proof1413

variable {G : Type} [Group G] [Finite G]

theorem case3_of_m22
    (h133 : Item133) {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L) (hST : HypS A ∨ HypT A)
    (φ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.M22)
    (hW : ¬ Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G)) :
    Sec21.IsIrreducibleOn (Sec4.autIn (L ⊓ Subgroup.normalizer (A : Set G)) (A ⊓ L)) ∧
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ∧
      CFSG.Assembly.IsElemAbelian 3 (oThreeWStar A) ∧ Nat.card (oThreeWStar A) = 9 ∧
      wStar A = oThreeWStar A ⊔
        Sec4.autIn (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A ∧
      omegaA A = orbitIn (Subgroup.normalizer (A : Set G)) (Subgroup.zpowers c) ∧
      (omegaA A).ncard = 9 ∧
      Nonempty (lBarA c L A ≃* Multiplicative (ZMod 3) × Sec12.lBar c L) ∧
      (IsLThreePi (L ⧸ aschbacherSolvableCore 3 L) ∨
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7)) ∨
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M22)) := by
  have hM12 : Nat.card CFSG.Blueprint.NativeSporadic.M22 ≠
      Nat.card CFSG.Blueprint.NativeSporadic.M12 := by
    rw [KFacts.KS14.card_nativeM22, KFacts.KS14.card_nativeM12]
    norm_num
  have hJ2 : Nat.card CFSG.Blueprint.NativeSporadic.M22 ≠
      Nat.card CFSG.Blueprint.NativeSporadic.J2 := by
    rw [KFacts.KS14.card_nativeM22, KFacts.KS14.card_nativeJ2]
    norm_num
  have hM12p : Group.IsPerfect CFSG.Blueprint.NativeSporadic.M12 :=
    (Sec13.isPerfect_center_of_isSimpleGroup CFSG.Sporadic.Mathieu.fam_m12_simplicity.2.2
      (by rw [KFacts.KS14.card_nativeM12]; norm_num)).1
  have hJ2p : Group.IsPerfect CFSG.Blueprint.NativeSporadic.J2 :=
    (Sec13.isPerfect_center_of_isSimpleGroup CFSG.Sporadic.J2.isSimpleGroup_J2
      (by rw [KFacts.KS14.card_nativeJ2]; norm_num)).1
  rcases h133 G A c L hD hST with h1 | ⟨-, hA7, -⟩ | h3 | hPGL | hM | hJ
  · exact absurd h1 hW
  ·
    obtain ⟨ψ⟩ := hA7
    obtain ⟨χ⟩ := Sec13.nonempty_thetaQuot_equiv hD Sec13.isPerfect_center_alt7.1 ψ
    exact (KFacts.KS14.isEmpty_mulEquiv_M22_alternating.2.1.false (φ.symm.trans χ)).elim
  · exact h3
  ·
    exact absurd (Sec13.facts_of_isZ3PGLThreePi hD hPGL).1
      (not_isLThreePi_of_mulEquiv φ KFacts.KS14.not_isoLThreePi_M22)
  ·
    obtain ⟨ψ⟩ := hM
    obtain ⟨χ⟩ := Sec13.nonempty_thetaQuot_equiv hD hM12p ψ
    exact ((isEmpty_mulEquiv_of_card_ne hM12).false (φ.symm.trans χ)).elim
  ·
    obtain ⟨ψ⟩ := hJ
    obtain ⟨χ⟩ := Sec13.nonempty_thetaQuot_equiv hD hJ2p ψ
    exact ((isEmpty_mulEquiv_of_card_ne hJ2).false (φ.symm.trans χ)).elim

end Proof1413

theorem step1421M22R_of
    (h133 : Item133) (hNW : Step1422NotWHR) : Step1421M22R := by
  intro G _ _ A c L hR hfail a ha La hLa hM
  have hS : Sec14Std G A a La := Proof1413.sec14Std_at hR.toSec14Std ha.1 hLa
  obtain ⟨φ⟩ := hM
  have h3 := Proof1413.case3_of_m22 h133 hS.toSec13Data hS.hypS_or_hypT φ
    (hNW G A c L hR hfail a ha La hLa ⟨φ⟩)
  rw [h3.2.2.2.2.2.1]

end CFSG.RankThree.PartTwo.Sec14
