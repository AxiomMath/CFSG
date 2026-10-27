module

import CFSG.RankThree.PartTwo.Sec16.Item16Tail13Tools
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec14.Concl142NHJInner
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
public import CFSG.RankThree.PartTwo.Sec13.Item13Models
public import CFSG.RankThree.PartTwo.Sec16.Item169GeneralDefs

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof1613

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec16.Proof169 CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU projImage)

variable {G : Type} [Group G] [Finite G]

theorem ctx169_of_point {A L : Subgroup G} {c : G} (h : Ctx169 G A c L) {b : G}
    (hb : Subgroup.zpowers b ∈ omegaA A) {K : Subgroup G} (hK : K ∈ lA A b) :
    Ctx169 G A b K :=
  { h with zpowers_mem_omegaA := hb, mem_lA := hK }

theorem three_dvd_card_L {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) :
    3 ∣ Nat.card L := by
  rcases (h.chosen136.2 c h.zpowers_mem_omegaA L h.mem_lA).1 with ⟨⟨φ⟩⟩ |
      ⟨p, e, hp, he, hiso⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact three_dvd_card_of_thetaQuot φ (by rw [KFacts.KS14.card_nativeJ2]; norm_num)
  · have h1 := Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 ↥L)
    exact (Sec19.Step1914TriProof.three_dvd_card_of_isoLThreePi he hiso).trans h1
  · exact three_dvd_card_of_thetaQuot φ
      (by rw [KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]; norm_num)
  · exact three_dvd_card_of_thetaQuot φ (by rw [KFacts.KS14.card_nativeM22]; norm_num)
  · exact three_dvd_card_of_thetaQuot φ (by rw [KFacts.KS14.card_nativeM12]; norm_num)

theorem centralizer_le_normalizer_L {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) :
    Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
  centralizer_le_normalizer_of_three_dvd h (three_dvd_card_L h)

theorem not_odd_of_le {T X : Subgroup G} (hTX : T ≤ X) (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥) :
    ¬ Odd (Nat.card X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hodd
  obtain ⟨k, hk⟩ := hT2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hT1
    rw [pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq T hk
  have h2 : 2 ∣ Nat.card X :=
    (dvd_pow_self 2 hk0).trans (hk ▸ Subgroup.card_dvd_of_le hTX)
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

theorem thetaCen_le_pPrimeCoreOf (b : G) :
    thetaCen ({b} : Set G) ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) := by
  obtain ⟨-, -, hc3, -⟩ := solvable_prime_complement_core_characterization
    (H := ↥(Subgroup.centralizer ({b} : Set G))) Nat.prime_three
  refine le_pPrimeCoreOf (Subgroup.map_subtype_le _) (centralizer_le_normalizer_thetaCen _) ?_
  rw [thetaCen, inSubgroup, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hc3

theorem nonempty_l34_of_even (h1612 : Step1612) {A M : Subgroup G} {a : G}
    (h : Ctx169 G A a M)
    (hev : ¬ Odd (Nat.card (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))))) :
    Nonempty (lBarA a M A ≃* Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2)) := by
  rcases h1612 G A a M h with ⟨hsimp, hT⟩ | h2
  · exfalso
    set X := pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) with hX
    have hXC : X ≤ Subgroup.centralizer (M : Set G) :=
      pPrimeCoreOf_le_centralizer_of_isSimpleGroup h.mem_thetaComponentsAt hsimp
        (three_dvd_card_L h.toSec14Std)
    have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
      h.A_le_centralizer.trans (le_normalizer_pPrimeCoreOf 3 _)
    have hX3 : Nat.Coprime 3 (Nat.card X) := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact coprime_card_pPrimeCoreOf 3 _
    have h2X : 2 ∣ Nat.card X := by
      rcases Nat.even_or_odd (Nat.card X) with he | ho
      · exact even_iff_two_dvd.mp he
      · exact absurd ho hev
    obtain ⟨P, hAP, hP1⟩ :=
      CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial
        3 2 Nat.prime_three Nat.prime_two A X (isPGroup_three_of_isElemAbelian h.isElemAbelian)
        hAX hX3 h2X
    exact hP1 (hT _ ⟨(Subgroup.map_subtype_le _).trans hXC,
      (isPiSubgroup_piOf_iff Nat.prime_two _).mpr (P.isPGroup'.map _), hAP⟩)
  · exact h2

theorem facts_l34 {A M : Subgroup G} {a : G} (h : Ctx169 G A a M)
    (φ : lBarA a M A ≃* Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2)) :
    a ∉ M ∧ Nat.card (A ⊓ M : Subgroup G) = 9 ∧
      Nonempty (lBarA a M A ≃* Multiplicative (ZMod 3) × Sec12.lBar a M) ∧
      Nonempty (↥M ⧸ aschbacherSolvableCore 3 ↥M ≃* projSL 3 (GaloisField 2 2)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hS, hZ⟩ := isPerfect_center_projSL 2 2 (by norm_num) (by norm_num)
  exact facts_of_prod h.toSec13Data hS hZ φ

theorem nonempty_quot_l34_of_even (h1612 : Step1612) (hBr : Step169TwoBridge)
    {A M : Subgroup G} {a : G} (h : Ctx169 G A a M)
    (hev : ¬ Odd (Nat.card (pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))))) :
    letI := kerAO2_normal h.toSec13Data.le_normalizer
    Nonempty (↥(A ⊔ M) ⧸ kerAO2 A M ≃*
      Multiplicative (ZMod 3) × projSL 3 (GaloisField 2 2)) := by
  obtain ⟨φ⟩ := nonempty_l34_of_even h1612 h hev
  obtain ⟨-, -, hprod, hL⟩ := facts_l34 h φ
  exact hBr G A a M h.toSec15R hL hprod

theorem false_of_trans_even (h1612 : Step1612) (h1510 : Item1510R) (hBr : Step169TwoBridge)
    {A L : Subgroup G} {c : G} (h : Ctx169 G A c L)
    (hev : ¬ Odd (Nat.card (pPrimeCoreOf 3 (Subgroup.centralizer ({c} : Set G)))))
    (htr : ∀ F ∈ omegaA A, ∃ w ∈ Subgroup.normalizer (A : Set G),
      F = (Subgroup.zpowers c).map (MulAut.conj w).toMonoidHom) : False := by
  obtain ⟨c', L', hL', hc', hempty⟩ := h1510 G A c L h.toSec15R
  obtain ⟨w, -, hw⟩ := htr _ hc'
  have hw' : Subgroup.zpowers c' = Subgroup.zpowers (w * c * w⁻¹) := by
    rw [hw, MonoidHom.map_zpowers]
    rfl
  have hev' : ¬ Odd (Nat.card (pPrimeCoreOf 3 (Subgroup.centralizer ({c'} : Set G)))) := by
    rwa [card_pPrimeCoreOf_centralizer_eq hw']
  have hM : Ctx169 G A c' L' := ctx169_of_point h hc' hL'
  exact hempty.false (nonempty_quot_l34_of_even h1612 hBr hM hev').some

theorem card_z3_prod {S : Type*} [Group S] :
    Nat.card (Multiplicative (ZMod 3) × S) = 3 * Nat.card S := by
  rw [Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

end CFSG.RankThree.PartTwo.Sec16.Proof1613

