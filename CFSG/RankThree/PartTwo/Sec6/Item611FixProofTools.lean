module

public import CFSG.RankThree.PartTwo.Sec6.Item611FixProof
public import CFSG.RankThree.PartTwo.Sec6.Item611FixProofE81Cover
public import CFSG.RankThree.PartTwo.Sec6.Item611Res3ProofTools
import CFSG.RankThree.PartTwo.Sec6.Item612Local
import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.RankThree.Coprime.ThompsonElementaryComplement
import CFSG.RankThree.PartOne.S11c.CentralWitness
import CFSG.RankThree.PartOne.CTP.SeitzToral
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantSylow
public import Certificates.Certificate8007
public import Certificates.Certificate8008

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (projSL projSU)

open Res611Res3

namespace Res611Fix

variable {G : Type} [Group G] [Finite G]

theorem exists_elemAbelian_le_of_quot {L : Subgroup G}
    {P : Subgroup (L ⧸ aschbacherSolvableCore 3 L)} (hP : CFSG.Assembly.IsElemAbelian 3 P) :
    ∃ B : Subgroup G, B ≤ L ∧ CFSG.Assembly.IsElemAbelian 3 B ∧ Nat.card B = Nat.card P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hπ
  have hker3 : ¬ 3 ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    exact (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).2.2.1
  have hP3 : IsPGroup 3 P := Sec5.isPGroup_of_isElemAbelian hP
  obtain ⟨E', hE'map, hE'dis⟩ := CFSG.RankThree.PartOne.CTP.SeitzToral.exists_lift_of_coprime_ker
    π (QuotientGroup.mk'_surjective _) hker3 P hP3
  have hinf : E' ⊓ π.ker = ⊥ := disjoint_iff.mp hE'dis
  have hinj : Function.Injective (π.comp E'.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hmem : (x : L) ∈ E' ⊓ π.ker := ⟨x.2, hx⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hcardE : Nat.card E' = Nat.card P := by
    rw [← hE'map, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, MonoidHom.range_comp,
      Subgroup.range_subtype]
  have hmemP : ∀ x ∈ E', π x ∈ P := fun x hx => hE'map ▸ ⟨x, hx, rfl⟩
  have hone : ∀ x ∈ E', π x = 1 → x = 1 := fun x hx h1 => by
    have hmem : x ∈ E' ⊓ π.ker := ⟨hx, h1⟩
    rwa [hinf, Subgroup.mem_bot] at hmem
  have hE'e : CFSG.Assembly.IsElemAbelian 3 E' := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · have hab : (a : L) * b * (a : L)⁻¹ * (b : L)⁻¹ = 1 := by
        refine hone _ (E'.mul_mem (E'.mul_mem (E'.mul_mem a.2 b.2) (E'.inv_mem a.2))
          (E'.inv_mem b.2)) ?_
        have hc := congrArg Subtype.val (hP.1.is_comm.comm ⟨π a, hmemP a a.2⟩ ⟨π b, hmemP b b.2⟩)
        simp only [Subgroup.coe_mul] at hc
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
        group
      calc ((a * b : E') : L) = (a : L) * b * (a : L)⁻¹ * (b : L)⁻¹ * (b * a) := by
            rw [Subgroup.coe_mul]; group
        _ = ((b * a : E') : L) := by rw [hab, one_mul, Subgroup.coe_mul]
    · exact hone _ (E'.pow_mem hx 3) (by rw [map_pow]; exact hP.2 _ (hmemP x hx))
  refine ⟨E'.map L.subtype, Subgroup.map_subtype_le _,
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 L.subtype E' hE'e, ?_⟩
  rw [Subgroup.card_map_of_injective L.subtype_injective, hcardE]

end Res611Fix

section Certs


theorem Res611Fix.exists_elemAbelian_le (h45 : Sec4.Item4_5) (h41 : Sec4.Item4_1LargePrime)
    (h413 : Sec4.Item4_13_forwardFix) {G : Type} [Group G] [Finite G] (hst : PartTwoStanding G)
    {A : Subgroup G} (hA : A ∈ partTwoS G) (hrank : 4 < CFSG.Open.pRank 3 A) {c : G}
    (hcA : c ∈ A) (hc1 : c ≠ 1) {L : Subgroup G} (hL : L ∈ lZeroStarAt A c)
    (hCA : A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c) :
    ∃ B : Subgroup G, B ≤ L ∧ CFSG.Assembly.IsElemAbelian 3 B ∧ 81 ≤ Nat.card B := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hA.1.1
  obtain ⟨m, hm5, hAcard⟩ := exists_card_eq_of_four_lt_pRank hAe hrank
  have h243 : 243 ≤ Nat.card A := by
    rw [hAcard]
    calc 243 = 3 ^ 5 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm5
  rcases Res611Fix.cases413 h45 h41 h413 hst hA hrank hcA hc1 hL hCA with
    ⟨e, -, m', hm', ⟨φ⟩, -⟩ | ⟨hAL, -⟩ | ⟨hdec, hcL, -⟩ | ⟨-, -, hZ3, hM, -⟩
  ·
    have h1 := le_pRank_projSL_two (n := 3 * m') (by omega)
    rw [← CFSG.RankThree.Coprime.pRank_eq_of_mulEquiv φ 3,
      (CFSG.RankThree.theta_quotient_core_and_ranks (G := ↥L)).2.2.1.1] at h1
    obtain ⟨B', hB', hB'card⟩ :=
      CFSG.RankThree.PartOne.exists_isElementaryAbelian_card_pRank (p := 3) (by norm_num) (H := ↥L)
    have hB'e : CFSG.Assembly.IsElemAbelian 3 B' :=
      ⟨hB'.toIsMulCommutative, fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx⟩
    refine ⟨B'.map L.subtype, Subgroup.map_subtype_le _,
      CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 L.subtype B' hB'e, ?_⟩
    rw [Subgroup.card_map_of_injective L.subtype_injective, hB'card]
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ CFSG.pRank 3 ↥L := Nat.pow_le_pow_right (by norm_num) (by omega)
  ·
    exact ⟨A, hAL, hAe, by omega⟩
  ·
    have hle := card_le_three_mul_card_inf hAe hcA hc1 hdec
    exact ⟨A ⊓ L, inf_le_right, isElemAbelian_of_le hAe inf_le_left, by omega⟩
  ·
    obtain ⟨P, hP, hP81⟩ := ks611G2CoverE81_holds _ hZ3 hM
    obtain ⟨B, hBL, hB, hBcard⟩ := Res611Fix.exists_elemAbelian_le_of_quot hP
    exact ⟨B, hBL, hB, by omega⟩

theorem Res611Fix.inf_thetaQuotCentralizer_eq_bot (h45 : Sec4.Item4_5)
    (h41 : Sec4.Item4_1LargePrime) (h413 : Sec4.Item4_13_forwardFix) {G : Type} [Group G]
    [Finite G] (hst : PartTwoStanding G) {A : Subgroup G} (hA : A ∈ partTwoS G)
    (hrank : 4 < CFSG.Open.pRank 3 A) {c : G} (hcA : c ∈ A) (hc1 : c ≠ 1) {L : Subgroup G}
    (hL : L ∈ lZeroStarAt A c) (hCA : A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c)
    {T : Subgroup G} (hT : CFSG.Assembly.IsElemAbelian 2 T) :
    T ⊓ thetaQuotCentralizer L = ⊥ := by
  obtain ⟨B, hBL, hB, h81⟩ :=
    Res611Fix.exists_elemAbelian_le h45 h41 h413 hst hA hrank hcA hc1 hL hCA
  exact inf_thetaQuotCentralizer_eq_bot_of_le hst.evenRank_eq hB hBL h81 hT

end Certs

end CFSG.RankThree.PartTwo.Sec6
