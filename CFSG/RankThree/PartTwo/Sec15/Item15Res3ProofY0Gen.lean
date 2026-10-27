module

public import CFSG.RankThree.PartTwo.Sec15.Item158Res2Proof159Y0
public import CFSG.RankThree.PartTwo.Sec15.Item1517StepsProofY0
public import CFSG.RankThree.PartTwo.KFacts.KP4
import CFSG.RankThree.PartTwo.Sec15.Item1515ResProofLA7
import CFSG.RankThree.PartTwo.Sec15.HypS
import CFSG.RankThree.PartTwo.Sec13.Item133
public import CFSG.RankThree.PartTwo.Sec15.Item1513ProofTools
public import CFSG.RankThree.PartTwo.Sec15.Item1514Steps1515S17
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsQuot
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsS17
public import CFSG.RankThree.PartTwo.Sec15.Item158Res2Proof159
public import CFSG.RankThree.PartTwo.Sec17.Item175Proof
public import CFSG.RankThree.PartTwo.Sec17.Item17ParaHJ

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

namespace Proof15Res3Y0Gen

variable {X : Type} [Group X]

theorem m22_sSup_invariant_eq_top
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.M22))
    {B : Subgroup X} (hB : Nat.card B = 9) :
    sSup (invariantPiSubgroups ⊤ B (piCompl 3)) = ⊤ := by
  have : Finite X := KFacts.KP4.finite_of_nonempty hX
  set F := invariantPiSubgroups (⊤ : Subgroup X) B (piCompl 3) with hF
  obtain ⟨a, b, -, -, -, hne, hpair⟩ := KFacts.KP4.m22_maxInvariant_eq_pair hX hB
  set R₀ := inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set X)) ⊔
    inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set X)) with hR₀
  set R₁ := inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a * b} : Set X)) ⊔
    inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a * b ^ 2} : Set X)) with hR₁
  have hR₀m : R₀ ∈ maxInvariantPiSubgroups ⊤ B (piCompl 3) := by
    rw [hpair]
    exact Set.mem_insert _ _
  have hR₁m : R₁ ∈ maxInvariantPiSubgroups ⊤ B (piCompl 3) := by
    rw [hpair]
    exact Set.mem_insert_of_mem _ rfl
  have hR₀J : R₀ ≤ sSup F := le_sSup hR₀m.prop
  have hR₁J : R₁ ≤ sSup F := le_sSup hR₁m.prop
  rcases KFacts.KP4.m22_sSup_cases hX hB F subset_rfl with h2 | ⟨-, ⟨φ⟩⟩ | htop
  ·
    exfalso
    have hJ : sSup F ∈ F := by
      refine ⟨le_top, ?_, le_normalizer_sSup fun Q hQ => hQ.2.2⟩
      rw [isPiSubgroup_piCompl_iff Nat.prime_three]
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h2
      rw [hn]
      intro h3
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
    have h0 : R₀ = sSup F := hR₀m.eq_of_le hJ hR₀J
    have h1 : R₁ = sSup F := hR₁m.eq_of_le hJ hR₁J
    exact hne (h0.trans h1.symm)
  ·
    exfalso
    obtain ⟨-, h16, -⟩ := KFacts.KP4.m22_maxInvariant_structure hX hB hR₀m
    have hdvd : Nat.card R₀ ∣ Nat.card (sSup F : Subgroup X) := Subgroup.card_dvd_of_le hR₀J
    rw [h16, Nat.card_congr φ.toEquiv, card_alternatingGroup_seven] at hdvd
    norm_num at hdvd
  · exact htop

end Proof15Res3Y0Gen

open Proof15Res3Y0Gen

theorem step159Y0Gen_of
    (h138 : Item138N) (hgen : KS1517Gen) : Step159Y0Gen := by
  intro G _ _ A c L ctx hO h7
  have h := ctx.toSec15R
  have hD := h.toSec13Data
  have hcL : c ∉ L := h.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  have h9 : Nat.card (A ⊓ L : Subgroup G) = 9 := ctx.card_inf
  have hAeq : A = Subgroup.zpowers c ⊔ (A ⊓ L) := eq_sup_of_card_nine hD h9 fun hc => hcL hc.2
  obtain ⟨hAbE, hAb9⟩ := Proof1515Res.isElemAbelian_card_aBar_of h h9
  refine Proof1515Res.le_sSup_of_gen_of h hAeq ?_
  rcases ctx.types with ⟨p, e, hp, he, hiso⟩ | ⟨⟨φ⟩⟩ | hM
  ·
    have hperf : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
      (Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt).1
    have hmod9 := not_modNine_of_inner h h138 KFacts.kSL3PiOrder3TypeC he hiso ctx.prod
    have hnot44 : ¬ Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rintro (⟨-, hψ⟩ | ⟨h2, -⟩)
      · exact ctx.not_three ⟨hψ, hO⟩
      · norm_num at h2
    exact hgen _ p e he hiso hperf hmod9 hnot44 _ hAbE hAb9
  · exact (h7.false φ).elim
  · exact m22_sSup_invariant_eq_top hM hAb9

end CFSG.RankThree.PartTwo.Sec15
