module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20o
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
import CFSG.Alternating.Multipliers.OddKernel
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15RankAlt
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreCoverUni
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15ACoreMatUni
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15KFactsLie
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup CFSG.RankThree.PerfectCover
open CFSG.Blueprint (LieModel)
open CFSG.Assembly.LowTwoRank (StatedLieTag)

theorem uc22p20r_rankWit_of_le_pRank {K : Type} [Group K] [Finite K] {p k : ℕ} (hp : p.Prime)
    (hk : k ≤ CFSG.Open.pRank p (⊤ : Subgroup K)) : uc22p20oRankWit K p k := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, -, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup K)
  obtain ⟨F, hF⟩ := Sylow.exists_subgroup_card_pow_prime (G := E) p (n := k)
    (by rw [hcard]; exact pow_dvd_pow p hk)
  refine ⟨F.map E.subtype, CFSG.Open.IsElemAbelian.mono hE (Subgroup.map_subtype_le F), ?_⟩
  rw [Subgroup.card_map_of_injective E.subtype_injective, hF]

theorem uc22p20r_ker_comp {K X : Type} [Group K] [Group X] (e : K ⧸ center K ≃* X) :
    (e.toMonoidHom.comp (QuotientGroup.mk' (center K))).ker = center K := by
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']

theorem uc22p20r_a9 : uc22p20oA9Witness := by
  intro K _ _ hq hodd ⟨e⟩
  haveI : Group.IsPerfect K := Group.isPerfect_def.mpr hq.1
  set η : K →* alternatingGroup (Fin (7 + 2)) := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hηs : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : η.ker = center K := uc22p20r_ker_comp e
  have hodd' : Odd (Nat.card η.ker) := by rw [hker]; exact hodd
  have h1 := CFSG.Alternating.Multipliers.card_ker_eq_one_of_odd (m := 7) (by norm_num) η hηs
    hker.le hodd'
  refine ⟨?_, ?_⟩
  · rw [hker] at h1
    exact Subgroup.card_eq_one.mp h1
  · have h3 := CFSG.LocalAnalysis.RankThreeUC.S15.lieOddRankAlt_holds K hq 9 (by norm_num) ⟨e⟩ 3
      Nat.prime_three (by norm_num)
    exact uc22p20r_rankWit_of_le_pRank Nat.prime_three (by rw [h3]; norm_num)

@[expose] def uc22p20rNativeGriess : Prop :=
  ∀ (X : Type) [Group X] (t : StatedLieTag) (n p f : ℕ), CFSG.Blueprint.LieModel X t n p f →
    commutator X = ⊤ ∧
      Nonempty (griessHopfMultiplier X ≃*
        CFSG.Blueprint.Multiplier.generic t n p f × CFSG.Blueprint.Multiplier.exceptional t n p f)

theorem uc22p20r_card_center_dvd_hopf {K X : Type} [Group K] [Group X] [Group.IsPerfect K]
    (e : K ⧸ center K ≃* X) : Nat.card (center K) ∣ Nat.card (hopfMultiplier X) := by
  set q : K →* X := e.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hqs : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = center K := uc22p20r_ker_comp e
  rw [← hker, ← map_hopfMultiplier_hopfLift q hqs hker.le]
  exact Subgroup.card_map_dvd (H := hopfMultiplier X) (hopfLift q hqs hker.le)

theorem uc22p20r_genericOrders_eq {t : StatedLieTag} {m n : ℕ} (h : uc22p20oNoOddMult t m n) :
    CFSG.Blueprint.Multiplier.genericOrders t m 2 n = (1, 1) := by
  have hn : 1 ≤ n := by
    rcases h with ⟨h, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> omega
  have hev : Even (2 ^ n) := Nat.even_pow.2 ⟨even_two, by omega⟩
  have hsub : Odd (2 ^ n - 1) := Nat.Even.sub_odd Nat.one_le_two_pow hev odd_one
  have hadd : Odd (2 ^ n + 1) := hev.add_one
  have h4 : Odd ((2 ^ n) ^ 4 + 1) := (Nat.even_pow.2 ⟨hev, by norm_num⟩).add_one
  have g2 : ∀ x : ℕ, Odd x → Nat.gcd 2 x = 1 := fun x hx => Nat.coprime_two_left.2 hx
  have g4 : ∀ x : ℕ, Odd x → Nat.gcd 4 x = 1 := fun x hx =>
    (Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hx) : Nat.Coprime (2 ^ 2) x)
  rcases h with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
  · rcases h with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ | rfl | rfl | rfl | rfl | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
    · change (Nat.gcd 2 (2 ^ n - 1), 1) = (1, 1)
      rw [g2 _ hsub]
    · change (Nat.gcd 4 (2 ^ n - 1), 1) = (1, 1)
      rw [g4 _ hsub]
    · change (Nat.gcd 4 (2 ^ n + 1), 1) = (1, 1)
      rw [g4 _ hadd]
    all_goals first
      | rfl
      | (change (Nat.gcd 2 (2 ^ n - 1), 1) = (1, 1); rw [g2 _ hsub])
      | (change (Nat.gcd 4 ((2 ^ n) ^ 4 + 1), 1) = (1, 1); rw [g4 _ h4])
  · rcases h with ⟨rfl, rfl⟩ | rfl | ⟨rfl, rfl⟩
    · change (Nat.gcd 4 (2 ^ n + 1), 1) = (1, 1)
      rw [g4 _ hadd]
    · rfl
    · change (Nat.gcd 4 ((2 ^ n) ^ 4 + 1), 1) = (1, 1)
      rw [g4 _ h4]
  · obtain rfl := h
    rfl

theorem uc22p20r_card_table {t : StatedLieTag} {m n : ℕ} (h : uc22p20oNoOddMult t m n) :
    ∃ k : ℕ, Nat.card (CFSG.Blueprint.Multiplier.generic t m 2 n ×
      CFSG.Blueprint.Multiplier.exceptional t m 2 n) = 2 ^ k := by
  have hcard : Nat.card (CFSG.Blueprint.Multiplier.generic t m 2 n ×
      CFSG.Blueprint.Multiplier.exceptional t m 2 n) =
      (CFSG.Blueprint.Multiplier.genericOrders t m 2 n).1 *
        (CFSG.Blueprint.Multiplier.genericOrders t m 2 n).2 *
        ((CFSG.Blueprint.Multiplier.exceptionalOrders t m 2 n).1 *
          (CFSG.Blueprint.Multiplier.exceptionalOrders t m 2 n).2) := by
    unfold CFSG.Blueprint.Multiplier.generic CFSG.Blueprint.Multiplier.exceptional
    simp only [Nat.card_prod, Nat.card_congr (Multiplicative.toAdd : _ ≃ _), Nat.card_zmod]
  obtain ⟨k, hk⟩ := CFSG.LocalAnalysis.RankThreeUC.S15.ksm_exc_two t m n
  refine ⟨k, ?_⟩
  rw [hcard, uc22p20r_genericOrders_eq h, hk]
  ring

theorem uc22p20r_center_of_native (hN : uc22p20rNativeGriess) : uc22p20oTrivialCenter := by
  intro K _ _ hq hodd t m n hNo hM
  haveI : Group.IsPerfect K := Group.isPerfect_def.mpr hq.1
  obtain ⟨-, ⟨eM⟩⟩ := hN (K ⧸ center K) t m 2 n hM
  obtain ⟨k, hk⟩ := uc22p20r_card_table hNo
  have hM' : Nat.card (hopfMultiplier (K ⧸ center K)) = 2 ^ k := by
    rw [← hk, ← Nat.card_congr (hopfMultiplierEquivGriess (K ⧸ center K)).toEquiv]
    exact Nat.card_congr eM.toEquiv
  have hdvd := uc22p20r_card_center_dvd_hopf (MulEquiv.refl (K ⧸ center K))
  rw [hM'] at hdvd
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hj0 : j = 0 := by
    rcases Nat.eq_zero_or_pos j with h0 | hpos
    · exact h0
    · exfalso
      rw [hj] at hodd
      exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, hpos.ne'⟩)
  rw [hj0, pow_zero] at hj
  exact Subgroup.card_eq_one.mp hj

theorem uc22p20r_u38_of_griess (hG : CFSG.Open.GriessAllModelsStatement) : uc22p20oU38Witness := by
  intro K _ _ hq hodd hU
  haveI : Group.IsPerfect K := Group.isPerfect_def.mpr hq.1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcl : StatedClassicalModel (K ⧸ center K) .PSU (2 + 1) 2 3 :=
    CFSG.Blueprint.LieModel.statedClassicalModel hU (by decide)
  obtain ⟨hadm, F, instF, instFin, hcardF, ⟨φ⟩⟩ := hcl
  haveI : Fintype F := Fintype.ofFinite F
  have hS₀ : Group.IsPerfect (StatedSU (2 + 1) (2 ^ 3) F) := by
    obtain ⟨-, -, -, hnq⟩ := hadm
    exact CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hcardF (n := 2 + 1) (by omega) hnq
  obtain ⟨k, hM⟩ := CFSG.LocalAnalysis.RankThreeUC.S15.ACore.card_hopfMultiplier_psu_char_two hG
    (l := 2) (f := 3) rfl hcardF hadm
  set ρ : K →* StatedProj (StatedSU (2 + 1) (2 ^ 3) F) :=
    φ.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hρs : Function.Surjective ρ := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hρk : ρ.ker = center K := uc22p20r_ker_comp φ
  obtain ⟨Z₀, hZn, j, hZD, hZK, hrank⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.S15.ACore.coverId_of_two_index hS₀ inferInstance
      ((StatedScalars (Fin (2 + 1)) F).subgroupOf (StatedSU (2 + 1) (2 ^ 3) F))
      (CFSG.Open.StatedAPI.statedScalars_subgroupOf_le_center _) ρ hρs hρk hM
  have hD : Nat.card ((StatedScalars (Fin (2 + 1)) F).subgroupOf (StatedSU (2 + 1) (2 ^ 3) F)) = 3 := by
    rw [(CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hcardF (by omega)).2.2]
    norm_num
  refine ⟨?_, ?_⟩
  · rw [hD] at hZK
    have hj : j = 0 := by
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · exact h0
      · exfalso
        rw [hZK] at hodd
        exact (Nat.not_even_iff_odd.2 hodd) ((Nat.even_pow.2 ⟨even_two, hpos.ne'⟩).mul_right _)
    have hZ₀ : Nat.card Z₀ ∣ 3 := by
      have h := Subgroup.card_dvd_of_le hZD
      rwa [hD] at h
    rw [hZK, hj, pow_zero, one_mul]
    exact Nat.div_dvd_of_dvd hZ₀
  · have hmat := CFSG.LocalAnalysis.RankThreeUC.S15.uniCoreMatrix F (2 ^ 3) (2 + 1) 3 Nat.prime_three
      (by norm_num) (by rw [Fintype.card_eq_nat_card, hcardF]) (by norm_num) (by norm_num) (by norm_num)
      (fun _ => by norm_num) Z₀ hZD
    have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup K) = 2 := by
      rw [hrank 3 Nat.prime_three (by norm_num), hmat]
      norm_num
    exact uc22p20r_rankWit_of_le_pRank Nat.prime_three h2.ge

theorem uc22p20r_global22f_of_tables (hG : CFSG.Open.GriessAllModelsStatement)
    (hN : uc22p20rNativeGriess) (hexcl : uc22p20oExclWitness) (htwo : uc22p20oTwoWitness) :
    Global22f :=
  ⟨hexcl, htwo, uc22p20r_u38_of_griess hG, uc22p20r_center_of_native hN, uc22p20r_a9⟩

section Certificates


theorem uc22p20r_nativeGriess : uc22p20rNativeGriess :=
  fun X _ t n p f h => CFSG.Milestones.cl_lit_griess_schur_multipliers_all_native_models X t n p f h

theorem uc22p20r_center : uc22p20oTrivialCenter :=
  uc22p20r_center_of_native uc22p20r_nativeGriess

theorem uc22p20r_u38 : uc22p20oU38Witness :=
  uc22p20r_u38_of_griess CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement

theorem uc22p20r_global22f_of (hexcl : uc22p20oExclWitness) (htwo : uc22p20oTwoWitness) : Global22f :=
  ⟨hexcl, htwo, uc22p20r_u38, uc22p20r_center, uc22p20r_a9⟩

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.UC22
