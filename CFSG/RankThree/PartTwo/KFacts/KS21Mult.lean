module

public import CFSG.RankThree.PartTwo.Sec21.Item226Gaps
public import CFSG.RankThree.PartTwo.Sec21.Item229Gaps
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs
public import CFSG.RankThree.PerfectCover.HopfFormula
import CFSG.Models.Transport
import CFSG.Models.PGL
public import CFSG.RankThree.Native.DerivedGenerators

public section


attribute [-instance] CFSG.RankThree.Native.fact_prime_five
namespace CFSG.RankThree.PartTwo.KFacts.KS21Mult

open CFSG CFSG.Assembly.LowTwoRank CFSG.Models Matrix
open CFSG.Assembly.RankThreeEven (projImage projSL projSU projSp projOmegaMinus)
open CFSG.Adapters.RankTwoModelTransports (statedProjEquivMapMk)

export CFSG.Adapters.RankTwoModelTransports (statedProjEquivProjImage)

theorem lieModel_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) {t : StatedLieTag}
    {n p f : ℕ} (h : LieModel Y t n p f) : LieModel X t n p f :=
  CFSG.Models.LieModel.of_mulEquiv e.symm h

theorem lieModel_projSL {n p e : ℕ} [Fact p.Prime] (h : StatedLieAdmissible .PSL n p e) :
    LieModel (projSL n (GaloisField p e)) .PSL n p e :=
  CFSG.PGLModel.lieModel_projSL h

theorem lieModel_projSU {n p e : ℕ} [Fact p.Prime] (h : StatedLieAdmissible .PSU n p e) :
    LieModel (projSU n p e) .PSU n p e :=
  CFSG.PGLModel.lieModel_projSU h

theorem lieModel_projSp {n p e : ℕ} [Fact p.Prime] (h : StatedLieAdmissible .PSp n p e) :
    LieModel (projSp n (GaloisField p e)) .PSp n p e :=
  CFSG.PGLModel.lieModel_projSp h

theorem lieModel_projOmegaMinus {n p e : ℕ} [Fact p.Prime]
    (h : StatedLieAdmissible .POmegaMinus n p e) {b c : GaloisField p e}
    (hbc : ∀ s : GaloisField p e, s ^ 2 + b * s + c ≠ 0) :
    LieModel (projOmegaMinus (n - 1) (GaloisField p e) b c) .POmegaMinus n p e :=
  CFSG.PGLModel.lieModel_projOmegaMinus h hbc

theorem card_center_dvd_griess {S Q : Type} [Group S] [Group Q] (hQ : Group.IsPerfect Q)
    (e : Q ⧸ Subgroup.center Q ≃* S) :
    Nat.card (Subgroup.center Q) ∣ Nat.card (CFSG.Open.griessHopfMultiplier S) := by
  have := hQ
  let q : Q →* S := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = Subgroup.center Q := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (Subgroup.center Q) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hmap := RankThree.PerfectCover.map_hopfMultiplier_hopfLift q hq hker.le
  rw [Nat.card_congr (RankThree.PerfectCover.hopfMultiplierEquivGriess S).toEquiv, ← hker,
    ← hmap]
  exact Subgroup.card_map_dvd (H := RankThree.PerfectCover.hopfMultiplier S)
    (RankThree.PerfectCover.hopfLift q hq hker.le)

theorem card_table_eq_one {t : StatedLieTag} {n p f : ℕ}
    (hg : Blueprint.Multiplier.genericOrders t n p f = (1, 1))
    (he : Blueprint.Multiplier.exceptionalOrders t n p f = (1, 1)) :
    Nat.card (Blueprint.Multiplier.generic t n p f ×
      Blueprint.Multiplier.exceptional t n p f) = 1 := by
  unfold Blueprint.Multiplier.generic Blueprint.Multiplier.exceptional
  rw [hg, he]
  simp

theorem center_eq_bot_of_table (hGA : ComponentClassification.TBLit.GriessMultipliersAllModels)
    {X : Type} [Group X] (hX : Group.IsPerfect X) {t : StatedLieTag} {n p f : ℕ}
    (hm : LieModel (X ⧸ Subgroup.center X) t n p f)
    (hg : Blueprint.Multiplier.genericOrders t n p f = (1, 1))
    (he : Blueprint.Multiplier.exceptionalOrders t n p f = (1, 1)) :
    Subgroup.center X = ⊥ := by
  obtain ⟨eM⟩ := (hGA _ t n p f hm).2
  have hdvd := card_center_dvd_griess hX (MulEquiv.refl (X ⧸ Subgroup.center X))
  rw [Nat.card_congr eM.toEquiv, card_table_eq_one hg he, Nat.dvd_one] at hdvd
  exact Subgroup.eq_bot_of_card_eq _ hdvd

theorem not_five_dvd_two_pow_add_one {n : ℕ} (hn : Odd n) : ¬ 5 ∣ 2 ^ n + 1 := by
  intro h
  have h' : ((2 ^ n + 1 : ℕ) : ZMod 5) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  push_cast at h'
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ, pow_mul, show (2 : ZMod 5) ^ 2 = -1 by decide] at h'
  rcases neg_one_pow_eq_or (ZMod 5) k with h1 | h1 <;> rw [h1] at h' <;> revert h' <;> decide

theorem not_three_dvd_two_pow_add_one {m : ℕ} (hm : Even m) : ¬ 3 ∣ 2 ^ m + 1 := by
  intro h
  have h' : ((2 ^ m + 1 : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
  push_cast at h'
  obtain ⟨k, rfl⟩ := hm
  rw [← two_mul, pow_mul, show (2 : ZMod 3) ^ 2 = 1 by decide, one_pow] at h'
  revert h'
  decide

theorem exceptionalOrders_PSU_five (n : ℕ) :
    Blueprint.Multiplier.exceptionalOrders .PSU 5 2 n = (1, 1) := by
  unfold Blueprint.Multiplier.exceptionalOrders
  split <;> simp_all

theorem exceptionalOrders_PSL_four {m : ℕ} (hm1 : m ≠ 1) :
    Blueprint.Multiplier.exceptionalOrders .PSL 4 2 m = (1, 1) := by
  unfold Blueprint.Multiplier.exceptionalOrders
  split <;> simp_all

theorem exceptionalOrders_PSp_three {m : ℕ} (hm1 : m ≠ 1) :
    Blueprint.Multiplier.exceptionalOrders .PSp 3 2 m = (1, 1) := by
  unfold Blueprint.Multiplier.exceptionalOrders
  split <;> simp_all

theorem exceptionalOrders_POmegaMinus_four (m : ℕ) :
    Blueprint.Multiplier.exceptionalOrders .POmegaMinus 4 2 m = (1, 1) := by
  unfold Blueprint.Multiplier.exceptionalOrders
  split <;> simp_all

theorem exceptionalOrders_PSU_six {m : ℕ} (hm1 : m ≠ 1) :
    Blueprint.Multiplier.exceptionalOrders .PSU 6 2 m = (1, 1) := by
  unfold Blueprint.Multiplier.exceptionalOrders
  split <;> simp_all

theorem odd_two_pow_sub_one {m : ℕ} (hm : 0 < m) : Odd (2 ^ m - 1) := by
  have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  obtain ⟨k, hk⟩ : Even (2 ^ m) := Nat.even_pow.mpr ⟨even_two, hm.ne'⟩
  exact ⟨k - 1, by omega⟩

theorem centralExtensionTrivial226_of_griess
    (hGA : ComponentClassification.TBLit.GriessMultipliersAllModels) :
    Sec21.CentralExtensionTrivial226 := by
  intro X _ _ hX n hn hodd ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hadm : StatedLieAdmissible .PSU 5 2 n := by
    refine ⟨Nat.prime_two, by omega, ?_⟩
    change 3 ≤ 5 ∧ (5, 2 ^ n) ≠ (3, 2)
    exact ⟨by norm_num, by simp⟩
  refine center_eq_bot_of_table hGA hX (lieModel_of_mulEquiv e (lieModel_projSU hadm)) ?_ ?_
  · change (Nat.gcd 5 (2 ^ n + 1), 1) = (1, 1)
    rw [show Nat.gcd 5 (2 ^ n + 1) = 1 from
      (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr (not_five_dvd_two_pow_add_one hodd)]
  · exact exceptionalOrders_PSU_five n

theorem centralExtensionTrivial229_of_griess
    (hGA : ComponentClassification.TBLit.GriessMultipliersAllModels) :
    Sec21.CentralExtensionTrivial229 := by
  intro X _ _ hX m hm hme hcases
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm1 : m ≠ 1 := by
    rintro rfl
    exact Nat.not_even_one hme
  have hq : Odd (2 ^ m - 1) := odd_two_pow_sub_one hm
  rcases hcases with he | he | ⟨b, c, hbc, he⟩ | he
  · obtain ⟨e⟩ := he
    have hadm : StatedLieAdmissible .PSL 4 2 m := by
      refine ⟨Nat.prime_two, hm, ?_⟩
      change 2 ≤ 4 ∧ (4, 2 ^ m) ≠ (2, 2) ∧ (4, 2 ^ m) ≠ (2, 3)
      exact ⟨by norm_num, by simp, by simp⟩
    refine center_eq_bot_of_table hGA hX (lieModel_of_mulEquiv e (lieModel_projSL hadm)) ?_ ?_
    · change (Nat.gcd 4 (2 ^ m - 1), 1) = (1, 1)
      have : Nat.Coprime (2 ^ 2) (2 ^ m - 1) :=
        Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hq)
      rw [show Nat.gcd 4 (2 ^ m - 1) = 1 by simpa using this]
    · exact exceptionalOrders_PSL_four hm1
  · obtain ⟨e⟩ := he
    have hadm : StatedLieAdmissible .PSp 3 2 m := by
      refine ⟨Nat.prime_two, hm, ?_⟩
      change 2 ≤ 3 ∧ (3, 2 ^ m) ≠ (2, 2)
      exact ⟨by norm_num, by simp⟩
    refine center_eq_bot_of_table hGA hX (lieModel_of_mulEquiv e (lieModel_projSp hadm)) ?_ ?_
    · change (Nat.gcd 2 (2 ^ m - 1), 1) = (1, 1)
      rw [show Nat.gcd 2 (2 ^ m - 1) = 1 from Nat.coprime_two_left.mpr hq]
    · exact exceptionalOrders_PSp_three hm1
  · obtain ⟨e⟩ := he
    have hadm : StatedLieAdmissible .POmegaMinus 4 2 m := by
      refine ⟨Nat.prime_two, hm, ?_⟩
      change 4 ≤ 4
      exact le_rfl
    refine center_eq_bot_of_table hGA hX
      (lieModel_of_mulEquiv e (lieModel_projOmegaMinus hadm hbc)) ?_ ?_
    · change (Nat.gcd 4 ((2 ^ m) ^ 4 + 1), 1) = (1, 1)
      have h1 : Odd ((2 ^ m) ^ 4 + 1) :=
        (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, hm.ne'⟩, by norm_num⟩).add_one
      have : Nat.Coprime (2 ^ 2) ((2 ^ m) ^ 4 + 1) :=
        Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr h1)
      rw [show Nat.gcd 4 ((2 ^ m) ^ 4 + 1) = 1 by simpa using this]
    · exact exceptionalOrders_POmegaMinus_four m
  · obtain ⟨e⟩ := he
    have hadm : StatedLieAdmissible .PSU 6 2 m := by
      refine ⟨Nat.prime_two, hm, ?_⟩
      change 3 ≤ 6 ∧ (6, 2 ^ m) ≠ (3, 2)
      exact ⟨by norm_num, by simp⟩
    refine center_eq_bot_of_table hGA hX (lieModel_of_mulEquiv e (lieModel_projSU hadm)) ?_ ?_
    · change (Nat.gcd 6 (2 ^ m + 1), 1) = (1, 1)
      have h2 : Nat.Coprime 2 (2 ^ m + 1) :=
        Nat.coprime_two_left.mpr (Nat.even_pow.mpr ⟨even_two, hm.ne'⟩).add_one
      have h3 : Nat.Coprime 3 (2 ^ m + 1) :=
        (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr (not_three_dvd_two_pow_add_one hme)
      have : Nat.Coprime (2 * 3) (2 ^ m + 1) := Nat.coprime_mul_iff_left.mpr ⟨h2, h3⟩
      rw [show Nat.gcd 6 (2 ^ m + 1) = 1 by simpa using this]
    · exact exceptionalOrders_PSU_six hm1

end CFSG.RankThree.PartTwo.KFacts.KS21Mult
