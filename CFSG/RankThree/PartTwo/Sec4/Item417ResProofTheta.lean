module

public import CFSG.RankThree.PartTwo.Sec4.Item4ResProof417
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs
import CFSG.RankThree.PartTwo.KFacts.KS21Mult
import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.RankThree.PartTwo.Sec4.Item462AltProofModels
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.RankThree.PartTwo.Sec13.Item13ResProofL3
import CFSG.RankThree.PartTwo.Late.Uniqueness

public section

namespace CFSG.RankThree.PartTwo.Sec4.Res417

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.LowTwoRank CFSG.Models
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem card_zmod_prod (a b : ℕ) :
    Nat.card (Multiplicative (ZMod a) × Multiplicative (ZMod b)) = a * b := by
  rw [Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod, Nat.card_zmod]

theorem card_table_PSL_three_dvd (p e : ℕ) :
    Nat.card (Blueprint.Multiplier.generic .PSL 3 p e ×
      Blueprint.Multiplier.exceptional .PSL 3 p e) ∣ 48 := by
  rw [Nat.card_prod, card_zmod_prod, card_zmod_prod]
  have hg : (Blueprint.Multiplier.genericOrders .PSL 3 p e).1 *
      (Blueprint.Multiplier.genericOrders .PSL 3 p e).2 ∣ 3 := by
    unfold Blueprint.Multiplier.genericOrders
    simpa using Nat.gcd_dvd_left 3 (p ^ e - 1)
  have hx : (Blueprint.Multiplier.exceptionalOrders .PSL 3 p e).1 *
      (Blueprint.Multiplier.exceptionalOrders .PSL 3 p e).2 ∣ 16 := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  exact (Nat.mul_dvd_mul hg hx).trans (by norm_num)

theorem card_table_PSU_three_dvd (p e : ℕ) :
    Nat.card (Blueprint.Multiplier.generic .PSU 3 p e ×
      Blueprint.Multiplier.exceptional .PSU 3 p e) ∣ 3 := by
  rw [Nat.card_prod, card_zmod_prod, card_zmod_prod]
  have hg : (Blueprint.Multiplier.genericOrders .PSU 3 p e).1 *
      (Blueprint.Multiplier.genericOrders .PSU 3 p e).2 ∣ 3 := by
    unfold Blueprint.Multiplier.genericOrders
    simpa using Nat.gcd_dvd_left 3 (p ^ e + 1)
  have hx : (Blueprint.Multiplier.exceptionalOrders .PSU 3 p e).1 *
      (Blueprint.Multiplier.exceptionalOrders .PSU 3 p e).2 = 1 := by
    unfold Blueprint.Multiplier.exceptionalOrders
    split <;> simp_all
  rw [hx, mul_one]
  exact hg

theorem card_center_dvd_forty_eight
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels) {X : Type} [Group X]
    [Finite X] (hX : IsQuasisimple X) {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (h : IsoLThreePi (X ⧸ Subgroup.center X) p e) : Nat.card (Subgroup.center X) ∣ 48 := by
  have hp : p.Prime := Fact.out
  have hdvd := KFacts.KS21Mult.card_center_dvd_griess hX.1
    (MulEquiv.refl (X ⧸ Subgroup.center X))
  rcases h with ⟨-, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩
  · have hadm : StatedLieAdmissible .PSL 3 p e := ⟨hp, he, by norm_num, by simp, by simp⟩
    have hm : LieModel (X ⧸ Subgroup.center X) .PSL 3 p e :=
      KFacts.KS21Mult.lieModel_of_mulEquiv φ (KFacts.KS21Mult.lieModel_projSL hadm)
    obtain ⟨eM⟩ := (hGA _ .PSL 3 p e hm).2
    rw [Nat.card_congr eM.toEquiv] at hdvd
    exact hdvd.trans (card_table_PSL_three_dvd p e)
  · have hq2 : p ^ e ≠ 2 := by
      intro h2
      obtain ⟨rfl, rfl⟩ := Sec13.eq_two_one_of_pow_eq_two hp h2
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have := Sec13.isSolvable_projSU_two
      exact false_of_isQuasisimple_of_isSolvable (Sec13.ResProof.isQuasisimple_quotient_center hX)
        (Group.isSolvable_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective)
    have hadm : StatedLieAdmissible .PSU 3 p e :=
      ⟨hp, he, le_refl 3, fun h3 => hq2 (Prod.mk.inj h3).2⟩
    have hm : LieModel (X ⧸ Subgroup.center X) .PSU 3 p e :=
      KFacts.KS21Mult.lieModel_of_mulEquiv φ (KFacts.KS21Mult.lieModel_projSU hadm)
    obtain ⟨eM⟩ := (hGA _ .PSU 3 p e hm).2
    rw [Nat.card_congr eM.toEquiv] at hdvd
    exact (hdvd.trans (card_table_PSU_three_dvd p e)).trans (by norm_num)

variable {G : Type} [Group G] [Finite G]

theorem isoLThreePi_quotient_center {L : Subgroup G} (hL : IsComponent L) {p e : ℕ}
    [Fact p.Prime] (he : 1 ≤ e)
    (h : IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (p ^ e) ∨
      IsoLThreePi (L ⧸ aschbacherSolvableCore 3 L) p e) :
    IsoLThreePi (L ⧸ Subgroup.center L) p e := by
  have hθZ := aschbacherSolvableCore_le_center hL.1
  obtain ⟨-, -, hcen⟩ := CFSG.LocalCores.quasisimple_central_quotient hL.1
    (aschbacherSolvableCore 3 L) hθZ
  let eZ : (L ⧸ aschbacherSolvableCore 3 L) ⧸ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) ≃*
      L ⧸ Subgroup.center L :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans
      (QuotientGroup.quotientQuotientEquivQuotient _ _ hθZ)
  rcases h with hSL | hPSL
  · exact isoLThreePi_congr eZ.symm
      (Item462AltProof.isoLThreePi_quotient_center_of_isSLThreePiAt he hSL)
  · have hZ := Item462AltProof.center_eq_bot_of_isoLThreePi
      (mem_thetaComponents_of_isComponent3 hL) he hPSL
    have e0 : (L ⧸ aschbacherSolvableCore 3 L) ⧸ Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)
        ≃* L ⧸ aschbacherSolvableCore 3 L :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact isoLThreePi_congr (eZ.symm.trans e0) hPSL

theorem theta_eq_bot (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (h2 : CFSG.pCore 2 G = ⊥) {L : Subgroup G} (hL : IsComponent L) (hSL : IsSLThreePiTheta L) :
    aschbacherSolvableCore 3 L = ⊥ := by
  obtain ⟨p, e, _, he, h⟩ := hSL
  have hZ := card_center_dvd_forty_eight hGA hL.1 he (isoLThreePi_quotient_center hL he h)
  have hθZ := aschbacherSolvableCore_le_center hL.1
  have hθdvd : Nat.card (aschbacherSolvableCore 3 L) ∣ 48 :=
    (Subgroup.card_dvd_of_le hθZ).trans hZ
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
    (solvable_prime_complement_core_characterization (H := L) Nat.prime_three).2.2.1
  have hθ16 : Nat.card (aschbacherSolvableCore 3 L) ∣ 2 ^ 4 := by
    have hcop : Nat.Coprime (Nat.card (aschbacherSolvableCore 3 L)) 3 :=
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3))
    exact hcop.dvd_of_dvd_mul_right (by simpa [show (48 : ℕ) = 2 ^ 4 * 3 by norm_num] using hθdvd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2θ : IsPGroup 2 (aschbacherSolvableCore 3 L) := by
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hθ16
    exact IsPGroup.of_card hk
  have hle1 : aschbacherSolvableCore 3 L ≤ CFSG.Open.pCore 2 L := by
    exact le_sSup ⟨inferInstance, h2θ⟩
  have hle2 := Late.pCoreOf_le_pCore_of_isSubnormal 2 hL.2
  rw [h2] at hle2
  have hle : (aschbacherSolvableCore 3 L).map L.subtype ≤ ⊥ :=
    (Subgroup.map_mono (f := L.subtype) hle1).trans hle2
  rw [le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective] at hle
  exact hle

@[expose] noncomputable def thetaQuotEquivOfEqBot {L : Subgroup G}
    (hθ : aschbacherSolvableCore 3 L = ⊥) : L ⧸ aschbacherSolvableCore 3 L ≃* L :=
  (QuotientGroup.quotientMulEquivOfEq hθ).trans QuotientGroup.quotientBot

end CFSG.RankThree.PartTwo.Sec4.Res417
