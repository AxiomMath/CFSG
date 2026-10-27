module

public import CFSG.RankThree.PartTwo.KFacts.AutLargeRee
import CFSG.RankThree.PartOne.RF4.FinalKFacts
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofReeConj
import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
import CFSG.SignalizerFunctorTheorem.CatalogBridge.LargeReeFixedEmbed

public section

namespace CFSG.RankThree.PartTwo.Sec19.SimsC198

open CFSG CFSG.LieType.Ree CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial


variable {a : ℕ} {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime]

theorem reeGamma_card_centralizer (hK : Nat.card K = 2 ^ (2 * a + 1))
    (y : ReeTag.F4.reeGamma K a) (hy : orderOf y = 3) :
    Nat.card (Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a))) =
      (2 ^ (2 * a + 1)) ^ 3 * ((2 ^ (2 * a + 1)) ^ 2 - 1) * ((2 ^ (2 * a + 1)) ^ 3 + 1) := by
  obtain ⟨e⟩ := Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU a K hK y hy
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : UnitaryFieldData 2 (2 * a + 1) (GaloisField 2 (2 * (2 * a + 1))) :=
    ⟨Nat.prime_two, by omega, GaloisField.card 2 _ (by omega)⟩
  rw [Nat.card_congr e.toEquiv]
  exact KFacts.card_unitarySU_three hU

theorem reeGamma_isQuasisimple_centralizer (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (y : ReeTag.F4.reeGamma K a) (hy : orderOf y = 3) :
    IsQuasisimple (Subgroup.centralizer ({y} : Set (ReeTag.F4.reeGamma K a))) := by
  obtain ⟨e⟩ := Sec8.Item8KFacts2Proof.centralizer_mulEquiv_unitarySU a K hK y hy
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 (2 * (2 * a + 1))) = (2 ^ (2 * a + 1)) ^ 2 := by
    rw [GaloisField.card 2 _ (by omega), ← pow_mul, mul_comm]
  have hnq : ((3 : ℕ), 2 ^ (2 * a + 1)) ≠ (3, 2) := by
    intro h
    have h2 : 2 ^ (2 * a + 1) = 2 := (Prod.mk.inj h).2
    have h8 : 2 ^ 3 ≤ 2 ^ (2 * a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hF le_rfl hnq).1.of_mulEquiv
    e

theorem reeGamma_fixed_of_outer (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    (α : MulAut (ReeTag.F4.reeGamma K a)) (hα : α ^ 3 = 1)
    (hout : α ∉ (MulAut.conj : _ →* MulAut (ReeTag.F4.reeGamma K a)).range) :
    ∃ (b : ℕ) (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k ReeTag.F4.prime),
      Nat.card k = 2 ^ (2 * b + 1) ∧ 3 * (2 * b + 1) = 2 * a + 1 ∧
      ∃ ι : ReeTag.F4.reeGamma k b →* ReeTag.F4.reeGamma K a,
        Function.Injective ι ∧ ∀ x, x ∈ ι.range ↔ α x = x := by
  obtain ⟨β, hβ, hcoset⟩ := KFacts.largeRee_order_three_inFieldCoset ha hK hα hout
  obtain ⟨x, hx⟩ :=
    CFSG.RankThree.PartOne.RF4.largeReeOrderThreeFieldConj a K hK β hβ α hα hcoset
  obtain ⟨b, hchar, hk', hbp, ι, hιinj, hιrange⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.exists_fixedPoints_reeGammaFieldAut_odd hK
      Nat.prime_three (by norm_num) β hβ
  have : Finite (fixSubfield β) := Subtype.finite
  refine ⟨b, fixSubfield β, inferInstance, inferInstance, hchar, hk', by omega,
    ((MulAut.conj x : MulAut (ReeTag.F4.reeGamma K a)) :
      ReeTag.F4.reeGamma K a ≃* ReeTag.F4.reeGamma K a).toMonoidHom.comp ι,
    (MulAut.conj x).injective.comp hιinj, fun z => ?_⟩
  rw [hx]
  exact KFacts.mem_range_conj_comp_iff (MulAut.conj x) (ReeTag.F4.reeGammaFieldAut K a β) ι
    hιrange z

end CFSG.RankThree.PartTwo.Sec19.SimsC198
