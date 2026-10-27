module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.OfType
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.TorusE9
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.EndNodes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.TwE6Nodes
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.ExcTwistedE6
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExcTwE6Rank
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneSpinMinus
public import CFSG.LieType.Steinberg.Minuscule.CertInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open
open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
  CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
  CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.Exceptional
  CFSG.AGLEmbeddingD2.Tits.GN516.Nodes
open CFSG.LieType.Steinberg.TwistedE6
open CFSG.ClassicalInvolution.Models.TwistedPairs (fixedField)
open CFSG.LieType.Simplicity CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc.TwE6
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottLeviExc.TwE6.PB1

private theorem f4_cartan_path (i j : Fin 4) (hij : i ≠ j) :
    (Tag.cartan .F4 i j ≠ 0 ↔ i.val + 1 = j.val ∨ j.val + 1 = i.val) := by
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide

theorem permWitnessTwistedE6_holds :
    PermWitnessTwistedE6 := by
  intro G _ _ hL
  have hCE : ChevalleyExceptionalModel G .twistedE6 2 1 :=
    hL.chevalleyExceptionalModel (by decide)
  obtain ⟨-, k, _, _, hk, θ, hθq, ⟨e⟩⟩ := id hCE
  have hk2 : Nat.card k = (2 ^ 1) ^ 2 := hk
  have : CharP k 2 :=
    finite_field_prime_power_characteristic Nat.prime_two
      (by omega : 1 ≤ 2 * 1) (by rw [hk2, ← pow_mul, mul_comm])
  have hθ : ∀ c, θ (θ c) = c := involutive_of_card hk2 hθq
  have h4 : 4 ≤ Nat.card k := by rw [hk2]; norm_num
  have : Finite (Module.End k (Fin CFSG.LieType.Steinberg.Minuscule.e6Data.d →₀ k)) :=
    Module.finite_of_finite k
  have : Finite ↥(fixedGroup k θ) := inferInstance
  let a : Fin (twistedDatum k θ).rank := nf 0
  let b : Fin (twistedDatum k θ).rank := nf 3
  let π : ↥(fixedGroup k θ) →* G :=
    e.symm.toMonoidHom.comp
      ((QuotientGroup.mk' _).comp (twistedIsogeny θ hθ h4))
  have h : BorelQuotient (twistedDatum k θ) (nHat θ) (hHat k θ) π (Nat.card kˣ) :=
    borelQuotient_e6tw hθ h4 hk2 hθq e
  have hcard3 : Nat.card kˣ = 3 := by
    rw [Nat.card_units, hk2]
    norm_num
  have h3 : BorelQuotient (twistedDatum k θ) (nHat θ) (hHat k θ) π 3 := hcard3 ▸ h
  have hpath : ∀ i j : Fin (twistedDatum k θ).rank, i ≠ j →
      ((twistedDatum k θ).cartan i j ≠ 0 ↔
        i.val + 1 = j.val ∨ j.val + 1 = i.val) :=
    fun i j hij => f4_cartan_path i j hij
  have hfix : Nat.card ↥(fixedField θ) = 2 := by
    simpa using card_fixedField (θ := θ) hk2 hθq
  have : CharP ↥(fixedField θ) 2 :=
    CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero (two_eq_zero_fixedField θ)
  have h6a : Nat.card (rankOne (twistedDatum k θ).rootGroup a) = 6 ∧
      ∃ x ∈ rankOne (twistedDatum k θ).rootGroup a,
        ∃ y ∈ rankOne (twistedDatum k θ).rootGroup a, x * y ≠ y * x :=
    ⟨card_rankOne_fixed (θ := θ) hfix (Or.inl rfl),
      noncomm_of_hasSL2Node hasSL2Node_twE6_zero⟩
  have hs : HasTorusSL2 (twistedDatum k θ) (hHat k θ) b k :=
    hasTorusSL2_twE6_three hθ h4
  have hbk : Nat.card k = 4 := by rw [hk2]; norm_num
  have hb : 2 < Nat.card ↥((twistedDatum k θ).rootGroup (Pi.single b 1)) := by
    have hle := card_le_card_rootGroup_of_hasTorusSL2 hs
    omega
  have hr : 2 ≤ (twistedDatum k θ).rank := by change 2 ≤ 4; norm_num
  have hab : a.val = 0 ∧ b.val + 1 = (twistedDatum k θ).rank :=
    ⟨rfl, by change 3 + 1 = 4; norm_num⟩
  have hend : endNodesThree (twistedDatum k θ) (hHat k θ) = {a} :=
    endNodesThree_eq_of_path h3 hr hpath (a := a) (b := b) (Or.inl hab) h6a hb
  obtain ⟨E, hEP, hE, hE9⟩ :=
    exists_E9_le_parJ_singleton h3 hs (hasSL2Node_twE6_zero.hasOrderThree) h6a
  exact permWitness_of_borelQuotient_singleton h3 (dvd_refl 3) hend h6a hEP hE hE9

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm
