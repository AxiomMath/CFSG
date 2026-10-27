module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.WordSub
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HaradaModel.SylowData
import Certificates.Kernel.HN1408.SylTGlue

public section

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.HaradaModel Subgroup

namespace Certificates

structure HarSylowFacts : Prop where
  sylow_card : Nat.card ↥(wordSubgroup sWords) = 2 ^ 11
  a_mem : elemA ∈ wordSubgroup sWords
  z_mem : elemZ ∈ wordSubgroup sWords
  z_comm_T : ∀ g ∈ wordSubgroup sWords, g ∈ blocks1408 → elemZ * g = g * elemZ
  centre_T : ∀ g ∈ wordSubgroup sWords, g ∈ blocks1408 →
    (∀ y ∈ wordSubgroup sWords, y ∈ blocks1408 → g * y = y * g) →
      g = 1 ∨ g = elemA ∨ g = elemZ ∨ g = elemA * elemZ
  centralizer_T_le : Nat.card ↥P1408 = 177408000 → ∀ g ∈ P1408,
    (∀ y ∈ wordSubgroup sWords, y ∈ blocks1408 → g * y = y * g) → g ∈ blocks1408
  derived_eq : ⁅wordSubgroup sWords, wordSubgroup sWords⁆ = wordSubgroup tpWords
  w0_eq : wordSubgroup (tpWords ++ w0Extra) =
    closure ((wordSubgroup tpWords : Set (Equiv.Perm (Fin 1408))) ∪
      {y | y ∈ wordSubgroup sWords ⊓ blocks1408 ∧ y ^ 2 = 1})
  card_T_a : {g : Equiv.Perm (Fin 1408) | g ∈ wordSubgroup sWords ⊓ blocks1408 ∧
    g ^ 2 = elemA}.ncard = 80
  card_T_az : {g : Equiv.Perm (Fin 1408) | g ∈ wordSubgroup sWords ⊓ blocks1408 ∧
    g ^ 2 = elemA * elemZ}.ncard = 48
  card_T'_a : {g : Equiv.Perm (Fin 1408) | g ∈ wordSubgroup tpWords ∧ g ^ 2 = elemA}.ncard = 16
  card_T'_z : {g : Equiv.Perm (Fin 1408) | g ∈ wordSubgroup tpWords ∧ g ^ 2 = elemZ}.ncard = 32
  card_T'_az : {g : Equiv.Perm (Fin 1408) | g ∈ wordSubgroup tpWords ∧
    g ^ 2 = elemA * elemZ}.ncard = 16
  card_W0_a : {g : Equiv.Perm (Fin 1408) | g ∈ wordSubgroup (tpWords ++ w0Extra) ∧
    g ^ 2 = elemA}.ncard = 48
  card_W0_az : {g : Equiv.Perm (Fin 1408) | g ∈ wordSubgroup (tpWords ++ w0Extra) ∧
    g ^ 2 = elemA * elemZ}.ncard = 16

end Certificates

public section

open CFSG.KD.HN1408.SylSG

namespace Certificates

open CFSG.EvenSporadicStandard.HNRecog CFSG.EvenSporadicStandard.HNRecog.HaradaModel Subgroup in
theorem certificate441662 : HarSylowFacts := by
  obtain ⟨x, R⟩ := exists_recS
  exact
    { sylow_card := R.sylow_card
      a_mem := R.a_mem
      z_mem := R.z_mem
      z_comm_T := fun _ hg _ => R.z_comm hg
      centre_T := fun _ hg hE hc => R.centre_T hg hE hc
      centralizer_T_le := fun hP _ hg hc => R.cent_T_le hP hg hc
      derived_eq := R.derived_eq
      w0_eq := R.w0_eq
      card_T_a := R.card_T_a
      card_T_az := R.card_T_az
      card_T'_a := R.card_T'_a
      card_T'_z := R.card_T'_z
      card_T'_az := R.card_T'_az
      card_W0_a := R.card_W0_a
      card_W0_az := R.card_W0_az }

end Certificates
