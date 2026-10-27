module

public import CFSG.LieType.SeitzGeneration.ExcTorusRank
public import CFSG.LieType.SeitzGeneration.ExcTorusSylow
public import CFSG.LieType.Chevalley.EvenCanonicalFieldCentralizerF4
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.SeitzGeneration.ExcTorusBlocks
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.RegimesExcFamilies
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.RankThree.PartOne.KE.EDualStabilizer

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Open (IsElemAbelian)

@[expose] def GGElemAbelianRankLE (G : Type*) [Group G] (p m : ℕ) : Prop :=
  ∀ E : Subgroup G, IsElemAbelian p E → Nat.card E ≤ p ^ m

@[expose] def GGExcElemAbelianExists (G : Type*) [Group G] (p m : ℕ) : Prop :=
  ∃ E : Subgroup G, IsElemAbelian p E ∧ p ^ m ≤ Nat.card E

theorem orderOf_card_fixSubfield_eq {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (σ : K ≃+* K) (hσ1 : σ ≠ 1) (hσp : σ ^ p = 1) :
    orderOf ((Nat.card (fixSubfield σ) : ℕ) : ZMod p) =
      orderOf ((Nat.card K : ℕ) : ZMod p) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (fixSubfield σ) :=
    Finite.of_injective (Subtype.val : fixSubfield σ → K) Subtype.val_injective
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  have hcardK : Nat.card K = 2 ^ Module.finrank (ZMod 2) K := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)
    rw [Nat.card_zmod] at h
    exact h
  have hn : 1 ≤ Module.finrank (ZMod 2) K := by
    by_contra h
    have h0 : Module.finrank (ZMod 2) K = 0 := by omega
    rw [h0, pow_zero] at hcardK
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    omega
  have hord : orderOf σ = p := orderOf_eq_prime hσp hσ1
  obtain ⟨hdvd, hfix⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield
    Nat.prime_two hn hcardK σ
  rw [hord] at hdvd hfix
  have hq : Nat.card K = Nat.card (fixSubfield σ) ^ p := by
    rw [hfix, hcardK, ← pow_mul, Nat.div_mul_cancel hdvd]
  have hcast : ((Nat.card K : ℕ) : ZMod p) = ((Nat.card (fixSubfield σ) : ℕ) : ZMod p) := by
    rw [hq, Nat.cast_pow]
    exact ZMod.pow_card _
  rw [hcast]

theorem entrywise_fixedFieldInclusion
    {τ : Tag} {K : Type} [Field K]
    [Finite K] (σ : K ≃+* K) (u : adjointGroup τ (fixSubfield σ)) :
    entrywiseAdjointAut τ σ (fixedFieldInclusion σ u) = fixedFieldInclusion σ u := by
  have h : baseChangeGL (fixSubfield σ).subtype (u : ModGL τ (fixSubfield σ)) ∈
      fixedFieldImage τ σ := ⟨u, u.2, rfl⟩
  exact Subtype.ext ((coe_entrywiseAdjointAut _ σ _).trans (fixedFieldImage_le h).2)

theorem exists_elemAbelian_fixSubfield
    {τ : Tag} {K : Type} [Field K]
    [Finite K] {p m : ℕ} (hp : p.Prime) (hm : 1 ≤ m) (σ : K ≃+* K) (hσ1 : σ ≠ 1)
    (hσp : σ ^ p = 1) {B : Subgroup (adjointGroup τ K)} (hB : IsElemAbelian p B)
    (hBcard : Nat.card B ≤ p ^ m)
    (hE : GGExcElemAbelianExists (adjointGroup τ (fixSubfield σ)) p (m - 1)) :
    ∃ E : Subgroup (adjointGroup τ K), IsElemAbelian p E ∧
      (∀ x ∈ E, entrywiseAdjointAut τ σ x = x) ∧ Nat.card B ≤ p * Nat.card E := by
  classical
  obtain ⟨E₀, hE₀, hE₀card⟩ := hE
  refine ⟨E₀.map (fixedFieldInclusion (τ := τ) σ), ?_, ?_, ?_⟩
  · exact hE₀.map _
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := hx
    exact entrywise_fixedFieldInclusion σ u
  · have hcard : Nat.card (E₀.map (fixedFieldInclusion (τ := τ) σ)) = Nat.card E₀ :=
      Subgroup.card_map_of_injective (fixedFieldInclusion_injective σ)
    rw [hcard]
    have hpow : p ^ m = p * p ^ (m - 1) := by
      conv_lhs => rw [show m = (m - 1) + 1 by omega]
      rw [pow_succ]
      ring
    calc Nat.card B ≤ p ^ m := hBcard
      _ = p * p ^ (m - 1) := hpow
      _ ≤ p * Nat.card E₀ := Nat.mul_le_mul_left p hE₀card

end CFSG.StandardType
