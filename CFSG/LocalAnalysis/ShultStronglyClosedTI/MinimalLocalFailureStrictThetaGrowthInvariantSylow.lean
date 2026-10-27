module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureStrictThetaGrowthFamily
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddCorePrimeComplementGrowthSylow

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.StrictThetaGrowth

open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.OrderReductions.InvariantSylow

universe u

variable {G : Type u} [Group G] [Finite G]

theorem admissible_invariant_sylow_containing_witness
    {H : Subgroup G} {z : G} (h : InvolutionPointLocalEmbedding H z)
    (beta : rightCosetSpace H) (hbeta : beta ≠ rightCosetMk H 1)
    (p : ℕ) (hp : p.Prime) (X A : Subgroup G) (v : G)
    (hadm : Admissible H z beta p X A v) :
    let T := Subgroup.normalizer (X : Set G) ⊓ pairOddCore H beta
    ∃ Q : Sylow p T,
      A ≤ (Q : Subgroup T).map T.subtype ∧
      v ∈ Subgroup.normalizer ((Q : Subgroup T).map T.subtype : Set G) ∧
      (Q : Subgroup T).map T.subtype ≠ ⊥ := by
  let : Fact p.Prime := ⟨hp⟩
  let Y := Subgroup.normalizer (X : Set G)
  let T := Y ⊓ pairOddCore H beta
  have hvY : v ∈ Y := hadm.flip_normalizes
  have hvNY : v ∈ Subgroup.normalizer (Y : Set G) := Y.le_normalizer hvY
  have hvJ : v ∈ Subgroup.normalizer (pairOddCore H beta : Set G) :=
    generatedPairGrowth_flip_normalizes_pair_odd_core h hbeta hadm.flip
  have hvT : v ∈ Subgroup.normalizer (T : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hvNY, hvJ⟩
  let f := T.normalizerMonoidHom ⟨v, hvT⟩
  have hTodd : Odd (Nat.card T) := (pairOddCore_odd H beta).of_dvd_nat
    (Subgroup.card_dvd_of_le (inf_le_right : T ≤ pairOddCore H beta))
  have hf : Function.Involutive f := primeComplementGrowth_normalizer_action_involutive
    T v (order_two_of_mem_pointClass h.distinguished_order hadm.flip.1) hvT
  let AT := A.subgroupOf T
  have hATp : IsPGroup p AT := hadm.witness_prime.comap_subtype
  have hATinv : AT.map f.toMonoidHom = AT := by
    apply Subgroup.map_injective (f := T.subtype) T.subtype_injective
    have hcomp : T.subtype.comp f.toMonoidHom =
        (MulAut.conj v).toMonoidHom.comp T.subtype := by
      ext a
      exact Subgroup.normalizerMonoidHom_apply_apply_coe T ⟨v, hvT⟩ a
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hadm.witness_le]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hadm.flip_normalizes_witness
  obtain ⟨Q, hAQ, hQinv⟩ := exists_invariant_sylow_containing_of_odd p hTodd f hf AT
    hATp hATinv
  have hAQG : A ≤ (Q : Subgroup T).map T.subtype := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hadm.witness_le]
    exact Subgroup.map_mono hAQ
  have hvQ := CFSG.OrderReductions.TwoPointSylow.normalizes_image_of_invariant
    T v hvT (Q : Subgroup T) hQinv
  have hQne : (Q : Subgroup T).map T.subtype ≠ ⊥ := by
    intro hbot
    exact hadm.witness_noncentral (hAQG.trans (hbot ▸ bot_le))
  exact ⟨Q, hAQG, hvQ, hQne⟩

end CFSG.ShultStronglyClosedTI.StrictThetaGrowth
