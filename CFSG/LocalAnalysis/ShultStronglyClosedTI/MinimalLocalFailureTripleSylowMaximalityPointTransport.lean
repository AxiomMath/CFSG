module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTripleSylowMaximalityStrongEmbedding
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.StrongEmbeddingMaximality
public import CFSG.StronglyEmbedded.BenderNormalSeries

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TripleSylowMaximality

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.OrderReductions.InvolutionGraph CFSG.OrderReductions.StrongEmbedding

universe u v

variable {G : Type u} [Group G] [Finite G]

theorem rank_two_stronglyEmbedded_action_double_transitive
    {Ω : Type v} [MulAction G Ω]
    (htrans : MulAction.IsPretransitive G Ω) (alpha : Ω)
    (hH : fusionStronglyEmbedded (MulAction.stabilizer G alpha))
    (hrank : TwoRankAtLeastTwo G) :
    MulAction.IsMultiplyPretransitive G Ω 2 := by
  let H := MulAction.stabilizer G alpha
  have horder := fusionStronglyEmbedded_to_orderReduction H hH
  let base : Conjugates H := ⟨H, ⟨1, one_smul G H⟩⟩
  have hbase : MulAction.stabilizer G base = H :=
    conjugate_stabilizer_eq H horder base
  have hcoset : MulAction.IsMultiplyPretransitive G (G ⧸ H) 2 := by
    have h := (actionCoset_two_pretransitive_iff
      (inferInstance : MulAction.IsPretransitive G (Conjugates H)) base).mpr
        (rank_two_strongEmbedding_conjugates_double_transitive hrank H hH)
    rwa [hbase] at h
  exact (actionCoset_two_pretransitive_iff htrans alpha).mp hcoset

theorem stronglyEmbedded_action_triple_sylow_maximality_and_conjugacy
    {Ω : Type v} [MulAction G Ω] [Finite Ω]
    (htrans : MulAction.IsPretransitive G Ω)
    (htwo : MulAction.IsMultiplyPretransitive G Ω 2)
    (alpha beta : Ω) (hbeta : beta ≠ alpha)
    (hH : IsStronglyEmbedded (MulAction.stabilizer G alpha))
    {z : G} (hzalpha : z • alpha = alpha) (hz : IsInvolution z)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) {P : Subgroup G}
    (hP : theorem4bIsSylowSubgroupOf p P
      ((MulAction.stabilizer G alpha ⊓ MulAction.stabilizer G beta) ⊓
        MulAction.stabilizer G (z • beta))) :
    Maximal (fun R : Subgroup G => IsPGroup p R ∧
      2 < Nat.card {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω R}) P ∧
      ∀ Q : Subgroup G, Maximal (fun R : Subgroup G => IsPGroup p R ∧
        2 < Nat.card {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω R}) Q →
        ∃ g : G, Q.conjBy g = P := by
  let H := MulAction.stabilizer G alpha
  let e := actionCosetEquiv htrans alpha
  let beta' : conjugateCosetSpace H := e.symm beta
  have hebase : e (QuotientGroup.mk 1 : conjugateCosetSpace H) = alpha :=
    one_smul G alpha
  have hebeta : e beta' = beta := e.apply_symm_apply beta
  have hbeta' : beta' ≠ (QuotientGroup.mk 1 : conjugateCosetSpace H) := by
    intro h
    exact hbeta (hebeta.symm.trans ((congrArg e h).trans hebase))
  have hbetaStab : MulAction.stabilizer G beta' = MulAction.stabilizer G beta := by
    rw [actionCosetEquiv_stabilizer htrans alpha beta', hebeta]
  have hzbetaStab : MulAction.stabilizer G (z • beta') =
      MulAction.stabilizer G (z • beta) := by
    rw [actionCosetEquiv_stabilizer htrans alpha (z • beta'),
      actionCosetEquiv_smul htrans alpha z beta', hebeta]
  have hE : theorem4bSection7E H z beta' =
      ((MulAction.stabilizer G alpha ⊓ MulAction.stabilizer G beta) ⊓
        MulAction.stabilizer G (z • beta)) := by
    rw [theorem4bSection7E, theorem4bSection7D, hbetaStab, hzbetaStab]
  have hP' : theorem4bIsSylowSubgroupOf p P (theorem4bSection7E H z beta') :=
    hE.symm ▸ hP
  have hcard (R : Subgroup G) : Nat.card (theorem4bFixedPoints H R) =
      Nat.card {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω R} :=
    Nat.card_congr (actionCosetFixedEquiv htrans alpha R)
  have hpred : (fun R : Subgroup G => IsPGroup p R ∧
      2 < Nat.card (theorem4bFixedPoints H R)) =
      (fun R : Subgroup G => IsPGroup p R ∧
      2 < Nat.card {omega : Ω // omega ∈ fixedPointsOfSubgroup G Ω R}) := by
    funext R
    rw [hcard]
  have hresult := stronglyEmbedded_base_triple_sylow_maximality_and_conjugacy hH
    ((actionCoset_two_pretransitive_iff htrans alpha).mpr htwo)
    (MulAction.mem_stabilizer_iff.mpr hzalpha) hz hbeta' hp hpodd hP'
  rwa [hpred] at hresult

theorem stronglyEmbedded_three_point_sylow_conjugacy
    (H : Subgroup G) (hH : fusionStronglyEmbedded H)
    (htwo : MulAction.IsMultiplyPretransitive G (Conjugates H) 2)
    (K K' : Conjugates H) (hKK' : K ≠ K')
    {z : G} (hzK : z ∈ K.val) (hz : orderOf z = 2)
    {p : ℕ} (hp : p.Prime) (hpodd : Odd p) {P : Subgroup G}
    (hP : theorem4bIsSylowSubgroupOf p P
      ((K.val ⊓ K'.val) ⊓ (K'.val.conjBy z⁻¹))) :
    Maximal (fun R : Subgroup G => IsPGroup p R ∧
      2 < Nat.card {omega : Conjugates H //
        omega ∈ fixedPointsOfSubgroup G (Conjugates H) R}) P ∧
      ∀ Q : Subgroup G, Maximal (fun R : Subgroup G => IsPGroup p R ∧
        2 < Nat.card {omega : Conjugates H //
          omega ∈ fixedPointsOfSubgroup G (Conjugates H) R}) Q →
        ∃ g : G, Q.conjBy g = P := by
  have horder := fusionStronglyEmbedded_to_orderReduction H hH
  have hK : fusionStronglyEmbedded K.val := by
    obtain ⟨g, hg⟩ := K.property
    rw [← hg]
    exact hH.map_mulEquiv (MulAut.conj g)
  have hzI : IsInvolution z := ⟨(orderOf_eq_prime_iff.mp hz).2,
    (orderOf_eq_prime_iff.mp hz).1⟩
  have hzInv : z⁻¹ = z := inv_eq_self_of_orderOf_eq_two hz
  have hzfix : z • K = K := by
    apply MulAction.mem_stabilizer_iff.mp
    rw [conjugate_stabilizer_eq H horder]
    exact hzK
  have hE : ((MulAction.stabilizer G K ⊓ MulAction.stabilizer G K') ⊓
      MulAction.stabilizer G (z • K')) =
        ((K.val ⊓ K'.val) ⊓ K'.val.conjBy z⁻¹) := by
    rw [conjugate_stabilizer_eq H horder, conjugate_stabilizer_eq H horder,
      conjugate_stabilizer_eq H horder]
    change ((K.val ⊓ K'.val) ⊓ K'.val.conjBy z) = _
    rw [hzInv]
  apply stronglyEmbedded_action_triple_sylow_maximality_and_conjugacy
    (inferInstance : MulAction.IsPretransitive G (Conjugates H)) htwo K K' hKK'.symm
    (by rw [conjugate_stabilizer_eq H horder]; exact hK.to_native) hzfix hzI hp hpodd
  exact hE.symm ▸ hP

end CFSG.ShultStronglyClosedTI.TripleSylowMaximality
