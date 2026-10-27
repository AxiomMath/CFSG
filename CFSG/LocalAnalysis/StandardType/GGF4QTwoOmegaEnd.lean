module

public import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalTwo
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocalFrame
import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
import CFSG.GroupTheory.WeirSylow.UniqueE27Orthogonal
import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.StandardType

open CFSG.ClassicalGroups.Orthogonal.OmegaMinus8ThreeLocal

private theorem nonempty_mulEquiv_omegaMinus8_zmod_two {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {b c : K} (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nonempty (↥(omegaMinus8 K b c) ≃* ↥(omegaMinus8 (ZMod 2) 1 1)) := by
  let _ : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 := by rwa [← Nat.card_eq_fintype_card]
  let φ : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hK').symm
  have hφ : ∀ s : ZMod 2, s ^ 2 + φ b * s + φ c ≠ 0 := by
    intro s hs
    apply hbc (φ.symm s)
    apply φ.injective
    rw [map_add, map_add, map_mul, map_pow, RingEquiv.apply_symm_apply, hs, map_zero]
  have key : ∀ x y : ZMod 2, (∀ s : ZMod 2, s ^ 2 + x * s + y ≠ 0) → x = 1 ∧ y = 1 := by
    decide +kernel
  obtain ⟨hb, hc⟩ := key _ _ hφ
  have hmap := CFSG.ClassicalInvolution.Upgrade.map_statedOmega (ι := OmegaIdx) φ
    (QK := CFSG.Open.StatedQuadMinus 4 K b c) (QL := CFSG.Open.StatedQuadMinus 4 (ZMod 2) 1 1)
    (fun v => CFSG.ClassicalInvolution.Upgrade.statedQuadMinus_comp φ hb hc v)
  exact ⟨((CFSG.Adapters.RankTwoModelTransports.glCongr (ι := OmegaIdx) φ).subgroupMap
    (omegaMinus8 K b c)).trans (MulEquiv.subgroupCongr hmap)⟩

private theorem statedClassicalModel_of_hasLabel_twD41 {X : Type} [Group X]
    (hX : GGHasLabel ⟨.twD, 4, 1⟩ X) :
    CFSG.Open.StatedClassicalModel X .POmegaMinus 4 2 1 := by
  obtain ⟨K, hF, hfin, hK, b, c, hbc, ⟨e⟩⟩ := hX
  exact ⟨by simp only [CFSG.Open.StatedLieAdmissible]; norm_num, K, hF, hfin, hK, b, c, hbc,
    ⟨e.trans (omegaMinusProjEquiv 4 b c)⟩⟩

private theorem exists_mulEquiv_omegaMinus8_two {Y : Type} [Group Y] (hZ : Subgroup.center Y = ⊥)
    (hL : CFSG.Open.StatedClassicalModel (Y ⧸ Subgroup.center Y) .POmegaMinus 4 2 1) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), Nat.card K = 2 ∧
      ∃ b c : K, (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧ Nonempty (Y ≃* ↥(omegaMinus8 K b c)) := by
  obtain ⟨-, K, hF, hfin, hK, b, c, hbc, ⟨e⟩⟩ := hL
  let _ : Fintype K := Fintype.ofFinite K
  have hK' : Fintype.card K = 2 ^ 1 := by simpa [Nat.card_eq_fintype_card] using hK
  have hchar : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 1) hK'
  have hQs : ∀ (d : K) (v : Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K),
      CFSG.Open.StatedQuadMinus 4 K b c (d • v) =
        d ^ 2 * CFSG.Open.StatedQuadMinus 4 K b c v := by
    intro d w
    simp only [CFSG.Open.StatedQuadMinus, Pi.smul_apply, smul_eq_mul, mul_add, Finset.mul_sum]
    have hterm : ∀ i : Fin (4 - 1),
        d * w (Sum.inl i) * (d * w (Sum.inr (Sum.inl i))) =
          d ^ 2 * (w (Sum.inl i) * w (Sum.inr (Sum.inl i))) := fun i => by ring
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    ring
  have hv₀ : CFSG.Open.StatedQuadMinus 4 K b c (Pi.single (Sum.inr (Sum.inr 0)) (1 : K)) ≠ 0 := by
    simp [CFSG.Open.StatedQuadMinus]
  have hscal : (CFSG.Open.StatedScalars (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K).subgroupOf
      (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c)) = ⊥ :=
    TableBOrth.scalars_subgroupOf_omega_eq_bot (Q := CFSG.Open.StatedQuadMinus 4 K b c) hQs hv₀
  have eProj : CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c)) ≃*
      ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c)) :=
    (QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot
  have q : (Y ⧸ Subgroup.center Y) ≃* Y :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact ⟨K, hF, hfin, hchar, by rw [hK]; norm_num, b, c, hbc, ⟨q.symm.trans (e.trans eProj)⟩⟩

theorem nonempty_mulEquiv_twoOmega_of_marking {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥)
    (hX : LargeEvenMarking X (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 4 ∧ lab.n = 1)) :
    Nonempty (X ≃* ↥Two.omega) := by
  obtain ⟨lab, -, hHas, -, -, -, -, -, hP⟩ := largeEvenMarking_exists_hasLabel hX
  obtain ⟨t, r, m⟩ := lab
  obtain ⟨ht, hr, hm⟩ := hP
  dsimp only at ht hr hm
  subst ht hr hm
  obtain ⟨K, _, _, _, hK, b, c, hbc, ⟨e⟩⟩ :=
    exists_mulEquiv_omegaMinus8_two hZ (statedClassicalModel_of_hasLabel_twD41 hHas)
  obtain ⟨e₂⟩ := nonempty_mulEquiv_omegaMinus8_zmod_two hK hbc
  exact ⟨(e.trans e₂).trans (omegaEquiv (toModelIso (K := ZMod 2) (b := 1) (c := 1)
    (by decide +kernel) (by decide +kernel)))⟩

theorem exists_mulEquiv_twoOmega_of_marking_torus {X : Type} [Group X] [Finite X]
    (hZ : Subgroup.center X = ⊥)
    (hX : LargeEvenMarking X (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 4 ∧ lab.n = 1))
    {E : Subgroup X} (hE : CFSG.Open.IsElemAbelian 3 E) (hEcard : Nat.card E = 27) :
    ∃ ψ : X ≃* ↥Two.omega, ∀ g : X, g ∈ E ↔ ((ψ g : Two.Aut) ∈ (cm (ZMod 2)).range) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 : (3 : ZMod 2) ≠ 0 := by decide +kernel
  have hbc : ∀ s : ZMod 2, s ^ 2 + 1 * s + 1 ≠ 0 := by decide +kernel
  obtain ⟨ψ₁⟩ := nonempty_mulEquiv_twoOmega_of_marking hZ hX
  have : Finite ↥Two.omega := Finite.of_equiv X ψ₁.toEquiv
  have hU : CFSG.GroupTheory.UniqueElemSylow 3 3 ↥Two.omega :=
    CFSG.GroupTheory.UniqueElemSylow.of_mulEquiv (omegaEquiv (toModelIso h3 hbc))
      (CFSG.GroupTheory.WeirSylow.uniqueElemSylow_statedOmega_quadMinus_four (ZMod 2) hbc
        (by rw [Nat.card_zmod]; decide +kernel))
  have hmemA₀ : ∀ y : ↥Two.omega,
      y ∈ (cmOmega h3 hbc).range ↔ (y : Two.Aut) ∈ (cm (ZMod 2)).range := by
    intro y
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v, rfl⟩
    · rintro ⟨v, hv⟩
      exact ⟨v, Subtype.ext hv⟩
  have hinj : Function.Injective (cmOmega h3 hbc) := fun v w h =>
    cm_injective (congrArg Subtype.val h)
  have hA₀_ea : CFSG.Open.IsElemAbelian 3 (cmOmega h3 hbc).range := by
    rw [MonoidHom.range_eq_map]
    refine CFSG.SectionRank.isElemAbelian_map ?_ (cmOmega h3 hbc)
    refine ⟨isMulCommutative_iff.mpr ?_, ?_⟩
    · intro a b
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      exact mul_comm _ _
    · intro x _
      exact TableBSymp.pow_card_eq_one_zmod (m := 3) (p := 3)
        (x : Multiplicative (Fin 3 → ZMod 3))
  have hA₀_card : Nat.card (cmOmega h3 hbc).range = 3 ^ 3 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  have hE₁_ea : CFSG.Open.IsElemAbelian 3 (E.map ψ₁.toMonoidHom) :=
    CFSG.SectionRank.isElemAbelian_map hE ψ₁.toMonoidHom
  have hE₁_card : Nat.card (E.map ψ₁.toMonoidHom) = 3 ^ 3 := by
    rw [Subgroup.card_map_of_injective ψ₁.injective, hEcard]
    norm_num
  obtain ⟨h, hh⟩ := CFSG.GroupTheory.UniqueElemSylow.exists_conj_eq hU hA₀_ea hA₀_card hE₁_ea
    hE₁_card
  refine ⟨ψ₁.trans (MulAut.conj h⁻¹), fun g => ?_⟩
  rw [MulEquiv.trans_apply, ← hmemA₀]
  have key : g ∈ E ↔ ψ₁ g ∈ E.map ψ₁.toMonoidHom := by
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  rw [key, hh, Subgroup.mem_map_equiv, MulAut.conj_symm_apply, MulAut.conj_apply, inv_inv]

end CFSG.StandardType
