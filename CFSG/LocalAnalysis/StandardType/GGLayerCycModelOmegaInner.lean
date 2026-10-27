module

public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelOmegaInnerOrth
public import CFSG.LocalAnalysis.StandardType.GGLayerCycModelLabels

public section

namespace CFSG.StandardType

namespace LayerCyc

open Module QuadraticMap CFSG.Assembly CFSG.RankThree.PartOne.KCOrthogonal LayerCores
  LayerCores.OrthRegular

theorem not_smallFixedException_of_five_le {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (h5 : 5 ≤ finrank K V) : ¬ SmallFixedException Q := by
  rintro (⟨h, -⟩ | ⟨⟨h, -⟩, -⟩) <;> omega

theorem ggModelLayerCyclic_conj_of_orthEmbedding {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) (h5 : 5 ≤ finrank K V) {H : Type} [Group H]
    {f : H →* (V ≃ₗ[K] V)} (hf : Function.Injective f)
    (hrange : f.range = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : H) : GGModelLayerCyclic p (MulAut.conj h) := by
  classical
  refine ggModelLayerCyclic_of_subCycCoreFamily fun _ hαp => ?_
  set O := TauCeti.QuadraticMap.orthogonalGroup Q with hO
  have hfr : ∀ x : H, f x ∈ ⁅O, O⁆ := fun x => by
    rw [← hrange]
    exact ⟨x, rfl⟩
  have hfO : ∀ x : H, f x ∈ O := fun x => LayerFacts.ggCommutator_self_le O (hfr x)
  have hcent : ∀ x : H, h ^ p * x = x * h ^ p := by
    intro x
    have h1 : MulAut.conj (h ^ p) x = x := by rw [map_pow, hαp, MulAut.one_apply]
    rwa [MulAut.conj_apply, mul_inv_eq_iff_eq_mul] at h1
  have hp1 : h ^ p = 1 := by
    apply hf
    rw [map_one]
    refine eq_one_of_commute_orthDerived hQ (by omega) (not_smallFixedException_of_five_le h5)
      (hfO _) fun y hy => ?_
    rw [← hrange] at hy
    obtain ⟨x, rfl⟩ := hy
    rw [← map_mul, ← map_mul, hcent x]
  set A := Subgroup.zpowers (f h) with hAdef
  have hAO : A ≤ O := Subgroup.zpowers_le.mpr (hfO h)
  have hAodd : Odd (Nat.card A) := by
    rw [hAdef, Nat.card_zpowers, orderOf_injective f hf]
    exact Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hp1)
  obtain ⟨β, S, hS⟩ := exists_subCycCoreFamily_orthCentralizer hQ hAO hAodd
  have hS' := (hS.inf_of_commutator_le (N := ⁅O, O⁆)
    (Subgroup.commutator_mono inf_le_right inf_le_right)).comap f hf
    (by rw [hrange]; exact inf_le_right)
  have hC : ((Subgroup.centralizer (A : Set (V ≃ₗ[K] V)) ⊓ O) ⊓ ⁅O, O⁆).comap f =
      ggFix (MulAut.conj h) := by
    ext x
    rw [Subgroup.mem_comap, Subgroup.mem_inf, Subgroup.mem_inf, mem_ggFix, MulAut.conj_apply,
      hAdef, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
    constructor
    · rintro ⟨⟨hx, -⟩, -⟩
      exact (hf (by rw [map_mul, map_mul]; exact hx)).symm
    · intro hx
      refine ⟨⟨?_, hfO x⟩, hfr x⟩
      rw [← map_mul, ← map_mul, hx]
  rw [hC] at hS'
  exact ⟨β, _, hS'⟩

end LayerCyc

open CFSG.Assembly CFSG.LieType.Universal LayerCyc

theorem ggLayerOmegaPlusInnerModelInput_holds : GGLayerOmegaPlusInnerModelInput := by
  intro m n K _ _ hK hn hm p hp hp2 h
  have := LayerCC.charP_two_of_natCard hK
  have hinj : Function.Injective (Spin.spinMatrix (Spin.quadPlus m K)) :=
    (MonoidHom.ker_eq_bot_iff _).mp
      (Spin.ker_spinMatrix_quadPlus_eq_bot (n := m) (K := K) CharTwo.two_eq_zero)
  have hrange : (Spin.spinMatrix (Spin.quadPlus m K)).range =
      LargeEvenOmega (LargeEvenQPlus K m) :=
    Spin.range_spinMatrix_quadPlus (by omega)
  set e := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange) with he
  have hf : Function.Injective
      ((Spin.spinAction (Spin.quadPlus m K)).comp e.symm.toMonoidHom) :=
    RootCentOmega.spinAction_quadPlus_injective.comp e.symm.injective
  refine ggModelLayerCyclic_conj_of_orthEmbedding (Spin.nondegenerate_polarBilin_quadPlus m K)
    ?_ hf ?_ hp hp2 h
  · rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective,
      ← MonoidHom.range_eq_map, Spin.range_spinAction_quadPlus_eq_commutator (by omega)]

theorem ggLayerOmegaMinusInnerModelInput_holds : GGLayerOmegaMinusInnerModelInput := by
  intro m n K _ _ hK hn hm b c hbc p hp hp2 h
  have := LayerCC.charP_two_of_natCard hK
  have hinj : Function.Injective (Spin.spinMatrix (Spin.quadMinus (m + 1) K b c)) :=
    (MonoidHom.ker_eq_bot_iff _).mp
      (Spin.ker_spinMatrix_quadMinus_eq_bot (n := m + 1) hbc CharTwo.two_eq_zero)
  have hrange := Spin.range_spinMatrix_quadMinus (n := m + 1) (K := K) (by omega) hbc
  set e := ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).trans
    (largeEvenOmegaMinusEquiv m K b c).symm with he
  have hf : Function.Injective
      ((Spin.spinAction (Spin.quadMinus (m + 1) K b c)).comp e.symm.toMonoidHom) :=
    (RootCentOmega.spinAction_quadMinus_injective hbc).comp e.symm.injective
  refine ggModelLayerCyclic_conj_of_orthEmbedding
    (Spin.nondegenerate_polarBilin_quadMinus_of_finite (m + 1) K hbc) ?_ hf ?_ hp hp2 h
  · rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
    omega
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective,
      ← MonoidHom.range_eq_map, Spin.range_spinAction_quadMinus_eq_commutator (by omega) hbc]

theorem ggLayerOmegaPlusModelInput_holds :
    GGLayerOmegaPlusModelInput :=
  ggLayerOmegaPlusModelInput_of ggLayerOmegaPlusInnerModelInput_holds

theorem ggLayerOmegaMinusModelInput_holds :
    GGLayerOmegaMinusModelInput :=
  ggLayerOmegaMinusModelInput_of ggLayerOmegaMinusInnerModelInput_holds

theorem ggLayerCenterCyclicInput_of_derived_exc
    (hder : GGLayerDerivedFixSolvableInput) (hexc : GGLayerCenterCyclicExcInput) :
    GGLayerCenterCyclicInput :=
  ggLayerCenterCyclicInput_of_inputs ggLayerOmegaPlusInnerModelInput_holds
    ggLayerOmegaMinusInnerModelInput_holds hder hexc

end CFSG.StandardType

end
