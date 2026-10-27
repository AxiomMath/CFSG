module

public import CFSG.HardMathSupport.Solomon.Coordinator.ONCTwoLocalA
import CFSG.RankThree.PartTwo.KFacts.KS14HJCentralizer
public import CFSG.RankThree.PartTwo.Sec13.Item134ONProof

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148V

attribute [local irreducible] dotProduct

open CFSG CFSG.RankThree.Native.ONTriple Subgroup
open scoped commutatorElement

section Model


theorem isTripleCover_K0G : Sec4.IsTripleCover ↥K0G (alternatingGroup (Fin 6)) := by
  refine ⟨?_, ⟨?_⟩⟩
  · rw [CFSG.HardMathSupport.Solomon.Coordinator.center_K0, card_zpowers_zK0]
  · exact (QuotientGroup.quotientMulEquivOfEq
      (CFSG.HardMathSupport.Solomon.Coordinator.center_K0.trans
        CFSG.HardMathSupport.Solomon.Coordinator.ker_actK6.symm)).trans
      (QuotientGroup.quotientKerEquivOfSurjective _
        CFSG.HardMathSupport.Solomon.Coordinator.actK6_surjective)

theorem isPerfect_K0G : Group.IsPerfect ↥K0G :=
  ⟨CFSG.HardMathSupport.Solomon.Coordinator.K0_perfect⟩

theorem model_exists_centralizer_eq_sup {y : GM} (hy3 : y ^ 3 = 1) (hyz : y ∉ zpowers zG) :
    ∃ n : GM, centralizer {y} = zpowers y ⊔ K0G.map (MulAut.conj n).toMonoidHom ∧
      zpowers y ⊓ K0G.map (MulAut.conj n).toMonoidHom = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hy1 : y ≠ 1 := fun h => hyz (h ▸ one_mem _)
  have hp : IsPGroup 3 (zpowers y) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime hy3 hy1)
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq GM P P0Syl
  have hyP : (MulAut.conj g).toMonoidHom y ∈ P0G := by
    rw [← P0Syl_coe, ← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact mem_map_of_mem _ (hP (mem_zpowers y))
  obtain ⟨w, -, c, hwc⟩ := exists_word_conj_x0 hyP (conj_not_mem_zpowers hyz g)
  set n := g⁻¹ * wordN w with hn
  have hyn : y = n * (xG 0 ^ 1 * zG ^ c) * n⁻¹ := by
    rw [pow_one, ← hwc]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, n]
    group
  obtain ⟨h1, h2⟩ := centralizer_conj n (α := 1) (by norm_num) c
  rw [← hyn] at h1 h2
  exact ⟨n, h1, h2⟩

end Model

section Abstract


theorem exists_centralizer_eq_sup_of_ON {X : Type} [Group X] (ψ : X ≃* GM) {u : X}
    (hu3 : u ^ 3 = 1) (huz : u ∉ center X) :
    ∃ K : Subgroup X, Sec4.IsTripleCover ↥K (alternatingGroup (Fin 6)) ∧ Group.IsPerfect ↥K ∧
      centralizer {u} = zpowers u ⊔ K ∧ zpowers u ⊓ K = ⊥ ∧ center X ≤ K := by
  have hyz : ψ u ∉ zpowers zG := fun h =>
    huz ((CFSG.RankThree.PartTwo.Sec13.ON134.mem_center_iff_model ψ).mpr h)
  obtain ⟨n, h1, h2⟩ := model_exists_centralizer_eq_sup (by rw [← map_pow, hu3, map_one]) hyz
  set K₁ : Subgroup GM := K0G.map (MulAut.conj n).toMonoidHom with hK₁
  set K : Subgroup X := K₁.map ψ.symm.toMonoidHom with hK
  have hmapX : ∀ S : Subgroup X, (S.map ψ.toMonoidHom).map ψ.symm.toMonoidHom = S := by
    intro S
    rw [Subgroup.map_map]
    convert Subgroup.map_id S
    ext x
    simp
  have eK₁ : ↥K0G ≃* ↥K₁ := K0G.equivMapOfInjective _ (MulAut.conj n).injective
  have eK : ↥K₁ ≃* ↥K := K₁.equivMapOfInjective _ ψ.symm.injective
  refine ⟨K, KFacts.KS14.isTripleCover_congr (eK₁.trans eK) isTripleCover_K0G, ?_, ?_, ?_, ?_⟩
  · haveI := isPerfect_K0G
    haveI : Group.IsPerfect ↥K₁ := Group.IsPerfect.ofSurjective (f := eK₁.toMonoidHom) eK₁.surjective
    exact Group.IsPerfect.ofSurjective (f := eK.toMonoidHom) eK.surjective
  · have hc : (centralizer {u}).map ψ.toMonoidHom = centralizer {ψ u} := by
      ext y
      simp only [mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [← map_mul, ← map_mul, hx]
      · intro hy
        refine ⟨ψ.symm y, ?_, by simp⟩
        apply ψ.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]
    have hz : (zpowers u).map ψ.toMonoidHom = zpowers (ψ u) := MonoidHom.map_zpowers _ _
    rw [← hmapX (centralizer {u}), hc, h1, Subgroup.map_sup, ← hz, hmapX]
  · have hz : (zpowers u).map ψ.toMonoidHom = zpowers (ψ u) := MonoidHom.map_zpowers _ _
    have hKK : K.map ψ.toMonoidHom = K₁ := by
      rw [hK, Subgroup.map_map]
      convert Subgroup.map_id K₁
      ext x
      simp
    apply Subgroup.map_injective (f := ψ.toMonoidHom) ψ.injective
    rw [Subgroup.map_bot, Subgroup.map_inf_eq _ _ _ ψ.injective, hz, hKK, h2]
  · intro x hx
    have hxz : ψ x ∈ zpowers zG :=
      (CFSG.RankThree.PartTwo.Sec13.ON134.mem_center_iff_model ψ).mp hx
    have hzK₁ : zG ∈ K₁ := ⟨zG, zG_mem_K0', conj_zG n⟩
    have hψK₁ : ψ x ∈ K₁ := zpowers_le.mpr hzK₁ hxz
    exact ⟨ψ x, hψK₁, by simp⟩

end Abstract

end CFSG.RankThree.PartTwo.Sec4.Ronan148V
