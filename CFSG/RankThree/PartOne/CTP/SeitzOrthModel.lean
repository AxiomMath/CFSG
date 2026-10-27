module

public import CFSG.RankThree.PartOne.CTP.SeitzOrthMinus
public import CFSG.RankThree.PartOne.CTP.SeitzLift
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian

public section

namespace CFSG.RankThree.PartOne.CTP

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank
open CFSG.RankThree.Classical2 (orthDerived)

theorem closure_centralizers_statedProj_quadMinus_four {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (E : Subgroup (StatedProj (StatedOmega (StatedQuadMinus 4 K b c))))
    [CFSG.IsElementaryAbelian p E] (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {k : StatedProj (StatedOmega (StatedQuadMinus 4 K b c)) |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hQ : ⇑(quadMinus 4 K b c) = StatedQuadMinus 4 K b c := coe_quadMinus 4 K b c
  have hE : ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 K b c)⁆ =
        elementaryGroup (quadMinus 4 K b c) :=
    commutator_orthogonalGroup_quadMinus (by norm_num) hirr
  obtain ⟨hnd, -⟩ := regular_quadMinus (n := 4) (K := K) (by norm_num) hirr
  have : Nontrivial (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) := inferInstance
  have : Finite (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) := Module.finite_of_finite K
  have : Finite ((Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) ≃ₗ[K]
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K)) :=
    Finite.of_injective (fun g => (g : (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) →
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K))) DFunLike.coe_injective
  let ψ : StatedOmega (StatedQuadMinus 4 K b c) ≃* orthDerived (quadMinus 4 K b c) :=
    (statedOmegaEquiv hQ hE).trans (MulEquiv.subgroupCongr hE).symm
  have hψ : ∀ y : StatedOmega (StatedQuadMinus 4 K b c),
      ((ψ y : orthDerived (quadMinus 4 K b c)) :
        (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K) ≃ₗ[K] (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K)) =
        toLinEquiv (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) K (y : GL _ K) := fun y => rfl
  let π : orthDerived (quadMinus 4 K b c) →* StatedProj (StatedOmega (StatedQuadMinus 4 K b c)) :=
    (QuotientGroup.mk' ((StatedScalars _ K).subgroupOf
      (StatedOmega (StatedQuadMinus 4 K b c)))).comp ψ.symm.toMonoidHom
  have hπ : Function.Surjective π := (QuotientGroup.mk'_surjective _).comp ψ.symm.surjective
  have hker : π.ker = (scalars K (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → K)).subgroupOf
      (orthDerived (quadMinus 4 K b c)) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change QuotientGroup.mk (ψ.symm x) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, mem_statedScalars_iff]
    have := hψ (ψ.symm x)
    rw [MulEquiv.apply_symm_apply] at this
    rw [← this]
  have hker' : ¬ p ∣ Nat.card π.ker := by
    rw [hker]
    have h := (scalarKernel_data hnd hp hp2).2
    rw [QuotientGroup.ker_mk'] at h
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 h.symm
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)
  have hexp : ∀ x ∈ E, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  exact closure_centralizers_of_lift π hπ hker' E hcomm hexp fun E' hc he hcd _ =>
    closure_centralizers_orthDerived_quadMinus_four hirr hp hp5 E' hc he (hcd.trans hcard)

end CFSG.RankThree.PartOne.CTP
