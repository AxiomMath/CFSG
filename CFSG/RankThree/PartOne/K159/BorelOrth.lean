module

public import CFSG.RankThree.PartOne.K159.BorelSL
public import CFSG.RankThree.PartOne.K159.BorelUnitary
public import CFSG.RankThree.PartOne.S11d.OrthModels
public import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow

public section

namespace CFSG.RankThree.PartOne.K159

open Module QuadraticMap CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2
open scoped MatrixGroups commutatorElement

section Four

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem borelFactsGrp_orthDerived_four {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (Q : QuadraticForm K W) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : finrank K W = 4) (hts : ∀ U : Submodule K W, finrank K U = 2 → ∃ u ∈ U, Q u ≠ 0)
    {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K - 1) (hp3 : 3 < p) :
    BorelFactsGrp p ↥(orthDerived Q) := by
  obtain ⟨E, _, _, D, ψ, hψ⟩ := exists_evenMinus_model Q hQ (n := 2) (by norm_num) (by omega) hts
  have : Finite W := Module.finite_of_finite K
  have : Finite (W ≃ₗ[K] W) :=
    Finite.of_injective (fun g : W ≃ₗ[K] W => (g : W → W)) DFunLike.coe_injective
  have : CharP E 2 := charP_two_of_algebra (K := K)
  have := D.finite_E
  let e1 : Q.IsometryEquiv (evenNormTailForm D.N 1) :=
    { toLinearEquiv := ψ
      map_app' := fun w => hψ w }
  let e2 : Q.IsometryEquiv (hermFourForm D) := e1.trans (hermFourIsometry D)
  obtain ⟨-, -, -, -, -, -, -, -, hinj, -, -, -, -, -, -, -, hcomm, -⟩ :=
    even_minus_four_hermitian_derived_model D
  have hrange : orthDerived (hermFourForm D) = (hermFourRho D).range := hcomm
  let e3 : SL(2, E) ≃* ↥(orthDerived (hermFourForm D)) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange.symm)
  have hpE : p ∣ Nat.card E - 1 := by
    rw [D.card_E]
    exact hpq.trans (by simpa using Nat.sub_dvd_pow_sub_pow (Nat.card K) 1 2)
  have hSL := borelFactsGrp_specialLinear (K := E) (m := 2) hp hpE le_rfl (by omega)
  exact BorelFactsGrp.of_mulEquiv (e3.trans (orthDerivedEquiv e2).symm) hSL

end Four

section Six

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem borelFactsGrp_orthDerived_six {W : Type} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (Q : QuadraticForm K W) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : finrank K W = 6) (hts : ∀ U : Submodule K W, finrank K U = 3 → ∃ u ∈ U, Q u ≠ 0)
    {p : ℕ} (hp : p.Prime) (hpq : p ∣ Nat.card K - 1) (hp3 : 3 < p) :
    BorelFactsGrp p ↥(orthDerived Q) := by
  obtain ⟨E, _, _, D, ψ, hψ⟩ := exists_evenMinus_model Q hQ (n := 3) (by norm_num) (by omega) hts
  have : CharP E 2 := charP_two_of_algebra (K := K)
  have := D.finite_E
  have : Finite W := Module.finite_of_finite K
  have : Finite (W ≃ₗ[K] W) :=
    Finite.of_injective (fun g : W ≃ₗ[K] W => (g : W → W)) DFunLike.coe_injective
  let e1 : Q.IsometryEquiv (evenNormTailForm D.N 2) :=
    { toLinearEquiv := ψ
      map_app' := fun w => hψ w }
  let e2 : Q.IsometryEquiv D.sixForm := e1.trans D.sixIsometry
  obtain ⟨-, -, -, -, -, -, -, -, hinj, -, -, -, -, -, -, -, hcomm, -⟩ :=
    even_minus_six_unitary_derived_model D
  have hrange : orthDerived D.sixForm = D.sixRho.range := hcomm
  let e3 : D.sixSU ≃* ↥(orthDerived D.sixForm) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange.symm)
  obtain ⟨f, hU, hcard, hbar⟩ := D.exists_unitaryFieldData
  obtain ⟨e4⟩ := D.nonempty_sixSU_mulEquiv hU hbar
  obtain ⟨R, hR⟩ := CFSG.ClassicalGroups.UnitaryFlag.exists_isHypTransport (r := 2) (ε := 0) hU
  have hfin := hU.finite
  have hpq' : p ∣ 2 ^ f - 1 := by
    rw [← hcard]
    exact hpq
  have hB := borelFactsGrp_hypSU_four hU hp hpq' hp3
  exact BorelFactsGrp.of_mulEquiv
    ((CFSG.ClassicalGroups.UnitaryFlag.hypTransport hU hR).trans
      (e4.symm.trans (e3.trans (orthDerivedEquiv e2).symm))) hB

end Six

end CFSG.RankThree.PartOne.K159
