module

public import CFSG.Quasithin.Background.G8Nine

public section

namespace CFSG.Quasithin

open CFSG.Open

section Finite

variable {H : Type*} [Group H] [Finite H]

theorem perfect_le_oTwoUpper {K X : Subgroup H} (hKX : K ≤ X) (hK : Group.IsPerfect K) :
    K ≤ oTwoUpper X := by
  set M := oTwoUpper X with hM
  have hnorm : ∀ g ∈ K, g ∈ Subgroup.normalizer (M : Set H) := fun g hg =>
    le_normalizer_oTwoUpper X (hKX hg)
  have hMn : (M.subgroupOf K).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact (Subgroup.mem_normalizer_iff.mp (hnorm g g.2) n).mp hn⟩
  have hQ : IsPGroup 2 (K ⧸ M.subgroupOf K) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper X (hKX y.2)
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hk
  have hperf : Group.IsPerfect (K ⧸ M.subgroupOf K) :=
    Group.IsPerfect.ofSurjective (G := K) (G' := K ⧸ M.subgroupOf K)
      (f := QuotientGroup.mk' (M.subgroupOf K)) (QuotientGroup.mk'_surjective _)
  have hnil : Group.IsNilpotent (K ⧸ M.subgroupOf K) := hQ.isNilpotent
  have hsub : Subsingleton (K ⧸ M.subgroupOf K) :=
    CFSG.ComponentClassification.SolvableKernelContainment.perfect_solvable_subsingleton
  intro k hk
  have h1 : (⟨k, hk⟩ : K) ∈ M.subgroupOf K := by
    rw [← QuotientGroup.eq_one_iff]
    exact hsub.elim _ _
  exact h1

theorem oTwoUpper_eq_of_layer_le (hO2 : CFSG.pCore 2 H = ⊥) {X : Subgroup H}
    (hXF : X ≤ CFSG.generalizedFitting H) (hEX : CFSG.layer H ≤ X) : oTwoUpper X = X := by
  refine le_antisymm (oTwoUpper_le X) fun x hx => ?_
  have hx' : x ∈ (↑(CFSG.fittingSubgroup H ⊔ CFSG.layer H) : Set H) := hXF hx
  rw [Subgroup.normal_mul] at hx'
  obtain ⟨f, hf, e, he, rfl⟩ := Set.mem_mul.mp hx'
  have hfX : f ∈ X := by
    have := X.mul_mem hx (X.inv_mem (hEX he))
    simpa using this
  have hodd : Odd (orderOf f) :=
    (G8.fitting_odd hO2).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hf)
  have h1 : f ∈ oTwoUpper X := mem_oTwoUpper_of_odd hfX hodd
  have hperf : Group.IsPerfect (CFSG.layer H) := by
    rw [CFSG.layer_eq_componentClassification]
    exact CFSG.ComponentClassification.Layer.perfect H
  have h2 : e ∈ oTwoUpper X := perfect_le_oTwoUpper hEX hperf he
  exact (oTwoUpper X).mul_mem h1 h2

theorem a44_abstract (hO2 : CFSG.pCore 2 H = ⊥) {X : Subgroup H}
    (h : IsTheta H X ∨ (IsSubnormal X (CFSG.generalizedFitting H) ∧
      lambdaSubgroup (Subgroup.centralizer (X : Set H) ⊓ CFSG.generalizedFitting H) ≤ X)) :
    IsSubnormal X ⊤ ∧ oTwoUpper X = X ∧
      ∀ U : Subgroup H, IsPGroup 2 U → U ≤ Subgroup.normalizer (X : Set H) →
        U ⊓ Subgroup.centralizer (X : Set H) = ⊥ := by
  rcases h with hθ | ⟨hsub, hΛ⟩
  · have hnormal := hθ.normal
    refine ⟨A4.subnormal_of_normal le_top (hnormal.subgroupOf ⊤),
      oTwoUpper_eq_of_layer_le hO2 hθ.le_generalizedFitting hθ.layer_le, fun U hU _ => ?_⟩
    exact g8_9_two hO2 hθ hU
  · refine ⟨isSubnormal_top_of_isSubnormal_generalizedFitting hsub,
      oTwoUpper_eq_of_layer_le hO2 (A4.subnormal_le hsub) (layer_le_of_lambda_le hΛ hsub),
      fun U hU hUX => ?_⟩
    exact g8_9_one hO2 hΛ hsub hU hUX

end Finite

end CFSG.Quasithin
