module

import CFSG.LocalAnalysis.ComponentInitial.LinearHigherConjAutInner
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.RankThree.PartOne.KC.PlaneLifting
public import CFSG.RankThree.PartOne.KC.PlaneReduction

public noncomputable section

namespace CFSG.RankThree.LinearThreePlane

open Matrix CFSG CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.RankThree.PartOne (autThetaT autPlaneProduct)
open CFSG.RankThree.LocalRank (aschbacherSolvableCore)
open scoped commutatorElement Pointwise

section Helpers

variable {K : Type} [Field K]

theorem mem_inner_of_mem_linearAutGroup [Finite K] {p : ℕ} (hp3 : Nat.Coprime p 3)
    {a : MulAut (projectiveSL 3 K)} (ha : a ∈ linearAutGroup 3 K) (hap : a ^ p = 1) :
    a ∈ (MulAut.conj : projectiveSL 3 K →* MulAut (projectiveSL 3 K)).range :=
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_range_conj_of_mem_linearAutGroup_of_coprime ha hp3 hap

theorem card_le_mul_card_inf_of_cyclic_quotient {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) {A E D : Subgroup G} (hAE : A ≤ E) [(D.subgroupOf E).Normal]
    [IsCyclic (E ⧸ D.subgroupOf E)] (hApow : ∀ x ∈ A, x ^ p = 1) :
    Nat.card A ≤ p * Nat.card (A ⊓ D : Subgroup G) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set π := QuotientGroup.mk' (D.subgroupOf E) with hπ
  let ψ : A →* E ⧸ D.subgroupOf E := π.comp (Subgroup.inclusion hAE)
  have hker : ψ.ker = D.subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show π (Subgroup.inclusion hAE x) = 1 ↔ _
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  have hrange : Nat.card ψ.range ≤ p := by
    have hexp : Monoid.exponent ψ.range ∣ p := by
      apply Monoid.exponent_dvd_of_forall_pow_eq_one
      rintro ⟨_, x, rfl⟩
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← map_pow, Subgroup.coe_one]
      have : x ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hApow x x.2)
      rw [this, map_one]
    rw [← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd hp.pos hexp
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv, hker] at hcard
  have hsub : Nat.card (D.subgroupOf A) = Nat.card (A ⊓ D : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective A.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  rw [hcard, hsub]
  exact Nat.mul_le_mul_right _ hrange

end Helpers

end CFSG.RankThree.LinearThreePlane
