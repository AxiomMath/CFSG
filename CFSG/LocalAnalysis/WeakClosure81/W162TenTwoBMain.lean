module

public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenDefs
import CFSG.LocalAnalysis.WeakClosure81.W162TenTwoBMin
import CFSG.LocalAnalysis.WeakClosure81.W162TenTwoBApply

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem w162_oddCoreShape15_of_shape {I Q₀ : Subgroup G} [(I.subgroupOf Q₀).Normal] {p : ℕ}
    (hp : p.Prime) (hpow : ∀ y ∈ Q₀, y ^ p ∈ I)
    (hshape : I.relIndex Q₀ = p ∨ (I.relIndex Q₀ = p ^ 3 ∧ ∃ y ∈ Q₀, ∃ z ∈ Q₀, ⁅y, z⁆ ∉ I)) :
    OddCoreShape15 I Q₀ p := by
  have hcard : Nat.card (↥Q₀ ⧸ I.subgroupOf Q₀) = I.relIndex Q₀ := by
    rw [← Subgroup.index_eq_card]
    rfl
  rcases hshape with h1 | ⟨h3, y, hy, z, hz, hnot⟩
  · exact Or.inl (hcard.trans h1)
  · have hcard3 : Nat.card (↥Q₀ ⧸ I.subgroupOf Q₀) = p ^ 3 := hcard.trans h3
    haveI : Fact p.Prime := ⟨hp⟩
    haveI : Fact (IsPGroup p (↥Q₀ ⧸ I.subgroupOf Q₀)) := ⟨IsPGroup.of_card hcard3⟩
    have hpow' : ∀ g : ↥Q₀ ⧸ I.subgroupOf Q₀, g ^ p = 1 := by
      intro g
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hpow x.1 x.2
    have hexp : Monoid.exponent (↥Q₀ ⧸ I.subgroupOf Q₀) = p := by
      rcases (Nat.dvd_prime hp).1 (Monoid.exponent_dvd_of_forall_pow_eq_one hpow') with h | h
      · exfalso
        have hone : ∀ g : ↥Q₀ ⧸ I.subgroupOf Q₀, g = 1 := fun g => by
          simpa [h] using Monoid.pow_exponent_eq_one g
        have hsub : Subsingleton (↥Q₀ ⧸ I.subgroupOf Q₀) :=
          ⟨fun a b => (hone a).trans (hone b).symm⟩
        have hc : Nat.card (↥Q₀ ⧸ I.subgroupOf Q₀) = 1 :=
          Nat.card_eq_one_iff_unique.2 ⟨hsub, ⟨1⟩⟩
        rw [hcard3] at hc
        exact (Nat.one_lt_pow (by norm_num) hp.one_lt).ne' hc
      · exact h
    have hnc : ¬ IsMulCommutative (↥Q₀ ⧸ I.subgroupOf Q₀) := by
      intro hcomm
      have h1 : ((⟨y, hy⟩ : ↥Q₀) : ↥Q₀ ⧸ I.subgroupOf Q₀) *
          ((⟨z, hz⟩ : ↥Q₀) : ↥Q₀ ⧸ I.subgroupOf Q₀) =
          ((⟨z, hz⟩ : ↥Q₀) : ↥Q₀ ⧸ I.subgroupOf Q₀) *
          ((⟨y, hy⟩ : ↥Q₀) : ↥Q₀ ⧸ I.subgroupOf Q₀) :=
        hcomm.is_comm.comm _ _
      apply hnot
      have h2 : (QuotientGroup.mk' (I.subgroupOf Q₀)) ⁅(⟨y, hy⟩ : ↥Q₀), ⟨z, hz⟩⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 h1
      exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h2)
    exact Or.inr ⟨hcard3, CFSG.isExtraspecial_of_noncommutative_card_p3_exponent_p hcard3 hexp hnc,
      hexp⟩

section Certified


theorem w15Ten2b_of_eight1 (hI : NamedInputs15 G) (hW : W15Eight1 G) : W15Ten2b G := by
  intro M V₀ V U S H P Q₀ hS h hP hQ
  obtain ⟨p, hp, hp2, hpow, hcl⟩ := hP.w162_exp_class hI hW hS h hQ
  refine ⟨p, hp, ?_⟩
  haveI := hQ.normal_subgroupOf hP
  exact w162_oddCoreShape15_of_shape hp hpow
    (hP.w162_relIndex_shape hI hW hS h hQ hp hp2 hpow hcl)

end Certified

end CFSG.LocalAnalysis.WeakClosure81
