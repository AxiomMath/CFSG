module

public import CFSG.RankThree.PartOne.S10.SemisimpleContract
public import CFSG.GroupTheory.LocalCores.Layer
import CFSG.RankThree.PartOne.S10.QuotientComponentOrbit
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantConjugacy
import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.RankThree.PartOne.SemisimpleSection

open CFSG CFSG.LocalCores Subgroup

section ComponentPermutation

variable {X : Type*} [Group X]

@[expose] def conjComponentPerm (g : X) : Equiv.Perm (ComponentIndex X) where
  toFun C := ⟨C.1.map (MulAut.conj g).toMonoidHom, isComponent_map_mulEquiv _ C.2⟩
  invFun C := ⟨C.1.map (MulAut.conj g⁻¹).toMonoidHom, isComponent_map_mulEquiv _ C.2⟩
  left_inv C := Subtype.ext (by
    simp only
    rw [← RankThreeEvenClassification.Helpers.subgroup_map_conj_mul, inv_mul_cancel]
    ext y
    simp)
  right_inv C := Subtype.ext (by
    simp only
    rw [← RankThreeEvenClassification.Helpers.subgroup_map_conj_mul, mul_inv_cancel]
    ext y
    simp)

theorem coe_conjComponentPerm (g : X) (C : ComponentIndex X) :
    (conjComponentPerm g C).1 = C.1.map (MulAut.conj g).toMonoidHom := rfl

@[expose] def conjComponentPermHom (X : Type*) [Group X] : X →* Equiv.Perm (ComponentIndex X) where
  toFun := conjComponentPerm
  map_one' := Equiv.ext fun C => Subtype.ext (by
    rw [coe_conjComponentPerm]
    ext y
    simp)
  map_mul' g h := Equiv.ext fun C => Subtype.ext (by
    rw [Equiv.Perm.mul_apply, coe_conjComponentPerm, coe_conjComponentPerm, coe_conjComponentPerm,
      ← RankThreeEvenClassification.Helpers.subgroup_map_conj_mul])

end ComponentPermutation

end CFSG.RankThree.PartOne.SemisimpleSection

namespace CFSG.RankThree.PartOne

open CFSG CFSG.LocalCores Subgroup SemisimpleSection
open CFSG.Assembly (evenRank)

theorem perfect_subgroups_normalize_quotient_components_at_rank_three_of
    (h3 : QuotientComponentOrbitBound) :
    PerfectSubgroupsNormalizeQuotientComponentsAtRankThree := by
  intro G _ _ hG N _ P hP L hL
  have := hP
  let α : ↥P →* Equiv.Perm (ComponentIndex (G ⧸ N)) :=
    (conjComponentPermHom (G ⧸ N)).comp P.subtype
  have : Group.IsPerfect ↥α.range := Group.IsPerfect.range α
  have hM : Subsingleton ↥α.range := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    refine Group.IsPerfect.not_isSolvable ↥α.range ?_
    refine CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two ?_
    have hsub : (Nat.card ↥α.range).primeFactors ⊆ {2, 3} := by
      intro r hr
      have hrp : r.Prime := Nat.prime_of_mem_primeFactors hr
      have hrdvd : r ∣ Nat.card ↥α.range := Nat.dvd_of_mem_primeFactors hr
      have : Fact r.Prime := ⟨hrp⟩
      obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' (G := ↥α.range) r hrdvd
      obtain ⟨y, hy⟩ := σ.2
      obtain ⟨a, t, ht, hat⟩ :=
        Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' r hrp.ne_one
      have ht0 : t ≠ 0 := by
        rintro rfl
        exact ht (dvd_zero r)
      have hord : orderOf (y ^ t) = r ^ a := by
        rw [orderOf_pow_of_dvd ht0 (hat ▸ dvd_mul_left t _), hat,
          Nat.mul_div_cancel _ (Nat.pos_of_ne_zero ht0)]
      have hα : α (y ^ t) ≠ 1 := by
        intro h1
        rw [map_pow, hy] at h1
        have h2 : orderOf (σ : Equiv.Perm (ComponentIndex (G ⧸ N))) ∣ t :=
          orderOf_dvd_of_pow_eq_one h1
        rw [Subgroup.orderOf_coe, hσ] at h2
        exact ht h2
      obtain ⟨C, hC⟩ : ∃ C : ComponentIndex (G ⧸ N), α (y ^ t) C ≠ C := by
        by_contra hno
        push Not at hno
        exact hα (Equiv.ext hno)
      have hmove : C.1.map (MulAut.conj (((y ^ t : ↥P)) : G ⧸ N)).toMonoidHom ≠ C.1 := fun h =>
        hC (Subtype.ext h)
      have hxord : ∃ k : ℕ, orderOf (((y ^ t : ↥P)) : G ⧸ N) = r ^ k :=
        ⟨a, (Subgroup.orderOf_coe (y ^ t)).trans hord⟩
      obtain ⟨hrd, hd4⟩ := h3 G 3 hG N r hrp _ hxord C.1 C.2 hmove _ rfl
      have hr4 : r ≤ 4 := hrd.trans hd4
      have hr2 := hrp.two_le
      interval_cases r
      · simp
      · simp
      · norm_num at hrp
    exact (Finset.card_le_card hsub).trans (by simp)
  intro y hy
  have h1 : α ⟨y, hy⟩ = 1 :=
    congrArg Subtype.val (Subsingleton.elim (⟨α ⟨y, hy⟩, ⟨_, rfl⟩⟩ : ↥α.range) 1)
  have h2 := congrArg (fun σ : Equiv.Perm (ComponentIndex (G ⧸ N)) => (σ ⟨L, hL⟩).1) h1
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h2

theorem perfect_subgroups_normalize_quotient_components_at_rank_three :
    PerfectSubgroupsNormalizeQuotientComponentsAtRankThree :=
  perfect_subgroups_normalize_quotient_components_at_rank_three_of
    quotient_component_orbit_bound

end CFSG.RankThree.PartOne
