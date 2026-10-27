module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.LeviUniq

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {Λ : Type*} [Group Λ]

@[reducible, expose] def IsTwoElt (x : Λ) : Prop := ∃ k : ℕ, orderOf x = 2 ^ k

theorem isTwoElt_iff_pow {x : Λ} : IsTwoElt x ↔ ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [← hk]; exact pow_orderOf_eq_one x⟩
  · rintro ⟨k, hk⟩
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    exact ⟨j, hj⟩

theorem IsTwoElt.mul_of_commute {x y : Λ} (hc : Commute x y) (hx : IsTwoElt x)
    (hy : IsTwoElt y) : IsTwoElt (x * y) := by
  rw [isTwoElt_iff_pow] at hx hy ⊢
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a + b, ?_⟩
  rw [hc.mul_pow, pow_add, pow_mul, ha, one_pow, one_mul, mul_comm, pow_mul, hb, one_pow]

theorem IsTwoElt.inv {x : Λ} (hx : IsTwoElt x) : IsTwoElt x⁻¹ := by
  obtain ⟨k, hk⟩ := hx
  exact ⟨k, by rw [orderOf_inv, hk]⟩

theorem isTwoElt_one : IsTwoElt (1 : Λ) := ⟨0, by simp⟩

theorem IsTwoElt.conj {x : Λ} (hx : IsTwoElt x) (g : Λ) : IsTwoElt (g * x * g⁻¹) := by
  obtain ⟨k, hk⟩ := hx
  have hs : SemiconjBy g x (g * x * g⁻¹) := by
    unfold SemiconjBy
    group
  exact ⟨k, by rw [← hs.orderOf_eq, hk]⟩

theorem isPGroup_of_forall_isTwoElt {R : Subgroup Λ} (h : ∀ x ∈ R, IsTwoElt x) :
    IsPGroup 2 R := fun x => by
  obtain ⟨k, hk⟩ := isTwoElt_iff_pow.mp (h x x.2)
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem forall_isTwoElt_closure {S : Set Λ} (hS : ∀ x ∈ S, IsTwoElt x)
    (hc : S.Pairwise Commute) : ∀ x ∈ Subgroup.closure S, IsTwoElt x := by
  have hcomm := Subgroup.isMulCommutative_closure hc
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hS y hy
  | one => exact isTwoElt_one
  | mul y z hy hz ihy ihz =>
    exact IsTwoElt.mul_of_commute
      (congrArg Subtype.val (hcomm.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)) ihy ihz
  | inv y _ ihy => exact ihy.inv

theorem eq_one_of_isTwoElt_of_mem_center
    (hO2 : ∀ R : Subgroup Λ, R.Normal → IsPGroup 2 R → R = ⊥) {N : Subgroup Λ} [N.Normal]
    {z : Λ} (hzN : z ∈ N) (hzC : z ∈ Subgroup.centralizer (N : Set Λ)) (hz : IsTwoElt z) :
    z = 1 := by
  set C : Subgroup Λ := Subgroup.centralizer (N : Set Λ) ⊓ N with hCdef
  have hCn : C.Normal := by
    rw [hCdef]
    exact Subgroup.normal_inf_normal _ _
  have hzc : z ∈ C := ⟨hzC, hzN⟩
  have hR := Subgroup.normalClosure_normal (s := ({z} : Set Λ))
  have hRC : Subgroup.normalClosure ({z} : Set Λ) ≤ C :=
    Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr hzc)
  have hconj : ∀ x ∈ Group.conjugatesOfSet ({z} : Set Λ), IsTwoElt x ∧ x ∈ C := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    rw [Set.mem_singleton_iff] at hy
    subst hy
    obtain ⟨g, rfl⟩ := isConj_iff.mp hxy
    exact ⟨hz.conj g, hCn.conj_mem _ hzc g⟩
  have hpair : (Group.conjugatesOfSet ({z} : Set Λ)).Pairwise Commute := by
    intro a ha b hb _
    have hbN : b ∈ N := (hconj b hb).2.2
    exact (Subgroup.mem_centralizer_iff.mp (hconj a ha).2.1 b hbN).symm
  have h2 : IsPGroup 2 (Subgroup.normalClosure ({z} : Set Λ)) :=
    isPGroup_of_forall_isTwoElt fun x hx =>
      forall_isTwoElt_closure (fun y hy => (hconj y hy).1) hpair x hx
  have hbot := hO2 _ hR h2
  have hzR : z ∈ Subgroup.normalClosure ({z} : Set Λ) :=
    Subgroup.subset_normalClosure (Set.mem_singleton z)
  rw [hbot, Subgroup.mem_bot] at hzR
  exact hzR

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.LeviFamily.LeviUniq

end
