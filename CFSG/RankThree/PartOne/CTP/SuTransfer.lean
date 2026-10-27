module

public import CFSG.RankThree.PartOne.CTP.UnitaryTransfer

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LieType.Universal.Unitary (SUid SUid_eq_statedSU)
open CFSG.LieType.BorelTits (unitaryInvolution)
open scoped MatrixGroups

section Setup

variable {f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 f K)

theorem suid_four_eq_gramSU :
    SUid (unitaryInvolution K 2 f) 4 =
      gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
  rw [SUid_eq_statedSU h.card_eq_sq 4, Units.val_one]
  exact unitarySU_eq_gramSU h 4

@[expose] noncomputable def suEquivFour :
    SUid (unitaryInvolution K 2 f) 4 ≃*
      gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
  MulEquiv.subgroupCongr (suid_four_eq_gramSU h)

omit [Finite K] [CharP K 2] in
theorem center_gramSU_one_eq_four :
    Subgroup.center (gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) =
      normOneScalars h (gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) 4 := by
  have hn : 3 ≤ 4 := by norm_num
  have hnq : ¬ (4 = 3 ∧ 2 ^ f = 2) := by rintro ⟨h4, -⟩; omega
  refine le_antisymm (fun z hz => ?_) (normOneScalars_le_center h _ 4)
  have hsimple := CFSG.RankThree.Classical.isSimpleGroup_primeFormP_one h hn hnq
  have hnc := CFSG.RankThree.Classical.not_commute_primeFormP_one h hn hnq
  have hzc : (QuotientGroup.mk z : primeFormP h ((1 : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K)) ∈ Subgroup.center _ := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hz g']
  rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center (primeFormP h ((1 : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K))) with hb | ht
  · rw [hb, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hzc
    exact hzc
  · exfalso
    apply hnc
    intro x y
    have hx : x ∈ Subgroup.center (primeFormP h ((1 : GL (Fin 4) K) :
        Matrix (Fin 4) (Fin 4) K)) := by rw [ht]; trivial
    exact (Subgroup.mem_center_iff.mp hx y).symm

theorem gcd_four_two_pow_add_one {f : ℕ} (hq : 4 ≤ 2 ^ f) : Nat.gcd 4 (2 ^ f + 1) = 1 := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 hf
  have hodd : Odd (2 ^ f + 1) := by
    obtain ⟨k, hk⟩ := h2
    exact ⟨k, by omega⟩
  have hcop : Nat.Coprime 2 (2 ^ f + 1) := (Nat.coprime_two_left).mpr hodd
  have h4 : Nat.Coprime (2 ^ 2) (2 ^ f + 1) := hcop.pow_left 2
  simpa using h4

omit [Finite K] [CharP K 2] in
theorem normOneScalars_four_eq_bot (hq : 4 ≤ 2 ^ f) :
    normOneScalars h (gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) 4 = ⊥ := by
  have hcard := CFSG.RankThree.Classical.card_normOneScalars_one h (by norm_num : 1 ≤ 4)
  rw [gcd_four_two_pow_add_one hq] at hcard
  exact Subgroup.eq_bot_of_card_eq _ hcard

include h in
theorem center_suid_four_eq_bot (hq : 4 ≤ 2 ^ f) :
    Subgroup.center (SUid (unitaryInvolution K 2 f) 4) = ⊥ := by
  ext x
  rw [← mem_center_iff_of_mulEquiv (suEquivFour h), center_gramSU_one_eq_four h,
    normOneScalars_four_eq_bot h hq, Subgroup.mem_bot, Subgroup.mem_bot]
  exact map_eq_one_iff _ (suEquivFour h).injective

@[expose] noncomputable def suProjFour :
    SUid (unitaryInvolution K 2 f) 4 →*
      primeFormP h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) :=
  (QuotientGroup.mk' (normOneScalars h
    (gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) 4)).comp (suEquivFour h).toMonoidHom

theorem suProjFour_surjective : Function.Surjective (suProjFour h) :=
  (QuotientGroup.mk'_surjective _).comp (suEquivFour h).surjective

theorem suProjFour_injective (hq : 4 ≤ 2 ^ f) : Function.Injective (suProjFour h) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hmem : suEquivFour h x ∈ normOneScalars h
      (gramSU h ((1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) 4 :=
    (QuotientGroup.eq_one_iff _).mp hx
  rw [normOneScalars_four_eq_bot h hq, Subgroup.mem_bot] at hmem
  exact (map_eq_one_iff _ (suEquivFour h).injective).mp hmem

theorem suProjFour_bijective (hq : 4 ≤ 2 ^ f) : Function.Bijective (suProjFour h) :=
  ⟨suProjFour_injective h hq, suProjFour_surjective h⟩

include h in
theorem injective_of_ker_le_center_su (hq : 4 ≤ 2 ^ f) {G : Type*} [Group G]
    (θ : SUid (unitaryInvolution K 2 f) 4 →* G) (hker : θ.ker ≤ Subgroup.center _) :
    Function.Injective θ := by
  refine (MonoidHom.ker_eq_bot_iff θ).mp (eq_bot_iff.mpr fun x hx => ?_)
  have := hker hx
  rw [center_suid_four_eq_bot h hq] at this
  exact this

end Setup

end CFSG.RankThree.PartOne.CTP
