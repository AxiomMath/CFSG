module

public import CFSG.RankThree.PerfectCover.HopfCoverAut

set_option linter.style.haveILetI false

public section

namespace CFSG.RankThree.PerfectCover

variable {S : Type} [Group S] [Finite S] [Group.IsPerfect S]

theorem hopfCoverAut_mem_hopfMultiplier (δ : MulAut S) {x : HopfCover S}
    (hx : x ∈ hopfMultiplier S) : hopfCoverAut δ x ∈ hopfMultiplier S := by
  rw [MonoidHom.mem_ker] at hx ⊢
  have h := congrArg (fun f : HopfCover S →* S => f x) (hopfCoverMap_hopfCoverAut δ)
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hx, map_one] at h
  exact h

theorem hopfCoverAut_map_hopfMultiplier (δ : MulAut S) :
    (hopfMultiplier S).map (hopfCoverAut δ).toMonoidHom = hopfMultiplier S := by
  classical
  letI : Finite (HopfCover S) := finite_hopfCover (inferInstance : Group.IsPerfect S)
  apply Subgroup.eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    exact hopfCoverAut_mem_hopfMultiplier δ hx
  · rw [Subgroup.card_map_of_injective (f := (hopfCoverAut δ).toMonoidHom)
      (hopfCoverAut δ).injective]

@[expose] noncomputable def hopfCoverAutOnMultiplier (δ : MulAut S) :
    MulAut (hopfMultiplier S) :=
  ((hopfCoverAut δ).subgroupMap (hopfMultiplier S)).trans
    (MulEquiv.subgroupCongr (hopfCoverAut_map_hopfMultiplier δ))

@[expose] noncomputable def hopfCoverAutOnSylowTwo (δ : MulAut S)
    (P : Sylow 2 (hopfMultiplier S)) : MulAut P := by
  classical
  letI : IsMulCommutative (hopfMultiplier S) :=
    ⟨⟨fun a b => Subtype.ext
      (Subgroup.mem_center_iff.1 (hopfMultiplier_le_center b.2) (a : HopfCover S))⟩⟩
  letI : Finite (HopfCover S) := finite_hopfCover (inferInstance : Group.IsPerfect S)
  letI : Finite (Sylow 2 (hopfMultiplier S)) := Sylow.finite_of_finiteIndex P
  exact ((hopfCoverAutOnMultiplier δ).subgroupMap P).trans
    (MulEquiv.subgroupCongr
      (Subgroup.characteristic_iff_map_eq.mp
        (Sylow.characteristic_of_normal P inferInstance) (hopfCoverAutOnMultiplier δ)))

theorem hopfCoverAutOnMultiplier_pow_three (δ : MulAut S) (hδ : δ ^ 3 = 1) :
    hopfCoverAutOnMultiplier δ ^ 3 = 1 := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change (hopfCoverAut δ ^ 3) (x : HopfCover S) = (x : HopfCover S)
  rw [hopfCoverAut_pow_three δ hδ]
  rfl

theorem hopfCoverAutOnSylowTwo_pow_three (δ : MulAut S) (hδ : δ ^ 3 = 1)
    (P : Sylow 2 (hopfMultiplier S)) : hopfCoverAutOnSylowTwo δ P ^ 3 = 1 := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  change (hopfCoverAutOnMultiplier δ ^ 3) (x : hopfMultiplier S) =
    (x : hopfMultiplier S)
  rw [hopfCoverAutOnMultiplier_pow_three δ hδ]
  rfl

theorem hopfCoverAutOnSylowTwo_fixed_eq_one (δ : MulAut S) (hδ : δ ^ 3 = 1)
    (P : Sylow 2 (hopfMultiplier S)) (hPcard : Nat.card P = 4)
    (hPne : hopfCoverAutOnSylowTwo δ P ≠ 1) :
    ∀ p : P, hopfCoverAutOnSylowTwo δ P p = p → p = 1 := by
  letI : Finite (HopfCover S) := finite_hopfCover (inferInstance : Group.IsPerfect S)
  letI : Finite (hopfMultiplier S) := inferInstance
  exact CFSG.GroupTheory.fixed_eq_one_of_aut_pow_three_card_four hPcard _
    (hopfCoverAutOnSylowTwo_pow_three δ hδ P) hPne

theorem hopfCoverAut_fixed_two_eq_one (δ : MulAut S) (hδ : δ ^ 3 = 1)
    (P : Sylow 2 (hopfMultiplier S)) (hPcard : Nat.card P = 4)
    (hPne : hopfCoverAutOnSylowTwo δ P ≠ 1)
    {z : HopfCover S} (hzM : z ∈ hopfMultiplier S)
    (hz2 : ∃ k : ℕ, z ^ (2 ^ k) = 1)
    (hfix : hopfCoverAut δ z = z) : z = 1 := by
  classical
  letI : IsMulCommutative (hopfMultiplier S) :=
    ⟨⟨fun a b => Subtype.ext
      (Subgroup.mem_center_iff.1 (hopfMultiplier_le_center b.2) (a : HopfCover S))⟩⟩
  let zm : hopfMultiplier S := ⟨z, hzM⟩
  letI : (Subgroup.zpowers zm).Normal := inferInstance
  have hz2' : IsPGroup 2 (Subgroup.zpowers zm) := by
    obtain ⟨k, hk⟩ := hz2
    have hkM : zm ^ (2 ^ k) = 1 := Subtype.ext (by simpa using hk)
    have hdvd : orderOf zm ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hkM
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    refine IsPGroup.of_card (n := j) ?_
    rw [Nat.card_zpowers, hj]
  have hzP : zm ∈ (P : Subgroup (hopfMultiplier S)) :=
    hz2'.le_sylow_of_normal (N := Subgroup.zpowers zm) P (Subgroup.mem_zpowers zm)
  let zp : P := ⟨zm, hzP⟩
  have hfixP : hopfCoverAutOnSylowTwo δ P zp = zp := by
    apply Subtype.ext
    apply Subtype.ext
    change hopfCoverAut δ z = z
    exact hfix
  have hzp1 : zp = 1 :=
    hopfCoverAutOnSylowTwo_fixed_eq_one δ hδ P hPcard hPne zp hfixP
  have hzm1 : zm = 1 := by
    have h := congrArg (fun p : P => (p : hopfMultiplier S)) hzp1
    simpa [zp] using h
  exact Subtype.ext_iff.mp hzm1

theorem hopfCoverAut_inner_apply_eq (g : S) (z : HopfCover S) (hz : z ∈ hopfMultiplier S) :
    hopfCoverAut (MulAut.conj g) z = z := by
  classical
  obtain ⟨x, hx⟩ := hopfCoverMap_surjective (S := S) g
  have h2 : (hopfCoverMap S).comp (MulAut.conj x).toMonoidHom =
      (MulAut.conj g).toMonoidHom.comp (hopfCoverMap S) := by
    ext y
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
      map_inv, hx]
  have hcomp : (hopfCoverMap S).comp (hopfCoverAut (MulAut.conj g)).toMonoidHom =
      (hopfCoverMap S).comp (MulAut.conj x).toMonoidHom := by
    rw [hopfCoverMap_hopfCoverAut, h2]
  have heq := hopfCover_hom_ext_of_comp_eq (S := S) (q := hopfCoverMap S)
    (hopfMultiplier_le_center (S := S))
    (hopfCoverAut (MulAut.conj g)).toMonoidHom (MulAut.conj x).toMonoidHom hcomp
  have hz' : hopfCoverAut (MulAut.conj g) z = MulAut.conj x z := by
    simpa using DFunLike.congr_fun heq z
  rw [hz']
  change x * z * x⁻¹ = z
  have hcomm : x * z = z * x :=
    Subgroup.mem_center_iff.mp (hopfMultiplier_le_center hz) x
  rw [hcomm]
  group

theorem fixed_free_base_mul_inner_left (δ : MulAut S)
    (hfree : ∀ z ∈ hopfMultiplier S, (∃ k : ℕ, z ^ (2 ^ k) = 1) →
      hopfCoverAut δ z = z → z = 1)
    (g : S) :
    ∀ z ∈ hopfMultiplier S, (∃ k : ℕ, z ^ (2 ^ k) = 1) →
      hopfCoverAut (MulAut.conj g * δ) z = z → z = 1 := by
  intro z hz h2 hfix
  apply hfree z hz h2
  rw [hopfCoverAut_mul, MulAut.mul_apply] at hfix
  rw [hopfCoverAut_inner_apply_eq g (hopfCoverAut δ z)
    (hopfCoverAut_mem_hopfMultiplier δ hz)] at hfix
  exact hfix

theorem fixed_free_base_pow_two (δ : MulAut S) (hδ3 : δ ^ 3 = 1)
    (hfree : ∀ z ∈ hopfMultiplier S, (∃ k : ℕ, z ^ (2 ^ k) = 1) →
      hopfCoverAut δ z = z → z = 1) :
    ∀ z ∈ hopfMultiplier S, (∃ k : ℕ, z ^ (2 ^ k) = 1) →
      hopfCoverAut (δ ^ 2) z = z → z = 1 := by
  intro z hz h2 hfix
  rw [hopfCoverAut_sq] at hfix
  exact fixed_free_pow_two (hopfCoverAut δ) (hopfCoverAut_pow_three δ hδ3) hfree z hz h2 hfix

end CFSG.RankThree.PerfectCover
