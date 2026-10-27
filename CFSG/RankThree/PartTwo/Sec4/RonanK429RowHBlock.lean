module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429RowHCore

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429H

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec4.RonanK429

section Block

variable {G M : Type} [Group G] [Group M]

theorem isSubnormal_map_subgroupOf {C K : Subgroup G} (hKC : K ≤ C) (β : G →* M)
    (h : (K.subgroupOf C).IsSubnormal) : ((K.map β).subgroupOf (C.map β)).IsSubnormal := by
  set ψ : C →* C.map β := β.subgroupMap C
  have hψ : Function.Surjective ψ := β.subgroupMap_surjective C
  have hmap : (K.subgroupOf C).map ψ = (K.map β).subgroupOf (C.map β) := by
    ext ⟨y, hy⟩
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨⟨x, hxC⟩, hxK, hxy⟩
      refine ⟨x, hxK, ?_⟩
      exact congrArg Subtype.val hxy
    · rintro ⟨x, hxK, rfl⟩
      exact ⟨⟨x, hKC hxK⟩, hxK, rfl⟩
  rw [← hmap]
  exact h.map hψ

variable [Finite G] [Finite M]

theorem not_isType429_of_quasisimple_block
    {C K : Subgroup G}
    (hKC : K ≤ C) [hKp : Group.IsPerfect K] (hKs : (K.subgroupOf C).IsSubnormal) (β : G →* M)
    (hβ : Function.Injective (β.comp K.subtype)) {Q : Subgroup M} (hQC : Q ≤ C.map β)
    (hKQ : K.map β ≤ Q) (hQ : IsQuasisimple Q) {z : M} (hzQ : z ∈ Q)
    (hz : ∀ q ∈ Q, q * z = z * q) (hz3 : orderOf z = 3) :
    ¬ IsType429 (K ⧸ CFSG.pCore 2 K) := by
  intro hT
  haveI := nontrivial_of_isType429 hT
  haveI : Nontrivial K := (QuotientGroup.mk'_surjective (CFSG.pCore 2 K)).nontrivial
  have hs := isSubnormal_subgroupOf_of_le hQC hKQ (isSubnormal_map_subgroupOf hKC β hKs)
  rcases Res429.eq_top_or_le_center_of_isSubnormal hQ hs with htop | hcen
  ·
    have hzK : z ∈ K.map β := Subgroup.subgroupOf_eq_top.mp htop hzQ
    obtain ⟨k, hkK, hkz⟩ := hzK
    have hkc : ∀ k' : K, (⟨k, hkK⟩ : K) * k' = k' * ⟨k, hkK⟩ := by
      intro k'
      apply hβ
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        Subgroup.coe_mul, map_mul, hkz]
      exact (hz (β k') (hKQ ⟨k', k'.2, rfl⟩)).symm
    have hko : orderOf (⟨k, hkK⟩ : K) = 3 := by
      rw [← hz3, ← hkz]
      exact (orderOf_injective _ hβ ⟨k, hkK⟩).symm
    have hcen : (QuotientGroup.mk' (CFSG.pCore 2 K) ⟨k, hkK⟩ : K ⧸ CFSG.pCore 2 K) ∈
        Subgroup.center (K ⧸ CFSG.pCore 2 K) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨k', rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 K) q
      rw [← map_mul, ← map_mul, hkc k']
    have hne : (QuotientGroup.mk' (CFSG.pCore 2 K) ⟨k, hkK⟩ : K ⧸ CFSG.pCore 2 K) ≠ 1 := by
      intro h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 K)) ⟨_, h1⟩
      have hn' : (⟨k, hkK⟩ : K) ^ 2 ^ n = 1 := congrArg Subtype.val hn
      have hd : orderOf (⟨k, hkK⟩ : K) ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hn'
      rw [hko] at hd
      have := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp
        (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2))
      exact this hd
    haveI : Group.IsPerfect (K ⧸ CFSG.pCore 2 K) := inferInstance
    have hZ := center_eq_bot_of_isType429 hT
    rw [hZ, Subgroup.mem_bot] at hcen
    exact hne hcen
  ·
    have hab : ∀ a b : K, a * b = b * a := by
      intro a b
      apply hβ
      simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
        Subgroup.coe_mul, map_mul]
      have ha : (⟨β a, hKQ ⟨a, a.2, rfl⟩⟩ : Q) ∈ Subgroup.center Q := hcen (by
        show β a ∈ K.map β
        exact ⟨a, a.2, rfl⟩)
      have := Subgroup.mem_center_iff.mp ha ⟨β b, hKQ ⟨b, b.2, rfl⟩⟩
      exact (congrArg Subtype.val this).symm
    exact Group.IsPerfect.not_isSolvable K (Group.isSolvable_of_comm hab)

theorem not_isType429_of_quasisimple_block_on
    {C K : Subgroup G}
    (hKC : K ≤ C) [hKp : Group.IsPerfect K] (hKs : (K.subgroupOf C).IsSubnormal) (β : C →* M)
    (hβ : Function.Injective (β.comp (Subgroup.inclusion hKC))) {Q : Subgroup M}
    (hQC : Q ≤ β.range) (hKQ : ∀ k : K, β (Subgroup.inclusion hKC k) ∈ Q) (hQ : IsQuasisimple Q)
    {z : M} (hzQ : z ∈ Q) (hz : ∀ q ∈ Q, q * z = z * q) (hz3 : orderOf z = 3) :
    ¬ IsType429 (K ⧸ CFSG.pCore 2 K) := by
  set K' : Subgroup C := K.subgroupOf C with hK'
  let e : K' ≃* K := Subgroup.subgroupOfEquivOfLe hKC
  haveI : Group.IsPerfect K' :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hs : (K'.subgroupOf (⊤ : Subgroup C)).IsSubnormal := hKs.comap (⊤ : Subgroup C).subtype
  have hcomp : ∀ a : K', (β.comp K'.subtype) a = (β.comp (Subgroup.inclusion hKC)) (e a) :=
    fun a => rfl
  have hinj : Function.Injective (β.comp K'.subtype) := fun a b hab =>
    e.injective (hβ (by rw [← hcomp, ← hcomp]; exact hab))
  have hQC' : Q ≤ (⊤ : Subgroup C).map β := by
    rw [← MonoidHom.range_eq_map]
    exact hQC
  have hKQ' : K'.map β ≤ Q := by
    rintro _ ⟨c, hc, rfl⟩
    exact hKQ ⟨c, hc⟩
  intro hT
  exact not_isType429_of_quasisimple_block (G := C) le_top hs β hinj hQC' hKQ' hQ hzQ hz hz3
    (isType429_quot_congr e.symm hT)

end Block

end CFSG.RankThree.PartTwo.Sec4.RonanK429H
