module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.LocalCores
open scoped commutatorElement

theorem normal_subgroupOf_of_commutator_le {G : Type*} [Group G] {C N : Subgroup G}
    (h : ⁅C, C⁆ ≤ N) : (N.subgroupOf C).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have h1 : ((g * n * g⁻¹ : C) : G) = ⁅(g : G), (n : G)⁆ * (n : G) := by
    simp [commutatorElement_def, mul_assoc]
  rw [h1]
  exact N.mul_mem (h (Subgroup.commutator_mem_commutator g.2 n.2)) hn

@[expose] def BlockData {G : Type*} [Group G] (C : Subgroup G) (y : G) : Prop :=
  ∃ N₁ N₂ : Subgroup G, N₁ ≤ C ∧ N₂ ≤ C ∧ ⁅C, C⁆ ≤ N₁ ⊔ N₂ ∧
    (N₁.subgroupOf C).Normal ∧ (N₂.subgroupOf C).Normal ∧ IsQuasisimple N₁ ∧ IsQuasisimple N₂ ∧
    (∃ j ∈ N₁, ∃ z ∈ Subgroup.centralizer (N₁ : Set G), y = j * z) ∧
    (∃ j ∈ N₂, ∃ z ∈ Subgroup.centralizer (N₂ : Set G), y = j * z)


section Transport

variable {G : Type*} [Group G] {X : Type*} [Group X]

@[expose] def imageIn {S : Subgroup G} (ψ : S ≃* X) (N : Subgroup G) : Subgroup X :=
  (N.subgroupOf S).map ψ.toMonoidHom

theorem mem_imageIn {S : Subgroup G} (ψ : S ≃* X) {N : Subgroup G} {x : X} :
    x ∈ imageIn ψ N ↔ ((ψ.symm x : S) : G) ∈ N := by
  unfold imageIn
  rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]

theorem imageIn_sup {S : Subgroup G} (ψ : S ≃* X) {N₁ N₂ : Subgroup G} (h₁ : N₁ ≤ S)
    (h₂ : N₂ ≤ S) : imageIn ψ (N₁ ⊔ N₂) = imageIn ψ N₁ ⊔ imageIn ψ N₂ := by
  unfold imageIn
  rw [Subgroup.subgroupOf_sup h₁ h₂, Subgroup.map_sup]

theorem BlockData.transport {S : Subgroup G} (ψ : S ≃* X) {t y : G} (ht : t ∈ S) (hy : y ∈ S)
    (hB : BlockData (S ⊓ Subgroup.centralizer {t}) y) :
    BlockData (Subgroup.centralizer {ψ ⟨t, ht⟩}) (ψ ⟨y, hy⟩) := by
  obtain ⟨N₁, N₂, hN₁, hN₂, hcomm, hn₁, hn₂, hq₁, hq₂, hy₁, hy₂⟩ := hB
  set C : Subgroup G := S ⊓ Subgroup.centralizer {t} with hC
  set w : X := ψ ⟨t, ht⟩ with hw
  have hcent : ∀ g : X, g ∈ Subgroup.centralizer ({w} : Set X) ↔
      ((ψ.symm g : S) : G) ∈ C := by
    intro g
    rw [Subgroup.mem_centralizer_singleton_iff, hC, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hg
      refine ⟨(ψ.symm g).2, ?_⟩
      have h1 : ψ.symm g * ⟨t, ht⟩ = ⟨t, ht⟩ * ψ.symm g := by
        apply ψ.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact hg
      exact congrArg Subtype.val h1
    · rintro ⟨-, hg⟩
      have h1 : ψ.symm g * ⟨t, ht⟩ = ⟨t, ht⟩ * ψ.symm g := Subtype.ext hg
      have h2 := congrArg ψ h1
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
      exact h2
  have hNC : ∀ N : Subgroup G, N ≤ C → imageIn ψ N ≤ Subgroup.centralizer {w} := by
    intro N hNC x hx
    rw [hcent]
    exact hNC ((mem_imageIn ψ).mp hx)
  have hNS : ∀ N : Subgroup G, N ≤ C → N ≤ S := fun N hN x hx => (hN hx).1
  have hnorm : ∀ N : Subgroup G, N ≤ C → (N.subgroupOf C).Normal →
      ((imageIn ψ N).subgroupOf (Subgroup.centralizer {w})).Normal := by
    intro N hNC hN
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf, mem_imageIn] at hn ⊢
    have hgC := (hcent (g : X)).mp g.2
    have hnC := (hcent (n : X)).mp n.2
    have h1 : ((ψ.symm ((g * n * g⁻¹ : Subgroup.centralizer ({w} : Set X)) : X) : S) : G) =
        (((ψ.symm (g : X) : S) : G)) * ((ψ.symm (n : X) : S) : G) *
          (((ψ.symm (g : X) : S) : G))⁻¹ := by
      simp
    rw [h1]
    have := hN.conj_mem (⟨_, hnC⟩ : C) (Subgroup.mem_subgroupOf.mpr hn) ⟨_, hgC⟩
    exact Subgroup.mem_subgroupOf.mp this
  have hquasi : ∀ N : Subgroup G, N ≤ C → IsQuasisimple N → IsQuasisimple (imageIn ψ N) := by
    intro N hNC hq
    let e : N ≃* imageIn ψ N :=
      (Subgroup.subgroupOfEquivOfLe (hNS N hNC)).symm.trans
        (Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective)
    exact isQuasisimple_of_mulEquiv e hq
  have hyz : ∀ N : Subgroup G, N ≤ C → (∃ j ∈ N, ∃ z ∈ Subgroup.centralizer (N : Set G),
      y = j * z) → ∃ j ∈ imageIn ψ N, ∃ z ∈ Subgroup.centralizer (imageIn ψ N : Set X),
      ψ ⟨y, hy⟩ = j * z := by
    rintro N hNC ⟨j, hj, z, hz, hyjz⟩
    have hjS : j ∈ S := hNS N hNC hj
    have hzS : z ∈ S := by
      have : z = j⁻¹ * y := by rw [hyjz]; group
      rw [this]
      exact S.mul_mem (S.inv_mem hjS) hy
    refine ⟨ψ ⟨j, hjS⟩, ?_, ψ ⟨z, hzS⟩, ?_, ?_⟩
    · rw [mem_imageIn, MulEquiv.symm_apply_apply]
      exact hj
    · rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' : ((ψ.symm x : S) : G) ∈ N := (mem_imageIn ψ).mp hx
      have hxz : ((ψ.symm x : S) : G) * z = z * ((ψ.symm x : S) : G) :=
        Subgroup.mem_centralizer_iff.mp hz _ hx'
      have h1 : ψ.symm x * ⟨z, hzS⟩ = ⟨z, hzS⟩ * ψ.symm x := Subtype.ext hxz
      have h2 := congrArg ψ h1
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
      exact h2
    · rw [← map_mul]
      congr 1
      exact Subtype.ext hyjz
  refine ⟨imageIn ψ N₁, imageIn ψ N₂, hNC N₁ hN₁, hNC N₂ hN₂, ?_, hnorm N₁ hN₁ hn₁,
    hnorm N₂ hN₂ hn₂, hquasi N₁ hN₁ hq₁, hquasi N₂ hN₂ hq₂, hyz N₁ hN₁ hy₁, hyz N₂ hN₂ hy₂⟩
  rw [← imageIn_sup ψ (hNS N₁ hN₁) (hNS N₂ hN₂), Subgroup.commutator_le]
  intro g hg k hk
  rw [mem_imageIn]
  have hgC := (hcent g).mp hg
  have hkC := (hcent k).mp hk
  have h1 : ((ψ.symm ⁅g, k⁆ : S) : G) = ⁅((ψ.symm g : S) : G), ((ψ.symm k : S) : G)⁆ := by
    simp [commutatorElement_def]
  rw [h1]
  exact hcomm (Subgroup.commutator_mem_commutator hgC hkC)

end Transport


section Comb

variable {X : Type*} [Group X] [Finite X]

theorem BlockData.exists_le_of_perfect_subnormal {C Y : Subgroup X} {y : X}
    (hB : BlockData C y) (hYC : Y ≤ C) (hYp : Group.IsPerfect Y) (hY0 : Y ≠ ⊥)
    (hYs : (Y.subgroupOf C).IsSubnormal) :
    ∃ J : Subgroup X, J ≤ Y ∧ (J.subgroupOf C).Normal ∧ Group.IsPerfect J ∧
      ¬ Group.IsSolvable J ∧ ∃ j₀ ∈ J, ∃ z ∈ Subgroup.centralizer (J : Set X), y = j₀ * z := by
  obtain ⟨N₁, N₂, hN₁, hN₂, hcomm, hn₁, hn₂, hq₁, hq₂, hy₁, hy₂⟩ := hB
  have hdich : ∀ N : Subgroup X, N ≤ C → (N.subgroupOf C).Normal → IsQuasisimple N →
      N ≤ Y ∨ ∀ n ∈ N, ∀ g ∈ Y, n * g = g * n := by
    intro N hNC hNn hq
    have hcomp : IsComponent (N.subgroupOf C) :=
      ⟨isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNC).symm hq,
        Subgroup.Normal.isSubnormal hNn⟩
    rcases component_subnormal_subgroup hcomp hYs with h | h
    · left
      intro x hx
      have : (⟨x, hNC hx⟩ : C) ∈ Y.subgroupOf C := h (Subgroup.mem_subgroupOf.mpr hx)
      exact Subgroup.mem_subgroupOf.mp this
    · right
      intro n hn g hg
      have h1 : ⁅(⟨n, hNC hn⟩ : C), (⟨g, hYC hg⟩ : C)⁆ ∈ ⁅N.subgroupOf C, Y.subgroupOf C⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_subgroupOf.mpr hn)
          (Subgroup.mem_subgroupOf.mpr hg)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
      exact congrArg Subtype.val h1
  have hperf : ∀ N : Subgroup X, IsQuasisimple N → Group.IsPerfect N := fun N hq => hq.1
  have hns : ∀ N : Subgroup X, IsQuasisimple N → ¬ Group.IsSolvable N := by
    intro N hq hsol
    haveI := isQuasisimple_nontrivial hq
    haveI := hq.1
    exact Group.IsPerfect.not_isSolvable N hsol
  rcases hdich N₁ hN₁ hn₁ hq₁ with h₁ | h₁
  · exact ⟨N₁, h₁, hn₁, hperf N₁ hq₁, hns N₁ hq₁, hy₁⟩
  rcases hdich N₂ hN₂ hn₂ hq₂ with h₂ | h₂
  · exact ⟨N₂, h₂, hn₂, hperf N₂ hq₂, hns N₂ hq₂, hy₂⟩
  exfalso
  have hYN : Y ≤ N₁ ⊔ N₂ := by
    have : ⁅Y, Y⁆ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hYC hYC
    rw [Subgroup.isPerfect_iff.mp hYp] at this
    exact this.trans hcomm
  have hcen : N₁ ⊔ N₂ ≤ Subgroup.centralizer (Y : Set X) := by
    refine sup_le (fun n hn => ?_) (fun n hn => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact (h₁ n hn g hg).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact (h₂ n hn g hg).symm
  have hYY : ⁅Y, Y⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp (hcen (hYN ha)) b hb).symm
  apply hY0
  rw [← Subgroup.isPerfect_iff.mp hYp, hYY]

end Comb

end CFSG.RankThree.PartTwo.Sec8.Hering418
