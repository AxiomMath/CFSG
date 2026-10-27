module

public import CFSG.RankThree.PartOne.N143.ExistsZ
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
public import CFSG.RankThree.PartOne.N143.GroupLemmas

public section

namespace CFSG.RankThree.PartOne.N143

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G}

@[expose] noncomputable def Aline (A J : Subgroup G) (Ps : Subgroup (MulAut A)) (zs : MulAut A) :
    Subgroup (MulAut A) :=
  (torusImage A J ⊓ Ps) ⊔ Subgroup.zpowers zs

omit [Finite G] in
theorem Aline_le_Ps {J : Subgroup G} {Ps : Subgroup (MulAut A)} {zs : MulAut A} (hz : zs ∈ Ps) :
    Aline A J Ps zs ≤ Ps :=
  sup_le inf_le_right ((Subgroup.zpowers_le).2 hz)

theorem JGood.card_inf_Ps {c : G} {J : Subgroup G} (h : JGood p A c J) {Ps : Subgroup (MulAut A)}
    {zs : MulAut A} (hspec : HessianSpec p A Ps zs) : Nat.card (torusImage A J ⊓ Ps : Subgroup _) = 3 := by
  obtain ⟨e⟩ := h.weyl
  have hle : (torusImage A J ⊓ Ps : Subgroup (MulAut A)) ≤ torusImage A J := inf_le_left
  rw [← card_subgroupOf_of_le hle]
  have heq : Nat.card ((torusImage A J ⊓ Ps : Subgroup (MulAut A)).subgroupOf (torusImage A J)) =
      Nat.card {σ : Equiv.Perm (Fin 3) // σ ^ 3 = 1} := by
    refine Nat.card_congr ((e.toEquiv.subtypeEquiv fun a => ?_))
    show (a : MulAut A) ∈ (torusImage A J ⊓ Ps : Subgroup (MulAut A)) ↔ (e a) ^ 3 = 1
    constructor
    · intro ha
      have h3 : (a : MulAut A) ^ 3 = 1 := (hspec.mem_P _ (h.torusImage_le a.2)).1 ha.2
      rw [← map_pow]
      convert map_one e
      exact Subtype.ext h3
    · intro h3
      have h3' : (a : MulAut A) ^ 3 = 1 := by
        have : a ^ 3 = 1 := e.injective (by rw [map_pow, h3, map_one])
        exact congrArg Subtype.val this
      exact ⟨a.2, (hspec.mem_P _ (h.torusImage_le a.2)).2 h3'⟩
  rw [heq]
  have : Fintype.card {σ : Equiv.Perm (Fin 3) // σ ^ 3 = 1} = 3 := by decide
  rw [Nat.card_eq_fintype_card, this]

theorem JGood.disjoint_zpowers {c : G} {J : Subgroup G} (h : JGood p A c J) {Ps : Subgroup (MulAut A)}
    {zs : MulAut A} (hspec : HessianSpec p A Ps zs) :
    Disjoint (torusImage A J ⊓ Ps : Subgroup (MulAut A)) (Subgroup.zpowers zs) := by
  rw [Subgroup.disjoint_def]
  intro y hy hyz
  obtain ⟨s, hs, hsJ⟩ := h.exists_reflection
  have hy3 : y ^ 3 = 1 := (hspec.mem_P _ (h.torusImage_le hy.1)).1 hy.2
  have hinv := h.reflection_inv hs hsJ hy.1 hy3
  have hcomm : s * y = y * s := by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hyz
    rw [← hi]
    exact (Commute.zpow_left (hspec.z_central s : Commute zs s) i).eq.symm
  have h2 : y = y⁻¹ := by rw [← hinv, mul_inv_eq_iff_eq_mul.2 hcomm]
  have h3 : y * y = 1 := by
    rw [eq_inv_iff_mul_eq_one] at h2
    exact h2
  calc y = y ^ 3 * (y * y)⁻¹ := by group
    _ = 1 := by rw [hy3, h3]; simp

theorem JGood.card_Aline {c : G} {J : Subgroup G} (h : JGood p A c J) {Ps : Subgroup (MulAut A)}
    {zs : MulAut A} (hspec : HessianSpec p A Ps zs) : Nat.card (Aline A J Ps zs) = 9 := by
  have hcomm : ∀ k ∈ (torusImage A J ⊓ Ps : Subgroup (MulAut A)), ∀ l ∈ Subgroup.zpowers zs,
      k * l = l * k := by
    intro k _ l hl
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hl
    exact (Commute.zpow_left (hspec.z_central k : Commute zs k) i).eq.symm
  have hcard := Torsion37.card_sup_of_commute_disjoint hcomm (h.disjoint_zpowers hspec)
  have hzc : Nat.card (Subgroup.zpowers zs) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hspec.z_cube hspec.z_ne
  rw [h.card_inf_Ps hspec, hzc] at hcard
  exact hcard

omit [Finite G] in
theorem mem_Aline {J : Subgroup G} {Ps : Subgroup (MulAut A)} {zs : MulAut A}
    (hspec : HessianSpec p A Ps zs) {y : MulAut A} (hy : y ∈ Aline A J Ps zs) :
    ∃ j ∈ (torusImage A J ⊓ Ps : Subgroup (MulAut A)), ∃ n : ℕ, y = j * zs ^ n := by
  have hcomm : ∀ k ∈ (torusImage A J ⊓ Ps : Subgroup (MulAut A)), ∀ l ∈ Subgroup.zpowers zs,
      k * l = l * k := by
    intro k _ l hl
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hl
    exact (Commute.zpow_left (hspec.z_central k : Commute zs k) i).eq.symm
  obtain ⟨j, hj, l, hl, rfl⟩ := Torsion37.exists_mul_of_mem_sup_of_commute hcomm hy
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hl
  refine ⟨j, hj, (i % 3).toNat, ?_⟩
  have hord : orderOf zs = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime hspec.z_cube hspec.z_ne
  have h1 : zs ^ i = zs ^ (i % (orderOf zs : ℤ)) := (zpow_mod_orderOf zs i).symm
  rw [h1, hord]
  have hnn : 0 ≤ i % ((3 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
  rw [← zpow_natCast, Int.toNat_of_nonneg (by simpa using hnn)]
  simp

theorem exists_Aline_of_mem {c : G} {L : Subgroup G} (hctx : HessCtx p A c L) {Ps : Subgroup (MulAut A)} {zs : MulAut A}
    (hspec : HessianSpec p A Ps zs) (hpair : KF134Pair)
    {y : MulAut A} (hyP : y ∈ Ps) (hyZ : y ∉ Subgroup.zpowers zs) :
    ∃ J ∈ thetaCompZeroStarE p A, y ∈ Aline A J Ps zs := by
  have hy3 : y ^ 3 = 1 := (hspec.mem_P y (hspec.P_le hyP)).1 hyP
  obtain ⟨s, hs, t, ht, hst, hy⟩ := hspec.prod_refl y (hspec.P_le hyP) hy3 hyZ
  have hnc : s * t ≠ t * s := hctx.hess s hs t ht hst
  obtain ⟨I, hI, hsI, htI⟩ := hpair G p A c L A hctx.hyp hctx.facts12 hctx.facts13 hctx.notFive
    (Or.inr ⟨rfl, hctx.allL3⟩) s hs t ht hnc
  refine ⟨I, hI, Subgroup.mem_sup_left ⟨?_, hyP⟩⟩
  rcases hy with rfl | rfl
  · exact Subgroup.mul_mem _ hsI htI
  · exact Subgroup.mul_mem _ htI hsI

end CFSG.RankThree.PartOne.N143
