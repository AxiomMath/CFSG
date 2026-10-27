module

public import CFSG.LocalAnalysis.StandardType.FS81.D6Cent
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly
open scoped commutatorElement Pointwise

theorem map_conj_mul {G : Type} [Group G] (L : Subgroup G) (a b : G) :
    (L.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      L.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem zpowers_le_normalizer_of_le_centralizer {G : Type} [Group G] {x : G} {L : Subgroup G}
    (hL : L ≤ Subgroup.centralizer ({x} : Set G)) :
    Subgroup.zpowers x ≤ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro h hh l hl
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hh
  have hcomm : Commute l x := Subgroup.mem_centralizer_singleton_iff.mp (hL hl)
  have hxl : Commute (x ^ m) l := (hcomm.symm).zpow_left m
  rw [← hm, hxl.eq]
  simpa using hl

theorem commutator_sup_zpowers_le_of_centralizer {G : Type} [Group G] {x : G} {L : Subgroup G}
    (hL : L ≤ Subgroup.centralizer ({x} : Set G)) :
    ⁅Subgroup.zpowers x ⊔ L, Subgroup.zpowers x ⊔ L⁆ ≤ L := by
  let K : Subgroup G := Subgroup.zpowers x ⊔ L
  have hzpN : Subgroup.zpowers x ≤ Subgroup.normalizer (L : Set G) :=
    zpowers_le_normalizer_of_le_centralizer hL
  haveI hNnormal : (L.subgroupOf K).Normal :=
    Subgroup.normal_subgroupOf_sup_of_le_normalizer (H := Subgroup.zpowers x) (N := L) hzpN
  have htop : L.subgroupOf K ⊔ (Subgroup.zpowers x).subgroupOf K = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := L) (A' := Subgroup.zpowers x) (B := K)
      le_sup_right le_sup_left, sup_comm, Subgroup.subgroupOf_self]
  haveI : IsMulCommutative ((Subgroup.zpowers x).subgroupOf K) := inferInstance
  have hcomm : _root_.commutator ↥K ≤ L.subgroupOf K :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top (N := L.subgroupOf K)
      (H := (Subgroup.zpowers x).subgroupOf K) htop inferInstance
  calc ⁅K, K⁆ = (_root_.commutator ↥K).map K.subtype :=
        (Subgroup.map_subtype_commutator K).symm
    _ ≤ (L.subgroupOf K).map K.subtype := Subgroup.map_mono hcomm
    _ = L := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left]
        exact le_sup_right

theorem isPerfect_of_isSimpleGroup_of_center_eq_bot {G : Type} [Group G] [IsSimpleGroup G]
    (hZ : Subgroup.center G = ⊥) [Nontrivial G] : Group.IsPerfect G := by
  rw [Group.isPerfect_def]
  haveI : (commutator G).Normal := by
    rw [show commutator G = ⁅(⊤ : Subgroup G), ⊤⁆ from rfl]
    infer_instance
  rcases Subgroup.Normal.eq_bot_or_eq_top (commutator G) with hbot | htop
  · exfalso
    have hcomm : IsMulCommutative G := (commutator_eq_bot_iff G).mp hbot
    have hctop : Subgroup.center G = ⊤ := Subgroup.center_eq_top
    exact bot_ne_top (hZ.symm.trans hctop)
  · exact htop

theorem le_closure_cube_of_simple {G : Type} [Group G] [Finite G] (P : Subgroup G)
    [IsSimpleGroup P] (h3 : 3 ∣ Nat.card P) :
    P ≤ Subgroup.closure {y : G | y ∈ P ∧ y ^ 3 = 1} := by
  let T : Set G := {y : G | y ∈ P ∧ y ^ 3 = 1}
  let S : Subgroup G := Subgroup.closure T
  have hSP : S ≤ P := (Subgroup.closure_le _).mpr (fun y hy => hy.1)
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hne : S.subgroupOf P ≠ ⊥ := by
    obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' (G := ↥P) 3 h3
    intro hbot
    have hy3 : (y : G) ^ 3 = 1 := by
      have hord : orderOf (y : G) = 3 := by
        rw [Subgroup.orderOf_coe, hyord]
      rw [← hord]
      exact pow_orderOf_eq_one _
    have hyS : (y : G) ∈ S := Subgroup.subset_closure ⟨y.2, hy3⟩
    have hySub : y ∈ S.subgroupOf P := by
      rwa [Subgroup.mem_subgroupOf]
    rw [hbot] at hySub
    have hy1 : y = 1 := Subgroup.mem_bot.mp hySub
    rw [hy1] at hyord
    simp at hyord
  have hnorm : (S.subgroupOf P).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hSP]
    intro h k hh hk
    induction hh using Subgroup.closure_induction with
    | mem y hy =>
        refine Subgroup.subset_closure ⟨P.mul_mem (P.mul_mem hk hy.1) (P.inv_mem hk), ?_⟩
        rw [conj_pow, hy.2]
        group
    | one => simpa using S.one_mem
    | mul x y hx hy ihx ihy =>
        rw [show k * (x * y) * k⁻¹ = (k * x * k⁻¹) * (k * y * k⁻¹) by group]
        exact S.mul_mem ihx ihy
    | inv x hx ih =>
        rw [show k * x⁻¹ * k⁻¹ = (k * x * k⁻¹)⁻¹ by group]
        exact S.inv_mem ih
  haveI : (S.subgroupOf P).Normal := hnorm
  rcases Subgroup.Normal.eq_bot_or_eq_top (S.subgroupOf P) with hbot | htop
  · exact absurd hbot hne
  · exact Subgroup.subgroupOf_eq_top.mp htop

end CFSG.StandardType.FrameRoute.FS81

end
