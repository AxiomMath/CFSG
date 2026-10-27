module

public import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.Quasithin.SteinbergBMPerfectSubnormalSignalizer
import CFSG.RankThree.LocalRank.ThetaCoreQuotients

public section

namespace CFSG.RankThree.PartOne.HyperplaneObstruction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open scoped commutatorElement

theorem commutator_two_group_le_theta_of_perfect_cover_component {H : Type*} [Group H] [Finite H]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L K Y : Subgroup H} (hL : L ∈ thetaComponents p H)
    (hKL : K ≤ L) (hK : ⁅K, K⁆ = K) (hLK : L ≤ K ⊔ aschbacherSolvableCore p H)
    (hY : IsPGroup 2 Y) (hKY : K ≤ normalizer (Y : Set H)) :
    ⁅K, Y⁆ ≤ aschbacherSolvableCore p H := by
  obtain ⟨hNs, hNchar, hNp, -⟩ := solvable_prime_complement_core_characterization (H := H) hp
  set N := aschbacherSolvableCore p H with hN
  have : N.Normal := inferInstance
  set π := QuotientGroup.mk' N with hπ
  have hNker : N.map π = ⊥ := by rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk']
  have hJc := isComponent_map_of_mem_thetaComponents hp hL
  have hKJ : K.map π = L.map π := by
    refine le_antisymm (Subgroup.map_mono hKL) ?_
    calc L.map π ≤ (K ⊔ N).map π := Subgroup.map_mono hLK
      _ = K.map π ⊔ N.map π := Subgroup.map_sup _ _ _
      _ = K.map π := by rw [hNker, sup_bot_eq]
  have hJsub : (K.map π).IsSubnormal := hKJ ▸ hJc.2
  have hJperf : ⁅K.map π, K.map π⁆ = K.map π := by rw [← Subgroup.map_commutator, hK]
  have hR2 : IsPGroup 2 (Y.map π) := hY.map π
  have hJR : K.map π ≤ normalizer ((Y.map π : Subgroup (H ⧸ N)) : Set (H ⧸ N)) := by
    rintro _ ⟨k, hk, rfl⟩
    exact Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π (hKY hk))
  obtain ⟨-, hsig⟩ := CFSG.Quasithin.SteinbergBM.perfect_subnormal_p_signalizer_action
    Nat.prime_two hJperf hJsub hR2 hJR
  have hθX : aschbacherSolvableCore p (H ⧸ N) = ⊥ :=
    (solvable_prime_complement_core_quotient_centralizers (G := H) hp N hNs hNp).2.2.1
  have hθJ : aschbacherSolvableCore p (K.map π) = ⊥ := by
    rw [aschbacherSolvableCore_eq_subgroupOf hp hJsub, hθX, Subgroup.bot_subgroupOf]
  have hO2 : inSubgroup (pCore 2) (K.map π) = ⊥ := by
    have hle := (solvable_prime_complement_core_characterization (H := K.map π) hp).2.2.2.2.2.2
      2 Nat.prime_two (Ne.symm hp2)
    rw [hθJ, le_bot_iff] at hle
    rw [inSubgroup, hle, Subgroup.map_bot]
  rw [hO2, le_bot_iff, ← Subgroup.map_commutator, Subgroup.map_eq_bot_iff] at hsig
  exact hsig.trans (QuotientGroup.ker_mk' N).le

theorem commutator_two_group_le_theta_centralizer {G : Type*} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {d : G} {L K Y : Subgroup G} (hL : L ∈ thetaComponentsAt p d)
    (hKL : K ≤ L) (hK : ⁅K, K⁆ = K)
    (hLK : L ≤ K ⊔ inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({d} : Set G)))
    (hY : IsPGroup 2 Y) (hYd : Y ≤ Subgroup.centralizer ({d} : Set G))
    (hKY : K ≤ normalizer (Y : Set G)) :
    ⁅K, Y⁆ ≤ inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({d} : Set G)) := by
  set C := Subgroup.centralizer ({d} : Set G) with hC
  obtain ⟨hLC, hL'⟩ := mem_thetaComponentsAt_iff.mp hL
  have hKC : K ≤ C := hKL.trans hLC
  have hNC : inSubgroup (aschbacherSolvableCore p) C ≤ C := Subgroup.map_subtype_le _
  have hNsub : (inSubgroup (aschbacherSolvableCore p) C).subgroupOf C =
      aschbacherSolvableCore p C := Subgroup.comap_map_eq_self_of_injective C.subtype_injective _
  have hmain := commutator_two_group_le_theta_of_perfect_cover_component (H := C) hp hp2
    (L := L.subgroupOf C) (K := K.subgroupOf C) (Y := Y.subgroupOf C) hL'
    (fun x hx => Subgroup.mem_subgroupOf.mpr (hKL (Subgroup.mem_subgroupOf.mp hx)))
    (by
      apply Subgroup.map_injective C.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKC, hK])
    (by
      rw [← hNsub, ← Subgroup.subgroupOf_sup hKC hNC]
      exact fun x hx => hLK (Subgroup.mem_subgroupOf.mp hx))
    hY.comap_subtype
    (by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_normalizer_iff.mp (hKY (Subgroup.mem_subgroupOf.mp hx)) (y : G))
  have h2 := Subgroup.map_mono (f := C.subtype) hmain
  rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKC,
    Subgroup.map_subgroupOf_eq_of_le hYd] at h2

end CFSG.RankThree.PartOne.HyperplaneObstruction
