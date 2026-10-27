module

public import CFSG.RankThree.PartOne.KC.PlaneReduction

public section

namespace CFSG.RankThree.PartOne.KGD

open Subgroup CFSG CFSG.RankThree.PartOne CFSG.RankThree.LocalRank
open scoped Pointwise

theorem autThetaT_eq_map_thetaT {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    (B : Subgroup M) (A : Subgroup B) {t : B} (htA : t ∈ A) (ht1 : t ≠ 1) :
    autThetaT p B (A.map B.subtype) = (thetaT p A).map B.subtype := by
  refine le_antisymm (fun x hx => ?_) (map_subtype_thetaT_le hp B A)
  simp only [autThetaT, Subgroup.mem_iInf] at hx
  have hxt := hx (t : M) (Subgroup.mem_map_of_mem _ htA) (fun h => ht1 (Subtype.ext h))
  rw [← map_subtype_theta_centralizer hp B t] at hxt
  obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 hxt
  refine Subgroup.mem_map_of_mem _ ?_
  simp only [thetaT, Subgroup.mem_iInf]
  intro b hbA hb1
  have h1 := hx (b : M) (Subgroup.mem_map_of_mem _ hbA) (fun h => hb1 (Subtype.ext h))
  rw [← map_subtype_theta_centralizer hp B b] at h1
  obtain ⟨y', hy', hyy'⟩ := Subgroup.mem_map.1 h1
  have hy : y' = y := Subtype.ext hyy'
  rwa [hy] at hy'

theorem autPlaneProduct_eq_map {M : Type*} [Group M] [Finite M] {p : ℕ} (hp : p.Prime)
    (B : Subgroup M) (E : Subgroup B) {t : B} (htE : t ∈ E) (ht1 : t ≠ 1) :
    autPlaneProduct p B (E.map B.subtype) (t : M) =
      (⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set B)), E⁆ ⊔
        thetaT p E).map B.subtype := by
  rw [autPlaneProduct, Subgroup.map_sup, Subgroup.map_commutator,
    map_subtype_theta_centralizer hp B t, autThetaT_eq_map_thetaT hp B E htE ht1]

theorem planeLocalCoreOdd_of_subgroup_form {T : Type*} [Group T] [Finite T] {p : ℕ}
    (hp : p.Prime)
    (h : ∀ B : Subgroup (MulAut T), (MulAut.conj : T →* MulAut T).range ≤ B →
      ∀ E : Subgroup B, IsElementaryAbelian p E → Nat.card E = p ^ 2 →
        ∀ t ∈ E, t ≠ 1 →
          Odd (Nat.card ↥(⁅inSubgroup (aschbacherSolvableCore p) (centralizer ({t} : Set B)), E⁆ ⊔
            thetaT p E))) :
    PlaneLocalCoreOdd p T := by
  intro B hB A hAB hA hAcard t htA ht1
  have : Fact p.Prime := ⟨hp⟩
  have := hA
  have hE : IsElementaryAbelian p (A.subgroupOf B) := IsElementaryAbelian.subgroupOf hAB
  have hEcard : Nat.card (A.subgroupOf B) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAB).toEquiv, hAcard]
  have ht'E : (⟨t, hAB htA⟩ : B) ∈ A.subgroupOf B := Subgroup.mem_subgroupOf.2 htA
  have ht'1 : (⟨t, hAB htA⟩ : B) ≠ 1 := fun h => ht1 (congrArg Subtype.val h)
  have hodd := h B hB (A.subgroupOf B) hE hEcard _ ht'E ht'1
  have hAE : (A.subgroupOf B).map B.subtype = A := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hAB]
  have heq : autPlaneProduct p B A t = (⁅inSubgroup (aschbacherSolvableCore p)
      (centralizer ({(⟨t, hAB htA⟩ : B)} : Set B)), A.subgroupOf B⁆ ⊔
        thetaT p (A.subgroupOf B)).map B.subtype := by
    have := autPlaneProduct_eq_map hp B (A.subgroupOf B) ht'E ht'1
    rwa [hAE] at this
  rw [heq, Subgroup.card_map_of_injective B.subtype_injective]
  exact hodd.not_two_dvd_nat

end CFSG.RankThree.PartOne.KGD
