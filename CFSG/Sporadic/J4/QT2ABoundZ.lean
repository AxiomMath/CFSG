module

public import CFSG.Sporadic.J4.QT2ARad
public import CFSG.Sporadic.J4.QT2LocCntMain

public section

namespace CFSG.Sporadic.J4.QT2A

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

theorem card_le_Z1131
    (hM : MatFacts) (hC : Nat.card Cz = 21799895040) {S : Subgroup J}
    (hS : IsPGroup 2 S) (hSC : S ≤ Cz) {y : J} (hyC : y ∈ Cz) (hy3 : orderOf y = 3)
    (hSy : ∀ s ∈ S, s * y * s⁻¹ ∈ Subgroup.zpowers y) : Nat.card S ≤ 2 ^ 15 := by
  refine card_le_of_sylow_data Cz Qz Ycl (Ycl_le_Cz hM) Qz_le_Cz
    (fun l hl r hr => Qz_conj hl hr) (isPGroup_Qz hM hC) (card_Ycl hM) (k := 807403520)
    (by rw [hC]) (by norm_num) (m := 10395) (by rw [hC]; norm_num) (by norm_num) ?_ hS hSC hyC
    hy3 hSy
  intro y' hy' hy1
  obtain ⟨n, hn, rfl⟩ := Ycl_subset hM hy'
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hy1 yJ_zero
  exact ⟨fun j => el5 (qWordG qSub j), fun j => el5_qWordG_mem_Qz hM (by decide) j,
    conj_injective hM (Mx_yJ hM n) (conjDistinct_yEl (Set.mem_Iio.1 hn) hn0)⟩

theorem card_le_Z3
    (hF : J4Facts)
    (hC : Nat.card ↥(Subgroup.centralizer ({eta uJ 11 3} : Set J)) = 21799895040)
    {S : Subgroup J} (hS : IsPGroup 2 S)
    (hSC : S ≤ Subgroup.centralizer ({eta uJ 11 3} : Set J)) {y : J}
    (hyC : y ∈ Subgroup.centralizer ({eta uJ 11 3} : Set J)) (hy3 : orderOf y = 3)
    (hSy : ∀ s ∈ S, s * y * s⁻¹ ∈ Subgroup.zpowers y) : Nat.card S ≤ 2 ^ 15 := by
  obtain ⟨g, -, hg⟩ := QT2.exists_conj_eta_three_of_mem_zMasks QT2.mem_zMasks_1131
  have hCz : Nat.card Cz = 21799895040 := by
    have h := card_centralizer_conj g (eta uJ 11 3)
    rw [hg] at h
    rw [← hC]
    exact h
  obtain ⟨hS', hcard, hy3', hSy'⟩ := conj_data g hS hy3 hSy
  have hconjC : ∀ x ∈ Subgroup.centralizer ({eta uJ 11 3} : Set J), g * x * g⁻¹ ∈ Cz := by
    intro x hx
    rw [mem_Cz]
    have h1 : eta uJ 11 3 * x = x * eta uJ 11 3 :=
      Subgroup.mem_centralizer_iff.1 hx (eta uJ 11 3) rfl
    show eta uJ 11 1131 * (g * x * g⁻¹) = g * x * g⁻¹ * eta uJ 11 1131
    rw [← hg]
    calc g * eta uJ 11 3 * g⁻¹ * (g * x * g⁻¹) = g * (eta uJ 11 3 * x) * g⁻¹ := by group
      _ = g * (x * eta uJ 11 3) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * (g * eta uJ 11 3 * g⁻¹) := by group
  have key := card_le_Z1131 hF.mat hCz hS' (map_conj_le g hSC hconjC) (hconjC y hyC) hy3' hSy'
  rwa [hcard] at key

end CFSG.Sporadic.J4.QT2A
