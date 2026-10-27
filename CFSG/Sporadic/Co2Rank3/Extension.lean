module

public import CFSG.Sporadic.Co2Rank3.AutBound

public noncomputable section

namespace CFSG.Sporadic.Co2Rank3

open CFSG.Sporadic.Co2Cert CFSG.Certificates CFSG.Sporadic.Co2Rank3.Native MulAction

theorem ncard_co2N_36 :
    (orbit co2N (36 : Fin 2300)).ncard = 42 :=
  ncard_co2N (36, 42) (by simp [stabRoots]) (by norm_num)

theorem ncard_co2N_4 :
    (orbit co2N (4 : Fin 2300)).ncard = 336 :=
  ncard_co2N (4, 336) (by simp [stabRoots]) (by norm_num)

theorem ncard_co2N_5 :
    (orbit co2N (5 : Fin 2300)).ncard = 512 :=
  ncard_co2N (5, 512) (by simp [stabRoots]) (by norm_num)

theorem ncard_co2N_2 :
    (orbit co2N (2 : Fin 2300)).ncard = 512 :=
  ncard_co2N (2, 512) (by simp [stabRoots]) (by norm_num)

theorem ncard_co2N_1 :
    (orbit co2N (1 : Fin 2300)).ncard = 896 :=
  ncard_co2N (1, 896) (by simp [stabRoots]) (by norm_num)

theorem ncard_co2P01_4 :
    (orbit co2P01 (4 : Fin 2300)).ncard = 324 :=
  ncard_co2P01 (4, 324) (by simp [p01Roots]) (by norm_num)

theorem ncard_co2P01_3 :
    (orbit co2P01 (3 : Fin 2300)).ncard = 567 :=
  ncard_co2P01 (3, 567) (by simp [p01Roots]) (by norm_num)

theorem ncard_co2P01_2 :
    (orbit co2P01 (2 : Fin 2300)).ncard = 567 :=
  ncard_co2P01 (2, 567) (by simp [p01Roots]) (by norm_num)

theorem ncard_co2P01_8 :
    (orbit co2P01 (8 : Fin 2300)).ncard = 840 :=
  ncard_co2P01 (8, 840) (by simp [p01Roots]) (by norm_num)

theorem card_co2P0 :
    Nat.card co2P0 = 18393661440 := by
  rw [← card_co2P_stabilizer, card_inf_stabilizer_eq]
  rfl

section Extension

variable {H : Subgroup (Equiv.Perm (Fin 2300))}
  (htr : ∀ x : Fin 2300, ∃ h ∈ H, h • (0 : Fin 2300) = x)
  (hstab : H ⊓ stabilizer (Equiv.Perm (Fin 2300)) (0 : Fin 2300) = co2P0)
include htr hstab

theorem orbitalRel_suborbits_of_stabilizer :
    (∀ x y : Fin 2300, orbitalRel H 0 3 x y → orbitalRel H 0 3 y x) ∧
    (∀ y : Fin 2300, orbitalRel H 0 3 0 y ↔ y ∈ orbit co2P0 (3 : Fin 2300)) ∧
    (∀ y : Fin 2300, orbitalRel H 0 3 3 y ↔ y = 0 ∨ y ∈ orbit co2N (36 : Fin 2300) ∨
      y ∈ orbit co2N (4 : Fin 2300) ∨ y ∈ orbit co2N (2 : Fin 2300)) ∧
    (∀ y : Fin 2300, orbitalRel H 0 3 1 y ↔ y ∈ orbit co2P01 (4 : Fin 2300) ∨
      y ∈ orbit co2P01 (2 : Fin 2300)) := by
  have h := orbitalRel_co2_suborbits (H := H) (a := 0) (b := 3) (c := 1) htr
    (by rw [hstab]; exact co2P0_cover) (by rw [hstab]; exact ncard_co2Delta)
    (by rw [hstab]; exact ncard_co2Gamma) (N := co2N) (by rw [hstab]; exact co2N_le)
    (d₁ := 36) (d₂ := 4) (d₃ := 5) (d₄ := 2) (d₅ := 1) co2N_cover ncard_co2N_36 ncard_co2N_4
    ncard_co2N_5 ncard_co2N_2 ncard_co2N_1
    (by rw [hstab]; exact mem_co2Delta_of_lab co2Rank3Facts.loc36)
    (by rw [hstab]; exact mem_co2Delta_of_lab co2Rank3Facts.loc4)
    (by rw [hstab]; exact mem_co2Delta_of_lab co2Rank3Facts.loc5)
    (by rw [hstab]; exact mem_co2Gamma_of_lab co2Rank3Facts.loc2) (M := co2P01)
    (by rw [hstab]; exact le_rfl) (e₁ := 4) (e₂ := 3) (e₃ := 2) (e₄ := 8) co2P01_cover
    ncard_co2P01_4 ncard_co2P01_3 ncard_co2P01_2 ncard_co2P01_8
    (by rw [hstab]; exact mem_co2Delta_of_lab co2Rank3Facts.loc4)
    (by rw [hstab]; exact mem_orbit_self _)
    (by rw [hstab]; exact mem_co2Gamma_of_lab co2Rank3Facts.loc2)
  rw [hstab] at h
  exact h

omit htr hstab in
theorem orbitalRel_smul_left_iff {h : Equiv.Perm (Fin 2300)} (hh : h ∈ H) {x y : Fin 2300} :
    orbitalRel H 0 3 (h • x) y ↔ orbitalRel H 0 3 x (h⁻¹ • y) := by
  rw [← orbitalRel_smul_iff hh (x := x) (y := h⁻¹ • y), smul_inv_smul]

omit htr hstab in
theorem co2Graph_adj_smul_left
    {h : Equiv.Perm (Fin 2300)} (hh : h ∈ co2P) {x y : Fin 2300} :
    co2Graph.Adj (h • x) y ↔ co2Graph.Adj x (h⁻¹ • y) := by
  rw [co2Graph_adj, co2Graph_adj, ← orbitalRel_smul_iff hh (x := x) (y := h⁻¹ • y),
    smul_inv_smul]

theorem orbitalRel_iff_co2Graph_adj
    (x y : Fin 2300) :
    orbitalRel H 0 3 x y ↔ co2Graph.Adj x y := by
  obtain ⟨-, hH0, hH3, hH1⟩ := orbitalRel_suborbits_of_stabilizer htr hstab
  obtain ⟨-, hP0, hP3, hP1⟩ := orbitalRel_suborbits_of_stabilizer co2P_htr rfl
  have hle : co2P0 ≤ H := hstab ▸ inf_le_left
  rcases co2P0_cover x with rfl | hx | hx
  · rw [hH0, co2Graph_adj, hP0]
  · obtain ⟨p, hp, rfl⟩ := mem_orbit_subgroup_iff.1 hx
    rw [orbitalRel_smul_left_iff (hle hp), co2Graph_adj_smul_left hp.1, hH3,
      co2Graph_adj, hP3]
  · obtain ⟨p, hp, rfl⟩ := mem_orbit_subgroup_iff.1 hx
    rw [orbitalRel_smul_left_iff (hle hp), co2Graph_adj_smul_left hp.1, hH1,
      co2Graph_adj, hP1]

theorem le_co2Aut_of_stabilizer :
    H ≤ co2Aut := fun h hh x y => by
  rw [← orbitalRel_iff_co2Graph_adj htr hstab, ← orbitalRel_iff_co2Graph_adj htr hstab]
  exact orbitalRel_smul_iff hh

theorem card_of_stabilizer :
    Nat.card H = 42305421312000 := by
  have h1 := (stabilizer H (0 : Fin 2300)).index_mul_card
  rw [index_stabilizer] at h1
  have horb : orbit H (0 : Fin 2300) = Set.univ :=
    Set.eq_univ_of_forall fun x => mem_orbit_subgroup_iff.2 (htr x)
  rw [horb, Set.ncard_univ, Nat.card_fin, card_inf_stabilizer_eq, hstab, card_co2P0] at h1
  rw [← h1]

theorem eq_co2P_of_stabilizer :
    H = co2P := by
  have hle : H ≤ co2P := co2Aut_eq ▸ le_co2Aut_of_stabilizer htr hstab
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_co2P, card_of_stabilizer htr hstab])

end Extension

end CFSG.Sporadic.Co2Rank3
