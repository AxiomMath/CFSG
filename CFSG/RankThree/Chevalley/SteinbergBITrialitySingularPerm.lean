module

public import CFSG.RankThree.Chevalley.SteinbergBID4A2CharStab

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6

@[expose] def a2Rot : Equiv.Perm (Fin 3) := finRotate 3

theorem a2_rotation_check : ∀ x ∈ d4Sigma0List, ∀ y ∈ d4Sigma0List, x + y ∈ d4Sigma0List →
    x 0 • x + x 2 • y + x + Pi.single 0 1 = 0 → y 0 • x + y 2 • y + y + Pi.single 2 1 = 0 →
      (∀ i j : Fin 3, chainRoot d4ChainA2 i j 0 • x + chainRoot d4ChainA2 i j 2 • y =
          chainRoot d4ChainA2 (a2Rot i) (a2Rot j)) ∨
        ∀ i j : Fin 3, chainRoot d4ChainA2 i j 0 • x + chainRoot d4ChainA2 i j 2 • y =
          chainRoot d4ChainA2 (a2Rot.symm i) (a2Rot.symm j) := by
  decide +kernel

theorem eq_of_mem_d4Sigma0List : ∀ β ∈ d4Sigma0List,
    β = β 0 • (Pi.single 0 1 : Fin Tag.D4.rank → ℤ) + β 2 • Pi.single 2 1 := by
  decide +kernel

theorem chainRootA2_eq_smul_add (i j : Fin 3) :
    chainRoot d4ChainA2 i j = chainRoot d4ChainA2 i j 0 • (Pi.single 0 1 : Fin Tag.D4.rank → ℤ) +
      chainRoot d4ChainA2 i j 2 • Pi.single 2 1 := by
  revert i j
  decide +kernel

theorem single_zero_mem_d4Sigma0List : (Pi.single 0 1 : Fin Tag.D4.rank → ℤ) ∈ d4Sigma0List := by
  decide

theorem single_two_mem_d4Sigma0List : (Pi.single 2 1 : Fin Tag.D4.rank → ℤ) ∈ d4Sigma0List := by
  decide

theorem add_single_mem_d4Sigma0List :
    (Pi.single 0 1 + Pi.single 2 1 : Fin Tag.D4.rank → ℤ) ∈ d4Sigma0List := by
  decide

theorem neg_mem_d4Sigma0List : ∀ β ∈ d4Sigma0List, -β ∈ d4Sigma0List := by
  decide +kernel

theorem exists_perm_of_sq_add_add_one (L : (Fin Tag.D4.rank → ℤ) →+ (Fin Tag.D4.rank → ℤ))
    (hL : ∀ β ∈ d4Sigma0List, L β ∈ d4Sigma0List)
    (hquad : ∀ β ∈ d4Sigma0List, L (L β) + L β + β = 0) :
    ∃ π : Equiv.Perm (Fin 3), ∀ i j : Fin 3,
      L (chainRoot d4ChainA2 i j) = chainRoot d4ChainA2 (π i) (π j) := by
  have hx := hL _ single_zero_mem_d4Sigma0List
  have hy := hL _ single_two_mem_d4Sigma0List
  have hxy : L (Pi.single 0 1) + L (Pi.single 2 1) ∈ d4Sigma0List := by
    rw [← map_add]
    exact hL _ add_single_mem_d4Sigma0List
  have hLsum : ∀ β : Fin Tag.D4.rank → ℤ,
      β = β 0 • (Pi.single 0 1 : Fin Tag.D4.rank → ℤ) + β 2 • Pi.single 2 1 →
      L β = β 0 • L (Pi.single 0 1) + β 2 • L (Pi.single 2 1) := fun β hβ => by
    conv_lhs => rw [hβ]
    rw [map_add, map_zsmul, map_zsmul]
  have h0 := hquad _ single_zero_mem_d4Sigma0List
  have h2 := hquad _ single_two_mem_d4Sigma0List
  rw [hLsum _ (eq_of_mem_d4Sigma0List _ hx)] at h0
  rw [hLsum _ (eq_of_mem_d4Sigma0List _ hy)] at h2
  rcases a2_rotation_check _ hx _ hy hxy h0 h2 with h | h
  · exact ⟨a2Rot, fun i j => by rw [hLsum _ (chainRootA2_eq_smul_add i j), h]⟩
  · exact ⟨a2Rot.symm, fun i j => by rw [hLsum _ (chainRootA2_eq_smul_add i j), h]⟩

theorem exists_perm_of_sq_sub_add_one (L : (Fin Tag.D4.rank → ℤ) →+ (Fin Tag.D4.rank → ℤ))
    (hL : ∀ β ∈ d4Sigma0List, L β ∈ d4Sigma0List)
    (hquad : ∀ β ∈ d4Sigma0List, L (L β) - L β + β = 0) :
    ∃ π : Equiv.Perm (Fin 3), ∀ i j : Fin 3,
      L (chainRoot d4ChainA2 i j) = chainRoot d4ChainA2 (π j) (π i) := by
  obtain ⟨π, hπ⟩ := exists_perm_of_sq_add_add_one (-L)
    (fun β hβ => by rw [AddMonoidHom.neg_apply]; exact neg_mem_d4Sigma0List _ (hL β hβ))
    (fun β hβ => by
      simp only [AddMonoidHom.neg_apply, map_neg, neg_neg]
      rw [← hquad β hβ]
      abel)
  refine ⟨π, fun i j => ?_⟩
  have h := hπ i j
  rw [AddMonoidHom.neg_apply, neg_eq_iff_eq_neg] at h
  rw [h, chainRoot_swap, neg_neg]

end CFSG.RankThree.Chevalley
