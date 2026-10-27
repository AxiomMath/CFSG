module

public import Mathlib.Algebra.Group.Subgroup.Lattice

public section

namespace CFSG.Quasithin.Background.Harris.OrdinaryProofs

variable {X : Type} [Group X]

theorem exists_mul_mem_of_sup_eq_top {K T : Subgroup X} [K.Normal] (hsup : K ⊔ T = ⊤)
    (x : X) : ∃ k ∈ K, ∃ t ∈ T, k * t = x := by
  have hx : x ∈ K ⊔ T := by
    rw [hsup]
    exact Subgroup.mem_top x
  exact Subgroup.mem_sup_of_normal_left.mp hx

theorem maximal_of_inf_maximal {K T M : Subgroup X} [K.Normal] (hsup : K ⊔ T = ⊤)
    (hmax : ∀ B : Subgroup X, T ⊓ K ≤ B → B ≤ M ⊓ K → B = T ⊓ K ∨ B = M ⊓ K) :
    ∀ B : Subgroup X, T ≤ B → B ≤ M → B = T ∨ B = M := by
  intro B hTB hBM
  rcases hmax (B ⊓ K) (fun x hx => ⟨hTB hx.1, hx.2⟩) (fun x hx => ⟨hBM hx.1, hx.2⟩) with h | h
  · left
    apply le_antisymm _ hTB
    intro b hb
    obtain ⟨k, hk, t, ht, hkt⟩ := exists_mul_mem_of_sup_eq_top hsup b
    have hkB : k ∈ B := by
      have hk' : k = b * t⁻¹ := eq_mul_inv_of_mul_eq hkt
      rw [hk']
      exact B.mul_mem hb (B.inv_mem (hTB ht))
    have hkTK : k ∈ T ⊓ K := by
      rw [← h]
      exact ⟨hkB, hk⟩
    rw [← hkt]
    exact T.mul_mem hkTK.1 ht
  · right
    apply le_antisymm hBM
    intro m hm
    obtain ⟨k, hk, t, ht, hkt⟩ := exists_mul_mem_of_sup_eq_top hsup m
    have htM : t ∈ M := hBM (hTB ht)
    have hkMK : k ∈ M ⊓ K := by
      refine ⟨?_, hk⟩
      have hk' : k = m * t⁻¹ := eq_mul_inv_of_mul_eq hkt
      rw [hk']
      exact M.mul_mem hm (M.inv_mem htM)
    have hkB : k ∈ B := by
      have : k ∈ B ⊓ K := by
        rw [h]
        exact hkMK
      exact this.1
    rw [← hkt]
    exact B.mul_mem hkB (hTB ht)

end CFSG.Quasithin.Background.Harris.OrdinaryProofs

end
