module

public import CFSG.RankThree.PartTwo.Sec11.Item1120V0BarSylow

public section

namespace CFSG.RankThree.PartTwo.Sec11

namespace Item1120V0Bar

theorem card_le_three_pow_of_isPGroup {G : Type*} [Group G] [Finite G] {P : Subgroup G}
    (hP : IsPGroup 3 P) : Nat.card P ≤ 3 ^ (Nat.card G).factorization 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  calc Nat.card P ≤ Nat.card (Q : Subgroup G) := Subgroup.card_le_of_le hQ
    _ = 3 ^ (Nat.card G).factorization 3 := Sylow.card_eq_multiplicity Q

theorem orderOf_mul_le_card_closure_pair {G : Type*} [Group G] [Finite G] {b ξ : G}
    (hbξ : b * ξ = ξ * b) (hdisj : Subgroup.zpowers b ⊓ Subgroup.zpowers ξ = ⊥) :
    orderOf b * orderOf ξ ≤ Nat.card (Subgroup.closure ({b, ξ} : Set G)) := by
  have hbmem : b ∈ Subgroup.closure ({b, ξ} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hξmem : ξ ∈ Subgroup.closure ({b, ξ} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  let f : Fin (orderOf b) × Fin (orderOf ξ) → Subgroup.closure ({b, ξ} : Set G) :=
    fun p => ⟨b ^ (p.1 : ℕ) * ξ ^ (p.2 : ℕ),
      (Subgroup.closure ({b, ξ} : Set G)).mul_mem (pow_mem hbmem _) (pow_mem hξmem _)⟩
  have hf : Function.Injective f := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ hij
    have h : b ^ (i : ℕ) * ξ ^ (j : ℕ) = b ^ (i' : ℕ) * ξ ^ (j' : ℕ) :=
      congrArg Subtype.val hij
    have hL : (b ^ (i' : ℕ))⁻¹ * b ^ (i : ℕ) = ξ ^ (j' : ℕ) * (ξ ^ (j : ℕ))⁻¹ := by
      rw [eq_mul_inv_of_mul_eq h]
      group
    have h1 : (b ^ (i' : ℕ))⁻¹ * b ^ (i : ℕ) ∈ (⊥ : Subgroup G) := by
      rw [← hdisj, Subgroup.mem_inf]
      constructor
      · exact (Subgroup.zpowers b).mul_mem
          ((Subgroup.zpowers b).inv_mem (pow_mem (Subgroup.mem_zpowers b) _))
          (pow_mem (Subgroup.mem_zpowers b) _)
      · rw [hL]
        exact (Subgroup.zpowers ξ).mul_mem (pow_mem (Subgroup.mem_zpowers ξ) _)
          ((Subgroup.zpowers ξ).inv_mem (pow_mem (Subgroup.mem_zpowers ξ) _))
    rw [Subgroup.mem_bot, inv_mul_eq_one] at h1
    have hbeq : b ^ (i : ℕ) = b ^ (i' : ℕ) := h1.symm
    have h2 : b ^ (i : ℕ) * ξ ^ (j : ℕ) = b ^ (i : ℕ) * ξ ^ (j' : ℕ) := by
      rw [h, hbeq]
    have hξeq : ξ ^ (j : ℕ) = ξ ^ (j' : ℕ) := mul_left_cancel h2
    have hi : (i : ℕ) = (i' : ℕ) := by
      have hm := pow_eq_pow_iff_modEq.1 hbeq
      unfold Nat.ModEq at hm
      rwa [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt i'.isLt] at hm
    have hj : (j : ℕ) = (j' : ℕ) := by
      have hm := pow_eq_pow_iff_modEq.1 hξeq
      unfold Nat.ModEq at hm
      rwa [Nat.mod_eq_of_lt j.isLt, Nat.mod_eq_of_lt j'.isLt] at hm
    exact Prod.ext (Fin.ext hi) (Fin.ext hj)
  have hcard := Nat.card_le_card_of_injective f hf
  simpa [Nat.card_prod] using hcard

theorem conj_mem_closure_pair_of_card {G : Type*} [Group G] [Finite G] {b ξ γ : G}
    (hP : IsPGroup 3 (Subgroup.closure ({b, ξ, γ} : Set G)))
    (hbξ : b * ξ = ξ * b) (hdisj : Subgroup.zpowers b ⊓ Subgroup.zpowers ξ = ⊥)
    (hcard : 3 ^ (Nat.card G).factorization 3 ≤ 3 * (orderOf b * orderOf ξ)) :
    γ * b * γ⁻¹ ∈ Subgroup.closure ({b, ξ} : Set G) ∧
      γ * ξ * γ⁻¹ ∈ Subgroup.closure ({b, ξ} : Set G) := by
  have hUQ : Subgroup.closure ({b, ξ} : Set G) ≤ Subgroup.closure ({b, ξ, γ} : Set G) :=
    Subgroup.closure_mono
      (Set.insert_subset_insert (Set.singleton_subset_iff.2 (Set.mem_insert _ _)))
  have hcardU : orderOf b * orderOf ξ ≤ Nat.card (Subgroup.closure ({b, ξ} : Set G)) :=
    orderOf_mul_le_card_closure_pair hbξ hdisj
  have hcardQ : Nat.card (Subgroup.closure ({b, ξ, γ} : Set G)) ≤
      3 * Nat.card (Subgroup.closure ({b, ξ} : Set G)) :=
    (card_le_three_pow_of_isPGroup hP).trans (hcard.trans (Nat.mul_le_mul_left 3 hcardU))
  have hconj := conj_mem_of_card_le_three_mul hP hUQ hcardQ
  have hbU : b ∈ Subgroup.closure ({b, ξ} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hξU : ξ ∈ Subgroup.closure ({b, ξ} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hγQ : γ ∈ Subgroup.closure ({b, ξ, γ} : Set G) :=
    Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  exact ⟨hconj γ hγQ b hbU, hconj γ hγQ ξ hξU⟩

theorem v0_conclusion_of_inner {Z : Type*} [Group Z] [Finite Z] {b ξ γ : Z}
    (hcent : Function.Injective (MulAut.conj : Z →* MulAut Z))
    (hP : IsPGroup 3 (Subgroup.closure
      ({MulAut.conj b, MulAut.conj ξ, MulAut.conj γ} : Set (MulAut Z))))
    (hbξ : b * ξ = ξ * b) (hdisj : Subgroup.zpowers b ⊓ Subgroup.zpowers ξ = ⊥)
    (hcard : 3 ^ (Nat.card Z).factorization 3 ≤ 3 * (orderOf b * orderOf ξ)) :
    MulAut.conj γ * MulAut.conj b * (MulAut.conj γ)⁻¹ ∈
        Subgroup.closure ({MulAut.conj b, MulAut.conj ξ} : Set (MulAut Z)) ∧
      MulAut.conj γ * MulAut.conj ξ * (MulAut.conj γ)⁻¹ ∈
        Subgroup.closure ({MulAut.conj b, MulAut.conj ξ} : Set (MulAut Z)) := by
  have hmap : ∀ x ∈ Subgroup.closure ({b, ξ, γ} : Set Z),
      MulAut.conj x ∈
        Subgroup.closure ({MulAut.conj b, MulAut.conj ξ, MulAut.conj γ} : Set (MulAut Z)) := by
    intro x hx
    have h := Subgroup.mem_map_of_mem (MulAut.conj : Z →* MulAut Z) hx
    rwa [MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq,
      Set.image_singleton] at h
  have hH : IsPGroup 3 (Subgroup.closure ({b, ξ, γ} : Set Z)) := by
    refine isPGroup_iff_pow_pow_eq_one.2 fun g => ?_
    obtain ⟨k, hk⟩ :=
      IsPGroup.exists_pow_pow_eq_one hP ⟨MulAut.conj (g : Z), hmap (g : Z) g.2⟩
    have hk' : MulAut.conj (g : Z) ^ 3 ^ k = 1 := by
      have h := congrArg Subtype.val hk
      simpa only [Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_mk] using h
    have h3 : (g : Z) ^ 3 ^ k = 1 := by
      apply hcent
      rw [map_pow, map_one]
      exact hk'
    exact ⟨k, Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact h3)⟩
  have hconj : ∀ x ∈ Subgroup.closure ({b, ξ} : Set Z),
      MulAut.conj x ∈ Subgroup.closure ({MulAut.conj b, MulAut.conj ξ} : Set (MulAut Z)) := by
    intro x hx
    have h := Subgroup.mem_map_of_mem (MulAut.conj : Z →* MulAut Z) hx
    rwa [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton] at h
  obtain ⟨k1, k2⟩ := conj_mem_closure_pair_of_card hH hbξ hdisj hcard
  exact ⟨by simpa only [map_mul, map_inv] using hconj _ k1,
    by simpa only [map_mul, map_inv] using hconj _ k2⟩

end Item1120V0Bar

end CFSG.RankThree.PartTwo.Sec11

end
