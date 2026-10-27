module

public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolCardCent

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1119Sym

theorem aux_SylowAux_map_conj_one {G : Type*} [Group G] (H : Subgroup G) :
    H.map (MulAut.conj (1 : G)).toMonoidHom = H := by
  ext x
  simp [MulAut.conj_apply, Subgroup.mem_map]

theorem aux_SylowAux_map_pow_succ {G : Type*} [Group G] (s : G) (n : ℕ) (H : Subgroup G) :
    H.map (MulAut.conj (s ^ (n + 1))).toMonoidHom =
      (H.map (MulAut.conj (s ^ n)).toMonoidHom).map (MulAut.conj s).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, pow_succ', mul_assoc]

theorem three_group_fixes_line {G : Type*} [Group G] (l₁ l₂ : Subgroup G) (hne : l₁ ≠ l₂) (s : G)
    (hs : ∃ k : ℕ, s ^ 3 ^ k = 1)
    (h₁ : l₁.map (MulAut.conj s).toMonoidHom = l₁ ∨ l₁.map (MulAut.conj s).toMonoidHom = l₂)
    (h₂ : l₂.map (MulAut.conj s).toMonoidHom = l₁ ∨ l₂.map (MulAut.conj s).toMonoidHom = l₂) :
    l₁.map (MulAut.conj s).toMonoidHom = l₁ := by
  by_contra hcon
  have hinj : Function.Injective (MulAut.conj s).toMonoidHom := (MulAut.conj s).injective
  have hσ1 : l₁.map (MulAut.conj s).toMonoidHom = l₂ := h₁.resolve_left hcon
  have hσ2 : l₂.map (MulAut.conj s).toMonoidHom = l₁ := by
    rcases h₂ with h | h
    · exact h
    · exfalso
      have hmap : l₁.map (MulAut.conj s).toMonoidHom = l₂.map (MulAut.conj s).toMonoidHom := by
        rw [hσ1, h]
      exact hne (Subgroup.map_injective hinj hmap)
  have hA : ∀ n : ℕ, l₁.map (MulAut.conj (s ^ (2 * n))).toMonoidHom = l₁ ∧
      l₁.map (MulAut.conj (s ^ (2 * n + 1))).toMonoidHom = l₂ := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · rw [Nat.mul_zero, pow_zero]
        exact aux_SylowAux_map_conj_one l₁
      · rw [Nat.mul_zero, Nat.zero_add, pow_one]
        exact hσ1
    | succ n ih =>
      have hE : l₁.map (MulAut.conj (s ^ (2 * (n + 1)))).toMonoidHom = l₁ := by
        rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, aux_SylowAux_map_pow_succ, ih.2, hσ2]
      refine ⟨hE, ?_⟩
      rw [aux_SylowAux_map_pow_succ, hE, hσ1]
  obtain ⟨k, hk⟩ := hs
  have hodd : Odd (3 ^ k) := Odd.pow (by decide)
  obtain ⟨m, hm⟩ := hodd
  have h3 : l₁.map (MulAut.conj (s ^ 3 ^ k)).toMonoidHom = l₁ := by
    rw [hk]
    exact aux_SylowAux_map_conj_one l₁
  rw [hm, (hA m).2] at h3
  exact hne h3.symm

theorem eq_of_le_isPGroup {G : Type*} [Group G] [Finite G]
    (P S R H : Subgroup G) (c : G) (T : Finset G)
    (hPS : P ≤ S) (hS : IsPGroup 3 S)
    (hRmax : ∀ K : Subgroup G, K ≤ H → IsPGroup 3 K → R ≤ K → K = R)
    (hRP : R ≤ P) (hPR : Nat.card P = 3 * Nat.card R)
    (hRc : R ≤ Subgroup.centralizer ({c} : Set G)) (hCH : Subgroup.centralizer ({c} : Set G) ≤ H)
    (hT : T.card ≤ 3) (hSc : ∀ s ∈ S, s * c * s⁻¹ ∈ T) : S = P := by
  have hCS : S ⊓ Subgroup.centralizer ({c} : Set G) ≤ S := inf_le_left
  have hCH' : S ⊓ Subgroup.centralizer ({c} : Set G) ≤ H := inf_le_right.trans hCH
  have hCgrp : IsPGroup 3 (S ⊓ Subgroup.centralizer ({c} : Set G) : Subgroup G) :=
    IsPGroup.to_le hS hCS
  have hRC : R ≤ S ⊓ Subgroup.centralizer ({c} : Set G) := le_inf (hRP.trans hPS) hRc
  have hCR : S ⊓ Subgroup.centralizer ({c} : Set G) = R := hRmax _ hCH' hCgrp hRC
  have hbound := card_le_three_mul_card_centralizer S c T hT hSc
  rw [hCR] at hbound
  have hle : Nat.card S ≤ Nat.card P := by
    rw [hPR]
    exact hbound
  exact (Subgroup.eq_of_le_of_card_ge hPS hle).symm

end CFSG.RankThree.PartTwo.Sec11.Item1119Sym

end
