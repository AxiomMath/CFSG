module

public import CFSG.Quasithin.H13.A6S1514

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise

@[expose] def lK : Perm (Fin 6) := swap 0 5 * swap 1 2

theorem lK_facts : Perm.sign lK = 1 ∧ lK 4 = 4 ∧ lK 5 ≠ 5 := by decide

@[expose] def KGens : List (Perm (Fin 6)) :=
  [swap 0 1 * swap 2 3, swap 0 2 * swap 1 3, swap 0 3 * swap 1 2,
    lK⁻¹ * (swap 0 1 * swap 2 3) * lK, lK⁻¹ * (swap 0 2 * swap 1 3) * lK,
    lK⁻¹ * (swap 0 3 * swap 1 2) * lK]

@[expose] def evalW (w : List ℕ) : Perm (Fin 6) := (w.map fun i => KGens.getD i 1).prod

@[expose] def KWords : List (List ℕ) :=
  [[], [2, 4, 1], [1, 4, 2], [5], [0, 5, 1, 4], [1, 5, 0], [0, 3, 2, 4], [2, 3, 0], [3],
    [0, 5, 1], [0, 3, 2], [4], [1, 4, 1], [0], [2, 4, 2], [3, 2, 4], [1, 3, 0], [0, 3], [0, 5],
    [5, 1, 4], [2, 5, 0], [5, 1], [0, 4], [3, 2], [4, 2, 3], [1, 5], [5, 0], [0, 3, 0],
    [5, 0, 3], [1, 3], [1], [0, 4, 1], [4, 2], [2, 3, 2], [1, 4], [2, 5, 1], [3, 0], [4, 1, 5],
    [2, 3], [3, 0, 5], [2, 5], [0, 5, 0], [4, 1], [2], [0, 4, 2], [2, 4], [1, 3, 2], [1, 5, 1],
    [0, 3, 1], [4, 0], [0, 5, 2], [3, 1], [5, 2], [0, 4, 0], [1, 4, 0], [2, 5, 2], [2, 3, 1],
    [1, 5, 2], [2, 4, 0], [1, 3, 1]]

@[expose] def StabAt (σ : Perm (Fin 6)) : Prop :=
  σ 4 = 4 → Perm.sign σ = 1 → ∃ w ∈ KWords, evalW w = σ

instance (σ : Perm (Fin 6)) : Decidable (StabAt σ) := by unfold StabAt; infer_instance

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem exists_lK : ∃ l : ↥(Subgroup.normalizer (V : Set G)), (l : G) ∈ L ∧ S.frame.ρ l = lK :=
  (S.frame.image_L lK).2 (Perm.mem_alternatingGroup.2 lK_facts.1)

theorem not_mem_L1T {l : ↥(Subgroup.normalizer (V : Set G))} (hl : S.frame.ρ l = lK) :
    (l : G) ∉ S.L1 ⊔ T := by
  intro h
  have hmul : ((S.L1 ⊔ T : Subgroup G) : Set G) = (S.L1 : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left _ _ S.T_le_normalizer_L1
  rw [← SetLike.mem_coe, hmul] at h
  obtain ⟨a, ha, t, ht, hat⟩ := h
  have haN : a ∈ Subgroup.normalizer (V : Set G) := S.frame.L_le (S.L1_le.trans inf_le_left ha)
  have htN : t ∈ Subgroup.normalizer (V : Set G) := S.frame.T_le ht
  have e : l = ⟨a, haN⟩ * ⟨t, htN⟩ := Subtype.ext hat.symm
  obtain ⟨h4, h5, -⟩ := S.rho_L1 (g := ⟨a, haN⟩) ha
  obtain ⟨-, ht5, -⟩ := S.frame.T_D ⟨t, htN⟩ ht
  have hl5 : S.frame.ρ l 5 = lK 5 := by rw [hl]
  rw [e, map_mul, Perm.mul_apply] at hl5
  have hlK5 : lK 5 = 0 := by decide
  rw [hlK5] at hl5
  have ht5' : S.frame.ρ ⟨t, htN⟩ 5 = 4 ∨ S.frame.ρ ⟨t, htN⟩ 5 = 5 := by
    have := ht5
    omega
  rcases ht5' with h | h <;> rw [h] at hl5
  · rw [h4] at hl5
    exact absurd hl5 (by decide)
  · rw [h5] at hl5
    exact absurd hl5 (by decide)

end Setting4

end CFSG.Quasithin.H13.A6
