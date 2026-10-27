module

public import CFSG.LocalAnalysis.StandardType.FS81.N7FixSylowB
import CFSG.LocalAnalysis.StandardType.FS81.N7FixGen
import CFSG.LocalAnalysis.StandardType.FS81.OddCoreOrthRows

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

theorem q2nN7_card_sets :
    {T : Finset (Fin 8) | (0 : Fin 8) ∉ T ∧ T.card = 6}.ncard = 7 := by
  have h : {T : Finset (Fin 8) | (0 : Fin 8) ∉ T ∧ T.card = 6} =
      ↑(Finset.univ.filter fun T : Finset (Fin 8) => (0 : Fin 8) ∉ T ∧ T.card = 6) := by
    ext T
    simp
  rw [h, Set.ncard_coe_finset]
  decide

theorem q2nN7_E6set_ncard : E6set.ncard = 7 := by
  have h : E6set = sgn '' {T : Finset (Fin 8) | (0 : Fin 8) ∉ T ∧ T.card = 6} := by
    ext M
    constructor
    · rintro ⟨T, h0, hT, rfl⟩
      exact ⟨T, ⟨h0, hT⟩, rfl⟩
    · rintro ⟨T, ⟨h0, hT⟩, rfl⟩
      exact ⟨T, h0, hT, rfl⟩
  rw [h, Set.ncard_image_of_injective _ q2nN7_sgn_injective]
  exact q2nN7_card_sets

theorem q2nN7_exists_perm {T T' : Finset (Fin 8)} (h0 : (0 : Fin 8) ∉ T) (hT : T.card = 6)
    (h0' : (0 : Fin 8) ∉ T') (hT' : T'.card = 6) :
    ∃ π : Equiv.Perm (Fin 8), π 0 = 0 ∧ T.map π.toEmbedding = T' := by
  have hmem : ∀ {U : Finset (Fin 8)}, (0 : Fin 8) ∉ U → U.card = 6 →
      ∃ k : Fin 8, k ≠ 0 ∧ ∀ a, a ∈ U ↔ (a ≠ 0 ∧ a ≠ k) := by
    intro U h0 hU
    have hc : (Uᶜ).card = 2 := by
      rw [Finset.card_compl, hU]
      rfl
    obtain ⟨x, y, hxy, hUc⟩ := Finset.card_eq_two.1 hc
    have h0c : (0 : Fin 8) ∈ Uᶜ := Finset.mem_compl.2 h0
    rw [hUc, Finset.mem_insert, Finset.mem_singleton] at h0c
    have key : ∀ a, a ∈ U ↔ a ∉ Uᶜ := fun a => by rw [Finset.mem_compl, not_not]
    rcases h0c with h | h
    · refine ⟨y, fun hy => hxy (h.symm.trans hy.symm), fun a => ?_⟩
      rw [key, hUc]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or, ← h]
    · refine ⟨x, fun hx => hxy (hx.trans h), fun a => ?_⟩
      rw [key, hUc]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or, ← h]
      tauto
  obtain ⟨k, hk0, hk⟩ := hmem h0 hT
  obtain ⟨k', hk0', hk'⟩ := hmem h0' hT'
  refine ⟨Equiv.swap k k', Equiv.swap_apply_of_ne_of_ne (Ne.symm hk0) (Ne.symm hk0'), ?_⟩
  ext a
  rw [Finset.mem_map_equiv, hk', hk, Equiv.symm_swap]
  by_cases h1 : a = k
  · subst h1
    rw [Equiv.swap_apply_left]
    exact ⟨fun h => ⟨hk0, fun e => h.2 e.symm⟩, fun h => ⟨hk0', fun e => h.2 e.symm⟩⟩
  · by_cases h2 : a = k'
    · subst h2
      rw [Equiv.swap_apply_right]
      exact ⟨fun h => absurd rfl h.2, fun h => absurd rfl h.2⟩
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      exact ⟨fun h => ⟨h.1, h2⟩, fun h => ⟨h.1, h1⟩⟩

namespace N7Setup

variable {X : Type} [Group X] [Finite X] (S : N7Setup X)

theorem q2nN7_E6_ncard : {x : X | S.ρ x ∈ E6set}.ncard = 7 := by
  have h : {x : X | S.ρ x ∈ E6set} = S.ρ ⁻¹' E6set := rfl
  rw [h, Set.ncard_preimage_of_injective_subset_range S.ρ_inj ?_]
  · exact q2nN7_E6set_ncard
  · intro M hM
    obtain ⟨x, hx⟩ := S.exists_of_mem_E6set hM
    exact ⟨x, hx⟩

theorem q2nN7_E6_conj {τ x : X} (hτ : S.ρ τ ∈ E6set) (hx : S.ρ x ∈ E6set) :
    ∃ m ∈ S.H, x = m * τ * m⁻¹ := by
  obtain ⟨T, h0, hT, hτT⟩ := hτ
  obtain ⟨T', h0', hT', hxT⟩ := hx
  obtain ⟨π, hπ0, hπ⟩ := q2nN7_exists_perm h0 hT h0' hT'
  obtain ⟨m, hm⟩ := S.surj_H _ (perm_mem_evenFix0 (n := 7) π hπ0)
  refine ⟨m, (S.mem_H_iff m).2 (hm ▸ perm_mem_evenFix0 (n := 7) π hπ0), ?_⟩
  apply S.ρ_inj
  have hinv : S.ρ m * S.ρ m⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hconj : S.ρ m * sgn T = sgn T' * S.ρ m := by
    rw [hm, q2nN7_spMat_mul_sgn, hπ]
  calc S.ρ x = sgn T' := hxT
    _ = sgn T' * (S.ρ m * S.ρ m⁻¹) := by rw [hinv, mul_one]
    _ = (sgn T' * S.ρ m) * S.ρ m⁻¹ := by rw [mul_assoc]
    _ = (S.ρ m * sgn T) * S.ρ m⁻¹ := by rw [hconj]
    _ = S.ρ (m * τ * m⁻¹) := by rw [map_mul, map_mul, hτT]

theorem exists_central_E6 {P : Subgroup X} (hPH : P ≤ S.H) (hP : IsPGroup 2 P) :
    ∃ τ : X, S.ρ τ ∈ E6set ∧ ∀ y ∈ P, y * τ = τ * y := by
  have hconj : ∀ y ∈ P, ∀ τ ∈ {x : X | S.ρ x ∈ E6set}, y * τ * y⁻¹ ∈ {x : X | S.ρ x ∈ E6set} := by
    intro y hy τ hτ
    have hτH : τ ∈ S.H := S.F1_le_H (Subgroup.subset_closure hτ)
    have hyH : y ∈ S.H := hPH hy
    exact S.conj_E6_mem hτ (mul_mem (mul_mem hyH hτH) (inv_mem hyH))
  obtain ⟨τ, hτ, hc⟩ := q2nN7_exists_central (p := 2) P hP {x : X | S.ρ x ∈ E6set}
    (Set.toFinite _) (by rw [S.q2nN7_E6_ncard]; decide) hconj
  exact ⟨τ, hτ, hc⟩

theorem closure_conj_eq_F1 {P : Subgroup X} (hPH : P ≤ S.H) (hF1P : S.F1 ≤ P) {τ : X}
    (hτ : S.ρ τ ∈ E6set) :
    Subgroup.closure {y | y ∈ P ∧ ∃ m : X, y = m * τ * m⁻¹} = S.F1 := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨hyP, m, rfl⟩
    exact Subgroup.subset_closure (S.conj_E6_mem hτ (hPH hyP))
  · refine (Subgroup.closure_le _).2 ?_
    intro x hx
    obtain ⟨m, -, rfl⟩ := S.q2nN7_E6_conj hτ hx
    exact Subgroup.subset_closure ⟨hF1P (Subgroup.subset_closure hx), m, rfl⟩

end N7Setup

end CFSG.StandardType.FrameRoute.FS81

end
