module

public import CFSG.LocalAnalysis.StandardType.FS81.N7MainMono

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

private theorem nmh_prod_eq_neg_one_pow (t : Fin 8 → ZMod 3) (ht : IsSign t) :
    (∏ i, t i) = (-1 : ZMod 3) ^ (Finset.univ.filter fun i => t i = -1).card := by
  have h1 : (∏ i, t i) = ∏ i, (if t i = -1 then (-1 : ZMod 3) else 1) := by
    apply Finset.prod_congr rfl
    intro i _
    rcases ht i with h | h <;> simp [h]
  rw [h1, Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

private theorem nmh_nf_prod_isSign (t : Fin 8 → ZMod 3) (ht : IsSign t) :
    (∏ i, t i) = 1 ∨ (∏ i, t i) = -1 := by
  rw [nmh_prod_eq_neg_one_pow t ht]
  rcases Nat.even_or_odd (Finset.univ.filter fun i => t i = -1).card with he | ho
  · left
    exact Even.neg_one_pow he
  · right
    exact Odd.neg_one_pow ho

private theorem nmh_nf_spMat_congr {σ τ : Equiv.Perm (Fin 8)} {s t : Fin 8 → ZMod 3}
    (h1 : σ = τ) (h2 : s = t) : spMat σ s = spMat τ t := by
  rw [h1, h2]

private theorem nmh_nf_spMat_one_eq_nmSgn {t : Fin 8 → ZMod 3} (ht : IsSign t) :
    spMat 1 t = nmSgn (Finset.univ.filter fun i => t i = -1) := by
  ext i j
  rw [spMat_apply, Equiv.Perm.one_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    by_cases h : t i = -1
    · have hmem : i ∈ Finset.univ.filter (fun i => t i = -1) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩
      simp [nmSgn, Matrix.diagonal, hmem, h]
    · rcases ht i with h1 | h1
      · have hmem : i ∉ Finset.univ.filter (fun i => t i = -1) :=
          fun hm => h (Finset.mem_filter.mp hm).2
        simp [nmSgn, Matrix.diagonal, hmem, h1]
      · exact absurd h1 h
  · rw [if_neg hij]
    simp [nmSgn, Matrix.diagonal, hij]

private theorem nmh_spMat_mulVec_fix0 {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3}
    (hσ : σ 0 = 0) : spMat σ s *ᵥ nmE0 = s 0 • nmE0 := by
  funext i
  simp only [spMat_mulVec]
  by_cases hi : i = 0
  · subst hi
    have hsymm : σ.symm 0 = 0 := by
      have := Equiv.symm_apply_apply σ 0
      rwa [hσ] at this
    rw [hsymm]
    simp [nmE0]
  · have hsymm : σ.symm i ≠ 0 := by
      intro h
      exact hi (by rw [← Equiv.apply_symm_apply σ i, h, hσ])
    have hz : nmE0 (σ.symm i) = 0 := by simp [nmE0, hsymm]
    rw [hz, mul_zero]
    simp [nmE0, hi]

private theorem nmh_commutator_diag {u : Fin 8 → ZMod 3} (hu : IsSign u) :
    ∃ t : Fin 8 → ZMod 3, IsSign t ∧ (∏ j, t j) = ∏ j, u j ∧
      spMat (Equiv.swap 0 1) u * spMat (Equiv.swap 1 2) (fun _ => (1 : ZMod 3)) *
        spMat (Equiv.swap 0 1) u * spMat (Equiv.swap 1 2) (fun _ => 1) *
        spMat (Equiv.swap 0 1) u * spMat (Equiv.swap 1 2) (fun _ => 1) =
      spMat 1 t := by
  let α : Equiv.Perm (Fin 8) := Equiv.swap 0 1
  let γ : Equiv.Perm (Fin 8) := Equiv.swap 1 2
  let δ : Equiv.Perm (Fin 8) := γ * α * γ
  refine ⟨fun j => (u (δ (α (γ j))) * u (γ (α (γ j)))) * u (γ j), ?_, ?_, ?_⟩
  · exact IsSign.mul (IsSign.mul (fun j => hu (δ (α (γ j))))
      (fun j => hu (γ (α (γ j))))) (fun j => hu (γ j))
  · have h1 : (∏ j, u (δ (α (γ j)))) = ∏ j, u j := by
      simpa only [Equiv.Perm.mul_apply] using Equiv.prod_comp (δ * α * γ) u
    have h2 : (∏ j, u (γ (α (γ j)))) = ∏ j, u j := by
      simpa only [Equiv.Perm.mul_apply] using Equiv.prod_comp (γ * α * γ) u
    have h3 : (∏ j, u (γ j)) = ∏ j, u j := by
      simpa only [Equiv.Perm.mul_apply] using Equiv.prod_comp γ u
    calc ∏ j, (u (δ (α (γ j))) * u (γ (α (γ j)))) * u (γ j)
        = (∏ j, u (δ (α (γ j))) * u (γ (α (γ j)))) * (∏ j, u (γ j)) := by
          rw [Finset.prod_mul_distrib]
      _ = ((∏ j, u (δ (α (γ j)))) * (∏ j, u (γ (α (γ j))))) * (∏ j, u (γ j)) := by
          rw [Finset.prod_mul_distrib]
      _ = ((∏ j, u j) * (∏ j, u j)) * (∏ j, u j) := by rw [h1, h2, h3]
      _ = ∏ j, u j := by
          rcases nmh_nf_prod_isSign u hu with h | h <;> rw [h] <;> decide
  · have e1 : spMat α u * spMat γ (fun _ => (1 : ZMod 3)) =
        spMat (α * γ) (fun j => u (γ j)) := by
      rw [spMat_mul]
      simp only [mul_one]
    have e2 : (spMat α u * spMat γ (fun _ => 1)) * spMat α u =
        spMat ((α * γ) * α) (fun j => u (γ (α j)) * u j) := by
      rw [e1, spMat_mul]
    have e3 : ((spMat α u * spMat γ (fun _ => 1)) * spMat α u) * spMat γ (fun _ => 1) =
        spMat (((α * γ) * α) * γ) (fun j => u (γ (α (γ j))) * u (γ j)) := by
      rw [e2, spMat_mul]
      simp only [mul_one]
    have e4 : (((spMat α u * spMat γ (fun _ => 1)) * spMat α u) * spMat γ (fun _ => 1)) *
        spMat α u =
        spMat ((((α * γ) * α) * γ) * α)
          (fun j => (u (γ (α (γ (α j)))) * u (γ (α j))) * u j) := by
      rw [e3, spMat_mul]
    have e5 : ((((spMat α u * spMat γ (fun _ => 1)) * spMat α u) * spMat γ (fun _ => 1)) *
        spMat α u) * spMat γ (fun _ => 1) =
        spMat (((((α * γ) * α) * γ) * α) * γ)
          (fun j => (u (γ (α (γ (α (γ j))))) * u (γ (α (γ j)))) * u (γ j)) := by
      rw [e4, spMat_mul]
      simp only [mul_one]
    rw [e5]
    apply nmh_nf_spMat_congr
    · decide
    · rfl

theorem nm_normalizer_cases {X : Type} [Group X] [Finite X] (S : N7MSetup X) :
    (∀ x : X, (∀ a, a ∈ S.Fgrp ↔ x * a * x⁻¹ ∈ S.Fgrp) → S.ρ x ∈ evenAll0 7) ∨
      (∀ A ∈ nmFK, ∃ x, S.ρ x = A) := by
  by_cases h : ∀ x : X, (∀ a, a ∈ S.Fgrp ↔ x * a * x⁻¹ ∈ S.Fgrp) →
      ∃ σ s, IsSign s ∧ S.ρ x = spMat σ s ∧ σ 0 = 0
  · left
    intro x hx
    obtain ⟨σ, s, hs, heq, hσ0⟩ := h x hx
    rw [← S.norm_iff x]
    exact ⟨s 0, by rw [heq, nmh_spMat_mulVec_fix0 hσ0]⟩
  · right
    rw [not_forall] at h
    obtain ⟨y, hy⟩ := h
    rw [not_imp] at hy
    obtain ⟨hy_norm, hy_not⟩ := hy
    obtain ⟨π, s, hs, hy_eq⟩ := nm_normalizer_mono S hy_norm
    have hπ0 : π 0 ≠ 0 := fun hp0 => hy_not ⟨π, s, hs, hy_eq, hp0⟩
    let j : Fin 8 := π 0
    let τ₁ : Equiv.Perm (Fin 8) := Equiv.swap j 1
    let β : Equiv.Perm (Fin 8) := Equiv.swap 0 1 * τ₁ * π
    have hτ0 : τ₁ 0 = 0 := by
      have h : Equiv.swap j 1 0 = 0 :=
        Equiv.swap_apply_of_ne_of_ne (by simpa only [j] using Ne.symm hπ0) (by decide)
      simpa only [τ₁] using h
    have hβ0 : β 0 = 0 := by
      have h : τ₁ (π 0) = 1 := by
        have := Equiv.swap_apply_left j 1
        simpa only [τ₁, j] using this
      rw [show β = Equiv.swap 0 1 * τ₁ * π from rfl]
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h, Equiv.swap_apply_right]
    have hβinv0 : β⁻¹ 0 = 0 := by
      have h := Equiv.symm_apply_apply β 0
      rwa [hβ0] at h
    obtain ⟨a, ha⟩ := S.surj_H1 (spMat τ₁ (fun _ => 1))
      ⟨τ₁, fun _ => 1, fun _ => Or.inl rfl, ⟨hτ0, by simp⟩, rfl⟩
    obtain ⟨b, hb⟩ := S.surj_H1 (spMat β⁻¹ (fun _ => 1))
      ⟨β⁻¹, fun _ => 1, fun _ => Or.inl rfl, ⟨hβinv0, by simp⟩, rfl⟩
    let u : Fin 8 → ZMod 3 := fun k => s (β⁻¹ k)
    have hu : IsSign u := fun k => hs (β⁻¹ k)
    have hperm1 : (τ₁ * π) * β⁻¹ = Equiv.swap 0 1 := by
      have hβinv : β⁻¹ = π⁻¹ * (τ₁⁻¹ * (Equiv.swap 0 1)⁻¹) := by
        dsimp only [β]
        rw [mul_inv_rev, mul_inv_rev]
      rw [hβinv]
      rw [show (τ₁ * π) * (π⁻¹ * (τ₁⁻¹ * (Equiv.swap 0 1)⁻¹)) =
          (Equiv.swap 0 1)⁻¹ by group, Equiv.swap_inv]
    let M : X := a * y * b
    have hM1 : S.ρ M = spMat (Equiv.swap 0 1) u := by
      rw [show M = a * y * b from rfl]
      rw [map_mul, map_mul, ha, hy_eq, hb]
      simp only [spMat_mul, one_mul, mul_one]
      apply nmh_nf_spMat_congr
      · exact hperm1
      · rfl
    have hε : (∏ k : Fin 8, u k) = 1 := by
      rcases nmh_nf_prod_isSign u hu with h1 | hneg
      · exact h1
      · exfalso
        obtain ⟨t, ht_sign, ht_prod, ht_mat⟩ := nmh_commutator_diag hu
        let A' : Finset (Fin 8) := Finset.univ.filter fun j => t j = -1
        obtain ⟨gB, hgB⟩ := S.surj_H1 (spMat (Equiv.swap 1 2) (fun _ => 1))
          ⟨Equiv.swap 1 2, fun _ => 1, fun _ => Or.inl rfl, ⟨by decide, by simp⟩, rfl⟩
        let d : X := M * gB * M * gB * M * gB
        have hdρ : S.ρ d = spMat (Equiv.swap 0 1) u * spMat (Equiv.swap 1 2) (fun _ => 1) *
            spMat (Equiv.swap 0 1) u * spMat (Equiv.swap 1 2) (fun _ => 1) *
            spMat (Equiv.swap 0 1) u * spMat (Equiv.swap 1 2) (fun _ => 1) := by
          simp only [d, map_mul, hM1, hgB]
        have hd_diag : S.ρ d = spMat 1 t := by rw [hdρ, ht_mat]
        have htprod : (∏ j, t j) = -1 := by rw [ht_prod]; exact hneg
        have hdiag : spMat 1 t = nmSgn A' := nmh_nf_spMat_one_eq_nmSgn ht_sign
        have hodd : Odd A'.card := by
          have hpow : (-1 : ZMod 3) ^ A'.card = -1 := by
            change (-1 : ZMod 3) ^ (Finset.univ.filter fun i => t i = -1).card = -1
            rw [← nmh_prod_eq_neg_one_pow t ht_sign]
            exact htprod
          rcases Nat.even_or_odd A'.card with he | ho
          · have h1 : (-1 : ZMod 3) ^ A'.card = 1 := Even.neg_one_pow he
            exact absurd (hpow.symm.trans h1) (by decide)
          · exact ho
        exact (S.ne_nmSgn_of_odd hodd d) (by rw [hd_diag, hdiag])
    have hDmem : spMat 1 u ∈ nmF := ⟨1, u, hu, ⟨rfl, hε⟩, rfl⟩
    obtain ⟨e, he⟩ := S.exists_of_mem_nmF hDmem
    have hp_mem : ∃ p : X, S.ρ p = spMat (Equiv.swap 0 1) (fun _ => 1) :=
      ⟨M * e, by
        rw [map_mul, hM1, he, spMat_mul]
        apply nmh_nf_spMat_congr
        · simp
        · funext k
          simpa using IsSign.mul_self hu k⟩
    obtain ⟨p, hp⟩ := hp_mem
    intro A hA
    obtain ⟨σ, s', hs', hps', hAeq⟩ := hA
    rw [hAeq]
    have hdecomp : spMat σ (fun _ => 1) * spMat 1 s' = spMat σ s' := by
      rw [spMat_mul]
      apply nmh_nf_spMat_congr
      · simp
      · funext k; simp
    have hσ_mem : ∃ x : X, S.ρ x = spMat σ (fun _ => 1) := by
      by_cases hσ0 : σ 0 = 0
      · exact S.surj_H1 _ ⟨σ, fun _ => 1, fun _ => Or.inl rfl, ⟨hσ0, by simp⟩, rfl⟩
      · let τ' : Equiv.Perm (Fin 8) := Equiv.swap (σ 0) 1
        let β' : Equiv.Perm (Fin 8) := Equiv.swap 0 1 * τ' * σ
        have hτ'0 : τ' 0 = 0 := by
          have h : Equiv.swap (σ 0) 1 0 = 0 :=
            Equiv.swap_apply_of_ne_of_ne (Ne.symm hσ0) (by decide)
          simpa only [τ'] using h
        have hβ'0 : β' 0 = 0 := by
          have h : τ' (σ 0) = 1 := by
            have := Equiv.swap_apply_left (σ 0) 1
            simpa only [τ'] using this
          rw [show β' = Equiv.swap 0 1 * τ' * σ from rfl]
          rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h, Equiv.swap_apply_right]
        have hσ_decomp : spMat τ' (fun _ => 1) * spMat (Equiv.swap 0 1) (fun _ => 1) *
              spMat β' (fun _ => 1) = spMat σ (fun _ => 1) := by
          rw [spMat_mul, spMat_mul]
          apply nmh_nf_spMat_congr
          · ext x
            rw [show β' = Equiv.swap 0 1 * τ' * σ from rfl]
            dsimp only [τ']
            simp only [Equiv.Perm.mul_apply]
            rw [Equiv.swap_apply_self, Equiv.swap_apply_self]
          · funext k; simp
        obtain ⟨xτ, hxτ⟩ := S.surj_H1 (spMat τ' (fun _ => 1))
          ⟨τ', fun _ => 1, fun _ => Or.inl rfl, ⟨hτ'0, by simp⟩, rfl⟩
        obtain ⟨xβ, hxβ⟩ := S.surj_H1 (spMat β' (fun _ => 1))
          ⟨β', fun _ => 1, fun _ => Or.inl rfl, ⟨hβ'0, by simp⟩, rfl⟩
        exact ⟨xτ * p * xβ, by rw [map_mul, map_mul, hxτ, hp, hxβ, hσ_decomp]⟩
    obtain ⟨xσ, hxσ⟩ := hσ_mem
    have hDmem' : spMat 1 s' ∈ nmF := ⟨1, s', hs', ⟨rfl, hps'⟩, rfl⟩
    obtain ⟨xd, hxd⟩ := S.exists_of_mem_nmF hDmem'
    exact ⟨xσ * xd, by rw [map_mul, hxσ, hxd, hdecomp]⟩

end CFSG.StandardType.FrameRoute.FS81

end
