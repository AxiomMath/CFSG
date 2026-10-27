module

public import Mathlib.GroupTheory.Index

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

private lemma r920kwa_eq_two_of_dvd_two {n : ℕ} (hdvd : n ∣ 2) (h0 : n ≠ 0) (h1 : n ≠ 1) :
    n = 2 := by
  have hle : n ≤ 2 := Nat.le_of_dvd (by decide : 0 < 2) hdvd
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hle1 : n ≤ 1 := Nat.lt_succ_iff.mp hlt
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle1 with h | h
    · exact absurd h h0
    · exact absurd h h1
  · exact heq

private lemma r920kwa_eq_or_eq_top_of_le_of_index_two {G : Type*} [Group G] [Finite G]
    {B C : Subgroup G} (hB : B.index = 2) (hle : B ≤ C) : C = B ∨ C = ⊤ := by
  by_cases htop : C = ⊤
  · exact Or.inr htop
  · left
    have hC2 : C.index = 2 := by
      have hdvd : C.index ∣ 2 := by
        have := Subgroup.index_dvd_of_le hle
        rwa [hB] at this
      exact r920kwa_eq_two_of_dvd_two hdvd (Subgroup.FiniteIndex.index_ne_zero (H := C))
        fun h0 => htop (Subgroup.index_eq_one.mp h0)
    have hdvd' : B.index ∣ C.index := by
      rw [hB, hC2]
    exact (Subgroup.eq_of_index_dvd_index hle hdvd').symm

theorem false_of_irreducible_section_of_abelian_index_two {T E : Type} [Group T] [Finite T]
    [Group E] [Finite E] (π : T →* E) (hπ : Function.Surjective π) (hE : ∀ e : E, e * e = 1)
    (hE8 : Nat.card E = 8) (σ : T ≃* T) (f : E ≃* E) (hσf : ∀ t, π (σ t) = f (π t))
    (hirr : ∀ F : Subgroup E, (∀ e ∈ F, f e ∈ F) → F = ⊥ ∨ F = ⊤)
    (hab : ∃ B : Subgroup T, (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ B.index ≤ 2)
    (hrk : ∀ A : Subgroup T, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → Nat.card (A.map π) ≤ 4) :
    False := by
  have hnotcomm : ¬ (∀ a b : T, a * b = b * a) := by
    intro hcomm
    have htop_abel : ∀ a ∈ (⊤ : Subgroup T), ∀ b ∈ (⊤ : Subgroup T), a * b = b * a :=
      fun a _ b _ => hcomm a b
    have hle := hrk ⊤ htop_abel
    have htopmap : (⊤ : Subgroup T).map π = ⊤ := Subgroup.map_top_of_surjective π hπ
    rw [htopmap, Subgroup.card_top, hE8] at hle
    exact absurd hle (by decide)
  obtain ⟨B, hBcomm, hBindex⟩ := hab
  have hBindex_ne_one : B.index ≠ 1 := by
    intro h1
    have hBtop : B = ⊤ := Subgroup.index_eq_one.mp h1
    refine hnotcomm fun a b => ?_
    exact hBcomm a (hBtop ▸ Subgroup.mem_top a) b (hBtop ▸ Subgroup.mem_top b)
  have hBindex2 : B.index = 2 := by
    rcases lt_or_eq_of_le hBindex with hlt | heq
    · have hle1 : B.index ≤ 1 := Nat.lt_succ_iff.mp hlt
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hle1 with h0 | h1
      · exact absurd h0 (Subgroup.FiniteIndex.index_ne_zero (H := B))
      · exact absurd h1 hBindex_ne_one
    · exact heq
  have hBmap_le : Nat.card (B.map π) ≤ 4 := hrk B hBcomm
  have hBmul : Nat.card (B.map π) * (B.map π).index = 8 := by
    have := Subgroup.card_mul_index (B.map π)
    rwa [hE8] at this
  have hBmap_index_dvd : (B.map π).index ∣ 2 := by
    have := Subgroup.index_map_dvd B hπ
    rwa [hBindex2] at this
  have hBmap_index_ne_one : (B.map π).index ≠ 1 := by
    intro h1
    have htop : B.map π = ⊤ := Subgroup.index_eq_one.mp h1
    have hcard8 : Nat.card (B.map π) = 8 := by rw [htop, Subgroup.card_top, hE8]
    have : (8 : ℕ) ≤ 4 := by rw [← hcard8]; exact hBmap_le
    exact absurd this (by decide)
  have hBmap_index2 : (B.map π).index = 2 :=
    r920kwa_eq_two_of_dvd_two hBmap_index_dvd
      (Subgroup.FiniteIndex.index_ne_zero (H := B.map π)) hBmap_index_ne_one
  have hBcard : Nat.card (B.map π) = 4 := by
    have hBmul2 : Nat.card (B.map π) * 2 = 8 := by
      rw [hBmap_index2] at hBmul
      exact hBmul
    refine Nat.mul_right_cancel (m := 2) (by decide) ?_
    rw [hBmul2]
  let N : Subgroup T := π.ker
  have hNmap : N.map π = ⊥ := Subgroup.map_ker_self π
  have hNleB : N ≤ B := by
    rcases r920kwa_eq_or_eq_top_of_le_of_index_two hBindex2
        (le_sup_left : B ≤ B ⊔ N) with h | h
    · exact sup_eq_left.mp h
    · exfalso
      have hBmap_top : B.map π = ⊤ := by
        have hsupmap : (B ⊔ N).map π = (B.map π) ⊔ (N.map π) := Subgroup.map_sup B N π
        have htop : (B ⊔ N).map π = ⊤ := by rw [h, Subgroup.map_top_of_surjective π hπ]
        rw [hsupmap, hNmap, sup_bot_eq] at htop
        exact htop
      have hcard8 : Nat.card (B.map π) = 8 := by rw [hBmap_top, Subgroup.card_top, hE8]
      have : (8 : ℕ) ≤ 4 := by rw [← hcard8]; exact hBmap_le
      exact absurd this (by decide)
  let B' : Subgroup T := B.map σ.toMonoidHom
  have hB'comm : ∀ a ∈ B', ∀ b ∈ B', a * b = b * a := by
    intro a ha b hb
    rcases Subgroup.mem_map.mp ha with ⟨a₀, ha₀, rfl⟩
    rcases Subgroup.mem_map.mp hb with ⟨b₀, hb₀, rfl⟩
    rw [← map_mul, ← map_mul, hBcomm a₀ ha₀ b₀ hb₀]
  have hB'index : B'.index = 2 := by
    change (B.map σ.toMonoidHom).index = 2
    rw [Subgroup.index_map_of_bijective (H := B) (f := σ.toMonoidHom) σ.bijective, hBindex2]
  have hNleB' : N ≤ B' := by
    intro n hn
    have hn1 : π n = 1 := MonoidHom.mem_ker.mp hn
    have hσinvN : σ.symm n ∈ N := by
      show π (σ.symm n) = 1
      have h1 : f (π (σ.symm n)) = 1 := by
        have h2 := hσf (σ.symm n)
        rw [MulEquiv.apply_symm_apply, hn1] at h2
        exact h2.symm
      exact f.injective (by rw [h1, map_one])
    exact Subgroup.mem_map.mpr ⟨σ.symm n, hNleB hσinvN, σ.apply_symm_apply n⟩
  have hπB' : B'.map π = (B.map π).map f.toMonoidHom := by
    change (B.map σ.toMonoidHom).map π = (B.map π).map f.toMonoidHom
    have hcomp : π.comp σ.toMonoidHom = f.toMonoidHom.comp π := MonoidHom.ext fun t => hσf t
    rw [Subgroup.map_map, Subgroup.map_map, hcomp]
  have hBneB' : B' ≠ B := by
    have hnotinv : ¬ (∀ x ∈ B.map π, f x ∈ B.map π) := by
      intro hinv
      rcases hirr (B.map π) hinv with h | h
      · have h1 : Nat.card (B.map π) = 1 := by rw [h, Subgroup.card_bot]
        exact absurd (h1 ▸ hBcard) (by decide)
      · have h1 : Nat.card (B.map π) = 8 := by rw [h, Subgroup.card_top, hE8]
        exact absurd (h1 ▸ hBcard) (by decide)
    have hex : ∃ x ∈ B.map π, f x ∉ B.map π := by
      by_contra h
      apply hnotinv
      intro x hx
      by_contra hfx
      exact h ⟨x, hx, hfx⟩
    obtain ⟨e, he, hfe⟩ := hex
    intro hEq
    have hPeq : (B.map π).map f.toMonoidHom = B.map π := by rw [← hπB', hEq]
    have hfe' : f e ∈ B.map π := by
      have : f e ∈ (B.map π).map f.toMonoidHom := Subgroup.mem_map_of_mem f.toMonoidHom he
      rwa [hPeq] at this
    exact hfe hfe'
  have hsup : B ⊔ B' = ⊤ := by
    rcases r920kwa_eq_or_eq_top_of_le_of_index_two hBindex2
        (le_sup_left : B ≤ B ⊔ B') with h | h
    · have hle : B' ≤ B := sup_eq_left.mp h
      have hdvd : B'.index ∣ B.index := by
        rw [hB'index, hBindex2]
      exact absurd (Subgroup.eq_of_index_dvd_index hle hdvd) hBneB'
    · exact h
  have hZle_center : B ⊓ B' ≤ Subgroup.center T := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    have hcz : Subgroup.centralizer ({z} : Set T) = ⊤ := by
      rw [eq_top_iff]
      rw [← hsup]
      apply sup_le
      · intro b hb
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact hBcomm z hz.1 b hb
      · intro b hb
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        exact hB'comm z hz.2 b hb
    have hzcenter : z ∈ Subgroup.center T :=
      Subgroup.centralizer_eq_top_iff_subset.mp hcz (Set.mem_singleton z)
    exact Subgroup.mem_center_iff.mp hzcenter g
  have hNle_center : N ≤ Subgroup.center T :=
    le_trans (le_inf hNleB hNleB') hZle_center
  have hZindex : (B ⊓ B').index ≤ 4 := by
    have h := Subgroup.index_inf_le (H := B) (K := B')
    rw [hBindex2, hB'index] at h
    have h22 : (2 : ℕ) * 2 = 4 := by decide
    rwa [h22] at h
  have hcenter_index_le : (Subgroup.center T).index ≤ 4 := by
    have hdvd : (Subgroup.center T).index ∣ (B ⊓ B').index :=
      Subgroup.index_dvd_of_le hZle_center
    have hpos : 0 < (B ⊓ B').index :=
      Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := B ⊓ B'))
    exact le_trans (Nat.le_of_dvd hpos hdvd) hZindex
  let C₀ : Subgroup E := (Subgroup.center T).map π
  have hC₀inv : ∀ x ∈ C₀, f x ∈ C₀ := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨z, hz, rfl⟩
    refine Subgroup.mem_map.mpr ⟨σ z, ?_, hσf z⟩
    rw [Subgroup.mem_center_iff]
    intro g
    have hgz : σ.symm g * z = z * σ.symm g := (Subgroup.mem_center_iff.mp hz) (σ.symm g)
    calc
      g * σ z = σ (σ.symm g) * σ z := by rw [MulEquiv.apply_symm_apply]
      _ = σ (σ.symm g * z) := by rw [← map_mul]
      _ = σ (z * σ.symm g) := by rw [hgz]
      _ = σ z * σ (σ.symm g) := by rw [map_mul]
      _ = σ z * g := by rw [MulEquiv.apply_symm_apply]
  have hC₀index_le : C₀.index ≤ 4 := by
    have hdvd : C₀.index ∣ (Subgroup.center T).index :=
      Subgroup.index_map_dvd (Subgroup.center T) hπ
    have hpos : 0 < (Subgroup.center T).index :=
      Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := Subgroup.center T))
    exact le_trans (Nat.le_of_dvd hpos hdvd) hcenter_index_le
  have hC₀mul : Nat.card C₀ * C₀.index = 8 := by
    have := Subgroup.card_mul_index C₀
    rwa [hE8] at this
  have hC₀card : 2 ≤ Nat.card C₀ := by
    have h1 : Nat.card C₀ * C₀.index ≤ Nat.card C₀ * 4 := Nat.mul_le_mul_left _ hC₀index_le
    have h2 : 8 ≤ 4 * Nat.card C₀ := by
      calc
        8 = Nat.card C₀ * C₀.index := hC₀mul.symm
        _ ≤ Nat.card C₀ * 4 := h1
        _ = 4 * Nat.card C₀ := Nat.mul_comm _ _
    have h3 : 4 * 2 ≤ 4 * Nat.card C₀ := by
      have h42 : (8 : ℕ) = 4 * 2 := by decide
      rwa [h42] at h2
    exact Nat.le_of_mul_le_mul_left h3 (by decide)
  have hC₀eq_top : C₀ = ⊤ := by
    rcases hirr C₀ hC₀inv with h | h
    · have h1 : Nat.card C₀ = 1 := by rw [h, Subgroup.card_bot]
      exact absurd (h1 ▸ hC₀card) (by decide)
    · exact h
  have hcenter_top : Subgroup.center T = ⊤ := by
    rw [eq_top_iff]
    intro t _
    have hπt : π t ∈ C₀ := by rw [hC₀eq_top]; exact Subgroup.mem_top (π t)
    rcases Subgroup.mem_map.mp hπt with ⟨z, hz, hzπ⟩
    have hmemN : t * z⁻¹ ∈ N := by
      show π (t * z⁻¹) = 1
      rw [map_mul, map_inv, hzπ, mul_inv_cancel]
    have hmemCenter : t * z⁻¹ ∈ Subgroup.center T := hNle_center hmemN
    have htz : (t * z⁻¹) * z = t := by rw [mul_assoc, inv_mul_cancel, mul_one]
    rw [← htz]
    exact mul_mem hmemCenter hz
  have hcomm : ∀ a b : T, a * b = b * a := by
    intro a b
    have ha : a ∈ Subgroup.center T := by rw [hcenter_top]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.mp ha b).symm
  exact hnotcomm hcomm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
