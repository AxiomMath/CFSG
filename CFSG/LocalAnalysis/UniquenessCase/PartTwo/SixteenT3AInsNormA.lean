module

public import CFSG.Quasithin.Background.A1bPGroups
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenT3AInsConj
public import CFSG.LocalAnalysis.StandardType.ElementaryAbelianNineLines

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped Pointwise

private theorem s16t_a_card {p n : ℕ} {P : Type} [Group P] (h : IsElemAbelianOfRank p n P) :
    Nat.card P = p ^ n := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
    Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem s16t_a_rank_comm_pow {p n : ℕ} {P : Type} [Group P]
    (h : IsElemAbelianOfRank p n P) :
    (∀ a b : P, a * b = b * a) ∧ ∀ a : P, a ^ p = 1 := by
  obtain ⟨e⟩ := h
  refine ⟨fun a b => e.injective ?_, fun a => e.injective ?_⟩
  · rw [map_mul, map_mul, mul_comm]
  · rw [map_pow, map_one]
    ext i
    simp

theorem s16t_a_exists_stable_line {Γ : Type} [Group Γ] {Λ Λ₀ B : Subgroup Γ}
    (hΛ : IsElemAbelianOfRank 3 2 ↥Λ) (hΛ₀ : Λ₀ ≤ Λ) (hcard₀ : Nat.card Λ₀ = 3)
    (hB : IsPGroup 2 ↥B) (hBΛ : ∀ b ∈ B, ∀ f ∈ Λ, b * f * b⁻¹ ∈ Λ)
    (hBΛ₀ : ∀ b ∈ B, ∀ f ∈ Λ₀, b * f * b⁻¹ ∈ Λ₀) :
    ∃ a ∈ Λ, a ∉ Λ₀ ∧ orderOf a = 3 ∧ ∀ b ∈ B, b * a * b⁻¹ ∈ Subgroup.zpowers a := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite ↥Λ₀ := Nat.finite_of_card_ne_zero (by rw [hcard₀]; norm_num)
  have hcardΛ : Nat.card ↥Λ = 9 := by simpa using s16t_a_card hΛ
  have hcommΛ : ∀ u v : ↥Λ, u * v = v * u := (s16t_a_rank_comm_pow hΛ).1
  have hexpΛ : ∀ u : ↥Λ, u ^ 3 = 1 := (s16t_a_rank_comm_pow hΛ).2
  have hexp : ∀ f ∈ Λ, f ^ 3 = 1 := by
    intro f hf
    have h := hexpΛ ⟨f, hf⟩
    simpa using congrArg Subtype.val h
  obtain ⟨x, y, hx1, hy, hgen⟩ :=
    CFSG.StandardType.ElementaryAbelianNine.exists_generators hcommΛ hexpΛ hcardΛ
  let lineΓ : Fin 4 → Subgroup Γ :=
    fun k => (CFSG.StandardType.ElementaryAbelianNine.line x y k).map Λ.subtype
  have hline_inj : Function.Injective lineΓ := by
    intro i j hij
    have hmap : CFSG.StandardType.ElementaryAbelianNine.line x y i =
        CFSG.StandardType.ElementaryAbelianNine.line x y j :=
      (Subgroup.map_injective Λ.subtype_injective) hij
    exact (CFSG.StandardType.ElementaryAbelianNine.line_injective hcommΛ hexpΛ hx1 hy) hmap
  have hline_card : ∀ k, Nat.card ↥(lineΓ k) = 3 := by
    intro k
    show Nat.card ↥((CFSG.StandardType.ElementaryAbelianNine.line x y k).map Λ.subtype) = 3
    rw [Subgroup.card_map_of_injective Λ.subtype_injective]
    exact CFSG.StandardType.ElementaryAbelianNine.card_line hexpΛ hx1 hy k
  have hline_le : ∀ k, lineΓ k ≤ Λ := fun k => Subgroup.map_subtype_le _
  have hsub : ∀ H : Subgroup Γ, H ≤ Λ → Nat.card ↥H = 3 → H ∈ Set.range lineΓ := by
    intro H hH hHc
    let H' : Subgroup ↥Λ := H.comap Λ.subtype
    have hH'map : H'.map Λ.subtype = H :=
      Subgroup.map_comap_eq_self (by rwa [Subgroup.range_subtype])
    have hH'card : Nat.card ↥H' = 3 := by
      have h1 : Nat.card ↥(H'.map Λ.subtype) = Nat.card ↥H' :=
        Subgroup.card_map_of_injective Λ.subtype_injective
      rw [hH'map, hHc] at h1
      exact h1.symm
    obtain ⟨k, hk⟩ := CFSG.StandardType.ElementaryAbelianNine.exists_line_eq
      hcommΛ hexpΛ hgen hH'card
    refine ⟨k, ?_⟩
    show (CFSG.StandardType.ElementaryAbelianNine.line x y k).map Λ.subtype = H
    rw [← hk]
    exact hH'map
  let T : Set (Subgroup Γ) := {H | H ≤ Λ ∧ Nat.card ↥H = 3}
  have hT : T = Set.range lineΓ := by
    ext H
    constructor
    · intro hH
      have hH' : H ≤ Λ ∧ Nat.card ↥H = 3 := hH
      exact hsub H hH'.1 hH'.2
    · rintro ⟨k, rfl⟩
      exact ⟨hline_le k, hline_card k⟩
  have hTcard : T.ncard = 4 := by
    rw [hT, Set.ncard_range_of_injective hline_inj]
    simp
  let Ω : Set (Subgroup Γ) := {H | H ≤ Λ ∧ Nat.card ↥H = 3 ∧ H ≠ Λ₀}
  have hΩeq : Ω = T \ {Λ₀} := by
    ext H
    simp only [Ω, T, Set.mem_sdiff, Set.mem_singleton_iff, Set.mem_setOf_eq]
    tauto
  have hΛ₀T : Λ₀ ∈ T := by
    change Λ₀ ≤ Λ ∧ Nat.card ↥Λ₀ = 3
    exact ⟨hΛ₀, hcard₀⟩
  have hΩncard : Ω.ncard = 3 := by
    rw [hΩeq, Set.ncard_sdiff_singleton_of_mem hΛ₀T, hTcard]
  have hΩcard : Nat.card ↥Ω = 3 := by
    rw [Nat.card_coe_set_eq]
    exact hΩncard
  have hΩstable : ∀ b ∈ B, ∀ H ∈ Ω, H.map (MulAut.conj b).toMonoidHom ∈ Ω := by
    intro b hb H hH
    have hH' : H ≤ Λ ∧ Nat.card ↥H = 3 ∧ H ≠ Λ₀ := hH
    obtain ⟨hHle, hHcard, hHne⟩ := hH'
    refine ⟨?_, ?_, ?_⟩
    · intro z hz
      obtain ⟨w, hw, hwz⟩ := Subgroup.mem_map.mp hz
      rw [← hwz]
      simpa [MulAut.conj_apply] using hBΛ b hb w (hHle hw)
    · rw [Subgroup.card_map_of_injective (MulAut.conj b).injective, hHcard]
    · intro hconj
      apply hHne
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · intro z hz
        have hz' : b * z * b⁻¹ ∈ Λ₀ := by
          have hmem : b * z * b⁻¹ ∈ H.map (MulAut.conj b).toMonoidHom :=
            Subgroup.mem_map.mpr ⟨z, hz, by simp [MulAut.conj_apply]⟩
          rwa [hconj] at hmem
        have h2 := hBΛ₀ b⁻¹ (B.inv_mem hb) (b * z * b⁻¹) hz'
        convert h2 using 1
        group
      · simp [hcard₀, hHcard]
  obtain ⟨H, hHΩ, hHfix⟩ :=
    s16t_a_exists_conj_stable_set hB hΩstable (by rw [hΩcard]; exact ⟨1, rfl⟩)
  have hH' : H ≤ Λ ∧ Nat.card ↥H = 3 ∧ H ≠ Λ₀ := hHΩ
  obtain ⟨hHle, hHcard, hHne⟩ := hH'
  haveI : Finite ↥H := Nat.finite_of_card_ne_zero (by rw [hHcard]; norm_num)
  obtain ⟨g, hg⟩ := (isCyclic_of_prime_card (p := 3) hHcard).exists_generator
  let a : Γ := (g : Γ)
  have hmemH : a ∈ H := g.2
  have hH_eq : H = Subgroup.zpowers a := by
    refine le_antisymm ?_ ?_
    · intro z hz
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨z, hz⟩)
      have hn' : (z : Γ) = a ^ n := by
        have h := congrArg Subtype.val hn
        simpa [a] using h.symm
      rw [hn']
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩
    · rw [Subgroup.zpowers_le]
      exact hmemH
  refine ⟨a, hHle hmemH, ?_, ?_, ?_⟩
  · intro has
    apply hHne
    have hle : H ≤ Λ₀ := by
      rw [hH_eq]
      exact Subgroup.zpowers_le.mpr has
    exact Subgroup.eq_of_le_of_card_ge hle (by simp [hcard₀, hHcard])
  · have h1 : Nat.card ↥(Subgroup.zpowers a) = orderOf a := Nat.card_zpowers a
    rw [← hH_eq, hHcard] at h1
    exact h1.symm
  · intro b hb
    have hmem : b * a * b⁻¹ ∈ H.map (MulAut.conj b).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨a, hmemH, by simp [MulAut.conj_apply]⟩
    rw [hHfix b hb] at hmem
    rwa [hH_eq] at hmem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
