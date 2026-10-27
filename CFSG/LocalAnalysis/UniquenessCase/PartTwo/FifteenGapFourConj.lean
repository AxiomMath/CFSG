module

public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

variable {A : Type} [Group A]

theorem s15GapFour_map_conj_mul (K : Subgroup A) (a b : A) :
    K.map (MulAut.conj (a * b)).toMonoidHom =
      (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem s15GapFour_map_conj_one (K : Subgroup A) :
    K.map (MulAut.conj (1 : A)).toMonoidHom = K := by
  ext x
  simp [Subgroup.mem_map]

theorem s15GapFour_ncard_conj_le [Finite A] (M K L : Subgroup A) :
    Set.ncard {X : Subgroup A | ∃ φ ∈ M, X = K.map (MulAut.conj φ).toMonoidHom} ≤
      Set.ncard {X : Subgroup A | ∃ n ∈ M ⊓ normalizer (L : Set A),
          X = K.map (MulAut.conj n).toMonoidHom} *
        Set.ncard {X : Subgroup A | ∃ φ ∈ M, X = L.map (MulAut.conj φ).toMonoidHom} := by
  classical
  haveI : Finite (Subgroup A) := Finite.of_injective _ SetLike.coe_injective
  set 𝒦 : Set (Subgroup A) := {X | ∃ φ ∈ M, X = K.map (MulAut.conj φ).toMonoidHom} with h𝒦
  set 𝒞 : Set (Subgroup A) :=
    {X | ∃ n ∈ M ⊓ normalizer (L : Set A), X = K.map (MulAut.conj n).toMonoidHom} with h𝒞
  set 𝓛 : Set (Subgroup A) := {X | ∃ φ ∈ M, X = L.map (MulAut.conj φ).toMonoidHom} with h𝓛
  have hrep : ∀ L' ∈ 𝓛, ∃ ψ ∈ M, L' = L.map (MulAut.conj ψ).toMonoidHom := fun L' h => h
  choose! ψ hψM hψL using hrep
  have hsub : 𝒦 ⊆ (fun p : Subgroup A × Subgroup A =>
      p.1.map (MulAut.conj (ψ p.2)).toMonoidHom) '' (𝒞 ×ˢ 𝓛) := by
    rintro X ⟨φ, hφ, rfl⟩
    have hL' : L.map (MulAut.conj φ).toMonoidHom ∈ 𝓛 := ⟨φ, hφ, rfl⟩
    set ψ' := ψ (L.map (MulAut.conj φ).toMonoidHom) with hψ'
    have hψ'M : ψ' ∈ M := hψM _ hL'
    have hLeq : L.map (MulAut.conj φ).toMonoidHom = L.map (MulAut.conj ψ').toMonoidHom :=
      hψL _ hL'
    have hn : ψ'⁻¹ * φ ∈ M ⊓ normalizer (L : Set A) := by
      refine Subgroup.mem_inf.2 ⟨M.mul_mem (M.inv_mem hψ'M) hφ, ?_⟩
      have key : L.map (MulAut.conj (ψ'⁻¹ * φ)).toMonoidHom = L := by
        rw [s15GapFour_map_conj_mul, hLeq, ← s15GapFour_map_conj_mul, inv_mul_cancel,
          s15GapFour_map_conj_one]
      exact mem_normalizer_iff_map_conj_eq.2 key
    refine ⟨(K.map (MulAut.conj (ψ'⁻¹ * φ)).toMonoidHom, L.map (MulAut.conj φ).toMonoidHom),
      ⟨⟨_, hn, rfl⟩, hL'⟩, ?_⟩
    change (K.map (MulAut.conj (ψ'⁻¹ * φ)).toMonoidHom).map (MulAut.conj ψ').toMonoidHom = _
    rw [← s15GapFour_map_conj_mul, mul_inv_cancel_left]
  calc 𝒦.ncard ≤ ((fun p : Subgroup A × Subgroup A =>
        p.1.map (MulAut.conj (ψ p.2)).toMonoidHom) '' (𝒞 ×ˢ 𝓛)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (𝒞 ×ˢ 𝓛).ncard := Set.ncard_image_le (Set.toFinite _)
    _ = 𝒞.ncard * 𝓛.ncard := Set.ncard_prod

theorem s15GapFour_mem_normalizer_of_odd [Finite A] (N K : Subgroup A)
    (hcard : Set.ncard {X : Subgroup A | ∃ φ ∈ N, X = K.map (MulAut.conj φ).toMonoidHom} ≤ 2)
    {y : A} (hy : y ∈ N) {q : ℕ} (hq : Odd q) (hyq : y ^ q = 1) :
    y ∈ normalizer (K : Set A) := by
  classical
  set S : Set (Subgroup A) :=
    {X | ∃ φ ∈ N, X = K.map (MulAut.conj φ).toMonoidHom} with hS
  haveI : Finite (Subgroup A) := Finite.of_injective _ SetLike.coe_injective
  have hSfin : S.Finite := Set.toFinite S
  let c : ℕ → Subgroup A := fun n => K.map (MulAut.conj (y ^ n)).toMonoidHom
  have hcS : ∀ n, c n ∈ S := fun n => ⟨y ^ n, N.pow_mem hy n, rfl⟩
  have hcsucc : ∀ n, c (n + 1) = (c n).map (MulAut.conj y).toMonoidHom := fun n => by
    simp only [c, pow_succ']
    exact s15GapFour_map_conj_mul K y (y ^ n)
  have hc0 : c 0 = K := by
    simp only [c, pow_zero]
    exact s15GapFour_map_conj_one K
  have hc1 : c 1 = K.map (MulAut.conj y).toMonoidHom := by
    simp [c]
  have hinj : Function.Injective (Subgroup.map (MulAut.conj y).toMonoidHom) :=
    Subgroup.map_injective (MulAut.conj y).injective
  by_contra hne
  have hne' : c 1 ≠ c 0 := by
    rw [hc1, hc0]
    intro h
    exact hne (mem_normalizer_iff_map_conj_eq.2 h)
  have hc2 : c 2 = c 0 := by
    by_contra h2
    have h21 : c 2 ≠ c 1 := by
      intro h
      apply hne'
      refine hinj ?_
      rw [← hcsucc 0, ← hcsucc 1]
      exact h
    have hsub : ({c 0, c 1, c 2} : Set (Subgroup A)) ⊆ S := by
      intro X hX
      rcases hX with rfl | rfl | rfl
      · exact hcS 0
      · exact hcS 1
      · exact hcS 2
    have h3 : ({c 0, c 1, c 2} : Set (Subgroup A)).ncard = 3 :=
      Set.ncard_eq_three.2 ⟨c 0, c 1, c 2, hne'.symm, Ne.symm h2, h21.symm, rfl⟩
    have := Set.ncard_le_ncard hsub hSfin
    omega
  have hperiod : ∀ n, c (n + 2) = c n := by
    intro n
    induction n with
    | zero => exact hc2
    | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by omega, hcsucc (n + 2), ih, ← hcsucc n]
  have heven : ∀ j, c (2 * j) = c 0 := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih =>
      rw [show 2 * (j + 1) = 2 * j + 2 by omega, hperiod, ih]
  obtain ⟨j, rfl⟩ := hq
  have hcq : c (2 * j + 1) = K := by
    simp only [c, hyq]
    exact s15GapFour_map_conj_one K
  rw [hcsucc, heven, hc0] at hcq
  exact hne' (by rw [hc1, hc0]; exact hcq)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
