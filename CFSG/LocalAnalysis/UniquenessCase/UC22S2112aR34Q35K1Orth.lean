module

public import CFSG.Blueprint.Catalog
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35K1Lift
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35K1OrthB
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35K1OrthC
import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutInner

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open
open CFSG.Blueprint (LieModel)

theorem uc22s2112r34q35_alpha_omegaOdd {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p = 3 ∨ p = 5) (hX : LieModel X .POmegaOdd 3 p 1) (P : Sylow 2 X) {x : X}
    (hx : x ∈ normalizer ((P : Subgroup X) : Set X)) {s : ℕ} (hs : s.Prime) (hs7 : 7 ≤ s)
    (hs13 : s ≠ 13) : orderOf x ≠ s := by
  intro hxs
  obtain ⟨K, hField, hFinite, e, hK, he, hO, ⟨eX⟩⟩ :=
    uc22s2112r34q35_exists_model_Q7 hp hX
  let H := StatedOmega (uc22s2112r34q35_Q7 e)
  let Z := (StatedScalars (Fin 4 ⊕ Fin 3) K).subgroupOf H
  have hZ : IsPGroup 2 Z := uc22s2112r34q35_isPGroup_scalars_Q7 e
  have h2 : (2 : K) ≠ 0 := by
    have hodd : Odd (Nat.card K) := by
      rcases hK with h | h <;> rw [h] <;> norm_num
    exact Ring.two_ne_zero (CFSG.ABGLocalTools.ringChar_ne_two_of_odd_card hodd)
  obtain ⟨S, hS⟩ := uc22s2112r34q35_exists_sylow_T7 h2 e hO
  obtain ⟨h, hhs, hh1, hhN⟩ :=
    uc22s2112r34q35_exists_lift_mem_normalizer hZ eX S P hx hs (by omega) hxs
  have hSH : (S : Subgroup H).map H.subtype = uc22s2112r34q35_T (Fin 3) 0 1 K ⊓ H := hS
  have hN : ∀ g ∈ uc22s2112r34q35_T (Fin 3) 0 1 K ⊓ H,
      (h : GL (Fin 4 ⊕ Fin 3) K) * g * (h : GL (Fin 4 ⊕ Fin 3) K)⁻¹ ∈
        uc22s2112r34q35_T (Fin 3) 0 1 K ⊓ H := by
    intro g hg
    have hgS : g ∈ (S : Subgroup H).map H.subtype := by rw [hSH]; exact hg
    obtain ⟨s', hs'mem, hs'eq⟩ := Subgroup.mem_map.mp hgS
    have hmem : h * s' * h⁻¹ ∈ (S : Subgroup H) :=
      (Subgroup.mem_normalizer_iff.mp hhN s').mp hs'mem
    have hs'val : (s' : GL (Fin 4 ⊕ Fin 3) K) = g := hs'eq
    have hconj : ((h * s' * h⁻¹ : H) : GL (Fin 4 ⊕ Fin 3) K) =
        (h : GL (Fin 4 ⊕ Fin 3) K) * g * (h : GL (Fin 4 ⊕ Fin 3) K)⁻¹ := by
      simp [hs'val]
    have hmemmap : ((h * s' * h⁻¹ : H) : GL (Fin 4 ⊕ Fin 3) K) ∈
        (S : Subgroup H).map H.subtype := ⟨h * s' * h⁻¹, hmem, rfl⟩
    rw [hconj, hSH] at hmemmap
    exact hmemmap
  have hN' : ∀ g ∈ uc22s2112r34q35_T (Fin 3) 0 1 K ⊓ H,
      (h : GL (Fin 4 ⊕ Fin 3) K)⁻¹ * g * (h : GL (Fin 4 ⊕ Fin 3) K) ∈
        uc22s2112r34q35_T (Fin 3) 0 1 K ⊓ H := by
    intro g hg
    have hhN' : h⁻¹ ∈ normalizer ((S : Subgroup H) : Set H) := Subgroup.inv_mem _ hhN
    have hgS : g ∈ (S : Subgroup H).map H.subtype := by rw [hSH]; exact hg
    obtain ⟨s', hs'mem, hs'eq⟩ := Subgroup.mem_map.mp hgS
    have hmem : h⁻¹ * s' * (h⁻¹)⁻¹ ∈ (S : Subgroup H) :=
      (Subgroup.mem_normalizer_iff.mp hhN' s').mp hs'mem
    have hs'val : (s' : GL (Fin 4 ⊕ Fin 3) K) = g := hs'eq
    have hconj : ((h⁻¹ * s' * (h⁻¹)⁻¹ : H) : GL (Fin 4 ⊕ Fin 3) K) =
        (h : GL (Fin 4 ⊕ Fin 3) K)⁻¹ * g * (h : GL (Fin 4 ⊕ Fin 3) K) := by
      simp [hs'val]
    have hmemmap : ((h⁻¹ * s' * (h⁻¹)⁻¹ : H) : GL (Fin 4 ⊕ Fin 3) K) ∈
        (S : Subgroup H).map H.subtype := ⟨h⁻¹ * s' * (h⁻¹)⁻¹, hmem, rfl⟩
    rw [hconj, hSH] at hmemmap
    exact hmemmap
  have hhGL : (h : GL (Fin 4 ⊕ Fin 3) K) ^ s = 1 := by
    have := congrArg (fun z : H => (z : GL (Fin 4 ⊕ Fin 3) K)) hhs
    simpa using this
  have hgl : (h : GL (Fin 4 ⊕ Fin 3) K) = 1 :=
    uc22s2112r34q35_eq_one_of_normalizes_T7 hK he hs hs7 hs13 h.2 hhGL hN hN'
  exact hh1 (Subtype.ext hgl)

theorem uc22s2112r34q35_alpha_omegaMinus {X : Type} [Group X] [Finite X] {p : ℕ}
    (hp : p = 3 ∨ p = 5) (hX : LieModel X .POmegaMinus 4 p 1) (P : Sylow 2 X) {x : X}
    (hx : x ∈ normalizer ((P : Subgroup X) : Set X)) {s : ℕ} (hs : s.Prime) (hs7 : 7 ≤ s)
    (hs13 : s ≠ 13) : orderOf x ≠ s := by
  intro hxs
  obtain ⟨K, hField, hFinite, e, hK, he, hO, ⟨eX⟩⟩ :=
    uc22s2112r34q35_exists_model_Q8 hp hX
  let H := StatedOmega (uc22s2112r34q35_Q8 e)
  let Z := (StatedScalars (Fin 4 ⊕ Fin 4) K).subgroupOf H
  have hZ : IsPGroup 2 Z := uc22s2112r34q35_isPGroup_scalars_Q8 e
  have h2 : (2 : K) ≠ 0 := by
    have hodd : Odd (Nat.card K) := by
      rcases hK with h | h <;> rw [h] <;> norm_num
    exact Ring.two_ne_zero (CFSG.ABGLocalTools.ringChar_ne_two_of_odd_card hodd)
  obtain ⟨S, hS⟩ := uc22s2112r34q35_exists_sylow_T8 h2 e hO
  obtain ⟨h, hhs, hh1, hhN⟩ :=
    uc22s2112r34q35_exists_lift_mem_normalizer hZ eX S P hx hs (by omega) hxs
  have hSH : (S : Subgroup H).map H.subtype = uc22s2112r34q35_T (Fin 4) 0 1 K ⊓ H := hS
  have hN : ∀ g ∈ uc22s2112r34q35_T (Fin 4) 0 1 K ⊓ H,
      (h : GL (Fin 4 ⊕ Fin 4) K) * g * (h : GL (Fin 4 ⊕ Fin 4) K)⁻¹ ∈
        uc22s2112r34q35_T (Fin 4) 0 1 K ⊓ H := by
    intro g hg
    have hgS : g ∈ (S : Subgroup H).map H.subtype := by rw [hSH]; exact hg
    obtain ⟨s', hs'mem, hs'eq⟩ := Subgroup.mem_map.mp hgS
    have hmem : h * s' * h⁻¹ ∈ (S : Subgroup H) :=
      (Subgroup.mem_normalizer_iff.mp hhN s').mp hs'mem
    have hs'val : (s' : GL (Fin 4 ⊕ Fin 4) K) = g := hs'eq
    have hconj : ((h * s' * h⁻¹ : H) : GL (Fin 4 ⊕ Fin 4) K) =
        (h : GL (Fin 4 ⊕ Fin 4) K) * g * (h : GL (Fin 4 ⊕ Fin 4) K)⁻¹ := by
      simp [hs'val]
    have hmemmap : ((h * s' * h⁻¹ : H) : GL (Fin 4 ⊕ Fin 4) K) ∈
        (S : Subgroup H).map H.subtype := ⟨h * s' * h⁻¹, hmem, rfl⟩
    rw [hconj, hSH] at hmemmap
    exact hmemmap
  have hN' : ∀ g ∈ uc22s2112r34q35_T (Fin 4) 0 1 K ⊓ H,
      (h : GL (Fin 4 ⊕ Fin 4) K)⁻¹ * g * (h : GL (Fin 4 ⊕ Fin 4) K) ∈
        uc22s2112r34q35_T (Fin 4) 0 1 K ⊓ H := by
    intro g hg
    have hhN' : h⁻¹ ∈ normalizer ((S : Subgroup H) : Set H) := Subgroup.inv_mem _ hhN
    have hgS : g ∈ (S : Subgroup H).map H.subtype := by rw [hSH]; exact hg
    obtain ⟨s', hs'mem, hs'eq⟩ := Subgroup.mem_map.mp hgS
    have hmem : h⁻¹ * s' * (h⁻¹)⁻¹ ∈ (S : Subgroup H) :=
      (Subgroup.mem_normalizer_iff.mp hhN' s').mp hs'mem
    have hs'val : (s' : GL (Fin 4 ⊕ Fin 4) K) = g := hs'eq
    have hconj : ((h⁻¹ * s' * (h⁻¹)⁻¹ : H) : GL (Fin 4 ⊕ Fin 4) K) =
        (h : GL (Fin 4 ⊕ Fin 4) K)⁻¹ * g * (h : GL (Fin 4 ⊕ Fin 4) K) := by
      simp [hs'val]
    have hmemmap : ((h⁻¹ * s' * (h⁻¹)⁻¹ : H) : GL (Fin 4 ⊕ Fin 4) K) ∈
        (S : Subgroup H).map H.subtype := ⟨h⁻¹ * s' * (h⁻¹)⁻¹, hmem, rfl⟩
    rw [hconj, hSH] at hmemmap
    exact hmemmap
  have hhGL : (h : GL (Fin 4 ⊕ Fin 4) K) ^ s = 1 := by
    have := congrArg (fun z : H => (z : GL (Fin 4 ⊕ Fin 4) K)) hhs
    simpa using this
  have hgl : (h : GL (Fin 4 ⊕ Fin 4) K) = 1 :=
    uc22s2112r34q35_eq_one_of_normalizes_T8 hK he hs hs7 hs13 h.2 hhGL hN hN'
  exact hh1 (Subtype.ext hgl)

end CFSG.LocalAnalysis.UniquenessCase.UC22
