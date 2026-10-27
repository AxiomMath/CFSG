module

public import CFSG.LocalAnalysis.StandardType.FS81.N7MainMono
public import CFSG.LocalAnalysis.StandardType.FS81.N7MainE6
import CFSG.LocalAnalysis.StandardType.FS81.Realized

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

private theorem nmh_evenAll0_mul {A B : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    (hA : A ∈ evenAll0 7) (hB : B ∈ evenAll0 7) : A * B ∈ evenAll0 7 := by
  obtain ⟨σ, s, hs, ⟨hσ, hps⟩, rfl⟩ := hA
  obtain ⟨τ, t, ht, ⟨hτ, hpt⟩, rfl⟩ := hB
  refine ⟨σ * τ, fun j => s (τ j) * t j, ?_, ⟨?_, ?_⟩, spMat_mul σ τ s t⟩
  · intro j
    rcases hs (τ j) with h | h <;> rcases ht j with h' | h' <;>
      simp only [h, h'] <;> decide
  · show (σ * τ) 0 = 0
    rw [Equiv.Perm.mul_apply, hτ, hσ]
  · show ∏ j : Fin 8, s (τ j) * t j = 1
    rw [Finset.prod_mul_distrib, hpt, mul_one, Equiv.prod_comp τ s, hps]

private theorem nmh_evenAll0_one : (1 : Matrix (Fin 8) (Fin 8) (ZMod 3)) ∈ evenAll0 7 :=
  ⟨1, fun _ => 1, fun _ => Or.inl rfl, ⟨rfl, by simp⟩, spMat_one.symm⟩

private theorem nmh_spMat_mul_inv {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3} (hs : IsSign s) :
    spMat σ⁻¹ (fun j => s (σ⁻¹ j)) * spMat σ s = 1 := by
  rw [spMat_mul, inv_mul_cancel]
  rw [show (fun j => s (σ⁻¹ (σ j)) * s j) = (fun _ => 1) by
    funext j
    show s (σ.symm (σ j)) * s j = 1
    rw [Equiv.symm_apply_apply]
    rcases hs j with h | h <;> rw [h] <;> decide]
  exact spMat_one

private theorem nmh_eq_inv_of_mul_eq_one {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3}
    (hs : IsSign s) {h' : Matrix (Fin 8) (Fin 8) (ZMod 3)} (h : spMat σ s * h' = 1) :
    h' = spMat σ⁻¹ (fun j => s (σ⁻¹ j)) := by
  calc h' = 1 * h' := by rw [one_mul]
    _ = (spMat σ⁻¹ (fun j => s (σ⁻¹ j)) * spMat σ s) * h' := by
        rw [nmh_spMat_mul_inv hs]
    _ = spMat σ⁻¹ (fun j => s (σ⁻¹ j)) * (spMat σ s * h') := by rw [mul_assoc]
    _ = spMat σ⁻¹ (fun j => s (σ⁻¹ j)) := by rw [h, mul_one]

private theorem nmh_inv_mem {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3} (hs : IsSign s)
    (hσ : σ 0 = 0) (hps : ∏ i, s i = 1) {h' : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    (h : spMat σ s * h' = 1) : h' ∈ evenAll0 7 := by
  have hinv : h' = spMat σ⁻¹ (fun j => s (σ⁻¹ j)) := nmh_eq_inv_of_mul_eq_one hs h
  rw [hinv]
  refine ⟨σ⁻¹, fun j => s (σ⁻¹ j), fun j => hs (σ⁻¹ j), ⟨?_, ?_⟩, rfl⟩
  · show σ⁻¹ 0 = 0
    simpa [hσ] using Equiv.symm_apply_apply σ 0
  · show ∏ j : Fin 8, s (σ⁻¹ j) = 1
    rw [Equiv.prod_comp σ⁻¹ s, hps]

private theorem nmh_nmF1_mulVec_e0 {M : Matrix (Fin 8) (Fin 8) (ZMod 3)} (hM : M ∈ nmF1) :
    M *ᵥ nmE0 = nmE0 := by
  obtain ⟨A, h0, -, rfl⟩ := hM
  exact nmSgn_mulVec_single_of_notMem h0

private theorem nmh_exists_ne_zero_ne (i : Fin 8) :
    ∃ j : Fin 8, j ≠ 0 ∧ j ≠ i := by
  by_cases h : i = 1
  · exact ⟨2, by decide, by rw [h]; decide⟩
  · exact ⟨1, by decide, fun hji => h (hji.symm)⟩

private theorem nmh_conj_nmSgn {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3} (hs : IsSign s)
    {A : Finset (Fin 8)} {h' : Matrix (Fin 8) (Fin 8) (ZMod 3)}
    (h : spMat σ s * h' = 1) : spMat σ s * nmSgn A * h' = nmSgn (A.image σ) := by
  rw [nmh_eq_inv_of_mul_eq_one hs h]
  have hd : nmSgn A =
      spMat (1 : Equiv.Perm (Fin 8)) (fun i => if i ∈ A then -1 else 1) := by
    ext i j
    by_cases hij : i = j <;> simp [nmSgn, spMat_apply, hij]
  rw [hd]
  rw [spMat_mul, spMat_mul, mul_one, mul_inv_cancel]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [spMat_apply, if_true, nmSgn, Matrix.diagonal_apply]
    have hmem : σ⁻¹ i ∈ A ↔ i ∈ A.image σ := by
      constructor
      · intro hi
        exact Finset.mem_image.mpr ⟨σ⁻¹ i, hi, Equiv.apply_symm_apply σ i⟩
      · intro hi
        obtain ⟨x, hx, hxj⟩ := Finset.mem_image.mp hi
        have hx_eq : σ⁻¹ i = x := by
          rw [← hxj]
          simp
        rwa [hx_eq]
    simp only [hmem]
    by_cases hAi : i ∈ A.image σ
    · simp only [if_pos hAi]
      rcases hs (σ.symm i) with hsign | hsign
      · simp [hsign]
      · simp [hsign]
        decide
    · simp only [if_neg hAi]
      rcases hs (σ.symm i) with hsign | hsign
      · simp [hsign]
      · simp [hsign]
        decide
  · simp [spMat_apply, nmSgn, hij]

namespace N7MSetup

variable {X : Type} [Group X] [Finite X] (S : N7MSetup X)

@[expose] def H1grp : Subgroup X where
  carrier := {x | S.ρ x ∈ evenAll0 7}
  mul_mem' := by
    intro x y hx hy
    show S.ρ (x * y) ∈ evenAll0 7
    rw [map_mul]
    exact nmh_evenAll0_mul hx hy
  one_mem' := by
    show S.ρ 1 ∈ evenAll0 7
    rw [map_one]
    exact nmh_evenAll0_one
  inv_mem' := by
    intro x hx
    obtain ⟨σ, s, hs, ⟨hσ, hps⟩, hA⟩ := hx
    have hleft : spMat σ s * S.ρ x⁻¹ = 1 := by
      rw [← hA, ← map_mul, mul_inv_cancel, map_one]
    show S.ρ x⁻¹ ∈ evenAll0 7
    exact nmh_inv_mem hs hσ hps hleft

@[expose] def F1grp : Subgroup X where
  carrier := {x | S.ρ x ∈ nmF1}
  mul_mem' := by
    intro x y hx hy
    show S.ρ (x * y) ∈ nmF1
    rw [map_mul]
    exact nmF1_mul hx hy
  one_mem' := by
    show S.ρ 1 ∈ nmF1
    rw [map_one]
    exact nmF1_one
  inv_mem' := by
    intro x hx
    obtain ⟨A, h0, he, hA⟩ := hx
    have hsq : S.ρ x * S.ρ x = 1 := nmF_sq (nmF1_subset_nmF ⟨A, h0, he, hA⟩)
    have hinv : S.ρ x⁻¹ = S.ρ x := by
      calc S.ρ x⁻¹ = (S.ρ x * S.ρ x) * S.ρ x⁻¹ := by rw [hsq, one_mul]
        _ = S.ρ x * (S.ρ x * S.ρ x⁻¹) := by rw [mul_assoc]
        _ = S.ρ x := by
            rw [show S.ρ x * S.ρ x⁻¹ = 1 from by
              rw [← map_mul, mul_inv_cancel, map_one], mul_one]
    show S.ρ x⁻¹ ∈ nmF1
    rw [hinv]
    exact ⟨A, h0, he, hA⟩

@[expose] def Weak : Prop :=
  ∀ x g : X, S.ρ x ∈ nmE6 → S.ρ (g * x * g⁻¹) ∈ evenAll0 7 → S.ρ (g * x * g⁻¹) ∈ nmE6

theorem mem_H1grp (x : X) : x ∈ S.H1grp ↔ S.ρ x ∈ evenAll0 7 := Iff.rfl

theorem mem_F1grp (x : X) : x ∈ S.F1grp ↔ S.ρ x ∈ nmF1 := Iff.rfl

theorem F1grp_le_H1grp : S.F1grp ≤ S.H1grp :=
  fun _ hx => nmF_subset_evenAll0 (nmF1_subset_nmF hx)

theorem H1grp_le_FKgrp : S.H1grp ≤ S.FKgrp := fun _ hx => evenAll0_subset_nmFK hx

theorem F1grp_comm : IsMulCommutative S.F1grp := by
  refine ⟨⟨fun a b => ?_⟩⟩
  refine Subtype.ext (S.ρ_inj ?_)
  show S.ρ (a.1 * b.1) = S.ρ (b.1 * a.1)
  rw [map_mul, map_mul]
  exact nmF_comm (nmF1_subset_nmF a.2) (nmF1_subset_nmF b.2)

theorem conj_mem_F1grp {h : X} (hh : h ∈ S.H1grp) {f : X} (hf : f ∈ S.F1grp) :
    h * f * h⁻¹ ∈ S.F1grp := by
  obtain ⟨A, hA0, hAeven, hAf⟩ := hf
  obtain ⟨σ, s, hs, ⟨hσ0, -⟩, hsp⟩ := hh
  have hleft : spMat σ s * S.ρ h⁻¹ = 1 := by
    rw [← hsp, ← map_mul, mul_inv_cancel, map_one]
  refine ⟨A.image σ, ?_, ?_, ?_⟩
  · simp only [Finset.mem_image]
    rintro ⟨x, hx, hx0⟩
    exact hA0 (by
      have hx_eq : x = 0 := σ.injective (by rw [hx0, hσ0])
      rw [hx_eq] at hx
      exact hx)
  · rw [Finset.card_image_of_injective _ σ.injective]
    exact hAeven
  · rw [map_mul, map_mul, hsp, hAf]
    exact nmh_conj_nmSgn hs hleft

private theorem nmh_fixed_of_conj {x : X}
    (hiff : ∀ a, a ∈ S.F1grp ↔ x * a * x⁻¹ ∈ S.F1grp) :
    ∀ f ∈ S.F1grp, S.ρ f *ᵥ (S.ρ x *ᵥ nmE0) = S.ρ x *ᵥ nmE0 := by
  intro f hf
  have ha : x⁻¹ * f * x ∈ S.F1grp := by
    refine (hiff (x⁻¹ * f * x)).2 ?_
    rw [show x * (x⁻¹ * f * x) * x⁻¹ = f from by group]
    exact hf
  have hfix : S.ρ (x⁻¹ * f * x) *ᵥ nmE0 = nmE0 := nmh_nmF1_mulVec_e0 ha
  calc S.ρ f *ᵥ (S.ρ x *ᵥ nmE0)
      = (S.ρ f * S.ρ x) *ᵥ nmE0 := by rw [Matrix.mulVec_mulVec]
    _ = S.ρ (f * x) *ᵥ nmE0 := by rw [map_mul]
    _ = S.ρ (x * (x⁻¹ * f * x)) *ᵥ nmE0 := by
        rw [show f * x = x * (x⁻¹ * f * x) from by group]
    _ = (S.ρ x * S.ρ (x⁻¹ * f * x)) *ᵥ nmE0 := by rw [map_mul]
    _ = S.ρ x *ᵥ (S.ρ (x⁻¹ * f * x) *ᵥ nmE0) := by rw [Matrix.mulVec_mulVec]
    _ = S.ρ x *ᵥ nmE0 := by rw [hfix]

private theorem nmh_eq_smul_e0 {u : Coords 8}
    (hu : ∀ f ∈ S.F1grp, S.ρ f *ᵥ u = u) : ∃ c : ZMod 3, u = c • nmE0 := by
  have hzero : ∀ i : Fin 8, i ≠ 0 → u i = 0 := by
    intro i hi
    obtain ⟨j, hj0, hji⟩ := nmh_exists_ne_zero_ne i
    have h0 : (0 : Fin 8) ∉ ({i, j} : Finset (Fin 8)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hi h.symm, fun h => hj0 h.symm⟩
    have hcard : ({i, j} : Finset (Fin 8)).card = 2 := Finset.card_pair (Ne.symm hji)
    have hmem : nmSgn ({i, j} : Finset (Fin 8)) ∈ nmF1 :=
      ⟨_, h0, by rw [hcard]; exact even_two, rfl⟩
    obtain ⟨f, hfρ⟩ := S.exists_of_mem_nmF (nmF1_subset_nmF hmem)
    have hfF1 : f ∈ S.F1grp := by
      rw [S.mem_F1grp, hfρ]
      exact hmem
    have hfixv : nmSgn ({i, j} : Finset (Fin 8)) *ᵥ u = u := by
      have hv := hu f hfF1
      rwa [hfρ] at hv
    have hcoord := congrFun hfixv i
    rw [nmSgn_mulVec] at hcoord
    have hnegi : -u i = u i := by
      simpa [Finset.mem_insert, Finset.mem_singleton] using hcoord
    exact (by decide : ∀ a : ZMod 3, -a = a → a = 0) (u i) hnegi
  refine ⟨u 0, ?_⟩
  funext i
  by_cases hi : i = 0
  · subst hi
    simp [nmE0]
  · have hui : u i = 0 := hzero i hi
    simp [nmE0, hui, hi]

end N7MSetup

theorem nm_normalizer_F1 {X : Type} [Group X] [Finite X] (S : N7MSetup X) {x : X} :
    (∀ a, a ∈ S.F1grp ↔ x * a * x⁻¹ ∈ S.F1grp) ↔ x ∈ S.H1grp := by
  constructor
  · intro hiff
    obtain ⟨c, hc⟩ := N7MSetup.nmh_eq_smul_e0 S (N7MSetup.nmh_fixed_of_conj S hiff)
    exact (S.mem_H1grp x).2 ((S.norm_iff x).1 ⟨c, hc⟩)
  · intro hx a
    constructor
    · intro ha
      exact S.conj_mem_F1grp hx ha
    · intro ha
      have hx' : x⁻¹ ∈ S.H1grp := S.H1grp.inv_mem hx
      have hconj : x⁻¹ * (x * a * x⁻¹) * (x⁻¹)⁻¹ ∈ S.F1grp := S.conj_mem_F1grp hx' ha
      rwa [show x⁻¹ * (x * a * x⁻¹) * (x⁻¹)⁻¹ = a from by group] at hconj

theorem nm_card_le_of_F1_normal {X : Type} [Group X] [Finite X] (S : N7MSetup X)
    (hN : S.F1grp.Normal) : Nat.card X ≤ 2 ^ 8 * Nat.factorial 8 := by
  have hmem : ∀ x : X, x ∈ S.H1grp := by
    intro x
    refine (nm_normalizer_F1 S).1 ?_
    intro a
    constructor
    · intro ha
      exact hN.conj_mem a ha x
    · intro ha
      have hconj := hN.conj_mem (x * a * x⁻¹) ha x⁻¹
      rwa [show x⁻¹ * (x * a * x⁻¹) * (x⁻¹)⁻¹ = a from by group] at hconj
  let f : X → ↥(evenAll0 7) := fun x => ⟨S.ρ x, hmem x⟩
  have hf : Function.Injective f := by
    intro x y hxy
    exact S.ρ_inj (congrArg Subtype.val hxy)
  calc Nat.card X ≤ Nat.card ↥(evenAll0 7) := Nat.card_le_card_of_injective f hf
    _ ≤ 2 ^ 8 * Nat.factorial 8 := card_spSet_le 8 _

end CFSG.StandardType.FrameRoute.FS81

end
