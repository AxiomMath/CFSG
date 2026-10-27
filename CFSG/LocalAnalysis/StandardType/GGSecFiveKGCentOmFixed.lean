module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentOmCorank

import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentOmTorus

public section

namespace CFSG.StandardType.KGCentOm

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin

open Classical in
private noncomputable def kgcWt {K : Type} [Field K] {α : Type*} (L : Set α) (ξ₀ ξ : α → K)
    (ζ : Kˣ) : Kˣ :=
  if ∀ σ ∈ L, ξ σ = ξ₀ σ then ζ else if ∀ σ ∈ L, ξ σ * ξ₀ σ = 1 then ζ⁻¹ else 1

private theorem kgcWt_self {K : Type} [Field K] {α : Type*} {L : Set α} {ξ₀ : α → K} {ζ : Kˣ} :
    kgcWt L ξ₀ ξ₀ ζ = ζ :=
  if_pos fun _ _ => rfl

private theorem kgcWt_of_not {K : Type} [Field K] {α : Type*} {L : Set α} {ξ₀ ξ : α → K} {ζ : Kˣ}
    (hA : ¬ ∀ σ ∈ L, ξ σ = ξ₀ σ) (hB : ¬ ∀ σ ∈ L, ξ σ * ξ₀ σ = 1) : kgcWt L ξ₀ ξ ζ = 1 := by
  rw [kgcWt, if_neg hA, if_neg hB]

private theorem kgcWt_pow {K : Type} [Field K] {α : Type*} {L : Set α} {ξ₀ ξ : α → K} {ζ : Kˣ}
    {p : ℕ} (hζ : ζ ^ p = 1) : kgcWt L ξ₀ ξ ζ ^ p = 1 := by
  unfold kgcWt
  split_ifs
  · exact hζ
  · rw [inv_pow, hζ, inv_one]
  · exact one_pow p

private theorem kgcWt_mul_eq_one {K : Type} [Field K] {α : Type*} {L : Set α} {ξ₀ ξ ξ' : α → K}
    (ζ : Kˣ) (h₀ : ¬ ∀ σ ∈ L, ξ₀ σ * ξ₀ σ = 1) (h : ∀ σ ∈ L, ξ σ * ξ' σ = 1) :
    kgcWt L ξ₀ ξ ζ * kgcWt L ξ₀ ξ' ζ = 1 := by
  by_cases hA : ∀ σ ∈ L, ξ σ = ξ₀ σ
  · have hB' : ∀ σ ∈ L, ξ' σ * ξ₀ σ = 1 := fun σ hσ => by
      rw [← hA σ hσ, mul_comm]
      exact h σ hσ
    have hA' : ¬ ∀ σ ∈ L, ξ' σ = ξ₀ σ := fun hA' => h₀ fun σ hσ => by
      have h1 := hB' σ hσ
      rwa [hA' σ hσ] at h1
    unfold kgcWt
    rw [if_pos hA, if_neg hA', if_pos hB', mul_inv_cancel]
  · by_cases hB : ∀ σ ∈ L, ξ σ * ξ₀ σ = 1
    · have hA' : ∀ σ ∈ L, ξ' σ = ξ₀ σ := fun σ hσ => by
        rw [eq_inv_of_mul_eq_one_right (h σ hσ), eq_inv_of_mul_eq_one_right (hB σ hσ)]
      unfold kgcWt
      rw [if_neg hA, if_pos hB, if_pos hA', inv_mul_cancel]
    · have hA' : ¬ ∀ σ ∈ L, ξ' σ = ξ₀ σ := fun hA' => hB fun σ hσ => by
        rw [← hA' σ hσ]
        exact h σ hσ
      have hB' : ¬ ∀ σ ∈ L, ξ' σ * ξ₀ σ = 1 := fun hB' => hA fun σ hσ => by
        rw [eq_inv_of_mul_eq_one_left (h σ hσ), eq_inv_of_mul_eq_one_right (hB' σ hσ)]
      unfold kgcWt
      rw [if_neg hA, if_neg hB, if_neg hA', if_neg hB', mul_one]

private theorem exists_mem_kgcTorusSet_cls {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hn : 3 ≤ n) {G : Type*} [Group G] {p : ℕ} {D : Subgroup G} {ψ : spinGroup (quadPlus n K) →* G}
    (hψ : Function.Injective ψ) (hL : kgcLiftSet ψ D ⊆ kgcTorusSet hn ψ D p) {i₀ : Fin n}
    (hi₀ : ¬ KGCFixedIdx hn (kgcLiftSet ψ D) i₀) :
    ∃ x ∈ kgcTorusSet hn ψ D p, kgcDiag x (.inl i₀) ≠ 1 ∧ ∀ m,
      (¬ ∀ σ ∈ kgcLiftSet ψ D, kgcDiag σ m = kgcDiag σ (.inl i₀)) →
      (¬ ∀ σ ∈ kgcLiftSet ψ D, kgcDiag σ m * kgcDiag σ (.inl i₀) = 1) → kgcDiag x m = 1 := by
  have hLT : kgcLiftSet ψ D ⊆ ggTorus (plusDatum n K hn) := fun σ hσ => (hL hσ).1
  obtain ⟨σ₀, hσ₀L, hσ₀⟩ : ∃ σ ∈ kgcLiftSet ψ D, kgcDiag σ (.inl i₀) ≠ 1 := by
    by_contra h
    push Not at h
    exact hi₀ ((kgcFixedIdx_iff hn hLT i₀ true).2 h)
  have h0 : kgcDiag σ₀ (.inl i₀) ≠ 0 :=
    left_ne_zero_of_mul_eq_one (kgcDiag_inl_mul_inr hn (hLT hσ₀L) i₀)
  obtain ⟨ζ, hζv⟩ : ∃ ζ : Kˣ, (ζ : K) = kgcDiag σ₀ (.inl i₀) := ⟨Units.mk0 _ h0, rfl⟩
  have hζ : ζ ^ p = 1 := Units.ext (by
    rw [Units.val_pow_eq_pow_val, hζv, ← kgcDiag_pow hn (hLT hσ₀L), (hL hσ₀L).2.1, kgcDiag_one,
      Units.val_one])
  have h₀ : ¬ ∀ σ ∈ kgcLiftSet ψ D, kgcDiag σ (.inl i₀) * kgcDiag σ (.inl i₀) = 1 := fun h => by
    rcases mul_self_eq_one_iff.mp (h σ₀ hσ₀L) with h1 | h1
    · exact hσ₀ h1
    · exact hσ₀ (by rw [h1, CharTwo.neg_eq])
  let W : Fin n ⊕ Fin n → Kˣ := fun m =>
    kgcWt (kgcLiftSet ψ D) (kgcDiag · (.inl i₀)) (kgcDiag · m) ζ
  have hW : ∀ {m m'}, (∀ σ ∈ kgcLiftSet ψ D, kgcDiag σ m * kgcDiag σ m' = 1) →
      W m * W m' = 1 := fun h => kgcWt_mul_eq_one ζ h₀ h
  have hWp : ∀ m, W m ^ p = 1 := fun _ => kgcWt_pow hζ
  obtain ⟨x, hxT, hxv⟩ := exists_mem_ggTorus_vec_eq_smul hn fun k => W (.inl k)
  have hxW : ∀ m, kgcDiag x m = W m := by
    rintro (k | k)
    · exact kgcDiag_eq_of_smul hn (hxv k).1
    · rw [eq_inv_of_mul_eq_one_right (hW fun σ hσ => kgcDiag_inl_mul_inr hn (hLT hσ) k),
        Units.val_inv_eq_inv_val]
      exact kgcDiag_eq_of_smul hn (hxv k).2
  refine ⟨x, mem_kgcTorusSet_of_kgcDiag hn hψ hLT hxT
    (pow_eq_one_of_kgcDiag hn hxT fun k => by
      rw [hxW, ← Units.val_pow_eq_pow_val, hWp, Units.val_one])
    fun _ s t h => by rw [hxW, hxW, ← Units.val_mul, hW h, Units.val_one], ?_, fun m hA hB => ?_⟩
  · rw [hxW, show W (.inl i₀) = ζ from kgcWt_self, hζv]
    exact hσ₀
  · rw [hxW, show W m = 1 from kgcWt_of_not hA hB, Units.val_one]

private theorem not_sq_le_self_of_prime {p : ℕ} (hp : p.Prime) : ¬ p ^ 2 ≤ p := by
  have := hp.two_le
  intro h
  nlinarith

theorem not_existsUnique_fixed_index_of_ncard {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hn : 3 ≤ n) {G : Type*}
    [Group G] {p : ℕ} (hp : p.Prime) {D : Subgroup G} {ψ : spinGroup (quadPlus n K) →* G}
    (hψ : Function.Injective ψ) (hDp : ∀ d ∈ D, d ^ p = 1)
    (hlift : ∀ d ∈ D, ∃ s ∈ ggTorus (plusDatum n K hn), ∀ u, d * ψ u * d⁻¹ = ψ (s * u * s⁻¹))
    (hKC2' : Set.ncard (kgcTorusSet hn ψ D p) ≤ p) :
    ¬ ∃! i : Fin n, KGCFixedIdx hn (kgcLiftSet ψ D) i := by
  rintro ⟨i₀, hi₀, huniq⟩
  have hL := kgcLiftSet_subset_kgcTorusSet hn hψ hDp hlift
  have hLT : kgcLiftSet ψ D ⊆ ggTorus (plusDatum n K hn) := fun σ hσ => (hL hσ).1
  obtain ⟨j, hji, -⟩ := exists_ne_and_ne hn i₀ i₀
  obtain ⟨σ, hσL, hσj⟩ : ∃ σ ∈ kgcLiftSet ψ D, kgcDiag σ (.inl j) ≠ 1 := by
    by_contra h
    push Not at h
    exact hji (huniq j ((kgcFixedIdx_iff hn hLT j true).2 h))
  have hζ0 : kgcDiag σ (.inl j) ≠ 0 :=
    left_ne_zero_of_mul_eq_one (kgcDiag_inl_mul_inr hn (hLT hσL) j)
  obtain ⟨x, hxT, hxv⟩ := exists_mem_ggTorus_vec_eq_smul hn (Pi.mulSingle i₀ (Units.mk0 _ hζ0))
  have hx1 : ∀ k ≠ i₀, ∀ r, kgcDiag x (kgcIdx k r) = 1 := by
    intro k hk r
    cases r
    · rw [kgcDiag_eq_of_smul hn (hxv k).2, Pi.mulSingle_eq_of_ne hk, Units.val_one, inv_one]
    · rw [kgcDiag_eq_of_smul hn (hxv k).1, Pi.mulSingle_eq_of_ne hk, Units.val_one]
  have hxi₀ : kgcDiag x (.inl i₀) = kgcDiag σ (.inl j) := by
    rw [show (Sum.inl i₀ : Fin n ⊕ Fin n) = kgcIdx i₀ true from rfl,
      kgcDiag_eq_of_smul hn (hxv i₀).1, Pi.mulSingle_eq_same, Units.val_mk0]
  have hne : ∀ {a b : Fin n} {s t : Bool}, a ≠ b →
      (∀ τ ∈ kgcLiftSet ψ D, kgcDiag τ (kgcIdx a s) * kgcDiag τ (kgcIdx b t) = 1) → a ≠ i₀ := by
    intro a b s t hab h ha
    refine hab (ha.trans (huniq b ((kgcFixedIdx_iff hn hLT b t).2 fun τ hτ => ?_)).symm)
    have h1 := h τ hτ
    rwa [ha, (kgcFixedIdx_iff hn hLT i₀ s).1 hi₀ τ hτ, one_mul] at h1
  have hxT0 : x ∈ kgcTorusSet hn ψ D p := by
    refine mem_kgcTorusSet_of_kgcDiag hn hψ hLT hxT (pow_eq_one_of_kgcDiag hn hxT fun k => ?_)
      fun hab s t h => ?_
    · by_cases hk : k = i₀
      · rw [hk, hxi₀, ← kgcDiag_pow hn (hLT hσL), (hL hσL).2.1, kgcDiag_one]
      · rw [show kgcDiag x (.inl k) = 1 from hx1 k hk true, one_pow]
    · rw [hx1 _ (hne hab h) s, hx1 _ (hne (s := t) (t := s) hab.symm fun τ hτ => by
        rw [mul_comm]
        exact h τ hτ) t, mul_one]
  exact not_sq_le_self_of_prime hp ((sq_le_ncard_kgcTorusSet hn hp hxT0 (hL hσL)
    (m₁ := .inl i₀) (m₂ := .inl j) (by rw [hxi₀]; exact hσj) (hx1 j hji true)
    ((kgcFixedIdx_iff hn hLT i₀ true).1 hi₀ σ hσL) hσj).trans hKC2')

theorem exists_longRoot_centralized_of_ncard {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hn : 3 ≤ n) {G : Type*}
    [Group G] {p : ℕ} (hp : p.Prime) {D : Subgroup G} {ψ : spinGroup (quadPlus n K) →* G}
    (hψ : Function.Injective ψ) (hDp : ∀ d ∈ D, d ^ p = 1)
    (hlift : ∀ d ∈ D, ∃ s ∈ ggTorus (plusDatum n K hn), ∀ u, d * ψ u * d⁻¹ = ψ (s * u * s⁻¹))
    (hKC2' : Set.ncard (kgcTorusSet hn ψ D p) ≤ p) {i j : Fin n} (hij : i ≠ j)
    (hi : ¬ KGCFixedIdx hn (kgcLiftSet ψ D) i) (hj : ¬ KGCFixedIdx hn (kgcLiftSet ψ D) j) :
    ∃ s t : Bool, ∀ b : K, ψ ((plusFrame n K hn).longRoot hij s t (.ofAdd b)) ∈
      Subgroup.centralizer (D : Set G) := by
  have hL := kgcLiftSet_subset_kgcTorusSet hn hψ hDp hlift
  have hLT : kgcLiftSet ψ D ⊆ ggTorus (plusDatum n K hn) := fun σ hσ => (hL hσ).1
  by_contra hno
  have hc : ∀ s t : Bool,
      ¬ ∀ σ ∈ kgcLiftSet ψ D, kgcDiag σ (kgcIdx i s) * kgcDiag σ (kgcIdx j t) = 1 :=
    fun s t h => hno ⟨s, t, mem_centralizer_longRoot_of_kgcDiag hn hlift hij s t h⟩
  have hne1 : ¬ ∀ σ ∈ kgcLiftSet ψ D, kgcDiag σ (.inl j) = kgcDiag σ (.inl i) := fun h =>
    hc true false fun σ hσ => by
      show kgcDiag σ (.inl i) * kgcDiag σ (.inr j) = 1
      rw [← h σ hσ]
      exact kgcDiag_inl_mul_inr hn (hLT hσ) j
  have hne2 : ¬ ∀ σ ∈ kgcLiftSet ψ D, kgcDiag σ (.inl j) * kgcDiag σ (.inl i) = 1 := fun h =>
    hc true true fun σ hσ => by
      show kgcDiag σ (.inl i) * kgcDiag σ (.inl j) = 1
      rw [mul_comm]
      exact h σ hσ
  obtain ⟨x, hx, hxi, hx1⟩ := exists_mem_kgcTorusSet_cls hn hψ hL hi
  obtain ⟨y, hy, hyj, hy1⟩ := exists_mem_kgcTorusSet_cls hn hψ hL hj
  exact not_sq_le_self_of_prime hp ((sq_le_ncard_kgcTorusSet hn hp hx hy hxi
    (hx1 _ hne1 hne2) (hy1 _ (fun h => hne1 fun σ hσ => (h σ hσ).symm) fun h =>
      hne2 fun σ hσ => by rw [mul_comm]; exact h σ hσ) hyj).trans hKC2')

end CFSG.StandardType.KGCentOm

end
