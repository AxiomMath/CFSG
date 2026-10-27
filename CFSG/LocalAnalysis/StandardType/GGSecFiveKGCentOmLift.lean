module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentOmCorank

import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin

public section

namespace CFSG.StandardType.KGCentOm

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin

theorem kgcLiftSet_subset_ggTorus {n : ℕ} {K : Type} [Field K] [CharP K 2] (hn : 3 ≤ n)
    {G : Type*} [Group G] {D : Subgroup G} {ψ : spinGroup (quadPlus n K) →* G}
    (hψ : Function.Injective ψ)
    (hlift : ∀ d ∈ D, ∃ s ∈ ggTorus (plusDatum n K hn), ∀ u, d * ψ u * d⁻¹ = ψ (s * u * s⁻¹)) :
    kgcLiftSet ψ D ⊆ ggTorus (plusDatum n K hn) := fun _ hs =>
  (kgcLiftSet_subset_kgcTorusSet hn (p := 0) hψ (fun d _ => pow_zero d) hlift hs).1

theorem conj_eq_of_mem_kgcLiftSet_of_commute {n : ℕ} {K : Type} [Field K] [CharP K 2]
    (hn : 3 ≤ n) {G : Type*} [Group G] {D : Subgroup G} {ψ : spinGroup (quadPlus n K) →* G}
    (hψ : Function.Injective ψ) {t : G} (htN : t ∈ Subgroup.normalizer (ψ.range : Set G))
    (htD : t ∈ Subgroup.centralizer (D : Set G)) {γ : spinGroup (quadPlus n K)}
    {c : spinGroup (quadPlus n K) →* spinGroup (quadPlus n K)}
    (hconj : ∀ k, t * ψ k * t⁻¹ = ψ (γ * c k * γ⁻¹)) {s : spinGroup (quadPlus n K)}
    (hs : s ∈ kgcLiftSet ψ D) : γ * c s * γ⁻¹ = s := by
  obtain ⟨d, hd, hds⟩ := hs
  have hsurj : ∀ w, ∃ k, γ * c k * γ⁻¹ = w := fun w => by
    obtain ⟨k, hk⟩ : t⁻¹ * ψ w * t ∈ ψ.range :=
      (Subgroup.mem_normalizer_iff''.mp htN (ψ w)).mp ⟨w, rfl⟩
    refine ⟨k, hψ ?_⟩
    rw [← hconj, hk]
    group
  have htd : t * d = d * t := (Subgroup.mem_centralizer_iff.mp htD d hd).symm
  have key : ∀ k, γ * c s * γ⁻¹ * (γ * c k * γ⁻¹) * (γ * c s * γ⁻¹)⁻¹ =
      s * (γ * c k * γ⁻¹) * s⁻¹ := fun k => hψ (by
    have e1 : γ * c s * γ⁻¹ * (γ * c k * γ⁻¹) * (γ * c s * γ⁻¹)⁻¹ =
        γ * c (s * k * s⁻¹) * γ⁻¹ := by
      simp only [map_mul, map_inv]
      group
    rw [e1, ← hconj, ← hds, ← hds (γ * c k * γ⁻¹), ← hconj]
    calc t * (d * ψ k * d⁻¹) * t⁻¹ = t * d * ψ k * (t * d)⁻¹ := by group
      _ = d * t * ψ k * (d * t)⁻¹ := by rw [htd]
      _ = d * (t * ψ k * t⁻¹) * d⁻¹ := by group)
  have hcen : s⁻¹ * (γ * c s * γ⁻¹) ∈ Subgroup.center (spinGroup (quadPlus n K)) := by
    refine Subgroup.mem_center_iff.mpr fun w => ?_
    obtain ⟨k, rfl⟩ := hsurj w
    calc γ * c k * γ⁻¹ * (s⁻¹ * (γ * c s * γ⁻¹)) =
        s⁻¹ * (s * (γ * c k * γ⁻¹) * s⁻¹) * (γ * c s * γ⁻¹) := by group
      _ = s⁻¹ * (γ * c s * γ⁻¹ * (γ * c k * γ⁻¹) * (γ * c s * γ⁻¹)⁻¹) * (γ * c s * γ⁻¹) := by
          rw [key k]
      _ = s⁻¹ * (γ * c s * γ⁻¹) * (γ * c k * γ⁻¹) := by group
  rw [RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo (K := K) hn, Subgroup.mem_bot] at hcen
  exact (inv_mul_eq_one.mp hcen).symm

theorem eq_self_of_map_le {U G : Type*} [Group U] [Group G] {ψ : U →* G}
    (hψ : Function.Injective ψ) {J : Subgroup G} {t : G}
    (htJ : t ∈ Subgroup.centralizer (J : Set G)) {φ : U → U}
    (hconj : ∀ k, t * ψ k * t⁻¹ = ψ (φ k)) {R : Subgroup U} (hR : R.map ψ ≤ J) {z : U}
    (hz : z ∈ R) : φ z = z :=
  hψ (by
    rw [← hconj, mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_centralizer_iff.mp htJ (ψ z) (hR ⟨z, hz, rfl⟩)).symm)

theorem conj_longRoot_eq_of_forall_lift {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n) {G : Type*}
    [Group G] {D J : Subgroup G} {ψ : spinGroup (quadPlus n K) →* G} (hψ : Function.Injective ψ)
    (hlift : ∀ d ∈ D, ∃ s ∈ ggTorus (plusDatum n K hn), ∀ u, d * ψ u * d⁻¹ = ψ (s * u * s⁻¹))
    (hKC1 : ∀ β ∈ (plusDatum n K hn).roots,
      (plusDatum n K hn).rootGroup β ≤ (Subgroup.centralizer (D : Set G)).comap ψ →
        ((plusDatum n K hn).rootGroup β).map ψ ≤ J)
    {t : G} (htJ : t ∈ Subgroup.centralizer (J : Set G))
    {φ : spinGroup (quadPlus n K) → spinGroup (quadPlus n K)}
    (hconj : ∀ k, t * ψ k * t⁻¹ = ψ (φ k)) {i j : Fin n} (hij : i ≠ j) (s s' : Bool)
    (hS : ∀ σ ∈ kgcLiftSet ψ D, ∀ b : K,
      σ * (plusFrame n K hn).longRoot hij s s' (.ofAdd b) * σ⁻¹ =
        (plusFrame n K hn).longRoot hij s s' (.ofAdd b)) (b : K) :
    φ ((plusFrame n K hn).longRoot hij s s' (.ofAdd b)) =
      (plusFrame n K hn).longRoot hij s s' (.ofAdd b) := by
  obtain ⟨β, hβ, hβstd⟩ := exists_mem_rootsD_toStdD_eq n hij (boolSign_eq_one_or_eq_neg_one s)
    (boolSign_eq_one_or_eq_neg_one s')
  have hRG : (plusDatum n K hn).rootGroup β = ((plusFrame n K hn).longRoot hij s s').range :=
    plusRootGroup_eq hn hij s s' hβstd
  have hcent : (plusDatum n K hn).rootGroup β ≤ (Subgroup.centralizer (D : Set G)).comap ψ := by
    rw [hRG]
    rintro _ ⟨c, rfl⟩
    refine Subgroup.mem_comap.mpr (Subgroup.mem_centralizer_iff.mpr fun d hd => ?_)
    obtain ⟨σ, -, hσ⟩ := hlift d hd
    rw [← mul_inv_eq_iff_eq_mul, hσ]
    exact congrArg ψ (hS σ ⟨d, hd, hσ⟩ (Multiplicative.toAdd c))
  exact eq_self_of_map_le hψ htJ hconj (hKC1 β hβ hcent) (by rw [hRG]; exact ⟨_, rfl⟩)

private theorem kgcDiag_mul_eq_one_of_fix_longRoot {n : ℕ} {K : Type} [Field K] (hn : 3 ≤ n)
    {σ : spinGroup (quadPlus n K)} (hσ : σ ∈ ggTorus (plusDatum n K hn)) {i j : Fin n}
    (hij : i ≠ j) (s t : Bool)
    (h : σ * (plusFrame n K hn).longRoot hij s t (.ofAdd 1) * σ⁻¹ =
      (plusFrame n K hn).longRoot hij s t (.ofAdd 1)) :
    kgcDiag σ (kgcIdx i s) * kgcDiag σ (kgcIdx j t) = 1 := by
  rw [StdPosD.conj_longRoot_of_smul (plusFrame n K hn) hij s t
    (spinAction_vec_eq_kgcDiag_smul hn hσ i s) (spinAction_vec_eq_kgcDiag_smul hn hσ j t),
    mul_one] at h
  exact Multiplicative.ofAdd.injective ((plusFrame n K hn).longRoot_injective hij s t h)

theorem kgcFixedIdx_of_mem_centralizer {n : ℕ} {K : Type} [Field K] [CharP K 2] (hn : 3 ≤ n)
    {G : Type*} [Group G] {D : Subgroup G} {ψ : spinGroup (quadPlus n K) →* G}
    (hψ : Function.Injective ψ)
    (hLT : kgcLiftSet ψ D ⊆ ggTorus (plusDatum n K hn)) {a b : Fin n} (hab : a ≠ b)
    (h : ∀ r : Bool, ψ ((plusFrame n K hn).longRoot hab true r (.ofAdd 1)) ∈
      Subgroup.centralizer (D : Set G)) :
    KGCFixedIdx hn (kgcLiftSet ψ D) a := by
  refine (kgcFixedIdx_iff hn hLT a true).mpr fun σ hσ => ?_
  have hfix : ∀ r : Bool, kgcDiag σ (kgcIdx a true) * kgcDiag σ (kgcIdx b r) = 1 := fun r => by
    obtain ⟨d, hd, hσd⟩ := id hσ
    refine kgcDiag_mul_eq_one_of_fix_longRoot hn (hLT hσ) hab true r (hψ ?_)
    rw [← hσd, mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_centralizer_iff.mp (h r) d hd
  have h1 : kgcDiag σ (.inl a) * kgcDiag σ (.inl b) = 1 := hfix true
  have h0 : kgcDiag σ (.inl a) * kgcDiag σ (.inr b) = 1 := hfix false
  have h2 := kgcDiag_inl_mul_inr hn (hLT hσ) b
  have hxx : kgcDiag σ (.inl a) * kgcDiag σ (.inl a) = 1 := by
    calc kgcDiag σ (.inl a) * kgcDiag σ (.inl a) =
        kgcDiag σ (.inl a) * kgcDiag σ (.inl a) * (kgcDiag σ (.inl b) * kgcDiag σ (.inr b)) := by
          rw [h2, mul_one]
      _ = kgcDiag σ (.inl a) * kgcDiag σ (.inl b) * (kgcDiag σ (.inl a) * kgcDiag σ (.inr b)) := by
          ring
      _ = 1 := by rw [h1, h0, one_mul]
  rcases mul_self_eq_one_iff.mp hxx with hx | hx
  · exact hx
  · exact hx.trans (CharTwo.neg_eq 1)

end CFSG.StandardType.KGCentOm

end
