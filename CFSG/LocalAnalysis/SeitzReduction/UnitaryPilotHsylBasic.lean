module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearData
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogRigidityIsotropic
public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotBlocks

public section

namespace CFSG.SeitzReduction.UnitaryPilot

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)
open CFSG.LinearGroups (stdHermForm stdHermForm_apply stdHermForm_isSymm
  stdHermForm_separatingLeft hermTransvection_apply)

section Form

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {n : ℕ}

theorem stdHermForm_single_right (v : Fin n → K) (j : Fin n) (c : K) :
    stdHermForm h n v (Pi.single j c) = h.bar (v j) * c := by
  rw [stdHermForm_apply, Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
  simp

theorem stdHermForm_single_add_single {k k' : Fin n} (hkk' : k ≠ k') (c : K) :
    stdHermForm h n (Pi.single k 1 + Pi.single k' c) (Pi.single k 1 + Pi.single k' c) =
      1 + h.norm c := by
  rw [stdHermForm_apply, Fintype.sum_eq_add k k' hkk' fun i hi => by
    simp [hi.1, hi.2]]
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hkk', Pi.single_eq_of_ne hkk'.symm,
    add_zero, zero_add, map_one, mul_one, UnitaryFieldData.norm]
  ring

end Form

section Even

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K) {n : ℕ}

theorem exists_transvection_mem_unitaryBlock {J : Finset (Fin n)} {v : Fin n → K}
    (hvJ : ∀ i ∉ J, v i = 0) (hv : stdHermForm h n v v = 0) {τ : K} (hτ : τ ∈ h.traceZero) :
    ∃ g : unitarySU 2 f K n,
      (∀ x, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x =
        x + (τ * stdHermForm h n v x) • v) ∧ g ∈ unitaryBlock h J ∧ g * g = 1 := by
  have := h.charP
  obtain ⟨g, hg⟩ := exists_mem_unitarySU_hermTransvection h hv hτ
  have hgx : ∀ x, ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x =
      x + (τ * stdHermForm h n v x) • v := fun x => by
    have := LinearMap.congr_fun hg x
    rwa [Matrix.mulVecLin_apply, hermTransvection_apply] at this
  refine ⟨g, hgx, ?_, ?_⟩
  · rw [mem_unitaryBlock]
    intro i j hij
    have h1 := congrFun (hgx (Pi.single j 1)) i
    rw [mulVec_single_one, col_apply] at h1
    rw [h1, Pi.add_apply, Pi.smul_apply, smul_eq_mul, stdHermForm_single_right h, mul_one,
      Pi.single_apply, one_apply]
    rcases hij with hi | hj
    · rw [hvJ i hi, mul_zero, add_zero]
    · rw [hvJ j hj, map_zero, mul_zero, zero_mul, add_zero]
  · apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, OneMemClass.coe_one, Units.val_one,
      Matrix.ext_iff_mulVec]
    intro x
    rw [← Matrix.mulVec_mulVec, hgx, hgx, Matrix.one_mulVec, map_add, map_smul, hv, smul_eq_mul,
      mul_zero, add_zero, add_assoc, ← add_smul, CharTwo.add_self_eq_zero, zero_smul, add_zero]

theorem eq_one_and_agrees_of_forall_involution {J : Finset (Fin n)} (hJ : 3 ≤ J.card)
    {A : GL (Fin n) K}
    (hAu : ((A : Matrix (Fin n) (Fin n) K).map h.bar)ᵀ * (A : Matrix (Fin n) (Fin n) K) = 1)
    {φ : K ≃+* K}
    (hfix : ∀ g : unitarySU 2 f K n, g ∈ unitaryBlock h J → g * g = 1 →
      A * glAut φ (g : GL (Fin n) K) = (g : GL (Fin n) K) * A) :
    φ = 1 ∧ ∃ μ : K, h.norm μ = 1 ∧ ∀ i j, (i ∈ J ∨ j ∈ J) →
      (A : Matrix (Fin n) (Fin n) K) i j = μ * (1 : Matrix (Fin n) (Fin n) K) i j := by
  have := h.finite
  have := h.charP
  obtain ⟨τ, hτ, hτ0⟩ := h.exists_mem_traceZero_ne_zero
  let T : (Fin n → K) →ₛₗ[(φ : K →+* K)] (Fin n → K) :=
    { toFun := fun x => (A : Matrix (Fin n) (Fin n) K) *ᵥ fun i => φ (x i)
      map_add' := fun x y => by
        simp only [Pi.add_apply, map_add]
        rw [← Matrix.mulVec_add]
        rfl
      map_smul' := fun c x => by
        simp only [Pi.smul_apply, smul_eq_mul, map_mul]
        rw [← Matrix.mulVec_smul]
        rfl }
  have hTapply : ∀ x, T x = (A : Matrix (Fin n) (Fin n) K) *ᵥ fun i => φ (x i) := fun _ => rfl
  have hTinj : Function.Injective T := by
    intro x y hxy
    rw [hTapply, hTapply] at hxy
    have h1 := congrArg (((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ ·) hxy
    simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at h1
    funext i
    exact φ.injective (congrFun h1 i)
  have hTg : ∀ g : GL (Fin n) K, A * glAut φ g = g * A →
      ∀ x, T ((g : Matrix (Fin n) (Fin n) K) *ᵥ x) = (g : Matrix (Fin n) (Fin n) K) *ᵥ T x := by
    intro g hg x
    rw [hTapply, hTapply]
    have hφg : (fun i => φ (((g : Matrix (Fin n) (Fin n) K) *ᵥ x) i)) =
        ((glAut φ g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ fun i => φ (x i) := by
      funext i
      have h1 := RingHom.map_mulVec (φ : K →+* K) (g : Matrix (Fin n) (Fin n) K) x i
      simp only [RingEquiv.coe_toRingHom] at h1
      rw [h1, coe_glAut]
      rfl
    rw [hφg, Matrix.mulVec_mulVec, ← Units.val_mul, hg, Units.val_mul, ← Matrix.mulVec_mulVec]
  have hstar : ∀ v : Fin n → K, (∀ i ∉ J, v i = 0) → stdHermForm h n v v = 0 → ∀ x,
      φ (τ * stdHermForm h n v x) • T v = (τ * stdHermForm h n v (T x)) • v := by
    intro v hvJ hv x
    obtain ⟨g, hgx, hgJ, hgg⟩ := exists_transvection_mem_unitaryBlock h hvJ hv hτ
    have h1 := hTg g (hfix g hgJ hgg) x
    rw [hgx, hgx, map_add, map_smulₛₗ] at h1
    simpa using add_left_cancel h1
  have hline : ∀ v : Fin n → K, (∀ i ∉ J, v i = 0) → stdHermForm h n v v = 0 →
      ∃ μ : K, T v = μ • v := by
    intro v hvJ hv
    by_cases hv0 : v = 0
    · exact ⟨0, by rw [hv0, map_zero, smul_zero]⟩
    obtain ⟨x₀, hx₀⟩ : ∃ x, stdHermForm h n v x ≠ 0 := by
      by_contra! hall
      exact hv0 (stdHermForm_separatingLeft h n v hall)
    have hne : φ (τ * stdHermForm h n v x₀) ≠ 0 :=
      (map_ne_zero φ).mpr (mul_ne_zero hτ0 hx₀)
    refine ⟨(φ (τ * stdHermForm h n v x₀))⁻¹ * (τ * stdHermForm h n v (T x₀)), ?_⟩
    rw [mul_smul, ← hstar v hvJ hv x₀, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hperp : ∀ v : Fin n → K, (∀ i ∉ J, v i = 0) → stdHermForm h n v v = 0 → ∀ x,
      stdHermForm h n v x = 0 → stdHermForm h n v (T x) = 0 := by
    intro v hvJ hv x hx
    by_cases hv0 : v = 0
    · rw [hv0, map_zero, LinearMap.zero_apply]
    have h1 := hstar v hvJ hv x
    rw [hx, mul_zero, map_zero, zero_smul, eq_comm, smul_eq_zero] at h1
    rcases h1 with h1 | h1
    · exact (mul_eq_zero.mp h1).resolve_left hτ0
    · exact absurd h1 hv0
  have hcol : ∀ i ∉ J, ∀ k ∈ J, (A : Matrix (Fin n) (Fin n) K) i k = 0 := by
    intro i hi k hk
    obtain ⟨k', hk', hkk'⟩ : ∃ k' ∈ J, k ≠ k' := by
      obtain ⟨k₁, h₁, k₂, h₂, h12⟩ := Finset.one_lt_card.1 (by omega : 1 < J.card)
      by_cases e : k = k₁
      · exact ⟨k₂, h₂, e ▸ h12⟩
      · exact ⟨k₁, h₁, e⟩
    have hvec : ∀ c : K, h.norm c = 1 →
        (A : Matrix (Fin n) (Fin n) K) i k + (A : Matrix (Fin n) (Fin n) K) i k' * φ c = 0 := by
      intro c hc
      have hvJ : ∀ l ∉ J, (Pi.single k 1 + Pi.single k' c : Fin n → K) l = 0 := by
        intro l hl
        have hlk : l ≠ k := fun e => hl (e ▸ hk)
        have hlk' : l ≠ k' := fun e => hl (e ▸ hk')
        simp [hlk, hlk']
      have hiso : stdHermForm h n (Pi.single k 1 + Pi.single k' c)
          (Pi.single k 1 + Pi.single k' c) = 0 := by
        rw [stdHermForm_single_add_single h hkk', hc, CharTwo.add_self_eq_zero]
      obtain ⟨μ, hμ⟩ := hline _ hvJ hiso
      have h1 := congrFun hμ i
      rw [Pi.smul_apply, hvJ i hi, smul_zero] at h1
      simp only [hTapply, mulVec, dotProduct] at h1
      rw [Fintype.sum_eq_add k k' hkk' fun l hl => by simp [hl.1, hl.2]] at h1
      simpa [Pi.single_apply, hkk', hkk'.symm] using h1
    obtain ⟨κ, hκN, hκ1⟩ := exists_norm_eq_one_ne_one h
    have e1 := hvec 1 (by simp [UnitaryFieldData.norm])
    have e2 := hvec κ hκN
    rw [map_one, mul_one] at e1
    have hφκ : (1 : K) - φ κ ≠ 0 := by
      rw [sub_ne_zero]
      intro e
      apply hκ1
      apply Units.ext
      rw [Units.val_one]
      exact φ.injective (by rw [← e, map_one])
    have e3 : (A : Matrix (Fin n) (Fin n) K) i k' * (1 - φ κ) = 0 := by
      linear_combination e1 - e2
    have hAik' := (mul_eq_zero.1 e3).resolve_right hφκ
    rw [hAik', add_zero] at e1
    exact e1
  have hsupp : ∀ x : Fin n → K, (∀ i ∉ J, x i = 0) → ∀ i ∉ J, T x i = 0 := by
    intro x hx i hi
    simp only [hTapply, mulVec, dotProduct]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k ∈ J
    · rw [hcol i hi k hk, zero_mul]
    · rw [hx k hk, map_zero, mul_zero]
  set ι : Fin J.card → Fin n := fun k => J.orderEmbOfFin rfl k with hιdef
  have hι : Function.Injective ι := (J.orderEmbOfFin rfl).injective
  have hιJ : ∀ i, i ∈ J ↔ i ∈ Set.range ι := fun i => by
    rw [show Set.range ι = (J : Set (Fin n)) from Finset.range_orderEmbOfFin J rfl,
      Finset.mem_coe]
  let E : (Fin J.card → K) →ₗ[K] (Fin n → K) := Function.ExtendByZero.linearMap K ι
  let R : (Fin n → K) →ₗ[K] (Fin J.card → K) := LinearMap.funLeft K K ι
  have hE : ∀ y k, E y (ι k) = y k := fun y k => hι.extend_apply y 0 k
  have hE0 : ∀ y i, i ∉ J → E y i = 0 := fun y i hi => by
    change Function.extend ι y 0 i = 0
    rw [Function.extend_apply' _ _ _ (fun ⟨k, hk⟩ => hi ((hιJ i).2 ⟨k, hk⟩)), Pi.zero_apply]
  have hRE : ∀ y, R (E y) = y := fun y => funext fun k => hE y k
  have hER : ∀ x : Fin n → K, (∀ i ∉ J, x i = 0) → E (R x) = x := fun x hx => funext fun i => by
    by_cases hi : i ∈ J
    · obtain ⟨k, rfl⟩ := (hιJ i).1 hi
      rw [hE]
      rfl
    · rw [hE0 _ _ hi, hx i hi]
  have hform : ∀ y x, stdHermForm h n (E y) x = stdHermForm h J.card y (R x) := by
    intro y x
    rw [stdHermForm_apply, stdHermForm_apply]
    refine (Fintype.sum_of_injective ι hι (fun k => h.bar (y k) * R x k)
      (fun i => h.bar (E y i) * x i) (fun i hi => ?_) (fun k => ?_)).symm
    · rw [hE0 _ _ (fun hiJ => hi ((hιJ i).1 hiJ)), map_zero, zero_mul]
    · show h.bar (y k) * R x k = h.bar (E y (ι k)) * x (ι k)
      rw [hE]
      rfl
  let T' : (Fin J.card → K) →ₛₗ[(φ : K →+* K)] (Fin J.card → K) :=
    { toFun := fun y => R (T (E y))
      map_add' := fun y y' => by simp only [map_add]
      map_smul' := fun c y => by simp only [map_smul, map_smulₛₗ] }
  have hET' : ∀ y, E (T' y) = T (E y) := fun y => hER _ (hsupp _ (hE0 y))
  have hT'inj : Function.Injective T' := by
    intro y₁ y₂ h12
    have h1 := congrArg E h12
    rw [hET', hET'] at h1
    rw [← hRE y₁, ← hRE y₂, hTinj h1]
  have hline' : ∀ y, stdHermForm h J.card y y = 0 → ∃ μ : K, T' y = μ • y := by
    intro y hy
    obtain ⟨μ, hμ⟩ := hline (E y) (hE0 y) (by rw [hform, hRE, hy])
    exact ⟨μ, by change R (T (E y)) = μ • y; rw [hμ, map_smul, hRE]⟩
  have hperp' : ∀ y, stdHermForm h J.card y y = 0 → ∀ x, stdHermForm h J.card y x = 0 →
      stdHermForm h J.card y (T' x) = 0 := by
    intro y hy x hx
    have h1 := hperp (E y) (hE0 y) (by rw [hform, hRE, hy]) (E x) (by rw [hform, hRE, hx])
    rw [hform] at h1
    exact h1
  obtain ⟨hφ1, μ, hμ⟩ :=
    CFSG.ComponentClassification.UnbalancedCatalog.semilinear_eq_smul_of_isotropic h
      (stdHermForm_isSymm h J.card) (stdHermForm_separatingLeft h J.card)
      (by rw [Module.finrank_fin_fun]; exact hJ) T' hT'inj hline' hperp'
  have hcolJ : ∀ i, ∀ k ∈ J,
      (A : Matrix (Fin n) (Fin n) K) i k = μ * (1 : Matrix (Fin n) (Fin n) K) i k := by
    intro i k hk
    obtain ⟨l, rfl⟩ := (hιJ k).1 hk
    have hEs : E (Pi.single l 1) = Pi.single (ι l) 1 := by
      funext j
      by_cases hj : j ∈ J
      · obtain ⟨l', rfl⟩ := (hιJ j).1 hj
        rw [hE, Pi.single_apply, Pi.single_apply]
        exact if_congr hι.eq_iff.symm rfl rfl
      · rw [hE0 _ _ hj, Pi.single_eq_of_ne (fun e : j = ι l => hj (e ▸ hk))]
    have h1 : T (Pi.single (ι l) 1) = μ • Pi.single (ι l) 1 := by
      rw [← hEs, ← hET', hμ, map_smul]
    have h2 := congrFun h1 i
    have hφs : (fun j => φ ((Pi.single (ι l) (1 : K) : Fin n → K) j)) = Pi.single (ι l) 1 := by
      funext j
      simp only [Pi.single_apply]
      split_ifs <;> simp
    rw [hTapply, hφs, mulVec_single_one, col_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_apply] at h2
    rw [h2, one_apply]
  obtain ⟨k₀, hk₀⟩ : J.Nonempty := Finset.card_pos.1 (by omega)
  have hunit : ∀ i j, ∑ r, h.bar ((A : Matrix (Fin n) (Fin n) K) r i) *
      (A : Matrix (Fin n) (Fin n) K) r j = (1 : Matrix (Fin n) (Fin n) K) i j := by
    intro i j
    have := congrFun (congrFun hAu i) j
    rw [mul_apply] at this
    simpa only [transpose_apply, Matrix.map_apply] using this
  have hμ1 : h.norm μ = 1 := by
    have h1 := hunit k₀ k₀
    rw [Finset.sum_eq_single k₀ (fun r _ hr => by
      rw [hcolJ r k₀ hk₀, one_apply_ne hr, mul_zero, mul_zero]) (by simp)] at h1
    rw [hcolJ k₀ k₀ hk₀, one_apply_eq, mul_one] at h1
    rw [UnitaryFieldData.norm, mul_comm]
    exact h1
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, UnitaryFieldData.norm, zero_mul] at hμ1
    exact zero_ne_one hμ1
  have hrow : ∀ i ∈ J, ∀ j ∉ J, (A : Matrix (Fin n) (Fin n) K) i j = 0 := by
    intro i hi j hj
    have h1 := hunit j i
    rw [Finset.sum_eq_single i (fun r _ hr => by
      rw [hcolJ r i hi, one_apply_ne hr, mul_zero, mul_zero]) (by simp)] at h1
    rw [hcolJ i i hi, one_apply_eq, mul_one, one_apply_ne (fun e : j = i => hj (e ▸ hi))] at h1
    exact (h.bar_eq_zero_iff).1 ((mul_eq_zero.1 h1).resolve_right hμ0)
  refine ⟨hφ1, μ, hμ1, fun i j hij => ?_⟩
  by_cases hj : j ∈ J
  · exact hcolJ i j hj
  · have hi : i ∈ J := hij.resolve_right hj
    rw [hrow i hi j hj, one_apply_ne (fun e : i = j => hj (e ▸ hi)), mul_zero]

end Even

end CFSG.SeitzReduction.UnitaryPilot
