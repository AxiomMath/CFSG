module

public import CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LinearAlgebra.CoprimeActions.CharacterWeightSpaceIndependence

private def spCW_component {F V E : Type*} [Field F] [AddCommGroup V] [Module F V] [Group E]
    [DecidableEq (E →* Fˣ)] {m : ℕ} (χ χ' : Fin m → (E →* Fˣ)) (T : Module.End F V)
    (v : Fin m → V) (g : Fin m → F) (c : E →* Fˣ) : V :=
  (∑ i ∈ Finset.univ.filter (fun i => χ' i = c), g i • T (v i)) -
    (∑ i ∈ Finset.univ.filter (fun i => χ i = c), g i • v i)

private lemma spCW_component_mem {F V E : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Group E] [DecidableEq (E →* Fˣ)] (τ : Representation F E V) {m : ℕ}
    (χ χ' : Fin m → (E →* Fˣ)) (T : Module.End F V) (v : Fin m → V) (g : Fin m → F)
    (hv : ∀ i, v i ∈ weightSpace τ (χ i)) (hTv : ∀ i, T (v i) ∈ weightSpace τ (χ' i))
    (c : E →* Fˣ) : spCW_component χ χ' T v g c ∈ weightSpace τ c := by
  rw [spCW_component]
  refine Submodule.sub_mem _ ?_ ?_
  · refine Submodule.sum_mem _ fun i hi => ?_
    rw [← (Finset.mem_filter.mp hi).2]
    exact Submodule.smul_mem _ _ (hTv i)
  · refine Submodule.sum_mem _ fun i hi => ?_
    rw [← (Finset.mem_filter.mp hi).2]
    exact Submodule.smul_mem _ _ (hv i)

private lemma spCW_component_self {F V E : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Group E] [DecidableEq (E →* Fˣ)] {m : ℕ} (χ χ' : Fin m → (E →* Fˣ))
    (T : Module.End F V) (v : Fin m → V) (g : Fin m → F) (hχ : Function.Injective χ)
    (hχχ' : ∀ i j, χ i ≠ χ' j) (i : Fin m) :
    spCW_component χ χ' T v g (χ i) = -(g i • v i) := by
  have hEmpt : Finset.univ.filter (fun i' => χ' i' = χ i) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro i' _
    exact fun h => hχχ' i i' h.symm
  have hSing : Finset.univ.filter (fun i' => χ i' = χ i) = {i} := by
    ext i'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨fun h => hχ h, fun h => by rw [h]⟩
  simp only [spCW_component, hEmpt, hSing, Finset.sum_empty, Finset.sum_singleton, zero_sub]

private lemma spCW_component_sum {F V E : Type*} [Field F] [AddCommGroup V] [Module F V]
    [Group E] [DecidableEq (E →* Fˣ)] {m : ℕ} (χ χ' : Fin m → (E →* Fˣ))
    (T : Module.End F V) (v : Fin m → V) (g : Fin m → F)
    (hg : ∑ i, g i • (T - 1) (v i) = 0) :
    ∑ c ∈ (Finset.univ.image χ ∪ Finset.univ.image χ'), spCW_component χ χ' T v g c = 0 := by
  have hg' : ∑ i, g i • T (v i) = ∑ i, g i • v i := by
    have hterm : ∀ i, g i • (T - 1) (v i) = g i • T (v i) - g i • v i := by
      intro i
      rw [LinearMap.sub_apply, smul_sub]
      rfl
    have h0 : ∑ i, (g i • T (v i) - g i • v i) = 0 := by
      simpa only [hterm] using hg
    rw [Finset.sum_sub_distrib] at h0
    exact sub_eq_zero.mp h0
  have hA : ∑ c ∈ (Finset.univ.image χ ∪ Finset.univ.image χ'),
      (∑ i ∈ Finset.univ.filter (fun i => χ' i = c), g i • T (v i))
      = ∑ i, g i • T (v i) :=
    Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
      (t := Finset.univ.image χ ∪ Finset.univ.image χ')
      (fun i _ => Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
        ⟨i, Finset.mem_univ i, rfl⟩)))
      (fun i => g i • T (v i))
  have hB : ∑ c ∈ (Finset.univ.image χ ∪ Finset.univ.image χ'),
      (∑ i ∈ Finset.univ.filter (fun i => χ i = c), g i • v i)
      = ∑ i, g i • v i :=
    Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
      (t := Finset.univ.image χ ∪ Finset.univ.image χ')
      (fun i _ => Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
        ⟨i, Finset.mem_univ i, rfl⟩)))
      (fun i => g i • v i)
  simp only [spCW_component]
  rw [Finset.sum_sub_distrib, hA, hB, hg', sub_self]

private lemma spCW_linearIndependent_sub_one {F V E : Type*} [Field F] [AddCommGroup V]
    [Module F V] [Group E] (τ : Representation F E V) (T : Module.End F V) {m : ℕ}
    (χ χ' : Fin m → (E →* Fˣ)) (hχ : Function.Injective χ)
    (hχχ' : ∀ i j, χ i ≠ χ' j) (v : Fin m → V) (hv0 : ∀ i, v i ≠ 0)
    (hv : ∀ i, v i ∈ weightSpace τ (χ i)) (hTv : ∀ i, T (v i) ∈ weightSpace τ (χ' i)) :
    LinearIndependent F (fun i => (T - 1) (v i)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hsum : ∑ c ∈ (Finset.univ.image χ ∪ Finset.univ.image χ'),
      spCW_component χ χ' T v g c = 0 := spCW_component_sum χ χ' T v g hg
  have hindep := independent τ (fun c : E →* Fˣ => c) Function.injective_id
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero] at hindep
  have hzi : spCW_component χ χ' T v g (χ i) = 0 :=
    hindep (Finset.univ.image χ ∪ Finset.univ.image χ') (spCW_component χ χ' T v g)
      (fun c _ => spCW_component_mem τ χ χ' T v g hv hTv c) hsum (χ i)
      (Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)))
  rw [spCW_component_self χ χ' T v g hχ hχχ' i, neg_eq_zero] at hzi
  exact (smul_eq_zero.mp hzi).resolve_right (hv0 i)

private lemma spCW_sum_reindex {K k V : Type*} [Field K] [Fintype K] [Field k]
    [AddCommGroup V] [Module k V] (a : Kˣ) (ι : K →+* k) {j : ℕ} (hj : j < Nat.card K)
    (w : K → V) :
    (∑ c : K, ι c ^ (Nat.card K - 1 - j) • w ((a : K) * c)) =
      (ι (a : K)) ^ j • (∑ c : K, ι c ^ (Nat.card K - 1 - j) • w c) := by
  have hpowq : (ι (a : K)) ^ (Nat.card K - 1) = 1 := by
    rw [← map_pow, Nat.card_eq_fintype_card,
      FiniteField.pow_card_sub_one_eq_one (a : K) (Units.ne_zero a), map_one]
  have hjle : j ≤ Nat.card K - 1 := Nat.le_sub_one_of_lt hj
  have hkj : (Nat.card K - 1 - j) + j = Nat.card K - 1 := Nat.sub_add_cancel hjle
  have hpowj : ((ι (a : K)) ^ (Nat.card K - 1 - j))⁻¹ = (ι (a : K)) ^ j :=
    (mul_eq_one_iff_inv_eq₀ (pow_ne_zero _ ((map_ne_zero ι).mpr (Units.ne_zero a)))).mp
      (by rw [← pow_add, hkj, hpowq])
  have hne : (a : K)⁻¹ ≠ 0 := inv_ne_zero (Units.ne_zero a)
  calc (∑ c : K, ι c ^ (Nat.card K - 1 - j) • w ((a : K) * c))
      = ∑ c : K, ι ((a : K)⁻¹ * c) ^ (Nat.card K - 1 - j) • w c := by
        rw [← Function.Bijective.sum_comp (mulLeft_bijective₀ ((a : K)⁻¹) hne)
          (fun c : K => ι c ^ (Nat.card K - 1 - j) • w ((a : K) * c))]
        refine Finset.sum_congr rfl fun c _ => ?_
        simp only [mul_inv_cancel_left₀ (Units.ne_zero a) c]
    _ = ∑ c : K, (ι (a : K)) ^ j • (ι c ^ (Nat.card K - 1 - j) • w c) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        have hιc : ι ((a : K)⁻¹ * c) = (ι (a : K))⁻¹ * ι c := by
          rw [map_mul, map_inv₀]
        rw [hιc, mul_pow, inv_pow, hpowj, mul_smul]
    _ = (ι (a : K)) ^ j • (∑ c : K, ι c ^ (Nat.card K - 1 - j) • w c) := by
        rw [Finset.smul_sum]

private lemma spCW_target_apply {E K k : Type*} [Group E] [Field K] [Field k] (ι : K →+* k)
    (α : E →* Kˣ) (ψ : E →* kˣ) (j : ℕ) (e : E) :
    ((ψ * ((Units.map ι.toMonoidHom).comp α) ^ j) e : k)
      = (ψ e : k) * (ι (α e : K)) ^ j := by
  simp only [MonoidHom.mul_apply, MonoidHom.pow_apply, MonoidHom.comp_apply, Units.val_mul,
    Units.val_pow_eq_pow_val, Units.coe_map, RingHom.toMonoidHom_eq_coe]
  rfl

theorem mem_weightSpace_of_inv_mul_mul {F V E G : Type*} [Field F] [AddCommGroup V]
    [Module F V] [Group E] [Group G] (ρ : Representation F G V) (τ : E →* G) {y : G}
    (θ : E →* E) (hθ : ∀ e, y⁻¹ * τ e * y = τ (θ e)) {χ : E →* Fˣ} {v : V}
    (hv : v ∈ weightSpace (ρ.comp τ) χ) : ρ y v ∈ weightSpace (ρ.comp τ) (χ.comp θ) := by
  rw [mem_weightSpace] at hv ⊢
  intro e
  have h1 : τ e * y = y * τ (θ e) := by
    rw [← hθ e]
    group
  calc ρ (τ e) (ρ y v) = ρ (τ e * y) v := by
        simp only [map_mul, Module.End.mul_apply]
    _ = ρ (y * τ (θ e)) v := by rw [h1]
    _ = ρ y (ρ (τ (θ e)) v) := by
        simp only [map_mul, Module.End.mul_apply]
    _ = ρ y ((χ (θ e) : F) • v) := by
        rw [show ρ (τ (θ e)) v = (χ (θ e) : F) • v from by
          simpa only [MonoidHom.comp_apply] using hv (θ e)]
    _ = (χ (θ e) : F) • ρ y v := by rw [map_smul]
    _ = ((χ.comp θ) e : F) • ρ y v := rfl

theorem sum_pow_smul_mem_weightSpace_of_conj {G E K k V : Type*} [Group G] [Group E] [Field K]
    [Fintype K] [Field k] [AddCommGroup V] [Module k V] (ρ : Representation k G V)
    (τ : E →* G) (x : K → G) (α : E →* Kˣ)
    (hx : ∀ e c, τ e * x c * (τ e)⁻¹ = x ((α e : K) * c)) (ι : K →+* k) {ψ : E →* kˣ} {z : V}
    (hz : z ∈ weightSpace (ρ.comp τ) ψ) {j : ℕ} (hj : j < Nat.card K) :
    (∑ c : K, ι c ^ (Nat.card K - 1 - j) • ρ (x c) z) ∈
      weightSpace (ρ.comp τ) (ψ * ((Units.map ι.toMonoidHom).comp α) ^ j) := by
  classical
  rw [mem_weightSpace]
  intro e
  have hper : ∀ c : K, ρ (τ e) (ρ (x c) z) = (ψ e : k) • ρ (x ((α e : K) * c)) z := by
    intro c
    have h1 : τ e * x c = x ((α e : K) * c) * τ e := by
      rw [← hx e c]
      group
    calc ρ (τ e) (ρ (x c) z) = ρ (τ e * x c) z := by
          simp only [map_mul, Module.End.mul_apply]
      _ = ρ (x ((α e : K) * c) * τ e) z := by rw [h1]
      _ = ρ (x ((α e : K) * c)) (ρ (τ e) z) := by
          simp only [map_mul, Module.End.mul_apply]
      _ = ρ (x ((α e : K) * c)) ((ψ e : k) • z) := by
          rw [show ρ (τ e) z = (ψ e : k) • z from by
            simpa only [MonoidHom.comp_apply] using hz e]
      _ = (ψ e : k) • ρ (x ((α e : K) * c)) z := by rw [map_smul]
  calc (ρ.comp τ) e (∑ c : K, ι c ^ (Nat.card K - 1 - j) • ρ (x c) z)
      = ∑ c : K, ι c ^ (Nat.card K - 1 - j) • ρ (τ e) (ρ (x c) z) := by
        simp only [MonoidHom.comp_apply, map_sum, map_smul]
    _ = (ψ e : k) • ∑ c : K, ι c ^ (Nat.card K - 1 - j) • ρ (x ((α e : K) * c)) z := by
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [hper c, smul_comm]
    _ = (ψ e : k) • ((ι (α e : K)) ^ j •
          (∑ c : K, ι c ^ (Nat.card K - 1 - j) • ρ (x c) z)) := by
        rw [spCW_sum_reindex (α e) ι hj (fun c => ρ (x c) z)]
    _ = ((ψ * ((Units.map ι.toMonoidHom).comp α) ^ j) e : k) •
          (∑ c : K, ι c ^ (Nat.card K - 1 - j) • ρ (x c) z) := by
        rw [smul_smul, spCW_target_apply]

theorem le_finrank_range_sub_one_of_weightSpace {F V E : Type*} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] [Group E] (τ : Representation F E V)
    (T : Module.End F V) {m : ℕ} (χ χ' : Fin m → (E →* Fˣ)) (hχ : Function.Injective χ)
    (hχχ' : ∀ i j, χ i ≠ χ' j) (v : Fin m → V) (hv0 : ∀ i, v i ≠ 0)
    (hv : ∀ i, v i ∈ weightSpace τ (χ i)) (hTv : ∀ i, T (v i) ∈ weightSpace τ (χ' i)) :
    m ≤ Module.finrank F (LinearMap.range (T - 1)) := by
  have hli : LinearIndependent F (fun i => (T - 1) (v i)) :=
    spCW_linearIndependent_sub_one τ T χ χ' hχ hχχ' v hv0 hv hTv
  have hspan : Module.finrank F
      (Submodule.span F (Set.range (fun i : Fin m => (T - 1) (v i)))) = m := by
    simpa using finrank_span_eq_card hli
  calc m = Module.finrank F (Submodule.span F (Set.range (fun i : Fin m => (T - 1) (v i)))) :=
        hspan.symm
    _ ≤ Module.finrank F (LinearMap.range (T - 1)) := by
        apply Submodule.finrank_mono
        rw [Submodule.span_le]
        rintro x ⟨i, rfl⟩
        exact ⟨v i, rfl⟩

theorem le_finrank_range_sub_one_of_conj {F V E G : Type*} [Field F] [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] [Group E] [Group G] (ρ : Representation F G V)
    (τ : E →* G) {y : G} (θ : E →* E) (hθ : ∀ e, y⁻¹ * τ e * y = τ (θ e)) {m : ℕ}
    (ψ : Fin m → (E →* Fˣ)) (hψ : Function.Injective ψ) (hψθ : ∀ i j, ψ i ≠ (ψ j).comp θ)
    (v : Fin m → V) (hv0 : ∀ i, v i ≠ 0) (hv : ∀ i, v i ∈ weightSpace (ρ.comp τ) (ψ i)) :
    m ≤ Module.finrank F (LinearMap.range (ρ y - 1)) := by
  exact le_finrank_range_sub_one_of_weightSpace (ρ.comp τ) (ρ y) ψ (fun i => (ψ i).comp θ)
    hψ hψθ v hv0 hv fun i => mem_weightSpace_of_inv_mul_mul ρ τ θ hθ (hv i)

end CFSG.LocalAnalysis.WeakClosure81
