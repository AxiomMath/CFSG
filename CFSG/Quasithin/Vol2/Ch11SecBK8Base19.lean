module

public import CFSG.Quasithin.Vol2.Ch11SecBK8Base18

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {K : Type} [Field K]

theorem card_commSub_mul_card_fix [Finite K] (y : MulAut (W6 K)) :
    Nat.card ↥(commSub ⊤ (Subgroup.zpowers y)) * Nat.card (FixW y) = Nat.card (W6 K) := by
  rw [commSub_zpowers_eq_map (fun _ _ _ _ => Subgroup.mem_top _), ← card_fixV_zpowers,
    ← ker_commHom, ← MonoidHom.range_eq_map, mul_comm, ← Subgroup.index_ker,
    Subgroup.card_mul_index]

theorem trvW_natEmb {f : (Fin 3 → K) →ₗ[K] K} {w : Fin 3 → K} {y : MulAut (W6 K)}
    (hy : ∀ v, toAddMap y v = trvW f w v) (a b : K) (u : StdMod (Fin 3) K) :
    y (natEmb a b u) = natEmb a b (Multiplicative.ofAdd
      (Multiplicative.toAdd u + f (Multiplicative.toAdd u) • w)) := by
  apply Multiplicative.toAdd.injective
  have := hy (natVec a b (Multiplicative.toAdd u))
  change Multiplicative.toAdd (y (natEmb a b u)) = _ at this
  rw [this, toAdd_natEmb, toAdd_ofAdd]
  funext i
  rcases i with i | i <;> simp [natVec, mul_assoc]

theorem trvW_trvW [CharP K 2] {f : (Fin 3 → K) →ₗ[K] K} {w : Fin 3 → K} (hfw : f w = 0)
    (v : I6 → K) : trvW f w (trvW f w v) = v := by
  have h1 : trvW f w v ∘ Sum.inl = v ∘ Sum.inl + f (v ∘ Sum.inl) • w := by
    funext j
    rfl
  have h2 : trvW f w v ∘ Sum.inr = v ∘ Sum.inr + f (v ∘ Sum.inr) • w := by
    funext j
    rfl
  have h3 : ∀ u : Fin 3 → K, f (u + f u • w) = f u := fun u => by
    rw [map_add, map_smul, hfw, smul_zero, add_zero]
  change trvW f w v + Sum.elim (f (trvW f w v ∘ Sum.inl) • w) (f (trvW f w v ∘ Sum.inr) • w) = v
  rw [h1, h2, h3, h3]
  funext i
  rcases i with i | i <;>
    simp only [trvW, Pi.add_apply, Sum.elim_inl, Sum.elim_inr, add_assoc,
      CharTwo.add_self_eq_zero, add_zero]

theorem commSub_top_trvW [CharP K 2] {f : (Fin 3 → K) →ₗ[K] K} {w : Fin 3 → K}
    {y : MulAut (W6 K)} (hy : ∀ v, toAddMap y v = trvW f w v) (hf : f ≠ 0) (hfw : f w = 0) :
    commSub ⊤ (Subgroup.zpowers y) = sqSub (K ∙ w) := by
  have hsq : y * y = 1 := by
    refine toAddMap_injective fun v => ?_
    rw [toAddMap_mul, hy, hy, toAddMap_one, trvW_trvW hfw]
  have hz : ∀ z ∈ Subgroup.zpowers y, z = 1 ∨ z = y := by
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [← two_mul, _root_.zpow_mul, zpow_two, hsq, one_zpow]
    · right
      rw [_root_.zpow_add, _root_.zpow_mul, zpow_two, hsq, one_zpow, one_mul, zpow_one]
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, f v₀ = 1 := by
    obtain ⟨u, hu⟩ : ∃ u, f u ≠ 0 := by
      by_contra h
      push Not at h
      exact hf (LinearMap.ext h)
    exact ⟨(f u)⁻¹ • u, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hu]⟩
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨z, hz', v, -, rfl⟩
    rcases hz z hz' with rfl | rfl
    · rw [MulAut.one_apply, mul_inv_cancel]
      exact (sqSub _).one_mem
    · rw [SetLike.mem_coe, mem_sqSub, toAdd_comm_trvW hy, Sum.elim_comp_inl, Sum.elim_comp_inr]
      exact ⟨Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w),
        Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)⟩
  · intro x hx
    obtain ⟨c₁, hc₁⟩ := Submodule.mem_span_singleton.mp hx.1
    obtain ⟨c₂, hc₂⟩ := Submodule.mem_span_singleton.mp hx.2
    refine Subgroup.subset_closure ⟨y, Subgroup.mem_zpowers y,
      Multiplicative.ofAdd (Sum.elim (c₁ • v₀) (c₂ • v₀)), Subgroup.mem_top _, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [toAdd_comm_trvW hy, toAdd_ofAdd, Sum.elim_comp_inl, Sum.elim_comp_inr, map_smul,
      map_smul, hv₀, smul_eq_mul, smul_eq_mul, mul_one, mul_one, hc₁, hc₂]
    funext i
    rcases i with i | i <;> rfl

theorem commSub_natSub_scal {A : Subgroup (MulAut (W6 K))} (hA : A ≤ linSub) (a b c : K)
    {x : W6 K} (hx : x ∈ commSub (natSub a b) A) : scalHom c x ∈ commSub (natSub a b) A := by
  have hle : commSub (natSub a b) A ≤ (commSub (natSub a b) A).comap (scalHom c) := by
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨y, hy, v, hv, rfl⟩
    refine Subgroup.subset_closure ⟨y, hy, scalHom c v, scalHom_natSub c a b hv, ?_⟩
    have hlin := mem_linSub.mp (hA hy)
    have := hlin c (Multiplicative.toAdd v)
    change Multiplicative.toAdd (y (Multiplicative.ofAdd (c • Multiplicative.toAdd v))) =
      c • Multiplicative.toAdd (y v) at this
    apply Multiplicative.toAdd.injective
    have e1 : scalHom c v = Multiplicative.ofAdd (c • Multiplicative.toAdd v) := rfl
    have e2 : scalHom c (y v * v⁻¹) =
        Multiplicative.ofAdd (c • Multiplicative.toAdd (y v * v⁻¹)) := rfl
    rw [e1, e2, toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_ofAdd, this, toAdd_mul, toAdd_inv,
      smul_add, smul_neg]
  exact hle hx

theorem commSub_zpowers_natEmb [CharP K 2] {A : Subgroup (MulAut (W6 K))}
    {f : (Fin 3 → K) →ₗ[K] K} (hform : ∀ y ∈ A, ∃ w, f w = 0 ∧ ∀ v, toAddMap y v = trvW f w v)
    (hsurj : ∀ w, f w = 0 → ∃ y ∈ A, ∀ v, toAddMap y v = trvW f w v) (a b : K)
    {u : Fin 3 → K} (hu : f u ≠ 0) :
    commSub (Subgroup.zpowers (natEmb a b (Multiplicative.ofAdd u))) A =
      natSubOf a b (LinearMap.ker f) := by
  set z₀ := natEmb a b (Multiplicative.ofAdd u) with hz₀
  have hsq : z₀ * z₀ = 1 := by
    apply Multiplicative.toAdd.injective
    funext i
    simp [CharTwo.add_self_eq_zero]
  have hz : ∀ z ∈ Subgroup.zpowers z₀, z = 1 ∨ z = z₀ := by
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · left
      rw [← two_mul, _root_.zpow_mul, zpow_two, hsq, one_zpow]
    · right
      rw [_root_.zpow_add, _root_.zpow_mul, zpow_two, hsq, one_zpow, one_mul, zpow_one]
  have hgen : ∀ (y : MulAut (W6 K)) (w : Fin 3 → K), (∀ v, toAddMap y v = trvW f w v) →
      y z₀ * z₀⁻¹ = natEmb a b (Multiplicative.ofAdd (f u • w)) := by
    intro y w hyw
    rw [hz₀, trvW_natEmb hyw, toAdd_ofAdd, ofAdd_add, map_mul, mul_inv_cancel_comm]
  apply le_antisymm
  · rw [commSub, Subgroup.closure_le]
    rintro _ ⟨y, hy, z, hz', rfl⟩
    obtain ⟨w, hw, hyw⟩ := hform y hy
    rcases hz z hz' with rfl | rfl
    · rw [map_one, one_mul, inv_one]
      exact (natSubOf _ _ _).one_mem
    · rw [hgen y w hyw]
      exact mem_natSubOf.mpr ⟨f u • w, by rw [LinearMap.mem_ker, map_smul, hw, smul_zero], rfl⟩
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := mem_natSubOf.mp hx
    obtain ⟨y, hy, hys⟩ := hsurj ((f u)⁻¹ • s) (by rw [map_smul, hs, smul_zero])
    refine Subgroup.subset_closure ⟨y, hy, z₀, Subgroup.mem_zpowers z₀, ?_⟩
    rw [hgen y _ hys, smul_smul, mul_inv_cancel₀ hu, one_smul]

end CFSG.Quasithin.Vol2.Ch11.SecB.K8
