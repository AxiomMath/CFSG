module

public import CFSG.Quasithin.Vol2.Ch11SecBK8Base12

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

variable {K : Type} [Field K]

@[expose] noncomputable def fixPlane (A : Subgroup (MulAut (W6 K))) : Submodule K (Fin 3 → K) :=
  ⨅ g : ↥(dgMat A), fixSub (g : GL (Fin 3) K)

theorem mem_fixPlane {A : Subgroup (MulAut (W6 K))} {u : Fin 3 → K} :
    u ∈ fixPlane A ↔ ∀ g ∈ dgMat A, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ u = u := by
  rw [fixPlane, Submodule.mem_iInf]
  exact ⟨fun h g hg => mem_fixSub.mp (h ⟨g, hg⟩), fun h g => mem_fixSub.mpr (h g.1 g.2)⟩

theorem mem_fixV_iff_fixPlane {A : Subgroup (MulAut (W6 K))} (hAD : A ≤ dgSub K) (v : W6 K) :
    v ∈ fixV A ↔ Multiplicative.toAdd v ∘ Sum.inl ∈ fixPlane A ∧
      Multiplicative.toAdd v ∘ Sum.inr ∈ fixPlane A := by
  rw [mem_fixPlane, mem_fixPlane]
  constructor
  · intro h
    refine ⟨fun g hg => ?_, fun g hg => ?_⟩
    · exact ((dg_fix_iff g _).mp (congrArg Multiplicative.toAdd (h _ hg.1))).1
    · exact ((dg_fix_iff g _).mp (congrArg Multiplicative.toAdd (h _ hg.1))).2
  · rintro ⟨h1, h2⟩ y hy
    obtain ⟨g, rfl⟩ := hAD hy
    have hg : g ∈ dgMat A := ⟨hy, matAut_dgHom_mem_dgSub g⟩
    exact congrArg Multiplicative.ofAdd ((dg_fix_iff g _).mpr ⟨h1 g hg, h2 g hg⟩)

theorem card_fixV_eq_sq {A : Subgroup (MulAut (W6 K))} (hAD : A ≤ dgSub K) :
    Nat.card ↥(fixV A) = Nat.card ↥(fixPlane A) ^ 2 := by
  rw [sq, ← Nat.card_prod]
  refine Nat.card_congr
    { toFun := fun v => (⟨_, ((mem_fixV_iff_fixPlane hAD v.1).mp v.2).1⟩,
        ⟨_, ((mem_fixV_iff_fixPlane hAD v.1).mp v.2).2⟩)
      invFun := fun p => ⟨Multiplicative.ofAdd (Sum.elim p.1.1 p.2.1),
        (mem_fixV_iff_fixPlane hAD _).mpr ⟨p.1.2, p.2.2⟩⟩
      left_inv := fun v => Subtype.ext (by
        apply Multiplicative.toAdd.injective
        funext i
        rcases i with i | i <;> rfl)
      right_inv := fun p => rfl }

theorem eq_add_of_ker {g : GL (Fin 3) K} (f : (Fin 3 → K) →ₗ[K] K) {v₀ : Fin 3 → K}
    (hv₀ : f v₀ = 1) (hker : ∀ v, f v = 0 → (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v)
    (v : Fin 3 → K) :
    (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v =
      v + f v • ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v₀ - v₀) := by
  have h1 := hker (v - f v • v₀) (by rw [map_sub, map_smul, hv₀, smul_eq_mul, mul_one, sub_self])
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul] at h1
  rw [smul_sub]
  calc (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v
      = ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v - f v • ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v₀)) +
        f v • ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v₀) := by abel
    _ = (v - f v • v₀) + f v • ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v₀) := by rw [h1]
    _ = v + (f v • ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v₀) - f v • v₀) := by abel

abbrev trvW (f : (Fin 3 → K) →ₗ[K] K) (w : Fin 3 → K) (v : I6 → K) : I6 → K :=
  v + Sum.elim (f (v ∘ Sum.inl) • w) (f (v ∘ Sum.inr) • w)

theorem axis_model [Finite K] [CharP K 2] {A : Subgroup (MulAut (W6 K))} (hAD : A ≤ dgSub K)
    (hA : IsElemAbelian2 A) (hcard : Nat.card A = Nat.card K ^ 2)
    (hfix : Nat.card ↥(fixV A) = Nat.card K ^ 4) :
    ∃ f : (Fin 3 → K) →ₗ[K] K, f ≠ 0 ∧ fixPlane A = LinearMap.ker f ∧
      (∀ y ∈ A, ∃ w, f w = 0 ∧ ∀ v, toAddMap y v = trvW f w v) ∧
      (∀ w, f w = 0 → ∃ y ∈ A, ∀ v, toAddMap y v = trvW f w v) := by
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hS2 : Module.finrank K (fixPlane A) = 2 := by
    rw [card_fixV_eq_sq hAD, show Nat.card K ^ 4 = (Nat.card K ^ 2) ^ 2 by ring] at hfix
    have h1 := Nat.pow_left_injective (by norm_num : 2 ≠ 0) hfix
    rw [Module.natCard_eq_pow_finrank (K := K)] at h1
    exact Nat.pow_right_injective hq h1
  have hlt : fixPlane A < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun h => ?_
    have := hS2
    rw [h, finrank_top, Module.finrank_fin_fun] at this
    omega
  obtain ⟨f, hf0, hf⟩ := Submodule.exists_le_ker_of_lt_top _ hlt
  have hkerf : fixPlane A = LinearMap.ker f := by
    refine Submodule.eq_of_le_of_finrank_le hf ?_
    have h1 := LinearMap.finrank_range_add_finrank_ker f
    rw [Module.finrank_fin_fun] at h1
    have h3 : Module.finrank K (LinearMap.range f) ≠ 0 := fun h =>
      hf0 (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h))
    omega
  obtain ⟨v₀, hv₀⟩ : ∃ v₀, f v₀ = 1 := by
    obtain ⟨u, hu⟩ : ∃ u, f u ≠ 0 := by
      by_contra h
      push Not at h
      exact hf0 (LinearMap.ext h)
    exact ⟨(f u)⁻¹ • u, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hu]⟩
  let wy : MulAut (W6 K) → Fin 3 → K := fun y => toAddMap y (Sum.elim v₀ 0) ∘ Sum.inl - v₀
  have hform : ∀ y ∈ A, f (wy y) = 0 ∧ ∀ v, toAddMap y v = trvW f (wy y) v := by
    intro y hy
    obtain ⟨g, rfl⟩ := hAD hy
    have hgF : g ∈ dgMat A := ⟨hy, matAut_dgHom_mem_dgSub g⟩
    have hker : ∀ v, f v = 0 → (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v := fun v hv =>
      mem_fixPlane.mp (hkerf ▸ hv : v ∈ fixPlane A) g hgF
    have hwy : wy (matAut (dgHom g)) = (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v₀ - v₀ := by
      simp only [wy, toAddMap_matAut, dgHom_mulVec, Sum.elim_comp_inl]
    have hg := eq_add_of_ker f hv₀ hker
    have hfw : f (wy (matAut (dgHom g))) = 0 := by
      rw [hwy]
      set w := (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v₀ - v₀ with hw
      have hgv : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v₀ = v₀ + w := by rw [hw]; abel
      have hgw : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w = w + f w • w := hg w
      have h1 : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v₀) = v₀ := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, dgMat_sq hA g hgF, Units.val_one,
          Matrix.one_mulVec]
      rw [hgv, Matrix.mulVec_add, hgv, hgw] at h1
      have hww : w + w = 0 := by
        funext j
        exact CharTwo.add_self_eq_zero (w j)
      have h2 : f w • w = 0 := by
        calc f w • w = (w + w) + f w • w := by rw [hww, zero_add]
          _ = (v₀ + w + (w + f w • w)) - v₀ := by abel
          _ = 0 := by rw [h1, sub_self]
      rcases smul_eq_zero.mp h2 with h | h
      · exact h
      · rw [h, map_zero]
    refine ⟨hfw, fun v => ?_⟩
    change toAddMap (matAut (dgHom g)) v = trvW f (wy (matAut (dgHom g))) v
    rw [toAddMap_matAut, dgHom_mulVec, hwy]
    funext i
    rcases i with i | i
    · exact congrFun (hg (v ∘ Sum.inl)) i
    · exact congrFun (hg (v ∘ Sum.inr)) i
  refine ⟨f, hf0, hkerf, fun y hy => ⟨wy y, (hform y hy).1, (hform y hy).2⟩, fun w hw => ?_⟩
  let φ : ↥A → {w : Fin 3 → K // f w = 0} := fun y => ⟨wy y, (hform y y.2).1⟩
  have hinj : Function.Injective φ := by
    intro y y' h
    have h1 : wy y = wy y' := congrArg Subtype.val h
    apply Subtype.ext
    apply toAddMap_injective
    intro v
    rw [(hform y y.2).2, (hform y' y'.2).2, h1]
  have hcardS : Nat.card {w : Fin 3 → K // f w = 0} = Nat.card K ^ 2 := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun w => (LinearMap.mem_ker (f := f)).symm),
      Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.ker f), ← hkerf, hS2]
  obtain ⟨y, hy⟩ := (hinj.bijective_of_nat_card_le (by rw [hcardS, hcard])).2 ⟨w, hw⟩
  have hyw : wy y = w := congrArg Subtype.val hy
  exact ⟨y, y.2, fun v => by rw [(hform y y.2).2, hyw]⟩

end CFSG.Quasithin.Vol2.Ch11.SecB.K8
