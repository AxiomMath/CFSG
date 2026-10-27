module

public import CFSG.Quasithin.Vol2.Ch11SecBK7F
public import CFSG.Quasithin.Vol2.Ch11SecO1bB
public import CFSG.Quasithin.Vol2.KGNatSL3Line

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecO1b

open CFSG.Quasithin CFSG.Quasithin.H13 KGNat SecA
open CFSG.Open (pCoreOf)
open CFSG.ClassicalInvolution.ModelFacts.OddCover Matrix
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (flagSpace)
open CFSG.QuasithinUnique.Setup.X7a (Q2)
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ : Subgroup G}
  [IsMulCommutative ↥(fsuV T I)] {K : Type} [Field K] [Finite K] [CharP K 2]

section SL3

variable {π : ↥(StatedSL 3 K) →* ↥(autOn L (fsuV T I))} {f : ↥(fsuV T I) → (Fin 3 → K)}
  {g : SpecialLinearGroup (Fin 3) K}

omit [CharP K 2] in
theorem mem_V1_sl3_iff (hS : SecD.NatSetting11 G T L I n) (hK : Nat.card K = 2 ^ n)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) (autOn L (fsuV T I)) ⊥ π f)
    (hg : ∀ x : MulAut ↥(fsuV T I), x ∈ autOn (T ⊓ L) (fsuV T I) ↔
      ∃ u ∈ Usl K, x = ((rho3 π (g * u * g⁻¹) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)))
    (hV₁ : IsVi T L I n 1 V₁) (v : ↥(fsuV T I)) :
    (v : G) ∈ V₁ ↔ ∃ c : K, f v = c • ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![1, 0, 0]) := by
  rw [← Subgroup.mem_subgroupOf, mem_V1_sl3 hS hK hf hg hV₁]
  exact mem_pre_line_iff hf g v

theorem r1_linear_sl3 (hS : SecD.NatSetting11 G T L I n) (hK : Nat.card K = 2 ^ n)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) (autOn L (fsuV T I)) ⊥ π f)
    (hg : ∀ x : MulAut ↥(fsuV T I), x ∈ autOn (T ⊓ L) (fsuV T I) ↔
      ∃ u ∈ Usl K, x = ((rho3 π (g * u * g⁻¹) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)))
    (hV₁ : IsVi T L I n 1 V₁) {r : G} (hr : r ∈ ROf T L V₁) :
    ∃ A : (Fin 3 → K) →ₗ[K] (Fin 3 → K),
      ∀ w, f (SecA.conjV (fsuV T I) r (r1_le_normalizer hS hV₁ hr) w) = A (f w) := by
  obtain ⟨a, b, hab⟩ := r1_shape_sl3 hS hK hf hg hV₁ hr
  refine ⟨Matrix.mulVecLin ((g : Matrix (Fin 3) (Fin 3) K) * (uMat a b 0 *
    ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))), fun w => ?_⟩
  rw [Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← hab w,
    Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem comm_mem_V1_sl3 (hS : SecD.NatSetting11 G T L I n) (hK : Nat.card K = 2 ^ n)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) (autOn L (fsuV T I)) ⊥ π f)
    (hg : ∀ x : MulAut ↥(fsuV T I), x ∈ autOn (T ⊓ L) (fsuV T I) ↔
      ∃ u ∈ Usl K, x = ((rho3 π (g * u * g⁻¹) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)))
    (hV₁ : IsVi T L I n 1 V₁) {r : G} (hr : r ∈ ROf T L V₁) (v : ↥(fsuV T I)) :
    ((SecA.conjV (fsuV T I) r (r1_le_normalizer hS hV₁ hr) v * v⁻¹ : ↥(fsuV T I)) : G) ∈ V₁ := by
  obtain ⟨a, b, hab⟩ := r1_shape_sl3 hS hK hf hg hV₁ hr
  rw [← Subgroup.mem_subgroupOf, mem_V1_sl3 hS hK hf hg hV₁]
  change f (_ * _) ∈ gmap g (flagSpace 3 K 1)
  rw [hf.map_mul_inv, mem_gmap, Matrix.mulVec_sub, hab v, uMat_mulVec, ← stdLine_eq_flagSpace]
  exact ⟨by simp, by simp⟩

end SL3

section Sp4

variable {π : ↥(StatedSp 2 K) →* ↥(autOn L (fsuV T I))} {f : ↥(fsuV T I) → (Fin 2 ⊕ Fin 2 → K)}
  {g : StatedSp 2 K}

omit [CharP K 2] in
theorem mem_V1_sp4_iff (hS : SecD.NatSetting11 G T L I n) (hK : Nat.card K = 2 ^ n)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) (autOn L (fsuV T I)) ⊥ π f)
    (hg : ∀ x : MulAut ↥(fsuV T I), x ∈ autOn (T ⊓ L) (fsuV T I) ↔
      ∃ u ∈ Usp K, x = ((π (g * u * g⁻¹) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)))
    (hV₁ : IsVi T L I n 1 V₁) (v : ↥(fsuV T I)) :
    (v : G) ∈ V₁ ↔ ∃ c : K, f v = c • (mat 2 K g *ᵥ vec4 1 0 0 0) := by
  rw [← Subgroup.mem_subgroupOf, mem_V1_sp4 hS hK hf hg hV₁]
  exact mem_gS1_iff g (f v)

omit [CharP K 2] in
theorem mem_V3_sp4_iff (hS : SecD.NatSetting11 G T L I n) (hK : Nat.card K = 2 ^ n)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) (autOn L (fsuV T I)) ⊥ π f)
    (hg : ∀ x : MulAut ↥(fsuV T I), x ∈ autOn (T ⊓ L) (fsuV T I) ↔
      ∃ u ∈ Usp K, x = ((π (g * u * g⁻¹) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)))
    {V₃ : Subgroup G} (hV₃ : IsVi T L I n 3 V₃) (v : ↥(fsuV T I)) :
    (v : G) ∈ V₃ ↔ (mat 2 K g⁻¹ *ᵥ f v) (.inr 0) = 0 := by
  rw [← Subgroup.mem_subgroupOf, mem_V3_sp4 hS hK hf hg hV₃]
  exact mem_gmapSp

theorem comm_mem_V1_sp4 (hS : SecD.NatSetting11 G T L I n) (hK : Nat.card K = 2 ^ n)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) (autOn L (fsuV T I)) ⊥ π f)
    (hg : ∀ x : MulAut ↥(fsuV T I), x ∈ autOn (T ⊓ L) (fsuV T I) ↔
      ∃ u ∈ Usp K, x = ((π (g * u * g⁻¹) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)))
    (hV₁ : IsVi T L I n 1 V₁) {V₃ : Subgroup G} (hV₃ : IsVi T L I n 3 V₃) {r : G}
    {N : StatedSp 2 K} (hN : N ∈ pCoreOf 2 (perfectCore (Q2 K 0))) (hr : r ∈ ROf T L V₁)
    (hrN : ∀ w, f (SecA.conjV (fsuV T I) r (r1_le_normalizer hS hV₁ hr) w) =
      mat 2 K (g * N * g⁻¹) *ᵥ f w)
    (v : ↥(fsuV T I)) (hv : (v : G) ∈ V₃) :
    ((SecA.conjV (fsuV T I) r (r1_le_normalizer hS hV₁ hr) v * v⁻¹ : ↥(fsuV T I)) : G) ∈ V₁ := by
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four
    (four_le_card hS.one_lt hK)
  rw [← Subgroup.mem_subgroupOf, mem_V1_sp4 hS hK hf hg hV₁]
  change f (_ * _) ∈ gmapSp g (spLine K)
  have hx := (mem_V3_sp4_iff hS hK hf hg hV₃ v).mp hv
  obtain ⟨h1, h2, h3⟩ := KA.pCore_mulVec hK4 hN hx
  rw [hf.map_mul_inv, hrN, mem_gmapSp, Matrix.mulVec_sub, KA.gconj_mulVec_sp, mat_inv_mulVec]
  refine ⟨?_, ?_, ?_⟩
  · rw [Pi.sub_apply, h1, sub_self]
  · rw [Pi.sub_apply, h2, hx, sub_self]
  · rw [Pi.sub_apply, h3, sub_self]

theorem comm_mem_V1_of_fix (hS : SecD.NatSetting11 G T L I n) (hK : Nat.card K = 2 ^ n)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) (autOn L (fsuV T I)) ⊥ π f)
    (hg : ∀ x : MulAut ↥(fsuV T I), x ∈ autOn (T ⊓ L) (fsuV T I) ↔
      ∃ u ∈ Usp K, x = ((π (g * u * g⁻¹) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)))
    (hV₁ : IsVi T L I n 1 V₁) {r : G} {N : StatedSp 2 K} (hr : r ∈ ROf T L V₁)
    (hrN : ∀ w, f (SecA.conjV (fsuV T I) r (r1_le_normalizer hS hV₁ hr) w) =
      mat 2 K (g * N * g⁻¹) *ᵥ f w)
    (hfix : ∀ x : Fin 2 ⊕ Fin 2 → K, x (.inr 0) = 0 → mat 2 K N *ᵥ x = x)
    (v : ↥(fsuV T I)) :
    ((SecA.conjV (fsuV T I) r (r1_le_normalizer hS hV₁ hr) v * v⁻¹ : ↥(fsuV T I)) : G) ∈ V₁ := by
  have he0 : (vec4 1 0 0 0 : Fin 2 ⊕ Fin 2 → K) ≠ 0 := fun h =>
    (one_ne_zero : (1 : K) ≠ 0) (congrFun h (.inl 0))
  obtain ⟨c, hc⟩ := SecB.K7.eq_trv_of_fix he0 fun x hx => hfix x (by
    rw [SecB.K7.bil_comm, spB_e0] at hx
    exact hx)
  rw [← Subgroup.mem_subgroupOf, mem_V1_sp4 hS hK hf hg hV₁]
  change f (_ * _) ∈ gmapSp g (spLine K)
  rw [hf.map_mul_inv, hrN, mem_gmapSp, Matrix.mulVec_sub, KA.gconj_mulVec_sp, mat_inv_mulVec,
    hc, SecB.K7.trv_mulVec, add_sub_cancel_left]
  exact (spLine K).smul_mem _ ⟨rfl, rfl, rfl⟩

theorem r1_linear_sp4 (hS : SecD.NatSetting11 G T L I n) (hK : Nat.card K = 2 ^ n)
    (hπ : (FFModel.nat (StatedSp 2 K)).RealizesVia (autOn L (fsuV T I)) ⊤ ⊥ π)
    (hf : IsCoord (linModelNat (StatedSp 2 K)) (autOn L (fsuV T I)) ⊥ π f)
    (hg : ∀ x : MulAut ↥(fsuV T I), x ∈ autOn (T ⊓ L) (fsuV T I) ↔
      ∃ u ∈ Usp K, x = ((π (g * u * g⁻¹) : ↥(autOn L (fsuV T I))) : MulAut ↥(fsuV T I)))
    (hV₁ : IsVi T L I n 1 V₁) {r : G} (hr : r ∈ ROf T L V₁) :
    ∃ A : (Fin 2 ⊕ Fin 2 → K) →ₗ[K] (Fin 2 ⊕ Fin 2 → K),
      ∀ w, f (SecA.conjV (fsuV T I) r (r1_le_normalizer hS hV₁ hr) w) = A (f w) := by
  obtain ⟨N, -, hN⟩ := r1_shape_sp4 hS hK hπ hf hg hV₁ hr
  exact ⟨Matrix.mulVecLin (mat 2 K (g * N * g⁻¹)), fun w => by
    rw [Matrix.mulVecLin_apply, hN w]⟩

end Sp4

end CFSG.Quasithin.Vol2.Ch11.SecO1b
