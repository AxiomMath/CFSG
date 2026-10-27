module

public import TauCeti.LinearAlgebra.RootSystem.FiniteType.Basic
public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.Data.Int.Order.Units
public import Mathlib.Tactic.Group
public import CFSG.LieType.Steinberg.OfCartan
public import CFSG.LieType.RootSystem.Basic
public import Mathlib.Tactic.IntervalCases
public import TauCeti.LinearAlgebra.RootSystem.Coxeter.Matrix
public import CFSG.LocalAnalysis.StandardType.GGWeylCartan
public import CFSG.LieType.RootSystem.Positivity
public import Mathlib.Data.Set.Card
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRootRefl
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import CFSG.LocalAnalysis.StandardType.GGResSideDatumDefs
public import CFSG.LocalAnalysis.StandardType.GGWeylSimpleConjBasic
public import CFSG.LocalAnalysis.StandardType.GGWeylSimpleConjCone

public section

namespace CFSG.StandardType.S2MathFi1451

open CFSG CFSG.Assembly CFSG.LieType.RootSystem CFSG.StandardType.SecFiveRootRefl
  CFSG.StandardType

theorem cartanTree_G₂ : CartanTree CartanMatrix.G₂ :=
  cartanTree_chain (by norm_num) _ fun i j => by fin_cases i <;> fin_cases j <;> decide

private theorem key {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι} {n : ℕ}
    (e : Fin n ≃ ι)
    (M₀ : CoxeterMatrix (Fin n)) (C₀ : Matrix (Fin n) (Fin n) ℤ) (hMe : M = M₀.reindex e)
    (hC₀ : GGIntCartan M₀ C₀) (hFT₀ : TauCeti.IsFiniteType C₀) (hT : CartanTree C₀) :
    ∃ (C : Matrix ι ι ℤ) (hC : TauCeti.IsFiniteType C), coxeterMatrix hC = M ∧ CartanTree C := by
  have hC : GGIntCartan M (Matrix.reindex e e C₀) := hMe ▸ hC₀.reindex e
  have hFT : TauCeti.IsFiniteType (Matrix.reindex e e C₀) := by
    rw [Matrix.reindex_apply]
    exact hFT₀.submatrix e.symm.injective
  exact ⟨_, hFT, (coxeterMatrix_eq_of_ggIntCartan hFT hC), hT.reindex e⟩

theorem ggWeyl_exists_cartanTree {ι : Type} [Fintype ι] [DecidableEq ι] {M : CoxeterMatrix ι}
    (hM : GGIsWeylMatrix M) :
    ∃ (C : Matrix ι ι ℤ) (hC : TauCeti.IsFiniteType C), coxeterMatrix hC = M ∧ CartanTree C := by
  rcases hM with ⟨n, e, hn, hMA | ⟨hn2, hMB⟩ | ⟨hn4, hMD⟩⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ |
    ⟨e, hF4⟩ | ⟨e, hMG⟩
  · exact key e _ _ hMA (ggIntCartan_A n) (TauCeti.isFiniteType_cartanMatrix_A n)
      (cartanTree_A n hn)
  · exact key e _ _ hMB (ggIntCartan_B n) (TauCeti.isFiniteType_cartanMatrix_B n)
      (cartanTree_B n (by omega))
  · exact key e _ _ hMD (ggIntCartan_D n) (TauCeti.isFiniteType_cartanMatrix_D n)
      (cartanTree_D n hn4)
  · have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_E6
    rw [TauCeti.DynkinType.cartanMatrix_E6] at h
    exact key e _ _ hE6 ggIntCartan_E₆ h (cartanTree_E 6 (by norm_num))
  · have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_E7
    rw [TauCeti.DynkinType.cartanMatrix_E7] at h
    exact key e _ _ hE7 ggIntCartan_E₇ h (cartanTree_E 7 (by norm_num))
  · have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_E8
    rw [TauCeti.DynkinType.cartanMatrix_E8] at h
    exact key e _ _ hE8 ggIntCartan_E₈ h (cartanTree_E 8 (by norm_num))
  · have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_F4
    rw [TauCeti.DynkinType.cartanMatrix_F4] at h
    exact key e _ _ hF4 ggIntCartan_F₄ h cartanTree_F₄
  · have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_G2
    rw [TauCeti.DynkinType.cartanMatrix_G2] at h
    have h1 : TauCeti.IsFiniteType (CartanMatrix.G₂.transpose : Matrix (Fin 2) (Fin 2) ℤ) := h
    have h' := h1.transpose
    rw [Matrix.transpose_transpose] at h'
    exact key e _ _ hMG ggIntCartan_G₂ h' cartanTree_G₂

end CFSG.StandardType.S2MathFi1451

namespace CFSG.StandardType.S2MathFi1451

open CFSG.LieType.RootSystem CFSG.LieType.Steinberg.OfCartan CFSG.StandardType.SecFiveRootRefl

theorem coxeterOrder_injOn {c c' : ℤ} (hc : c ∈ ({0, 1, 2, 3} : Set ℤ))
    (hc' : c' ∈ ({0, 1, 2, 3} : Set ℤ)) (h : TauCeti.coxeterOrder c = TauCeti.coxeterOrder c') :
    c = c' := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hc hc'
  rcases hc with rfl | rfl | rfl | rfl <;> rcases hc' with rfl | rfl | rfl | rfl <;>
    simp_all [TauCeti.coxeterOrder_zero, TauCeti.coxeterOrder_one, TauCeti.coxeterOrder_two,
      TauCeti.coxeterOrder_three]

theorem simpleSystems_conj {Λ Λ' : Type} [Fintype Λ] [DecidableEq Λ] [Fintype Λ']
    [DecidableEq Λ'] {A : Matrix Λ Λ ℤ} (hA : TauCeti.IsFiniteType A) {C : Matrix Λ' Λ' ℤ}
    (hC : TauCeti.IsFiniteType C) (hT : CartanTree C)
    (τ : (coxeterMatrix hC).Group ≃* (coxeterMatrix hA).Group)
    (hτ : ∀ k, ∃ (w : (coxeterMatrix hA).Group) (i : Λ),
      τ ((coxeterMatrix hC).toCoxeterSystem.simple k) =
        w * (coxeterMatrix hA).toCoxeterSystem.simple i * w⁻¹) :
    ∃ (σ : Λ ≃ Λ') (x : (coxeterMatrix hA).Group), ∀ i,
      τ ((coxeterMatrix hC).toCoxeterSystem.simple (σ i)) =
        x * (coxeterMatrix hA).toCoxeterSystem.simple i * x⁻¹ := by
  classical
  have hsA : ∀ i, (coxeterMatrix hA).toCoxeterSystem.simple i = (coxeterMatrix hA).simple i :=
    fun i => by rw [CoxeterMatrix.toCoxeterSystem_simple]
  choose w0 i0 hτw using hτ
  let t : Λ' → (coxeterMatrix hA).Group := fun k => τ ((coxeterMatrix hC).toCoxeterSystem.simple k)
  let β : Λ' → Λ → ℤ := fun k => weylAction hA (w0 k) (Pi.single (i0 k) 1)
  let βc : Λ' → (Λ → ℤ) →ₗ[ℤ] ℤ := fun k => rootCoroot hA (w0 k) (i0 k)
  let a : Λ' → Λ' → ℤ := fun k l => βc k (β l)
  have ha_self : ∀ k, a k k = 2 := fun k => rootCoroot_self hA (w0 k) (i0 k)
  have hprod : ∀ k l, k ≠ l → (a k l = 0 ↔ a l k = 0) ∧ a k l * a l k = C k l * C l k := by
    intro k l hkl
    have hne : w0 k * (coxeterMatrix hA).toCoxeterSystem.simple (i0 k) * (w0 k)⁻¹ ≠
        w0 l * (coxeterMatrix hA).toCoxeterSystem.simple (i0 l) * (w0 l)⁻¹ := by
      rw [← hτw k, ← hτw l]
      intro h
      exact hkl ((coxeterMatrix hC).toCoxeterSystem.simple_injective (τ.injective h))
    obtain ⟨hmem, hiff, hord⟩ := orderOf_conj_mul_conj hA hne
    refine ⟨hiff, ?_⟩
    have hordC : orderOf (w0 k * (coxeterMatrix hA).toCoxeterSystem.simple (i0 k) * (w0 k)⁻¹ *
        (w0 l * (coxeterMatrix hA).toCoxeterSystem.simple (i0 l) * (w0 l)⁻¹)) =
        TauCeti.coxeterOrder (C k l * C l k) := by
      rw [← hτw k, ← hτw l, ← map_mul, MulEquiv.orderOf_eq,
        (coxeterMatrix hC).toCoxeterSystem.orderOf_simple_mul_simple]
      simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply]
    exact coxeterOrder_injOn hmem (hC.apply_mul_apply_mem_of_ne hkl) (hord.symm.trans hordC)
  obtain ⟨par, root, depth, hpar, hdepth⟩ := hT
  have hC0 : ∀ k l, k ≠ l → C k l = 0 → a k l = 0 := by
    intro k l hkl h0
    obtain ⟨hiff, hp⟩ := hprod k l hkl
    rw [h0, zero_mul] at hp
    rcases mul_eq_zero.mp hp with h | h
    · exact h
    · exact hiff.mpr h
  obtain ⟨c, hc0, hc⟩ := exists_gauge_of_tree (K := ℚ) C (fun k l => (a k l : ℚ)) par root depth
    (fun k l hkl h0 => by simp [hC0 k l hkl h0])
    (fun k l hkl _ => by exact_mod_cast (hprod k l hkl).2)
    (fun k l _ h0 => by exact_mod_cast h0) hpar hdepth
  let ε : Λ' → ℤ := fun k => if 0 < c k then 1 else -1
  have hε2 : ∀ k, ε k * ε k = 1 := fun k => by
    simp only [ε]
    split_ifs <;> norm_num
  have hεc : ∀ k, 0 < (ε k : ℚ) * c k := fun k => by
    simp only [ε]
    split_ifs with h
    · simpa using h
    · have : c k < 0 := lt_of_le_of_ne (not_lt.mp h) (hc0 k)
      push_cast
      linarith
  have hεcases : ∀ k (v : Λ → ℤ), ε k • v = v ∨ ε k • v = -v := fun k v => by
    simp only [ε]
    split_ifs <;> simp
  let π : Λ' → Λ → ℤ := fun k => ε k • β k
  let πc : Λ' → (Λ → ℤ) →ₗ[ℤ] ℤ := fun k => ε k • βc k
  obtain ⟨A', hA'def⟩ : ∃ A' : Matrix Λ' Λ' ℤ, A' = Matrix.of fun k l => πc k (π l) := ⟨_, rfl⟩
  have hcart : ∀ k l, πc k (π l) = A' k l := fun k l => by rw [hA'def, Matrix.of_apply]
  have hA'kl : ∀ k l, A' k l = ε k * ε l * a k l := fun k l => by
    rw [← hcart]
    simp only [π, πc, LinearMap.smul_apply, map_zsmul, smul_eq_mul, a]
    ring
  have h2 : ∀ k, A' k k = 2 := fun k => by rw [hA'kl, hε2, one_mul, ha_self]
  have hsim : ∀ k l, k ≠ l →
      (A' k l : ℚ) = ((ε k : ℚ) * c k) * C k l / ((ε l : ℚ) * c l) := by
    intro k l hkl
    have hg := hc k l hkl
    try simp only at hg
    have hck := hc0 k
    have hcl := hc0 l
    have hεl : (ε l : ℚ) * ε l = 1 := by exact_mod_cast hε2 l
    have hεl0 : (ε l : ℚ) ≠ 0 := fun h => by rw [h, zero_mul] at hεl; norm_num at hεl
    rw [hA'kl]
    push_cast
    rw [← hg]
    field_simp
    linear_combination (ε k : ℚ) * (a k l : ℚ) * hεl
  have hA' : TauCeti.IsFiniteType A' :=
    isFiniteType_of_diagonal_similar hC (fun k => (ε k : ℚ) * c k) hεc h2 hsim
  have hAA : ∀ k l, A' k l * A' l k = C k l * C l k := by
    intro k l
    by_cases hkl : k = l
    · subst hkl
      rw [h2, hC.apply_self]
    · rw [hA'kl, hA'kl, ← (hprod k l hkl).2]
      linear_combination (a k l * a l k * ε l * ε l) * hε2 k + (a k l * a l k) * hε2 l
  have hcox : coxeterMatrix hA' = coxeterMatrix hC := by
    refine CoxeterMatrix.ext (Matrix.ext fun k l => ?_)
    have := TauCeti.coxeterMatrixOfCartanMatrix_apply A' hA'.apply_self
      (fun _ _ h => hA'.apply_mul_apply_mem_of_ne h) k l
    have h' := TauCeti.coxeterMatrixOfCartanMatrix_apply C hC.apply_self
      (fun _ _ h => hC.apply_mul_apply_mem_of_ne h) k l
    rw [hAA] at this
    exact this.trans h'.symm
  have hlift : (coxeterMatrix hA').IsLiftable t := by
    intro k l
    rw [hcox]
    simp only [t]
    rw [← map_mul, ← map_pow, (coxeterMatrix hC).toCoxeterSystem.simple_mul_simple_pow, map_one]
  let h := (coxeterMatrix hA').toCoxeterSystem.lift ⟨t, hlift⟩
  have hh : ∀ k, h ((coxeterMatrix hA').toCoxeterSystem.simple k) = t k := fun k =>
    (coxeterMatrix hA').toCoxeterSystem.lift_apply_simple hlift k
  have hrefl : ∀ k v, weylAction hA (h ((coxeterMatrix hA').toCoxeterSystem.simple k)) v =
      v - πc k v • π k := by
    intro k v
    rw [hh, show t k = _ from hτw k, weylAction_conj_simple]
    have : πc k v • π k = βc k v • β k := by
      simp only [πc, π]
      rw [LinearMap.smul_apply, smul_eq_mul, smul_smul, mul_comm (ε k) (βc k v), mul_assoc, hε2,
        mul_one]
    rw [this]
    rfl
  have hgen : Subgroup.closure (Set.range t) = ⊤ := by
    have hr : Set.range t =
        τ.toMonoidHom '' Set.range (coxeterMatrix hC).toCoxeterSystem.simple := by
      ext x
      simp [t]
    rw [hr, ← MonoidHom.map_closure,
      (coxeterMatrix hC).toCoxeterSystem.subgroup_closure_range_simple,
      Subgroup.map_top_of_surjective _ τ.surjective]
  have hsurj : Function.Surjective h := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    exact ⟨_, hh k⟩
  let φ := Fintype.linearCombination ℤ π
  have hQneg : ∀ v : Λ → ℤ, (∃ x : Λ' → ℤ, (0 ≤ x ∨ x ≤ 0) ∧ v = φ x) →
      ∃ x : Λ' → ℤ, (0 ≤ x ∨ x ≤ 0) ∧ -v = φ x := by
    rintro v ⟨x, hx, rfl⟩
    exact ⟨-x, hx.symm.imp neg_nonneg.mpr neg_nonpos.mpr, by rw [map_neg]⟩
  have hεβ : ∀ k, β k = ε k • π k := fun k => by
    simp only [π, smul_smul, hε2, one_smul]
  have htT : ∀ k, ∃ (w : (coxeterMatrix hA).Group) (i : Λ),
      t k = w * (coxeterMatrix hA).simple i * w⁻¹ :=
    fun k => ⟨w0 k, i0 k, by rw [show t k = _ from hτw k, hsA]⟩
  have hcone : ∀ (w : (coxeterMatrix hA).Group) (i : Λ), ∃ x : Λ' → ℤ, (0 ≤ x ∨ x ≤ 0) ∧
      weylAction hA w (Pi.single i 1) = φ x := by
    intro w i
    obtain ⟨u, k, hu⟩ := exists_conj_of_closure_eq_top t htT hgen i
    have hconj : w * (coxeterMatrix hA).toCoxeterSystem.simple i * w⁻¹ =
        (w * u * w0 k) * (coxeterMatrix hA).toCoxeterSystem.simple (i0 k) * (w * u * w0 k)⁻¹ := by
      rw [hsA i, hu, show t k = _ from hτw k]
      group
    obtain ⟨g, hg⟩ := hsurj (w * u)
    obtain ⟨x, hx, hxe⟩ := transported_nonneg_or_nonpos hA hA' h π πc hrefl hcart g k
    have hbase : ∃ x : Λ' → ℤ, (0 ≤ x ∨ x ≤ 0) ∧
        weylAction hA (w * u * w0 k) (Pi.single (i0 k) 1) = φ x := by
      rw [weylAction_mul_apply, show weylAction hA (w0 k) (Pi.single (i0 k) 1) = β k from rfl,
        hεβ k, map_zsmul, ← hg]
      rcases hεcases k (weylAction hA (h g) (π k)) with he | he <;> rw [he]
      · exact ⟨x, hx, hxe⟩
      · exact hQneg _ ⟨x, hx, hxe⟩
    rcases weylAction_eq_or_eq_neg_of_conj_eq hA hconj with h1 | h1 <;> rw [h1]
    · exact hbase
    · exact hQneg _ hbase
  have hπ : ∀ k, ∃ (w : (coxeterMatrix hA).Group) (i : Λ),
      π k = weylAction hA w (Pi.single i 1) := by
    intro k
    rcases hεcases k (β k) with he | he
    · exact ⟨w0 k, i0 k, he⟩
    · exact ⟨w0 k * (coxeterMatrix hA).toCoxeterSystem.simple (i0 k), i0 k, by
        rw [show π k = ε k • β k from rfl, he, weylAction_mul_apply, weylAction_simple_single,
          map_neg]⟩
  have hind : LinearIndependent ℤ π := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hmul : Matrix.mulVec A' g = 0 := by
      funext l
      have := congrArg (πc l) hg
      rw [map_sum, map_zero] at this
      simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
      rw [← this]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_zsmul, smul_eq_mul, hcart, mul_comm]
    exact congrFun (Matrix.eq_zero_of_mulVec_eq_zero hA'.det_ne_zero hmul)
  obtain ⟨u, σ, hσ⟩ := exists_weylAction_eq_of_cone hA π hπ hind hcone
  refine ⟨σ, u, fun i => ?_⟩
  rw [hτw (σ i)]
  have hε0 : (ε (σ i) : ℚ) ≠ 0 := by
    intro h0
    have := hε2 (σ i)
    have h0' : ε (σ i) = 0 := by exact_mod_cast h0
    rw [h0', zero_mul] at this
    exact absurd this (by norm_num)
  refine (ggWeyl_conj_simple_eq_of_root_smul hA u (w0 (σ i)) i (i0 (σ i)) hε0 ?_).symm
  rw [hσ i, show π (σ i) = ε (σ i) • β (σ i) from rfl, map_zsmul, ← Int.cast_smul_eq_zsmul ℚ]

end CFSG.StandardType.S2MathFi1451

namespace CFSG.StandardType

open CFSG.LieType.RootSystem

theorem ggWeylSimpleSystemsConjInput_holds : GGWeylSimpleSystemsConjInput := by
  intro Λ Λ' _ _ _ _ M M' hM hM' W _ f f' hconj
  obtain ⟨A, hA, rfl, -⟩ := S2MathFi1451.ggWeyl_exists_cartanTree hM
  obtain ⟨C, hC, rfl, hT⟩ := S2MathFi1451.ggWeyl_exists_cartanTree hM'
  obtain ⟨σ, x, hx⟩ := S2MathFi1451.simpleSystems_conj hA hC hT (f'.trans f.symm) (fun k => by
    obtain ⟨w, i, h⟩ := hconj k
    refine ⟨f.symm w, i, ?_⟩
    rw [MulEquiv.trans_apply, CoxeterMatrix.toCoxeterSystem_simple,
      CoxeterMatrix.toCoxeterSystem_simple, h]
    simp)
  refine ⟨σ, f x, fun i => ?_⟩
  have := congrArg f (hx i)
  simpa [CoxeterMatrix.toCoxeterSystem_simple] using this

end CFSG.StandardType
