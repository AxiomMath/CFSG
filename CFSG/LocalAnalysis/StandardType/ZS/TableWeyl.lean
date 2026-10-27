module

public import CFSG.LocalAnalysis.StandardType.ZS.TableCommon
public import CFSG.LocalAnalysis.StandardType.ZS.RootMatrix
import CFSG.LocalAnalysis.StandardType.ZS.TypeA
import CFSG.LocalAnalysis.StandardType.ZS.WeylModule
import CFSG.LocalAnalysis.StandardType.ZS.AdaptMonomial
import CFSG.LocalAnalysis.StandardType.ZS.TableWeylChar
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.GGKGPosRootPairs
import CFSG.GroupTheory.SwapMulOrder

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem orderOf_mul_le_three_of_typeA (hp : p ≠ 2) [Module.Finite (ZMod p) U] {ℓ : ℕ}
    {J : Subgroup (U ≃ₗ[ZMod p] U)} (T : Equiv.Perm (Fin (ℓ + 1)) ≃* J)
    (hT : ∀ k : Fin ℓ, IsRefl p (T (Equiv.swap k.castSucc k.succ) : U ≃ₗ[ZMod p] U))
    {x y : U ≃ₗ[ZMod p] U} (hx : x ∈ J) (hy : y ∈ J) (hrx : IsRefl p x) (hry : IsRefl p y) :
    orderOf (x * y) ≤ 3 := by
  have hx' : (T.symm ⟨x, hx⟩).IsSwap := isSwap_symm_apply_of_isRefl hp T hT hrx
  have hy' : (T.symm ⟨y, hy⟩).IsSwap := isSwap_symm_apply_of_isRefl hp T hT hry
  have hcoe : (x * y) =
      ((T (T.symm ⟨x, hx⟩ * T.symm ⟨y, hy⟩) : J) : U ≃ₗ[ZMod p] U) := by
    rw [map_mul, T.apply_symm_apply, T.apply_symm_apply]
    rfl
  rw [hcoe, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  have hmem := CFSG.GroupTheory.orderOf_mul_mem_of_isSwap hx' hy'
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  omega

private theorem cartanModel_isLiftable (hp : p ≠ 2) {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Matrix ι ι ℤ} (hK : TauCeti.IsFiniteType K)
    (hconn : GGSimplyLacedConnected (CFSG.LieType.RootSystem.coxeterMatrix hK))
    {u : ι → U} {φ : ι → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hdata : ∀ i j, φ i (u j) = (K i j : ZMod p)) :
    (CFSG.LieType.RootSystem.coxeterMatrix hK).IsLiftable
      (fun i => Module.reflection (hφ i)) := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [(CFSG.LieType.RootSystem.coxeterMatrix hK).diagonal i, pow_one]
    exact (isRefl_reflection hp (hφ i)).1
  · have hmem := hK.apply_mul_apply_mem_of_ne hij
    have hMapp : (CFSG.LieType.RootSystem.coxeterMatrix hK) i j =
        TauCeti.coxeterOrder (K i j * K j i) := by
      simp only [CFSG.LieType.RootSystem.coxeterMatrix,
        TauCeti.coxeterMatrixOfCartanMatrix_apply]
    rcases hconn.1 i j hij with h2 | h3
    · have hprod : K i j * K j i = 0 :=
        (TauCeti.coxeterOrder_eq_two_iff hmem).mp (by rw [← hMapp, h2])
      have hKij : K i j = 0 := by
        rcases mul_eq_zero.mp hprod with h | h
        · exact h
        · exact hK.apply_eq_zero_iff.mpr h
      have hz : φ i (u j) = 0 := by rw [hdata i j, hKij]; norm_num
      have hz' : φ j (u i) = 0 := by
        rw [hdata j i, hK.apply_eq_zero_iff.mp hKij]; norm_num
      rw [h2]
      exact reflection_mul_reflection_pow_two (hφ i) (hφ j) hz hz'
    · have hprod : K i j * K j i = 1 := by
        rcases hmem with h0 | h1 | h2' | h3'
        · have hM := hMapp
          rw [h0] at hM; rw [h3] at hM; simp at hM
        · exact h1
        · have hM := hMapp
          rw [h2'] at hM; rw [h3] at hM; simp at hM
        · have hM := hMapp
          rw [h3'] at hM; rw [h3] at hM; simp at hM
      have hcast : (K i j : ZMod p) * (K j i : ZMod p) = 1 := by
        rw [← Int.cast_mul, hprod]; norm_num
      have hz : φ i (u j) * φ j (u i) = 1 := by rw [hdata i j, hdata j i]; exact hcast
      rw [h3]
      exact reflection_mul_reflection_pow_three (hφ i) (hφ j) hz

private theorem orderOf_simple_mul_conj_le_three {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Matrix ι ι ℤ} (hK : TauCeti.IsFiniteType K)
    (hconn : GGSimplyLacedConnected (CFSG.LieType.RootSystem.coxeterMatrix hK))
    (i j : ι) (w : (CFSG.LieType.RootSystem.coxeterMatrix hK).Group) :
    0 < orderOf ((CFSG.LieType.RootSystem.coxeterMatrix hK).simple i * w *
      (CFSG.LieType.RootSystem.coxeterMatrix hK).simple j * w⁻¹) ∧
      orderOf ((CFSG.LieType.RootSystem.coxeterMatrix hK).simple i * w *
        (CFSG.LieType.RootSystem.coxeterMatrix hK).simple j * w⁻¹) ≤ 3 := by
  let M : CoxeterMatrix ι := CFSG.LieType.RootSystem.coxeterMatrix hK
  have ha : M.simple i * M.simple i = 1 := M.toCoxeterSystem.simple_mul_simple_self i
  have hb : (w * M.simple j * w⁻¹) * (w * M.simple j * w⁻¹) = 1 := by
    rw [show (w * M.simple j * w⁻¹) * (w * M.simple j * w⁻¹) =
        w * (M.simple j * M.simple j) * w⁻¹ by group,
      show M.simple j * M.simple j = 1 from M.toCoxeterSystem.simple_mul_simple_self j,
      mul_one, mul_inv_cancel]
  by_cases hcomm : Commute (M.simple i) (w * M.simple j * w⁻¹)
  · have he2 : (M.simple i * w * M.simple j * w⁻¹) ^ 2 = 1 := by
      rw [show M.simple i * w * M.simple j * w⁻¹ =
          M.simple i * (w * M.simple j * w⁻¹) by group, hcomm.mul_pow]
      simp [pow_two, ha, hb]
    have hdvd2 : orderOf (M.simple i * w * M.simple j * w⁻¹) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one he2
    have hpos2 : 0 < orderOf (M.simple i * w * M.simple j * w⁻¹) :=
      Nat.pos_of_dvd_of_pos hdvd2 (by norm_num)
    exact ⟨hpos2, le_trans (Nat.le_of_dvd (by norm_num : 0 < 2) hdvd2) (by norm_num)⟩
  · have he3 : (M.simple i * w * M.simple j * w⁻¹) ^ 3 = 1 := by
      rw [show M.simple i * w * M.simple j * w⁻¹ =
          M.simple i * (w * M.simple j * w⁻¹) by group]
      simpa using ggWeyl_refl_order3 hK hconn 1 w i j hcomm
    have hdvd3 : orderOf (M.simple i * w * M.simple j * w⁻¹) ∣ 3 :=
      orderOf_dvd_of_pow_eq_one he3
    have hpos3 : 0 < orderOf (M.simple i * w * M.simple j * w⁻¹) :=
      Nat.pos_of_dvd_of_pos hdvd3 (by norm_num)
    exact ⟨hpos3, le_trans (Nat.le_of_dvd (by norm_num : 0 < 3) hdvd3) (by norm_num)⟩

theorem orderOf_mul_le_three_of_isCartanModel (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {ι : Type} [Fintype ι] [DecidableEq ι] {K : Matrix ι ι ℤ} (hK : TauCeti.IsFiniteType K)
    (hconn : GGSimplyLacedConnected (CFSG.LieType.RootSystem.coxeterMatrix hK))
    {J : Subgroup (U ≃ₗ[ZMod p] U)} (hA : IsCartanModel p K J)
    (htv : QTwoLin.TransvectionFree J) {x y : U ≃ₗ[ZMod p] U} (hx : x ∈ J) (hy : y ∈ J)
    (hrx : IsRefl p x) (hry : IsRefl p y) : orderOf (x * y) ≤ 3 := by
  classical
  obtain ⟨u, φ, hφ, hdata, hspan, hker, hJeq⟩ := hA
  let M : CoxeterMatrix ι := CFSG.LieType.RootSystem.coxeterMatrix hK
  let r : ι → U ≃ₗ[ZMod p] U := fun i => Module.reflection (hφ i)
  have hlift : M.IsLiftable r := cartanModel_isLiftable hp hK hconn hφ hdata
  let ψ : M.Group →* (U ≃ₗ[ZMod p] U) := M.toCoxeterSystem.lift ⟨r, hlift⟩
  have hψ (i : ι) : ψ (M.simple i) = r i := by
    simpa using M.toCoxeterSystem.lift_apply_simple hlift i
  have hr_refl (i : ι) : IsRefl p (r i) := isRefl_reflection hp (hφ i)
  have hS : ∀ s ∈ Set.range r, IsRefl p s := by
    rintro _ ⟨i, rfl⟩
    exact hr_refl i
  have htv' : QTwoLin.TransvectionFree (Subgroup.closure (Set.range r)) := by
    rw [← hJeq]; exact htv
  obtain ⟨g, hg, s, hs, hxs⟩ := exists_conj_of_isRefl_mem_closure hp hS htv'
    (by rw [← hJeq]; exact hx) hrx
  obtain ⟨h, hh, t', ht', hyt⟩ := exists_conj_of_isRefl_mem_closure hp hS htv'
    (by rw [← hJeq]; exact hy) hry
  obtain ⟨i, rfl⟩ := hs
  obtain ⟨j, rfl⟩ := ht'
  let k : U ≃ₗ[ZMod p] U := g⁻¹ * h
  have hk_mem : k ∈ Subgroup.closure (Set.range r) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hh
  have hk_range : k ∈ ψ.range :=
    (Subgroup.closure_le ψ.range).mpr (by
      rintro _ ⟨i, rfl⟩
      exact MonoidHom.mem_range.mpr ⟨M.simple i, hψ i⟩) hk_mem
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hk_range
  have hc_eq : r i * k * r j * k⁻¹ = ψ (M.simple i * w * M.simple j * w⁻¹) := by
    rw [show r i = ψ (M.simple i) from (hψ i).symm,
      show r j = ψ (M.simple j) from (hψ j).symm,
      show k = ψ w from hw.symm, map_mul, map_mul, map_mul, map_inv]
  have horder_eq : orderOf (x * y) = orderOf (r i * k * r j * k⁻¹) := by
    rw [show x * y = g * (r i * k * r j * k⁻¹) * g⁻¹ by
      rw [hxs, hyt]
      change g * r i * g⁻¹ * (h * r j * h⁻¹) =
        g * (r i * (g⁻¹ * h) * r j * (g⁻¹ * h)⁻¹) * g⁻¹
      group]
    exact IsConj.orderOf_eq (isConj_iff.mpr ⟨g⁻¹, by group⟩)
  have hdvd : orderOf (x * y) ∣ orderOf (M.simple i * w * M.simple j * w⁻¹) := by
    rw [horder_eq, hc_eq]
    exact orderOf_map_dvd ψ _
  obtain ⟨hpos, hbound⟩ := orderOf_simple_mul_conj_le_three hK hconn i j w
  exact le_trans (Nat.le_of_dvd hpos hdvd) hbound

theorem orderOf_mul_le_three_of_isCartanModel_E (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {n : ℕ} (hn : n = 6 ∨ n = 7 ∨ n = 8) {J : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : IsCartanModel p (CartanMatrix.E n) J) (htv : QTwoLin.TransvectionFree J)
    {x y : U ≃ₗ[ZMod p] U} (hx : x ∈ J) (hy : y ∈ J) (hrx : IsRefl p x) (hry : IsRefl p y) :
    orderOf (x * y) ≤ 3 := by
  rcases hn with rfl | rfl | rfl
  · have hFT : TauCeti.IsFiniteType (CartanMatrix.E 6) := by
      have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_E6
      rwa [TauCeti.DynkinType.cartanMatrix_E6] at h
    have hconn : GGSimplyLacedConnected (CFSG.LieType.RootSystem.coxeterMatrix hFT) := by
      rw [coxeterMatrix_eq_of_ggIntCartan hFT ggIntCartan_E₆]
      exact ggSimplyLacedConnected_of_weyl (Or.inr (Or.inl ⟨Equiv.refl (Fin 6), rfl⟩))
        (by intro i j hij; fin_cases i <;> fin_cases j <;>
          simp_all [CoxeterMatrix.E₆, Matrix.of_apply, Matrix.cons_val'])
    exact orderOf_mul_le_three_of_isCartanModel hp hFT hconn hA htv hx hy hrx hry
  · have hFT : TauCeti.IsFiniteType (CartanMatrix.E 7) := by
      have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_E7
      rwa [TauCeti.DynkinType.cartanMatrix_E7] at h
    have hconn : GGSimplyLacedConnected (CFSG.LieType.RootSystem.coxeterMatrix hFT) := by
      rw [coxeterMatrix_eq_of_ggIntCartan hFT ggIntCartan_E₇]
      exact ggSimplyLacedConnected_of_weyl (Or.inr (Or.inr (Or.inl ⟨Equiv.refl (Fin 7), rfl⟩)))
        (by intro i j hij; fin_cases i <;> fin_cases j <;>
          simp_all [CoxeterMatrix.E₇, Matrix.of_apply, Matrix.cons_val'])
    exact orderOf_mul_le_three_of_isCartanModel hp hFT hconn hA htv hx hy hrx hry
  · have hFT : TauCeti.IsFiniteType (CartanMatrix.E 8) := by
      have h := TauCeti.DynkinType.isFiniteType_cartanMatrix_E8
      rwa [TauCeti.DynkinType.cartanMatrix_E8] at h
    have hconn : GGSimplyLacedConnected (CFSG.LieType.RootSystem.coxeterMatrix hFT) := by
      rw [coxeterMatrix_eq_of_ggIntCartan hFT ggIntCartan_E₈]
      exact ggSimplyLacedConnected_of_weyl
        (Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl (Fin 8), rfl⟩))))
        (by intro i j hij; fin_cases i <;> fin_cases j <;>
          simp_all [CoxeterMatrix.E₈, Matrix.of_apply, Matrix.cons_val'])
    exact orderOf_mul_le_three_of_isCartanModel hp hFT hconn hA htv hx hy hrx hry

private noncomputable def f4Coord (p : ℕ) {U : Type} [AddCommGroup U] [Module (ZMod p) U]
    (u : Fin 4 → U) (v : Fin 4 → ℤ) : U :=
  ∑ j, ((v j : ℤ) : ZMod p) • u j

private theorem f4Coord_single (u : Fin 4 → U) (j : Fin 4) :
    f4Coord p u (Pi.single j 1) = u j := by
  rw [f4Coord, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [hb]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

private theorem f4Coord_sub (u : Fin 4 → U) (v w : Fin 4 → ℤ) :
    f4Coord p u (v - w) = f4Coord p u v - f4Coord p u w := by
  simp only [f4Coord, Pi.sub_apply, Int.cast_sub, sub_smul, Finset.sum_sub_distrib]

private theorem f4Coord_zsmul (u : Fin 4 → U) (c : ℤ) (v : Fin 4 → ℤ) :
    f4Coord p u (c • v) = (c : ZMod p) • f4Coord p u v := by
  simp only [f4Coord, Pi.smul_apply, smul_eq_mul, Int.cast_mul, mul_smul, Finset.smul_sum]

private theorem f4Coord_reflection (u : Fin 4 → U) {φ : Fin 4 → Module.Dual (ZMod p) U}
    (hφ : ∀ i, φ i (u i) = 2)
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.F₄ i j : ZMod p)) (i : Fin 4) (v : Fin 4 → ℤ) :
    f4Coord p u (CFSG.LieType.RootSystem.reflection CartanMatrix.F₄ i v) =
      Module.reflection (hφ i) (f4Coord p u v) := by
  rw [CFSG.LieType.RootSystem.reflection_apply, Module.reflection_apply]
  rw [f4Coord_sub, f4Coord_zsmul, f4Coord_single]
  congr 2
  rw [show (∑ j, CartanMatrix.F₄ i j * v j : ℤ) =
      (∑ j, (CartanMatrix.F₄ i j : ZMod p) * ((v j : ℤ) : ZMod p)) by push_cast; rfl]
  have hφu : φ i (f4Coord p u v) =
      ∑ j, (CartanMatrix.F₄ i j : ZMod p) * ((v j : ℤ) : ZMod p) := by
    simp only [f4Coord, map_sum, map_smul, smul_eq_mul, hK]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  rw [hφu]

private noncomputable def f4ReflEnd : Module.End ℤ (Fin 4 → ℤ) :=
  CFSG.LieType.RootSystem.reflection CartanMatrix.F₄ 0 *
    CFSG.LieType.RootSystem.reflection CartanMatrix.F₄ 1 *
    CFSG.LieType.RootSystem.reflection CartanMatrix.F₄ 2 *
    CFSG.LieType.RootSystem.reflection CartanMatrix.F₄ 3

private noncomputable def f4ReflGroup {u : Fin 4 → U}
    {φ : Fin 4 → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2) :
    U ≃ₗ[ZMod p] U :=
  Module.reflection (hφ 0) * Module.reflection (hφ 1) * Module.reflection (hφ 2) *
    Module.reflection (hφ 3)

private theorem f4ReflEnd_pow_six : f4ReflEnd ^ 6 = (-1 : Module.End ℤ (Fin 4 → ℤ)) := by
  have hmat : LinearMap.toMatrixAlgEquiv' (f4ReflEnd ^ 6) = -1 := by
    rw [show f4ReflEnd ^ 6 =
        (CFSG.LieType.RootSystem.reflection CartanMatrix.F₄ 0 *
          CFSG.LieType.RootSystem.reflection CartanMatrix.F₄ 1 *
          CFSG.LieType.RootSystem.reflection CartanMatrix.F₄ 2 *
          CFSG.LieType.RootSystem.reflection CartanMatrix.F₄ 3) ^ 6 from rfl]
    rw [map_pow]
    decide +kernel
  apply LinearMap.toMatrixAlgEquiv'.injective
  rw [hmat, map_neg, map_one]

private theorem f4Coord_comp_reflections {u : Fin 4 → U}
    {φ : Fin 4 → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hdata : ∀ i j, φ i (u j) = (CartanMatrix.F₄ i j : ZMod p)) (v : Fin 4 → ℤ) :
    f4Coord p u (f4ReflEnd v) = f4ReflGroup hφ (f4Coord p u v) := by
  show f4Coord p u
      ((CFSG.LieType.RootSystem.reflection CartanMatrix.F₄ 0 *
        CFSG.LieType.RootSystem.reflection CartanMatrix.F₄ 1 *
        CFSG.LieType.RootSystem.reflection CartanMatrix.F₄ 2 *
        CFSG.LieType.RootSystem.reflection CartanMatrix.F₄ 3) v) =
    (Module.reflection (hφ 0) * Module.reflection (hφ 1) * Module.reflection (hφ 2) *
      Module.reflection (hφ 3)) (f4Coord p u v)
  simp only [Module.End.mul_apply]
  rw [f4Coord_reflection u hφ hdata 0, f4Coord_reflection u hφ hdata 1,
    f4Coord_reflection u hφ hdata 2, f4Coord_reflection u hφ hdata 3]
  rfl

private theorem f4Coord_pow_reflections {u : Fin 4 → U}
    {φ : Fin 4 → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hdata : ∀ i j, φ i (u j) = (CartanMatrix.F₄ i j : ZMod p)) (n : ℕ) (v : Fin 4 → ℤ) :
    f4Coord p u ((f4ReflEnd ^ n) v) = (f4ReflGroup hφ ^ n) (f4Coord p u v) := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc f4Coord p u ((f4ReflEnd ^ (n + 1)) v)
          = f4Coord p u (f4ReflEnd ((f4ReflEnd ^ n) v)) := by
              rw [pow_succ', Module.End.mul_apply]
        _ = f4ReflGroup hφ (f4Coord p u ((f4ReflEnd ^ n) v)) :=
              f4Coord_comp_reflections hφ hdata ((f4ReflEnd ^ n) v)
        _ = f4ReflGroup hφ ((f4ReflGroup hφ ^ n) (f4Coord p u v)) := by rw [ih]
        _ = (f4ReflGroup hφ ^ (n + 1)) (f4Coord p u v) := by rw [pow_succ']; rfl

private theorem f4Coord_surjective {u : Fin 4 → U}
    (hspan : Submodule.span (ZMod p) (Set.range u) = ⊤) :
    Function.Surjective (f4Coord p u) := by
  have hrange : LinearMap.range (Fintype.linearCombination (ZMod p) u) = ⊤ := by
    rw [Fintype.range_linearCombination, hspan]
  intro x
  have hx : x ∈ LinearMap.range (Fintype.linearCombination (ZMod p) u) := by
    rw [hrange]; trivial
  obtain ⟨c, hc⟩ := hx
  choose v hv using fun j => ZMod.intCast_surjective (c j)
  refine ⟨v, ?_⟩
  rw [f4Coord, ← hc, Fintype.linearCombination_apply]
  exact Finset.sum_congr rfl fun j _ => by rw [hv j]

private theorem f4ReflGroup_pow_six {u : Fin 4 → U}
    {φ : Fin 4 → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hdata : ∀ i j, φ i (u j) = (CartanMatrix.F₄ i j : ZMod p))
    (hspan : Submodule.span (ZMod p) (Set.range u) = ⊤) :
    f4ReflGroup hφ ^ 6 = (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) := by
  have hpow := f4Coord_pow_reflections hφ hdata
  have hsurj := f4Coord_surjective hspan
  have hfinal : ∀ x : U, (f4ReflGroup hφ ^ 6) x = -x := by
    intro x
    obtain ⟨v, rfl⟩ := hsurj x
    rw [← hpow 6 v, f4ReflEnd_pow_six]
    change f4Coord p u (-v) = -f4Coord p u v
    rw [show -v = (-1 : ℤ) • v from by rw [neg_one_smul], f4Coord_zsmul]
    simp
  apply LinearEquiv.ext
  intro x
  rw [hfinal x]
  rfl

theorem neg_mem_of_isCartanModel_F4 {J : Subgroup (U ≃ₗ[ZMod p] U)}
    (hA : IsCartanModel p CartanMatrix.F₄ J) :
    (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈ J := by
  obtain ⟨u, φ, hφ, hdata, hspan, hker, hJeq⟩ := hA
  have hg6 := f4ReflGroup_pow_six hφ hdata hspan
  rw [hJeq, ← hg6]
  have hg : f4ReflGroup hφ ∈ Subgroup.closure (Set.range fun i => Module.reflection (hφ i)) := by
    show Module.reflection (hφ 0) * Module.reflection (hφ 1) * Module.reflection (hφ 2) *
      Module.reflection (hφ 3) ∈ _
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.subset_closure ⟨0, rfl⟩) (Subgroup.subset_closure ⟨1, rfl⟩))
      (Subgroup.subset_closure ⟨2, rfl⟩)) (Subgroup.subset_closure ⟨3, rfl⟩)
  exact Subgroup.pow_mem _ hg 6

private def chain3K (e : Fin 3 → Fin 4) : Matrix (Fin 3) (Fin 3) (ZMod p) :=
  Matrix.of fun i j : Fin 3 => (CartanMatrix.F₄ (e i) (e j) : ZMod p)

private def chain3Φ (φ : Fin 4 → Module.Dual (ZMod p) U) (e : Fin 3 → Fin 4) :
    U →ₗ[ZMod p] (Fin 3 → ZMod p) where
  toFun := fun x j => φ (e j) x
  map_add' := fun x y => funext fun j => map_add (φ (e j)) x y
  map_smul' := fun c x => funext fun j => map_smul (φ (e j)) c x

private def chain3W (u : Fin 4 → U) (e : Fin 3 → Fin 4) : Submodule (ZMod p) U :=
  Submodule.span (ZMod p) (Set.range fun j : Fin 3 => u (e j))

private def chain3W' (φ : Fin 4 → Module.Dual (ZMod p) U) (e : Fin 3 → Fin 4) :
    Submodule (ZMod p) U := ⨅ j : Fin 3, LinearMap.ker (φ (e j))

private def chain3B {u : Fin 4 → U} {φ : Fin 4 → Module.Dual (ZMod p) U}
    (hφ : ∀ i, φ i (u i) = 2) (e : Fin 3 → Fin 4) : Subgroup (U ≃ₗ[ZMod p] U) :=
  Subgroup.closure (Set.range fun j : Fin 3 => Module.reflection (hφ (e j)))

private noncomputable def chain3Ψ (u : Fin 4 → U) (e : Fin 3 → Fin 4) :
    (Fin 3 → ZMod p) →ₗ[ZMod p] U where
  toFun := fun c => ∑ i, ((chain3K (p := p) e).adjugate.mulVec c) i • u (e i)
  map_add' := fun c d => by
    simp only [Matrix.mulVec_add, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := fun a c => by
    simp only [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
      RingHom.id_apply]

private theorem chain3_ker (φ : Fin 4 → Module.Dual (ZMod p) U) (e : Fin 3 → Fin 4) :
    LinearMap.ker (chain3Φ (p := p) φ e) = chain3W' (p := p) φ e := by
  ext x
  rw [LinearMap.mem_ker,
    show chain3W' (p := p) φ e = ⨅ j : Fin 3, LinearMap.ker (φ (e j)) from rfl,
    Submodule.mem_iInf, funext_iff]
  simp only [LinearMap.mem_ker, Pi.zero_apply, chain3Φ]
  exact Iff.rfl

private theorem chain3_memW (u : Fin 4 → U) (e : Fin 3 → Fin 4) (x : U) :
    x ∈ chain3W (p := p) u e ↔ ∃ c : Fin 3 → ZMod p, ∑ j, c j • u (e j) = x := by
  simp only [chain3W, Submodule.mem_span_range_iff_exists_fun]

private theorem chain3_mulVec {u : Fin 4 → U} {φ : Fin 4 → Module.Dual (ZMod p) U}
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.F₄ i j : ZMod p)) (e : Fin 3 → Fin 4)
    {c : Fin 3 → ZMod p} (h : ∑ j, c j • u (e j) = 0) :
    (chain3K (p := p) e).mulVec c = 0 := by
  funext k
  have hc := congrArg (φ (e k)) h
  simp only [map_sum, map_smul, map_zero, smul_eq_mul] at hc
  show (∑ j, (chain3K (p := p) e) k j * c j) = 0
  rw [← hc]
  apply Finset.sum_congr rfl
  intro j _
  rw [hK, show (chain3K (p := p) e) k j = (CartanMatrix.F₄ (e k) (e j) : ZMod p) from rfl]
  ring

private theorem chain3_linearIndependent {u : Fin 4 → U}
    {φ : Fin 4 → Module.Dual (ZMod p) U} (hK : ∀ i j, φ i (u j) = (CartanMatrix.F₄ i j : ZMod p))
    (e : Fin 3 → Fin 4) (hKdet : (chain3K (p := p) e).det ≠ 0) :
    LinearIndependent (ZMod p) (fun j : Fin 3 => u (e j)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h0 : (chain3K (p := p) e).mulVec c = (chain3K (p := p) e).mulVec 0 := by
    rw [chain3_mulVec hK e hc]
    ext i
    simp [Matrix.mulVec]
  have hc0 : c = 0 := Matrix.mulVec_injective_of_det_ne_zero hKdet h0
  intro i
  exact congrFun hc0 i

private theorem chain3_finrank {u : Fin 4 → U} {φ : Fin 4 → Module.Dual (ZMod p) U}
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.F₄ i j : ZMod p)) (e : Fin 3 → Fin 4)
    (hKdet : (chain3K (p := p) e).det ≠ 0) :
    Module.finrank (ZMod p) (chain3W (p := p) u e) = 3 := by
  rw [show chain3W (p := p) u e =
      Submodule.span (ZMod p) (Set.range fun j : Fin 3 => u (e j)) from rfl,
    finrank_span_eq_card (chain3_linearIndependent hK e hKdet)]
  simp

private theorem chain3_inf {u : Fin 4 → U} {φ : Fin 4 → Module.Dual (ZMod p) U}
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.F₄ i j : ZMod p)) (e : Fin 3 → Fin 4)
    (hKdet : (chain3K (p := p) e).det ≠ 0) :
    chain3W (p := p) u e ⊓ chain3W' (p := p) φ e = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  obtain ⟨c, hc⟩ := (chain3_memW u e x).mp hx.1
  have hx' : x ∈ chain3W' (p := p) φ e := hx.2
  have hx'' : x ∈ ⨅ j : Fin 3, LinearMap.ker (φ (e j)) := hx'
  have hmap : (chain3K (p := p) e).mulVec c = 0 := by
    funext k
    have h : x ∈ LinearMap.ker (φ (e k)) :=
      (Submodule.mem_iInf (fun j => LinearMap.ker (φ (e j)))).mp hx'' k
    rw [LinearMap.mem_ker] at h
    rw [← hc] at h
    simp only [map_sum, map_smul, smul_eq_mul] at h
    show (∑ j, (chain3K (p := p) e) k j * c j) = 0
    rw [← h]
    apply Finset.sum_congr rfl
    intro j _
    rw [hK, show (chain3K (p := p) e) k j = (CartanMatrix.F₄ (e k) (e j) : ZMod p) from rfl]
    ring
  have h0 : (chain3K (p := p) e).mulVec c = (chain3K (p := p) e).mulVec 0 := by
    rw [hmap]
    ext i
    simp [Matrix.mulVec]
  have hc0 : c = 0 := Matrix.mulVec_injective_of_det_ne_zero hKdet h0
  rw [hc0] at hc
  simp at hc
  exact hc.symm

private theorem chain3_ΦΨ {u : Fin 4 → U} {φ : Fin 4 → Module.Dual (ZMod p) U}
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.F₄ i j : ZMod p)) (e : Fin 3 → Fin 4)
    (c : Fin 3 → ZMod p) :
    chain3Φ (p := p) φ e (chain3Ψ (p := p) u e c) = (chain3K (p := p) e).det • c := by
  funext j
  show φ (e j) (∑ i, ((chain3K (p := p) e).adjugate.mulVec c) i • u (e i)) =
    (chain3K (p := p) e).det * c j
  rw [map_sum]
  simp only [map_smul, smul_eq_mul, hK]
  have h2 : ((chain3K (p := p) e).mulVec ((chain3K (p := p) e).adjugate.mulVec c)) j =
      (chain3K (p := p) e).det * c j := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, Matrix.smul_mulVec, Matrix.one_mulVec]
    rfl
  rw [← h2]
  show (∑ i, ((chain3K (p := p) e).adjugate.mulVec c) i * (chain3K (p := p) e) j i) =
    ∑ i, (chain3K (p := p) e) j i * ((chain3K (p := p) e).adjugate.mulVec c) i
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem chain3_ΨΦ {u : Fin 4 → U} {φ : Fin 4 → Module.Dual (ZMod p) U}
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.F₄ i j : ZMod p)) (e : Fin 3 → Fin 4)
    (hKdet : (chain3K (p := p) e).det ≠ 0) (x : U) :
    chain3Φ (p := p) φ e
        (chain3Ψ (p := p) u e ((chain3K (p := p) e).det⁻¹ • chain3Φ (p := p) φ e x)) =
      chain3Φ (p := p) φ e x := by
  rw [chain3_ΦΨ hK e, smul_smul, mul_inv_cancel₀ hKdet, one_smul]

private theorem chain3_sup {u : Fin 4 → U} {φ : Fin 4 → Module.Dual (ZMod p) U}
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.F₄ i j : ZMod p)) (e : Fin 3 → Fin 4)
    (hKdet : (chain3K (p := p) e).det ≠ 0) :
    chain3W (p := p) u e ⊔ chain3W' (p := p) φ e = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  have hwW : chain3Ψ (p := p) u e
      ((chain3K (p := p) e).det⁻¹ • chain3Φ (p := p) φ e x) ∈ chain3W (p := p) u e := by
    rw [chain3_memW]
    exact ⟨(chain3K (p := p) e).adjugate.mulVec
      ((chain3K (p := p) e).det⁻¹ • chain3Φ (p := p) φ e x), rfl⟩
  exact Submodule.mem_sup.mpr
    ⟨chain3Ψ (p := p) u e ((chain3K (p := p) e).det⁻¹ • chain3Φ (p := p) φ e x), hwW,
      x - chain3Ψ (p := p) u e ((chain3K (p := p) e).det⁻¹ • chain3Φ (p := p) φ e x),
      by rw [← chain3_ker, LinearMap.mem_ker, map_sub, chain3_ΨΦ hK e hKdet]; abel, by abel⟩

private theorem chain3_compl {u : Fin 4 → U} {φ : Fin 4 → Module.Dual (ZMod p) U}
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.F₄ i j : ZMod p)) (e : Fin 3 → Fin 4)
    (hKdet : (chain3K (p := p) e).det ≠ 0) :
    IsCompl (chain3W (p := p) u e) (chain3W' (p := p) φ e) :=
  ⟨disjoint_iff_inf_le.mpr (by rw [chain3_inf hK e hKdet]),
    codisjoint_iff_le_sup.mpr (by rw [chain3_sup hK e hKdet])⟩

private theorem chain3_gen {u : Fin 4 → U} {φ : Fin 4 → Module.Dual (ZMod p) U}
    (hφ : ∀ i, φ i (u i) = 2)
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.F₄ i j : ZMod p)) (e : Fin 3 → Fin 4) (j : Fin 3) :
    ∀ w ∈ chain3W (p := p) u e, Module.reflection (hφ (e j)) w ∈ chain3W (p := p) u e := by
  have hmap : (chain3W (p := p) u e).map
      ((Module.reflection (hφ (e j)) : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) ≤
      chain3W (p := p) u e := by
    rw [show chain3W (p := p) u e =
        Submodule.span (ZMod p) (Set.range fun j : Fin 3 => u (e j)) from rfl,
      Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
    show Module.reflection (hφ (e j)) (u (e k)) ∈ chain3W (p := p) u e
    rw [Module.reflection_apply, hK]
    exact (chain3W (p := p) u e).sub_mem (Submodule.subset_span ⟨k, rfl⟩)
      ((chain3W (p := p) u e).smul_mem _ (Submodule.subset_span ⟨j, rfl⟩))
  intro w hw
  exact hmap (Submodule.mem_map_of_mem (f :=
    ((Module.reflection (hφ (e j)) : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)) hw)

private theorem chain3_fix {u : Fin 4 → U} {φ : Fin 4 → Module.Dual (ZMod p) U}
    (hφ : ∀ i, φ i (u i) = 2) (e : Fin 3 → Fin 4) :
    ∀ h ∈ chain3B hφ e, ∀ w ∈ chain3W' (p := p) φ e, h w = w := by
  intro h hh w hw
  simp only [chain3B] at hh
  have hpair : (∀ w ∈ chain3W' (p := p) φ e, h w = w) ∧
      (∀ w ∈ chain3W' (p := p) φ e, h⁻¹ w = w) := by
    induction hh using Subgroup.closure_induction with
    | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        refine ⟨?_, ?_⟩
        · intro w hw
          have hw' : w ∈ ⨅ j : Fin 3, LinearMap.ker (φ (e j)) := hw
          have hwj : w ∈ LinearMap.ker (φ (e j)) :=
            (Submodule.mem_iInf (fun j => LinearMap.ker (φ (e j)))).mp hw' j
          rw [LinearMap.mem_ker] at hwj
          rw [Module.reflection_apply, hwj, zero_smul, sub_zero]
        · intro w hw
          rw [Module.reflection_inv]
          have hw' : w ∈ ⨅ j : Fin 3, LinearMap.ker (φ (e j)) := hw
          have hwj : w ∈ LinearMap.ker (φ (e j)) :=
            (Submodule.mem_iInf (fun j => LinearMap.ker (φ (e j)))).mp hw' j
          rw [LinearMap.mem_ker] at hwj
          rw [Module.reflection_apply, hwj, zero_smul, sub_zero]
    | one => exact ⟨fun w _ => rfl, fun w _ => rfl⟩
    | mul y z hy hz ihy ihz =>
        exact ⟨fun w hw => by rw [LinearEquiv.mul_apply, ihz.1 w hw, ihy.1 w hw],
          fun w hw => by rw [mul_inv_rev, LinearEquiv.mul_apply, ihy.2 w hw, ihz.2 w hw]⟩
    | inv y hy ihy => exact ⟨fun w hw => ihy.2 w hw, fun w hw => by
        rw [inv_inv]; exact ihy.1 w hw⟩
  exact hpair.1 w hw

private theorem chain3_inv {u : Fin 4 → U} {φ : Fin 4 → Module.Dual (ZMod p) U}
    (hφ : ∀ i, φ i (u i) = 2)
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.F₄ i j : ZMod p)) (e : Fin 3 → Fin 4) :
    ∀ h ∈ chain3B hφ e, ∀ w ∈ chain3W (p := p) u e, h w ∈ chain3W (p := p) u e := by
  intro h hh
  have hpair : (∀ w ∈ chain3W (p := p) u e, h w ∈ chain3W (p := p) u e) ∧
      (∀ w ∈ chain3W (p := p) u e, h⁻¹ w ∈ chain3W (p := p) u e) := by
    simp only [chain3B] at hh
    induction hh using Subgroup.closure_induction with
    | mem y hy =>
        obtain ⟨j, rfl⟩ := hy
        exact ⟨chain3_gen hφ hK e j, fun w hw => by
          rw [Module.reflection_inv]; exact chain3_gen hφ hK e j w hw⟩
    | one => exact ⟨fun w hw => by simpa using hw, fun w hw => by simpa using hw⟩
    | mul y z hy hz ihy ihz =>
        exact ⟨fun w hw => by
            rw [LinearEquiv.mul_apply]
            exact ihy.1 (z w) (ihz.1 w hw),
          fun w hw => by
            rw [mul_inv_rev, LinearEquiv.mul_apply]
            exact ihz.2 (y⁻¹ w) (ihy.2 w hw)⟩
    | inv y hy ihy => exact ⟨fun w hw => ihy.2 w hw, fun w hw => by
        rw [inv_inv]; exact ihy.1 w hw⟩
  exact hpair.1

private theorem chain3_irr_span {u : Fin 4 → U} {φ : Fin 4 → Module.Dual (ZMod p) U}
    (hφ : ∀ i, φ i (u i) = 2)
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.F₄ i j : ZMod p)) (e : Fin 3 → Fin 4)
    {X : Submodule (ZMod p) U} (hXinv : ∀ h ∈ chain3B hφ e, ∀ x ∈ X, h x ∈ X)
    (h01 : (CartanMatrix.F₄ (e 0) (e 1) : ZMod p) ≠ 0)
    (h10 : (CartanMatrix.F₄ (e 1) (e 0) : ZMod p) ≠ 0)
    (h12 : (CartanMatrix.F₄ (e 1) (e 2) : ZMod p) ≠ 0)
    (h21 : (CartanMatrix.F₄ (e 2) (e 1) : ZMod p) ≠ 0)
    {j : Fin 3} (huj : u (e j) ∈ X) : chain3W (p := p) u e ≤ X := by
  have step (a b : Fin 3) (hab : (CartanMatrix.F₄ (e a) (e b) : ZMod p) ≠ 0)
      (hb : u (e b) ∈ X) : u (e a) ∈ X := by
    have hra : Module.reflection (hφ (e a)) ∈ chain3B hφ e := Subgroup.subset_closure ⟨a, rfl⟩
    have hmem : Module.reflection (hφ (e a)) (u (e b)) - u (e b) ∈ X :=
      X.sub_mem (hXinv _ hra _ hb) hb
    have hval : Module.reflection (hφ (e a)) (u (e b)) - u (e b) =
        -((CartanMatrix.F₄ (e a) (e b) : ZMod p)) • u (e a) := by
      rw [Module.reflection_apply, hK, sub_sub_cancel_left, ← neg_smul]
      rfl
    rw [hval] at hmem
    have := X.smul_mem (-((CartanMatrix.F₄ (e a) (e b) : ZMod p)))⁻¹ hmem
    rwa [smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr hab), one_smul] at this
  rw [show chain3W (p := p) u e =
      Submodule.span (ZMod p) (Set.range fun j : Fin 3 => u (e j)) from rfl, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  fin_cases j
  · fin_cases k
    · exact huj
    · exact step 1 0 h10 huj
    · exact step 2 1 h21 (step 1 0 h10 huj)
  · fin_cases k
    · exact step 0 1 h01 huj
    · exact huj
    · exact step 2 1 h21 huj
  · fin_cases k
    · exact step 0 1 h01 (step 1 2 h12 huj)
    · exact step 1 2 h12 huj
    · exact huj

private theorem chain3_irr {u : Fin 4 → U} {φ : Fin 4 → Module.Dual (ZMod p) U}
    (hφ : ∀ i, φ i (u i) = 2)
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.F₄ i j : ZMod p)) (e : Fin 3 → Fin 4)
    (hKdet : (chain3K (p := p) e).det ≠ 0)
    (h01 : (CartanMatrix.F₄ (e 0) (e 1) : ZMod p) ≠ 0)
    (h10 : (CartanMatrix.F₄ (e 1) (e 0) : ZMod p) ≠ 0)
    (h12 : (CartanMatrix.F₄ (e 1) (e 2) : ZMod p) ≠ 0)
    (h21 : (CartanMatrix.F₄ (e 2) (e 1) : ZMod p) ≠ 0) :
    IrredOnSection (chain3B hφ e) ⊥ (chain3W (p := p) u e) := by
  intro X _ hXW hXinv
  by_cases hX0 : X = ⊥
  · exact Or.inl hX0
  · right
    obtain ⟨x, hxX, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX0
    have hex : ∃ j : Fin 3, φ (e j) x ≠ 0 := by
      by_contra h
      push Not at h
      have hxW' : x ∈ chain3W' (p := p) φ e :=
        (Submodule.mem_iInf (fun j => LinearMap.ker (φ (e j)))).mpr fun j => by
          rw [LinearMap.mem_ker]; exact h j
      have : x ∈ chain3W (p := p) u e ⊓ chain3W' (p := p) φ e := ⟨hXW hxX, hxW'⟩
      rw [chain3_inf hK e hKdet] at this
      exact hx0 (by simpa using this)
    obtain ⟨j, hj⟩ := hex
    have huj : u (e j) ∈ X := by
      have hrj : Module.reflection (hφ (e j)) ∈ chain3B hφ e := Subgroup.subset_closure ⟨j, rfl⟩
      have hmem : Module.reflection (hφ (e j)) x - x ∈ X :=
        X.sub_mem (hXinv _ hrj x hxX) hxX
      have hval : Module.reflection (hφ (e j)) x - x = -(φ (e j) x) • u (e j) := by
        rw [Module.reflection_apply, sub_sub_cancel_left, ← neg_smul]
        rfl
      rw [hval] at hmem
      have := X.smul_mem (-(φ (e j) x))⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr hj), one_smul] at this
    exact le_antisymm hXW (chain3_irr_span hφ hK e hXinv h01 h10 h12 h21 huj)

private theorem chain3_ne (hp : p ≠ 2) {u : Fin 4 → U}
    {φ : Fin 4 → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2) (e : Fin 3 → Fin 4) :
    ∃ h ∈ chain3B hφ e, ∃ w ∈ chain3W (p := p) u e, h w ≠ w := by
  refine ⟨Module.reflection (hφ (e 0)), Subgroup.subset_closure ⟨0, rfl⟩, u (e 0), ?_, ?_⟩
  · rw [show chain3W (p := p) u e =
        Submodule.span (ZMod p) (Set.range fun j : Fin 3 => u (e j)) from rfl]
    exact Submodule.subset_span ⟨0, rfl⟩
  · intro hcon
    have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
    have hu0 : u (e 0) ≠ 0 := by
      intro h0
      have := hφ (e 0)
      rw [h0, map_zero] at this
      exact h2 this.symm
    have hneg : Module.reflection (hφ (e 0)) (u (e 0)) = -u (e 0) := by
      rw [Module.reflection_apply, hφ (e 0), two_smul]
      abel
    rw [hneg] at hcon
    have hz : (2 : ZMod p) • u (e 0) = 0 := by
      rw [two_smul]
      nth_rewrite 2 [← hcon]
      rw [add_neg_cancel]
    exact hu0 ((smul_eq_zero.mp hz).resolve_left h2)

private theorem splitSupport_chain3 (hp : p ≠ 2) {u : Fin 4 → U}
    {φ : Fin 4 → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.F₄ i j : ZMod p)) (e : Fin 3 → Fin 4)
    (hKdet : (chain3K (p := p) e).det ≠ 0)
    (h01 : (CartanMatrix.F₄ (e 0) (e 1) : ZMod p) ≠ 0)
    (h10 : (CartanMatrix.F₄ (e 1) (e 0) : ZMod p) ≠ 0)
    (h12 : (CartanMatrix.F₄ (e 1) (e 2) : ZMod p) ≠ 0)
    (h21 : (CartanMatrix.F₄ (e 2) (e 1) : ZMod p) ≠ 0) :
    SplitSupport (Subgroup.closure (Set.range fun j => Module.reflection (hφ (e j)))) 3 := by
  have hmain := splitSupport_of_isCompl (K := ZMod p) (B := chain3B hφ e)
    (W := chain3W (p := p) u e) (W' := chain3W' (p := p) φ e)
    (chain3_compl hK e hKdet) (chain3_fix hφ e) (chain3_inv hφ hK e)
    (chain3_irr hφ hK e hKdet h01 h10 h12 h21) (chain3_ne hp hφ e)
  rwa [chain3_finrank hK e hKdet] at hmain

private theorem chain3_data (hp : p ≠ 2) (e : Fin 3 → Fin 4)
    (he : e = ![0, 1, 2] ∨ e = ![1, 2, 3]) :
    (chain3K (p := p) e).det = 2 ∧
      (CartanMatrix.F₄ (e 0) (e 1) : ZMod p) ≠ 0 ∧
      (CartanMatrix.F₄ (e 1) (e 0) : ZMod p) ≠ 0 ∧
      (CartanMatrix.F₄ (e 1) (e 2) : ZMod p) ≠ 0 ∧
      (CartanMatrix.F₄ (e 2) (e 1) : ZMod p) ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have h1ne : (1 : ZMod p) ≠ 0 := fun h => h2 (by rw [← mul_one (2 : ZMod p), h, mul_zero])
  have hne : ∀ z : ℤ, (z = -1 ∨ z = -2) → ((z : ℤ) : ZMod p) ≠ 0 := by
    rintro z (rfl | rfl)
    · rw [Int.cast_neg, Int.cast_one]; exact neg_ne_zero.mpr h1ne
    · rw [Int.cast_neg, Int.cast_ofNat]; exact neg_ne_zero.mpr h2
  rcases he with rfl | rfl
  · refine ⟨?_, hne _ (by decide +kernel), hne _ (by decide +kernel), hne _ (by decide +kernel),
      hne _ (by decide +kernel)⟩
    simp [chain3K, CartanMatrix.F₄, Matrix.det_fin_three]; ring
  · refine ⟨?_, hne _ (by decide +kernel), hne _ (by decide +kernel), hne _ (by decide +kernel),
      hne _ (by decide +kernel)⟩
    simp [chain3K, CartanMatrix.F₄, Matrix.det_fin_three]; ring

private theorem exists_chain3 (hp : p ≠ 2) {u : Fin 4 → U}
    {φ : Fin 4 → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.F₄ i j : ZMod p)) (e : Fin 3 → Fin 4)
    (hKdet : (chain3K (p := p) e).det ≠ 0)
    (h01 : (CartanMatrix.F₄ (e 0) (e 1) : ZMod p) ≠ 0)
    (h10 : (CartanMatrix.F₄ (e 1) (e 0) : ZMod p) ≠ 0)
    (h12 : (CartanMatrix.F₄ (e 1) (e 2) : ZMod p) ≠ 0)
    (h21 : (CartanMatrix.F₄ (e 2) (e 1) : ZMod p) ≠ 0) :
    ∃ B : Subgroup (U ≃ₗ[ZMod p] U),
      B ≤ Subgroup.closure (Set.range fun j => Module.reflection (hφ j)) ∧
        (∀ j : Fin 3, Module.reflection (hφ (e j)) ∈ B) ∧ ReflGen p B ∧ SplitSupport B 3 := by
  refine ⟨Subgroup.closure (Set.range fun j : Fin 3 => Module.reflection (hφ (e j))), ?_, ?_, ?_,
    splitSupport_chain3 hp hφ hK e hKdet h01 h10 h12 h21⟩
  · refine (Subgroup.closure_le
      (Subgroup.closure (Set.range fun j => Module.reflection (hφ j)))).mpr ?_
    rintro _ ⟨j, rfl⟩
    exact Subgroup.subset_closure ⟨e j, rfl⟩
  · intro j
    exact Subgroup.subset_closure ⟨j, rfl⟩
  · rw [ReflGen]
    apply le_antisymm
    · refine (Subgroup.closure_le (Subgroup.closure
        {t | t ∈ Subgroup.closure (Set.range fun j : Fin 3 => Module.reflection (hφ (e j))) ∧
          IsRefl p t})).mpr ?_
      rintro t ⟨j, rfl⟩
      exact Subgroup.subset_closure ⟨Subgroup.subset_closure ⟨j, rfl⟩,
        isRefl_reflection hp (hφ (e j))⟩
    · refine (Subgroup.closure_le
        (Subgroup.closure (Set.range fun j : Fin 3 => Module.reflection (hφ (e j))))).mpr ?_
      rintro t ⟨ht, -⟩
      exact ht

theorem exists_splitSupport_of_isCartanModel_F4 (hp : p ≠ 2) {u : Fin 4 → U}
    {φ : Fin 4 → Module.Dual (ZMod p) U} (hφ : ∀ i, φ i (u i) = 2)
    (hK : ∀ i j, φ i (u j) = (CartanMatrix.F₄ i j : ZMod p)) (i : Fin 4) :
    ∃ B : Subgroup (U ≃ₗ[ZMod p] U),
      B ≤ Subgroup.closure (Set.range fun j => Module.reflection (hφ j)) ∧
        Module.reflection (hφ i) ∈ B ∧ ReflGen p B ∧ SplitSupport B 3 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  obtain ⟨hdetB, h01B, h10B, h12B, h21B⟩ := chain3_data hp ![0, 1, 2] (Or.inl rfl)
  obtain ⟨hdetC, h01C, h10C, h12C, h21C⟩ := chain3_data hp ![1, 2, 3] (Or.inr rfl)
  fin_cases i
  · obtain ⟨B, h1, h2', h3, h4⟩ :=
      exists_chain3 hp hφ hK ![0, 1, 2] (by rw [hdetB]; exact h2) h01B h10B h12B h21B
    exact ⟨B, h1, h2' 0, h3, h4⟩
  · obtain ⟨B, h1, h2', h3, h4⟩ :=
      exists_chain3 hp hφ hK ![0, 1, 2] (by rw [hdetB]; exact h2) h01B h10B h12B h21B
    exact ⟨B, h1, h2' 1, h3, h4⟩
  · obtain ⟨B, h1, h2', h3, h4⟩ :=
      exists_chain3 hp hφ hK ![0, 1, 2] (by rw [hdetB]; exact h2) h01B h10B h12B h21B
    exact ⟨B, h1, h2' 2, h3, h4⟩
  · obtain ⟨B, h1, h2', h3, h4⟩ :=
      exists_chain3 hp hφ hK ![1, 2, 3] (by rw [hdetC]; exact h2) h01C h10C h12C h21C
    exact ⟨B, h1, h2' 2, h3, h4⟩

theorem throughRefl_of_isCartanModel_F4 (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {J : Subgroup (U ≃ₗ[ZMod p] U)} (hA : IsCartanModel p CartanMatrix.F₄ J)
    (htv : QTwoLin.TransvectionFree J) : ThroughRefl p 3 J := by
  obtain ⟨u, φ, hφ, hdata, hspan, hker, hJeq⟩ := hA
  have hS : ∀ s ∈ Set.range (fun j => Module.reflection (hφ j)), IsRefl p s := by
    rintro _ ⟨i, rfl⟩
    exact (isRefl_iff hp _).mpr ⟨u i, φ i, hφ i, rfl⟩
  have htv' : QTwoLin.TransvectionFree
      (Subgroup.closure (Set.range fun j => Module.reflection (hφ j))) := by
    rw [← hJeq]; exact htv
  refine throughRefl_of_forall_conj (Set.range fun j => Module.reflection (hφ j)) ?_ ?_
  · rintro _ ⟨i, rfl⟩
    obtain ⟨B, hB, hri, hrefl, hsplit⟩ := exists_splitSupport_of_isCartanModel_F4 hp hφ hdata i
    exact ⟨B, by rwa [hJeq], hri, hrefl, hsplit⟩
  · intro r hr hrr
    obtain ⟨g, hg, s, hs, hrs⟩ := exists_conj_of_isRefl_mem_closure hp hS htv'
      (by rwa [← hJeq]) hrr
    exact ⟨g, by rwa [hJeq], s, hs, hrs⟩

theorem tableConclusions_of_linWeyl (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (h3 : 3 ≤ Module.finrank (ZMod p) U) {J : Subgroup (U ≃ₗ[ZMod p] U)} (h : LinWeyl p J)
    (hT : TableHyp p J) (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV J) :
    TableConclusions p (Module.finrank (ZMod p) U) J := by
  rcases isCartanModel_cases_of_linWeyl hp h3 hT.irreducible h with
    ⟨ℓ, hA, T, hT'⟩ | ⟨ℓ, hℓ, hA⟩ | ⟨ℓ, hℓ, hA⟩ | hA | hA | hA | hA
  · exfalso
    obtain ⟨x, hx, y, hy, hrx, hry, hd⟩ := hT.dLarge
    exact absurd (orderOf_mul_le_three_of_typeA hp T hT' hx hy hrx hry) (by omega)
  · exfalso
    exact hprim (isImprimitiveOnV_of_isCartanModel_B hp hℓ hA)
  · exfalso
    exact hprim (isImprimitiveOnV_of_isCartanModel_D hp hℓ hA)
  · exfalso
    obtain ⟨x, hx, y, hy, hrx, hry, hd⟩ := hT.dLarge
    exact absurd (orderOf_mul_le_three_of_isCartanModel_E hp (Or.inl rfl) hA
      hT.transvectionFree hx hy hrx hry) (by omega)
  · exfalso
    obtain ⟨x, hx, y, hy, hrx, hry, hd⟩ := hT.dLarge
    exact absurd (orderOf_mul_le_three_of_isCartanModel_E hp (Or.inr (Or.inl rfl)) hA
      hT.transvectionFree hx hy hrx hry) (by omega)
  · exfalso
    obtain ⟨x, hx, y, hy, hrx, hry, hd⟩ := hT.dLarge
    exact absurd (orderOf_mul_le_three_of_isCartanModel_E hp (Or.inr (Or.inr rfl)) hA
      hT.transvectionFree hx hy hrx hry) (by omega)
  · have hdet : ((CartanMatrix.F₄.det : ℤ) : ZMod p) ≠ 0 := by
      rw [CartanMatrix.F₄_det]; norm_num
    have hdim : Module.finrank (ZMod p) U = 4 := IsCartanModel.finrank_eq_card_of_det hA hdet
    have hneg : (LinearEquiv.neg (ZMod p) : U ≃ₗ[ZMod p] U) ∈ J :=
      neg_mem_of_isCartanModel_F4 hA
    exact ⟨Or.inl hneg, coprimeWitness_of_neg_mem hp hneg,
      by simpa [hdim] using throughRefl_of_isCartanModel_F4 hp hA hT.transvectionFree⟩

end CFSG.StandardType.ZS
