module

public import CFSG.LocalAnalysis.StandardType.ZS.TableFactsDefs
public import CFSG.LocalAnalysis.StandardType.ZS.DLargeTFDefs
public import CFSG.LocalAnalysis.StandardType.GGZSNFourFamily
import CFSG.LocalAnalysis.StandardType.ZS.DLargeTFLift
import CFSG.LocalAnalysis.StandardType.ZS.NFourRelations
import TauCeti.GroupTheory.Sylow
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsWeyl
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsTransport
import CFSG.LocalAnalysis.StandardType.ZS.TableFactsOrthGeom
import CFSG.LocalAnalysis.StandardType.ZS.ClassReflClosure
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
import CFSG.LocalAnalysis.StandardType.ZS.MonomialCard
import CFSG.LocalAnalysis.StandardType.GGZSNFourSound
import CFSG.LocalAnalysis.StandardType.ZS.SubgroupSpaces
import CFSG.Timmesfeld.Components
public import CFSG.LocalAnalysis.StandardType.ZS.ImpExtSetting
public import CFSG.LocalAnalysis.StandardType.ZS.ImprimSystem
public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtSix
public import CFSG.LocalAnalysis.StandardType.ZS.OrthExtTable
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtTable
public import CFSG.LocalAnalysis.StandardType.ZS.UseInputOfCases

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

private def nFourOrderWord : List (Fin 4) :=
  [3, 2, 0, 1, 2, 3, 1, 0, 2, 0, 1, 2]

private def nFourUMat (t : ZMod 5) : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  (nFourOrderWord.map (n4Mat t)).prod

private lemma matrix_ker_le_range_of_one_dim (M : Matrix (Fin 4) (Fin 4) (ZMod 5))
    (c w : Fin 4 → ZMod 5) (hw : M.mulVec w = c)
    (hspan : ∀ v, M.mulVec v = 0 → ∃ a : ZMod 5, v = a • c) :
    LinearMap.ker (Matrix.toLin' M) ≤ LinearMap.range (Matrix.toLin' M) := by
  intro v hv
  rw [LinearMap.mem_ker, Matrix.toLin'_apply', Matrix.mulVecLin_apply] at hv
  rw [LinearMap.mem_range]
  obtain ⟨a, ha⟩ := hspan v hv
  refine ⟨a • w, ?_⟩
  rw [Matrix.toLin'_apply', Matrix.mulVecLin_apply]
  have hlin : M.mulVec (a • w) = a • M.mulVec w := by
    rw [← Matrix.mulVecLin_apply M (a • w), map_smul, Matrix.mulVecLin_apply]
  rw [hlin, hw, ha]

private def nFourM (t : ZMod 5) (k : ℕ) : Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  nFourUMat t ^ k - 1

private def nFourC (t : ZMod 5) (k : ℕ) : Fin 4 → ZMod 5 :=
  (nFourM t k).mulVec ((nFourM t k).mulVec ((nFourM t k).mulVec (Pi.single 0 1)))

private def nFourW (t : ZMod 5) (k : ℕ) : Fin 4 → ZMod 5 :=
  (nFourM t k).mulVec ((nFourM t k).mulVec (Pi.single 0 1))

private lemma matrix_ker_le_range_cases (t : ZMod 5) (k : ℕ)
    (htk : (t = 2 ∨ t = 3) ∧ (k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4)) :
    LinearMap.ker (Matrix.toLin' (nFourM t k)) ≤
      LinearMap.range (Matrix.toLin' (nFourM t k)) := by
  rcases htk with ⟨ht, hk⟩
  rcases ht with rfl | rfl <;> rcases hk with rfl | rfl | rfl | rfl <;>
    refine matrix_ker_le_range_of_one_dim (nFourM _ _) (nFourC _ _) (nFourW _ _) rfl ?_ <;>
    decide +kernel

private lemma two_zmod5_ne_zero : (2 : ZMod 5) ≠ 0 := by decide +kernel

private lemma two_zmod5_sq : (2 : ZMod 5) ^ 2 = -1 := by decide +kernel

private lemma three_zmod5_sq : (3 : ZMod 5) ^ 2 = -1 := by decide +kernel

private lemma zmod5_sq_eq_neg_one {t : ZMod 5} (ht : t ^ 2 = -1) : t = 2 ∨ t = 3 := by
  fin_cases t
  · exfalso; revert ht; decide +kernel
  · exfalso; revert ht; decide +kernel
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exfalso; revert ht; decide +kernel

private lemma nFourUMat_two_pow_five : nFourUMat 2 ^ 5 = 1 := by decide +kernel

private lemma nFourUMat_two_ne_one : nFourUMat 2 ≠ 1 := by decide +kernel

private lemma nFourUMat_three_pow_five : nFourUMat 3 ^ 5 = 1 := by decide +kernel

private lemma nFourUMat_three_ne_one : nFourUMat 3 ≠ 1 := by decide +kernel

private lemma toMatrix_mulVec_equivFun {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] {n : ℕ} (f : Module.Basis (Fin n) K V) (A : V →ₗ[K] V) (x : V) :
    Matrix.mulVec (LinearMap.toMatrix f f A) (f.equivFun x) = f.equivFun (A x) := by
  simp only [f.equivFun_apply]
  exact LinearMap.toMatrix_mulVec_repr f f A x

private lemma ker_le_range_of_toMatrix {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] {n : ℕ} (f : Module.Basis (Fin n) K V) (A : V →ₗ[K] V)
    (h : LinearMap.ker (Matrix.toLin' (LinearMap.toMatrix f f A)) ≤
      LinearMap.range (Matrix.toLin' (LinearMap.toMatrix f f A))) :
    LinearMap.ker A ≤ LinearMap.range A := by
  intro x hx
  rw [LinearMap.mem_ker] at hx
  rw [LinearMap.mem_range]
  have hx' : f.equivFun x ∈ LinearMap.ker (Matrix.toLin' (LinearMap.toMatrix f f A)) := by
    rw [LinearMap.mem_ker, Matrix.toLin'_apply', Matrix.mulVecLin_apply,
      toMatrix_mulVec_equivFun, hx, map_zero]
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (h hx')
  refine ⟨f.equivFun.symm y, ?_⟩
  apply f.equivFun.injective
  rw [← toMatrix_mulVec_equivFun f A (f.equivFun.symm y), f.equivFun.apply_symm_apply,
    ← Matrix.mulVecLin_apply, ← Matrix.toLin'_apply']
  exact hy

private lemma ker_le_range_conj {K : Type} [Field K] {V : Type} [AddCommGroup V]
    [Module K V] (g : V ≃ₗ[K] V) {A : V →ₗ[K] V} (h : LinearMap.ker A ≤ LinearMap.range A) :
    LinearMap.ker ((g : V →ₗ[K] V) * A * ((g⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V)) ≤
      LinearMap.range ((g : V →ₗ[K] V) * A * ((g⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V)) := by
  intro v hv
  rw [LinearMap.mem_ker] at hv
  rw [LinearMap.mem_range]
  have hAg : A (((g⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) v) = 0 := by
    have hv' := hv
    rw [Module.End.mul_apply, Module.End.mul_apply] at hv'
    exact g.injective (by simpa using hv')
  obtain ⟨y, hy⟩ := LinearMap.mem_range.mp (h (LinearMap.mem_ker.mpr hAg))
  refine ⟨g y, ?_⟩
  simp only [Module.End.mul_apply]
  rw [show ((g⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) (g y) = y from by
        simp]
  rw [hy]
  simp

private lemma eq_one_of_conj_eq_one {H : Type} [Group H] {u y : H}
    (h : y * u * y⁻¹ = 1) : u = 1 := by
  have h2 : y⁻¹ * (y * u * y⁻¹) * y = u := by group
  calc u = y⁻¹ * (y * u * y⁻¹) * y := h2.symm
    _ = y⁻¹ * 1 * y := by rw [h]
    _ = 1 := by group

private lemma exists_u0_two {V5 : Type} [AddCommGroup V5] [Module (ZMod 5) V5]
    (f : Module.Basis (Fin 4) (ZMod 5) V5) :
    ∃ u₀ ∈ basisClosure f (weylN4Mats 2), orderOf u₀ = 5 ∧
      (∀ k : ℕ, (k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) →
        LinearMap.ker (((u₀ ^ k : V5 ≃ₗ[ZMod 5] V5) : V5 →ₗ[ZMod 5] V5) - 1) ≤
          LinearMap.range (((u₀ ^ k : V5 ≃ₗ[ZMod 5] V5) : V5 →ₗ[ZMod 5] V5) - 1)) := by
  obtain ⟨s, hs, hcl, -, -⟩ :=
    exists_n4_tuple two_zmod5_ne_zero two_zmod5_sq f
  have hmat : ∀ i, automorphismToMatrix f (s i) = n4Mat 2 i :=
    fun i => by rw [automorphismToMatrix_apply]; exact hs i
  let u₀ : V5 ≃ₗ[ZMod 5] V5 := (nFourOrderWord.map s).prod
  have hu0mat : automorphismToMatrix f u₀ = nFourUMat 2 := by
    dsimp only [u₀, nFourUMat]
    rw [map_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun i _ => hmat i)
  refine ⟨u₀, ?_, ?_, ?_⟩
  · rw [← hcl]
    exact Subgroup.list_prod_mem (Subgroup.closure (Set.range s)) fun x hx =>
      Subgroup.subset_closure ((List.mem_map.mp hx).imp fun _ hi => hi.2)
  · rw [← orderOf_injective (automorphismToMatrix f)
        (automorphismToMatrix_injective f) u₀, hu0mat]
    exact (orderOf_eq_prime_iff (p := 5) (x := nFourUMat 2)).mpr
      ⟨nFourUMat_two_pow_five, nFourUMat_two_ne_one⟩
  · intro k hk
    have hpowmat : LinearMap.toMatrix f f
        ((u₀ ^ k : V5 ≃ₗ[ZMod 5] V5) : V5 →ₗ[ZMod 5] V5) = nFourUMat 2 ^ k := by
      change automorphismToMatrix f (u₀ ^ k) = nFourUMat 2 ^ k
      rw [map_pow, hu0mat]
    have hsub : LinearMap.toMatrix f f
        (((u₀ ^ k : V5 ≃ₗ[ZMod 5] V5) : V5 →ₗ[ZMod 5] V5) - 1) = nFourM 2 k := by
      rw [map_sub, LinearMap.toMatrix_one, hpowmat]
      rfl
    exact ker_le_range_of_toMatrix f _ (by
      rw [hsub]
      exact matrix_ker_le_range_cases 2 k ⟨Or.inl rfl, hk⟩)

private lemma exists_u0_three {V5 : Type} [AddCommGroup V5] [Module (ZMod 5) V5]
    (f : Module.Basis (Fin 4) (ZMod 5) V5) :
    ∃ u₀ ∈ basisClosure f (weylN4Mats 3), orderOf u₀ = 5 ∧
      (∀ k : ℕ, (k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) →
        LinearMap.ker (((u₀ ^ k : V5 ≃ₗ[ZMod 5] V5) : V5 →ₗ[ZMod 5] V5) - 1) ≤
          LinearMap.range (((u₀ ^ k : V5 ≃ₗ[ZMod 5] V5) : V5 →ₗ[ZMod 5] V5) - 1)) := by
  obtain ⟨s, hs, hcl, -, -⟩ :=
    exists_n4_tuple two_zmod5_ne_zero three_zmod5_sq f
  have hmat : ∀ i, automorphismToMatrix f (s i) = n4Mat 3 i :=
    fun i => by rw [automorphismToMatrix_apply]; exact hs i
  let u₀ : V5 ≃ₗ[ZMod 5] V5 := (nFourOrderWord.map s).prod
  have hu0mat : automorphismToMatrix f u₀ = nFourUMat 3 := by
    dsimp only [u₀, nFourUMat]
    rw [map_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun i _ => hmat i)
  refine ⟨u₀, ?_, ?_, ?_⟩
  · rw [← hcl]
    exact Subgroup.list_prod_mem (Subgroup.closure (Set.range s)) fun x hx =>
      Subgroup.subset_closure ((List.mem_map.mp hx).imp fun _ hi => hi.2)
  · rw [← orderOf_injective (automorphismToMatrix f)
        (automorphismToMatrix_injective f) u₀, hu0mat]
    exact (orderOf_eq_prime_iff (p := 5) (x := nFourUMat 3)).mpr
      ⟨nFourUMat_three_pow_five, nFourUMat_three_ne_one⟩
  · intro k hk
    have hpowmat : LinearMap.toMatrix f f
        ((u₀ ^ k : V5 ≃ₗ[ZMod 5] V5) : V5 →ₗ[ZMod 5] V5) = nFourUMat 3 ^ k := by
      change automorphismToMatrix f (u₀ ^ k) = nFourUMat 3 ^ k
      rw [map_pow, hu0mat]
    have hsub : LinearMap.toMatrix f f
        (((u₀ ^ k : V5 ≃ₗ[ZMod 5] V5) : V5 →ₗ[ZMod 5] V5) - 1) = nFourM 3 k := by
      rw [map_sub, LinearMap.toMatrix_one, hpowmat]
      rfl
    exact ker_le_range_of_toMatrix f _ (by
      rw [hsub]
      exact matrix_ker_le_range_cases 3 k ⟨Or.inr rfl, hk⟩)

private lemma sylow_data {H : Type} [Group H] [Finite H] {uH u0H : H}
    (huHord : orderOf uH = 5) (hu0Hord : orderOf u0H = 5) (hcard : ¬ 25 ∣ Nat.card H) :
    ∃ (k' : ℕ) (y : H), (k' = 1 ∨ k' = 2 ∨ k' = 3 ∨ k' = 4) ∧
      uH = y⁻¹ * u0H ^ k' * y := by
  have h5pow : u0H ^ 5 = 1 := by
    have h := pow_orderOf_eq_one u0H
    rwa [hu0Hord] at h
  obtain ⟨y, hy⟩ := TauCeti.exists_mul_mul_inv_mem_zpowers_of_not_sq_dvd
    (G := H) (p := 5) (by simpa using hcard) hu0Hord huHord
  rw [Subgroup.mem_zpowers_iff] at hy
  obtain ⟨k, hk⟩ := hy
  have hkmod : u0H ^ k = u0H ^ (k % 5) := zpow_eq_zpow_emod' k h5pow
  have hk'z : (((k % 5).toNat : ℕ) : ℤ) = k % 5 :=
    Int.toNat_of_nonneg (Int.emod_nonneg k (by norm_num))
  have hk' : u0H ^ (k % 5).toNat = y * uH * y⁻¹ := by
    rw [← zpow_natCast, hk'z, ← hkmod, hk]
  have hk'lt : (k % 5).toNat < 5 := by omega
  have hk'ne : (k % 5).toNat ≠ 0 := by
    intro h0
    have h1 : y * uH * y⁻¹ = 1 := by rw [← hk', h0, pow_zero]
    have hone := eq_one_of_conj_eq_one h1
    rw [hone, orderOf_one] at huHord
    exact absurd huHord (by norm_num)
  have hk'cases : (k % 5).toNat = 1 ∨ (k % 5).toNat = 2 ∨ (k % 5).toNat = 3 ∨
      (k % 5).toNat = 4 := by omega
  refine ⟨(k % 5).toNat, y, hk'cases, ?_⟩
  rw [hk']
  group

private lemma sylow_conj {V5 : Type} [AddCommGroup V5] [Module (ZMod 5) V5]
    (f : Module.Basis (Fin 4) (ZMod 5) V5)
    {S : Set (Matrix (Fin 4) (Fin 4) (ZMod 5))} (hcard : ¬ 25 ∣ Nat.card (basisClosure f S))
    {u u₀ : V5 ≃ₗ[ZMod 5] V5} (hu : u ∈ basisClosure f S)
    (hu₀ : u₀ ∈ basisClosure f S) (h5 : orderOf u = 5) (hu₀ord : orderOf u₀ = 5) :
    ∃ (k' : ℕ) (y : V5 ≃ₗ[ZMod 5] V5), (k' = 1 ∨ k' = 2 ∨ k' = 3 ∨ k' = 4) ∧
      (u : V5 →ₗ[ZMod 5] V5) = ((y⁻¹ : V5 ≃ₗ[ZMod 5] V5) : V5 →ₗ[ZMod 5] V5) *
        ((u₀ ^ k' : V5 ≃ₗ[ZMod 5] V5) : V5 →ₗ[ZMod 5] V5) *
        (y : V5 →ₗ[ZMod 5] V5) := by
  let H : Subgroup (V5 ≃ₗ[ZMod 5] V5) := basisClosure f S
  have : Finite V5 := Finite.of_injective f.equivFun f.equivFun.injective
  have : Finite (V5 ≃ₗ[ZMod 5] V5) :=
    Finite.of_injective (fun e : V5 ≃ₗ[ZMod 5] V5 => (e : V5 → V5))
      (fun _ _ h => LinearEquiv.ext fun v => congrFun h v)
  have : Finite H := Subtype.finite
  have huH : u ∈ H := hu
  have hu₀H : u₀ ∈ H := hu₀
  have huHord : orderOf (⟨u, huH⟩ : H) = 5 := by
    rw [Subgroup.orderOf_mk u huH, h5]
  have hu0Hord : orderOf (⟨u₀, hu₀H⟩ : H) = 5 := by
    rw [Subgroup.orderOf_mk u₀ hu₀H, hu₀ord]
  obtain ⟨k', y, hk'cases, hy⟩ :=
    sylow_data huHord hu0Hord (by simpa using hcard)
  refine ⟨k', (y : V5 ≃ₗ[ZMod 5] V5), hk'cases, ?_⟩
  have := congrArg (fun z : H => (z : V5 →ₗ[ZMod 5] V5)) hy
  simpa [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_inv] using this

private lemma conj_apply {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {u u₀ : V ≃ₗ[K] V} {k' : ℕ} {y : V ≃ₗ[K] V}
    (hcoe : (u : V →ₗ[K] V) = ((y⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) *
      ((u₀ ^ k' : V ≃ₗ[K] V) : V →ₗ[K] V) * (y : V →ₗ[K] V))
    (hpow : LinearMap.ker (((u₀ ^ k' : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) ≤
      LinearMap.range (((u₀ ^ k' : V ≃ₗ[K] V) : V →ₗ[K] V) - 1)) :
    LinearMap.ker ((u : V →ₗ[K] V) - 1) ≤ LinearMap.range ((u : V →ₗ[K] V) - 1) := by
  have hg1 : ((y⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) * (y : V →ₗ[K] V) = 1 := by
    ext v
    rw [Module.End.mul_apply]
    simp
  have hgoal : (u : V →ₗ[K] V) - 1 =
      ((y⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) *
        (((u₀ ^ k' : V ≃ₗ[K] V) : V →ₗ[K] V) - 1) * (y : V →ₗ[K] V) := by
    rw [hcoe, mul_sub, mul_one, sub_mul, hg1]
  rw [hgoal]
  exact ker_le_range_conj (y⁻¹) hpow

theorem ker_sub_one_le_range_of_orderOf_eq_five (hp5 : p = 5)
    (f : Module.Basis (Fin 4) (ZMod p) V) {t : ZMod p} (ht : t ^ 2 = -1)
    {S : Set (Matrix (Fin 4) (Fin 4) (ZMod p))} (hS : S = weylN4Mats t ∨ S = weylEN4Mats t)
    (hcard : ¬ 25 ∣ Nat.card (basisClosure f S)) {u : V ≃ₗ[ZMod p] V}
    (hu : u ∈ basisClosure f S) (h5 : orderOf u = 5) :
    LinearMap.ker ((u : V →ₗ[ZMod p] V) - 1) ≤ LinearMap.range ((u : V →ₗ[ZMod p] V) - 1) := by
  subst p
  have ht23 : t = 2 ∨ t = 3 := zmod5_sq_eq_neg_one ht
  have hU0 : ∃ u₀ ∈ basisClosure f (weylN4Mats t), orderOf u₀ = 5 ∧
      (∀ k : ℕ, (k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4) →
        LinearMap.ker (((u₀ ^ k : V ≃ₗ[ZMod 5] V) : V →ₗ[ZMod 5] V) - 1) ≤
          LinearMap.range (((u₀ ^ k : V ≃ₗ[ZMod 5] V) : V →ₗ[ZMod 5] V) - 1)) := by
    rcases ht23 with rfl | rfl
    · exact exists_u0_two f
    · exact exists_u0_three f
  obtain ⟨u₀, hu₀N4, hu₀ord, hu₀pow⟩ := hU0
  have hsubN4 : basisClosure f (weylN4Mats t) ≤ basisClosure f S := by
    rcases hS with rfl | rfl
    · exact le_rfl
    · exact Subgroup.closure_mono fun g hg => Set.mem_insert_of_mem (diagSignMat 3) hg
  obtain ⟨k', y, hk'cases, hcoe⟩ :=
    sylow_conj f hcard hu (hsubN4 hu₀N4) h5 hu₀ord
  exact conj_apply hcoe (hu₀pow k' hk'cases)

private theorem exists_mem_inf_centralizer_ne_zero [Module.Finite (ZMod p) V]
    {VX VY CY : Submodule (ZMod p) V}
    (hle : VY ≤ VX) (hsup : VY ⊔ CY = ⊤) (hinf : VY ⊓ CY = ⊥)
    (h4 : Module.finrank (ZMod p) VX = 4) (h3 : Module.finrank (ZMod p) VY = 3) :
    ∃ c ∈ VX ⊓ CY, c ≠ 0 := by
  have hVX : VX = VY ⊔ (VX ⊓ CY) := by
    have h1 : VX ⊓ (VY ⊔ CY) = VY ⊔ VX ⊓ CY := by
      rw [inf_comm VX (VY ⊔ CY), sup_inf_assoc_of_le CY hle, inf_comm CY VX]
    rwa [hsup, inf_top_eq] at h1
  have hfr : Module.finrank (ZMod p) ↥(VX ⊓ CY) = 1 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq VY (VX ⊓ CY)
    rw [← hVX] at h
    have hdisj : VY ⊓ (VX ⊓ CY) = ⊥ := by
      rw [← inf_assoc, inf_eq_left.mpr hle, hinf]
    rw [hdisj, finrank_bot, add_zero, h4, h3] at h
    omega
  have hne : VX ⊓ CY ≠ ⊥ := by
    intro hbot
    have : Module.finrank (ZMod p) ↥(VX ⊓ CY) = 0 := by rw [hbot, finrank_bot]
    omega
  exact Submodule.exists_mem_ne_zero_of_ne_bot hne

private theorem restrictHom_sub_mem_commutatorSpace {X Y : Subgroup (V ≃ₗ[ZMod p] V)} (hYX : Y ≤ X)
    (y : Y) (w : HardMathSupport.Kantor79.commutatorSpace X) :
    ((restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
        (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨y.1, hYX y.2⟩ w : _) : V) - (w : V) ∈
      HardMathSupport.Kantor79.commutatorSpace Y := by
  rw [restrictHom_apply]
  exact HardMathSupport.Kantor79.movedSpace_le_commutatorSpace y.2 ⟨(w : V), rfl⟩

private theorem exists_ker_not_range_restrictHom [Module.Finite (ZMod p) V]
    {X Y : Subgroup (V ≃ₗ[ZMod p] V)} (hYX : Y ≤ X)
    (hsX : SplitSupport X 4) (hsY : SplitSupport Y 3) (y : Y)
    (z : HardMathSupport.Kantor79.commutatorSpace X ≃ₗ[ZMod p]
      HardMathSupport.Kantor79.commutatorSpace X)
    (hz : z = restrictHom X (HardMathSupport.Kantor79.commutatorSpace X)
      (fun _ hh _ hv => apply_mem_commutatorSpace hh hv) ⟨y.1, hYX y.2⟩) :
    ∃ c : HardMathSupport.Kantor79.commutatorSpace X,
      c ∈ LinearMap.ker ((z : HardMathSupport.Kantor79.commutatorSpace X →ₗ[ZMod p]
          HardMathSupport.Kantor79.commutatorSpace X) - 1) ∧
      c ∉ LinearMap.range ((z : HardMathSupport.Kantor79.commutatorSpace X →ₗ[ZMod p]
          HardMathSupport.Kantor79.commutatorSpace X) - 1) := by
  let VX := HardMathSupport.Kantor79.commutatorSpace X
  let VY := HardMathSupport.Kantor79.commutatorSpace Y
  let CY := centralizerSpace Y
  subst z
  obtain ⟨c, hc, hc0⟩ := exists_mem_inf_centralizer_ne_zero (VX := VX) (VY := VY) (CY := CY)
    (HardMathSupport.Kantor79.commutatorSpace_mono hYX) hsY.1.sup_eq_top hsY.1.inf_eq_bot
    hsX.2.1 hsY.2.1
  rw [Submodule.mem_inf] at hc
  refine ⟨⟨c, hc.1⟩, ?_, ?_⟩
  · rw [LinearMap.mem_ker]
    change (restrictHom X VX (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
        ⟨y.1, hYX y.2⟩ : VX →ₗ[ZMod p] VX) ⟨c, hc.1⟩ - (⟨c, hc.1⟩ : VX) = 0
    rw [sub_eq_zero]
    apply Subtype.ext
    change (restrictHom X VX (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
        ⟨y.1, hYX y.2⟩ ⟨c, hc.1⟩ : V) = c
    rw [restrictHom_apply]
    exact (mem_centralizerSpace.mp hc.2) y y.2
  · rintro ⟨w, hw⟩
    have hcw : c ∈ VY := by
      have hval : ((restrictHom X VX (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
          ⟨y.1, hYX y.2⟩ w : VX) : V) - (w : V) = c := by
        have h := congrArg (fun x : VX => (x : V)) hw
        change ((restrictHom X VX (fun _ hh _ hv => apply_mem_commutatorSpace hh hv)
          ⟨y.1, hYX y.2⟩ w : VX) : V) - (w : V) = c at h
        simpa using h
      rw [← hval]
      exact restrictHom_sub_mem_commutatorSpace hYX y w
    have : c ∈ VY ⊓ CY := ⟨hcw, hc.2⟩
    rw [hsY.1.inf_eq_bot] at this
    exact hc0 ((Submodule.mem_bot (ZMod p)).mp this)

theorem false_of_isOrthType_of_le_of_ker_le_range (hp5 : p = 5) [Module.Finite (ZMod p) V]
    {X Y : Subgroup (V ≃ₗ[ZMod p] V)} (hYX : Y ≤ X) (hsX : SplitSupport X 4)
    (hsY : SplitSupport Y 3) (hOY : IsOrthType p (movedGroup Y))
    (hX : ∀ u ∈ movedGroup X, orderOf u = 5 →
      LinearMap.ker ((u : HardMathSupport.Kantor79.commutatorSpace X →ₗ[ZMod p]
          HardMathSupport.Kantor79.commutatorSpace X) - 1) ≤
        LinearMap.range ((u : HardMathSupport.Kantor79.commutatorSpace X →ₗ[ZMod p]
          HardMathSupport.Kantor79.commutatorSpace X) - 1)) : False := by
  let VX := HardMathSupport.Kantor79.commutatorSpace X
  let VY := HardMathSupport.Kantor79.commutatorSpace Y
  let hXinv : ∀ h ∈ X, ∀ w ∈ VX, h w ∈ VX := fun _ hh _ hv => apply_mem_commutatorSpace hh hv
  let hYinv : ∀ h ∈ Y, ∀ w ∈ VY, h w ∈ VY := fun _ hh _ hv => apply_mem_commutatorSpace hh hv
  obtain ⟨g, hgY, hgord⟩ := TableFacts.exists_orderOf_eq_of_isOrthType (V := VY)
    (by omega) (by rw [hsY.2.1]) hOY
  obtain ⟨y₀, hy₀⟩ := MonoidHom.mem_range.mp hgY
  have hYinj : Function.Injective (restrictHom Y VY hYinv) :=
    restrictHom_injective_of_splitSupport hsY
  have hy0ord : orderOf y₀ = 5 := by
    have h := orderOf_injective (restrictHom Y VY hYinv) hYinj y₀
    rw [hy₀, hgord] at h
    exact h.symm.trans hp5
  let yX : X := ⟨y₀.1, hYX y₀.2⟩
  let z : VX ≃ₗ[ZMod p] VX := restrictHom X VX hXinv yX
  have hzmem : z ∈ movedGroup X := MonoidHom.mem_range.mpr ⟨yX, rfl⟩
  have hzord : orderOf z = 5 := by
    have h1 := orderOf_injective (restrictHom X VX hXinv)
      (restrictHom_injective_of_splitSupport hsX) yX
    have h2 : orderOf yX = orderOf y₀ :=
      (Subgroup.orderOf_mk y₀.1 (hYX y₀.2)).trans (Subgroup.orderOf_coe y₀)
    rw [h2, hy0ord] at h1
    exact h1
  obtain ⟨c, hker, hnotrange⟩ := exists_ker_not_range_restrictHom hYX hsX hsY y₀ z rfl
  exact hnotrange (hX z hzmem hzord hker)

private theorem card_of_modelIso_n4
    {A : Subgroup (V ≃ₗ[ZMod p] V)}
    (h : ModelIso p .N4 A) : Nat.card A = 7680 := by
  obtain ⟨e, -⟩ := h
  rw [← Nat.card_congr e.toEquiv, card_model_n4]

private theorem card_of_modelIso_en4
    {A : Subgroup (V ≃ₗ[ZMod p] V)}
    (h : ModelIso p .EN4 A) : Nat.card A = 46080 := by
  obtain ⟨e, -⟩ := h
  rw [← Nat.card_congr e.toEquiv, card_model_en4]

private theorem center_card_of_modelIso_n4
    {A : Subgroup (V ≃ₗ[ZMod p] V)}
    (h : ModelIso p .N4 A) : Nat.card (Subgroup.center ↥A) = 4 := by
  obtain ⟨e, -⟩ := h
  obtain ⟨-, -, -, -, -, hcenter, -⟩ := exists_n4_model
  rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective, hcenter]

private theorem center_card_of_modelIso_en4
    {A : Subgroup (V ≃ₗ[ZMod p] V)}
    (h : ModelIso p .EN4 A) : Nat.card (Subgroup.center ↥A) = 4 := by
  obtain ⟨e, -⟩ := h
  obtain ⟨-, -, -, -, -, hcenter, -⟩ := exists_en4_model
  rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective, hcenter]

private theorem exists_pair_of_model {A : Subgroup (V ≃ₗ[ZMod p] V)}
    {M : Subgroup (Matrix.GeneralLinearGroup (Fin 4) (ZMod 13))} (e : ↥M ≃* ↥A)
    (hrefl : ∀ g : ↥M, IsReflMat g.1 ↔ IsRefl p (e g : V ≃ₗ[ZMod p] V))
    {t₀ t₂ c : ↥M} (href0 : IsReflMat t₀.1) (hord : orderOf (t₀ * t₂) = 4)
    (hc : c * t₀ * c⁻¹ = t₂) :
    ∃ x ∈ A, ∃ y ∈ A, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) := by
  have hrefl0A : IsRefl p (e t₀ : V ≃ₗ[ZMod p] V) := (hrefl t₀).mp href0
  have hcA : (e c : V ≃ₗ[ZMod p] V) * (e t₀ : V ≃ₗ[ZMod p] V) *
      ((e c : V ≃ₗ[ZMod p] V))⁻¹ = (e t₂ : V ≃ₗ[ZMod p] V) := by
    have h := congrArg (fun z : ↥M => (e z : V ≃ₗ[ZMod p] V)) hc
    simpa [map_mul, map_inv] using h
  have hrefl2A : IsRefl p (e t₂ : V ≃ₗ[ZMod p] V) := by
    have h := IsRefl.conj hrefl0A (e c : V ≃ₗ[ZMod p] V)
    rwa [hcA] at h
  have hgt : 3 < orderOf ((e t₀ : V ≃ₗ[ZMod p] V) * (e t₂ : V ≃ₗ[ZMod p] V)) := by
    have h1 : orderOf ((e t₀ : V ≃ₗ[ZMod p] V) * (e t₂ : V ≃ₗ[ZMod p] V)) =
        orderOf (e t₀ * e t₂ : ↥A) := by
      rw [← Subgroup.coe_mul, Subgroup.orderOf_coe]
    have h2 : orderOf (e t₀ * e t₂ : ↥A) = orderOf (t₀ * t₂) := by
      rw [← map_mul]
      exact orderOf_injective (e : ↥M →* ↥A) e.injective (t₀ * t₂)
    rw [h1, h2, hord]
    norm_num
  exact ⟨(e t₀ : V ≃ₗ[ZMod p] V), (e t₀).2, (e t₂ : V ≃ₗ[ZMod p] V), (e t₂).2,
    hrefl0A, hrefl2A, hgt⟩

private theorem exists_pair_of_modelIso_n4
    {A : Subgroup (V ≃ₗ[ZMod p] V)}
    (h : ModelIso p .N4 A) :
    ∃ x ∈ A, ∃ y ∈ A, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) := by
  obtain ⟨e, hrefl⟩ := h
  obtain ⟨t, htm, -, -, -, -, -, -, href0, hord⟩ := exists_n4_model
  have hrel : N4Rel t := n4Rel_of_model htm
  have hsq0 : t 0 * t 0 = 1 := by
    have h := hrel.1 0 0
    rwa [show nFourExp 0 0 = 1 by decide, pow_one] at h
  have hsq1 : t 1 * t 1 = 1 := by
    have h := hrel.1 1 1
    rwa [show nFourExp 1 1 = 1 by decide, pow_one] at h
  have hsq2 : t 2 * t 2 = 1 := by
    have h := hrel.1 2 2
    rwa [show nFourExp 2 2 = 1 by decide, pow_one] at h
  have h3a : (t 0 * t 1) ^ 3 = 1 := by
    have h := hrel.1 0 1
    rwa [show nFourExp 0 1 = 3 by decide] at h
  have h3b : (t 1 * t 2) ^ 3 = 1 := by
    have h := hrel.1 1 2
    rwa [show nFourExp 1 2 = 3 by decide] at h
  have hconj01 : IsConj (t 0) (t 1) := isConj_iff.mpr
    ⟨t 0 * t 1, CFSG.Timmesfeld.Components.conj_eq_of_pow_three hsq0 hsq1 h3a⟩
  have hconj12 : IsConj (t 1) (t 2) := isConj_iff.mpr
    ⟨t 1 * t 2, CFSG.Timmesfeld.Components.conj_eq_of_pow_three hsq1 hsq2 h3b⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp (hconj01.trans hconj12)
  exact exists_pair_of_model e hrefl href0 hord hc

private theorem exists_pair_of_modelIso_en4
    {A : Subgroup (V ≃ₗ[ZMod p] V)}
    (h : ModelIso p .EN4 A) :
    ∃ x ∈ A, ∃ y ∈ A, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) := by
  obtain ⟨e, hrefl⟩ := h
  obtain ⟨t, htm, -, -, -, -, -, -, href0, hord⟩ := exists_en4_model
  have hrel : EN4Rel t := en4Rel_of_model htm
  have hsq0 : t 0 * t 0 = 1 := by
    have h := hrel.1 0 0
    rwa [show enFourExp 0 0 = 1 by decide, pow_one] at h
  have hsq1 : t 1 * t 1 = 1 := by
    have h := hrel.1 1 1
    rwa [show enFourExp 1 1 = 1 by decide, pow_one] at h
  have hsq2 : t 2 * t 2 = 1 := by
    have h := hrel.1 2 2
    rwa [show enFourExp 2 2 = 1 by decide, pow_one] at h
  have h3a : (t 0 * t 1) ^ 3 = 1 := by
    have h := hrel.1 0 1
    rwa [show enFourExp 0 1 = 3 by decide] at h
  have h3b : (t 1 * t 2) ^ 3 = 1 := by
    have h := hrel.1 1 2
    rwa [show enFourExp 1 2 = 3 by decide] at h
  have hconj01 : IsConj (t 0) (t 1) := isConj_iff.mpr
    ⟨t 0 * t 1, CFSG.Timmesfeld.Components.conj_eq_of_pow_three hsq0 hsq1 h3a⟩
  have hconj12 : IsConj (t 1) (t 2) := isConj_iff.mpr
    ⟨t 1 * t 2, CFSG.Timmesfeld.Components.conj_eq_of_pow_three hsq1 hsq2 h3b⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp (hconj01.trans hconj12)
  exact exists_pair_of_model e hrefl href0 hord hc

private theorem not_imprimitive_of_modelIso [Module.Finite (ZMod p) V]
    (hp5 : p = 5)
    {X : Subgroup (V ≃ₗ[ZMod p] V)} (hX : ReflGen p X) (hsX : SplitSupport X 4)
    (hmodel : ModelIso p .N4 (movedGroup X) ∨ ModelIso p .EN4 (movedGroup X)) :
    ¬ Quasithin.SimsG4.IsImprimitiveOnV (movedGroup X) := by
  intro himp
  have hp2 : p ≠ 2 := by rw [hp5]; norm_num
  obtain ⟨b, i₀, i₁, ζ, hi, heq⟩ :=
    TableFacts.exists_monomial_movedGroup hp2 (m := 4) (by norm_num) hX hsX himp
  have hlow : 7680 ≤ Nat.card (movedGroup X) := by
    rcases hmodel with h | h
    · rw [card_of_modelIso_n4 h]
    · rw [card_of_modelIso_en4 h]; norm_num
  have hζdvd : orderOf ζ ∣ p - 1 :=
    orderOf_dvd_iff_pow_eq_one.mpr (ZMod.units_pow_card_sub_one_eq_one p ζ)
  have hζle : orderOf ζ ≤ 4 := by
    have h : orderOf ζ ≤ p - 1 := Nat.le_of_dvd (by omega) hζdvd
    omega
  have hζdvd4 : orderOf ζ ∣ 4 := by
    have h : p - 1 = 4 := by omega
    rwa [h] at hζdvd
  rcases heq with hm | hm
  · have hcard : Nat.card (movedGroup X) = orderOf ζ ^ 3 * 24 := by
      rw [hm, card_gmmn (p := p) (n := 4) (by norm_num) b hi ζ]
      norm_num
    have h1536 : orderOf ζ ^ 3 * 24 ≤ 1536 := by
      calc orderOf ζ ^ 3 * 24 ≤ 4 ^ 3 * 24 :=
            Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hζle 3)
        _ = 1536 := by norm_num
    omega
  · have hcard : Nat.card (movedGroup X) = 2 * Nat.lcm 2 (orderOf ζ) ^ 3 * 24 := by
      rw [hm, card_g2mmn hp2 (n := 4) (by norm_num) b hi ζ]
      norm_num
    have hlcmdvd : Nat.lcm 2 (orderOf ζ) ∣ 4 := Nat.lcm_dvd (by norm_num) hζdvd4
    have hlcm : Nat.lcm 2 (orderOf ζ) ≤ 4 := Nat.le_of_dvd (by norm_num) hlcmdvd
    have h3072 : 2 * Nat.lcm 2 (orderOf ζ) ^ 3 * 24 ≤ 3072 := by
      calc 2 * Nat.lcm 2 (orderOf ζ) ^ 3 * 24 ≤ 2 * 4 ^ 3 * 24 :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hlcm 3))
        _ = 3072 := by norm_num
    omega

private theorem quadraticForm_exists_ne_zero {Q : QuadraticForm (ZMod p) V} {v : V}
    (hv : v ≠ 0) (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) : ∃ w, Q w ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hv (hQ.1 v fun y => by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, h (v + y), h v, h y]
    ring)

private theorem false_of_isOrthType_of_center_card_four [Module.Finite (ZMod p) V]
    {v : V} (hv : v ≠ 0) {A : Subgroup (V ≃ₗ[ZMod p] V)} (habs : AbsIrred p A)
    (horth : IsOrthType p A) (hcenter : Nat.card (Subgroup.center ↥A) = 4) : False := by
  obtain ⟨Q, hQ, hcase⟩ := horth
  obtain ⟨z, hzA, hzcent, hzord⟩ := exists_orderOf_eq_card_center_of_absIrred habs
  let zA : ↥A := ⟨z, hzA⟩
  have hzcenter : zA ∈ Subgroup.center ↥A := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (hzcent g.1 g.2).symm
  have hzordA : orderOf zA = 4 := by
    rw [Subgroup.orderOf_mk z hzA, hzord, hcenter]
  obtain ⟨c, hc⟩ := habs.exists_eq_smul_of_mem_center hzcenter
  have hzisom : IsIsom p Q (zA : V ≃ₗ[ZMod p] V) := by
    rcases hcase with hO | ⟨c₀, hc₀, hAc⟩
    · exact (hO z).mp hzA
    · rw [hAc] at hzA
      exact isIsom_of_mem_closure_classRefl hzA
  obtain ⟨v₀, hv₀⟩ := quadraticForm_exists_ne_zero hv hQ
  have hcv : ∀ w : V, (zA : V ≃ₗ[ZMod p] V) w = c • w := fun w => by
    have h := congrArg (fun f : V →ₗ[ZMod p] V => f w) hc
    simpa using h
  have hQv := hzisom v₀
  rw [hcv v₀, QuadraticMap.map_smul] at hQv
  have hc2 : c ^ 2 = 1 := by
    have h2 : (c * c - 1) • Q v₀ = 0 := by rw [sub_smul, hQv, one_smul, sub_self]
    have hzero : c * c - 1 = 0 := (smul_eq_zero.mp h2).resolve_right hv₀
    rw [pow_two]; exact sub_eq_zero.mp hzero
  have hc2' : c * c = 1 := by rw [← pow_two]; exact hc2
  have hz2 : zA ^ 2 = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    ext v
    change (zA : V ≃ₗ[ZMod p] V) ((zA : V ≃ₗ[ZMod p] V) v) = v
    rw [hcv, hcv, smul_smul, hc2', one_smul]
  have hdvd : orderOf zA ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hz2
  have hle : orderOf zA ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

private theorem model_data
    {A : Subgroup (V ≃ₗ[ZMod p] V)}
    (h : ModelIso p .N4 A ∨ ModelIso p .EN4 A) :
    (Nat.card A = 7680 ∨ Nat.card A = 46080) ∧ Nat.card (Subgroup.center ↥A) = 4 ∧
      (∃ x ∈ A, ∃ y ∈ A, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) := by
  rcases h with h | h
  · exact ⟨Or.inl (card_of_modelIso_n4 h), center_card_of_modelIso_n4 h,
      exists_pair_of_modelIso_n4 h⟩
  · exact ⟨Or.inr (card_of_modelIso_en4 h), center_card_of_modelIso_en4 h,
      exists_pair_of_modelIso_en4 h⟩

private theorem false_of_basisClosure_weyl [Module.Finite (ZMod p) V] (hp5 : p = 5)
    {X Y : Subgroup (V ≃ₗ[ZMod p] V)} (hYX : Y ≤ X) (hsX : SplitSupport X 4)
    (hsY : SplitSupport Y 3) (hOY : IsOrthType p (movedGroup Y))
    (hcard : Nat.card (movedGroup X) = 7680 ∨ Nat.card (movedGroup X) = 46080)
    {f : Module.Basis (Fin 4) (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X)}
    {t : ZMod p} (ht : t ^ 2 = -1) {S : Set (Matrix (Fin 4) (Fin 4) (ZMod p))}
    (hS : S = weylN4Mats t ∨ S = weylEN4Mats t) (hX : movedGroup X = basisClosure f S) : False := by
  refine false_of_isOrthType_of_le_of_ker_le_range hp5 hYX hsX hsY hOY ?_
  intro u hu h5
  have hcard25 : ¬ 25 ∣ Nat.card (basisClosure f S) := by
    rw [← hX]
    rcases hcard with h | h <;> rw [h] <;> norm_num
  exact ker_sub_one_le_range_of_orderOf_eq_five hp5 f ht hS hcard25 (hX ▸ hu) h5

theorem tfNFourFive_of_dLargeFourModel
    (hL : DLargeFourModel p) : TFNFourFive p := by
  unfold TFNFourFive
  intro hp5 U _ _ _ X Y hYX hXr htv hsX hmodel hYr hsY hOY
  unfold DLargeFourModel at hL
  have hp2 : p ≠ 2 := by rw [hp5]; norm_num
  have hrefl : ReflGen p (movedGroup X) := reflGen_movedGroup hXr
  have habs : AbsIrred p (movedGroup X) := absIrred_movedGroup hXr hsX
  have htv' : QTwoLin.TransvectionFree (movedGroup X) := transvectionFree_movedGroup hsX htv
  have hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV (movedGroup X) :=
    not_imprimitive_of_modelIso hp5 hXr hsX hmodel
  obtain ⟨hcard, hcenter, hpair⟩ := model_data hmodel
  have hres := hL (HardMathSupport.Kantor79.commutatorSpace X) (movedGroup X) hp2 hsX.2.1
    hrefl habs hprim htv' hpair
  rcases hres with hOrth | hN4case | hF4case | hH4case
  · have hpos : 0 < Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X) := by
      rw [hsX.2.1]; norm_num
    obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
    exact false_of_isOrthType_of_center_card_four hv habs hOrth hcenter
  · rcases hN4case with ⟨-, f, t, ht, hN4 | hEN4⟩
    · exact false_of_basisClosure_weyl hp5 hYX hsX hsY hOY hcard ht (Or.inl rfl) hN4
    · exact false_of_basisClosure_weyl hp5 hYX hsX hsY hOY hcard ht (Or.inr rfl) hEN4
  · obtain ⟨-, -, f, hF4⟩ := hF4case
    have h1152 : Nat.card (movedGroup X) = 1152 := by
      rw [hF4, TableFacts.card_basisClosure_weylF4 hp2 f]
    rcases hcard with h | h <;> rw [h] at h1152 <;> omega
  · exact hH4case.1 hp5

end CFSG.StandardType.ZS

end
