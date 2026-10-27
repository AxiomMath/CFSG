module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoOmCoord
public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoOmChars
import CFSG.GroupTheory.WeirSylow.OrthogonalTori
import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentTypeSum
import CFSG.ClassicalGroups.Orthogonal.PolarPairPlane

public section

namespace CFSG.StandardType.ChoiceTwoOm.OmCoord

open Module QuadraticMap
open CFSG.GroupTheory.WeirSylow
open CFSG.ClassicalGroups.Orthogonal

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {A : Subgroup (V ≃ₗ[K] V)}

private theorem p9Coord_forall_eq_zero_or_one {K : Type} [Field K] [CharP K 2]
    (hK : Nat.card K = 2) : ∀ a : K, a = 0 ∨ a = 1 := by
  obtain ⟨y, hy_ne, hy_unique⟩ := (Nat.card_eq_two_iff' (0 : K)).mp hK
  have hy1 : y = 1 := (hy_unique 1 one_ne_zero).symm
  intro a
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    have hay : a = y := hy_unique a ha
    rw [hay, hy1]

private theorem p9Coord_eq_zpow_of_commute_zL {K : Type} [Field K] [CharP K 2]
    (hK01 : ∀ a : K, a = 0 ∨ a = 1) (T : (K × K) →ₗ[K] (K × K))
    (hT : ∀ c, T (zL K c) = zL K (T c)) (hne : T ≠ 0) :
    ∃ a : ZMod 3, T = (zpow a : (K × K) ≃ₗ[K] (K × K)).toLinearMap := by
  set u := T (1, 0) with hu
  set u1 := u.1 with hu1
  set u2 := u.2 with hu2
  have hu' : u = (u1, u2) := rfl
  have hTz : T (0, 1) = zL K u := by
    have hz : (0, 1) = zL K (1, 0) := by
      rw [zL_apply]
      simp
    rw [hz, hT, hu]
  have hTc : ∀ c : K × K, T c = c.1 • u + c.2 • zL K u := by
    intro c
    have hc : c = c.1 • ((1, 0) : K × K) + c.2 • ((0, 1) : K × K) := by
      ext <;> simp
    calc
      T c = T (c.1 • ((1, 0) : K × K) + c.2 • ((0, 1) : K × K)) := by
        conv_lhs => rw [hc]
      _ = c.1 • T ((1, 0) : K × K) + c.2 • T ((0, 1) : K × K) := by
        rw [map_add, map_smul, map_smul]
      _ = c.1 • u + c.2 • zL K u := by rw [hTz, ← hu]
  rcases hK01 u1 with h1 | h1 <;> rcases hK01 u2 with h2 | h2
  · exfalso
    apply hne
    apply LinearMap.ext
    intro c
    rw [hTc c, hu', h1, h2]
    apply Prod.ext <;> simp [zL_apply]
  · refine ⟨1, ?_⟩
    have h1val : (1 : ZMod 3).val = 1 := by decide
    have hz1 : (zpow (1 : ZMod 3) : (K × K) ≃ₗ[K] (K × K)) = zL K := by
      rw [zpow, h1val, pow_one]
    apply LinearMap.ext
    intro c
    rw [hTc c, hu', h1, h2, hz1]
    apply Prod.ext <;> simp [zL_apply]
  · refine ⟨0, ?_⟩
    apply LinearMap.ext
    intro c
    rw [hTc c, hu', h1, h2, zpow_zero]
    have hz10 : (zL K) ((1 : K), (0 : K)) = ((0 : K), (1 : K)) := by
      rw [zL_apply]
      simp
    rw [hz10]
    simp
  · refine ⟨2, ?_⟩
    have h2val : (2 : ZMod 3).val = 2 := by decide
    apply LinearMap.ext
    intro c
    rw [hTc c, hu', h1, h2, zpow, h2val, pow_two]
    apply Prod.ext
    · simp [zL_apply]
    · simp [zL_apply]
      have h2' : (1 : K) + 1 = 0 := add_self_K 1
      rw [h2']
      simp
      linear_combination -add_self_K c.2

private theorem p9Coord_preserves_plane (C : OmCoord K Q A) {g : V ≃ₗ[K] V}
    (hg : ∀ f, g * C.tor f = C.tor f * g) :
    ∀ i : Fin C.s, ∀ c : K × K,
      ∃ c', g (C.Φ (Pi.single i c, 0)) = C.Φ (Pi.single i c', 0) := by
  intro i c
  refine C.preserves_plane (f₀ := 0) (f₁ := Pi.single i (1 : ZMod 3)) (i := i) rfl ?_ ?_
    (hg 0) (hg (Pi.single i (1 : ZMod 3))) c
  · simp
  · intro l hl _
    rw [Pi.single_eq_of_ne hl]

private theorem p9Coord_planeMap_zpow (hK01 : ∀ a : K, a = 0 ∨ a = 1)
    (C : OmCoord K Q A) {g : V ≃ₗ[K] V} (hg : ∀ f, g * C.tor f = C.tor f * g)
    (hpres : ∀ i : Fin C.s, ∀ c : K × K,
      ∃ c', g (C.Φ (Pi.single i c, 0)) = C.Φ (Pi.single i c', 0)) :
    ∀ i : Fin C.s, ∃ a : ZMod 3,
      C.planeMap i g = (zpow a : (K × K) ≃ₗ[K] (K × K)).toLinearMap := by
  intro i
  have hz : ∀ c, C.planeMap i g (zL K c) = zL K (C.planeMap i g c) := by
    intro c
    have h1val : (1 : ZMod 3).val = 1 := by decide
    have hz1 : (zpow (1 : ZMod 3) : (K × K) ≃ₗ[K] (K × K)) = zL K := by
      rw [zpow, h1val, pow_one]
    have e := congrArg (fun k : V ≃ₗ[K] V => k (C.Φ (Pi.single i c, 0)))
      (hg (Pi.single i (1 : ZMod 3)))
    simp only [LinearEquiv.mul_apply, C.tor_single, Pi.single_eq_same,
      C.apply_plane (hpres i)] at e
    rw [hz1] at e
    exact C.single_injective e
  have hne : C.planeMap i g ≠ 0 := by
    intro h0
    have hinj : Function.Injective (C.planeMap i g) := by
      intro c c' hcc'
      apply C.single_injective
      apply g.injective
      rw [C.apply_plane (hpres i) c, C.apply_plane (hpres i) c', hcc']
    have hzero : ((1 : K), (0 : K)) = 0 := hinj (by rw [h0]; rfl)
    have h1zero : (1 : K) = 0 := congrArg Prod.fst hzero
    exact one_ne_zero h1zero
  exact p9Coord_eq_zpow_of_commute_zL hK01 _ hz hne

private theorem p9Coord_fixedSpace_map (C : OmCoord K Q A) {g : V ≃ₗ[K] V}
    (hg : ∀ f, g * C.tor f = C.tor f * g) :
    ∃ m : C.W0 →ₗ[K] C.W0, ∀ x, g (C.Φ (0, x)) = C.Φ (0, m x) := by
  let m : C.W0 →ₗ[K] C.W0 :=
    (LinearMap.snd K (Fin C.s → K × K) C.W0).comp
      (C.Φ.symm.toLinearMap.comp (g.toLinearMap.comp (C.Φ.toLinearMap.comp
        (LinearMap.inr K (Fin C.s → K × K) C.W0))))
  have hψ1 : ∀ x : C.W0, (C.Φ.symm (g (C.Φ (0, x)))).1 = 0 := by
    intro x
    set p := C.Φ.symm (g (C.Φ (0, x))) with hp
    obtain ⟨d, y⟩ := p
    change d = 0
    funext i
    have hv : C.Φ (d, y) = g (C.Φ (0, x)) := by
      rw [hp, C.Φ.apply_symm_apply]
    have hfix : C.tor (Pi.single i (1 : ZMod 3)) (C.Φ (d, y)) = C.Φ (d, y) := by
      rw [hv]
      have e := congrArg (fun k : V ≃ₗ[K] V => k (C.Φ (0, x))) (hg (Pi.single i 1))
      simp only [LinearEquiv.mul_apply] at e
      rw [← e, C.tor_acts]
      have h0 : torC (Pi.single i (1 : ZMod 3)) (0 : Fin C.s → K × K) = 0 := by
        funext l
        simp [torC_apply]
      rw [h0]
    exact (C.tor_Φ_eq_iff (Pi.single i (1 : ZMod 3)) d y).mp hfix i (by simp)
  have hm0 : ∀ x : C.W0, C.Φ.symm (g (C.Φ (0, x))) = (0, m x) := by
    intro x
    apply Prod.ext
    · exact hψ1 x
    · rfl
  refine ⟨m, fun x => ?_⟩
  rw [← C.Φ.apply_symm_apply (g (C.Φ (0, x))), hm0 x]

theorem exists_torC_of_commute (hK : Nat.card K = 2) (C : OmCoord K Q A) {g : V ≃ₗ[K] V}
    (hg : ∀ f, g * C.tor f = C.tor f * g) :
    ∃ (f₀ : Fin C.s → ZMod 3) (m : C.W0 →ₗ[K] C.W0),
      ∀ d x, g (C.Φ (d, x)) = C.Φ (torC f₀ d, m x) := by
  classical
  have hK01 : ∀ a : K, a = 0 ∨ a = 1 := p9Coord_forall_eq_zero_or_one hK
  have hpres := p9Coord_preserves_plane C hg
  choose f₀ hf₀ using p9Coord_planeMap_zpow hK01 C hg hpres
  obtain ⟨m, hm⟩ := p9Coord_fixedSpace_map C hg
  refine ⟨f₀, m, fun d x => ?_⟩
  have hsum : (∑ i : Fin C.s, (Pi.single i (d i), (0 : C.W0))) = (d, 0) := by
    apply Prod.ext
    · rw [Prod.fst_sum]
      exact Finset.univ_sum_single d
    · rw [Prod.snd_sum]
      simp
  have hsplit : C.Φ (d, x) = ∑ i, C.Φ (Pi.single i (d i), 0) + C.Φ (0, x) := by
    calc
      C.Φ (d, x) = C.Φ ((d, 0) + (0, x)) := by simp
      _ = C.Φ (d, 0) + C.Φ (0, x) := map_add _ _ _
      _ = C.Φ (∑ i, (Pi.single i (d i), (0 : C.W0))) + C.Φ (0, x) := by rw [← hsum]
      _ = ∑ i, C.Φ (Pi.single i (d i), 0) + C.Φ (0, x) := by rw [map_sum]
  calc
    g (C.Φ (d, x)) = g (∑ i, C.Φ (Pi.single i (d i), 0) + C.Φ (0, x)) := by rw [hsplit]
    _ = ∑ i, g (C.Φ (Pi.single i (d i), 0)) + g (C.Φ (0, x)) := by rw [map_add, map_sum]
    _ = ∑ i, C.Φ (Pi.single i ((C.planeMap i g) (d i)), 0) + C.Φ (0, m x) := by
      congr 1
      · exact Finset.sum_congr rfl fun i _ => C.apply_plane (hpres i) (d i)
      · exact hm x
    _ = ∑ i, C.Φ (Pi.single i (zpow (f₀ i) (d i)), 0) + C.Φ (0, m x) := by
      congr 1
      exact Finset.sum_congr rfl fun i _ => by
        rw [hf₀ i]
        rfl
    _ = C.Φ (∑ i, (Pi.single i (zpow (f₀ i) (d i)), (0 : C.W0)) + (0, m x)) := by
      rw [map_add, map_sum]
    _ = C.Φ (torC f₀ d, m x) := by
      congr 1
      apply Prod.ext
      · funext k
        simp [torC_apply, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · simp [Prod.snd_sum]

section TypeHelpers

private noncomputable def p9Coord_Qp (s : ℕ) : QuadraticForm K (Fin s → K × K) :=
  QuadraticMap.pi (fun _ : Fin s => binForm (1 : K) 1)

private theorem p9Coord_binForm_nondegenerate :
    (polarBilin (binForm (1 : K) 1)).Nondegenerate := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hpolar : ∀ v w : K × K, polar (binForm (1 : K) 1) v w =
      2 * v.1 * w.1 + (v.1 * w.2 + w.1 * v.2) + 2 * v.2 * w.2 := by
    intro v w
    rw [QuadraticMap.polar, binForm_apply, binForm_apply, binForm_apply]
    simp only [Prod.fst_add, Prod.snd_add]
    ring
  refine CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun v hv => ?_
  have h1 : 2 * v.1 + v.2 = 0 := by
    have := hv (1, 0)
    rw [hpolar] at this
    simpa using this
  have h2' : v.1 + 2 * v.2 = 0 := by
    have := hv (0, 1)
    rw [hpolar] at this
    simpa using this
  rw [h2] at h1 h2'
  simp at h1 h2'
  exact Prod.ext h2' h1

private theorem p9Coord_binForm_not_plus (hK : Nat.card K = 2) :
    ¬ IsPlusType (binForm (1 : K) 1) := by
  have hK01 : ∀ a : K, a = 0 ∨ a = 1 := p9Coord_forall_eq_zero_or_one hK
  have hirr : ∀ s : K, s ^ 2 + (1 : K) * s + 1 ≠ 0 := by
    intro s
    rcases hK01 s with rfl | rfl
    · norm_num
    · intro hzero
      have h : (1 : K) + 1 = 0 := add_self_K 1
      have h1 : (1 : K) = 0 := by
        linear_combination hzero - h
      exact one_ne_zero h1
  rintro ⟨W, hW, hWs⟩
  have hdim : finrank K W = 1 := by
    have h2 : finrank K (K × K) = 2 := by simp
    omega
  obtain ⟨w, hw0⟩ := Module.finrank_pos_iff_exists_ne_zero.1 (by omega : 0 < finrank K W)
  have hw : (w : K × K) ≠ 0 := fun h => hw0 (Subtype.ext h)
  have hQw : binForm (1 : K) 1 (w : K × K) = 0 := hWs w w.2
  exact hw (binForm_eq_zero hirr hQw)

variable (C : OmCoord K Q A)

private noncomputable def p9Coord_plane (i : Fin C.s) : Submodule K (Fin C.s → K × K) :=
  LinearMap.range (LinearMap.single K (fun _ : Fin C.s => K × K) i)

private theorem p9Coord_plane_finrank (i : Fin C.s) :
    finrank K (p9Coord_plane C i) = 2 := by
  have hinj : Function.Injective (LinearMap.single K (fun _ : Fin C.s => K × K) i) := by
    intro c c' h
    have := congrFun h i
    simpa [LinearMap.single_apply] using this
  rw [p9Coord_plane, LinearMap.finrank_range_of_inj hinj]
  simp

private noncomputable def p9Coord_planeIsometry (i : Fin C.s) :
    (binForm (1 : K) 1).IsometryEquiv
      ((p9Coord_Qp (K := K) C.s).comp (p9Coord_plane C i).subtype) := by
  have hinj : Function.Injective (LinearMap.single K (fun _ : Fin C.s => K × K) i) := by
    intro c c' h
    have := congrFun h i
    simpa [LinearMap.single_apply] using this
  exact
    { toLinearEquiv := LinearEquiv.ofInjective
        (LinearMap.single K (fun _ : Fin C.s => K × K) i) hinj
      map_app' := by
        intro c
        change (p9Coord_Qp (K := K) C.s) (Pi.single i c) = binForm (1 : K) 1 c
        rw [p9Coord_Qp, QuadraticMap.pi_apply_single] }

private theorem p9Coord_plane_nondegenerate (i : Fin C.s) :
    (polarBilin ((p9Coord_Qp (K := K) C.s).comp (p9Coord_plane C i).subtype)).Nondegenerate :=
  nondegenerate_polarBilin_of_isometryEquiv (p9Coord_planeIsometry C i)
    (p9Coord_binForm_nondegenerate (K := K))

private theorem p9Coord_plane_not_plus (hK : Nat.card K = 2) (i : Fin C.s) :
    ¬ IsPlusType ((p9Coord_Qp (K := K) C.s).comp (p9Coord_plane C i).subtype) := by
  intro h
  exact p9Coord_binForm_not_plus hK ((isPlusType_congr (p9Coord_planeIsometry C i)).2 h)

private theorem p9Coord_plane_perp (i j : Fin C.s) (hij : i ≠ j)
    (x : Fin C.s → K × K) (hx : x ∈ p9Coord_plane C i)
    (y : Fin C.s → K × K) (hy : y ∈ p9Coord_plane C j) :
    polar (p9Coord_Qp (K := K) C.s) x y = 0 := by
  obtain ⟨cx, rfl⟩ := LinearMap.mem_range.1 hx
  obtain ⟨cy, rfl⟩ := LinearMap.mem_range.1 hy
  rw [p9Coord_Qp, CFSG.GroupTheory.WeirSylow.polar_pi]
  refine Finset.sum_eq_zero fun k _ => ?_
  simp only [LinearMap.single_apply]
  by_cases hki : k = i
  · subst hki
    simp [hij]
  · simp [hki]

private theorem p9Coord_planeSystem (hK : Nat.card K = 2) :
    CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.IsPlaneSystem (p9Coord_Qp (K := K) C.s)
      (p9Coord_plane C) where
  finrank_eq i := p9Coord_plane_finrank C i
  nondeg i := p9Coord_plane_nondegenerate C i
  not_isPlusType i := p9Coord_plane_not_plus C hK i
  perp i j hij x hx y hy := p9Coord_plane_perp C i j hij x hx y hy

private theorem p9Coord_Qp_top :
    (⨆ j ∈ (Finset.univ : Finset (Fin C.s)), p9Coord_plane C j) = ⊤ := by
  apply top_unique
  intro d _
  rw [← Finset.univ_sum_single d]
  refine Submodule.sum_mem _ fun i _ => ?_
  exact Submodule.mem_iSup_of_mem i
    (Submodule.mem_iSup_of_mem (Finset.mem_univ i) (LinearMap.mem_range_self _ _))

private theorem p9Coord_Qp_even [Finite K] (hK : Nat.card K = 2) :
    IsPlusType (p9Coord_Qp (K := K) C.s) ↔ Even C.s := by
  have h := (p9Coord_planeSystem C hK).isPlusType_biSup_iff
    (Finset.univ : Finset (Fin C.s))
  rw [p9Coord_Qp_top C, Finset.card_univ, Fintype.card_fin] at h
  exact (CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.isPlusType_comp_top_iff).symm.trans h

end TypeHelpers

private noncomputable def p9Coord_isometry (C : OmCoord K Q A) :
    ((p9Coord_Qp (K := K) C.s).prod (Q.restrict C.W0)).IsometryEquiv Q :=
  { toLinearEquiv := C.Φ
    map_app' := by
      intro p
      obtain ⟨d, x⟩ := p
      change Q (C.Φ (d, x)) = (p9Coord_Qp (K := K) C.s) d + (Q.restrict C.W0) x
      rw [C.form]
      have hQp : (p9Coord_Qp (K := K) C.s) d = ∑ i, binForm (1 : K) 1 (d i) := by
        rw [p9Coord_Qp, QuadraticMap.pi_apply]
      rw [hQp]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by
        rw [binForm_apply, nrm]
        ring }

private theorem p9Coord_isPlusType_prod_bot (C : OmCoord K Q A) (hW0 : C.W0 = ⊥) :
    IsPlusType ((p9Coord_Qp (K := K) C.s).prod (Q.restrict C.W0)) ↔
      IsPlusType (p9Coord_Qp (K := K) C.s) := by
  have hsub : Subsingleton C.W0 := by
    rw [hW0]
    infer_instance
  let proj : ((Fin C.s → K × K) × C.W0) ≃ₗ[K] (Fin C.s → K × K) :=
    { toFun := Prod.fst
      invFun := fun d => (d, 0)
      left_inv := fun p => by
        obtain ⟨d, x⟩ := p
        simp [hsub.elim x 0]
      right_inv := fun d => rfl
      map_add' := fun p q => rfl
      map_smul' := fun c p => rfl }
  let e0 : ((p9Coord_Qp (K := K) C.s).prod (Q.restrict C.W0)).IsometryEquiv
      (p9Coord_Qp (K := K) C.s) :=
    { toLinearEquiv := proj
      map_app' := by
        intro p
        obtain ⟨d, x⟩ := p
        change (p9Coord_Qp (K := K) C.s) d =
          (p9Coord_Qp (K := K) C.s) d + (Q.restrict C.W0) x
        have hx : x = 0 := hsub.elim x 0
        simp [hx] }
  exact isPlusType_congr e0

private theorem p9Coord_restrict_nondegenerate [FiniteDimensional K V]
    (C : OmCoord K Q A) (hrank : finrank K C.W0 = 2) {x y : C.W0}
    (hx : Q x = 0) (hy : Q y = 0) (hxy : polar Q x y = 1) :
    (polarBilin (Q.restrict C.W0)).Nondegenerate := by
  let xV : V := (x : V)
  let yV : V := (y : V)
  have hxV : Q xV = 0 := hx
  have hyV : Q yV = 0 := hy
  have hxyV : polar Q xV yV = 1 := hxy
  let S : Submodule K V := Submodule.span K {xV, yV}
  have hS_le : S ≤ C.W0 := by
    refine Submodule.span_le.2 ?_
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact x.2
    · exact y.2
  have hli : LinearIndependent K ![xV, yV] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have habV : a • xV + b • yV = 0 := hab
    have h1 : polar Q (a • xV + b • yV) xV = 0 := by rw [habV, polar_zero_left]
    have h2 : polar Q (a • xV + b • yV) yV = 0 := by rw [habV, polar_zero_left]
    rw [polar_add_left, polar_smul_left, polar_smul_left] at h1 h2
    rw [polar_self_eq_zero xV, polar_comm Q yV xV, hxyV] at h1
    rw [hxyV, polar_self_eq_zero yV] at h2
    simp only [zero_add, smul_eq_mul, mul_one, mul_zero, add_zero] at h1 h2
    exact ⟨h2, h1⟩
  have hS_finrank : finrank K S = 2 := by
    have h := finrank_span_eq_card hli
    rwa [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union, Fintype.card_fin] at h
  have hW0eq : C.W0 = S := by
    refine (Submodule.eq_of_le_of_finrank_eq hS_le ?_).symm
    rw [hS_finrank, hrank]
  have hPND : PolarNondegOn Q C.W0 := by
    rw [hW0eq]
    exact polarNondegOn_span_pair_of_polar_eq_one hxyV
  constructor
  · intro w hw
    apply Subtype.ext
    refine hPND (w : V) w.2 fun z hz => ?_
    have h := hw ⟨z, hz⟩
    rw [QuadraticMap.polarBilin_apply_apply] at h
    simpa [polar, QuadraticMap.restrict_apply] using h
  · intro w hw
    apply Subtype.ext
    refine hPND (w : V) w.2 fun z hz => ?_
    have h := hw ⟨z, hz⟩
    rw [QuadraticMap.polarBilin_apply_apply, polar_comm] at h
    simpa [polar, QuadraticMap.restrict_apply] using h

private theorem p9Coord_isPlusType_prod_hyperbolic [Finite K] [FiniteDimensional K V]
    (C : OmCoord K Q A)
    (hW0 : finrank K C.W0 = 2 ∧ ∃ x y : C.W0, Q x = 0 ∧ Q y = 0 ∧ polar Q x y = 1) :
    IsPlusType ((p9Coord_Qp (K := K) C.s).prod (Q.restrict C.W0)) ↔
      IsPlusType (p9Coord_Qp (K := K) C.s) := by
  obtain ⟨hrank, x, y, hx, hy, hxy⟩ := hW0
  have hxne : x ≠ 0 := by
    intro hx0
    have hx0' : (x : V) = 0 := by simpa using congrArg Subtype.val hx0
    have : polar Q (x : V) (y : V) = 0 := by rw [hx0', polar_zero_left]
    rw [this] at hxy
    exact zero_ne_one hxy
  have hW0plus : IsPlusType (Q.restrict C.W0) := by
    refine ⟨Submodule.span K {x}, ?_, ?_⟩
    · rw [finrank_span_singleton hxne]
      omega
    · intro z hz
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
      change Q ((c • x : C.W0) : V) = 0
      rw [Submodule.coe_smul, QuadraticMap.map_smul, hx, smul_zero]
  have hQpnd : (polarBilin (p9Coord_Qp (K := K) C.s)).Nondegenerate := by
    rw [p9Coord_Qp]
    exact nondegenerate_polarBilin_pi (fun _ => p9Coord_binForm_nondegenerate (K := K))
  have hW0nd := p9Coord_restrict_nondegenerate C hrank hx hy hxy
  by_cases hs : C.s = 0
  · have hsub : Subsingleton (Fin C.s → K × K) := by
      rw [hs]
      infer_instance
    have hQp : IsPlusType (p9Coord_Qp (K := K) C.s) :=
      @isPlusType_of_subsingleton K _ (Fin C.s → K × K) _ _ hsub _
    exact ⟨fun _ => hQp, fun _ => hQp.prod hW0plus⟩
  · have hs1 : 1 ≤ C.s := by omega
    have hdim : finrank K (Fin C.s → K × K) = 2 * C.s := by
      rw [Module.finrank_pi_fintype]
      simp [Module.finrank_prod, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      ring
    have hdimW : finrank K C.W0 = 2 * 1 := by omega
    have hiff := CFSG.RankThree.PartOne.K159.isPlusType_prod_iff
      (Q₁ := p9Coord_Qp (K := K) C.s) (Q₂ := Q.restrict C.W0)
      hQpnd hW0nd hs1 (by norm_num) hdim hdimW
    rw [hiff]
    simp [hW0plus]

private theorem p9Coord_isPlusType_prod_iff [Finite K] [FiniteDimensional K V]
    (C : OmCoord K Q A)
    (hW0 : C.W0 = ⊥ ∨
      (finrank K C.W0 = 2 ∧ ∃ x y : C.W0, Q x = 0 ∧ Q y = 0 ∧ polar Q x y = 1)) :
    IsPlusType ((p9Coord_Qp (K := K) C.s).prod (Q.restrict C.W0)) ↔
      IsPlusType (p9Coord_Qp (K := K) C.s) := by
  rcases hW0 with hW0 | hW0
  · exact p9Coord_isPlusType_prod_bot C hW0
  · exact p9Coord_isPlusType_prod_hyperbolic C hW0

theorem isPlusType_iff_even [Finite K] [FiniteDimensional K V] (hK : Nat.card K = 2)
    (C : OmCoord K Q A)
    (hW0 : C.W0 = ⊥ ∨
      (finrank K C.W0 = 2 ∧ ∃ x y : C.W0, Q x = 0 ∧ Q y = 0 ∧ polar Q x y = 1)) :
    CFSG.GroupTheory.WeirSylow.IsPlusType Q ↔ Even C.s := by
  have hprod := p9Coord_isPlusType_prod_iff C hW0
  have hcongr : IsPlusType ((p9Coord_Qp (K := K) C.s).prod (Q.restrict C.W0)) ↔
      IsPlusType Q := isPlusType_congr (p9Coord_isometry C)
  exact (hcongr.symm.trans hprod).trans (p9Coord_Qp_even C hK)

end CFSG.StandardType.ChoiceTwoOm.OmCoord
