module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusCurtis
public import CFSG.RankThree.GF2n.Smith81.S81QGraphCl
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusOuterOrbit
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusOuterBound
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusOuterInvol
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmPlusFamRep
import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQTrivType

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.Quasithin.SmithCurtis
open CFSG.RankThree.GF2n.Smith81.D6Spin (graphSpin)

variable {F : Type} [Field F] [Finite F] [CharP F 2]

private noncomputable def w135c2_omfPORep_repEquiv {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (g : G) : V ≃ₗ[k] V :=
  have hleft : Function.LeftInverse (ρ g⁻¹) (ρ g) := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hright : Function.RightInverse (ρ g⁻¹) (ρ g) := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  LinearEquiv.ofBijective (ρ g) ⟨hleft.injective, hright.surjective⟩

private theorem w135c2_omfPORep_repEquiv_apply {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (g : G) (v : V) :
    w135c2_omfPORep_repEquiv ρ g v = ρ g v := rfl

private theorem w135c2_omfPORep_repEquiv_symm_apply {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (g : G) (v : V) :
    (w135c2_omfPORep_repEquiv ρ g).symm v = ρ g⁻¹ v := by
  rw [LinearEquiv.symm_apply_eq]
  change v = ρ g (ρ g⁻¹ v)
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

private theorem w135c2_omfPORep_finrank_range_conj {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] (L : V ≃ₗ[k] V) (T : V →ₗ[k] V) :
    Module.finrank k (LinearMap.range (L.toLinearMap * T * L.symm.toLinearMap - 1)) =
      Module.finrank k (LinearMap.range (T - 1)) := by
  have h1 : L.toLinearMap * L.symm.toLinearMap = 1 := by
    ext v; simp
  have hconj : L.toLinearMap * T * L.symm.toLinearMap - 1 =
      L.toLinearMap * (T - 1) * L.symm.toLinearMap := by
    rw [mul_sub, sub_mul, mul_one, h1]
  have hsurj : Function.Surjective L.symm.toLinearMap := L.symm.surjective
  have hrange : LinearMap.range (L.toLinearMap * (T - 1) * L.symm.toLinearMap) =
      (LinearMap.range (T - 1)).map L.toLinearMap := by
    rw [show L.toLinearMap * (T - 1) * L.symm.toLinearMap =
      (L.toLinearMap).comp ((T - 1).comp L.symm.toLinearMap) from rfl]
    rw [LinearMap.range_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]
  rw [hconj, hrange]
  exact L.finrank_map_eq (LinearMap.range (T - 1))

private theorem w135c2_omfPORep_finrank_conj_T1 {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] (L T T₁ : V ≃ₗ[k] V) (hT₁ : T₁ = L * T * L⁻¹) :
    Module.finrank k (LinearMap.range (T₁.toLinearMap - 1)) =
      Module.finrank k (LinearMap.range (T.toLinearMap - 1)) := by
  have h1 : T₁.toLinearMap = L.toLinearMap * T.toLinearMap * L.symm.toLinearMap := by
    rw [hT₁, LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul]
    rfl
  have h := w135c2_omfPORep_finrank_range_conj L T.toLinearMap
  rwa [← h1] at h

private theorem w135c2_omfPORep_conj_intertwine {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (γ : G ≃* G) (T : V ≃ₗ[k] V)
    {h g z : G} (hgn : g * h * γ g⁻¹ = z)
    (hT : ∀ a v, T (ρ a v) = ρ (h * γ a * h⁻¹) (T v)) :
    ∀ a v, (w135c2_omfPORep_repEquiv ρ g * T * (w135c2_omfPORep_repEquiv ρ g)⁻¹) (ρ a v) =
      ρ (z * γ a * z⁻¹)
        ((w135c2_omfPORep_repEquiv ρ g * T * (w135c2_omfPORep_repEquiv ρ g)⁻¹) v) := by
  intro a v
  let L := w135c2_omfPORep_repEquiv ρ g
  have hLapply : ∀ v, L v = ρ g v := w135c2_omfPORep_repEquiv_apply ρ g
  have hLsymm : ∀ v, L.symm v = ρ g⁻¹ v := w135c2_omfPORep_repEquiv_symm_apply ρ g
  have hTv : T v = ρ (h * γ g * h⁻¹) (T (L.symm v)) := by
    have h1 : T v = T (L (L.symm v)) := by rw [LinearEquiv.apply_symm_apply]
    rw [h1, hLapply]
    exact hT g (L.symm v)
  have hgrp : g * (h * γ (g⁻¹ * a) * h⁻¹) * (h * γ g * h⁻¹) =
      g * (h * γ (g⁻¹ * a * g) * h⁻¹) := by
    simp only [map_mul, map_inv]
    group
  have hgrp2 : g * (h * γ (g⁻¹ * a * g) * h⁻¹) = (z * γ a * z⁻¹) * g := by
    rw [← hgn]
    simp only [map_mul, map_inv]
    group
  calc (L * T * L⁻¹) (ρ a v)
      = L (T (L.symm (ρ a v))) := rfl
    _ = L (T (ρ (g⁻¹ * a) v)) := by rw [hLsymm, act_mul]
    _ = L (ρ (h * γ (g⁻¹ * a) * h⁻¹) (T v)) := by rw [hT (g⁻¹ * a) v]
    _ = ρ (g * (h * γ (g⁻¹ * a) * h⁻¹)) (T v) := by rw [hLapply, act_mul]
    _ = ρ (g * (h * γ (g⁻¹ * a) * h⁻¹)) (ρ (h * γ g * h⁻¹) (T (L.symm v))) := by rw [hTv]
    _ = ρ (g * (h * γ (g⁻¹ * a) * h⁻¹) * (h * γ g * h⁻¹)) (T (L.symm v)) := by rw [act_mul]
    _ = ρ (g * (h * γ (g⁻¹ * a * g) * h⁻¹)) (T (L.symm v)) := by rw [hgrp]
    _ = ρ (z * γ a * z⁻¹) ((L * T * L⁻¹) v) := by
          rw [show (L * T * L⁻¹) v = ρ g (T (L.symm v)) from rfl]
          rw [act_mul, hgrp2]

private theorem w135c2_omfPORep_twist_intertwine {k G V : Type*} [Field k] [Group G]
    [AddCommGroup V] [Module k V] (ρ : Representation k G V) (γ : G ≃* G) (T₁ : V ≃ₗ[k] V)
    {z : G} (hT1 : ∀ a v, T₁ (ρ a v) = ρ (z * γ a * z⁻¹) (T₁ v)) :
    ∀ a v, ((w135c2_omfPORep_repEquiv ρ z)⁻¹ * T₁) (ρ a v) =
      ρ (γ a) (((w135c2_omfPORep_repEquiv ρ z)⁻¹ * T₁) v) := by
  intro a v
  let Nx := w135c2_omfPORep_repEquiv ρ z
  have hNsymm : ∀ v, Nx.symm v = ρ z⁻¹ v := w135c2_omfPORep_repEquiv_symm_apply ρ z
  have hNsymm_apply : ∀ b w, Nx.symm (ρ b w) = ρ (z⁻¹ * b) w := by
    intro b w
    rw [hNsymm, act_mul]
  have hgrp : z⁻¹ * (z * γ a * z⁻¹) = γ a * z⁻¹ := by group
  calc (Nx.symm * T₁) (ρ a v)
      = Nx.symm (T₁ (ρ a v)) := rfl
    _ = Nx.symm (ρ (z * γ a * z⁻¹) (T₁ v)) := by rw [hT1 a v]
    _ = ρ (z⁻¹ * (z * γ a * z⁻¹)) (T₁ v) := hNsymm_apply _ _
    _ = ρ (γ a) (Nx.symm (T₁ v)) := by rw [hNsymm, act_mul, hgrp]
    _ = ρ (γ a) ((Nx.symm * T₁) v) := rfl

private theorem w135c2_omfPORep_T1_y0 {k G V : Type*} [Field k] [Group G] [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) (z : G) (T₁ T' : V ≃ₗ[k] V)
    (hT' : T' = (w135c2_omfPORep_repEquiv ρ z).symm * T₁) {y₀ : V} (hy : T' y₀ = y₀) :
    T₁ y₀ = ρ z y₀ := by
  have h1 : T₁ y₀ = w135c2_omfPORep_repEquiv ρ z (T' y₀) := by
    rw [hT']
    exact (LinearEquiv.apply_symm_apply _ _).symm
  rw [h1, hy, w135c2_omfPORep_repEquiv_apply]

private theorem w135c2_omfPORep_zmod_two (c : ZMod 2) (hc : c ≠ 0) : c = 1 := by
  have h0 : c.val ≠ 0 := fun h => hc ((ZMod.val_eq_zero c).mp h)
  have hlt : c.val < 2 := ZMod.val_lt c
  have hval : c.val = 1 := by omega
  rw [← ZMod.natCast_zmod_val c, hval]
  norm_num

open CFSG.RankThree.GF2n.Smith81.D6Spin in
private theorem w135c2_omfPORep_graphSpin_graphSpin {n : ℕ} {K : Type} [Field K] (i₀ : Fin n)
    (x : spinGroup (quadPlus n K)) :
    graphSpin n K i₀ (graphSpin n K i₀ x) = x := by
  apply Subtype.ext
  show CliffordAlgebra.map (swapIso n K i₀) (CliffordAlgebra.map (swapIso n K i₀)
    (x : CliffordAlgebra (quadPlus n K))) = x
  exact cliffMap_cliffMap _ (swapIso_swapIso n K i₀) _

private theorem w135c2_omfPORep_omExtWt_comp_swap {n j : ℕ} (hj : j + 2 ≤ n) {hn : 2 ≤ n} :
    omExtWt n j ∘ omGraphSwap hn = omExtWt n j := by
  funext a
  rw [Function.comp_apply]
  rcases eq_or_ne a ⟨n - 2, by omega⟩ with h | h
  · subst h
    rw [omGraphSwap, Equiv.swap_apply_left]
    exact (omExtWt_apply_last hj).symm
  · rcases eq_or_ne a ⟨n - 1, by omega⟩ with h' | h'
    · subst h'
      rw [omGraphSwap, Equiv.swap_apply_right]
      exact omExtWt_apply_last hj
    · rw [omGraphSwap, Equiv.swap_apply_of_ne_of_ne h h']

open CFSG.LieType.RootSystem CFSG.StandardType in
private theorem w135c2_omfPORep_fix_y0 (_hF : Nat.card F = 2) {n : ℕ} (hn3 : 3 ≤ n)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadPlus n F)) V} (hρ : IsSimpleRep ρ)
    {y₀ : V} {χ : spinGroup (quadPlus n F) → ZMod 2} {μ : Fin n → ZMod 2}
    (ht : (omPlusCurtisDatum n F hn3).IsCurtisType ρ y₀ χ μ) (T' : V ≃ₗ[ZMod 2] V)
    (hT' : ∀ a v, T' (ρ a v) = ρ (graphSpin n F ⟨n - 1, by omega⟩ a) (T' v)) :
    T' y₀ = y₀ := by
  let D := omPlusCurtisDatum n F hn3
  have hfixU : ∀ {v : V}, v ∈ D.fixU ρ → T' v ∈ D.fixU ρ := by
    intro v hv
    rw [D.mem_fixU] at hv ⊢
    intro u hu
    have hγu : graphSpin n F ⟨n - 1, by omega⟩ u ∈ D.U := by
      have hsymm : (graphSpin n F ⟨n - 1, by omega⟩).symm =
          graphSpin n F ⟨n - 1, by omega⟩ := by
        refine MulEquiv.ext fun y => ?_
        apply (graphSpin n F ⟨n - 1, by omega⟩).injective
        rw [MulEquiv.apply_symm_apply, w135c2_omfPORep_graphSpin_graphSpin]
      have := graphSpin_symm_mem_U_omPlus (K := F) hn3 hu
      rwa [hsymm] at this
    have hint : T' (ρ (graphSpin n F ⟨n - 1, by omega⟩ u) v) = ρ u (T' v) := by
      rw [hT', w135c2_omfPORep_graphSpin_graphSpin]
    rw [← hint, hv (graphSpin n F ⟨n - 1, by omega⟩ u) hγu]
  obtain ⟨c, hc⟩ := D.fixU_eq_smul hρ ht (hfixU ht.1)
  have hc1 : c = 1 := by
    refine w135c2_omfPORep_zmod_two c fun hc0 => ?_
    have h0 : T' y₀ = 0 := by rw [hc, hc0, zero_smul]
    exact ht.2.1 (T'.injective (by rw [h0, map_zero]))
  rw [hc, hc1, one_smul]

open CFSG.LieType.RootSystem CFSG.StandardType in
private theorem w135c2_omfPORep_hv_inner (hF : Nat.card F = 2) {n : ℕ} (hn3 : 3 ≤ n)
    {χ : spinGroup (quadPlus n F) → ZMod 2} {μ : Fin n → ZMod 2} {j : ℕ}
    (hχ : χ 1 = 1) (hj : j + 3 ≤ n) (hμj : μ ⟨j, by omega⟩ = 1) :
    ∀ t : Fin n, μ t ≠ (omPlusCurtisDatum n F hn3).dScalar χ t →
      weylAction (isFiniteType_cartanD n)
        ((coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.simple t) (omExtWt n j) =
        omExtWt n j := by
  intro t htne
  have hn2 : 2 ≤ n := by omega
  have htne1 : μ t ≠ 1 := by rwa [omPlusCurtisDatum_two_dScalar hF hn3 hχ t] at htne
  have htj : t.val ≠ j := fun hh => htne1 (by
    have ht' : t = ⟨j, by omega⟩ := Fin.ext hh
    rw [ht']
    exact hμj)
  exact weylAction_simple_omExtWt hn2 hj htj

open CFSG.LieType.RootSystem CFSG.StandardType in
private theorem w135c2_omfPORep_hv_last (hF : Nat.card F = 2) {n : ℕ} (hn3 : 3 ≤ n)
    {χ : spinGroup (quadPlus n F) → ZMod 2} {μ : Fin n → ZMod 2} (hχ : χ 1 = 1)
    (hμn2 : μ ⟨n - 2, by omega⟩ = 1) (hμeq : μ ⟨n - 2, by omega⟩ = μ ⟨n - 1, by omega⟩) :
    ∀ t : Fin n, μ t ≠ (omPlusCurtisDatum n F hn3).dScalar χ t →
      weylAction (isFiniteType_cartanD n)
        ((coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.simple t)
        (omExtWt n (n - 2)) = omExtWt n (n - 2) := by
  intro t htne
  have hn2 : 2 ≤ n := by omega
  have htne1 : μ t ≠ 1 := by rwa [omPlusCurtisDatum_two_dScalar hF hn3 hχ t] at htne
  have htn2 : t ≠ ⟨n - 2, by omega⟩ := fun hh => htne1 (by rw [hh, hμn2])
  have htn1 : t ≠ ⟨n - 1, by omega⟩ := fun hh => htne1 (by rw [hh, ← hμeq, hμn2])
  have htlt : t.val + 2 < n := by
    have h1 := t.isLt
    have h2 : t.val ≠ n - 1 := fun hh => htn1 (Fin.ext hh)
    have h3 : t.val ≠ n - 2 := fun hh => htn2 (Fin.ext hh)
    omega
  exact weylAction_simple_omExtWt_of_add_two_eq hn2 (by omega) htlt

omit [Field F] [Finite F] [CharP F 2] in
open CFSG.LieType.RootSystem CFSG.StandardType in
private theorem w135c2_omfPORep_last_coord (_hF : Nat.card F = 2) {n : ℕ} (hn : 4 ≤ n)
    {x : (coxeterMatrix (isFiniteType_cartanD n)).Group}
    {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ}
    (hxr : OmRealizes n x π s) (hπ : π ⟨n - 1, by omega⟩ = ⟨n - 1, by omega⟩)
    (hs1 : s ⟨n - 1, by omega⟩ = 1) {j : ℕ} (hj : j + 2 ≤ n)
    {b b' : (coxeterMatrix (isFiniteType_cartanD n)).Group}
    (hb' : ∀ γ, weylAction (isFiniteType_cartanD n) b' γ =
      weylAction (isFiniteType_cartanD n) b (γ ∘ omGraphSwap (by omega)) ∘ omGraphSwap (by omega))
    (hulast : toStdD n (weylAction (isFiniteType_cartanD n) b (omExtWt n j))
      ⟨n - 1, by omega⟩ = 2) :
    toStdD n (weylAction (isFiniteType_cartanD n) (x * b') (omExtWt n j))
      ⟨n - 1, by omega⟩ = -2 := by
  have hn2 : 2 ≤ n := by omega
  rw [weylAction_mul_apply]
  have hbl : weylAction (isFiniteType_cartanD n) b' (omExtWt n j) =
      (weylAction (isFiniteType_cartanD n) b (omExtWt n j)) ∘ omGraphSwap hn2 := by
    rw [hb' (omExtWt n j), w135c2_omfPORep_omExtWt_comp_swap hj]
  rw [hbl, hxr]
  beta_reduce
  have hπsymm : π.symm ⟨n - 1, by omega⟩ = ⟨n - 1, by omega⟩ := by
    rw [Equiv.symm_apply_eq]
    exact hπ.symm
  rw [hπsymm, hs1, one_mul, toStdD_comp_omGraphSwap hn2, Function.update_self, hulast]

open CFSG.LieType.RootSystem CFSG.StandardType in
private theorem w135c2_omfPORep_orbit_hT1b (hF : Nat.card F = 2) {n : ℕ} (hn3 : 3 ≤ n)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadPlus n F)) V} {y₀ : V}
    {x : (coxeterMatrix (isFiniteType_cartanD n)).Group} {T₁ : V ≃ₗ[ZMod 2] V}
    {b b' : (coxeterMatrix (isFiniteType_cartanD n)).Group}
    (hT1y0 : T₁ y₀ = ρ ((omPlusCurtisDatum n F hn3).nW x) y₀)
    (hT1int : ∀ a w, T₁ (ρ a w) = ρ ((omPlusCurtisDatum n F hn3).nW x *
      graphSpin n F ⟨n - 1, by omega⟩ a * ((omPlusCurtisDatum n F hn3).nW x)⁻¹) (T₁ w))
    (hγ : graphSpin n F ⟨n - 1, by omega⟩ ((omPlusCurtisDatum n F hn3).nW b) =
      (omPlusCurtisDatum n F hn3).nW b') :
    T₁.toLinearMap (ρ ((omPlusCurtisDatum n F hn3).nW b) y₀) =
      (1 : ZMod 2) • ρ ((omPlusCurtisDatum n F hn3).nW (x * b')) y₀ := by
  rw [one_smul]
  show T₁ (ρ ((omPlusCurtisDatum n F hn3).nW b) y₀) =
    ρ ((omPlusCurtisDatum n F hn3).nW (x * b')) y₀
  have hgrp : (omPlusCurtisDatum n F hn3).nW x * (omPlusCurtisDatum n F hn3).nW b' *
      ((omPlusCurtisDatum n F hn3).nW x)⁻¹ * (omPlusCurtisDatum n F hn3).nW x =
      (omPlusCurtisDatum n F hn3).nW x * (omPlusCurtisDatum n F hn3).nW b' := by group
  rw [hT1int, hT1y0, hγ, act_mul, hgrp]
  rw [← omPlusCurtisDatum_two_nW_mul hF hn3]

open CFSG.LieType.RootSystem CFSG.StandardType in
private theorem w135c2_omfPORep_orbit_hinj {n j : ℕ} {u : Fin 4 → Fin n → ℤ}
    {b : Fin 4 → (coxeterMatrix (isFiniteType_cartanD n)).Group}
    (hu_inj : Function.Injective u)
    (hb : ∀ i, u i = weylAction (isFiniteType_cartanD n) (b i) (omExtWt n j)) :
    ∀ i l, i ≠ l → weylAction (isFiniteType_cartanD n) (b i) (omExtWt n j) ≠
      weylAction (isFiniteType_cartanD n) (b l) (omExtWt n j) := by
  intro i l hil h
  exact hil (hu_inj (by rw [hb i, hb l, h]))

omit [Field F] [Finite F] [CharP F 2] in
open CFSG.LieType.RootSystem CFSG.StandardType in
private theorem w135c2_omfPORep_orbit_hmove (hF : Nat.card F = 2) {n : ℕ} (hn : 4 ≤ n)
    {x : (coxeterMatrix (isFiniteType_cartanD n)).Group}
    {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ}
    (hxr : OmRealizes n x π s) (hπ : π ⟨n - 1, by omega⟩ = ⟨n - 1, by omega⟩)
    (hs1 : s ⟨n - 1, by omega⟩ = 1) {j : ℕ} (hj : j + 2 ≤ n)
    {b b' : Fin 4 → (coxeterMatrix (isFiniteType_cartanD n)).Group}
    {u : Fin 4 → Fin n → ℤ} (hu_last : ∀ i, toStdD n (u i) ⟨n - 1, by omega⟩ = 2)
    (hb : ∀ i, u i = weylAction (isFiniteType_cartanD n) (b i) (omExtWt n j))
    (hb' : ∀ i, ∀ γ, weylAction (isFiniteType_cartanD n) (b' i) γ =
      weylAction (isFiniteType_cartanD n) (b i) (γ ∘ omGraphSwap (by omega)) ∘
        omGraphSwap (by omega)) :
    ∀ i l, weylAction (isFiniteType_cartanD n) (b i) (omExtWt n j) ≠
      weylAction (isFiniteType_cartanD n) (x * b' l) (omExtWt n j) := by
  intro i l h
  have hlast1 : toStdD n (weylAction (isFiniteType_cartanD n) (b i) (omExtWt n j))
      ⟨n - 1, by omega⟩ = 2 := by
    rw [← hb i]
    exact hu_last i
  have hlast2 := w135c2_omfPORep_last_coord hF hn hxr hπ hs1 hj (hb' l)
    (by rw [← hb l]; exact hu_last l)
  rw [h] at hlast1
  rw [hlast2] at hlast1
  norm_num at hlast1

open CFSG.LieType.RootSystem CFSG.StandardType in
private theorem w135c2_omfPORep_orbit_bound
    (hF : Nat.card F = 2) {n : ℕ} (hn : 4 ≤ n) (hn3 : 3 ≤ n)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadPlus n F)) V} (hρ : IsSimpleRep ρ)
    {y₀ : V} {χ : spinGroup (quadPlus n F) → ZMod 2} {μ : Fin n → ZMod 2}
    (ht : (omPlusCurtisDatum n F hn3).IsCurtisType ρ y₀ χ μ)
    {x : (coxeterMatrix (isFiniteType_cartanD n)).Group}
    {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ}
    (hxr : OmRealizes n x π s) (hπ : π ⟨n - 1, by omega⟩ = ⟨n - 1, by omega⟩)
    (hs1 : s ⟨n - 1, by omega⟩ = 1)
    {j : ℕ} (hj1 : 1 ≤ j) (hj : j + 2 ≤ n)
    (hv : ∀ t : Fin n, μ t ≠ (omPlusCurtisDatum n F hn3).dScalar χ t →
      weylAction (isFiniteType_cartanD n)
        ((coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem.simple t) (omExtWt n j) =
        omExtWt n j)
    (T₁ : V ≃ₗ[ZMod 2] V)
    (hT1y0 : T₁ y₀ = ρ ((omPlusCurtisDatum n F hn3).nW x) y₀)
    (hT1int : ∀ (a : spinGroup (quadPlus n F)) (w : V),
      T₁ (ρ a w) = ρ ((omPlusCurtisDatum n F hn3).nW x *
        graphSpin n F ⟨n - 1, by omega⟩ a *
        ((omPlusCurtisDatum n F hn3).nW x)⁻¹) (T₁ w)) :
    4 ≤ Module.finrank (ZMod 2) (LinearMap.range (T₁.toLinearMap - 1)) := by
  have hn2 : 2 ≤ n := by omega
  let D := omPlusCurtisDatum n F hn3
  let cs := (coxeterMatrix (isFiniteType_cartanD n)).toCoxeterSystem
  let : MulAction (coxeterMatrix (isFiniteType_cartanD n)).Group (Fin n → ℤ) :=
    MulAction.compHom (Fin n → ℤ) (weylAction (isFiniteType_cartanD n))
  have hv' : ∀ t : Fin n, μ t ≠ D.dScalar χ t → cs.simple t • omExtWt n j = omExtWt n j :=
    fun t htne => by simpa [cs, MulAction.compHom_smul_def, Module.End.smul_def] using hv t htne
  obtain ⟨u, hu_mem, hu_inj, hu_last⟩ := exists_four_orbit_omExtWt_last hn hj1 hj
  choose b hb using fun i => hu_mem i
  choose b' hb' using fun i => exists_graphSpin_nW_omPlus (F := F) hF hn3 (b i)
  have hT1b : ∀ i, T₁.toLinearMap (ρ (D.nW (b i)) y₀) =
      (1 : ZMod 2) • ρ (D.nW (x * b' i)) y₀ :=
    fun i => w135c2_omfPORep_orbit_hT1b hF hn3 hT1y0 hT1int (hb' i).1
  have hinj := w135c2_omfPORep_orbit_hinj hu_inj hb
  have hmove := w135c2_omfPORep_orbit_hmove hF hn hxr hπ hs1 hj hu_last hb (fun i => (hb' i).2)
  have hinj' : ∀ i l, i ≠ l → b i • omExtWt n j ≠ b l • omExtWt n j := fun i l hil =>
    by simpa [MulAction.compHom_smul_def, Module.End.smul_def] using hinj i l hil
  have hmove' : ∀ i l, b i • omExtWt n j ≠ (x * b' l) • omExtWt n j := fun i l =>
    by simpa [MulAction.compHom_smul_def, Module.End.smul_def] using hmove i l
  exact le_finrank_range_sub_one_of_map_orbit (D := D) hρ ht hv' T₁.toLinearMap b
    (fun i => x * b' i) (fun _ => 1) hT1b hinj' hmove'

open CFSG.LieType.RootSystem CFSG.StandardType in
private theorem w135c2_omfPORep_four_le_of_separating
    (hF : Nat.card F = 2) {n : ℕ} (hn : 4 ≤ n) (hn3 : 3 ≤ n)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadPlus n F)) V} (hρ : IsSimpleRep ρ)
    {y₀ : V} {χ : spinGroup (quadPlus n F) → ZMod 2} {μ : Fin n → ZMod 2}
    (ht : (omPlusCurtisDatum n F hn3).IsCurtisType ρ y₀ χ μ) (hχ : χ 1 = 1)
    (hμeq : μ ⟨n - 2, by omega⟩ = μ ⟨n - 1, by omega⟩)
    {x : (coxeterMatrix (isFiniteType_cartanD n)).Group}
    {π : Equiv.Perm (Fin n)} {s : Fin n → ℤ}
    (hxr : OmRealizes n x π s) (hπ : π ⟨n - 1, by omega⟩ = ⟨n - 1, by omega⟩)
    (hs1 : s ⟨n - 1, by omega⟩ = 1) (T₁ : V ≃ₗ[ZMod 2] V)
    (hT1y0 : T₁ y₀ = ρ ((omPlusCurtisDatum n F hn3).nW x) y₀)
    (hT1int : ∀ a w, T₁ (ρ a w) = ρ ((omPlusCurtisDatum n F hn3).nW x *
      graphSpin n F ⟨n - 1, by omega⟩ a * ((omPlusCurtisDatum n F hn3).nW x)⁻¹) (T₁ w))
    (hsep : ∃ j : Fin n, j.val ≠ 0 ∧ μ j = 1) :
    4 ≤ Module.finrank (ZMod 2) (LinearMap.range (T₁.toLinearMap - 1)) := by
  obtain ⟨j, hj0, hj1⟩ := hsep
  have hj0' : 1 ≤ j.val := by have := j.isLt; omega
  by_cases hjle : j.val + 3 ≤ n
  · exact w135c2_omfPORep_orbit_bound (hF := hF) hn hn3 hρ ht hxr hπ hs1 hj0' (by omega)
      (w135c2_omfPORep_hv_inner (hF := hF) hn3 hχ hjle hj1) T₁ hT1y0 hT1int
  · have hjn2 : μ (⟨n - 2, by omega⟩ : Fin n) = 1 := by
      have hjval : j.val = n - 2 ∨ j.val = n - 1 := by have := j.isLt; omega
      rcases hjval with hh | hh
      · have hj' : j = ⟨n - 2, by omega⟩ := Fin.ext hh
        rwa [hj'] at hj1
      · have hj' : j = ⟨n - 1, by omega⟩ := Fin.ext hh
        rw [hμeq, ← hj']
        exact hj1
    exact w135c2_omfPORep_orbit_bound (hF := hF) hn hn3 hρ ht hxr hπ hs1
      (by omega : 1 ≤ n - 2) (by omega : (n - 2) + 2 ≤ n)
      (w135c2_omfPORep_hv_last (hF := hF) hn3 hχ hjn2 hμeq) T₁ hT1y0 hT1int

open CFSG.LieType.RootSystem CFSG.StandardType in
private theorem w135c2_omfPORep_main
    (hF : Nat.card F = 2) {n : ℕ} (hn : 4 ≤ n)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadPlus n F)) V} (hρ : IsSimpleRep ρ)
    (hρ1 : ∃ g, ρ g ≠ 1) (T : V ≃ₗ[ZMod 2] V) {h : spinGroup (quadPlus n F)}
    (hh : h * graphSpin n F ⟨n - 1, by omega⟩ h = 1)
    (hT : ∀ (g : spinGroup (quadPlus n F)) (v : V),
      T (ρ g v) = ρ (h * graphSpin n F ⟨n - 1, by omega⟩ g * h⁻¹) (T v)) :
    (∃ β : V ≃+ (Fin n ⊕ Fin n → F),
      ∀ (g : spinGroup (quadPlus n F)) (v : V), β (ρ g v) = spinAction (quadPlus n F) g (β v)) ∨
      4 ≤ Module.finrank (ZMod 2) (LinearMap.range (T.toLinearMap - 1)) := by
  have hn3 : 3 ≤ n := by omega
  have hFinite : Finite (coxeterMatrix (isFiniteType_cartanD n)).Group :=
    finite_group (isFiniteType_cartanD n)
  let D := omPlusCurtisDatum n F hn3
  have hsplit : SplitOver (ZMod 2) D.H := omPlusCurtisDatum_two_splitOver (k := ZMod 2) hF hn3
  obtain ⟨y₀, χ, μ, ht⟩ := D.exists_isCurtisType hsplit hρ
  have hχ : χ 1 = 1 := ht.chi_one
  obtain ⟨g, x, π, s, hs, hxr, hπ, hs1, hgn⟩ := exists_conj_graphSpin_eq_nW hn3 hh
  let L := w135c2_omfPORep_repEquiv ρ g
  let Nx := w135c2_omfPORep_repEquiv ρ (D.nW x)
  let T₁ : V ≃ₗ[ZMod 2] V := L * T * L⁻¹
  let T' : V ≃ₗ[ZMod 2] V := Nx.symm * T₁
  have hT1int := w135c2_omfPORep_conj_intertwine ρ (graphSpin n F ⟨n - 1, by omega⟩) T hgn hT
  have hT'int := w135c2_omfPORep_twist_intertwine ρ (graphSpin n F ⟨n - 1, by omega⟩) T₁ hT1int
  have hμeq : μ ⟨n - 2, by omega⟩ = μ ⟨n - 1, by omega⟩ :=
    mu_eq_of_twist_graphSpin hn3 hρ ht T' hT'int
  have hT'y0 := w135c2_omfPORep_fix_y0 hF hn3 hρ ht T' hT'int
  have hT1y0 := w135c2_omfPORep_T1_y0 ρ (D.nW x) T₁ T' rfl hT'y0
  have hfin := w135c2_omfPORep_finrank_conj_T1 L T T₁ rfl
  by_cases hsep : ∃ j : Fin n, j.val ≠ 0 ∧ μ j = 1
  · right
    have hb := w135c2_omfPORep_four_le_of_separating (hF := hF) hn hn3 hρ ht hχ hμeq hxr hπ hs1
      T₁ hT1y0 hT1int hsep
    rwa [← hfin]
  · left
    obtain ⟨g', hg'⟩ := hρ1
    exact omPlus_two_natural_of_not_separating hF hn3 hρ hg' ht hsep

theorem omPlus_two_outer_natural_or_four_le (hF : Nat.card F = 2) {n : ℕ} (hn : 4 ≤ n)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    {ρ : Representation (ZMod 2) (spinGroup (quadPlus n F)) V} (hρ : IsSimpleRep ρ)
    (hρ1 : ∃ g, ρ g ≠ 1) (T : V ≃ₗ[ZMod 2] V) {h : spinGroup (quadPlus n F)}
    (hh : h * graphSpin n F ⟨n - 1, by omega⟩ h = 1)
    (hT : ∀ (g : spinGroup (quadPlus n F)) (v : V),
      T (ρ g v) = ρ (h * graphSpin n F ⟨n - 1, by omega⟩ g * h⁻¹) (T v)) :
    (∃ β : V ≃+ (Fin n ⊕ Fin n → F),
      ∀ (g : spinGroup (quadPlus n F)) (v : V), β (ρ g v) = spinAction (quadPlus n F) g (β v)) ∨
      4 ≤ Module.finrank (ZMod 2) (LinearMap.range (T.toLinearMap - 1)) :=
  w135c2_omfPORep_main hF hn hρ hρ1 T hh hT

end CFSG.LocalAnalysis.WeakClosure81
