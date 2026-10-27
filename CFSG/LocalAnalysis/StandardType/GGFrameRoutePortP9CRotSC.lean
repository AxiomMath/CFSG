module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9CRotAux
import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs

public section

namespace CFSG.StandardType.FrameRoute

variable {K : Type} [Field K] [Algebra (ZMod 2) K] [Finite K] {V0 : Type} [AddCommGroup V0]
  [Module (ZMod 2) V0] {t : ℕ}

@[expose] noncomputable def P9rotRange (K : Type) [Field K] [Algebra (ZMod 2) K]
    (V0 : Type) [AddCommGroup V0] [Module (ZMod 2) V0] (t : ℕ) :
    Subgroup ((V0 × (Fin t → K)) ≃ₗ[ZMod 2] (V0 × (Fin t → K))) :=
  (P9rotHom (K := K) (V0 := V0) (t := t)).range

private lemma P9_linearEquiv_eq_one_of_finrank_le_one
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Module.Finite (ZMod 2) V]
    (h : Module.finrank (ZMod 2) V ≤ 1) (g : V ≃ₗ[ZMod 2] V) : g = 1 := by
  by_cases hsub : Subsingleton V
  · haveI : Subsingleton V := hsub
    apply LinearEquiv.ext
    intro w
    change g w = w
    exact Subsingleton.elim _ _
  · obtain ⟨v, hv⟩ := (finrank_le_one_iff (K := ZMod 2) (V := V)).mp h
    have hv0 : v ≠ 0 := by
      intro h0
      apply hsub
      refine ⟨fun a b => ?_⟩
      obtain ⟨c, hc⟩ := hv a
      obtain ⟨d, hd⟩ := hv b
      rw [h0, smul_zero] at hc hd
      exact hc.symm.trans hd
    apply LinearEquiv.ext
    intro w
    change g w = w
    obtain ⟨c, hc⟩ := hv w
    obtain ⟨c', hc'⟩ := hv (g v)
    have hgv_ne : g v ≠ 0 := by
      intro hzero
      exact hv0 (g.injective (hzero.trans (map_zero g).symm))
    have hc'ne : c' ≠ 0 := by
      intro h0
      apply hgv_ne
      rw [← hc', h0, zero_smul]
    have hc'1 : c' = 1 := by
      have h01 : ∀ c : ZMod 2, c ≠ 0 → c = 1 := by decide
      exact h01 c' hc'ne
    calc g w = g (c • v) := by rw [hc]
      _ = c • g v := map_smul g c v
      _ = c • v := by rw [← hc', hc'1, one_smul]
      _ = w := hc

theorem P9_rotRange_eq_of_sc (hK : Nat.card K = 4)
    (S : Subgroup ((V0 × (Fin t → K)) ≃ₗ[ZMod 2] (V0 × (Fin t → K))))
    (hS : S ≤ P9rotRange K V0 t)
    (hsc : ∀ g : (V0 × (Fin t → K)) ≃ₗ[ZMod 2] (V0 × (Fin t → K)),
      (∀ s ∈ S, g * s = s * g) → g ^ 3 = 1 → g ∈ S) :
    S = P9rotRange K V0 t := by
  refine le_antisymm hS ?_
  intro x hx
  change x ∈ (P9rotHom (K := K) (V0 := V0) (t := t)).range at hx
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hx
  have hcomm : ∀ s ∈ S, x * s = s * x := by
    intro s hs
    have hs' : s ∈ P9rotRange K V0 t := hS hs
    change s ∈ (P9rotHom (K := K) (V0 := V0) (t := t)).range at hs'
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hs'
    rw [← hb, ← ha]
    exact P9rot_comm a b
  have hx3 : x ^ 3 = 1 := by
    rw [← ha]
    exact P9rot_pow_three hK a
  exact hsc x hcomm hx3

theorem P9_finrank_le_one_of_sc (hK : Nat.card K = 4) [Module.Finite (ZMod 2) V0]
    (S : Subgroup ((V0 × (Fin t → K)) ≃ₗ[ZMod 2] (V0 × (Fin t → K))))
    (hS : S ≤ P9rotRange K V0 t)
    (hsc : ∀ g : (V0 × (Fin t → K)) ≃ₗ[ZMod 2] (V0 × (Fin t → K)),
      (∀ s ∈ S, g * s = s * g) → g ^ 3 = 1 → g ∈ S) :
    Module.finrank (ZMod 2) V0 ≤ 1 := by
  by_contra hlt
  have h2 : 2 ≤ Module.finrank (ZMod 2) V0 := by omega
  obtain ⟨g0, hg0pow, hg0ne⟩ := P9_exists_order_three h2
  let g : (V0 × (Fin t → K)) ≃ₗ[ZMod 2] (V0 × (Fin t → K)) :=
    g0.prodCongr (LinearEquiv.refl (ZMod 2) (Fin t → K))
  have hg_apply : ∀ x : V0 × (Fin t → K), g x = (g0 x.1, x.2) := by
    intro x
    change (g0.prodCongr (LinearEquiv.refl (ZMod 2) (Fin t → K))) x = (g0 x.1, x.2)
    rw [LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
  have hcomm : ∀ a : Fin t → Kˣ, g * P9rot a = P9rot a * g := by
    intro a
    apply LinearEquiv.ext
    intro v
    simp [LinearEquiv.mul_apply, hg_apply, P9rot_apply]
  have hg3 : g ^ 3 = 1 := by
    rw [pow_three']
    apply LinearEquiv.ext
    intro v
    change g (g (g v)) = v
    rw [show g v = (g0 v.1, v.2) from hg_apply v,
      show g (g0 v.1, v.2) = (g0 (g0 v.1), v.2) from hg_apply _,
      show g (g0 (g0 v.1), v.2) = (g0 (g0 (g0 v.1)), v.2) from hg_apply _]
    have hg0v : g0 (g0 (g0 v.1)) = v.1 := by
      have h := congrArg (fun e : V0 ≃ₗ[ZMod 2] V0 => e v.1) hg0pow
      rw [pow_three', LinearEquiv.mul_apply, LinearEquiv.mul_apply,
        LinearEquiv.one_eq_refl, LinearEquiv.refl_apply] at h
      exact h
    rw [hg0v]
  have hcommS : ∀ s ∈ S, g * s = s * g := by
    intro s hs
    have hs' : s ∈ P9rotRange K V0 t := hS hs
    change s ∈ (P9rotHom (K := K) (V0 := V0) (t := t)).range at hs'
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hs'
    rw [← hb]
    exact hcomm b
  have hgS : g ∈ S := hsc g hcommS hg3
  have hgRange : g ∈ P9rotRange K V0 t := hS hgS
  change g ∈ (P9rotHom (K := K) (V0 := V0) (t := t)).range at hgRange
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp hgRange
  have hg0eq : g0 = 1 := by
    apply LinearEquiv.ext
    intro v0
    change g0 v0 = v0
    have h : P9rot a (v0, 0) = g (v0, 0) := congrArg
      (fun e : (V0 × (Fin t → K)) ≃ₗ[ZMod 2] (V0 × (Fin t → K)) => e (v0, 0)) ha
    rw [P9rot_apply_inl a v0, hg_apply] at h
    exact (Prod.ext_iff.mp h).1.symm
  exact hg0ne hg0eq

theorem P9_centralizer_le_of_sc (hK : Nat.card K = 4) [Module.Finite (ZMod 2) V0]
    (S : Subgroup ((V0 × (Fin t → K)) ≃ₗ[ZMod 2] (V0 × (Fin t → K))))
    (hS : S ≤ P9rotRange K V0 t)
    (hsc : ∀ g : (V0 × (Fin t → K)) ≃ₗ[ZMod 2] (V0 × (Fin t → K)),
      (∀ s ∈ S, g * s = s * g) → g ^ 3 = 1 → g ∈ S)
    (g : (V0 × (Fin t → K)) ≃ₗ[ZMod 2] (V0 × (Fin t → K)))
    (hg : ∀ s ∈ S, g * s = s * g) : g ∈ S := by
  have heq : S = P9rotRange K V0 t := P9_rotRange_eq_of_sc hK S hS hsc
  have hcomm : ∀ a : Fin t → Kˣ, g * P9rot a = P9rot a * g := by
    intro a
    refine hg (P9rot a) ?_
    rw [heq]
    change P9rot a ∈ (P9rotHom (K := K) (V0 := V0) (t := t)).range
    exact MonoidHom.mem_range.mpr ⟨a, rfl⟩
  obtain ⟨g0, u, hu⟩ := P9_centralizer_rot hK g hcomm
  have hfr : Module.finrank (ZMod 2) V0 ≤ 1 := P9_finrank_le_one_of_sc hK S hS hsc
  have hg0 : g0 = 1 := P9_linearEquiv_eq_one_of_finrank_le_one hfr g0
  have hgu : g = P9rot u := by
    apply LinearEquiv.ext
    intro v
    rw [hu v, P9rot_apply]
    simp [hg0]
  rw [heq, hgu]
  change P9rot u ∈ (P9rotHom (K := K) (V0 := V0) (t := t)).range
  exact MonoidHom.mem_range.mpr ⟨u, rfl⟩

theorem P9_finrank_model (hK : Nat.card K = 4) [Module.Finite (ZMod 2) V0] :
    Module.finrank (ZMod 2) (V0 × (Fin t → K)) = Module.finrank (ZMod 2) V0 + 2 * t := by
  have hfin : Module.finrank (ZMod 2) K = 2 := by
    have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := K)
    rw [hK, Nat.card_zmod] at hcard
    have hpow : 2 ^ Module.finrank (ZMod 2) K = 2 ^ 2 := by
      rw [← hcard]
      norm_num
    exact Nat.pow_right_injective (le_refl 2) hpow
  rw [Module.finrank_prod, Module.finrank_pi_fintype, hfin]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [Nat.mul_comm]

end CFSG.StandardType.FrameRoute
