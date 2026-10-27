module

import Mathlib.Data.ZMod.Defs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.E7RootSetStab
public import CFSG.LieType.Chevalley.KernelComponentRoots
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP13Roots

import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP13Refl
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.E7RootSetRootsAux
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.E7RootSetLiftAux
import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalRoots
import CFSG.Mathlib.Decide.Bounded

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute

open Certificates.OmegaSevenMax
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.OddStandard.SmallF3.Omega.E7RootSet

private theorem p13wAux_bilin_ne_zero {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (B : LinearMap.BilinForm (ZMod 3) V) (hB : B.Nondegenerate) {u : V} (hu : u ≠ 0) :
    B u ≠ 0 := by
  intro h
  apply hu
  apply hB.1 u
  intro y
  rw [h]
  simp

private theorem p13wAux_ne_zero_of_bilin_self {V : Type*} [AddCommGroup V]
    [Module (ZMod 3) V] (B : LinearMap.BilinForm (ZMod 3) V) {v : V} (hv : B v v ≠ 0) :
    v ≠ 0 := by
  intro h
  apply hv
  rw [h]
  simp

private theorem p13wAux_finrank_ker {F : Type*} [Field F] {V : Type*} [AddCommGroup V]
    [Module F V] [FiniteDimensional F V] (f : V →ₗ[F] F) (hf : f ≠ 0) :
    Module.finrank F (LinearMap.ker f) + 1 = Module.finrank F V := by
  have htop : LinearMap.range f = ⊤ := Module.Dual.range_eq_top_of_ne_zero hf
  have h := LinearMap.finrank_range_add_finrank_ker f
  rw [htop, _root_.finrank_top, Module.finrank_self] at h
  omega

private theorem p13wAux_ker_eq_of_le {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] (B : LinearMap.BilinForm (ZMod 3) V)
    (hB : B.Nondegenerate) {ψ v : V} (hψ : ψ ≠ 0) (hv : B v v ≠ 0)
    (hle : ∀ x, B ψ x = 0 → B v x = 0) :
    LinearMap.ker (B ψ) = LinearMap.ker (B v) := by
  have hBψ : B ψ ≠ 0 := p13wAux_bilin_ne_zero B hB hψ
  have hBv : B v ≠ 0 :=
    p13wAux_bilin_ne_zero B hB (p13wAux_ne_zero_of_bilin_self B hv)
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · intro x hx
    exact hle x (LinearMap.mem_ker.mp hx)
  · have h1 := p13wAux_finrank_ker (B ψ) hBψ
    have h2 := p13wAux_finrank_ker (B v) hBv
    omega

private theorem p13wAux_smul_of_ker_eq {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (B : LinearMap.BilinForm (ZMod 3) V) (hB : B.Nondegenerate)
    (hsymm : ∀ x y, B x y = B y x) {ψ v : V} (hv : B v v ≠ 0)
    (hker : LinearMap.ker (B ψ) = LinearMap.ker (B v)) :
    ∃ c : ZMod 3, c ≠ 0 ∧ ψ = c • v := by
  have hv0 : v ≠ 0 := p13wAux_ne_zero_of_bilin_self B hv
  have hBv : B v ≠ 0 := p13wAux_bilin_ne_zero B hB hv0
  obtain ⟨y, hvy⟩ : ∃ y, B v y ≠ 0 := by
    by_contra h
    apply hBv
    ext z
    by_contra hz
    exact h ⟨z, hz⟩
  have hBψy : B ψ y ≠ 0 := by
    intro h0
    apply hvy
    have hmem : y ∈ LinearMap.ker (B v) := by
      rw [← hker]
      exact LinearMap.mem_ker.mpr h0
    exact LinearMap.mem_ker.mp hmem
  have hsmul : B ψ = (B ψ y / B v y) • B v := by
    ext z
    have hz : B v (z - (B v z / B v y) • y) = 0 := by
      rw [map_sub, map_smul, smul_eq_mul, _root_.div_mul_cancel₀ (B v z) hvy]
      exact _root_.sub_self _
    have hzψ : B ψ (z - (B v z / B v y) • y) = 0 := by
      have hmem : z - (B v z / B v y) • y ∈ LinearMap.ker (B v) :=
        LinearMap.mem_ker.mpr hz
      rw [← hker] at hmem
      exact LinearMap.mem_ker.mp hmem
    have hzψ' : B ψ z = (B v z / B v y) * B ψ y := by
      have h := hzψ
      rw [map_sub, map_smul, smul_eq_mul] at h
      exact _root_.sub_eq_zero.mp h
    have hexp : B ψ z = (B ψ y / B v y) * B v z := by
      rw [hzψ', div_mul_eq_mul_div, div_mul_eq_mul_div, mul_comm (B v z) (B ψ y)]
    rw [LinearMap.smul_apply, smul_eq_mul]
    exact hexp
  refine ⟨B ψ y / B v y, div_ne_zero hBψy hvy, ?_⟩
  have hzero : ∀ x : V, B x (ψ - (B ψ y / B v y) • v) = 0 := by
    intro x
    have hx := congrArg (fun f => f x) hsmul
    simp only [LinearMap.smul_apply, smul_eq_mul] at hx
    rw [map_sub, map_smul, smul_eq_mul, hsymm x ψ, hsymm x v, hx]
    exact _root_.sub_self _
  exact sub_eq_zero.mp (hB.2 (ψ - (B ψ y / B v y) • v) hzero)

private theorem p13wAux_smul_of_le {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] (B : LinearMap.BilinForm (ZMod 3) V)
    (hB : B.Nondegenerate) (hsymm : ∀ x y, B x y = B y x) {ψ v : V} (hψ : ψ ≠ 0)
    (hv : B v v ≠ 0) (hle : ∀ x, B ψ x = 0 → B v x = 0) :
    ∃ c : ZMod 3, c ≠ 0 ∧ ψ = c • v :=
  p13wAux_smul_of_ker_eq B hB hsymm hv (p13wAux_ker_eq_of_le B hB hψ hv hle)

private theorem p13wAux_pm_one (c : ZMod 3) (hc : c ≠ 0) : c = 1 ∨ c = -1 := by
  revert c
  decide +kernel

private theorem p13wAux_smul_single_eq_single {c : ZMod 3} {m n : Fin 6} (hc : c ≠ 0)
    (h : c • (Pi.single m (1 : ZMod 3) : Fin 6 → ZMod 3) =
      (Pi.single n (1 : ZMod 3) : Fin 6 → ZMod 3)) :
    m = n ∧ c = 1 := by
  have hm : (c • (Pi.single m (1 : ZMod 3) : Fin 6 → ZMod 3)) m ≠ 0 := by
    rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    exact hc
  have hmn : m = n := by
    by_contra hne
    rw [h] at hm
    have hz : (Pi.single n (1 : ZMod 3) : Fin 6 → ZMod 3) m = 0 :=
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) hne 1
    rw [hz] at hm
    exact hm rfl
  subst hmn
  have h' := congrFun h m
  simpa using h'

private theorem p13wAux_smul_single_eq_neg_single {c : ZMod 3} {m n : Fin 6} (hc : c ≠ 0)
    (h : c • (Pi.single m (1 : ZMod 3) : Fin 6 → ZMod 3) =
      -(Pi.single n (1 : ZMod 3) : Fin 6 → ZMod 3)) :
    m = n ∧ c = -1 := by
  have hm : (c • (Pi.single m (1 : ZMod 3) : Fin 6 → ZMod 3)) m ≠ 0 := by
    rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    exact hc
  have hmn : m = n := by
    by_contra hne
    rw [h] at hm
    have hz : (Pi.single n (1 : ZMod 3) : Fin 6 → ZMod 3) m = 0 :=
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) hne 1
    rw [Pi.neg_apply, hz] at hm
    exact hm _root_.neg_zero
  subst hmn
  have h' := congrFun h m
  simpa using h'

private theorem p13wAux_d6_apply_single {σ : Equiv.Perm (Fin 6)} {ε : Fin 6 → ZMod 3}
    {w : (Fin 6 → ZMod 3) → (Fin 6 → ZMod 3)}
    (hw_eq : ∀ x i, w x (σ i) = ε i * x i) (k : Fin 6) :
    w (Pi.single k (1 : ZMod 3)) = ε k • (Pi.single (σ k) (1 : ZMod 3) : Fin 6 → ZMod 3) := by
  funext j
  by_cases hj : j = σ k
  · subst hj
    rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, hw_eq,
      Pi.single_eq_same, mul_one]
  · have hsym : σ.symm j ≠ k := fun h => hj (by rw [← h, Equiv.apply_symm_apply])
    have h1 : w (Pi.single k (1 : ZMod 3)) j =
        ε (σ.symm j) * (Pi.single k (1 : ZMod 3) : Fin 6 → ZMod 3) (σ.symm j) := by
      have := hw_eq (Pi.single k (1 : ZMod 3)) (σ.symm j)
      rwa [Equiv.apply_symm_apply] at this
    rw [h1, Pi.single_eq_of_ne hsym, mul_zero, Pi.smul_apply, Pi.single_eq_of_ne hj,
      smul_zero]

private theorem p13wAux_d6_sign_change_even
    {w : (Fin 6 → ZMod 3) → (Fin 6 → ZMod 3)}
    {σ : Equiv.Perm (Fin 6)} {ε : Fin 6 → ZMod 3}
    (hε : ∀ k, ε k = 1 ∨ ε k = -1) (hprod : ∏ k, ε k = 1)
    (hw_eq : ∀ x i, w x (σ i) = ε i * x i)
    {i : Fin 6} (hsign : ∀ x, w x = fun j => if j = i then - x j else x j) : False := by
  have hε0 : ∀ k, ε k ≠ 0 := by
    intro k hk
    rcases hε k with h | h
    · rw [h] at hk
      exact (by decide : (1 : ZMod 3) ≠ 0) hk
    · rw [h] at hk
      exact (by decide : (-1 : ZMod 3) ≠ 0) hk
  have hneg : w (Pi.single i (1 : ZMod 3)) =
      -(Pi.single i (1 : ZMod 3) : Fin 6 → ZMod 3) := by
    rw [hsign]
    funext j
    by_cases hj : j = i
    · simp [hj]
    · simp [hj]
  have hone : ∀ k, k ≠ i → w (Pi.single k (1 : ZMod 3)) =
      (Pi.single k (1 : ZMod 3) : Fin 6 → ZMod 3) := by
    intro k hk
    rw [hsign]
    funext j
    by_cases hj : j = i
    · have hik : i ≠ k := fun h => hk h.symm
      simp [hj, hik]
    · simp [hj]
  have hσ : ∀ k, σ k = k := by
    intro k
    by_cases hk : k = i
    · rw [hk]
      have hwk := p13wAux_d6_apply_single hw_eq k
      rw [hk, hneg] at hwk
      exact (p13wAux_smul_single_eq_neg_single (hε0 i) hwk.symm).1
    · have hwk := p13wAux_d6_apply_single hw_eq k
      rw [hone k hk] at hwk
      exact (p13wAux_smul_single_eq_single (hε0 k) hwk.symm).1
  have hεi : ε i = -1 := by
    have hwk := p13wAux_d6_apply_single hw_eq i
    rw [hσ i, hneg] at hwk
    exact (p13wAux_smul_single_eq_neg_single (hε0 i) hwk.symm).2
  have hεone : ∀ k, k ≠ i → ε k = 1 := by
    intro k hk
    have hwk := p13wAux_d6_apply_single hw_eq k
    rw [hσ k, hone k hk] at hwk
    exact (p13wAux_smul_single_eq_single (hε0 k) hwk.symm).2
  have hprod' : ∏ k, ε k = -1 := by
    rw [Fintype.prod_eq_mul_prod_compl i ε, hεi]
    have hcomp : ∏ k ∈ ({i}ᶜ : Finset (Fin 6)), ε k = 1 := by
      apply Finset.prod_eq_one
      intro k hk
      rw [Finset.mem_compl, Finset.mem_singleton] at hk
      exact hεone k hk
    rw [hcomp, mul_one]
  rw [hprod'] at hprod
  exact (by decide : (-1 : ZMod 3) ≠ 1) hprod

private noncomputable def p13wAux_e7B : LinearMap.BilinForm (ZMod 3) V :=
  QuadraticMap.polarBilin qForm

private theorem p13wAux_e7B_apply (x y : V) : p13wAux_e7B x y = polarV x y := by
  rw [p13wAux_e7B, QuadraticMap.polarBilin_apply_apply, polar_qForm]

private def p13wAux_e7Codes : List ℕ :=
  CFSG.StandardType.e7RootsP1_certVecs.map fun v => encV (redV v)

open scoped CFSG.Decide.Bounded in
private theorem p13wAux_E7_finite :
    ∀ c ∈ List.range 2187,
      polarV (decV c) (decV c) ≠ 0 →
      (∀ j : Fin 7,
        encV ((Pi.single j (1 : ZMod 3) : V) -
          (2 * polarV (Pi.single j (1 : ZMod 3)) (decV c) /
            polarV (decV c) (decV c)) • decV c) ∈ p13wAux_e7Codes) →
      encV (decV c) ∈ p13wAux_e7Codes := by
  decide +kernel

private theorem p13wAux_redV_single :
    ∀ j : Fin 7, redV (Pi.single j (1 : ℤ) : Fin Tag.E7.rank → ℤ) =
      (Pi.single j (1 : ZMod 3) : V) := by
  decide +kernel

private theorem p13wAux_e7_mem_codes
    (x : V) :
    x ∈ rootSet ↔ encV x ∈ p13wAux_e7Codes := by
  constructor
  · intro hx
    have hx' : x ∈ (↑rootSet : Set V) := by simpa using hx
    rw [rootSet_eq_image] at hx'
    obtain ⟨α, hα, rfl⟩ := hx'
    exact List.mem_map.mpr ⟨α, (CFSG.StandardType.e7RootsP1_isRoot_iff α).mp hα, rfl⟩
  · intro hx
    obtain ⟨α, hα, hαx⟩ := List.mem_map.mp hx
    have hred : redV α = x := by
      have := congrArg decV hαx
      simpa [decV_encV] using this
    have hroot : redV α ∈ rootSet := by
      rw [mem_rootSet_iff]
      exact ⟨α, (CFSG.StandardType.e7RootsP1_isRoot_iff α).mpr hα, rfl⟩
    rwa [hred] at hroot

theorem p13a3_E7_pointwise_stabilizer
    (ψ : V) (hψ : ψ ≠ 0) (w : WeylGroup Tag.E7)
    (hw : ∀ x : V, polarV ψ x = 0 → rhoEquiv w x = x) :
    w = 1 ∨ ∃ β, IsRoot Tag.E7 β ∧ (redV β = ψ ∨ redV β = -ψ) ∧ w = rootReflection β := by
  classical
  have hB : p13wAux_e7B.Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mpr e7QForm_nondegenerate
  have hBsymm : p13wAux_e7B.IsSymm := QuadraticMap.isSymm_polarBilin qForm
  have hsymm : ∀ x y : V, p13wAux_e7B x y = p13wAux_e7B y x := fun x y => hBsymm.eq x y
  have hBapply : ∀ x y : V, p13wAux_e7B x y = polarV x y := p13wAux_e7B_apply
  have hpolar_comm : ∀ x y : V, polarV x y = polarV y x := by
    intro x y
    rw [← polar_qForm x y, ← polar_qForm y x]
    exact QuadraticMap.polar_comm (⇑qForm) x y
  have horth : ∀ z : V, qForm (rhoEquiv w z) = qForm z := by
    have hmem := rhoEquiv_mem (w := w)
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff] at hmem
    exact hmem
  have hg : ∀ x y : V, p13wAux_e7B (rhoEquiv w x) (rhoEquiv w y) = p13wAux_e7B x y := by
    intro x y
    rw [hBapply, hBapply, ← polar_qForm, ← polar_qForm]
    rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add, horth, horth, horth]
  have hfixH : ∀ x ∈ LinearMap.ker (p13wAux_e7B ψ), rhoEquiv w x = x := by
    intro x hx
    have hx' : p13wAux_e7B ψ x = 0 := LinearMap.mem_ker.mp hx
    rw [hBapply] at hx'
    exact hw x hx'
  have hBψ : p13wAux_e7B ψ ≠ 0 := p13wAux_bilin_ne_zero p13wAux_e7B hB hψ
  have hH : Module.finrank (ZMod 3) (LinearMap.ker (p13wAux_e7B ψ)) + 1 =
      Module.finrank (ZMod 3) V :=
    p13wAux_finrank_ker (p13wAux_e7B ψ) hBψ
  rcases P13a1_hyperplane_fixer (F := ZMod 3) (by decide : (2 : ZMod 3) ≠ 0)
      p13wAux_e7B hB hBsymm (rhoEquiv w) hg (LinearMap.ker (p13wAux_e7B ψ)) hH hfixH with
    hrefl | ⟨v, hv, hform⟩
  · left
    apply rho_injective
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    obtain ⟨y, rfl⟩ := redV_surj x
    rw [rho_apply_redV, rho_apply_redV]
    have h := congrArg (fun e : V ≃ₗ[ZMod 3] V => e (redV y)) hrefl
    rw [rhoEquiv_redV] at h
    simpa using h
  · right
    have hform' : ∀ x : V, rhoEquiv w x =
        x - (2 * polarV x v / polarV v v) • v := by
      intro x
      rw [hform x, hBapply x v, hBapply v v]
    have hpolarvv : polarV v v ≠ 0 := by
      intro h
      exact hv (by rw [hBapply]; exact h)
    have hsimple : ∀ j : Fin 7, (Pi.single j (1 : ZMod 3) : V) ∈ rootSet := by
      intro j
      rw [mem_rootSet_iff]
      exact ⟨(Pi.single j (1 : ℤ) : Fin Tag.E7.rank → ℤ), IsRoot.basis (τ := Tag.E7) j,
        p13wAux_redV_single j⟩
    have hmem_image : ∀ j : Fin 7,
        rhoEquiv w (Pi.single j (1 : ZMod 3)) ∈ rootSet := by
      intro j
      rw [← rho_image_rootSet w]
      exact Finset.mem_image.mpr ⟨_, hsimple j, rfl⟩
    have hcode : ∀ j : Fin 7,
        encV ((Pi.single j (1 : ZMod 3) : V) -
          (2 * polarV (Pi.single j (1 : ZMod 3)) v / polarV v v) • v) ∈
          p13wAux_e7Codes := by
      intro j
      rw [← p13wAux_e7_mem_codes]
      rw [← hform' (Pi.single j (1 : ZMod 3))]
      exact hmem_image j
    have hvcodes : encV v ∈ p13wAux_e7Codes := by
      have hmain := p13wAux_E7_finite (encV v) (List.mem_range.mpr (encV_lt v)) ?_ ?_
      · simpa [decV_encV] using hmain
      · rw [decV_encV]
        exact hpolarvv
      · intro j
        simpa [decV_encV] using hcode j
    have hvroot : v ∈ rootSet := (p13wAux_e7_mem_codes v).mpr hvcodes
    obtain ⟨β, hβ, hβv⟩ := mem_rootSet_iff.mp hvroot
    have hle : ∀ x : V, p13wAux_e7B ψ x = 0 → p13wAux_e7B v x = 0 := by
      intro x hx
      have hxfix : rhoEquiv w x = x := hfixH x hx
      rw [hform' x] at hxfix
      have hzero : (2 * polarV x v / polarV v v) • v = 0 := sub_eq_self.mp hxfix
      have hcoef : 2 * polarV x v / polarV v v = 0 := by
        rcases smul_eq_zero.mp hzero with h | h
        · exact h
        · exact absurd h (p13wAux_ne_zero_of_bilin_self p13wAux_e7B hv)
      have h2 : 2 * polarV x v = 0 := by
        rcases div_eq_zero_iff.mp hcoef with h | h
        · exact h
        · exact absurd h hpolarvv
      have hxv : polarV x v = 0 := by
        rcases mul_eq_zero.mp h2 with h | h
        · exact absurd h (by decide : (2 : ZMod 3) ≠ 0)
        · exact h
      rw [hBapply, hpolar_comm]
      exact hxv
    obtain ⟨c, hc, hψcv⟩ :=
      p13wAux_smul_of_le p13wAux_e7B hB hsymm hψ hv hle
    have hβsign : redV β = ψ ∨ redV β = -ψ := by
      rcases p13wAux_pm_one c hc with hc1 | hcneg
      · left
        rw [hβv, hψcv, hc1, one_smul]
      · right
        rw [hβv, hψcv, hcneg]
        simp
    have hbb : CFSG.LieType.Steinberg.Adjoint.iform β β = 2 :=
      CFSG.LieType.Chevalley.EvenOddRadical.iform_self_eq_two
        (Or.inr (Or.inr (Or.inl rfl))) hβ
    have hscalar : ∀ y : Fin Tag.E7.rank → ℤ,
        ((corootPair β y : ℤ) : ZMod 3) =
          2 * polarV (redV y) (redV β) / polarV (redV β) (redV β) := by
      intro y
      have hcor : corootPair β y = CFSG.LieType.Steinberg.Adjoint.iform β y := by
        rw [corootPair, hbb]
        exact Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)
      have hp1 : polarV (redV y) (redV β) =
          ((CFSG.LieType.Steinberg.Adjoint.iform y β : ℤ) : ZMod 3) := by
        rw [← polar_qForm, CFSG.StandardType.e7LiftP11_polarV_redV]
      have hp2 : polarV (redV β) (redV β) = (2 : ZMod 3) := by
        rw [← polar_qForm, CFSG.StandardType.e7LiftP11_polarV_redV, hbb]
        norm_num
      rw [hcor, hp1, hp2, CFSG.LieType.Steinberg.Adjoint.iform_comm β y]
      rw [mul_comm (2 : ZMod 3)
          ((CFSG.LieType.Steinberg.Adjoint.iform y β : ℤ) : ZMod 3),
        mul_div_cancel_right₀ _ (by decide : (2 : ZMod 3) ≠ 0)]
    have hformβ : ∀ x : V, rhoEquiv w x =
        x - (2 * polarV x (redV β) / polarV (redV β) (redV β)) • redV β := by
      intro x
      rw [hform' x, ← hβv]
    have hbase : ∀ y : Fin Tag.E7.rank → ℤ,
        rhoEquiv (rootReflection β) (redV y) = rhoEquiv w (redV y) := by
      intro y
      calc rhoEquiv (rootReflection β) (redV y)
          = redV (rootReflection β • y) := rhoEquiv_redV _ _
        _ = redV (y - corootPair β y • β) := by rw [rootReflection_smul hβ]
        _ = redV y - ((corootPair β y : ℤ) : ZMod 3) • redV β := by
              rw [redV_sub, redV_zsmul]
        _ = redV y - (2 * polarV (redV y) (redV β) /
              polarV (redV β) (redV β)) • redV β := by rw [hscalar]
        _ = rhoEquiv w (redV y) := (hformβ (redV y)).symm
    have hrooteq : rhoEquiv (rootReflection β) = rhoEquiv w := by
      apply LinearEquiv.ext
      intro x
      obtain ⟨y, rfl⟩ := redV_surj x
      exact hbase y
    refine ⟨β, hβ, hβsign, ?_⟩
    have hrmem : (rho (rootReflection β) :
        CFSG.OddStandard.SmallF3.Omega.OGroup qForm) = rho w := by
      apply Subtype.ext
      apply LinearEquiv.ext
      intro x
      obtain ⟨y, rfl⟩ := redV_surj x
      rw [rho_apply_redV, rho_apply_redV]
      have h := congrArg (fun e : V ≃ₗ[ZMod 3] V => e (redV y)) hrooteq
      rw [rhoEquiv_redV, rhoEquiv_redV] at h
      simpa using h
    exact (rho_injective hrmem).symm

@[expose] def D6EvenSignedPerm (w : (Fin 6 → ZMod 3) → (Fin 6 → ZMod 3)) : Prop :=
  ∃ (σ : Equiv.Perm (Fin 6)) (ε : Fin 6 → ZMod 3), (∀ i, ε i = 1 ∨ ε i = -1) ∧ (∏ i, ε i = 1) ∧
    ∀ x i, w x (σ i) = ε i * x i

private def p13wAux_dotB : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3) :=
  LinearMap.mk₂ (ZMod 3) (fun x y => ∑ i, x i * y i)
    (by intro x y z; simp [add_mul, Finset.sum_add_distrib])
    (by
      intro c x y
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)
    (by intro x y z; simp [mul_add, Finset.sum_add_distrib])
    (by
      intro c x y
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring)

private theorem p13wAux_dotB_apply (x y : Fin 6 → ZMod 3) :
    p13wAux_dotB x y = ∑ i, x i * y i := by
  rw [p13wAux_dotB, LinearMap.mk₂_apply]

private theorem p13wAux_dotB_symm (x y : Fin 6 → ZMod 3) :
    p13wAux_dotB x y = p13wAux_dotB y x := by
  rw [p13wAux_dotB_apply, p13wAux_dotB_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

private theorem p13wAux_dotB_nondegenerate : p13wAux_dotB.Nondegenerate := by
  constructor
  · intro x hx
    funext j
    have h := hx (Pi.single j (1 : ZMod 3))
    rw [p13wAux_dotB_apply, Finset.sum_eq_single j] at h
    · simpa using h
    · intro k _ hk
      simp [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hk]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  · intro y hy
    funext j
    have h := hy (Pi.single j (1 : ZMod 3))
    rw [p13wAux_dotB_apply, Finset.sum_eq_single j] at h
    · simpa using h
    · intro k _ hk
      simp [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hk]
    · intro hj
      exact absurd (Finset.mem_univ j) hj

private def p13wAux_lift (v : Fin 6 → ZMod 3) : Fin 6 → ℤ :=
  fun i => if v i = 0 then 0 else if v i = 1 then 1 else -1

private theorem p13wAux_D6_finite_aux :
    ∀ v : Fin 6 → ZMod 3, (∑ i : Fin 6, v i * v i) ≠ 0 →
      (∀ k : Fin 6, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∃ m : Fin 6, ∀ i : Fin 6,
        (Pi.single k (1 : ZMod 3) : Fin 6 → ZMod 3) i -
          (2 * (∑ j : Fin 6, v j *
            (Pi.single k (1 : ZMod 3) : Fin 6 → ZMod 3) j) /
            (∑ j : Fin 6, v j * v j)) * v i =
          ε * (Pi.single m (1 : ZMod 3) : Fin 6 → ZMod 3) i) →
      (∃ i : Fin 6, v = (Pi.single i (1 : ZMod 3) : Fin 6 → ZMod 3) ∨
        v = -(Pi.single i (1 : ZMod 3) : Fin 6 → ZMod 3)) ∨
        ((∑ i : Fin 6, |p13wAux_lift v i| = 2) ∧
          (∀ i : Fin 6, |p13wAux_lift v i| ≤ 1) ∧
          ∀ i, ((p13wAux_lift v i : ℤ) : ZMod 3) = v i) := by
  decide +kernel

private theorem p13wAux_D6_finite (v : Fin 6 → ZMod 3)
    (hv : (∑ i : Fin 6, v i * v i) ≠ 0)
    (hmono : ∀ k : Fin 6, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∃ m : Fin 6, ∀ i : Fin 6,
      (Pi.single k (1 : ZMod 3) : Fin 6 → ZMod 3) i -
        (2 * (∑ j : Fin 6, v j *
          (Pi.single k (1 : ZMod 3) : Fin 6 → ZMod 3) j) /
          (∑ j : Fin 6, v j * v j)) * v i =
        ε * (Pi.single m (1 : ZMod 3) : Fin 6 → ZMod 3) i) :
    (∃ i : Fin 6, v = (Pi.single i (1 : ZMod 3) : Fin 6 → ZMod 3) ∨
      v = -(Pi.single i (1 : ZMod 3) : Fin 6 → ZMod 3)) ∨
      (D6Root (p13wAux_lift v) ∧ ∀ i, ((p13wAux_lift v i : ℤ) : ZMod 3) = v i) := by
  rcases p13wAux_D6_finite_aux v hv hmono with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨⟨h1, h2⟩, h3⟩

private theorem p13wAux_D6Root_sq_sum {α : Fin 6 → ℤ} (hα : D6Root α) :
    (∑ i, ((α i : ℤ) : ZMod 3) * ((α i : ℤ) : ZMod 3)) = 2 := by
  have hsq : ∀ i : Fin 6, α i * α i = |α i| := by
    intro i
    have hb := abs_le.mp (hα.2 i)
    have h : α i = -1 ∨ α i = 0 ∨ α i = 1 := by omega
    rcases h with h | h | h <;> rw [h] <;> norm_num
  have hsum : (∑ i, α i * α i : ℤ) = 2 := by
    calc (∑ i, α i * α i : ℤ) = ∑ i, |α i| := Finset.sum_congr rfl fun i _ => hsq i
      _ = 2 := hα.1
  have hcast : ((∑ i, α i * α i : ℤ) : ZMod 3) =
      ∑ i, ((α i : ℤ) : ZMod 3) * ((α i : ℤ) : ZMod 3) := by
    push_cast
    rfl
  rw [← hcast, hsum]
  norm_num

private theorem p13wAux_dotB_single_left (x : Fin 6 → ZMod 3) (i : Fin 6) :
    (∑ l : Fin 6, x l * (Pi.single i (1 : ZMod 3) : Fin 6 → ZMod 3) l) = x i := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro l _ hl
    simp [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hl]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private theorem p13wAux_dotB_single_sq (i : Fin 6) :
    (∑ l : Fin 6, (Pi.single i (1 : ZMod 3) : Fin 6 → ZMod 3) l *
      (Pi.single i (1 : ZMod 3) : Fin 6 → ZMod 3) l) = 1 := by
  rw [Finset.sum_eq_single i]
  · simp
  · intro l _ hl
    simp [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hl]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

private theorem p13wAux_dotB_neg_single_left (x : Fin 6 → ZMod 3) (i : Fin 6) :
    (∑ l : Fin 6, x l * (-(Pi.single i (1 : ZMod 3)) : Fin 6 → ZMod 3) l) = -x i := by
  have h : (∑ l : Fin 6, x l * (-(Pi.single i (1 : ZMod 3)) : Fin 6 → ZMod 3) l) =
      ∑ l : Fin 6, -(x l * (Pi.single i (1 : ZMod 3) : Fin 6 → ZMod 3) l) := by
    apply Finset.sum_congr rfl
    intro l _
    rw [Pi.neg_apply]
    ring
  rw [h, Finset.sum_neg_distrib, p13wAux_dotB_single_left]

private theorem p13wAux_dotB_neg_single_sq (i : Fin 6) :
    (∑ l : Fin 6, (-(Pi.single i (1 : ZMod 3)) : Fin 6 → ZMod 3) l *
      (-(Pi.single i (1 : ZMod 3)) : Fin 6 → ZMod 3) l) = 1 := by
  have h : (∑ l : Fin 6, (-(Pi.single i (1 : ZMod 3)) : Fin 6 → ZMod 3) l *
      (-(Pi.single i (1 : ZMod 3)) : Fin 6 → ZMod 3) l) =
      ∑ l : Fin 6, (Pi.single i (1 : ZMod 3) : Fin 6 → ZMod 3) l *
        (Pi.single i (1 : ZMod 3) : Fin 6 → ZMod 3) l := by
    apply Finset.sum_congr rfl
    intro l _
    simp only [Pi.neg_apply]
    ring
  rw [h, p13wAux_dotB_single_sq]

theorem p13a3_D6_pointwise_stabilizer (ψ : Fin 6 → ZMod 3) (hψ : ψ ≠ 0)
    (w : (Fin 6 → ZMod 3) → (Fin 6 → ZMod 3)) (hw : D6EvenSignedPerm w)
    (hfix : ∀ x, (∑ i, ψ i * x i) = 0 → w x = x) :
    w = id ∨ ∃ α : Fin 6 → ℤ, D6Root α ∧
      ((∀ i, ((α i : ℤ) : ZMod 3) = ψ i) ∨ (∀ i, ((α i : ℤ) : ZMod 3) = -ψ i)) ∧
      ∀ x, w x = fun i => x i - (∑ j, (α j : ZMod 3) * x j) * (α i : ZMod 3) := by
  classical
  obtain ⟨σ, ε, hε, hprod, hw_eq⟩ := hw
  have hεsq : ∀ k, ε k * ε k = 1 := by
    intro k
    rcases hε k with h | h <;> rw [h] <;> decide
  have hB : p13wAux_dotB.Nondegenerate := p13wAux_dotB_nondegenerate
  have hBsymm : p13wAux_dotB.IsSymm := ⟨p13wAux_dotB_symm⟩
  have hsymm : ∀ x y, p13wAux_dotB x y = p13wAux_dotB y x := p13wAux_dotB_symm
  let f : (Fin 6 → ZMod 3) →ₗ[ZMod 3] (Fin 6 → ZMod 3) :=
    LinearMap.pi fun j => ε (σ.symm j) • LinearMap.proj (σ.symm j)
  let f' : (Fin 6 → ZMod 3) →ₗ[ZMod 3] (Fin 6 → ZMod 3) :=
    LinearMap.pi fun i => ε i • LinearMap.proj (σ i)
  have hf_apply : ∀ x, f x = w x := by
    intro x
    funext j
    simp only [f, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      smul_eq_mul]
    have h := hw_eq x (σ.symm j)
    rw [Equiv.apply_symm_apply] at h
    exact h.symm
  have hff'_apply : ∀ x, f' (f x) = x := by
    intro x
    funext i
    simp only [f', f, LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      smul_eq_mul]
    rw [Equiv.symm_apply_apply, ← mul_assoc, hεsq i, one_mul]
  have hf'f_apply : ∀ x, f (f' x) = x := by
    intro x
    funext j
    simp only [f, f', LinearMap.pi_apply, LinearMap.smul_apply, LinearMap.proj_apply,
      smul_eq_mul]
    rw [Equiv.apply_symm_apply, ← mul_assoc, hεsq (σ.symm j), one_mul]
  let g : (Fin 6 → ZMod 3) ≃ₗ[ZMod 3] (Fin 6 → ZMod 3) :=
    LinearEquiv.ofLinear f f' (LinearMap.ext hf'f_apply) (LinearMap.ext hff'_apply)
  have hg_apply : ∀ x, g x = w x := by
    intro x
    simp only [g, LinearEquiv.ofLinear_apply]
    exact hf_apply x
  have hg : ∀ x y, p13wAux_dotB (g x) (g y) = p13wAux_dotB x y := by
    intro x y
    rw [hg_apply x, hg_apply y]
    have hwx : ∀ z j, w z j = ε (σ.symm j) * z (σ.symm j) := by
      intro z j
      have h := hw_eq z (σ.symm j)
      rw [Equiv.apply_symm_apply] at h
      exact h
    simp only [p13wAux_dotB_apply, hwx]
    trans ∑ j : Fin 6, x (σ.symm j) * y (σ.symm j)
    · apply Finset.sum_congr rfl
      intro j _
      calc (ε (σ.symm j) * x (σ.symm j)) * (ε (σ.symm j) * y (σ.symm j))
          = (ε (σ.symm j) * ε (σ.symm j)) *
              (x (σ.symm j) * y (σ.symm j)) := by ring
        _ = 1 * (x (σ.symm j) * y (σ.symm j)) := by rw [hεsq]
        _ = x (σ.symm j) * y (σ.symm j) := by rw [one_mul]
    · exact Equiv.sum_comp σ.symm (fun i => x i * y i)
  have hBψ : p13wAux_dotB ψ ≠ 0 :=
    p13wAux_bilin_ne_zero p13wAux_dotB hB hψ
  have hfixH : ∀ x ∈ LinearMap.ker (p13wAux_dotB ψ), g x = x := by
    intro x hx
    have hx' : p13wAux_dotB ψ x = 0 := LinearMap.mem_ker.mp hx
    rw [p13wAux_dotB_apply] at hx'
    rw [hg_apply]
    exact hfix x hx'
  have hH : Module.finrank (ZMod 3) (LinearMap.ker (p13wAux_dotB ψ)) + 1 =
      Module.finrank (ZMod 3) (Fin 6 → ZMod 3) :=
    p13wAux_finrank_ker (p13wAux_dotB ψ) hBψ
  rcases P13a1_hyperplane_fixer (F := ZMod 3) (by decide : (2 : ZMod 3) ≠ 0)
      p13wAux_dotB hB hBsymm g hg (LinearMap.ker (p13wAux_dotB ψ)) hH hfixH with
    hrefl | ⟨v, hv, hform⟩
  · left
    funext x
    have hx : g x = x := by rw [hrefl]; rfl
    rw [← hg_apply x]
    exact hx
  · have hformw : ∀ x, w x =
        x - (2 * p13wAux_dotB x v / p13wAux_dotB v v) • v := by
      intro x
      rw [← hg_apply x, hform x]
    have hvsum : (∑ i : Fin 6, v i * v i) ≠ 0 := by
      rwa [p13wAux_dotB_apply] at hv
    have hmono : ∀ k : Fin 6, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧ ∃ m : Fin 6,
        ∀ i : Fin 6,
        (Pi.single k (1 : ZMod 3) : Fin 6 → ZMod 3) i -
          (2 * (∑ j : Fin 6, v j *
            (Pi.single k (1 : ZMod 3) : Fin 6 → ZMod 3) j) /
            (∑ j : Fin 6, v j * v j)) * v i =
          ε * (Pi.single m (1 : ZMod 3) : Fin 6 → ZMod 3) i := by
      intro k
      refine ⟨ε k, hε k, σ k, ?_⟩
      intro i
      have hwk := p13wAux_d6_apply_single hw_eq k
      have hcoord : w (Pi.single k (1 : ZMod 3)) i =
          (Pi.single k (1 : ZMod 3) : Fin 6 → ZMod 3) i -
            (2 * (∑ j : Fin 6, v j *
              (Pi.single k (1 : ZMod 3) : Fin 6 → ZMod 3) j) /
              (∑ j : Fin 6, v j * v j)) * v i := by
        have h := congrFun (hformw (Pi.single k (1 : ZMod 3))) i
        rw [p13wAux_dotB_apply, p13wAux_dotB_apply] at h
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h
        have hsum : (∑ j : Fin 6, (Pi.single k (1 : ZMod 3) : Fin 6 → ZMod 3) j * v j) =
            ∑ j : Fin 6, v j *
              (Pi.single k (1 : ZMod 3) : Fin 6 → ZMod 3) j :=
          Finset.sum_congr rfl fun j _ => mul_comm _ _
        rw [hsum] at h
        exact h
      rw [← hcoord]
      exact congrFun hwk i
    have hfin := p13wAux_D6_finite v hvsum hmono
    rcases hfin with ⟨i, hi | hi⟩ | ⟨hroot, hcast⟩
    · exfalso
      have hsign : ∀ x, w x = fun j => if j = i then - x j else x j := by
        intro x
        rw [hformw x, hi]
        funext j
        simp only [p13wAux_dotB_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [p13wAux_dotB_single_left, p13wAux_dotB_single_sq]
        by_cases hj : j = i
        · rw [hj]
          simp
          ring_nf
        · simp [hj]
      exact p13wAux_d6_sign_change_even hε hprod hw_eq hsign
    · exfalso
      have hsign : ∀ x, w x = fun j => if j = i then - x j else x j := by
        intro x
        rw [hformw x, hi]
        funext j
        simp only [p13wAux_dotB_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [p13wAux_dotB_neg_single_left, p13wAux_dotB_neg_single_sq]
        by_cases hj : j = i
        · rw [hj]
          simp
          ring_nf
        · simp [hj]
      exact p13wAux_d6_sign_change_even hε hprod hw_eq hsign
    · right
      have hle : ∀ x, p13wAux_dotB ψ x = 0 → p13wAux_dotB v x = 0 := by
        intro x hx
        have hxsum : (∑ i : Fin 6, ψ i * x i) = 0 := by
          rwa [p13wAux_dotB_apply] at hx
        have hxfix : w x = x := hfix x hxsum
        rw [hformw x] at hxfix
        have hzero : (2 * p13wAux_dotB x v / p13wAux_dotB v v) • v = 0 :=
          sub_eq_self.mp hxfix
        have hcoef : 2 * p13wAux_dotB x v / p13wAux_dotB v v = 0 := by
          rcases smul_eq_zero.mp hzero with h | h
          · exact h
          · exact absurd h (p13wAux_ne_zero_of_bilin_self p13wAux_dotB hv)
        have h2 : 2 * p13wAux_dotB x v = 0 := by
          rcases div_eq_zero_iff.mp hcoef with h | h
          · exact h
          · exact absurd h hv
        have hxv : p13wAux_dotB x v = 0 := by
          rcases mul_eq_zero.mp h2 with h | h
          · exact absurd h (by decide : (2 : ZMod 3) ≠ 0)
          · exact h
        rwa [p13wAux_dotB_symm]
      obtain ⟨c, hc, hψcv⟩ :=
        p13wAux_smul_of_le p13wAux_dotB hB hsymm hψ hv hle
      have hcpm : c = 1 ∨ c = -1 := p13wAux_pm_one c hc
      refine ⟨p13wAux_lift v, hroot, ?_, ?_⟩
      · rcases hcpm with hc1 | hcneg
        · left
          intro i
          rw [hcast i, hψcv, hc1, one_smul]
        · right
          intro i
          rw [hcast i, hψcv, hcneg]
          simp
      · intro x
        funext i
        rw [hformw x]
        simp only [p13wAux_dotB_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        have hvv : (∑ j : Fin 6, v j * v j) = 2 := by
          have h := p13wAux_D6Root_sq_sum hroot
          rw [← h]
          exact Finset.sum_congr rfl fun j _ => by rw [← hcast j]
        have hsum' : (∑ j : Fin 6, x j * v j) =
            ∑ j : Fin 6, (p13wAux_lift v j : ZMod 3) * x j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [hcast j, mul_comm]
        rw [hsum', hvv, ← hcast i]
        rw [mul_comm (2 : ZMod 3) (∑ j : Fin 6, (p13wAux_lift v j : ZMod 3) * x j),
          mul_div_cancel_right₀ _ (by decide : (2 : ZMod 3) ≠ 0)]

end CFSG.StandardType.FrameRoute
