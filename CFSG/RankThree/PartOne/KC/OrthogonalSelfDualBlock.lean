module

public import CFSG.RankThree.PartOne.KC.OrthogonalPairedBlock

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

section SelfDualBlock

variable {K : Type*} {V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

@[expose] noncomputable def componentPolar (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) (h : K[X]) :
    primaryComponent x.toLinearMap h →ₗ[K] primaryComponent x.toLinearMap h →ₗ[K] K :=
  (QuadraticMap.polarBilin Q).compl₁₂ (primaryComponent x.toLinearMap h).subtype
    (primaryComponent x.toLinearMap h).subtype

omit [Finite K] [FiniteDimensional K V] in
theorem componentPolar_apply (h : K[X]) (u w : primaryComponent x.toLinearMap h) :
    componentPolar Q x h u w = QuadraticMap.polar Q (u : V) (w : V) := rfl

omit [Finite K] [FiniteDimensional K V] in
theorem OddOrderIsometry.polar_smul_balanced (hx : OddOrderIsometry Q p x) {h : K[X]}
    [Fact (Irreducible h)] (σ : AdjoinRoot h ≃ₐ[K] AdjoinRoot h)
    (hσ : σ (AdjoinRoot.root h) = (AdjoinRoot.root h)⁻¹)
    (hlam0 : AdjoinRoot.root h ≠ 0) (a : AdjoinRoot h) (u w : primaryComponent x.toLinearMap h) :
    componentPolar Q x h (a • u) w = componentPolar Q x h u (σ a • w) := by
  have hxinv : ∀ w : primaryComponent x.toLinearMap h,
      (((AdjoinRoot.root h)⁻¹ • w : primaryComponent x.toLinearMap h) : V) = x.symm (w : V) := by
    intro w
    have h1 : ((AdjoinRoot.root h • ((AdjoinRoot.root h)⁻¹ • w) :
        primaryComponent x.toLinearMap h) : V) = (w : V) := by
      rw [smul_inv_smul₀ hlam0]
    rw [coe_root_smul_primaryComponent x.toLinearMap h] at h1
    exact x.eq_symm_apply.mpr h1
  have ha : a ∈ Algebra.adjoin K {AdjoinRoot.root h} := by
    rw [AdjoinRoot.adjoinRoot_eq_top]; trivial
  induction ha using Algebra.adjoin_induction generalizing u w with
  | mem a ha =>
    rw [Set.mem_singleton_iff] at ha
    subst ha
    change QuadraticMap.polar Q ((AdjoinRoot.root h • u : primaryComponent x.toLinearMap h) : V)
        (w : V) =
      QuadraticMap.polar Q (u : V) ((σ (AdjoinRoot.root h) • w :
        primaryComponent x.toLinearMap h) : V)
    rw [coe_root_smul_primaryComponent x.toLinearMap h, hσ, hxinv]
    exact hx.polar_apply _ _
  | algebraMap c =>
    change QuadraticMap.polar Q ((algebraMap K (AdjoinRoot h) c • u :
        primaryComponent x.toLinearMap h) : V) (w : V) =
      QuadraticMap.polar Q (u : V) ((σ (algebraMap K (AdjoinRoot h) c) • w :
        primaryComponent x.toLinearMap h) : V)
    rw [AlgEquiv.commutes, coe_algebraMap_smul_primaryComponent x.toLinearMap h,
      coe_algebraMap_smul_primaryComponent x.toLinearMap h, QuadraticMap.polar_smul_left,
      QuadraticMap.polar_smul_right]
  | add a b _ _ ha hb =>
    rw [add_smul, map_add, LinearMap.add_apply, ha u w, hb u w, map_add σ, add_smul, map_add]
  | mul a b _ _ ha hb =>
    rw [mul_smul, ha (b • u) w, hb u (σ a • w), map_mul, mul_comm (σ a) (σ b), mul_smul]

instance finite_adjoinRoot_of_fact (h : K[X]) [Fact (Irreducible h)] : Finite (AdjoinRoot h) := by
  have : Module.Finite K (AdjoinRoot h) :=
    (AdjoinRoot.powerBasis (Fact.out : Irreducible h).ne_zero).finite
  exact Module.finite_of_finite K

theorem OddOrderIsometry.exists_selfDual_hermitian (hx : OddOrderIsometry Q p x) (hp2 : Odd p)
    {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) :
    ∃ (d : ℕ) (H : primaryComponent x.toLinearMap h → primaryComponent x.toLinearMap h →
        AdjoinRoot h),
      h.natDegree = 2 * d ∧ AdjoinRoot.root h ^ Nat.card K ^ d = (AdjoinRoot.root h)⁻¹ ∧
      (∀ u w c, Algebra.trace K (AdjoinRoot h) (H u w * c) =
        QuadraticMap.polar Q (u : V) ((c • w : primaryComponent x.toLinearMap h) : V)) ∧
      (∀ u u' w, H (u + u') w = H u w + H u' w) ∧
      (∀ u w w', H u (w + w') = H u w + H u w') ∧
      (∀ (c : AdjoinRoot h) u w, H (c • u) w = frobPow K (AdjoinRoot h) d c * H u w) ∧
      (∀ (c : AdjoinRoot h) u w, H u (c • w) = c * H u w) ∧
      ∀ u w, H w u = frobPow K (AdjoinRoot h) d (H u w) := by
  classical
  have hirr := irreducible_of_mem_primaryFactors hh
  obtain ⟨d, hdeg, -, -, -, -, hroot, -⟩ := hx.selfDualModel hp2 hh hne1 hself
  have hd : finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  have hmon := (mem_primaryFactors.mp hh).2.1
  have hp0 : p ≠ 0 := fun h0' => hx.cast_ne_zero (by rw [h0']; simp)
  have hlamp : AdjoinRoot.root h ^ p = 1 := root_pow_eq_one (hx.dvd_X_pow_sub_one hh)
  have hlam0 : AdjoinRoot.root h ≠ 0 := fun h0' => by
    rw [h0', zero_pow hp0] at hlamp
    exact zero_ne_one hlamp
  set σ := frobPow K (AdjoinRoot h) d with hσdef
  have hσroot : σ (AdjoinRoot.root h) = (AdjoinRoot.root h)⁻¹ := by
    rw [hσdef, frobPow_apply, hroot]
  have hσσ : ∀ z, σ (σ z) = z := frobPow_frobPow K (AdjoinRoot h) hd
  have hbal := hx.polar_smul_balanced σ hσroot hlam0
  have hsymm : ∀ u w, componentPolar Q x h u w = componentPolar Q x h w u := fun u w =>
    QuadraticMap.polar_comm Q _ _
  refine ⟨d, hermForm (AdjoinRoot h) (componentPolar Q x h), hdeg, hroot, fun u w c => ?_,
    hermForm_add_left _ _, hermForm_add_right _ _, hermForm_smul_left σ hbal,
    hermForm_smul_right _ _, hermForm_symm σ hσσ hsymm hbal⟩
  exact trace_hermForm_mul _ _ u w c

theorem OddOrderIsometry.mem_range_blockGL_selfDual_iff (hx : OddOrderIsometry Q p x)
    {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h)
    (H : primaryComponent x.toLinearMap h → primaryComponent x.toLinearMap h → AdjoinRoot h)
    (hH : ∀ u w c, Algebra.trace K (AdjoinRoot h) (H u w * c) =
      QuadraticMap.polar Q (u : V) ((c • w : primaryComponent x.toLinearMap h) : V))
    (γ : BlockGL x h) :
    γ ∈ (blockGL Q x h).range ↔
      ∀ u w, H ((γ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) u)
        ((γ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) w) = H u w := by
  classical
  have hpt : ∀ u w : primaryComponent x.toLinearMap h, QuadraticMap.polar Q (u : V) (w : V) =
      Algebra.trace K (AdjoinRoot h) (H u w) := fun u w => by
    have := hH u w 1
    rw [mul_one, one_smul] at this
    exact this.symm
  constructor
  · rintro ⟨g, rfl⟩ u w
    refine eq_of_trace_mul_eq (K := K) fun c => ?_
    rw [hH, hH]
    have h1 : ((c • (blockGL Q x h g : Module.End (AdjoinRoot h)
        (primaryComponent x.toLinearMap h)) w : primaryComponent x.toLinearMap h) : V) =
        g.1 ((c • w : primaryComponent x.toLinearMap h) : V) := by
      rw [← map_smul]
      exact coe_blockGL h g _
    rw [h1, coe_blockGL h g u]
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
      (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp g.2).1).1 _ _
  · intro hγ
    have hsq := hx.squarefree_minpoly
    let a : primaryFactors x.toLinearMap := ⟨h, hh⟩
    let T := blockUpdate hsq a γ
    have hTc : T.1 ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := T.2
    have hTU : ∀ u : primaryComponent x.toLinearMap h, T.1 (u : V) =
        (((γ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) u : _) : V) :=
      blockUpdate_apply_self hsq a γ
    have horb : orbitSpace x.toLinearMap h = primaryComponent x.toLinearMap h := by
      rw [orbitSpace, ← hself, sup_idem]
    have hmem : T.1 ∈ supportedBlock Q x h := by
      refine hx.mem_supportedBlock_of_block hh hTc ?_ ?_
      · refine fixes_othersSpace_iff.mpr fun k hk hkh hkh' v hv => ?_
        have hka : (⟨k, hk⟩ : primaryFactors x.toLinearMap) ≠ a :=
          fun e => hkh (congrArg Subtype.val e)
        exact blockUpdate_apply_ne hsq a ⟨k, hk⟩ hka γ ⟨v, hv⟩
      · intro u hu
        refine hx.quadratic_eq_of_polar_eq hh hne1 hTc (fun u hu u' hu' => ?_) hu
        have hu₀ : u ∈ primaryComponent x.toLinearMap h := by rwa [horb] at hu
        have hu₀' : u' ∈ primaryComponent x.toLinearMap h := by rwa [horb] at hu'
        have e1 : T.1 u = (((γ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h))
          ⟨u, hu₀⟩ : _) : V) := hTU ⟨u, hu₀⟩
        have e2 : T.1 u' = (((γ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h))
          ⟨u', hu₀'⟩ : _) : V) := hTU ⟨u', hu₀'⟩
        rw [e1, e2, hpt, hγ ⟨u, hu₀⟩ ⟨u', hu₀'⟩, ← hpt]
    refine ⟨⟨T.1, hmem⟩, Units.ext (LinearMap.ext fun v => Subtype.ext ?_)⟩
    exact (hTU v)

end SelfDualBlock

end CFSG.RankThree.PartOne.KCOrthogonal
