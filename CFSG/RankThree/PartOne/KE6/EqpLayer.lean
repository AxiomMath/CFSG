module

public import CFSG.RankThree.PartOne.KE6.EqpKernel
public import CFSG.RankThree.PartOne.KE6.EqpFactor
public import CFSG.RankThree.PartOne.KE6.EqpSl2
public import CFSG.RankThree.PartOne.KE6.Phi6Std
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenLayers
public import CFSG.RankThree.Lattice.SteinbergBIE6QplusStab
public import CFSG.RankThree.PartOne.KE6.EqpTorus

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6 CFSG.RankThree.Lattice
  CFSG.RankThree.Chevalley CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints)
open scoped Matrix MatrixGroups Pointwise

section Helpers

theorem mem_map_conj_iff {G : Type*} [Group G] (H : Subgroup G) (c x : G) :
    x ∈ H.map (MulAut.conj c).toMonoidHom ↔ c⁻¹ * x * c ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : c⁻¹ * ((MulAut.conj c).toMonoidHom y) * c = y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact hy
  · intro h
    refine ⟨c⁻¹ * x * c, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem mem_iff_conj_mem_of_map_eq {G : Type*} [Group G] {A B : Subgroup G} {n : G}
    (h : A.map (MulAut.conj n).toMonoidHom = B) (y : G) : y ∈ A ↔ n * y * n⁻¹ ∈ B := by
  rw [← h, mem_map_conj_iff]
  have e : n⁻¹ * (n * y * n⁻¹) * n = y := by group
  rw [e]

theorem conj_commute_fixed {G : Type*} [Group G] (Φ : G →* G) {a b : G} (hab : Commute a b)
    (hΦb : Φ b = b) {y : G} (hy : a * Φ y * a⁻¹ = y) :
    a * Φ (b * y * b⁻¹) * a⁻¹ = b * y * b⁻¹ := by
  rw [map_mul, map_mul, map_inv, hΦb]
  have hc : a * b = b * a := hab.eq
  calc a * (b * Φ y * b⁻¹) * a⁻¹ = (a * b) * Φ y * (a * b)⁻¹ := by group
    _ = (b * a) * Φ y * (b * a)⁻¹ := by rw [hc]
    _ = b * (a * Φ y * a⁻¹) * b⁻¹ := by group
    _ = b * y * b⁻¹ := by rw [hy]

theorem e6WGamma_mul_e6W0 {u : WeylGroup Tag.E6} (hu : u ∈ e6WGamma) :
    u * e6W0 = e6W0 * u := by
  refine ext_single fun i => ?_
  rw [mul_smul, mul_smul, e6W0_smul, e6W0_smul, smul_neg,
    (mem_e6WGamma_iff.1 hu) (Pi.single i 1)]

theorem commute_canonicalRep_e6W0 {Ω : Type} [Field Ω] [CharP Ω 2] {u : WeylGroup Tag.E6}
    (hu : u ∈ e6WGamma) :
    Commute (eqpN Ω) (canonicalRep (coxeterSystem Tag.E6) Ω u) := by
  have hm := CFSG.RankThree.PartOne.KE.qplus_canonicalRep_mul (τ := Tag.E6) (K := Ω)
  show canonicalRep (coxeterSystem Tag.E6) Ω e6W0 * canonicalRep (coxeterSystem Tag.E6) Ω u =
    canonicalRep (coxeterSystem Tag.E6) Ω u * canonicalRep (coxeterSystem Tag.E6) Ω e6W0
  rw [← hm, ← hm, (e6WGamma_mul_e6W0 hu).symm]

end Helpers

section Theta

variable {Ω : Type} [Field Ω] [CharP Ω 2]

theorem eqp_theta_fixed_iff (m : Fin 15) (f : ℕ) {ω : Ω} (hω : ω ^ 2 ^ f = ω + 1)
    (z : ModGL Tag.E6 Ω) :
    eqpN Ω * Units.map (entrywiseHom (iterateFrobenius Ω 2 f)) z * (eqpN Ω)⁻¹ = z ↔
      e6Psi Ω (e6QpSupport m) f ((eqpCas m (eqpA ω)⁻¹)⁻¹ * z * eqpCas m (eqpA ω)⁻¹) =
        (eqpCas m (eqpA ω)⁻¹)⁻¹ * z * eqpCas m (eqpA ω)⁻¹ := by
  have h : eqpN Ω * Units.map (entrywiseHom (iterateFrobenius Ω 2 f)) z * (eqpN Ω)⁻¹ =
      eqpCas m (eqpA ω)⁻¹ * e6Psi Ω (e6QpSupport m) f ((eqpCas m (eqpA ω)⁻¹)⁻¹ * z *
        eqpCas m (eqpA ω)⁻¹) * (eqpCas m (eqpA ω)⁻¹)⁻¹ := eqp_theta_eq m f hω z
  rw [h]
  generalize eqpCas m (eqpA ω)⁻¹ = g
  generalize e6Psi Ω (e6QpSupport m) f (g⁻¹ * z * g) = a
  constructor
  · intro hz
    rw [← hz]
    group
  · intro ha
    rw [ha]
    group

end Theta

section Family

variable {Ω : Type} [Field Ω] [CharP Ω 2] [IsAlgClosed Ω]

theorem eqp_frob_bijective (f : ℕ) : Function.Bijective (iterateFrobenius Ω 2 f) := by
  refine ⟨(iterateFrobenius Ω 2 f).injective, fun y => ?_⟩
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos (show 0 < 2 by norm_num) f)
  exact ⟨z, by rw [iterateFrobenius_def]; exact hz⟩

theorem eqp_exists_omega (f : ℕ) (hf : 1 ≤ f) : ∃ ω : Ω, ω ^ 2 ^ f = ω + 1 := by
  have hq : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  obtain ⟨c, hc⟩ := exists_pow_sub_add_eq_zero hq (1 : Ω)
  refine ⟨c, ?_⟩
  have h2 : (2 : Ω) = 0 := eqp_two_eq_zero
  linear_combination hc - h2

theorem eqp_kernelLayer_of_family {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] [CharP K 2] {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) (m : Fin 15)
    {ι : Type} [Fintype ι] [DecidableEq ι] (Ξ : ι → Set (Fin Tag.E6.rank → ℤ))
    (P : ι → Subgroup (ModGL Tag.E6 Ω)) (hinj : Function.Injective Ξ)
    (hrange : Set.range Ξ = e6ComponentOrbits (e6QpSupport m))
    (hP : ∀ k, IsE6EvenFactor Ω (e6QpSupport m) f (Ξ k) (P k))
    {u : WeylGroup Tag.E6} (hu : u ∈ e6WGamma) {S : Set (Fin Tag.E6.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot Tag.E6 α)
    (hSJ : (u • ·) '' S = parabolicRoots Tag.E6 (e6QpSupport m)) :
    Nonempty (EqpKernelLayer (eqpN Ω) (Units.map (entrywiseHom (iterateFrobenius Ω 2 f))) S K
      ι) := by
  classical
  obtain ⟨ω, hω⟩ := eqp_exists_omega (Ω := Ω) f (by omega)
  have hFrb := eqp_frob_bijective (Ω := Ω) f
  have hJs := (gammaStable_iff_mem_e6QpSupport (e6QpSupport m)).2 ⟨m, rfl⟩
  have halg := eqp_halg K Ω
  obtain ⟨hcommute, μ, hμ1, hμ2, hμ3, hμ4, hμ5, hμ6⟩ :=
    ((E6_even_supported_finite_layers_detect_full_module_commutants Ω).2.2 (e6QpSupport m) hJs.1
      hJs.2 f hf halg).2 ι Ξ P hinj hrange hP
  have hmem : ∀ k, ∃ i ∈ e6QpSupport m, Ξ k = e6Xi (e6QpSupport m) i := fun k => by
    have : Ξ k ∈ Set.range Ξ := ⟨k, rfl⟩
    rw [hrange] at this
    exact this
  have hsep : ∀ k l, k ≠ l → IsSeparated (rootSetSupport (Ξ k)) (rootSetSupport (Ξ l)) := by
    intro k l hkl
    obtain ⟨i, hi, hik⟩ := hmem k
    obtain ⟨i', hi', hil⟩ := hmem l
    rw [hik, hil]
    exact isSeparated_rootSetSupport m hi hi' (by rw [← hik, ← hil]; exact hinj.ne hkl)
  have hcover : e6QpSupport m = ⋃ k, rootSetSupport (Ξ k) := by
    ext j
    rw [mem_iff_exists_rootSetSupport m j, Set.mem_iUnion, ← hrange]
    constructor
    · rintro ⟨_, ⟨k, rfl⟩, hj⟩
      exact ⟨k, hj⟩
    · rintro ⟨k, hj⟩
      exact ⟨_, ⟨k, rfl⟩, hj⟩
  have hspanE : ∀ k, rootSpan Tag.E6 Ω (Ξ k) = subsystemGroup Tag.E6 Ω (rootSetSupport (Ξ k)) := by
    intro k
    obtain ⟨i, hi, hik⟩ := hmem k
    rw [hik]
    conv_lhs => rw [e6Xi_eq_parabolicRoots_support m hi]
    exact (subsystemGroup_eq_rootSpan _).symm
  have hsupp : ∀ k, rootSetSupport (Ξ k) ⊆ e6QpSupport m := by
    intro k j hj
    obtain ⟨i, hi, hik⟩ := hmem k
    rw [hik] at hj
    exact mem_e6QpSupport_of_mem_rootSetSupport m hi hj
  have hPJ : ∀ k, P k ≤ subsystemGroup Tag.E6 Ω (e6QpSupport m) := fun k => by
    refine ((hP k).le).trans ?_
    rw [subsystemGroup_eq_rootSpan, subsystemGroup_eq_rootSpan]
    exact rootSpan_mono (CFSG.RankThree.Lattice.parabolicRoots_mono (hsupp k))
  have hnormJ : ∀ k, torusGroup Tag.E6 Ω ⊔ subsystemGroup Tag.E6 Ω (e6QpSupport m) ≤
      Subgroup.normalizer (rootSpan Tag.E6 Ω (Ξ k) : Set (ModGL Tag.E6 Ω)) := fun k => by
    rw [hspanE k]
    exact torus_sup_le_normalizer_of_separated (e6QpSupport m) (fun k => rootSetSupport (Ξ k))
      hsep hcover k
  have hgQ := eqpCas_mem_rootSpan (Ω := Ω) m (eqpA ω)⁻¹
  have htheta := eqp_theta_fixed_iff (Ω := Ω) m f hω
  have hmu5 := (hμ6 (eqpCas m (eqpA ω)⁻¹)).1
  generalize eqpCas m (eqpA ω)⁻¹ = g at hgQ htheta hmu5
  have hgJ : g ∈ subsystemGroup Tag.E6 Ω (e6QpSupport m) := by
    rw [subsystemGroup_eq_rootSpan]
    exact hgQ
  have hQ : (rootSpan Tag.E6 Ω S).map
      (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) Ω u)).toMonoidHom =
      subsystemGroup Tag.E6 Ω (e6QpSupport m) := by
    rw [(canonical_weyl_root_transport Tag.E6 Ω).1 u S hS, hSJ]
    exact (subsystemGroup_eq_rootSpan _).symm
  have hQmem := mem_iff_conj_mem_of_map_eq hQ
  have hnn : Commute (eqpN Ω) (canonicalRep (coxeterSystem Tag.E6) Ω u) :=
    commute_canonicalRep_e6W0 hu
  have hΦn : Units.map (entrywiseHom (iterateFrobenius Ω 2 f))
      (canonicalRep (coxeterSystem Tag.E6) Ω u) = canonicalRep (coxeterSystem Tag.E6) Ω u :=
    entrywise_canonicalRep' _ hFrb u
  have hconjsup : ∀ y ∈ torusGroup Tag.E6 Ω ⊔ rootSpan Tag.E6 Ω S,
      canonicalRep (coxeterSystem Tag.E6) Ω u * y * (canonicalRep (coxeterSystem Tag.E6) Ω u)⁻¹ ∈
        torusGroup Tag.E6 Ω ⊔ subsystemGroup Tag.E6 Ω (e6QpSupport m) := fun y hy =>
    conj_mem_torus_sup hS hQ hy
  refine ⟨EqpKernelLayer.ofFamily (w := u)
    (fun k => (P k).map (MulAut.conj ((canonicalRep (coxeterSystem Tag.E6) Ω u)⁻¹ * g)).toMonoidHom)
    hS hQ ?_ ?_ ?_ ?_ ?_ ?_ ?_⟩
  all_goals generalize hn : canonicalRep (coxeterSystem Tag.E6) Ω u = n at *
  ·
    intro k
    have := (e6EvenFactor_facts hf hK (hP k)).1
    exact Finite.of_equiv _ (Subgroup.equivMapOfInjective (P k) (MulAut.conj (n⁻¹ * g)).toMonoidHom
      (fun a b h => (MulAut.conj (n⁻¹ * g)).injective h)).toEquiv
  ·
    intro k
    exact CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective (P k) (MulAut.conj (n⁻¹ * g)).toMonoidHom
        (fun a b h => (MulAut.conj (n⁻¹ * g)).injective h))
      (e6EvenFactor_facts hf hK (hP k)).2.1
  ·
    intro k y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [hQmem]
    have e : n * (MulAut.conj (n⁻¹ * g)).toMonoidHom x * n⁻¹ = g * x * g⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact mul_mem (mul_mem hgJ (hPJ k hx)) (inv_mem hgJ)
  ·
    intro k y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [mem_twistedFixedPoints]
    have hΨx : e6Psi Ω (e6QpSupport m) f x = x :=
      ((e6EvenFactor_facts hf hK (hP k)).2.2.2.1 hx).2
    have hz : eqpN Ω * Units.map (entrywiseHom (iterateFrobenius Ω 2 f)) (g * x * g⁻¹) *
        (eqpN Ω)⁻¹ = g * x * g⁻¹ := by
      rw [htheta]
      have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
      rw [e]
      exact hΨx
    have h := conj_commute_fixed (Units.map (entrywiseHom (iterateFrobenius Ω 2 f)))
      hnn.inv_right (by rw [map_inv, hΦn]) hz
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have e2 : n⁻¹ * g * x * (n⁻¹ * g)⁻¹ = n⁻¹ * (g * x * g⁻¹) * n⁻¹⁻¹ := by group
    rw [e2]
    exact h
  ·
    intro k y hy hyR x' hx'
    obtain ⟨x, hx, rfl⟩ := hx'
    rw [mem_twistedFixedPoints] at hyR
    have hy₁ := conj_commute_fixed (Units.map (entrywiseHom (iterateFrobenius Ω 2 f))) hnn hΦn hyR
    have hy₁S := hconjsup y hy
    have hy₂Ψ := (htheta _).1 hy₁
    have hy₂S : g⁻¹ * (n * y * n⁻¹) * g ∈
        torusGroup Tag.E6 Ω ⊔ subsystemGroup Tag.E6 Ω (e6QpSupport m) :=
      mul_mem (mul_mem (inv_mem (Subgroup.mem_sup_right hgJ)) hy₁S) (Subgroup.mem_sup_right hgJ)
    have hy₂N := hnormJ k hy₂S
    have hnormP := e6EvenFactor_norm_of_fixed hf hK (hP k) hy₂N hy₂Ψ x hx
    refine ⟨_, hnormP, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  ·
    have hmap : ((⨆ i, (P i).map (MulAut.conj (n⁻¹ * g)).toMonoidHom).map
        (MulAut.conj n).toMonoidHom : Subgroup (ModGL Tag.E6 Ω)) =
        (⨆ i, P i).map (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.map_iSup, Subgroup.map_iSup]
      refine iSup_congr fun k => ?_
      ext z
      constructor
      · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
        refine ⟨x, hx, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      · rintro ⟨x, hx, rfl⟩
        refine ⟨_, ⟨x, hx, rfl⟩, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    have h1 : (((⨆ i, P i).map (MulAut.conj g).toMonoidHom : Subgroup (ModGL Tag.E6 Ω)) :
        Set (ModGL Tag.E6 Ω)) =
        (fun x => g * x * g⁻¹) '' ((μ.range : Subgroup (ModGL Tag.E6 Ω)) :
          Set (ModGL Tag.E6 Ω)) := by
      rw [hμ2, Subgroup.coe_map]
      rfl
    have h2 : (fun x => g * x * g⁻¹) '' ((rootSpan Tag.E6 Ω (parabolicRoots Tag.E6 (e6QpSupport m)) :
        Subgroup (ModGL Tag.E6 Ω)) : Set (ModGL Tag.E6 Ω)) =
        ((subsystemGroup Tag.E6 Ω (e6QpSupport m) : Subgroup (ModGL Tag.E6 Ω)) :
          Set (ModGL Tag.E6 Ω)) := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' : x ∈ subsystemGroup Tag.E6 Ω (e6QpSupport m) := by
          rw [subsystemGroup_eq_rootSpan]
          exact hx
        exact mul_mem (mul_mem hgJ hx') (inv_mem hgJ)
      · intro hz
        refine ⟨g⁻¹ * z * g, ?_, by group⟩
        have h3 : g⁻¹ * z * g ∈ subsystemGroup Tag.E6 Ω (e6QpSupport m) :=
          mul_mem (mul_mem (inv_mem hgJ) hz) hgJ
        rw [subsystemGroup_eq_rootSpan] at h3
        exact h3
    rw [hmap, h1, hmu5, h2]
  ·
    rintro ⟨α, hαS, hαfix⟩
    have hfixJ : ∃ β ∈ parabolicRoots Tag.E6 (e6QpSupport m), permLattice e6Rho β = β := by
      refine ⟨u • α, ?_, ?_⟩
      · rw [← hSJ]
        exact ⟨α, hαS, rfl⟩
      · rw [← (mem_e6WGamma_iff.1 hu) α, hαfix]
    obtain ⟨k, j, h₀, h⟩ := eqp_sl2_psi hK m Ξ P hrange hP hfixJ
    refine ⟨k, j, n⁻¹ * g * h₀, fun B => ?_⟩
    refine ⟨_, h B, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem eqp_kernelLayer {K : Type} [Field K] [Finite K] [Algebra K Ω]
    [IsAlgClosure K Ω] [CharP K 2] {f : ℕ} (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) (m : Fin 15)
    {u : WeylGroup Tag.E6} (hu : u ∈ e6WGamma) {S : Set (Fin Tag.E6.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot Tag.E6 α)
    (hSJ : (u • ·) '' S = parabolicRoots Tag.E6 (e6QpSupport m)) :
    ∃ ι' : Type, Nonempty (EqpKernelLayer (eqpN Ω)
      (Units.map (entrywiseHom (iterateFrobenius Ω 2 f))) S K ι') := by
  classical
  have hJs := (gammaStable_iff_mem_e6QpSupport (e6QpSupport m)).2 ⟨m, rfl⟩
  have halg := eqp_halg K Ω
  obtain ⟨ι, hι, hdec, Ξ, P, hinj, hrange, hP⟩ :=
    ((E6_even_supported_finite_layers_detect_full_module_commutants Ω).2.2 (e6QpSupport m) hJs.1
      hJs.2 f hf halg).1
  exact ⟨ι, eqp_kernelLayer_of_family hf hK m Ξ P hinj hrange hP hu hS hSJ⟩

end Family

end CFSG.RankThree.PartOne.KE6
