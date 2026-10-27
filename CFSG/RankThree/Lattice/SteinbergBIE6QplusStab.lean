module

public import CFSG.RankThree.Lattice.SteinbergBIE6QplusData
public import CFSG.LieType.Chevalley.C2E6NativeF4Coxeter
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderFourStab

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.E6 RootSpace Matrix

@[expose] def e6WGamma : Subgroup (WeylGroup Tag.E6) := relWeylTwist TwistTag.E6

theorem mem_e6WGamma {w : WeylGroup Tag.E6} : w ∈ e6WGamma ↔ e6WeylTwist w = w :=
  Iff.rfl

theorem card_e6WGamma : Nat.card e6WGamma = 1152 :=
  CFSG.LieType.Chevalley.C2E6Std.card_relWeylTwist_E6

theorem e6WeylTwist_simple_eq (i : Fin Tag.E6.rank) :
    e6WeylTwist (simple Tag.E6 i) = simple Tag.E6 (e6Rho i) :=
  weylTwist_simple TwistTag.E6 i

theorem mem_e6WGamma_iff {w : WeylGroup Tag.E6} :
    w ∈ e6WGamma ↔ ∀ x, w • permLattice e6Rho x = permLattice e6Rho (w • x) := by
  rw [mem_e6WGamma]
  constructor
  · intro h x
    have := e6WeylTwist_smul w x
    rw [h] at this
    rw [this, permLattice_e6Rho_e6Rho]
  · intro h
    refine ext_single fun i => ?_
    rw [e6WeylTwist_smul, h, permLattice_e6Rho_e6Rho]

theorem e6WGamma_eq_closure :
    e6WGamma = Subgroup.closure {simple Tag.E6 0 * simple Tag.E6 5,
      simple Tag.E6 2 * simple Tag.E6 4, simple Tag.E6 3, simple Tag.E6 1} := by
  have h : e6WGamma = Subgroup.closure (Set.range TwistTag.E6.orbitReflection) :=
    relWeylTwist_eq_closure TwistTag.E6
  rw [h]
  congr 1
  have h0 : TwistTag.E6.orbitWord 0 = ([0, 5] : List (Fin TwistTag.E6.tag.rank)) := by decide
  have h1 : TwistTag.E6.orbitWord 1 = ([2, 4] : List (Fin TwistTag.E6.tag.rank)) := by decide
  have h2 : TwistTag.E6.orbitWord 2 = ([3] : List (Fin TwistTag.E6.tag.rank)) := by decide
  have h3 : TwistTag.E6.orbitWord 3 = ([1] : List (Fin TwistTag.E6.tag.rank)) := by decide
  have e0 : TwistTag.E6.orbitReflection 0 = simple Tag.E6 0 * simple Tag.E6 5 := by
    rw [TwistTag.orbitReflection, h0, CoxeterSystem.wordProd_cons,
      CoxeterSystem.wordProd_singleton]
    rfl
  have e1 : TwistTag.E6.orbitReflection 1 = simple Tag.E6 2 * simple Tag.E6 4 := by
    rw [TwistTag.orbitReflection, h1, CoxeterSystem.wordProd_cons,
      CoxeterSystem.wordProd_singleton]
    rfl
  have e2 : TwistTag.E6.orbitReflection 2 = simple Tag.E6 3 := by
    rw [TwistTag.orbitReflection, h2, CoxeterSystem.wordProd_singleton]
    rfl
  have e3 : TwistTag.E6.orbitReflection 3 = simple Tag.E6 1 := by
    rw [TwistTag.orbitReflection, h3, CoxeterSystem.wordProd_singleton]
    rfl
  ext g
  simp only [Set.mem_range]
  constructor
  · rintro ⟨a, rfl⟩
    fin_cases a
    · exact Or.inl e0
    · exact Or.inr (Or.inl e1)
    · exact Or.inr (Or.inr (Or.inl e2))
    · exact Or.inr (Or.inr (Or.inr e3))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, e0⟩
    · exact ⟨1, e1⟩
    · exact ⟨2, e2⟩
    · exact ⟨3, e3⟩

theorem iform_permLattice_e6Rho' (x y : Fin Tag.E6.rank → ℤ) :
    iform (permLattice e6Rho x) (permLattice e6Rho y) = iform x y := by
  have hB : ∀ i j, Tag.E6.symmetrizedCartan (e6Rho i) (e6Rho j) =
      Tag.E6.symmetrizedCartan i j := fun i j => by
    rw [symmetrizedCartan_E6]
    exact TwistTag.cartan_perm TwistTag.E6 i j
  simp only [iform, permLattice, Function.comp_apply]
  rw [← Equiv.sum_comp e6Rho (fun i => ∑ j, x (e6Rho.symm i) * Tag.E6.symmetrizedCartan i j *
    y (e6Rho.symm j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp e6Rho (fun j => x (e6Rho.symm (e6Rho i)) *
    Tag.E6.symmetrizedCartan (e6Rho i) j * y (e6Rho.symm j))]
  simp [hB]

theorem permLattice_e6Rho_injective : Function.Injective (permLattice e6Rho) := fun x y h => by
  rw [← permLattice_e6Rho_e6Rho x, h, permLattice_e6Rho_e6Rho]

theorem isRoot_permLattice_e6Rho {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    IsRoot Tag.E6 (permLattice e6Rho α) :=
  IsRoot.permLattice (fun i j => TwistTag.cartan_perm TwistTag.E6 i j) hα

theorem e6WeylTwist_rootReflection {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    e6WeylTwist (rootReflection α) = rootReflection (permLattice e6Rho α) := by
  refine ext_single fun i => ?_
  rw [e6WeylTwist_smul, rootReflection_smul hα, rootReflection_smul (isRoot_permLattice_e6Rho hα),
    permLattice_sub, permLattice_e6Rho_e6Rho, permLattice_zsmul]
  congr 2
  rw [corootPair, corootPair, ← iform_permLattice_e6Rho' α, permLattice_e6Rho_e6Rho,
    iform_permLattice_e6Rho']

theorem rootReflection_mem_relWeylTwist {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (hρ : permLattice e6Rho α = α) : rootReflection α ∈ e6WGamma := by
  rw [mem_e6WGamma, e6WeylTwist_rootReflection hα, hρ]

theorem rootReflection_mul_mem_relWeylTwist {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (h0 : iform α (permLattice e6Rho α) = 0) :
    rootReflection α * rootReflection (permLattice e6Rho α) ∈ e6WGamma := by
  rw [mem_e6WGamma, map_mul, e6WeylTwist_rootReflection hα,
    e6WeylTwist_rootReflection (isRoot_permLattice_e6Rho hα), permLattice_e6Rho_e6Rho]
  exact (commute_rootReflection_of_iform_eq_zero hα (isRoot_permLattice_e6Rho hα) h0).symm.eq

theorem iform_rho_eq_zero {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α)
    (hne : permLattice e6Rho α ≠ α) : iform α (permLattice e6Rho α) = 0 := by
  obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hα
  exact iform_rho_check l hl hne

theorem card_subgroup_relWeylTwist_ne_zero {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (G : Subgroup (WeylGroup Tag.E6)) [Fintype G] (hG : G ≤ e6WGamma) :
    (Fintype.card G : ZMod p) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  have hdvd : Fintype.card G ∣ 1152 := by
    rw [← card_e6WGamma, ← Nat.card_eq_fintype_card]
    exact Subgroup.card_dvd_of_le hG
  have hp : p.Prime := Fact.out
  have h1152 := h.trans hdvd
  rw [show (1152 : ℕ) = 2 ^ 7 * 3 ^ 2 by norm_num] at h1152
  rcases (Nat.Prime.dvd_mul hp).1 h1152 with h | h
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
    omega
  · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
    omega

theorem simple_mem_relWeylTwist {i : Fin Tag.E6.rank} (hi : e6Rho i = i) :
    simple Tag.E6 i ∈ e6WGamma := by
  rw [mem_e6WGamma, e6WeylTwist_simple_eq, hi]

theorem cartan_rho_eq_zero_of_ne {i : Fin Tag.E6.rank} (hi : e6Rho i ≠ i) :
    Tag.E6.cartan i (e6Rho i) = 0 := by
  revert hi
  fin_cases i <;> decide

theorem simple_mul_rho_mem_relWeylTwist (i : Fin Tag.E6.rank) :
    simple Tag.E6 i * simple Tag.E6 (e6Rho i) ∈ e6WGamma := by
  by_cases hi : e6Rho i = i
  · rw [hi]
    exact mul_mem (simple_mem_relWeylTwist hi) (simple_mem_relWeylTwist hi)
  rw [mem_e6WGamma, map_mul, e6WeylTwist_simple_eq, e6WeylTwist_simple_eq]
  have hρρ : e6Rho (e6Rho i) = i := by revert i; decide
  rw [hρρ]
  have hc := cartan_rho_eq_zero_of_ne hi
  have hcomm : Commute (rootReflection (Pi.single i 1 : Fin Tag.E6.rank → ℤ))
      (rootReflection (Pi.single (e6Rho i) 1)) :=
    commute_rootReflection_of_iform_eq_zero (isRoot_single _ _) (isRoot_single _ _) (by
      rw [iform_single_left]
      simp [Pi.single_apply, hc])
  rw [simple_eq_rootReflection, simple_eq_rootReflection]
  exact hcomm.symm.eq

theorem exists_relWeylTwist_dominant {y : RootSpace Tag.E6} (hy : e6TwistIsometry y = y) :
    ∃ u ∈ e6WGamma, weylAct Tag.E6 u y ∈ dominantCone Tag.E6 := by
  obtain ⟨u, hu, hmax⟩ := Set.exists_max_image (e6WGamma : Set (WeylGroup Tag.E6))
    (fun u => inner ℝ (weylAct Tag.E6 u y) (heightVector Tag.E6)) (Set.toFinite _)
    ⟨1, one_mem _⟩
  refine ⟨u, hu, fun i => ?_⟩
  by_contra hneg
  rw [not_le] at hneg
  set Y := weylAct Tag.E6 u y with hYdef
  have hYψ : e6TwistIsometry Y = Y := by
    rw [hYdef, e6TwistIsometry_weylAct, hy, show e6WeylTwist u = u from hu]
  have hρneg : inner ℝ (ofLattice (Pi.single (e6Rho i) 1)) Y < 0 := by
    rw [← inner_single_e6TwistIsometry, hYψ]
    exact hneg
  have hcoef : ∀ k, inner ℝ (ofLattice (Pi.single k 1)) Y < 0 →
      ∑ j, (Tag.E6.cartan k j : ℝ) * Y j < 0 := fun k hk => by
    rw [inner_ofLattice_single_left] at hk
    have hd : (0 : ℝ) < CFSG.LieType.RootSystem.symmetrizer (isFiniteType_cartan Tag.E6) k :=
      Rat.cast_pos.2 (CFSG.LieType.RootSystem.symmetrizer_pos _ k)
    by_contra h
    rw [not_lt] at h
    nlinarith
  have hh : ∀ k, inner ℝ (ofLattice (Pi.single k 1 : Fin Tag.E6.rank → ℤ))
      (heightVector Tag.E6) = 1 := fun k => by
    rw [inner_ofLattice_heightVector, height_single, Int.cast_one]
  by_cases hi : e6Rho i = i
  · have h := hmax _ (mul_mem (simple_mem_relWeylTwist hi) hu)
    rw [weylAct_mul_apply, weylAct_simple, ← hYdef, inner_sub_left, real_inner_smul_left, hh,
      mul_one] at h
    have hc := hcoef i hneg
    linarith
  · have h := hmax _ (mul_mem (simple_mul_rho_mem_relWeylTwist i) hu)
    rw [weylAct_mul_apply, weylAct_mul_apply, weylAct_simple, weylAct_simple, ← hYdef] at h
    have hc := hcoef i hneg
    have hc' := hcoef _ hρneg
    have hcart : (Tag.E6.cartan i (e6Rho i) : ℝ) = 0 := by
      exact_mod_cast cartan_rho_eq_zero_of_ne hi
    have e : ∑ j, (Tag.E6.cartan i j : ℝ) * (Y - (∑ j, (Tag.E6.cartan (e6Rho i) j : ℝ) * Y j) •
        ofLattice (Pi.single (e6Rho i) 1 : Fin Tag.E6.rank → ℤ)) j =
          ∑ j, (Tag.E6.cartan i j : ℝ) * Y j := by
      simp only [toPi_sub, toPi_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ofLattice_apply,
        mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
      have h2 : ∑ x, (Tag.E6.cartan i x : ℝ) * ((∑ j, (Tag.E6.cartan (e6Rho i) j : ℝ) * Y j) *
          ((if x = e6Rho i then (1 : ℤ) else 0 : ℤ) : ℝ)) = 0 := by
        rw [Finset.sum_eq_single (e6Rho i) (fun b _ hb => by simp [hb]) (by simp)]
        simp [hcart]
      rw [h2, sub_zero]
    rw [e, inner_sub_left, real_inner_smul_left, hh, mul_one, inner_sub_left,
      real_inner_smul_left, hh, mul_one] at h
    linarith

section Transport

variable {p : ℕ} [Fact p.Prime]

theorem charVal_permLattice_of_fixed {R : Type*} [CommRing R] {z : Fin Tag.E6.rank → R}
    (hz : ∀ i, z (e6Rho i) = z i) (x : Fin Tag.E6.rank → ℤ) :
    charVal z (permLattice e6Rho x) = charVal z x := by
  simp only [charVal, permLattice, Function.comp_apply]
  rw [← Equiv.sum_comp e6Rho (fun i => ((x (e6Rho.symm i) : ℤ) : R) * z i)]
  simp [hz]

theorem exists_relWeylTwist_smul_rootKernel (hp3 : 3 < p) {z : Fin Tag.E6.rank → ZMod p}
    (hz0 : z ≠ 0) (hzγ : ∀ i, z (e6Rho i) = z i) :
    ∃ u ∈ e6WGamma, ∃ J : Set (Fin Tag.E6.rank), J ≠ Set.univ ∧
      (∀ i, i ∈ J ↔ e6Rho i ∈ J) ∧ (u • ·) '' rootKernel z = parabolicRoots Tag.E6 J := by
  classical
  set K := dualWeylStabilizer z ⊓ e6WGamma with hKdef
  have : Fintype K := Fintype.ofFinite _
  set r := avgColumn K (intLift z) with hrdef
  have hKz : K ≤ dualWeylStabilizer z := inf_le_left
  have hcard : (Fintype.card K : ZMod p) ≠ 0 :=
    card_subgroup_relWeylTwist_ne_zero hp3 K inf_le_right
  have hkey : ∀ α, IsRoot Tag.E6 α → (charVal r α = 0 ↔ α ∈ rootKernel z) := by
    intro α hα
    constructor
    · intro h
      have h' := charVal_avgColumn_cast hKz α
      rw [← hrdef, h, Int.cast_zero, eq_comm] at h'
      exact ⟨hα, (mul_eq_zero.1 h').resolve_left hcard⟩
    · intro hk
      by_cases hρ : permLattice e6Rho α = α
      · have hs : rootReflection α ∈ K :=
          ⟨rootReflection_mem_dualWeylStabilizer hk, rootReflection_mem_relWeylTwist hα hρ⟩
        have h := charVal_avgColumn_smul (intLift z) hs α
        rw [← hrdef, rootReflection_smul_self hα, charVal_neg] at h
        omega
      · have hρk : permLattice e6Rho α ∈ rootKernel z :=
          ⟨isRoot_permLattice_e6Rho hα, by rw [charVal_permLattice_of_fixed hzγ]; exact hk.2⟩
        have h0 := iform_rho_eq_zero hα hρ
        have ht : rootReflection α * rootReflection (permLattice e6Rho α) ∈ K :=
          ⟨mul_mem (rootReflection_mem_dualWeylStabilizer hk)
            (rootReflection_mem_dualWeylStabilizer hρk), rootReflection_mul_mem_relWeylTwist hα h0⟩
        have h := charVal_avgColumn_smul (intLift z) ht α
        have h0' : iform (permLattice e6Rho α) α = 0 := by rw [iform_comm]; exact h0
        rw [← hrdef, mul_smul,
          rootReflection_smul_of_iform_eq_zero (isRoot_permLattice_e6Rho hα) h0',
          rootReflection_smul_self hα, charVal_neg] at h
        omega
  have hz₀ : ∀ i, intLift z (e6Rho i) = intLift z i := fun i => by
    simp only [intLift, hzγ]
  have hrγ : ∀ x, charVal r ((1 : WeylGroup Tag.E6) • permLattice e6Rho x) = charVal r x := by
    intro x
    rw [one_smul, hrdef, charVal_avgColumn, charVal_avgColumn]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [(mem_e6WGamma_iff.1 a.2.2) x, charVal_permLattice_of_fixed hz₀]
  have hψ : e6TwistIsometry (dualVector r) = dualVector r := by
    have h := weylAct_twist_dualVector_eq hrγ
    rwa [map_one, LinearIsometryEquiv.coe_one, id] at h
  obtain ⟨u, hu, hdom⟩ := exists_relWeylTwist_dominant hψ
  set Y := weylAct Tag.E6 u (dualVector r) with hYdef
  have hYψ : e6TwistIsometry Y = Y := by
    rw [hYdef, e6TwistIsometry_weylAct, hψ, show e6WeylTwist u = u from hu]
  set J : Set (Fin Tag.E6.rank) := {i | inner ℝ (ofLattice (Pi.single i 1)) Y = 0} with hJdef
  have hinner : ∀ α : Fin Tag.E6.rank → ℤ,
      inner ℝ (ofLattice (u • α)) Y = ((charVal r α : ℤ) : ℝ) := fun α => by
    rw [hYdef, ← weylAct_ofLattice, LinearIsometryEquiv.inner_map_map, inner_ofLattice_dualVector]
  refine ⟨u, hu, J, ?_, fun i => ?_, ?_⟩
  · intro hJ
    obtain ⟨i, hi⟩ : ∃ i, z i ≠ 0 := by
      by_contra! h
      exact hz0 (funext h)
    have hY0 : Y = 0 := by
      refine eq_of_inner_ofLattice fun v => ?_
      rw [inner_ofLattice_eq_sum, inner_zero_right]
      refine Finset.sum_eq_zero fun j _ => ?_
      have hj : j ∈ J := hJ ▸ Set.mem_univ j
      rw [hj, mul_zero]
    have h := hinner (Pi.single i 1)
    rw [hY0, inner_zero_right] at h
    have h' := charVal_avgColumn_cast hKz (Pi.single i 1 : Fin Tag.E6.rank → ℤ)
    have hc : charVal r (Pi.single i 1 : Fin Tag.E6.rank → ℤ) = 0 := by
      exact_mod_cast h.symm
    rw [← hrdef, hc, Int.cast_zero, eq_comm] at h'
    exact hi (by
      have := (mul_eq_zero.1 h').resolve_left hcard
      rwa [charVal_single] at this)
  · simp only [hJdef, Set.mem_ofPred_eq]
    rw [← inner_single_e6TwistIsometry, hYψ]
  · ext β
    constructor
    · rintro ⟨α, hα, rfl⟩
      refine ⟨IsRoot.smul hα.1 u, fun i hi => ?_⟩
      have h0 : inner ℝ (ofLattice (u • α)) Y = 0 := by
        rw [hinner, (hkey α hα.1).2 hα, Int.cast_zero]
      exact (inner_root_eq_zero_iff hdom (IsRoot.smul hα.1 u)).1 h0 i hi
    · rintro ⟨hβ, hsupp⟩
      have h0 : inner ℝ (ofLattice β) Y = 0 :=
        (inner_root_eq_zero_iff hdom hβ).2 fun i hi => hsupp i hi
      refine ⟨u⁻¹ • β, ?_, smul_inv_smul u β⟩
      have hα : IsRoot Tag.E6 (u⁻¹ • β) := IsRoot.smul hβ u⁻¹
      refine (hkey _ hα).1 ?_
      have := hinner (u⁻¹ • β)
      rw [smul_inv_smul, h0] at this
      exact_mod_cast this.symm

end Transport

@[expose] def qpLzv (zl l : List ℤ) : ℤ := (∑ i : Fin Tag.E6.rank, vget l i * vget zl i) % 5

@[expose] def e6QpSearchOK (zl : List ℤ) : Bool :=
  !(Tag.E6.artifactRoots.all fun a => (qpLzv zl a == 0) ==
      (List.finRange Tag.E6.rank).all fun i => vget zl i == 0 || vget a i == 0) ||
  Tag.E6.artifactRoots.all fun a₀ => !(qpLzv zl a₀ == vget zl 0 &&
    (vget zl 0 != 0 || decide (0 < a₀.sum))) ||
  Tag.E6.artifactRoots.all fun a₁ => !(qpLzv zl a₁ == vget zl 1 &&
    (vget zl 1 != 0 || decide (0 < a₁.sum)) && lform a₀ a₁ == 0) ||
  Tag.E6.artifactRoots.all fun a₂ => !(qpLzv zl a₂ == vget zl 2 &&
    (vget zl 2 != 0 || decide (0 < a₂.sum)) && lform a₀ a₂ == -1 && lform a₁ a₂ == 0) ||
  Tag.E6.artifactRoots.all fun a₃ => !(qpLzv zl a₃ == vget zl 3 &&
    (vget zl 3 != 0 || decide (0 < a₃.sum)) && lform a₀ a₃ == 0 && lform a₁ a₃ == -1 &&
    lform a₂ a₃ == -1) ||
  Tag.E6.artifactRoots.all fun a₄ => !(qpLzv zl a₄ == vget zl 4 &&
    (vget zl 4 != 0 || decide (0 < a₄.sum)) && lform a₀ a₄ == 0 && lform a₁ a₄ == 0 &&
    lform a₂ a₄ == 0 && lform a₃ a₄ == -1) ||
  Tag.E6.artifactRoots.all fun a₅ => !(qpLzv zl a₅ == vget zl 5 &&
    (vget zl 5 != 0 || decide (0 < a₅.sum)) && lform a₀ a₅ == 0 && lform a₁ a₅ == 0 &&
    lform a₂ a₅ == 0 && lform a₃ a₅ == 0 && lform a₄ a₅ == -1 &&
    decide (lcomb [4, 3, 5, 6, 4, 2] [a₀, a₁, a₂, a₃, a₄, a₅] ∈ e6F4S27)) ||
  decide ([a₀, a₁, a₂, a₃, a₄, a₅] = [[1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0],
    [0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]])

theorem e6QpSearchOK_all : ∀ a b c d : Fin 5,
    e6QpSearchOK [(a : ℤ), (b : ℤ), (c : ℤ), (d : ℤ), (c : ℤ), (a : ℤ)] = true := by
  decide +kernel

theorem qpLzv_ofFn (z : Fin Tag.E6.rank → ZMod 5) (x : Fin Tag.E6.rank → ℤ) :
    ((qpLzv (List.ofFn fun i => ((z i).val : ℤ)) (List.ofFn x) : ℤ) : ZMod 5) = charVal z x := by
  have e : ((qpLzv (List.ofFn fun i => ((z i).val : ℤ)) (List.ofFn x) : ℤ) : ZMod 5) =
      ((∑ i : Fin Tag.E6.rank, vget (List.ofFn x) i *
        vget (List.ofFn fun i => ((z i).val : ℤ)) i : ℤ) : ZMod 5) :=
    ZMod.intCast_mod _ 5
  rw [e, charVal]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show List.ofFn x = vofFn Tag.E6.rank x from rfl, vget_vofFn,
    show (List.ofFn fun i => ((z i).val : ℤ)) = vofFn Tag.E6.rank (fun i => ((z i).val : ℤ))
      from rfl, vget_vofFn]
  simp

theorem qpLzv_nonneg_lt (zl l : List ℤ) : 0 ≤ qpLzv zl l ∧ qpLzv zl l < 5 :=
  ⟨Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num)⟩

theorem qpLzv_eq_of_charVal {z : Fin Tag.E6.rank → ZMod 5} {x : Fin Tag.E6.rank → ℤ} {c : ℤ}
    (hc0 : 0 ≤ c) (hc5 : c < 5) (h : charVal z x = (c : ZMod 5)) :
    qpLzv (List.ofFn fun i => ((z i).val : ℤ)) (List.ofFn x) = c := by
  have h' := qpLzv_ofFn z x
  rw [h, ZMod.intCast_eq_intCast_iff' _ _ 5] at h'
  obtain ⟨h0, h5⟩ := qpLzv_nonneg_lt (List.ofFn fun i => ((z i).val : ℤ)) (List.ofFn x)
  have h'' : qpLzv (List.ofFn fun i => ((z i).val : ℤ)) (List.ofFn x) % 5 = c % 5 := by
    exact_mod_cast h'
  rw [Int.emod_eq_of_lt h0 h5, Int.emod_eq_of_lt hc0 hc5] at h''
  exact h''

theorem vget_ofFn_val (z : Fin Tag.E6.rank → ZMod 5) (i : Fin Tag.E6.rank) :
    vget (List.ofFn fun i => ((z i).val : ℤ)) i = ((z i).val : ℤ) := by
  rw [show (List.ofFn fun i => ((z i).val : ℤ)) = vofFn Tag.E6.rank (fun i => ((z i).val : ℤ))
    from rfl, vget_vofFn]

theorem eq_one_of_mem_dualWeylStabilizer_five {z : Fin Tag.E6.rank → ZMod 5}
    (hzγ : ∀ i, z (e6Rho i) = z i) {J : Set (Fin Tag.E6.rank)}
    (hJ : rootKernel z = parabolicRoots Tag.E6 J) {g : WeylGroup Tag.E6}
    (hg : g ∈ dualWeylStabilizer z)
    (hpos : ∀ j ∈ J, 0 < height (g • (Pi.single j 1 : Fin Tag.E6.rank → ℤ))) : g = 1 := by
  set zl : List ℤ := List.ofFn fun i => ((z i).val : ℤ) with hzl
  have hz4 : z 4 = z 2 := hzγ 2
  have hz5 : z 5 = z 0 := hzγ 0
  have hS : e6QpSearchOK zl = true := by
    have h := e6QpSearchOK_all ⟨(z 0).val, (z 0).val_lt⟩ ⟨(z 1).val, (z 1).val_lt⟩
      ⟨(z 2).val, (z 2).val_lt⟩ ⟨(z 3).val, (z 3).val_lt⟩
    have e : zl = [((z 0).val : ℤ), ((z 1).val : ℤ), ((z 2).val : ℤ), ((z 3).val : ℤ),
        ((z 2).val : ℤ), ((z 0).val : ℤ)] := by
      rw [hzl, ofFn_six, hz4, hz5]
    rw [e]
    exact h
  have hJz : ∀ j, j ∈ J ↔ z j = 0 := fun j => by
    constructor
    · intro hj
      have : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ rootKernel z := by
        rw [hJ]
        exact ⟨isRoot_single _ j, fun i hi => by
          have : i ≠ j := fun e => hi (e ▸ hj)
          simp [this]⟩
      rw [← charVal_single z j]
      exact this.2
    · intro hj
      have : (Pi.single j 1 : Fin Tag.E6.rank → ℤ) ∈ rootKernel z :=
        ⟨isRoot_single _ j, by rw [charVal_single]; exact hj⟩
      rw [hJ] at this
      by_contra hjJ
      have := this.2 j hjJ
      simp at this
  have hval0 : ∀ i : Fin Tag.E6.rank, (vget zl i == 0) = decide (z i = 0) := fun i => by
    rw [hzl, vget_ofFn_val, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, Nat.cast_eq_zero,
      ZMod.val_eq_zero]
  have hhyp : (Tag.E6.artifactRoots.all fun a => (qpLzv zl a == 0) ==
      (List.finRange Tag.E6.rank).all fun i => vget zl i == 0 || vget a i == 0) = true := by
    rw [List.all_eq_true]
    intro a ha
    have hroot := isRoot_toVec ha
    have hlen := length_of_mem_artifactRoots ha
    have hk : toVec Tag.E6.rank a ∈ rootKernel z ↔
        toVec Tag.E6.rank a ∈ parabolicRoots Tag.E6 J := by
      rw [hJ]
    have h1 : toVec Tag.E6.rank a ∈ rootKernel z ↔ qpLzv zl a = 0 := by
      have e := qpLzv_ofFn z (toVec Tag.E6.rank a)
      rw [ofFn_toVec hlen, ← hzl] at e
      obtain ⟨h0, h5⟩ := qpLzv_nonneg_lt zl a
      constructor
      · intro hk
        rw [hk.2] at e
        have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).1 e
        omega
      · intro h
        refine ⟨hroot, ?_⟩
        rw [← e, h, Int.cast_zero]
    have h2 : toVec Tag.E6.rank a ∈ parabolicRoots Tag.E6 J ↔
        ∀ i : Fin Tag.E6.rank, z i = 0 ∨ toVec Tag.E6.rank a i = 0 := by
      constructor
      · intro h i
        by_cases hi : i ∈ J
        · exact Or.inl ((hJz i).1 hi)
        · exact Or.inr (h.2 i hi)
      · intro h
        exact ⟨hroot, fun i hi => (h i).resolve_left fun e => hi ((hJz i).2 e)⟩
    have h3 : ((List.finRange Tag.E6.rank).all fun i => vget zl i == 0 || vget a i == 0) =
        decide (∀ i : Fin Tag.E6.rank, z i = 0 ∨ toVec Tag.E6.rank a i = 0) := by
      rw [Bool.eq_iff_iff, List.all_eq_true, decide_eq_true_iff]
      constructor
      · intro h i
        have := h i (List.mem_finRange i)
        rw [Bool.or_eq_true, hval0] at this
        simpa [toVec] using this
      · intro h i _
        rw [Bool.or_eq_true, hval0]
        simpa [toVec] using h i
    rw [h3, beq_iff_eq, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, ← h2, ← hk, h1]
  have hS' := hS
  rw [e6QpSearchOK, hhyp, Bool.not_true, Bool.false_or] at hS'
  have hr : ∀ i, List.ofFn (g • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)) ∈
      Tag.E6.artifactRoots := fun i =>
    isRoot_iff_mem_artifactRoots.1 (IsRoot.smul (isRoot_single Tag.E6 i) g)
  have hv : ∀ i, qpLzv zl (List.ofFn (g • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))) = vget zl i :=
    fun i => by
      rw [hzl, vget_ofFn_val]
      refine qpLzv_eq_of_charVal (by positivity) (by exact_mod_cast (z i).val_lt) ?_
      rw [mem_dualWeylStabilizer.1 hg, charVal_single]
      simp
  have hp : ∀ i : Fin Tag.E6.rank, (vget zl i != 0 || decide (0 < (List.ofFn
      (g • (Pi.single i 1 : Fin Tag.E6.rank → ℤ))).sum)) = true := fun i => by
    by_cases hzi : z i = 0
    · have := hpos i ((hJz i).2 hzi)
      rw [Bool.or_eq_true]
      right
      rw [decide_eq_true_iff, List.sum_ofFn]
      exact this
    · rw [Bool.or_eq_true]
      left
      rw [bne_iff_ne, hzl, vget_ofFn_val]
      intro h
      exact hzi ((ZMod.val_eq_zero _).1 (by exact_mod_cast h))
  have hf : ∀ i j, lform (List.ofFn (g • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)))
      (List.ofFn (g • (Pi.single j 1 : Fin Tag.E6.rank → ℤ))) = Tag.E6.cartan i j := fun i j => by
    rw [lform_ofFn, e6Form_smul, e6Form_single]
  have hc := lcomb_gTuple g
  rw [gTuple, ofFn_six] at hc
  have v0 : (qpLzv zl (List.ofFn (g • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ))) ==
      vget zl 0) = true := beq_iff_eq.2 (hv 0)
  have p0 : (vget zl 0 != 0 || decide (0 < (List.ofFn
      (g • (Pi.single 0 1 : Fin Tag.E6.rank → ℤ))).sum)) = true := hp 0
  have v1 : (qpLzv zl (List.ofFn (g • (Pi.single 1 1 : Fin Tag.E6.rank → ℤ))) ==
      vget zl 1) = true := beq_iff_eq.2 (hv 1)
  have p1 : (vget zl 1 != 0 || decide (0 < (List.ofFn
      (g • (Pi.single 1 1 : Fin Tag.E6.rank → ℤ))).sum)) = true := hp 1
  have v2 : (qpLzv zl (List.ofFn (g • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ))) ==
      vget zl 2) = true := beq_iff_eq.2 (hv 2)
  have p2 : (vget zl 2 != 0 || decide (0 < (List.ofFn
      (g • (Pi.single 2 1 : Fin Tag.E6.rank → ℤ))).sum)) = true := hp 2
  have v3 : (qpLzv zl (List.ofFn (g • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ))) ==
      vget zl 3) = true := beq_iff_eq.2 (hv 3)
  have p3 : (vget zl 3 != 0 || decide (0 < (List.ofFn
      (g • (Pi.single 3 1 : Fin Tag.E6.rank → ℤ))).sum)) = true := hp 3
  have v4 : (qpLzv zl (List.ofFn (g • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ))) ==
      vget zl 4) = true := beq_iff_eq.2 (hv 4)
  have p4 : (vget zl 4 != 0 || decide (0 < (List.ofFn
      (g • (Pi.single 4 1 : Fin Tag.E6.rank → ℤ))).sum)) = true := hp 4
  have v5 : (qpLzv zl (List.ofFn (g • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ))) ==
      vget zl 5) = true := beq_iff_eq.2 (hv 5)
  have p5 : (vget zl 5 != 0 || decide (0 < (List.ofFn
      (g • (Pi.single 5 1 : Fin Tag.E6.rank → ℤ))).sum)) = true := hp 5
  have hfc : ∀ (i j : Fin Tag.E6.rank) (c : ℤ), Tag.E6.cartan i j = c →
      (lform (List.ofFn (g • (Pi.single i 1 : Fin Tag.E6.rank → ℤ)))
        (List.ofFn (g • (Pi.single j 1 : Fin Tag.E6.rank → ℤ))) == c) = true :=
    fun i j c h => beq_iff_eq.2 ((hf i j).trans h)
  have g0 := bor_of_not (List.all_eq_true.1 hS' _ (hr 0)) (by
    simp only [v0, p0, Bool.and_true])
  have g1 := bor_of_not (List.all_eq_true.1 g0 _ (hr 1)) (by
    simp only [v1, p1, hfc 0 1 (0) (by decide), Bool.and_true])
  have g2 := bor_of_not (List.all_eq_true.1 g1 _ (hr 2)) (by
    simp only [v2, p2, hfc 0 2 (-1) (by decide), hfc 1 2 (0) (by decide),
      Bool.and_true])
  have g3 := bor_of_not (List.all_eq_true.1 g2 _ (hr 3)) (by
    simp only [v3, p3, hfc 0 3 (0) (by decide), hfc 1 3 (-1) (by decide), hfc 2 3 (-1) (by decide),
      Bool.and_true])
  have g4 := bor_of_not (List.all_eq_true.1 g3 _ (hr 4)) (by
    simp only [v4, p4, hfc 0 4 (0) (by decide), hfc 1 4 (0) (by decide), hfc 2 4 (0) (by decide),
      hfc 3 4 (-1) (by decide), Bool.and_true])
  have g5 := bor_of_not (List.all_eq_true.1 g4 _ (hr 5)) (by
    simp only [v5, p5, hfc 0 5 (0) (by decide), hfc 1 5 (0) (by decide), hfc 2 5 (0) (by decide),
      hfc 3 5 (0) (by decide), hfc 4 5 (-1) (by decide), Bool.true_and, Bool.and_true]
    rw [hc]
    simpa using e6F4_S27_mem g)
  have hid := of_decide_eq_true g5
  simp only [List.cons.injEq, and_true] at hid
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hid
  refine ext_single fun i => List.ofFn_injective ?_
  rw [one_smul]
  fin_cases i
  · exact h0.trans (by decide +kernel)
  · exact h1.trans (by decide +kernel)
  · exact h2.trans (by decide +kernel)
  · exact h3.trans (by decide +kernel)
  · exact h4.trans (by decide +kernel)
  · exact h5.trans (by decide +kernel)

theorem parabolic_le_of_simple_mem {J : Set (Fin Tag.E6.rank)} {H : Subgroup (WeylGroup Tag.E6)}
    (h : ∀ j ∈ J, simple Tag.E6 j ∈ H) : (coxeterSystem Tag.E6).parabolic J ≤ H :=
  (coxeterSystem Tag.E6).parabolic_le_iff.2 h

theorem parabolic_le_dualWeylStabilizer {K : Type*} [CommRing K] {z : Fin Tag.E6.rank → K}
    {J : Set (Fin Tag.E6.rank)} (hJ : rootKernel z = parabolicRoots Tag.E6 J) :
    (coxeterSystem Tag.E6).parabolic J ≤ dualWeylStabilizer z := by
  refine parabolic_le_of_simple_mem fun j hj => ?_
  rw [simple_eq_rootReflection]
  refine rootReflection_mem_dualWeylStabilizer ?_
  rw [hJ]
  exact ⟨isRoot_single _ j, fun i hi => by
    have : i ≠ j := fun e => hi (e ▸ hj)
    simp [this]⟩

theorem dualWeylStabilizer_le_parabolic_five {z : Fin Tag.E6.rank → ZMod 5}
    (hzγ : ∀ i, z (e6Rho i) = z i) {J : Set (Fin Tag.E6.rank)}
    (hJ : rootKernel z = parabolicRoots Tag.E6 J) :
    dualWeylStabilizer z ≤ (coxeterSystem Tag.E6).parabolic J := by
  intro w hw
  obtain ⟨q, hx, hu, hxu⟩ := ((coxeterSystem Tag.E6).existsUnique_mem_parabolic_mul J w).exists
  set x := q.1
  set u := q.2
  have hxz : x ∈ dualWeylStabilizer z := parabolic_le_dualWeylStabilizer hJ hx
  have huz : u ∈ dualWeylStabilizer z := by
    have := mul_mem (inv_mem hxz) hw
    rwa [hxu, inv_mul_cancel_left] at this
  have hg : u⁻¹ = 1 := eq_one_of_mem_dualWeylStabilizer_five hzγ hJ (inv_mem huz) fun j hj => by
    have hr := IsRoot.smul (isRoot_single Tag.E6 j) u⁻¹
    rcases IsRoot.height_pos_or_neg hr with h | h
    · exact h
    · exfalso
      apply hu j hj
      rw [← (coxeterSystem Tag.E6).isRightDescent_inv_iff]
      exact (smul_single_mem_negRoots_iff u⁻¹ j).1 ⟨hr, h⟩
  rw [hxu, inv_eq_one.1 hg, mul_one]
  exact hx

theorem dualWeylStabilizer_gammaFixed_eq_closure {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    {z : Fin Tag.E6.rank → ZMod p} (hz0 : z ≠ 0) (hzγ : ∀ i, z (e6Rho i) = z i) :
    dualWeylStabilizer z = Subgroup.closure {s | ∃ α ∈ rootKernel z, s = rootReflection α} := by
  by_cases hp5 : 5 < p
  · exact dualWeylStabilizer_eq_closure hp5 z
  have hp : p = 5 := by
    have hpr : p.Prime := Fact.out
    interval_cases p
    · exact absurd hpr (by norm_num)
    · rfl
  subst hp
  refine le_antisymm (fun g hg => ?_) closure_rootReflection_le
  obtain ⟨u, hu, J, -, -, hΦ⟩ := exists_relWeylTwist_smul_rootKernel hp3 hz0 hzγ
  set z' : Fin Tag.E6.rank → ZMod 5 := fun i => charVal z (u⁻¹ • Pi.single i 1) with hz'def
  have hz' : ∀ x, charVal z' (u • x) = charVal z x := fun x => by
    have h := charVal_smul_eq_sum z u⁻¹ (u • x)
    rw [inv_smul_smul] at h
    rw [h, charVal]
  have hu' := inv_mem hu
  have hz'γ : ∀ i, z' (e6Rho i) = z' i := fun i => by
    simp only [hz'def]
    rw [← permLattice_single, (mem_e6WGamma_iff.1 hu') (Pi.single i 1),
      charVal_permLattice_of_fixed hzγ]
  have hJ' : rootKernel z' = parabolicRoots Tag.E6 J := by
    rw [← image_rootKernel_of_charVal hz', hΦ]
  have hg' := (mem_dualWeylStabilizer_conj hz' g).1 hg
  have hpar := dualWeylStabilizer_le_parabolic_five hz'γ hJ' hg'
  have hcl : (coxeterSystem Tag.E6).parabolic J ≤
      Subgroup.closure {s | ∃ α ∈ rootKernel z', s = rootReflection α} := by
    refine parabolic_le_of_simple_mem fun j hj => ?_
    refine Subgroup.subset_closure ⟨Pi.single j 1, ?_, simple_eq_rootReflection j⟩
    rw [hJ']
    exact ⟨isRoot_single _ j, fun i hi => by
      have : i ≠ j := fun e => hi (e ▸ hj)
      simp [this]⟩
  exact (mem_closure_rootKernel_conj hz' g).2 (hcl hpar)

end CFSG.RankThree.Lattice
