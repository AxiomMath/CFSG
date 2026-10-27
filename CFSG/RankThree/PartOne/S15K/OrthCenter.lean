module

public import CFSG.RankThree.PartOne.KC.OrthogonalInnerPlaneDefs
public import CFSG.RankThree.Classical.SteinbergBJOrthogonalDerivedCentralizer
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear

public section

namespace CFSG.RankThree.PartOne.S15K

open Polynomial Module CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

omit [Finite K] in
theorem specialBlock_center_pow_paired (hx : OddOrderIsometry Q p x) (hp : p.Prime) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ reciprocalPolynomial h)
    (hm : 1 ≤ primaryMultiplicity x.toLinearMap h) (hpm : ¬ p ∣ primaryMultiplicity x.toLinearMap h)
    {g : V ≃ₗ[K] V} (hg : g ∈ specialBlock Q x h)
    (hc : ∀ g' ∈ specialBlock Q x h, g * g' = g' * g) (hgp : g ^ p = 1) : g = 1 := by
  classical
  set m := primaryMultiplicity x.toLinearMap h with hmdef
  let b : Module.Basis (Fin m) (AdjoinRoot h) (primaryComponent x.toLinearMap h) :=
    Module.finBasisOfFinrankEq _ _ rfl
  let e₁ : ↥(specialBlock Q x h) ≃*
      SpecialLinearGroup (AdjoinRoot h) (primaryComponent x.toLinearMap h) :=
    MulEquiv.ofBijective (specialToSL Q x h)
      ⟨hx.specialToSL_injective hh, hx.specialToSL_surjective_paired hh hne⟩
  let e₂ : ↥(specialBlock Q x h) ≃* Matrix.SpecialLinearGroup (Fin m) (AdjoinRoot h) :=
    e₁.trans (Matrix.SpecialLinearGroup.toLin_equiv b).symm
  have hcen : e₂ ⟨g, hg⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin m) (AdjoinRoot h)) := by
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := e₂.surjective z
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc y y.2).symm
  obtain ⟨r, hrm, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcen
  rw [Fintype.card_fin] at hrm
  have hγp : (e₂ ⟨g, hg⟩) ^ p = 1 := by
    rw [← map_pow]
    have : (⟨g, hg⟩ : ↥(specialBlock Q x h)) ^ p = 1 := Subtype.ext hgp
    rw [this, map_one]
  have hmat : (Matrix.scalar (Fin m) r) ^ p = 1 := by
    rw [hr, ← Matrix.SpecialLinearGroup.coe_pow, hγp]
    rfl
  have hrp : r ^ p = 1 := by
    have := congrFun (congrFun hmat ⟨0, hm⟩) ⟨0, hm⟩
    rw [← map_pow] at this
    simpa [Matrix.scalar_apply] using this
  have hr1 : r = 1 := by
    have hcop : Nat.Coprime m p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm).symm
    have := pow_gcd_eq_one.2 ⟨hrm, hrp⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  have h1 : e₂ ⟨g, hg⟩ = 1 := by
    apply Subtype.ext
    rw [← hr, hr1, map_one]
    rfl
  have h2 : (⟨g, hg⟩ : ↥(specialBlock Q x h)) = 1 := e₂.injective (by rw [h1, map_one])
  exact congrArg Subtype.val h2

section SelfDual

open CFSG.LocalAnalysis.ComponentInitial

theorem specialBlock_center_pow_selfDual (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp3 : 3 < p)
    {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) (hm : 2 ≤ primaryMultiplicity x.toLinearMap h)
    (hpm : ¬ p ∣ primaryMultiplicity x.toLinearMap h) {g : V ≃ₗ[K] V}
    (hg : g ∈ specialBlock Q x h) (hc : ∀ g' ∈ specialBlock Q x h, g * g' = g' * g)
    (hgp : g ^ p = 1) : g = 1 := by
  classical
  have hp2 : Odd p := hp.odd_of_ne_two (by omega)
  have hirr := irreducible_of_mem_primaryFactors hh
  obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2 hh hne1 hself
  have hd : finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, hq, hbar⟩ := exists_unitaryFieldData K (AdjoinRoot h) hd
  have hbar' : ∀ z, frobPow K (AdjoinRoot h) d z = hU.bar z := fun z => by
    rw [hbar, frobPow_apply]
  let B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
    LinearMap.mk₂'ₛₗ hU.bar (RingHom.id _) H hadd1
      (fun c u w => by rw [hleft, smul_eq_mul, hbar']) hadd2
      (fun c u w => by rw [hright, smul_eq_mul, RingHom.id_apply])
  have hBH : ∀ u w, B u w = H u w := fun u w => rfl
  have hBsymm : B.IsSymm := ⟨fun u w => by rw [hBH, hBH, hsymm u w, hbar']⟩
  have hBl : B.SeparatingLeft := by
    intro u hu
    refine Subtype.ext (hx.eq_zero_of_polar_selfdual hh hself u.2 fun w hw => ?_)
    have h1 := hH u ⟨w, hw⟩ 1
    rw [mul_one, one_smul] at h1
    have h2 : H u ⟨w, hw⟩ = 0 := by rw [← hBH]; exact hu _
    rw [h2, map_zero] at h1
    exact h1.symm
  have hrange : (specialBlockGL Q x h).range = sesqSpecialUnitaryGroup B := by
    rw [range_specialBlockGL, sesqSpecialUnitaryGroup]
    congr 1
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH, mem_sesqUnitaryGroup]
    exact Iff.rfl
  have hdvd := hx.dvd_card_pow_add_one hp hh hne1 hroot
  have hp5 : 5 ≤ p := by
    by_contra hlt
    have h4 : p = 4 := by omega
    rw [h4] at hp
    exact absurd hp (by norm_num)
  have hq4 : 4 ≤ ℓ ^ (f * d) := by
    have h1 : Nat.card K ^ d = ℓ ^ (f * d) := by rw [hq, pow_mul]
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hq2 : 2 ≤ ℓ ^ (f * d) := by omega
  set γ : BlockGL x h := specialBlockGL Q x h ⟨g, hg⟩ with hγdef
  obtain ⟨c, hc'⟩ := KCUnitary.exists_smul_of_commute_special_unitary hU hBsymm hBl hm hq2
    (γ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) (fun δ hδ => by
      rw [← hrange] at hδ
      obtain ⟨⟨g', hg'⟩, rfl⟩ := hδ
      have h1 : γ * specialBlockGL Q x h ⟨g', hg'⟩ = specialBlockGL Q x h ⟨g', hg'⟩ * γ := by
        rw [hγdef, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hc g' hg')
      exact congrArg (fun u : BlockGL x h =>
        (u : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h))) h1)
  have hγ : (γ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) =
      c • LinearMap.id := LinearMap.ext hc'
  have hcm : c ^ primaryMultiplicity x.toLinearMap h = 1 := by
    have hdet := det_specialBlockGL h ⟨g, hg⟩
    rw [← hγdef, hγ, LinearMap.det_smul, LinearMap.det_id, mul_one] at hdet
    exact hdet
  have hcp : c ^ p = 1 := by
    obtain ⟨v, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (primaryComponent_ne_bot hx.squarefree_minpoly hh)
    have hγp : γ ^ p = 1 := by
      rw [hγdef, ← map_pow]
      have : (⟨g, hg⟩ : ↥(specialBlock Q x h)) ^ p = 1 := Subtype.ext hgp
      rw [this, map_one]
    have h1 : ((γ ^ p : BlockGL x h) :
        Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) = LinearMap.id := by
      rw [hγp]
      rfl
    have hid : (LinearMap.id : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) ^ p =
        LinearMap.id := by
      rw [← Module.End.one_eq_id, one_pow]
    rw [Units.val_pow_eq_pow_val, hγ, _root_.smul_pow, hid] at h1
    have h2 := congrArg (fun T => T ⟨v, hv0.1⟩) h1
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at h2
    have h3 : (c ^ p - 1) • (⟨v, hv0.1⟩ : primaryComponent x.toLinearMap h) = 0 := by
      rw [sub_smul, h2, one_smul, sub_self]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact sub_eq_zero.mp h4
    · exact absurd (congrArg Subtype.val h4) hv0.2
  have hc1 : c = 1 := by
    have hcop : Nat.Coprime (primaryMultiplicity x.toLinearMap h) p :=
      ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm).symm
    have := pow_gcd_eq_one.2 ⟨hcm, hcp⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  have hγ1 : γ = 1 := Units.ext (by rw [hγ, hc1, one_smul]; rfl)
  have h5 : (⟨g, hg⟩ : ↥(specialBlock Q x h)) = 1 :=
    hx.specialBlockGL_injective hh (by rw [← hγdef, hγ1, map_one])
  exact congrArg Subtype.val h5

end SelfDual

section Fixed

theorem fixedLayer_center [CharP K 2]
    (hinj : Function.Injective (QuotientGroup.mk' ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf
      (orthDerived Q))))
    (hq : 3 < Nat.card K) (hx : OddOrderIsometry Q p x) {n : ℕ}
    {C : Fin n → Subgroup (ProjOrthDerived Q)} (hsup : (⨆ i, C i) = fixedLayerImage Q x)
    (hcomm : ∀ i j, i ≠ j → ∀ u ∈ C i, ∀ v ∈ C j, u * v = v * u) (i : Fin n)
    {u : ProjOrthDerived Q} (hu : u ∈ C i) (hc : ∀ f ∈ C i, u * f = f * u) : u = 1 := by
  classical
  have hu' : u ∈ fixedLayerImage Q x := hsup ▸ (le_iSup C i) hu
  by_cases hlist : FixedLayerListed Q x
  swap
  · have : fixedLayerImage Q x = ⊥ := by simp [fixedLayerImage, hlist]
    rw [this, Subgroup.mem_bot] at hu'
    exact hu'
  have hW3 : 3 ≤ finrank K (fixedSpace x) := hlist.1
  set ρ : ↥(orthDerived Q) →* ProjOrthDerived Q :=
    QuotientGroup.mk' ((CFSG.ClassicalGroups.Orthogonal.scalars K V).subgroupOf (orthDerived Q))
    with hρ
  have hsupFix : (⨆ i, C i) = fixedComponentImage Q x := by
    rw [hsup, fixedLayerImage_of_listed hlist]
  rw [fixedLayerImage_of_listed hlist] at hu'
  obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.mp hu'
  have hcent : (⨆ j, C j) ≤ Subgroup.centralizer ({ρ u₀} : Set (ProjOrthDerived Q)) :=
    iSup_le fun j => by
      intro v hv
      rw [Subgroup.mem_centralizer_singleton_iff]
      by_cases hji : j = i
      · subst hji
        exact (hc v hv).symm
      · exact (hcomm i j (Ne.symm hji) _ hu v hv).symm
  have hu₀D : (u₀ : V ≃ₗ[K] V) ∈ supportedFixedDerived Q x := Subgroup.mem_subgroupOf.mp hu₀
  have hgB : (u₀ : V ≃ₗ[K] V) ∈ supportedBlock Q x (X - 1) :=
    (mem_supportedFixedDerived.mp hu₀D).1
  have hcommΩ : ∀ f : ↥(orthDerived Q), (f : V ≃ₗ[K] V) ∈ supportedFixedDerived Q x →
      f * u₀ = u₀ * f := by
    intro f hf
    have hmem : ρ f ∈ ⨆ j, C j := by
      rw [hsupFix]
      exact Subgroup.mem_map.mpr ⟨f, Subgroup.mem_subgroupOf.mpr hf, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.mp (hcent hmem)
    apply hinj
    show ρ (f * u₀) = ρ (u₀ * f)
    rw [map_mul, map_mul]
    exact this
  set γ := restrictFixed Q x ⟨(u₀ : V ≃ₗ[K] V), hgB⟩ with hγ
  have hWnd := hx.polarBilin_fixed_nondegenerate
  have hKq : 2 < Nat.card K := by omega
  obtain ⟨hscal, -, -⟩ := CFSG.RankThree.Classical.finite_orthogonal_derived_natural_linear_centralizer_scalar
    hKq (Q.comp (fixedSpace x).subtype) hWnd hW3
  obtain ⟨c, hc'⟩ := (hscal (γ : fixedSpace x →ₗ[K] fixedSpace x)).mp (fun g hg => by
    obtain ⟨f, hf⟩ := restrictFixed_surjective hx g
      (orthDerived_le_orthogonalGroup hg)
    have hfD : f.1 ∈ supportedFixedDerived Q x :=
      mem_supportedFixedDerived.mpr ⟨f.2, by rw [hf]; exact hg⟩
    have h1 := hcommΩ ⟨f.1, hx.supportedFixedDerived_le_orthDerived hfD⟩ hfD
    have h2 := congrArg Subtype.val h1
    have h3 : restrictFixed Q x (f * ⟨(u₀ : V ≃ₗ[K] V), hgB⟩) =
        restrictFixed Q x (⟨(u₀ : V ≃ₗ[K] V), hgB⟩ * f) := by
      congr 1
      exact Subtype.ext h2
    rw [map_mul, map_mul, hf] at h3
    refine LinearMap.ext fun w => ?_
    have := congrArg (fun e : fixedSpace x ≃ₗ[K] fixedSpace x => e w) h3
    exact this.symm)
  obtain ⟨P⟩ := CFSG.RankThree.Classical.nonempty_hypPair_of_finite hWnd hW3
  have hQsum : (Q.comp (fixedSpace x).subtype) (P.e + P.f) = 1 := by
    rw [QuadraticMap.map_add (Q.comp (fixedSpace x).subtype) P.e P.f, P.Q_e, P.Q_f, P.polar_ef,
      zero_add, zero_add]
  have hγO := restrictFixed_mem_orthogonalGroup (Q := Q) (x := x) ⟨(u₀ : V ≃ₗ[K] V), hgB⟩
  have hQγ := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hγO (P.e + P.f)
  have hγw : γ (P.e + P.f) = c • (P.e + P.f) := by
    have := congrArg (fun M : fixedSpace x →ₗ[K] fixedSpace x => M (P.e + P.f)) hc'
    exact this
  rw [hγw, QuadraticMap.map_smul, hQsum, smul_eq_mul, mul_one] at hQγ
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hc1 : c = 1 := by
    have h2 : (c + 1) * (c + 1) = 0 := by linear_combination hQγ + (1 + c) * h2K
    have h3 : c + 1 = 0 := mul_self_eq_zero.mp h2
    linear_combination h3 - h2K
  have hγ1 : γ = 1 := LinearEquiv.ext fun w => by
    have := congrArg (fun M : fixedSpace x →ₗ[K] fixedSpace x => M w) hc'
    simpa [hc1] using this
  have hu1 : (u₀ : V ≃ₗ[K] V) = 1 := hx.eq_one_of_restrictFixed_eq_one hgB hγ1
  have : u₀ = 1 := Subtype.ext hu1
  rw [this, map_one]

end Fixed

end CFSG.RankThree.PartOne.S15K
