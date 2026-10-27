module

public import CFSG.RankThree.PartOne.F106.OddRadBlocks
public import CFSG.RankThree.PartOne.S11d.OrthFixedLayer
public import CFSG.RankThree.PartOne.KC.OrthogonalDerivedInLayer
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44ThreeGL
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalLocalObstruction
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear

public section

namespace CFSG.RankThree.PartOne.F106.OddRadOrth

open Polynomial Module CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.LieType.Universal.Spin CFSG.LocalCores
open scoped commutatorElement

theorem odd_card_radical_perfectResidual_of_blocks {G : Type*} [Group G] [Finite G]
    {ι : Type*} (B : ι → Subgroup G) (hq : ∀ i, IsQuasisimple ↥(B i))
    (hsub : ∀ i, ((B i).subgroupOf (perfectResidual G)).IsSubnormal)
    (hle : perfectResidual G ≤ ⨆ i, B i)
    (hodd : ∀ i, Odd (Nat.card ↥(Subgroup.center ↥(B i)))) :
    Odd (Nat.card ↥(solvableRadical ↥(perfectResidual G))) := by
  set P := perfectResidual G with hP
  have hBP : ∀ i, B i ≤ P := fun i =>
    CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidual (B i) (hq i).1
  have hsup : (⨆ i, B i) = P := le_antisymm (iSup_le hBP) hle
  have hcomp : ∀ i, IsComponent ((B i).subgroupOf P) := fun i =>
    ⟨isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (hBP i)).symm (hq i), hsub i⟩
  refine odd_card_radical_of_blocks (fun i => (B i).subgroupOf P) hcomp ?_ fun i => ?_
  · apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_iSup, Subgroup.map_top, Subgroup.range_subtype]
    rw [show (⨆ i, ((B i).subgroupOf P).map P.subtype) = ⨆ i, B i from
      iSup_congr fun i => Subgroup.map_subgroupOf_eq_of_le (hBP i)]
    exact hsup
  · let e : ↥((B i).subgroupOf P) ≃* ↥(B i) := Subgroup.subgroupOfEquivOfLe (hBP i)
    have hc : Nat.card ↥(Subgroup.center ↥((B i).subgroupOf P)) =
        Nat.card ↥(Subgroup.center ↥(B i)) := by
      rw [← Subgroup.map_center_eq e]
      exact (Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).symm
    rw [hc]
    exact hodd i




instance finite_linearEquiv_orth {K V : Type*} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] : Finite (V ≃ₗ[K] V) := by
  have : Finite V := Module.finite_of_finite K
  exact Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V)) fun e₁ e₂ h =>
    LinearEquiv.ext (congrFun h)

section Burnside

theorem isSolvable_of_no_prime_gt_three {G : Type*} [Group G] [Finite G]
    (h : ∀ (g : G) (q : ℕ), q.Prime → 3 < q → orderOf g ≠ q) : Group.IsSolvable G := by
  have hpos : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hprime : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ Nat.card G → ℓ = 2 ∨ ℓ = 3 := by
    intro ℓ hℓ hdvd
    have : Fact ℓ.Prime := ⟨hℓ⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) ℓ hdvd
    by_contra hne
    push Not at hne
    have h4 : 3 < ℓ := by
      have := hℓ.two_le
      omega
    exact h g ℓ hℓ h4 hg
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd hpos
  have hm3 : ∀ {d : ℕ}, d.Prime → d ∣ m → d = 3 := by
    intro d hd hdm
    have hdG : d ∣ Nat.card G := hn ▸ Dvd.dvd.mul_left hdm _
    rcases hprime d hd hdG with rfl | rfl
    · exact absurd (hm.of_dvd_nat hdm) (by decide)
    · rfl
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have hm' : m = 3 ^ m.primeFactorsList.length := Nat.eq_prime_pow_of_unique_prime_dvd hm0 hm3
  exact CFSG.RankThree.PartTwo.Sec4.Census.isSolvable_of_card_dvd_two_pow_mul_three_pow
    (a := a) (b := m.primeFactorsList.length) (by rw [hn, ← hm'])

end Burnside

section Gen

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

abbrev nsub (Q : QuadraticForm K V) (x : V ≃ₗ[K] V) : Subgroup (V ≃ₗ[K] V) :=
  isometryCentralizer Q x ⊓ orthDerived Q

theorem mem_derivedSeries_of_mem_perfectResidual {G : Type*} [Group G] {g : G}
    (hg : g ∈ perfectResidual G) (n : ℕ) : g ∈ derivedSeries G n :=
  Subgroup.mem_iInf.mp hg n

omit [Finite K] in
theorem perfectResidual_nsub_decomp (hx : OddOrderIsometry Q p x) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep) {g : ↥(nsub Q x)}
    (hg : g ∈ perfectResidual ↥(nsub Q x)) :
    ∃ f ∈ supportedFixedDerived Q x, ∃ j ∈ specialProduct Q x Rep,
      (g : V ≃ₗ[K] V) = j * f := by
  have hNM : nsub Q x ≤ isometryCentralizer Q x := inf_le_left
  have hg1 : g ∈ commutator ↥(nsub Q x) := by
    have := mem_derivedSeries_of_mem_perfectResidual hg 1
    rwa [derivedSeries_one] at this
  have hgc : (g : V ≃ₗ[K] V) ∈ ⁅isometryCentralizer Q x, isometryCentralizer Q x⁆ := by
    have h1 : (g : V ≃ₗ[K] V) ∈ (commutator ↥(nsub Q x)).map (nsub Q x).subtype :=
      Subgroup.mem_map_of_mem _ hg1
    rw [Subgroup.map_subtype_commutator] at h1
    exact Subgroup.commutator_mono hNM hNM h1
  obtain ⟨f, hf, j, hj, hgjf⟩ := hx.exists_decomposition_of_mem_commutator hRep hgc
  exact ⟨f, hf, j, hj, hgjf⟩

theorem perfectResidual_nsub_unlisted (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hx : OddOrderIsometry Q p x) (hp2 : Odd p) {Rep : Finset K[X]}
    (hRep : IsOrbitRepresentatives x Rep)
    (hlist : ¬ (3 ≤ finrank K (fixedSpace x) ∧
      ¬ SmallFixedException (Q.comp (fixedSpace x).subtype)))
    {g : ↥(nsub Q x)} (hg : g ∈ perfectResidual ↥(nsub Q x)) :
    (g : V ≃ₗ[K] V) ∈ specialProduct Q x Rep := by
  classical
  obtain ⟨f, hf, j, hj, hgjf⟩ := perfectResidual_nsub_decomp hx hRep hg
  have hNM : nsub Q x ≤ isometryCentralizer Q x := inf_le_left
  let r : ↥(nsub Q x) →* (fixedSpace x ≃ₗ[K] fixedSpace x) :=
    (isometryRestrictFixed Q x).comp (Subgroup.inclusion hNM)
  have hsolv : Group.IsSolvable r.range := by
    by_cases hdim : finrank K (fixedSpace x) ≤ 2
    · have hcomm : ∀ a b : r.range, a * b = b * a := by
        rintro ⟨_, m, rfl⟩ ⟨_, m', rfl⟩
        have := hx.restrict_commute_of_mem_orthDerived hp2 hQ hRep hdim
          (Subgroup.mem_inf.mp m.2).1 (Subgroup.mem_inf.mp m.2).2
          (Subgroup.mem_inf.mp m'.2).1 (Subgroup.mem_inf.mp m'.2).2
        exact Subtype.ext this.eq
      let _ : CommGroup r.range := { (inferInstance : Group r.range) with mul_comm := hcomm }
      infer_instance
    · have h3 : 3 ≤ finrank K (fixedSpace x) := by omega
      have hexc : SmallFixedException (Q.comp (fixedSpace x).subtype) := by
        by_contra hne
        exact hlist ⟨h3, hne⟩
      have hno := (orthogonal_regular_space_coverage (Q.comp (fixedSpace x).subtype)
        hx.polarBilin_fixed_nondegenerate h3).1 hexc
      have hOsolv := isSolvable_of_no_prime_gt_three hno
      have hle : r.range ≤
          TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace x).subtype) := by
        rintro _ ⟨m, rfl⟩
        exact isometryRestrictFixed_mem_orthogonalGroup _
      exact Group.isSolvable_of_isSolvable_injective (f := (Subgroup.inclusion hle))
        (Subgroup.inclusion_injective hle)
  have hrg : r g = 1 := by
    obtain ⟨n, hn⟩ := hsolv.solvable
    have h1 : r.rangeRestrict g ∈ (derivedSeries ↥(nsub Q x) n).map r.rangeRestrict :=
      Subgroup.mem_map_of_mem _ (mem_derivedSeries_of_mem_perfectResidual hg n)
    have h2 := map_derivedSeries_le_derivedSeries r.rangeRestrict n h1
    rw [hn, Subgroup.mem_bot] at h2
    exact congrArg Subtype.val h2
  have hfM : f ∈ isometryCentralizer Q x := supportedFixedDerived_le_isometryCentralizer hf
  have hjM : j ∈ isometryCentralizer Q x := iSup₂_le (fun h _ => iSup_le fun _ =>
    specialBlock_le_isometryCentralizer h) hj
  have hgM : (g : V ≃ₗ[K] V) ∈ isometryCentralizer Q x := hNM g.2
  have h4 : r g = isometryRestrictFixed Q x ⟨j, hjM⟩ * isometryRestrictFixed Q x ⟨f, hfM⟩ := by
    rw [← map_mul]
    exact congrArg (isometryRestrictFixed Q x) (Subtype.ext hgjf)
  rw [h4, hx.restrictFixed_trivial_of_mem_specialProduct hRep hj hjM, one_mul] at hrg
  have hfB := supportedFixedDerived_le_supportedBlock hf
  have h5 : restrictFixed Q x ⟨f, hfB⟩ = 1 := by
    rw [← isometryRestrictFixed_restrictFixed]
    exact hrg
  have hf1 : f = 1 := hx.eq_one_of_restrictFixed_eq_one hfB h5
  rw [hgjf, hf1, mul_one]
  exact hj

end Gen



section CentersSpecial

variable {K : Type} [Field K] [Finite K] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem eq_one_of_sq_eq_one_of_two_eq_zero {R : Type*} [CommRing R] [IsDomain R] (h2 : (2 : R) = 0)
    {c : R} (hc : c ^ 2 = 1) : c = 1 := by
  have h8 : (c - 1) ^ 2 = 0 := by
    have : (c - 1) ^ 2 = c ^ 2 - 1 - 2 * (c - 1) := by ring
    rw [this, hc, h2]
    ring
  exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h8)

omit [Finite K] in
theorem specialBlock_center_sq_paired [CharP K 2] (hx : OddOrderIsometry Q p x) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap)
    (hne : h ≠ reciprocalPolynomial h)
    (hm : 1 ≤ primaryMultiplicity x.toLinearMap h)
    {g : V ≃ₗ[K] V} (hg : g ∈ specialBlock Q x h)
    (hc : ∀ g' ∈ specialBlock Q x h, g * g' = g' * g) (hg2 : g ^ 2 = 1) : g = 1 := by
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
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hcen
  have hγ2 : (e₂ ⟨g, hg⟩) ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨g, hg⟩ : ↥(specialBlock Q x h)) ^ 2 = 1 := Subtype.ext hg2
    rw [this, map_one]
  have hmat : (Matrix.scalar (Fin m) r) ^ 2 = 1 := by
    rw [hr, ← Matrix.SpecialLinearGroup.coe_pow, hγ2]
    rfl
  have hr2 : r ^ 2 = 1 := by
    have := congrFun (congrFun hmat ⟨0, hm⟩) ⟨0, hm⟩
    rw [← map_pow] at this
    simpa [Matrix.scalar_apply] using this
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h2b : (2 : AdjoinRoot h) = 0 := by
    rw [← map_ofNat (algebraMap K (AdjoinRoot h)) 2, h2K, map_zero]
  have hr1 : r = 1 := eq_one_of_sq_eq_one_of_two_eq_zero h2b hr2
  have h1 : e₂ ⟨g, hg⟩ = 1 := by
    apply Subtype.ext
    rw [← hr, hr1, map_one]
    rfl
  have h2 : (⟨g, hg⟩ : ↥(specialBlock Q x h)) = 1 := e₂.injective (by rw [h1, map_one])
  exact congrArg Subtype.val h2

section SelfDual

open CFSG.LocalAnalysis.ComponentInitial

theorem specialBlock_center_sq_selfDual [CharP K 2] (hx : OddOrderIsometry Q p x)
    (hp : p.Prime) (hp3 : 3 < p) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) (hm : 2 ≤ primaryMultiplicity x.toLinearMap h)
    {g : V ≃ₗ[K] V}
    (hg : g ∈ specialBlock Q x h) (hc : ∀ g' ∈ specialBlock Q x h, g * g' = g' * g)
    (hg2 : g ^ 2 = 1) : g = 1 := by
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
  have hcp : c ^ 2 = 1 := by
    obtain ⟨v, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
      (primaryComponent_ne_bot hx.squarefree_minpoly hh)
    have hγp : γ ^ 2 = 1 := by
      rw [hγdef, ← map_pow]
      have : (⟨g, hg⟩ : ↥(specialBlock Q x h)) ^ 2 = 1 := Subtype.ext hg2
      rw [this, map_one]
    have h1 : ((γ ^ 2 : BlockGL x h) :
        Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) = LinearMap.id := by
      rw [hγp]
      rfl
    have hid : (LinearMap.id : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) ^ 2 =
        LinearMap.id := by
      rw [← Module.End.one_eq_id, one_pow]
    rw [Units.val_pow_eq_pow_val, hγ, _root_.smul_pow, hid] at h1
    have h2 := congrArg (fun T => T ⟨v, hv0.1⟩) h1
    simp only [LinearMap.smul_apply, LinearMap.id_apply] at h2
    have h3 : (c ^ 2 - 1) • (⟨v, hv0.1⟩ : primaryComponent x.toLinearMap h) = 0 := by
      rw [sub_smul, h2, one_smul, sub_self]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact sub_eq_zero.mp h4
    · exact absurd (congrArg Subtype.val h4) hv0.2
  have h2K : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h2b : (2 : AdjoinRoot h) = 0 := by
    rw [← map_ofNat (algebraMap K (AdjoinRoot h)) 2, h2K, map_zero]
  have hc1 : c = 1 := eq_one_of_sq_eq_one_of_two_eq_zero h2b hcp
  have hγ1 : γ = 1 := Units.ext (by rw [hγ, hc1, one_smul]; rfl)
  have h5 : (⟨g, hg⟩ : ↥(specialBlock Q x h)) = 1 :=
    hx.specialBlockGL_injective hh (by rw [← hγdef, hγ1, map_one])
  exact congrArg Subtype.val h5

end SelfDual
end CentersSpecial


section Commute

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem fixes_of_commute_listed (hx : OddOrderIsometry Q p x)
    (hQ : (polarBilin Q).Nondegenerate) (h3 : 3 ≤ finrank K (fixedSpace x))
    (hnexc : ¬ SmallFixedException (Q.comp (fixedSpace x).subtype))
    {g : V ≃ₗ[K] V} (hg : g ∈ isometryCentralizer Q x)
    (hcomm : ∀ f ∈ supportedFixedDerived Q x, ∀ v, g (f v) = f (g v)) :
    ∀ w ∈ fixedSpace x, g w = w := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hWnd := hx.polarBilin_fixed_nondegenerate
  obtain ⟨k, hk⟩ := hx.even_finrank_fixed
  have h4 : 4 ≤ finrank K (fixedSpace x) := by omega
  obtain ⟨e, he0, hQe⟩ := exists_singular_of_even_regular (Q.comp (fixedSpace x).subtype) hWnd
    (n := k) (by omega) (by omega)
  have hsing : ∃ e ∈ fixedSpace x, e ≠ 0 ∧ Q e = 0 :=
    ⟨e, e.2, fun h => he0 (Subtype.ext h), hQe⟩
  have hM : ElementaryMapsMem Q (fixedSpace x) :=
    elementaryMapsMem_of_regular hWnd h3 (fun hq2 hd4 U hU => by
      by_contra hcon
      push Not at hcon
      exact hnexc (Or.inr ⟨⟨hd4, U, hU, hcon⟩, Or.inl hq2⟩))
  have hgQ : ∀ v, Q (g.toAddEquiv v) = (1 : K) * (RingEquiv.refl K) (Q v) := fun v => by
    rw [one_mul]
    exact (mem_isometryCentralizer.mp hg).1 v
  have hcomm' : ∀ g' ∈ supportedDerived Q (fixedSpace x), ∀ v,
      g.toAddEquiv (g' v) = g' (g.toAddEquiv v) := fun g' hg' v =>
    hcomm g' (supportedDerived_le_supportedFixedDerived hx hg') v
  obtain ⟨-, c, hc0, hc⟩ := scalar_restriction_of_commute g.toAddEquiv (RingEquiv.refl K) 1 hgQ
    hcomm' hQ hWnd h3 hsing hM (fun c v => by simp)
  have : Nontrivial (fixedSpace x) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨w₁, hw₁⟩ := exists_map_ne_zero hWnd
  have hcc : c * c = 1 := by
    have h1 := (mem_isometryCentralizer.mp hg).1 (w₁ : V)
    have h5 : g (w₁ : V) = c • (w₁ : V) := hc w₁ w₁.2
    rw [h5, QuadraticMap.map_smul, smul_eq_mul] at h1
    have h6 : (Q.comp (fixedSpace x).subtype) w₁ = Q (w₁ : V) := rfl
    rw [h6] at hw₁
    exact mul_right_cancel₀ hw₁ (by rw [one_mul]; exact h1)
  have hc1 : c = 1 := by
    have h8 : (c - 1) ^ 2 = 0 := by
      have : (c - 1) ^ 2 = c * c - 1 - 2 * (c - 1) := by ring
      rw [this, hcc, h2]
      ring
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h8)
  intro w hw
  have h5 : g w = c • w := hc w hw
  rw [h5, hc1, one_smul]

theorem fixedFactor_center_eq_one (hx : OddOrderIsometry Q p x)
    (hQ : (polarBilin Q).Nondegenerate) (h3 : 3 ≤ finrank K (fixedSpace x))
    (hnexc : ¬ SmallFixedException (Q.comp (fixedSpace x).subtype)) {n : ℕ}
    {F : Fin n → Subgroup (V ≃ₗ[K] V)} (hsup : (⨆ i, F i) = supportedFixedDerived Q x)
    (hcomm : ∀ i j, i ≠ j → ∀ u ∈ F i, ∀ v ∈ F j, u * v = v * u) (i : Fin n)
    {z : V ≃ₗ[K] V} (hz : z ∈ F i) (hc : ∀ f ∈ F i, z * f = f * z) : z = 1 := by
  have hzS : z ∈ supportedFixedDerived Q x := hsup ▸ (le_iSup F i) hz
  have hzB : z ∈ supportedBlock Q x (X - 1) := supportedFixedDerived_le_supportedBlock hzS
  have hzM : z ∈ isometryCentralizer Q x := supportedBlock_le_isometryCentralizer _ hzB
  have hcent : (⨆ j, F j) ≤ Subgroup.centralizer ({z} : Set (V ≃ₗ[K] V)) :=
    iSup_le fun j => by
      intro v hv
      rw [Subgroup.mem_centralizer_singleton_iff]
      by_cases hji : j = i
      · subst hji
        exact (hc v hv).symm
      · exact (hcomm i j (Ne.symm hji) _ hz v hv).symm
  have hfix := fixes_of_commute_listed hx hQ h3 hnexc hzM (fun f hf v => by
    have := Subgroup.mem_centralizer_singleton_iff.mp (hcent (hsup ▸ hf))
    have h1 := congrArg (fun e : V ≃ₗ[K] V => e v) this
    exact h1.symm)
  refine hx.eq_one_of_restrictFixed_eq_one hzB ?_
  exact LinearEquiv.ext fun w => Subtype.ext (hfix w w.2)

end Commute

section Assembly

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem odd_card_center_of_forall_sq {F : Type*} [Group F] [Finite F]
    (h : ∀ z : F, (∀ f : F, z * f = f * z) → z ^ 2 = 1 → z = 1) :
    Odd (Nat.card ↥(Subgroup.center F)) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card ↥(Subgroup.center F) := by
    rw [Nat.not_odd_iff_even] at hodd
    exact even_iff_two_dvd.mp hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center F)) 2 h2
  have hz2 : z ^ 2 = 1 := by
    rw [← hz]
    exact pow_orderOf_eq_one z
  have hc : ∀ f : F, (z : F) * f = f * (z : F) := fun f => (Subgroup.mem_center_iff.mp z.2 f).symm
  have h1 : (z : F) = 1 := h z hc (by simpa using congrArg Subtype.val hz2)
  have : z = 1 := Subtype.ext h1
  rw [this, orderOf_one] at hz
  omega

theorem odd_card_center_specialBlock (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp3 : 3 < p)
    {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    Odd (Nat.card ↥(Subgroup.center ↥(specialBlock Q x h))) := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  refine odd_card_center_of_forall_sq fun z hzc hz2 => ?_
  have hc : ∀ g' ∈ specialBlock Q x h, (z : V ≃ₗ[K] V) * g' = g' * z := fun g' hg' =>
    congrArg Subtype.val (hzc ⟨g', hg'⟩)
  have hz2' : (z : V ≃ₗ[K] V) ^ 2 = 1 := congrArg Subtype.val hz2
  have : (z : V ≃ₗ[K] V) = 1 := by
    by_cases hself : h = reciprocalPolynomial h
    · exact specialBlock_center_sq_selfDual hx hp hp3 hh hne1 hself hm z.2 hc hz2'
    · exact specialBlock_center_sq_paired hx hh hself (by omega) z.2 hc hz2'
  exact Subtype.ext this

theorem exists_fixed_blocks (hQ : (polarBilin Q).Nondegenerate) (hx : OddOrderIsometry Q p x)
    (hp2 : Odd p) {Rep : Finset K[X]} (hRep : IsOrbitRepresentatives x Rep) :
    ∃ (n : ℕ) (F : Fin n → Subgroup (V ≃ₗ[K] V)),
      (∀ i, IsQuasisimple ↥(F i) ∧ F i ≤ supportedFixedDerived Q x ∧
        ((F i).subgroupOf (supportedFixedDerived Q x)).Normal ∧
        Odd (Nat.card ↥(Subgroup.center ↥(F i)))) ∧
      ∀ g ∈ perfectResidual ↥(nsub Q x),
        (g : V ≃ₗ[K] V) ∈ specialProduct Q x Rep ⊔ ⨆ i, F i := by
  by_cases hlist : 3 ≤ finrank K (fixedSpace x) ∧
      ¬ SmallFixedException (Q.comp (fixedSpace x).subtype)
  · have hcov := (orthogonal_regular_space_coverage (Q.comp (fixedSpace x).subtype)
      hx.polarBilin_fixed_nondegenerate hlist.1).2 hlist.2
    obtain ⟨n, F, -, -, hsup, hF, hcomm, -⟩ := hx.exists_supported_factors hcov
    refine ⟨n, F, fun i => ⟨(hF i).1, (hF i).2.1, (hF i).2.2, ?_⟩, fun g hg => ?_⟩
    · refine odd_card_center_of_forall_sq fun z hzc _ => Subtype.ext ?_
      exact fixedFactor_center_eq_one hx hQ hlist.1 hlist.2 hsup hcomm i z.2
        (fun f hf => congrArg Subtype.val (hzc ⟨f, hf⟩))
    · obtain ⟨f, hf, j, hj, hgjf⟩ := perfectResidual_nsub_decomp hx hRep hg
      rw [hgjf]
      exact Subgroup.mul_mem_sup hj (hsup ▸ hf)
  · refine ⟨0, fun i => i.elim0, fun i => i.elim0, fun g hg => ?_⟩
    have := perfectResidual_nsub_unlisted hQ hx hp2 hRep hlist hg
    exact (le_sup_left : specialProduct Q x Rep ≤ _) this

end Assembly



section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem odd_card_center_subgroupOf {G : Type*} [Group G] {N F : Subgroup G} (hFN : F ≤ N)
    (h : Odd (Nat.card ↥(Subgroup.center ↥F))) :
    Odd (Nat.card ↥(Subgroup.center ↥(F.subgroupOf N))) := by
  let e : ↥(F.subgroupOf N) ≃* ↥F := Subgroup.subgroupOfEquivOfLe hFN
  have hc : Nat.card ↥(Subgroup.center ↥(F.subgroupOf N)) = Nat.card ↥(Subgroup.center ↥F) := by
    rw [← Subgroup.map_center_eq e]
    exact (Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective).symm
  rwa [hc]

theorem oddRad_nsub (hQ : (polarBilin Q).Nondegenerate) (xΩ : orthDerived Q)
    (hxo : orderOf xΩ = 5) :
    Odd (Nat.card ↥(solvableRadical ↥(perfectResidual ↥(nsub Q (xΩ : V ≃ₗ[K] V))))) := by
  classical
  have hp : Nat.Prime 5 := by norm_num
  have hp3 : 3 < 5 := by norm_num
  have hp2 : Odd 5 := by decide
  have hpl : (5 : ℕ) ≠ ringChar K := by rw [ringChar.eq K 2]; norm_num
  set xe : V ≃ₗ[K] V := (xΩ : V ≃ₗ[K] V) with hxe
  have hx : OddOrderIsometry Q 5 xe := oddOrderIsometry_of_orthDerived hp hpl hQ xΩ hxo
  obtain ⟨Rep, hRep⟩ := hx.exists_orbitRepresentatives
  obtain ⟨n, F, hF, hFgen⟩ := exists_fixed_blocks hQ hx hp2 hRep
  set N := nsub Q xe with hN
  let Rep' : Finset K[X] :=
    Rep.filter (fun h => h ≠ X - 1 ∧ 2 ≤ primaryMultiplicity xe.toLinearMap h)
  have hRep'mem : ∀ {h : K[X]}, h ∈ Rep' →
      h ∈ Rep ∧ h ≠ X - 1 ∧ 2 ≤ primaryMultiplicity xe.toLinearMap h := fun {h} hh => by
    have := Finset.mem_filter.mp hh
    exact ⟨this.1, this.2.1, this.2.2⟩
  let blk : {h : K[X] // h ∈ Rep'} ⊕ Fin n → Subgroup (V ≃ₗ[K] V) :=
    Sum.elim (fun h => specialBlock Q xe h.1) F
  have hbN : ∀ i, blk i ≤ N := by
    rintro (⟨h, hh⟩ | i)
    · obtain ⟨hhR, hne, hm⟩ := hRep'mem hh
      exact le_inf (specialBlock_le_isometryCentralizer h)
        (hx.specialBlock_le_orthDerived hp hp3 (hRep.1 hhR) hne hm)
    · exact le_inf ((hF i).2.1.trans supportedFixedDerived_le_isometryCentralizer)
        ((hF i).2.1.trans hx.supportedFixedDerived_le_orthDerived)
  have hbq : ∀ i, IsQuasisimple ↥(blk i) := by
    rintro (⟨h, hh⟩ | i)
    · obtain ⟨hhR, hne, hm⟩ := hRep'mem hh
      exact hx.quasisimple_specialBlock hp hp3 (hRep.1 hhR) hne hm
    · exact (hF i).1
  have hbodd : ∀ i, Odd (Nat.card ↥(Subgroup.center ↥(blk i))) := by
    rintro (⟨h, hh⟩ | i)
    · obtain ⟨hhR, hne, hm⟩ := hRep'mem hh
      exact odd_card_center_specialBlock hx hp hp3 (hRep.1 hhR) hne hm
    · exact (hF i).2.2.2
  refine odd_card_radical_perfectResidual_of_blocks (fun i => (blk i).subgroupOf N) ?_ ?_ ?_ ?_
  · exact fun i => isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (hbN i)).symm (hbq i)
  · rintro (⟨h, hh⟩ | i)
    · show (((specialBlock Q xe h).subgroupOf N).subgroupOf (perfectResidual ↥N)).IsSubnormal
      have hnorm : ((specialBlock Q xe h).subgroupOf N).Normal := by
        rw [Subgroup.normal_subgroupOf_iff
          (show specialBlock Q xe h ≤ N from hbN (Sum.inl ⟨h, hh⟩))]
        intro f k hf hk
        exact conj_mem_specialBlock (Subgroup.mem_inf.mp hk).1 hf
      exact (inferInstance : (((specialBlock Q xe h).subgroupOf N).subgroupOf
        (perfectResidual ↥N)).Normal).isSubnormal
    · show (((F i).subgroupOf N).subgroupOf (perfectResidual ↥N)).IsSubnormal
      have hFΩ : F i ≤ supportedFixedDerived Q xe := (hF i).2.1
      have hΩN : supportedFixedDerived Q xe ≤ N :=
        le_inf supportedFixedDerived_le_isometryCentralizer hx.supportedFixedDerived_le_orthDerived
      have hK2norm : ((supportedFixedDerived Q xe).subgroupOf N).Normal := by
        rw [Subgroup.normal_subgroupOf_iff hΩN]
        intro f k hf hk
        exact hx.conj_mem_supportedFixedDerived (Subgroup.mem_inf.mp hk).1 hf
      have hK1K2 : (F i).subgroupOf N ≤ (supportedFixedDerived Q xe).subgroupOf N :=
        fun g hg => hFΩ hg
      have hK1norm : (((F i).subgroupOf N).subgroupOf
          ((supportedFixedDerived Q xe).subgroupOf N)).Normal := by
        rw [Subgroup.normal_subgroupOf_iff hK1K2]
        intro h k hh hk
        have := (Subgroup.normal_subgroupOf_iff hFΩ).mp (hF i).2.2.1 (h : V ≃ₗ[K] V)
          (k : V ≃ₗ[K] V) (Subgroup.mem_subgroupOf.mp hh) (Subgroup.mem_subgroupOf.mp hk)
        exact Subgroup.mem_subgroupOf.mpr this
      exact (Subgroup.IsSubnormal.step _ _ hK1K2 hK2norm.isSubnormal hK1norm).comap _
  · intro g hg
    have hsup : (⨆ i, blk i) = (⨆ h : {h : K[X] // h ∈ Rep'}, specialBlock Q xe h.1) ⊔
        ⨆ i, F i := iSup_sum
    have hsp : specialProduct Q xe Rep ≤ ⨆ h : {h : K[X] // h ∈ Rep'}, specialBlock Q xe h.1 := by
      refine iSup₂_le fun h hh => iSup_le fun hne => ?_
      by_cases hm : 2 ≤ primaryMultiplicity xe.toLinearMap h
      · exact le_iSup (fun h : {h : K[X] // h ∈ Rep'} => specialBlock Q xe h.1)
          ⟨h, Finset.mem_filter.mpr ⟨hh, hne, hm⟩⟩
      · have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors (hRep.1 hh)⟩
        have hpos := hx.primaryMultiplicity_pos (hRep.1 hh)
        have h1 : primaryMultiplicity xe.toLinearMap h = 1 := by omega
        rw [hx.specialBlock_eq_bot_of_finrank_eq_one (hRep.1 hh) h1]
        exact bot_le
    have h1 := hFgen g hg
    have h2 : (g : V ≃ₗ[K] V) ∈ ⨆ i, blk i := by
      rw [hsup]
      exact sup_le_sup_right hsp _ h1
    have h3 : g ∈ (⨆ i, blk i).subgroupOf N := h2
    rwa [subgroupOf_iSup_of_le blk N hbN] at h3
  · exact fun i => odd_card_center_subgroupOf (hbN i) (hbodd i)

end Main

end CFSG.RankThree.PartOne.F106.OddRadOrth
