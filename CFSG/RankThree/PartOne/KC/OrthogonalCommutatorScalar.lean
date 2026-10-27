module

public import CFSG.RankThree.PartOne.KC.OrthogonalBlockQuasisimple
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeLinear
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeGroup

public section

namespace CFSG.RankThree.PartOne.KCOrthComm

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCUnitary CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Universal.Unitary

variable {K : Type} [Field K] [Finite K] {V : Type*} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {xe : V ≃ₗ[K] V}

omit [Finite K] in
theorem exists_smul_of_commute_paired (hx : OddOrderIsometry Q p xe) {h : K[X]}
    (hh : h ∈ primaryFactors xe.toLinearMap) (hne : h ≠ reciprocalPolynomial h)
    (hm : 2 ≤ primaryMultiplicity xe.toLinearMap h) {M : V ≃ₗ[K] V}
    (hMc : M ∈ Subgroup.centralizer ({xe} : Set (V ≃ₗ[K] V)))
    (hMF : ∀ f ∈ specialBlock Q xe h, ∀ v, M (f v) = f (M v)) :
    ∃ c : AdjoinRoot h, ∀ v : primaryComponent xe.toLinearMap h,
      M (v : V) = ((c • v : primaryComponent xe.toLinearMap h) : V) := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have key : ∀ δ : LinearMap.GeneralLinearGroup (AdjoinRoot h) (primaryComponent xe.toLinearMap h),
      LinearMap.det (δ : Module.End (AdjoinRoot h) (primaryComponent xe.toLinearMap h)) = 1 →
      Commute ((centralizerGL xe h ⟨M, hMc⟩ : BlockGL xe h) :
        Module.End (AdjoinRoot h) (primaryComponent xe.toLinearMap h))
        (δ : Module.End (AdjoinRoot h) (primaryComponent xe.toLinearMap h)) := by
    intro δ hδ
    obtain ⟨g, hg⟩ := hx.blockGL_surjective_paired hh hne δ
    have hdet : blockDet Q xe h g = 1 := by
      rw [blockDet_apply, hg]
      exact hδ
    have hgF : (g : V ≃ₗ[K] V) ∈ specialBlock Q xe h := mem_specialBlock.mpr ⟨g.2, hdet⟩
    have hcomm := hMF g hgF
    refine LinearMap.ext fun w => Subtype.ext ?_
    have hδw : ∀ w : primaryComponent xe.toLinearMap h,
        (((δ : Module.End (AdjoinRoot h) (primaryComponent xe.toLinearMap h)) w :
          primaryComponent xe.toLinearMap h) : V) = (g : V ≃ₗ[K] V) (w : V) := by
      intro w
      rw [← hg]
      exact coe_blockGL h g w
    change (((centralizerGL xe h ⟨M, hMc⟩ : BlockGL xe h) :
        Module.End (AdjoinRoot h) (primaryComponent xe.toLinearMap h))
        ((δ : Module.End (AdjoinRoot h) (primaryComponent xe.toLinearMap h)) w) : V) =
      (((δ : Module.End (AdjoinRoot h) (primaryComponent xe.toLinearMap h))
        (((centralizerGL xe h ⟨M, hMc⟩ : BlockGL xe h) :
          Module.End (AdjoinRoot h) (primaryComponent xe.toLinearMap h)) w) : _) : V)
    rw [coe_centralizerGL, hδw, hδw, coe_centralizerGL]
    exact hcomm w
  obtain ⟨c, hc⟩ := exists_smul_of_commute_special_linear (E := AdjoinRoot h) hm
    ((centralizerGL xe h ⟨M, hMc⟩ : BlockGL xe h) :
      Module.End (AdjoinRoot h) (primaryComponent xe.toLinearMap h)) key
  refine ⟨c, fun v => ?_⟩
  have := congrArg Subtype.val (hc v)
  rw [coe_centralizerGL] at this
  exact this

theorem exists_selfDual_unitary (hx : OddOrderIsometry Q p xe) (hp : p.Prime)
    (hp3 : 3 < p) {h : K[X]} [Fact (Irreducible h)] (hh : h ∈ primaryFactors xe.toLinearMap)
    (hne1 : h ≠ X - 1) (hself : h = reciprocalPolynomial h) :
    ∃ (ℓ f : ℕ) (hU : UnitaryFieldData ℓ f (AdjoinRoot h))
      (B : primaryComponent xe.toLinearMap h →ₛₗ[hU.bar] primaryComponent xe.toLinearMap h →ₗ[
        AdjoinRoot h] AdjoinRoot h),
      B.IsSymm ∧ B.SeparatingLeft ∧ 4 ≤ ℓ ^ f ∧
        (specialBlockGL Q xe h).range = sesqSpecialUnitaryGroup B := by
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
  let B : primaryComponent xe.toLinearMap h →ₛₗ[hU.bar]
      primaryComponent xe.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h :=
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
  have hrange : (specialBlockGL Q xe h).range = sesqSpecialUnitaryGroup B := by
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
  exact ⟨ℓ, f * d, hU, B, hBsymm, hBl, hq4, hrange⟩

theorem exists_smul_of_commute_selfDual (hx : OddOrderIsometry Q p xe)
    (hp : p.Prime) (hp3 : 3 < p) {h : K[X]} (hh : h ∈ primaryFactors xe.toLinearMap)
    (hne1 : h ≠ X - 1) (hself : h = reciprocalPolynomial h)
    (hm : 2 ≤ primaryMultiplicity xe.toLinearMap h) {M : V ≃ₗ[K] V}
    (hMc : M ∈ Subgroup.centralizer ({xe} : Set (V ≃ₗ[K] V)))
    (hMF : ∀ f ∈ specialBlock Q xe h, ∀ v, M (f v) = f (M v)) :
    ∃ c : AdjoinRoot h, ∀ v : primaryComponent xe.toLinearMap h,
      M (v : V) = ((c • v : primaryComponent xe.toLinearMap h) : V) := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  obtain ⟨ℓ, f, hU, B, hBs, hBl, hq4, hrange⟩ := exists_selfDual_unitary hx hp hp3 hh hne1 hself
  have key : ∀ δ ∈ sesqSpecialUnitaryGroup B,
      Commute ((centralizerGL xe h ⟨M, hMc⟩ : BlockGL xe h) :
        Module.End (AdjoinRoot h) (primaryComponent xe.toLinearMap h))
        (δ : Module.End (AdjoinRoot h) (primaryComponent xe.toLinearMap h)) := by
    intro δ hδ
    rw [← hrange] at hδ
    obtain ⟨g, hg⟩ := hδ
    have hcomm := hMF g.1 g.2
    refine LinearMap.ext fun w => Subtype.ext ?_
    have hδw : ∀ w : primaryComponent xe.toLinearMap h,
        (((δ : Module.End (AdjoinRoot h) (primaryComponent xe.toLinearMap h)) w :
          primaryComponent xe.toLinearMap h) : V) = (g : V ≃ₗ[K] V) (w : V) := by
      intro w
      rw [← hg]
      exact coe_blockGL h ⟨g.1, specialBlock_le_supportedBlock h g.2⟩ w
    change (((centralizerGL xe h ⟨M, hMc⟩ : BlockGL xe h) :
        Module.End (AdjoinRoot h) (primaryComponent xe.toLinearMap h))
        ((δ : Module.End (AdjoinRoot h) (primaryComponent xe.toLinearMap h)) w) : V) =
      (((δ : Module.End (AdjoinRoot h) (primaryComponent xe.toLinearMap h))
        (((centralizerGL xe h ⟨M, hMc⟩ : BlockGL xe h) :
          Module.End (AdjoinRoot h) (primaryComponent xe.toLinearMap h)) w) : _) : V)
    rw [coe_centralizerGL, hδw, hδw, coe_centralizerGL]
    exact hcomm w
  obtain ⟨c, hc⟩ := exists_smul_of_commute_special_unitary hU hBs hBl hm (by omega)
    ((centralizerGL xe h ⟨M, hMc⟩ : BlockGL xe h) :
      Module.End (AdjoinRoot h) (primaryComponent xe.toLinearMap h)) key
  refine ⟨c, fun v => ?_⟩
  have := congrArg Subtype.val (hc v)
  rw [coe_centralizerGL] at this
  exact this

omit [Finite K] in
theorem exists_blockScalar_of_mult_one {h : K[X]} [Fact (Irreducible h)]
    (hm : primaryMultiplicity xe.toLinearMap h = 1) {M : V ≃ₗ[K] V}
    (hMx : ∀ v, M (xe v) = xe (M v)) :
    ∃ f : K[X], ∀ v ∈ primaryComponent xe.toLinearMap h,
      M v = aeval xe.toLinearMap f v := by
  have hMc : M ∈ Subgroup.centralizer ({xe} : Set (V ≃ₗ[K] V)) := (mem_centralizer_iff xe).mpr hMx
  obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one
    (R := AdjoinRoot h) (M := primaryComponent xe.toLinearMap h) hm
    ((centralizerGL xe h ⟨M, hMc⟩ : BlockGL xe h) :
      Module.End (AdjoinRoot h) (primaryComponent xe.toLinearMap h))
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective c
  refine ⟨f, fun v hv => ?_⟩
  have := congrArg (fun γ : Module.End (AdjoinRoot h) (primaryComponent xe.toLinearMap h) =>
    ((γ ⟨v, hv⟩ : primaryComponent xe.toLinearMap h) : V)) hc
  rw [coe_centralizerGL] at this
  simpa using this

theorem exists_blockScalar (hx : OddOrderIsometry Q p xe) (hp : p.Prime)
    (hp3 : 3 < p) {h : K[X]} (hh : h ∈ primaryFactors xe.toLinearMap) (hne1 : h ≠ X - 1)
    {M : V ≃ₗ[K] V} (hMx : ∀ v, M (xe v) = xe (M v))
    (hMF : ∀ f ∈ specialBlock Q xe h, ∀ v, M (f v) = f (M v)) :
    ∃ f : K[X], ∀ v ∈ primaryComponent xe.toLinearMap h,
      M v = aeval xe.toLinearMap f v := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hMc : M ∈ Subgroup.centralizer ({xe} : Set (V ≃ₗ[K] V)) := (mem_centralizer_iff xe).mpr hMx
  have hpos : 1 ≤ primaryMultiplicity xe.toLinearMap h := by
    have hne : primaryComponent xe.toLinearMap h ≠ ⊥ :=
      primaryComponent_ne_bot hx.squarefree_minpoly hh
    have : Nontrivial (primaryComponent xe.toLinearMap h) :=
      Submodule.nontrivial_iff_ne_bot.mpr hne
    exact Module.finrank_pos
  obtain ⟨c, hc⟩ : ∃ c : AdjoinRoot h, ∀ v : primaryComponent xe.toLinearMap h,
      M (v : V) = ((c • v : primaryComponent xe.toLinearMap h) : V) := by
    rcases Nat.lt_or_ge (primaryMultiplicity xe.toLinearMap h) 2 with hm | hm
    · have h1 : primaryMultiplicity xe.toLinearMap h = 1 := by omega
      obtain ⟨f, hf⟩ := exists_blockScalar_of_mult_one h1 hMx
      refine ⟨AdjoinRoot.mk h f, fun v => ?_⟩
      rw [coe_mk_smul_primaryComponent]
      exact hf v v.2
    · by_cases hself : h = reciprocalPolynomial h
      · exact exists_smul_of_commute_selfDual hx hp hp3 hh hne1 hself hm hMc hMF
      · exact exists_smul_of_commute_paired hx hh hself hm hMc hMF
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective c
  refine ⟨f, fun v hv => ?_⟩
  have := hc ⟨v, hv⟩
  rw [coe_mk_smul_primaryComponent] at this
  exact this

end CFSG.RankThree.PartOne.KCOrthComm
