module

public import CFSG.RankThree.PartOne.KC.SymplecticIsotypicBlocks
public import CFSG.RankThree.PartOne.KC.OrthogonalComponentFacts
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorScalar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

section Symplectic

open Polynomial CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCSpIsotypic
open CFSG.Open (StatedSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

theorem k329kc3_spBlockFacts_of_spPaired {r : ℕ} {K : Type} [Field K] {ℓ f p : ℕ}
    (hq : 2 ≤ ℓ ^ f) (hpq : 3 ≤ p ∨ 4 ≤ ℓ ^ f) {x : StatedSp r K}
    {h : primaryFactors (spEnd x)} (hP : SpPairedBlock ℓ f p x h) :
    SpBlockFacts (spForm r K) (spLin r K x) h := by
  obtain ⟨φ, hφ, -⟩ := hP.factor
  refine spBlockFacts_of_paired ((spOrbitEquiv x rfl).trans φ) (fun g v hv => ?_) ?_
  · rw [MulEquiv.trans_apply, hφ, spEnd_orbitEquiv]
  · have hdeg : 1 ≤ (h : K[X]).natDegree :=
      Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors h.2)
    have hN : ℓ ^ f ≤ (ℓ ^ f) ^ (h : K[X]).natDegree := Nat.le_self_pow (by omega) _
    have hle := Nat.le_of_dvd (by omega) hP.dvd
    have hcard : 4 ≤ Nat.card (AdjoinRoot (h : K[X])) := by
      rw [hP.card_field]
      omega
    have : Finite (AdjoinRoot (h : K[X])) := Nat.finite_of_card_ne_zero (by omega)
    exact exists_finset_card_four_of_card hcard

theorem k329kc3_spBlockFacts_of_spSelfDual {r : ℕ} {K : Type} [Field K] {ℓ f p : ℕ}
    (hq : 4 ≤ ℓ ^ f) {x : StatedSp r K} {h : primaryFactors (spEnd x)}
    (hself : reciprocalPolynomial (h : K[X]) = h) (hS : SpSelfDualBlock ℓ f p x h) :
    SpBlockFacts (spForm r K) (spLin r K x) h := by
  obtain ⟨d, hdeg, -, _σ, -, -, -, -, -, hE, -, Hf, hHf, hHfl, -, -, φ, hφ⟩ := hS.exists_half
  have hO : ({(h : K[X]), reciprocalPolynomial (h : K[X])} : Set K[X]) = {(h : K[X])} := by
    rw [hself, Set.pair_eq_singleton]
  refine spBlockFacts_of_selfDual hE hHf hHfl ((spOrbitEquiv x hO).trans φ) (fun g v hv => ?_) ?_
  · rw [MulEquiv.trans_apply]
    have := hφ (spOrbitEquiv x hO g) v hv
    rw [this, spEnd_orbitEquiv]
  · have hd : d ≠ 0 := by
      have := Irreducible.natDegree_pos (irreducible_of_mem_primaryFactors h.2)
      omega
    rw [pow_mul]
    exact hq.trans (Nat.le_self_pow hd _)

theorem k329kc3_spBlockFacts {r : ℕ} {K : Type} [Field K] {ℓ f p : ℕ} {x : StatedSp r K}
    (hq : 3 < ℓ ^ f) (hK : Nat.card K = ℓ ^ f) (hsq : Squarefree (minpoly K (spEnd x)))
    (blocks : SpPrimaryBlocks ℓ f p x (proj r K x)) (h : primaryFactors (spEnd x)) :
    SpBlockFacts (spForm r K) (spLin r K x) h := by
  by_cases h1 : (h : K[X]) = X - 1
  · obtain ⟨h0, hm⟩ := h
    change h0 = X - 1 at h1
    subst h1
    exact spBlockFacts_of_spFixed hsq blocks hm (Or.inl (by omega))
  · by_cases h2 : reciprocalPolynomial (h : K[X]) = h
    · exact k329kc3_spBlockFacts_of_spSelfDual (by omega) h2 (blocks.selfDual h h1 h2)
    · exact k329kc3_spBlockFacts_of_spPaired (by omega) (Or.inr (by omega))
        (blocks.paired h (Ne.symm h2))

end Symplectic

section Orthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial

theorem k329kc3_isQuasisimple_specialBlock_paired {K : Type*} {V : Type*} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hne : h ≠ reciprocalPolynomial h) (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    CFSG.IsQuasisimple ↥(specialBlock Q x h) := by
  have h4 : 4 ≤ Nat.card (AdjoinRoot h) := by
    have := hx.p_lt_card_adjoinRoot hp hh hne1
    have := hp.two_le
    omega
  let b : Module.Basis (Fin (primaryMultiplicity x.toLinearMap h)) (AdjoinRoot h)
      (primaryComponent x.toLinearMap h) := Module.finBasisOfFinrankEq _ _ rfl
  let e₁ : ↥(specialBlock Q x h) ≃*
      SpecialLinearGroup (AdjoinRoot h) (primaryComponent x.toLinearMap h) :=
    MulEquiv.ofBijective (specialToSL Q x h)
      ⟨hx.specialToSL_injective hh, hx.specialToSL_surjective_paired hh hne⟩
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((Matrix.SpecialLinearGroup.toLin_equiv b).trans e₁.symm)
    (CFSG.RankThree.CALinearPlane.isQuasisimple_SL_of_two_le hm h4)

theorem k329kc3_exists_selfDual_unitary {K : Type} [Field K] [Finite K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {xe : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p xe) (hp2 : Odd p) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors xe.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) :
    ∃ (ℓ f : ℕ) (hU : UnitaryFieldData ℓ f (AdjoinRoot h))
      (B : primaryComponent xe.toLinearMap h →ₛₗ[hU.bar] primaryComponent xe.toLinearMap h →ₗ[
        AdjoinRoot h] AdjoinRoot h),
      B.IsSymm ∧ B.SeparatingLeft ∧ Nat.card K ≤ ℓ ^ f ∧
        (specialBlockGL Q xe h).range = sesqSpecialUnitaryGroup B := by
  classical
  have hirr := irreducible_of_mem_primaryFactors hh
  obtain ⟨d, H, hdeg, -, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2 hh hne1 hself
  have hd : finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  obtain ⟨ℓ, f, hU, hq, hbar⟩ :=
    CFSG.RankThree.PartOne.KCOrthogonal.exists_unitaryFieldData K (AdjoinRoot h) hd
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
  have hd0 : d ≠ 0 := by
    have := hirr.natDegree_pos
    omega
  have hle : Nat.card K ≤ ℓ ^ (f * d) := by
    rw [pow_mul, ← hq]
    exact Nat.le_self_pow hd0 _
  exact ⟨ℓ, f * d, hU, B, hBsymm, hBl, hle, hrange⟩

theorem k329kc3_isQuasisimple_specialBlock_selfDual {K : Type} {V : Type*} [Field K] [Finite K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) (hp2 : Odd p) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) (hm : 2 ≤ primaryMultiplicity x.toLinearMap h)
    (hq : (primaryMultiplicity x.toLinearMap h = 2 → 4 ≤ Nat.card K) ∧
      (primaryMultiplicity x.toLinearMap h = 3 → 3 ≤ Nat.card K)) :
    CFSG.IsQuasisimple ↥(specialBlock Q x h) := by
  obtain ⟨ℓ, f, hU, B, hBsymm, hBl, hle, hrange⟩ :=
    k329kc3_exists_selfDual_unitary hx hp2 hh hne1 hself
  let e₁ : ↥(specialBlock Q x h) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
      (MulEquiv.subgroupCongr hrange)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e₁.symm
    (CFSG.RankThree.PartOne.KCUnitary.isQuasisimple_sesqSpecialUnitaryGroup_of_two_le hU hBsymm
      hBl hm ⟨fun h2 => (hq.1 h2).trans hle, fun h3 => (hq.2 h3).trans hle⟩)

theorem k329kc3_quasisimple_specialBlock {K : Type} [Field K] [Finite K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h)
    (hq : (primaryMultiplicity x.toLinearMap h = 2 → 4 ≤ Nat.card K) ∧
      (primaryMultiplicity x.toLinearMap h = 3 → 3 ≤ Nat.card K)) :
    CFSG.IsQuasisimple ↥(specialBlock Q x h) := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  by_cases hself : h = reciprocalPolynomial h
  · exact k329kc3_isQuasisimple_specialBlock_selfDual hx (hp.odd_of_ne_two hp2) hh hne1 hself hm
      hq
  · exact k329kc3_isQuasisimple_specialBlock_paired hx hp hp2 hh hne1 hself hm

theorem k329kc3_specialBlock_le_orthDerived {K : Type} [Field K] [Finite K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {x : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h)
    (hq : (primaryMultiplicity x.toLinearMap h = 2 → 4 ≤ Nat.card K) ∧
      (primaryMultiplicity x.toLinearMap h = 3 → 3 ≤ Nat.card K)) :
    specialBlock Q x h ≤ orthDerived Q :=
  specialBlock_le_orthDerived_of_perfect (k329kc3_quasisimple_specialBlock hx hp hp2 hh hne1 hm hq).1
    ((specialBlock_le_isometryCentralizer h).trans (fun _ hg => (Subgroup.mem_inf.mp hg).1))

theorem k329kc3_exists_smul_of_commute_selfDual {K : Type} [Field K] [Finite K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {xe : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p xe) (hp2 : Odd p) {h : K[X]}
    (hh : h ∈ primaryFactors xe.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) (hm : 2 ≤ primaryMultiplicity xe.toLinearMap h)
    {M : V ≃ₗ[K] V} (hMc : M ∈ Subgroup.centralizer ({xe} : Set (V ≃ₗ[K] V)))
    (hMF : ∀ f ∈ specialBlock Q xe h, ∀ v, M (f v) = f (M v)) :
    ∃ c : AdjoinRoot h, ∀ v : primaryComponent xe.toLinearMap h,
      M (v : V) = ((c • v : primaryComponent xe.toLinearMap h) : V) := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  obtain ⟨ℓ, f, hU, B, hBs, hBl, hle, hrange⟩ :=
    k329kc3_exists_selfDual_unitary hx hp2 hh hne1 hself
  have hq2 : 2 ≤ ℓ ^ f := by
    have := Finite.one_lt_card (α := K)
    omega
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
      exact CFSG.RankThree.PartOne.KCOrthogonal.coe_blockGL h
        ⟨g.1, specialBlock_le_supportedBlock h g.2⟩ w
    change (((centralizerGL xe h ⟨M, hMc⟩ : BlockGL xe h) :
        Module.End (AdjoinRoot h) (primaryComponent xe.toLinearMap h))
        ((δ : Module.End (AdjoinRoot h) (primaryComponent xe.toLinearMap h)) w) : V) =
      (((δ : Module.End (AdjoinRoot h) (primaryComponent xe.toLinearMap h))
        (((centralizerGL xe h ⟨M, hMc⟩ : BlockGL xe h) :
          Module.End (AdjoinRoot h) (primaryComponent xe.toLinearMap h)) w) : _) : V)
    rw [coe_centralizerGL, hδw, hδw, coe_centralizerGL]
    exact hcomm w
  obtain ⟨c, hc⟩ := CFSG.RankThree.PartOne.KCUnitary.exists_smul_of_commute_special_unitary hU
    hBs hBl hm hq2
    ((centralizerGL xe h ⟨M, hMc⟩ : BlockGL xe h) :
      Module.End (AdjoinRoot h) (primaryComponent xe.toLinearMap h)) key
  refine ⟨c, fun v => ?_⟩
  have := congrArg Subtype.val (hc v)
  rw [coe_centralizerGL] at this
  exact this

theorem k329kc3_exists_blockScalar {K : Type} [Field K] [Finite K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {xe : V ≃ₗ[K] V} (hx : OddOrderIsometry Q p xe) (hp2 : Odd p) {h : K[X]}
    (hh : h ∈ primaryFactors xe.toLinearMap) (hne1 : h ≠ X - 1) {M : V ≃ₗ[K] V}
    (hMx : ∀ v, M (xe v) = xe (M v))
    (hMF : ∀ f ∈ specialBlock Q xe h, ∀ v, M (f v) = f (M v)) :
    ∃ f : K[X], ∀ v ∈ primaryComponent xe.toLinearMap h,
      M v = aeval xe.toLinearMap f v := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hMc : M ∈ Subgroup.centralizer ({xe} : Set (V ≃ₗ[K] V)) :=
    (CFSG.RankThree.PartOne.KCOrthogonal.mem_centralizer_iff xe).mpr hMx
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
      obtain ⟨f, hf⟩ := CFSG.RankThree.PartOne.KCOrthComm.exists_blockScalar_of_mult_one h1 hMx
      refine ⟨AdjoinRoot.mk h f, fun v => ?_⟩
      rw [coe_mk_smul_primaryComponent]
      exact hf v v.2
    · by_cases hself : h = reciprocalPolynomial h
      · exact k329kc3_exists_smul_of_commute_selfDual hx hp2 hh hne1 hself hm hMc hMF
      · exact CFSG.RankThree.PartOne.KCOrthComm.exists_smul_of_commute_paired hx hh hself hm hMc
          hMF
  obtain ⟨f, rfl⟩ := AdjoinRoot.mk_surjective c
  refine ⟨f, fun v hv => ?_⟩
  have := hc ⟨v, hv⟩
  rw [coe_mk_smul_primaryComponent] at this
  exact this

end Orthogonal

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
