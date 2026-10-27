module

public import CFSG.RankThree.PartOne.KC.OrthogonalBlockScalar
public import CFSG.RankThree.SteinbergR3ECALinearSplitBlocks
public import CFSG.LieType.Universal.Unitary.Clause0

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

section Unitary

open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg

theorem isQuasisimple_sesqSpecialUnitaryGroup_of_three_le {ℓ f : ℕ} {K : Type} [Field K]
    (h : UnitaryFieldData ℓ f K) {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hn : 3 ≤ Module.finrank K V) (hnq : (Module.finrank K V, ℓ ^ f) ≠ (3, 2)) :
    CFSG.IsQuasisimple (sesqSpecialUnitaryGroup B) := by
  have := h.finite
  have : Fact ℓ.Prime := ⟨h.prime⟩
  have := h.charP
  have hK := card_eq_sq_of_unitaryFieldData h
  obtain ⟨e₀, he₀⟩ := h.exists_orthonormal_basis hB hBl
  obtain ⟨e₁⟩ := CFSG.RankThree.CentralLiftU.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SUid h e₀ he₀
  rw [CFSG.RankThree.CentralLiftU.barEquiv_eq_unitaryInvolution h] at e₁
  obtain ⟨P, hP⟩ := exists_wittMatrix hK (Module.finrank K V)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (e₁.trans (conjEquiv P hP).symm).symm
    (isQuasisimple_SU hK hn hnq)

end Unitary

section Generic

variable {K : Type*} {V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.specialBlockGL_injective (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) : Function.Injective (specialBlockGL Q x h) := by
  intro g g' hgg
  have hinj := hx.blockGL_injective hh
  have h2 : (⟨g.1, specialBlock_le_supportedBlock h g.2⟩ : ↥(supportedBlock Q x h)) =
      ⟨g'.1, specialBlock_le_supportedBlock h g'.2⟩ := hinj hgg
  have h3 : g.1 = g'.1 := congrArg (fun y : ↥(supportedBlock Q x h) => y.1) h2
  exact Subtype.ext h3

omit [FiniteDimensional K V] in
theorem range_specialBlockGL (h : K[X]) :
    (specialBlockGL Q x h).range = (blockGL Q x h).range ⊓
      (Units.map (LinearMap.det : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h) →*
        AdjoinRoot h)).ker := by
  ext γ
  rw [Subgroup.mem_inf, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map, Units.val_one]
  constructor
  · rintro ⟨g, rfl⟩
    exact ⟨⟨⟨g.1, specialBlock_le_supportedBlock h g.2⟩, rfl⟩, det_specialBlockGL h g⟩
  · rintro ⟨⟨g, rfl⟩, hdet⟩
    exact ⟨⟨g.1, mem_specialBlock.mpr ⟨g.2, hdet⟩⟩, rfl⟩

end Generic

section Paired

variable {K : Type*} {V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

omit [Finite K] in
theorem OddOrderIsometry.specialToSL_surjective_paired (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hne : h ≠ reciprocalPolynomial h) :
    Function.Surjective (specialToSL Q x h) := by
  intro u
  obtain ⟨g, hg⟩ := hx.blockGL_surjective_paired hh hne u.toGeneralLinearGroup
  have hdet : blockDet Q x h g = 1 := by
    rw [blockDet_apply, hg]
    exact SpecialLinearGroup.det_eq_one u
  refine ⟨⟨g.1, mem_specialBlock.mpr ⟨g.2, hdet⟩⟩, Subtype.ext (LinearEquiv.ext fun v => ?_)⟩
  have := congrArg (fun γ : BlockGL x h => ((γ : Module.End (AdjoinRoot h)
    (primaryComponent x.toLinearMap h)) v)) hg
  exact this

theorem OddOrderIsometry.isQuasisimple_specialBlock_paired (hx : OddOrderIsometry Q p x)
    (hp : p.Prime) (hp3 : 3 < p) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1) (hne : h ≠ reciprocalPolynomial h)
    (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    CFSG.IsQuasisimple ↥(specialBlock Q x h) := by
  have h4 : 4 ≤ Nat.card (AdjoinRoot h) := by
    have := hx.p_lt_card_adjoinRoot hp hh hne1
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

end Paired

section SelfDual

open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type} {V : Type*} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem OddOrderIsometry.isQuasisimple_specialBlock_selfDual (hx : OddOrderIsometry Q p x)
    (hp : p.Prime) (hp3 : 3 < p) {h : K[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) (hm : 2 ≤ primaryMultiplicity x.toLinearMap h) :
    CFSG.IsQuasisimple ↥(specialBlock Q x h) := by
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
  have hnq : ∀ n, (n, ℓ ^ (f * d)) ≠ (3, 2) := fun n e => by
    have := congrArg Prod.snd e
    simp only at this
    omega
  let e₁ : ↥(specialBlock Q x h) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
      (MulEquiv.subgroupCongr hrange)
  refine CFSG.LocalCores.isQuasisimple_of_mulEquiv e₁.symm ?_
  rcases Nat.lt_or_ge (primaryMultiplicity x.toLinearMap h) 3 with h2 | h3
  · have hm2 : finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) = 2 := by
      have : primaryMultiplicity x.toLinearMap h = 2 := by omega
      exact this
    exact CFSG.RankThree.Classical.isQuasisimple_sesqSpecialUnitaryGroup hU hBsymm hBl hm2 hq4
  · exact isQuasisimple_sesqSpecialUnitaryGroup_of_three_le hU hBsymm hBl h3 (hnq _)

end SelfDual

end CFSG.RankThree.PartOne.KCOrthogonal
