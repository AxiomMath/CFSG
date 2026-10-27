module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallO8mCurtis
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartOne.KC.OrthogonalQuarticNonsplit
import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.OddOrderMovedSubspace.OddOrderMovedSubspace
import CFSG.CGT.T75N.PpdCyclic
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesInvolution
import CFSG.LargeExtraspecial.A2ModSqueeze
import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedModels
import CFSG.Adapters.LieModelOrders
import all CFSG.Timmesfeld.Orders.Distinct
import CFSG.RankThree.GF2n.Stroth80.Sec3Zsig
import CFSG.LinearAlgebra.CoprimeActions.InvolutionDimensionBounds
public import CFSG.RankThree.OrthogonalInvolutions.Conjugacy

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.SmallO8mIsometry

open Module Polynomial QuadraticMap
open CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary

universe u v

section Primary

variable {K : Type u} {V : Type v} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p d : ℕ} {x : V ≃ₗ[K] V}

theorem exists_unique_factor (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hd : 0 < d) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 2 * d)
    (hV : finrank K V = 2 * d) (hfix : ∀ w, x w = w → w = 0) :
    ∃ h : K[X], primaryFactors x.toLinearMap = {h} ∧ h.natDegree = 2 * d ∧
      primaryMultiplicity x.toLinearMap h = 1 := by
  classical
  have hsum := finrank_eq_sum_degree_mul_multiplicity hx.squarefree_minpoly
  rw [hV, Finset.sum_coe_sort (primaryFactors x.toLinearMap)
    (fun a => a.natDegree * primaryMultiplicity x.toLinearMap a)] at hsum
  have hdegree : ∀ a ∈ primaryFactors x.toLinearMap, 2 * d ≤ a.natDegree := fun a ha =>
    Nat.le_of_dvd (irreducible_of_mem_primaryFactors ha).natDegree_pos
      (hx.dvd_natDegree_of_orderOf hp hord hfix ha)
  have hge : ∀ a ∈ primaryFactors x.toLinearMap,
      2 * d ≤ a.natDegree * primaryMultiplicity x.toLinearMap a := by
    intro a ha
    have : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
    exact (hdegree a ha).trans (Nat.le_mul_of_pos_right _ (hx.primaryMultiplicity_pos ha))
  have hcard := Finset.card_nsmul_le_sum (primaryFactors x.toLinearMap)
    (fun a => a.natDegree * primaryMultiplicity x.toLinearMap a) (2 * d) hge
  rw [← hsum, smul_eq_mul] at hcard
  have hne : (primaryFactors x.toLinearMap).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    rw [hemp] at hsum
    simp only [Finset.sum_empty] at hsum
    omega
  have hc1 : (primaryFactors x.toLinearMap).card = 1 := by
    have := hne.card_pos
    nlinarith
  obtain ⟨h, hs⟩ := Finset.card_eq_one.mp hc1
  have hh : h ∈ primaryFactors x.toLinearMap := hs ▸ Finset.mem_singleton_self h
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hm := hx.primaryMultiplicity_pos hh
  have hprod : h.natDegree * primaryMultiplicity x.toLinearMap h = 2 * d := by
    rw [hs, Finset.sum_singleton] at hsum
    exact hsum.symm
  have hdeg := hdegree h hh
  have hm1 : primaryMultiplicity x.toLinearMap h = 1 := by
    by_contra hne1
    have h2 : 2 ≤ primaryMultiplicity x.toLinearMap h := by omega
    nlinarith
  exact ⟨h, hs, by simpa [hm1] using hprod, hm1⟩

theorem exists_field_model (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : Odd p)
    (hd : 0 < d) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 2 * d)
    (hV : finrank K V = 2 * d) (hfix : ∀ w, x w = w → w = 0) :
    ∃ (E : Type u) (_ : Field E) (_ : Algebra K E) (_ : Finite E)
      (hE : finrank K E = 2 * d) (e : V ≃ₗ[K] E) (z : Eˣ),
      (∀ w, Q w = hermitianForm hE (e w)) ∧
      (∀ w, e (x w) = (z : E) * e w) ∧ orderOf z = p ∧
      frobPow K E d z = (z : E)⁻¹ := by
  classical
  obtain ⟨h, hs, hdeg, hm⟩ := exists_unique_factor hx hp hd hord hV hfix
  have hh : h ∈ primaryFactors x.toLinearMap := hs ▸ Finset.mem_singleton_self h
  have hirr := irreducible_of_mem_primaryFactors hh
  have : Fact (Irreducible h) := ⟨hirr⟩
  have hne1 : h ≠ X - 1 := fun e => hx.X_sub_one_not_mem hfix (e ▸ hh)
  have hself : h = reciprocalPolynomial h := by
    have := hx.reciprocalPolynomial_mem hh
    rw [hs, Finset.mem_singleton] at this
    exact this.symm
  obtain ⟨d', hdegd, -, -, -, -, hroot, ι, hinj, -, hQι, hxι⟩ :=
    hx.selfDualModel hp2 hh hne1 hself
  have hd' : d' = d := by omega
  subst d'
  have hE : finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  let i₀ : Fin (primaryMultiplicity x.toLinearMap h) := ⟨0, by omega⟩
  let ι' : AdjoinRoot h →ₗ[K] V :=
    ι ∘ₗ LinearMap.single K (fun _ : Fin (primaryMultiplicity x.toLinearMap h) => AdjoinRoot h) i₀
  have hι' : ∀ z, ι' z = ι (Pi.single i₀ z) := fun z => rfl
  have hinj' : Function.Injective ι' := fun a b hab =>
    Pi.single_injective i₀ (hinj (by rw [← hι', ← hι']; exact hab))
  have hbij : Function.Bijective ι' := ⟨hinj',
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [hE, hV])).mp hinj'⟩
  let e := (LinearEquiv.ofBijective ι' hbij).symm
  obtain ⟨hz0, hzord⟩ := hx.orderOf_root hp hh hne1
  refine ⟨AdjoinRoot h, inferInstance, inferInstance, inferInstance, hE, e,
    Units.mk0 (AdjoinRoot.root h) hz0, ?_, ?_, hzord, ?_⟩
  · intro w
    have hw : w = ι (Pi.single i₀ (e w)) :=
      ((LinearEquiv.ofBijective ι' hbij).apply_symm_apply w).symm
    obtain ⟨hmem, hQ⟩ := hQι (Pi.single i₀ (e w))
    have hsumz : ∑ i, (Pi.single i₀ (e w) : Fin (primaryMultiplicity x.toLinearMap h) →
        AdjoinRoot h) i * (Pi.single i₀ (e w) : Fin (primaryMultiplicity x.toLinearMap h) →
        AdjoinRoot h) i ^ Nat.card K ^ d = e w * e w ^ Nat.card K ^ d := by
      rw [Finset.sum_eq_single i₀]
      · simp
      · intro i _ hi
        simp [Pi.single_eq_of_ne hi, zero_pow (pow_pos Nat.card_pos d).ne']
      · simp
    rw [congrArg Q hw, hQ, hermitianForm_apply]
    congr 1
    apply Subtype.ext
    rw [coe_unitaryNorm, frobPow_apply]
    exact hsumz
  · intro w
    apply (LinearEquiv.ofBijective ι' hbij).injective
    change (LinearEquiv.ofBijective ι' hbij) ((LinearEquiv.ofBijective ι' hbij).symm (x w)) =
      ι (Pi.single i₀ ((AdjoinRoot.root h) * e w))
    rw [(LinearEquiv.ofBijective ι' hbij).apply_symm_apply]
    have hw : w = ι (Pi.single i₀ (e w)) :=
      ((LinearEquiv.ofBijective ι' hbij).apply_symm_apply w).symm
    calc x w = x (ι (Pi.single i₀ (e w))) := congrArg x hw
      _ = ι (AdjoinRoot.root h • Pi.single i₀ (e w)) := hxι _
      _ = ι (Pi.single i₀ (AdjoinRoot.root h * e w)) := by
        congr 1
        ext i
        by_cases hi : i = i₀
        · subst hi; simp
        · simp [Pi.single_eq_of_ne hi]
  · rw [frobPow_apply]
    exact hroot

end Primary


section Frobenius

variable {K E : Type*} [Field K] [Finite K] [CharP K 2] [Field E] [Finite E] [CharP E 2]
  [Algebra K E] {d : ℕ} (hE : finrank K E = 2 * d)

include hE

omit [CharP K 2] [CharP E 2] in
theorem frob_mem_orthogonalGroup :
    (frobPow K E d).toLinearEquiv ∈ TauCeti.QuadraticMap.orthogonalGroup (hermitianForm hE) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro z
  rw [hermitianForm_apply, hermitianForm_apply]
  congr 1
  apply Subtype.ext
  change frobPow K E d z * frobPow K E d (frobPow K E d z) = z * frobPow K E d z
  rw [frobPow_frobPow K E hE, mul_comm]

omit [CharP K 2] in
theorem range_frob_sub_one :
    LinearMap.range ((frobPow K E d).toLinearMap - 1) =
      (fixedSubfield K E d).toSubalgebra.toSubmodule := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    change frobPow K E d (frobPow K E d w - w) = frobPow K E d w - w
    rw [map_sub, frobPow_frobPow K E hE]
    rw [CharTwo.sub_eq_add, CharTwo.sub_eq_add, add_comm]
  · intro hz
    have hz' : frobPow K E d z = z := hz
    obtain ⟨w, hw⟩ := (isUnitaryInvolution K E hE).trace_surj z hz'
    refine ⟨w, ?_⟩
    change frobPow K E d w - w = z
    rw [CharTwo.sub_eq_add, add_comm]
    exact hw

omit [CharP K 2] in
theorem finrank_range_frob_sub_one :
    finrank K (LinearMap.range ((frobPow K E d).toLinearMap - 1)) = d := by
  rw [range_frob_sub_one hE]
  exact finrank_fixedSubfield K E hE

omit [CharP K 2] in
theorem exists_nonsingular_range_frob (_hd : 0 < d) :
    ∃ z ∈ LinearMap.range ((frobPow K E d).toLinearMap - 1), hermitianForm hE z ≠ 0 := by
  have : FiniteDimensional K (fixedSubfield K E d) := inferInstance
  have : Algebra.IsSeparable K (fixedSubfield K E d) := inferInstance
  obtain ⟨t, ht⟩ := Algebra.trace_surjective K (fixedSubfield K E d) (1 : K)
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two
    (F := fixedSubfield K E d) (ringChar.eq (fixedSubfield K E d) 2) t
  refine ⟨(r : E), ?_, ?_⟩
  · rw [range_frob_sub_one hE]
    exact r.2
  · have hnorm : unitaryNorm hE (r : E) = t := by
      apply Subtype.ext
      rw [coe_unitaryNorm, show frobPow K E d (r : E) = (r : E) from r.2]
      exact congrArg Subtype.val hr.symm
    rw [hermitianForm_apply, hnorm, ht]
    exact one_ne_zero

end Frobenius


section InvertingModel

variable {K : Type u} {V : Type v} [Field K] [Finite K] [CharP K 2]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p d : ℕ} {x : V ≃ₗ[K] V}

theorem exists_involution_inverting (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : Odd p) (hd : 0 < d) (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 2 * d)
    (hV : finrank K V = 2 * d) (hfix : ∀ w, x w = w → w = 0) :
    ∃ r : V ≃ₗ[K] V, r ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ r * r = 1 ∧
      finrank K (LinearMap.range (r.toLinearMap - 1)) = d ∧
      (∃ w ∈ LinearMap.range (r.toLinearMap - 1), Q w ≠ 0) ∧ r * x * r = x⁻¹ := by
  obtain ⟨E, hfield, halg, hfinite, hE, e, z, hQ, hxe, -, hbarz⟩ :=
    exists_field_model hx hp hp2 hd hord hV hfix
  let : Field E := hfield
  let : Algebra K E := halg
  let : Finite E := hfinite
  have : CharP E 2 := charP_of_injective_algebraMap (algebraMap K E).injective 2
  let σ := (frobPow K E d).toLinearEquiv
  let r : V ≃ₗ[K] V := (e.trans σ).trans e.symm
  have her : ∀ v, e (r v) = frobPow K E d (e v) := fun v => by simp [r, σ]
  have hr2 : r * r = 1 := by
    ext v
    apply e.injective
    simp only [LinearEquiv.mul_apply, her, frobPow_frobPow K E hE,
      LinearEquiv.coe_one, id]
  have hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    rw [hQ, her]
    change hermitianForm hE (σ (e v)) = Q v
    rw [TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup (frob_mem_orthogonalGroup hE),
      ← hQ]
  have hrank : finrank K (LinearMap.range (r.toLinearMap - 1)) = d := by
    have hk := CFSG.QuasithinUnique.Setup.SL2Modules.finrank_ker_of_intertwining
      e r.toLinearMap σ.toLinearMap her
    have h1 := LinearMap.finrank_range_add_finrank_ker (r.toLinearMap - 1)
    have h2 := LinearMap.finrank_range_add_finrank_ker (σ.toLinearMap - 1)
    have hfr := finrank_range_frob_sub_one hE
    change finrank K (LinearMap.range (σ.toLinearMap - 1)) = d at hfr
    rw [hV] at h1
    rw [hE] at h2
    omega
  obtain ⟨w, hw, hQw⟩ := exists_nonsingular_range_frob hE hd
  obtain ⟨v, hv⟩ := hw
  refine ⟨r, hrO, hr2, hrank, ⟨e.symm w, ?_, ?_⟩, ?_⟩
  · refine ⟨e.symm v, ?_⟩
    apply e.injective
    change e (r (e.symm v) - e.symm v) = e (e.symm w)
    rw [map_sub, her, e.apply_symm_apply, e.apply_symm_apply]
    exact hv
  · rwa [hQ, e.apply_symm_apply]
  · ext v
    apply e.injective
    have hxinv : ∀ v, e (x⁻¹ v) = (z : E)⁻¹ * e v := by
      intro v
      have hh := hxe (x⁻¹ v)
      change e (x (x.symm v)) = (z : E) * e (x.symm v) at hh
      rw [x.apply_symm_apply] at hh
      have hh' := congrArg (fun w : E => (z : E)⁻¹ * w) hh
      simpa [mul_assoc, z.ne_zero] using hh'.symm
    simp only [LinearEquiv.mul_apply, her, hxe, map_mul, hbarz,
      frobPow_frobPow K E hE, hxinv]

end InvertingModel


section FullRank

variable {K : Type u} {V : Type v} [Field K] [Finite K] [CharP K 2]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p d : ℕ}

theorem exists_conjugate_inverted (hx : V ≃ₗ[K] V) (hxQ : OddOrderIsometry Q p hx)
    (hp : p.Prime) (hp2 : Odd p) (hd : 0 < d)
    (hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 2 * d) (hV : finrank K V = 2 * d)
    (hfix : ∀ w, hx w = w → w = 0) {s : V ≃ₗ[K] V}
    (hsO : s ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hs2 : s * s = 1)
    (hsrank : finrank K (LinearMap.range (s.toLinearMap - 1)) = d)
    (hsnon : ∃ w ∈ LinearMap.range (s.toLinearMap - 1), Q w ≠ 0) :
    ∃ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      s * (g⁻¹ * hx * g) * s = (g⁻¹ * hx * g)⁻¹ := by
  obtain ⟨r, hrO, hr2, hrank, hrnon, hrx⟩ :=
    exists_involution_inverting hxQ hp hp2 hd hord hV hfix
  have hr1 : r ≠ 1 := by
    intro heq
    rw [heq, LinearEquiv.coe_toLinearMap_one, ← Module.End.one_eq_id, sub_self,
      LinearMap.range_zero, finrank_bot] at hrank
    omega
  have hs1 : s ≠ 1 := by
    intro heq
    rw [heq, LinearEquiv.coe_toLinearMap_one, ← Module.End.one_eq_id, sub_self,
      LinearMap.range_zero, finrank_bot] at hsrank
    omega
  have hsord : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1
  have hrord : orderOf r = 2 := orderOf_eq_prime (by rw [pow_two]; exact hr2) hr1
  have hletters : CFSG.RankThree.OrthogonalInvolutions.suzukiLetter Q r =
      CFSG.RankThree.OrthogonalInvolutions.suzukiLetter Q s := by
    classical
    unfold CFSG.RankThree.OrthogonalInvolutions.suzukiLetter
    rw [hrank, hsrank]
    have hrnot : ¬ ∀ w ∈ LinearMap.range (r.toLinearMap - 1), Q w = 0 := by
      rintro h; obtain ⟨w, hw, hwQ⟩ := hrnon; exact hwQ (h w hw)
    have hsnot : ¬ ∀ w ∈ LinearMap.range (s.toLinearMap - 1), Q w = 0 := by
      rintro h; obtain ⟨w, hw, hwQ⟩ := hsnon; exact hwQ (h w hw)
    simp only [hrnot, hsnot, if_false]
  obtain ⟨g, hg, hgs⟩ :=
    (CFSG.RankThree.OrthogonalInvolutions.isConj_iff_suzukiLetter_eq
      (CFSG.RankThree.PartOne.KCOrthogonal.polarBilin_nondegenerate_of_separating K hxQ.regular)
      hsO hsord hrO hrord).mpr ⟨hletters, hrank.trans hsrank.symm⟩
  refine ⟨g, hg, ?_⟩
  have hconj : g * (s * (g⁻¹ * hx * g) * s) * g⁻¹ = r * hx * r := by
    rw [← hgs]
    group
  apply (MulAut.conj g).injective
  change g * (s * (g⁻¹ * hx * g) * s) * g⁻¹ = g * (g⁻¹ * hx * g)⁻¹ * g⁻¹
  rw [hconj, hrx]
  group

end FullRank


section MatrixFour

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.OrthogonalInvolutions

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
  (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {e : ℕ} (he : 2 ≤ e)
  (hK : Nat.card K = 2 ^ e)

include hirrQ he hK

theorem isOmega8m_coordinateDerived :
    IsOmega8m (matrixDerived (coordinateQuadMinus 4 K (by norm_num) b c)) e := by
  have Γ := CFSG.SeitzReduction.SymplecticPilot.peRhoMEquiv (by norm_num : 4 ≤ 4) hirrQ
  have hscal : (StatedScalars (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K).subgroupOf
      (StatedOmega (StatedQuadMinus 4 K b c)) = ⊥ := by
    apply CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (CFSG.LieType.Universal.Spin.coe_quadMinus 4 K b c)
    refine ⟨CFSG.LieType.Universal.Spin.Twisted.eVec 4 0 +
      CFSG.LieType.Universal.Spin.Twisted.fVec 4 0, ?_⟩
    norm_num [CFSG.LieType.Universal.Spin.quadMinus_apply,
      CFSG.LieType.Universal.Spin.Twisted.eVec, CFSG.LieType.Universal.Spin.Twisted.fVec,
      Pi.single_apply, Fin.sum_univ_succ]
  let π : StatedProj (StatedOmega (StatedQuadMinus 4 K b c)) ≃*
      StatedOmega (StatedQuadMinus 4 K b c) :=
    (QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot
  let Θ := π.trans (Γ.symm.trans (SmallO8mCurtis.coordinateEquiv hirrQ))
  have hmodel : IsOmega8m (StatedProj (StatedOmega (StatedQuadMinus 4 K b c))) e := by
    exact Or.inl ⟨by decide, ⟨⟨Nat.prime_two, by omega, by norm_num⟩,
      K, inferInstance, inferInstance, hK, b, c, hirrQ, ⟨MulEquiv.refl _⟩⟩⟩
  have hproj : IsOmega8m (matrixProjectiveDerived (coordinateQuadMinus 4 K (by norm_num) b c)) e :=
    hmodel.of_mulEquiv Θ
  exact hproj.of_mulEquiv
    (CFSG.RankThree.PartOne.AUTSL.derivedProjEquiv _
      (SmallO8mCurtis.coordinateMinus_ne_zero (b := b) (c := c))).symm

theorem exists_inverted_primitive_rank_four
    (s : matrixIsometries (coordinateQuadMinus 4 K (by norm_num) b c))
    (hs : s * s = 1)
    (hrank : finrank K (LinearMap.range ((matrixLinearIso s.val).toLinearMap - 1)) = 4) :
    ∃ p : ℕ, IsPrimitivePrimeDivisor p (8 * e) ∧
      ∃ x : matrixDerived (coordinateQuadMinus 4 K (by norm_num) b c),
        orderOf x = p ∧ matrixDerivedConjugation _ (matrixIsometryInclusion _ s) x = x⁻¹ := by
  classical
  let Q := coordinateQuadMinus 4 K (by norm_num) b c
  have hgeom := regular_coordinateQuadMinus 4 K b c (by norm_num) hirrQ
  have hQ : Q.polarBilin.Nondegenerate := hgeom.1
  have hnoTS : ∀ U : Submodule K (Fin (2 * 4) → K), finrank K U = 4 →
      ∃ u ∈ U, Q u ≠ 0 := by
    intro U hU
    let E := coordinateMinusIsometry 4 K (by norm_num) b c
    let U₀ := U.map E.symm.toLinearMap
    have hU₀ : finrank K U₀ = 4 := by
      rw [LinearEquiv.finrank_map_eq E.symm.toLinearEquiv]; exact hU
    obtain ⟨u, hu, hQu⟩ := (CFSG.ClassicalGroups.Orthogonal.isMinus_quadMinus
      (by norm_num : 1 ≤ 4) hirrQ).noTS U₀ hU₀
    obtain ⟨v, hv, rfl⟩ := hu
    refine ⟨v, hv, ?_⟩
    change (CFSG.LieType.Universal.Spin.quadMinus 4 K b c) (E.symm v) ≠ 0 at hQu
    rwa [E.symm.map_app] at hQu
  have hsnonsing : ∃ w ∈ LinearMap.range ((matrixLinearIso s.val).toLinearMap - 1), Q w ≠ 0 :=
    hnoTS _ hrank
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := 8 * e) (by omega) (by omega)
  have hG : IsOmega8m (matrixDerived Q) e := isOmega8m_coordinateDerived hirrQ he hK
  have hcard : Nat.card (matrixDerived Q) = ordTwistedD 4 (2 ^ e) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hG.card_eq_lieOrd (by norm_num)
  have hdvd : p ∣ Nat.card (matrixDerived Q) := by
    rw [hcard]
    apply ((profile_ordTwistedD (n := 4) (by norm_num) (by omega : 1 ≤ e)).prim
      p (8 * e) hp (by omega)).mpr
    unfold z2D
    left
    constructor
    · convert dvd_refl (8 * e) using 1; ring
    · exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
  have : Fact p.Prime := ⟨hp.prime⟩
  obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' p hdvd
  let xlin := matrixLinearIso (x₀ : GL (Fin (2 * 4)) K)
  have hxord : orderOf xlin = p := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe]; exact hx₀
  have hxpow : xlin ^ p = 1 := hxord ▸ pow_orderOf_eq_one xlin
  have hx1 : xlin ≠ 1 := by
    intro hh
    rw [hh, orderOf_one] at hxord
    exact hp.prime.one_lt.ne hxord
  have hxO : xlin ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (matrixDerived_le_isometries Q x₀.2)
  have hpK : (p : K) ≠ 0 := by
    have hne := hp.ne_two (by omega)
    exact (CharP.cast_eq_zero_iff K 2 p).not.mpr
      (fun hd => hne ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.prime).mp hd).symm)
  have hxQ : OddOrderIsometry Q p xlin :=
    ⟨hxO, hxpow, hpK, fun v hv => hQ.1 v hv⟩
  have horder2 : orderOf (2 : ZMod p) = 8 * e :=
    CFSG.RankThree.GF2n.Stroth80.orderOf_two_zmod_eq_of_primitive hp.prime (by omega)
      hp.dvd hp.2.2
  have hord : orderOf (Nat.card K : ZMod p) = 2 * 4 := by
    rw [hK, Nat.cast_pow, Nat.cast_ofNat, orderOf_pow' _ (by omega : e ≠ 0), horder2,
      Nat.gcd_eq_right (dvd_mul_left e 8), Nat.mul_div_cancel _ (by omega)]
  have : Fintype K := Fintype.ofFinite K
  have : Finite (Fin (2 * 4) → K) := inferInstance
  have hfix := (CFSG.CGT.T75N.simple_of_ppd
    (by simp : finrank K (Fin (2 * 4) → K) = 2 * 4)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul]; exact
      (hp.dvd_sub_one_iff (by omega) (e * (2 * 4))).mpr (by
        convert dvd_refl (8 * e) using 1; ring))
    (fun k hk hklt hpk => by
      rw [← Nat.card_eq_fintype_card, hK] at hpk
      rw [← pow_mul] at hpk
      have hdiv := (hp.dvd_sub_one_iff (by omega) (e * k)).mp hpk
      exact Nat.not_dvd_of_pos_of_lt (by positivity) (by nlinarith) hdiv)
    xlin hxpow hx1).1
  have hsO : matrixLinearIso s.val ∈ TauCeti.QuadraticMap.orthogonalGroup Q := s.2
  have hs2 : matrixLinearIso s.val * matrixLinearIso s.val = 1 := by
    rw [← map_mul, show s.val * s.val = 1 from congrArg Subtype.val hs, map_one]
  obtain ⟨g, hg, hinv⟩ := exists_conjugate_inverted xlin hxQ hp.prime
    (hp.prime.eq_two_or_odd'.resolve_left (hp.ne_two (by omega))) (by norm_num : 0 < 4)
    hord (by simp) hfix hsO hs2 hrank hsnonsing
  let gmat := matrixLinearIso.symm g
  have hgmat : gmat ∈ matrixIsometries Q := by
    change matrixLinearIso (matrixLinearIso.symm g) ∈ TauCeti.QuadraticMap.orthogonalGroup Q
    rwa [MulEquiv.apply_symm_apply]
  let x : matrixDerived Q := matrixDerivedConjugation Q
    (matrixIsometryInclusion Q ⟨gmat⁻¹, (matrixIsometries Q).inv_mem hgmat⟩) x₀
  have hxval : x.val = gmat⁻¹ * x₀.val * gmat := by
    rw [matrixDerivedConjugation_val]
    change gmat⁻¹ * CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut _ K 1 x₀.val *
      (gmat⁻¹)⁻¹ = _
    simp
  have hxlin : matrixLinearIso x.val = g⁻¹ * xlin * g := by
    rw [hxval, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  refine ⟨p, hp, x, ?_, ?_⟩
  · rw [← Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq matrixLinearIso, hxlin]
    change orderOf ((MulAut.conj g⁻¹) xlin) = p
    rw [MulEquiv.orderOf_eq]
    exact hxord
  · apply Subtype.ext
    apply matrixLinearIso.injective
    rw [matrixDerivedConjugation_val]
    change matrixLinearIso (s.val *
      CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut _ K 1 x.val * s.val⁻¹) =
      matrixLinearIso x.val⁻¹
    simp only [map_one, MulAut.one_apply, map_mul, map_inv]
    rw [hxlin]
    have hsinv : (matrixLinearIso s.val)⁻¹ = matrixLinearIso s.val :=
      inv_eq_of_mul_eq_one_right hs2
    rw [hsinv]
    exact hinv

end MatrixFour


section BinaryFour

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Timmesfeld
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {K W : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup W]
  [Module (ZMod 2) W] [Finite W] {b c : K} {e : ℕ}

theorem four_mul_le_finrank_of_rank_four (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (he : 2 ≤ e) (hK : Nat.card K = 2 ^ e)
    (ρ : Representation (ZMod 2) (matrixDerived (coordinateQuadMinus 4 K (by norm_num) b c)) W)
    (hfaith : Function.Injective ρ) (a : W ≃ₗ[ZMod 2] W) (ha : a * a = 1)
    (s : matrixIsometries (coordinateQuadMinus 4 K (by norm_num) b c)) (hs : s * s = 1)
    (heq : ∀ g w, a (ρ g w) =
      ρ (matrixDerivedConjugation _ (matrixIsometryInclusion _ s) g) (a w))
    (hrank : finrank K (LinearMap.range ((matrixLinearIso s.val).toLinearMap - 1)) = 4) :
    4 * e ≤ finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) := by
  obtain ⟨p, hp, x, hx, hxs⟩ := exists_inverted_primitive_rank_four hirrQ he hK s hs hrank
  have : Fact p.Prime := ⟨hp.prime⟩
  let π := CFSG.LinearAlgebra.CoprimeActions.InvolutionDimensionBounds.toEquivHom ρ
  have hπ : ∀ g w, π g w = ρ g w :=
    CFSG.LinearAlgebra.CoprimeActions.InvolutionDimensionBounds.toEquivHom_apply ρ
  have hπx : π x ≠ 1 := by
    intro hh
    have hh' : ρ x = ρ 1 := by
      ext w
      have h := LinearEquiv.congr_fun hh w
      simpa [hπ] using h
    have hx1 : x = 1 := hfaith hh'
    rw [hx1, orderOf_one] at hx
    exact hp.prime.one_lt.ne hx
  have hpx : (π x) ^ p = 1 := by rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have haa : ∀ w, a (a w) = w := fun w => LinearEquiv.congr_fun ha w
  have hinv : a * π x * a = (π x)⁻¹ := by
    ext w
    change a (π x (a w)) = (π x)⁻¹ w
    rw [hπ, heq, hxs, haa, ← hπ, map_inv]
  have h1 := CFSG.LargeExtraspecial.A2Mod.orderOf_two_le_finrank_commSpace
    (hp.ne_two (by omega)) hpx hπx
  have h2 := CFSG.GroupTheory.CoprimeActionSupport.InvertedOddOrderDisplacementRank.finrank_range_le
    a (π x) p (hp.prime.eq_two_or_odd'.resolve_left (hp.ne_two (by omega))) ha hpx hinv
  have horder : orderOf (2 : ZMod p) = 8 * e :=
    CFSG.RankThree.GF2n.Stroth80.orderOf_two_zmod_eq_of_primitive hp.prime (by omega)
      hp.dvd hp.2.2
  rw [horder] at h1
  change 8 * e ≤ finrank (ZMod 2) (LinearMap.range ((π x).toLinearMap - 1)) at h1
  omega

end BinaryFour


section SpinFour

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LieType.Universal.Spin

variable {K W : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup W]
  [Module (ZMod 2) W] [Finite W] {b c : K} {e : ℕ}

theorem four_mul_le_finrank_spin_of_rank_four
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (he : 2 ≤ e) (hK : Nat.card K = 2 ^ e)
    (ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) W)
    (hfaith : Function.Injective ρ) (a : W ≃ₗ[ZMod 2] W) (ha : a * a = 1)
    (α : MulAut (spinGroup (quadMinus 4 K b c)))
    (s : matrixIsometries (coordinateQuadMinus 4 K (by norm_num) b c)) (hs : s * s = 1)
    (hα : ∀ g, SmallO8mCurtis.coordinateEquiv hirrQ (α g) =
      matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s)
        (SmallO8mCurtis.coordinateEquiv hirrQ g))
    (heq : ∀ g w, a (ρ g w) = ρ (α g) (a w))
    (hrank : finrank K (LinearMap.range ((matrixLinearIso s.val).toLinearMap - 1)) = 4) :
    4 * e ≤ finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) := by
  let Θ := SmallO8mCurtis.coordinateSpinEquiv hirrQ
  let τ := ρ.comp Θ.symm.toMonoidHom
  have hτ : Function.Injective τ := fun g h heq => Θ.symm.injective (hfaith heq)
  have hproj : Function.Injective (matrixProjectiveProjection (coordinateQuadMinus 4 K
      (by norm_num) b c)) :=
    (CFSG.RankThree.PartOne.AUTSL.derivedProjEquiv _
      (SmallO8mCurtis.coordinateMinus_ne_zero (b := b) (c := c))).injective
  have hconj : ∀ g, Θ (α g) =
      matrixDerivedConjugation _ (matrixIsometryInclusion _ s) (Θ g) := by
    intro g
    apply hproj
    have h := hα g
    rw [SmallO8mCurtis.coordinateEquiv_apply, SmallO8mCurtis.coordinateEquiv_apply] at h
    change matrixProjectiveProjection _ (Θ (α g)) =
      matrixProjectiveConjugation _ (matrixIsometryInclusion _ s)
        (matrixProjectiveProjection _ (Θ g)) at h
    rwa [matrixProjectiveConjugation_mk] at h
  apply four_mul_le_finrank_of_rank_four hirrQ he hK τ hτ a ha s hs _ hrank
  intro g w
  change a (ρ (Θ.symm g) w) =
    ρ (Θ.symm (matrixDerivedConjugation _ (matrixIsometryInclusion _ s) g)) (a w)
  rw [heq]
  congr 2
  apply Θ.injective
  rw [Θ.apply_symm_apply, hconj, Θ.apply_symm_apply]

end SpinFour


section Moved

variable {K : Type u} {V : Type v} [Field K] [Finite K] [CharP K 2]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V}
  {p : ℕ} {x : V ≃ₗ[K] V}

omit [Finite K] [CharP K 2] in
theorem isCompl_fixed_range (hx : OddOrderIsometry Q p x) (hp : Odd p) :
    IsCompl (LinearMap.ker (x.toLinearMap - 1)) (LinearMap.range (x.toLinearMap - 1)) := by
  exact CFSG.LocalAnalysis.RankThreeUC.ProofSupport.OddOrderMovedSubspace.complementary
    hp hx.cast_ne_zero x hx.pow_eq_one

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem polar_fixed_range (hx : OddOrderIsometry Q p x) {u v : V}
    (hu : u ∈ LinearMap.ker (x.toLinearMap - 1))
    (hv : v ∈ LinearMap.range (x.toLinearMap - 1)) : polar Q u v = 0 := by
  have hxu : x u = u := by simpa [sub_eq_zero] using hu
  have hxiu : x.symm u = u := by
    have h := congrArg x.symm hxu
    rw [x.symm_apply_apply] at h
    exact h.symm
  obtain ⟨w, rfl⟩ := hv
  change polar Q u (x w - w) = 0
  rw [polar_sub_right, polar_comm Q u (x w), hx.polar_apply,
    hxiu, polar_comm Q w u, sub_self]

omit [Finite K] [CharP K 2] in
theorem nondegenerate_range (hx : OddOrderIsometry Q p x) (hp : Odd p) :
    (Q.comp (LinearMap.range (x.toLinearMap - 1)).subtype).polarBilin.Nondegenerate := by
  apply CFSG.RankThree.PartOne.KCOrthogonal.polarBilin_nondegenerate_of_separating K
  intro v hv
  apply Subtype.ext
  apply hx.regular
  intro w
  obtain ⟨c, hc, u, hu, rfl⟩ := exists_add_of_isCompl (isCompl_fixed_range hx hp) w
  rw [polar_add_right, polar_comm Q (v : V) c,
    polar_fixed_range hx hc v.2, zero_add]
  exact hv ⟨u, hu⟩

@[expose] noncomputable def movedEquiv (x : V ≃ₗ[K] V) :
    LinearMap.range (x.toLinearMap - 1) ≃ₗ[K] LinearMap.range (x.toLinearMap - 1) :=
  CFSG.RankThree.PartOne.KCOrthogonal.restrictEquiv _ x
    (fun _ ⟨w, hw⟩ => ⟨x w, by rw [← hw]; change x (x w) - x w = x (x w - w); rw [map_sub]⟩)
    (fun _ ⟨w, hw⟩ => ⟨x.symm w, by
      rw [← hw]
      change x (x.symm w) - x.symm w = x.symm (x w - w)
      rw [map_sub, x.apply_symm_apply, x.symm_apply_apply]⟩)

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem movedEquiv_apply (v : LinearMap.range (x.toLinearMap - 1)) :
    (movedEquiv x v : V) = x v := rfl

omit [Finite K] [CharP K 2] in
theorem movedEquiv_fixed_eq_zero (hx : OddOrderIsometry Q p x) (hp : Odd p)
    (v : LinearMap.range (x.toLinearMap - 1)) (hv : movedEquiv x v = v) : v = 0 := by
  apply Subtype.ext
  apply (Submodule.disjoint_def.mp (isCompl_fixed_range hx hp).disjoint) (v : V) _ v.2
  change x v - v = 0
  exact sub_eq_zero.mpr (congrArg Subtype.val hv)

omit [Finite K] [CharP K 2] in
theorem movedEquiv_oddOrderIsometry (hx : OddOrderIsometry Q p x) (hp : Odd p) :
    OddOrderIsometry (Q.comp (LinearMap.range (x.toLinearMap - 1)).subtype) p (movedEquiv x) := by
  refine ⟨?_, ?_, hx.cast_ne_zero, ?_⟩
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    change Q (x v) = Q v
    exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hx.mem v
  · have hpow : ∀ k v, ((movedEquiv x ^ k) v : V) = (x ^ k) v := by
      intro k
      induction k with
      | zero => intro v; rfl
      | succ k ih =>
        intro v
        rw [pow_succ', pow_succ', LinearEquiv.mul_apply, LinearEquiv.mul_apply,
          movedEquiv_apply, ih]
    apply LinearEquiv.ext
    intro v
    apply Subtype.ext
    rw [hpow, hx.pow_eq_one]
    rfl
  · exact (nondegenerate_range hx hp).1

theorem exists_involution_inverting_on_range (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : Odd p) {d : ℕ} (hd : 0 < d)
    (hord : orderOf (Nat.card K : ZMod p) = 2 * d)
    (hrange : finrank K (LinearMap.range (x.toLinearMap - 1)) = 2 * d) :
    ∃ r : V ≃ₗ[K] V, r ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ r * r = 1 ∧
      finrank K (LinearMap.range (r.toLinearMap - 1)) = d ∧ r * x * r = x⁻¹ := by
  let U := LinearMap.range (x.toLinearMap - 1)
  let C := LinearMap.ker (x.toLinearMap - 1)
  obtain ⟨rU, hrUO, hrU2, hrUrank, -, hrUx⟩ :=
    exists_involution_inverting (movedEquiv_oddOrderIsometry hx hp2) hp hp2 hd hord
      hrange (movedEquiv_fixed_eq_zero hx hp2)
  let E : (C × U) ≃ₗ[K] V := C.prodEquivOfIsCompl U (isCompl_fixed_range hx hp2)
  let r : V ≃ₗ[K] V := (E.symm.trans ((LinearEquiv.refl K C).prodCongr rU)).trans E
  have hrE : ∀ (c : C) (u : U), r (E (c, u)) = E (c, rU u) := by
    intro c u
    simp [r]
  have hE : ∀ (c : C) (u : U), E (c, u) = (c : V) + u := fun c u => rfl
  have hr2 : r * r = 1 := by
    ext v
    obtain ⟨⟨c, u⟩, rfl⟩ := E.surjective v
    rw [LinearEquiv.mul_apply, hrE, hrE]
    have h2 := LinearEquiv.congr_fun hrU2 u
    change rU (rU u) = u at h2
    rw [h2]
    rfl
  have hrO : r ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    obtain ⟨⟨c, u⟩, rfl⟩ := E.surjective v
    rw [hrE, hE, hE, QuadraticMap.map_add Q, QuadraticMap.map_add Q,
      polar_fixed_range hx c.2 (rU u).2, polar_fixed_range hx c.2 u.2, add_zero, add_zero]
    congr 1
    exact TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hrUO u
  have hrrange : LinearMap.range (r.toLinearMap - 1) =
      (LinearMap.range (rU.toLinearMap - 1)).map U.subtype := by
    ext v
    constructor
    · rintro ⟨w, rfl⟩
      obtain ⟨⟨c, u⟩, rfl⟩ := E.surjective w
      refine ⟨rU u - u, ⟨u, rfl⟩, ?_⟩
      change (rU u : V) - u = r (E (c, u)) - E (c, u)
      rw [hrE, hE, hE]
      abel
    · rintro ⟨w, ⟨u, rfl⟩, rfl⟩
      refine ⟨E (0, u), ?_⟩
      change r (E (0, u)) - E (0, u) = (rU u : V) - u
      rw [hrE, hE, hE]
      simp
  refine ⟨r, hrO, hr2, ?_, ?_⟩
  · rw [hrrange, ← (Submodule.equivMapOfInjective U.subtype U.injective_subtype
      (LinearMap.range (rU.toLinearMap - 1))).finrank_eq]
    exact hrUrank
  · ext v
    obtain ⟨⟨c, u⟩, rfl⟩ := E.surjective v
    have hxE : ∀ (c : C) (u : U), x (E (c, u)) = E (c, movedEquiv x u) := by
      intro c u
      rw [hE, map_add, hE]
      have hc : x c = c := by
        have hcc : (x.toLinearMap - 1) c = 0 := c.2
        exact sub_eq_zero.mp hcc
      rw [hc, movedEquiv_apply]
    have hxinvE : ∀ (c : C) (u : U), x⁻¹ (E (c, u)) = E (c, (movedEquiv x)⁻¹ u) := by
      intro c u
      apply x.injective
      rw [hxE]
      change x (x.symm (E (c, u))) = E (c, movedEquiv x ((movedEquiv x).symm u))
      rw [x.apply_symm_apply, (movedEquiv x).apply_symm_apply]
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hrE, hxE, hrE, hxinvE]
    apply congrArg (fun u : U => E (c, u))
    have h := LinearEquiv.congr_fun hrUx u
    simpa only [LinearEquiv.mul_apply] using h

end Moved


section RankThree

open CFSG.RankThree.OrthogonalInvolutions CFSG.Timmesfeld CFSG.Timmesfeld.Orders
open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
  (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {e : ℕ} (he : 2 ≤ e)
  (hK : Nat.card K = 2 ^ e)

include hirrQ he hK

theorem exists_primitive_with_range_six :
    ∃ p : ℕ, IsPrimitivePrimeDivisor p (6 * e) ∧
      ∃ x : matrixDerived (coordinateQuadMinus 4 K (by norm_num) b c), orderOf x = p ∧
        finrank K (LinearMap.range ((matrixLinearIso x.val).toLinearMap - 1)) = 6 := by
  classical
  let Q := coordinateQuadMinus 4 K (by norm_num) b c
  obtain ⟨p, hp⟩ := exists_isPrimitivePrimeDivisor (k := 6 * e) (by omega) (by omega)
  have hG := isOmega8m_coordinateDerived hirrQ he hK
  have hcard : Nat.card (matrixDerived Q) = ordTwistedD 4 (2 ^ e) := by
    simpa [CFSG.EvenSmallLie.CatalogOrders.lieOrd] using hG.card_eq_lieOrd (by norm_num)
  have hdvd : p ∣ Nat.card (matrixDerived Q) := by
    rw [hcard]
    apply ((profile_ordTwistedD (n := 4) (by norm_num) (by omega : 1 ≤ e)).prim
      p (6 * e) hp (by omega)).mpr
    unfold z2D
    right
    refine ⟨3, by norm_num, ?_⟩
    convert dvd_refl (6 * e) using 1; ring
  have : Fact p.Prime := ⟨hp.prime⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  let xlin := matrixLinearIso x.val
  have hxord : orderOf xlin = p := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe]; exact hx
  have hx1 : xlin ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hxord
    exact hp.prime.one_lt.ne hxord
  have hxpow : xlin ^ p = 1 := hxord ▸ pow_orderOf_eq_one xlin
  have hpK : ¬ p ∣ Nat.card K := by
    rw [hK]
    intro h
    have h2 := hp.prime.dvd_of_dvd_pow h
    exact hp.ne_two (by omega) ((Nat.prime_dvd_prime_iff_eq hp.prime Nat.prime_two).mp h2)
  have hdegree := CFSG.LargeExtraspecial.A2Mod.dvd_card_pow_finrank_commSpace_sub_one
    hp.prime hpK hxpow
  rw [hK, ← pow_mul] at hdegree
  have hd := (hp.dvd_sub_one_iff (by omega)
    (e * finrank K (LinearMap.range (xlin.toLinearMap - 1)))).mp hdegree
  have hpos := one_le_finrank_commSpace hx1
  have hle : finrank K (LinearMap.range (xlin.toLinearMap - 1)) ≤ 8 := by
    exact (Submodule.finrank_le _).trans_eq (by simp)
  have hcanc : 6 ∣ finrank K (LinearMap.range (xlin.toLinearMap - 1)) := by
    have hd' : e * 6 ∣ e * finrank K (LinearMap.range (xlin.toLinearMap - 1)) := by
      simpa only [mul_comm] using hd
    exact (Nat.mul_dvd_mul_iff_left (by omega : 0 < e)).mp hd'
  have hsix : finrank K (LinearMap.range (xlin.toLinearMap - 1)) = 6 := by
    obtain ⟨k, hk⟩ := hcanc
    change 1 ≤ finrank K (LinearMap.range (xlin.toLinearMap - 1)) at hpos
    omega
  exact ⟨p, hp, x, hx, hsix⟩


theorem exists_inverted_primitive_rank_three
    (s : matrixIsometries (coordinateQuadMinus 4 K (by norm_num) b c)) (hs : s * s = 1)
    (hrank : finrank K (LinearMap.range ((matrixLinearIso s.val).toLinearMap - 1)) = 3) :
    ∃ p : ℕ, IsPrimitivePrimeDivisor p (6 * e) ∧
      ∃ x : matrixDerived (coordinateQuadMinus 4 K (by norm_num) b c), orderOf x = p ∧
        matrixDerivedConjugation _ (matrixIsometryInclusion _ s) x = x⁻¹ := by
  classical
  let Q := coordinateQuadMinus 4 K (by norm_num) b c
  have hgeom := regular_coordinateQuadMinus 4 K b c (by norm_num) hirrQ
  have hQ : Q.polarBilin.Nondegenerate := hgeom.1
  obtain ⟨p, hp, x₀, hx₀, hrange⟩ := exists_primitive_with_range_six hirrQ he hK
  let xlin := matrixLinearIso x₀.val
  have hxord : orderOf xlin = p := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_coe]; exact hx₀
  have hxpow : xlin ^ p = 1 := hxord ▸ pow_orderOf_eq_one xlin
  have hpp : p.Prime := hp.prime
  have hpodd : Odd p := hp.prime.eq_two_or_odd'.resolve_left (hp.ne_two (by omega))
  have hpK : (p : K) ≠ 0 := by
    exact (CharP.cast_eq_zero_iff K 2 p).not.mpr
      (fun hd => hp.ne_two (by omega)
        ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp.prime).mp hd).symm)
  have hxQ : OddOrderIsometry Q p xlin :=
    ⟨matrixDerived_le_isometries Q x₀.2, hxpow, hpK, fun v hv => hQ.1 v hv⟩
  have horder2 : orderOf (2 : ZMod p) = 6 * e :=
    CFSG.RankThree.GF2n.Stroth80.orderOf_two_zmod_eq_of_primitive hp.prime (by omega)
      hp.dvd hp.2.2
  have hord : orderOf (Nat.card K : ZMod p) = 2 * 3 := by
    rw [hK, Nat.cast_pow, Nat.cast_ofNat, orderOf_pow' _ (by omega : e ≠ 0), horder2,
      Nat.gcd_eq_right (dvd_mul_left e 6), Nat.mul_div_cancel _ (by omega)]
  obtain ⟨r, hrO, hr2, hrankR, hrx⟩ := exists_involution_inverting_on_range hxQ hp.prime hpodd
    (by norm_num : 0 < 3) hord hrange
  have hsO : matrixLinearIso s.val ∈ TauCeti.QuadraticMap.orthogonalGroup Q := s.2
  have hs2 : matrixLinearIso s.val * matrixLinearIso s.val = 1 := by
    rw [← map_mul, show s.val * s.val = 1 from congrArg Subtype.val hs, map_one]
  have hr1 : r ≠ 1 := by
    intro hh
    rw [hh, LinearEquiv.coe_toLinearMap_one, ← Module.End.one_eq_id, sub_self,
      LinearMap.range_zero, finrank_bot] at hrankR
    omega
  have hs1 : matrixLinearIso s.val ≠ 1 := by
    intro hh
    rw [hh, LinearEquiv.coe_toLinearMap_one, ← Module.End.one_eq_id, sub_self,
      LinearMap.range_zero, finrank_bot] at hrank
    omega
  have hletters : suzukiLetter Q r = suzukiLetter Q (matrixLinearIso s.val) := by
    rw [suzukiLetter_eq_b_iff.mpr (by rw [hrankR]; decide),
      suzukiLetter_eq_b_iff.mpr (by rw [hrank]; decide)]
  obtain ⟨g, hg, hgs⟩ := (isConj_iff_suzukiLetter_eq hQ hsO
    (orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1) hrO
    (orderOf_eq_prime (by rw [pow_two]; exact hr2) hr1)).mpr
      ⟨hletters, hrankR.trans hrank.symm⟩
  have hinv : matrixLinearIso s.val * (g⁻¹ * xlin * g) * matrixLinearIso s.val =
      (g⁻¹ * xlin * g)⁻¹ := by
    apply (MulAut.conj g).injective
    change g * (matrixLinearIso s.val * (g⁻¹ * xlin * g) * matrixLinearIso s.val) * g⁻¹ =
      g * (g⁻¹ * xlin * g)⁻¹ * g⁻¹
    have hh : g * (matrixLinearIso s.val * (g⁻¹ * xlin * g) * matrixLinearIso s.val) * g⁻¹ =
        r * xlin * r := by rw [← hgs]; group
    rw [hh, hrx]
    group
  let gmat := matrixLinearIso.symm g
  have hgmat : gmat ∈ matrixIsometries Q := by
    change matrixLinearIso (matrixLinearIso.symm g) ∈ TauCeti.QuadraticMap.orthogonalGroup Q
    rwa [MulEquiv.apply_symm_apply]
  let x : matrixDerived Q := matrixDerivedConjugation Q
    (matrixIsometryInclusion Q ⟨gmat⁻¹, (matrixIsometries Q).inv_mem hgmat⟩) x₀
  have hxval : x.val = gmat⁻¹ * x₀.val * gmat := by
    rw [matrixDerivedConjugation_val]
    change gmat⁻¹ * CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut _ K 1 x₀.val *
      (gmat⁻¹)⁻¹ = _
    simp
  have hxlin : matrixLinearIso x.val = g⁻¹ * xlin * g := by
    rw [hxval, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  refine ⟨p, hp, x, ?_, ?_⟩
  · rw [← Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq matrixLinearIso, hxlin]
    change orderOf ((MulAut.conj g⁻¹) xlin) = p
    rw [MulEquiv.orderOf_eq]
    exact hxord
  · apply Subtype.ext
    apply matrixLinearIso.injective
    rw [matrixDerivedConjugation_val]
    change matrixLinearIso (s.val *
      CFSG.ComponentClassification.CatalogueBHigherLinearField.glFieldAut _ K 1 x.val * s.val⁻¹) =
      matrixLinearIso x.val⁻¹
    simp only [map_one, MulAut.one_apply, map_mul, map_inv]
    rw [hxlin, inv_eq_of_mul_eq_one_right hs2]
    exact hinv

end RankThree

section BinaryThree

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Timmesfeld
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear

variable {K W : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup W]
  [Module (ZMod 2) W] [Finite W] {b c : K} {e : ℕ}

theorem three_mul_le_finrank_of_rank_three (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (he : 2 ≤ e) (hK : Nat.card K = 2 ^ e)
    (ρ : Representation (ZMod 2) (matrixDerived (coordinateQuadMinus 4 K (by norm_num) b c)) W)
    (hfaith : Function.Injective ρ) (a : W ≃ₗ[ZMod 2] W) (ha : a * a = 1)
    (s : matrixIsometries (coordinateQuadMinus 4 K (by norm_num) b c)) (hs : s * s = 1)
    (heq : ∀ g w, a (ρ g w) =
      ρ (matrixDerivedConjugation _ (matrixIsometryInclusion _ s) g) (a w))
    (hrank : finrank K (LinearMap.range ((matrixLinearIso s.val).toLinearMap - 1)) = 3) :
    3 * e ≤ finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) := by
  obtain ⟨p, hp, x, hx, hxs⟩ := exists_inverted_primitive_rank_three hirrQ he hK s hs hrank
  have : Fact p.Prime := ⟨hp.prime⟩
  let π := CFSG.LinearAlgebra.CoprimeActions.InvolutionDimensionBounds.toEquivHom ρ
  have hπ : ∀ g w, π g w = ρ g w :=
    CFSG.LinearAlgebra.CoprimeActions.InvolutionDimensionBounds.toEquivHom_apply ρ
  have hπx : π x ≠ 1 := by
    intro hh
    have hh' : ρ x = ρ 1 := by
      ext w
      have h := LinearEquiv.congr_fun hh w
      simpa [hπ] using h
    have hx1 : x = 1 := hfaith hh'
    rw [hx1, orderOf_one] at hx
    exact hp.prime.one_lt.ne hx
  have hpx : (π x) ^ p = 1 := by rw [← map_pow, ← hx, pow_orderOf_eq_one, map_one]
  have haa : ∀ w, a (a w) = w := fun w => LinearEquiv.congr_fun ha w
  have hinv : a * π x * a = (π x)⁻¹ := by
    ext w
    change a (π x (a w)) = (π x)⁻¹ w
    rw [hπ, heq, hxs, haa, ← hπ, map_inv]
  have h1 := CFSG.LargeExtraspecial.A2Mod.orderOf_two_le_finrank_commSpace
    (hp.ne_two (by omega)) hpx hπx
  have h2 := CFSG.GroupTheory.CoprimeActionSupport.InvertedOddOrderDisplacementRank.finrank_range_le
    a (π x) p (hp.prime.eq_two_or_odd'.resolve_left (hp.ne_two (by omega))) ha hpx hinv
  have horder : orderOf (2 : ZMod p) = 6 * e :=
    CFSG.RankThree.GF2n.Stroth80.orderOf_two_zmod_eq_of_primitive hp.prime (by omega)
      hp.dvd hp.2.2
  rw [horder] at h1
  change 6 * e ≤ finrank (ZMod 2) (LinearMap.range ((π x).toLinearMap - 1)) at h1
  omega

end BinaryThree

section SpinThree

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LieType.Universal.Spin

variable {K W : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup W]
  [Module (ZMod 2) W] [Finite W] {b c : K} {e : ℕ}

theorem three_mul_le_finrank_spin_of_rank_three
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (he : 2 ≤ e) (hK : Nat.card K = 2 ^ e)
    (ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) W)
    (hfaith : Function.Injective ρ) (a : W ≃ₗ[ZMod 2] W) (ha : a * a = 1)
    (α : MulAut (spinGroup (quadMinus 4 K b c)))
    (s : matrixIsometries (coordinateQuadMinus 4 K (by norm_num) b c)) (hs : s * s = 1)
    (hα : ∀ g, SmallO8mCurtis.coordinateEquiv hirrQ (α g) =
      matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s)
        (SmallO8mCurtis.coordinateEquiv hirrQ g))
    (heq : ∀ g w, a (ρ g w) = ρ (α g) (a w))
    (hrank : finrank K (LinearMap.range ((matrixLinearIso s.val).toLinearMap - 1)) = 3) :
    3 * e ≤ finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) := by
  let Θ := SmallO8mCurtis.coordinateSpinEquiv hirrQ
  let τ := ρ.comp Θ.symm.toMonoidHom
  have hτ : Function.Injective τ := fun g h heq => Θ.symm.injective (hfaith heq)
  have hproj : Function.Injective (matrixProjectiveProjection (coordinateQuadMinus 4 K
      (by norm_num) b c)) :=
    (CFSG.RankThree.PartOne.AUTSL.derivedProjEquiv _
      (SmallO8mCurtis.coordinateMinus_ne_zero (b := b) (c := c))).injective
  have hconj : ∀ g, Θ (α g) =
      matrixDerivedConjugation _ (matrixIsometryInclusion _ s) (Θ g) := by
    intro g
    apply hproj
    have h := hα g
    rw [SmallO8mCurtis.coordinateEquiv_apply, SmallO8mCurtis.coordinateEquiv_apply] at h
    change matrixProjectiveProjection _ (Θ (α g)) =
      matrixProjectiveConjugation _ (matrixIsometryInclusion _ s)
        (matrixProjectiveProjection _ (Θ g)) at h
    rwa [matrixProjectiveConjugation_mk] at h
  apply three_mul_le_finrank_of_rank_three hirrQ he hK τ hτ a ha s hs _ hrank
  intro g w
  change a (ρ (Θ.symm g) w) =
    ρ (Θ.symm (matrixDerivedConjugation _ (matrixIsometryInclusion _ s) g)) (a w)
  rw [heq]
  congr 2
  apply Θ.injective
  rw [Θ.apply_symm_apply, hconj, Θ.apply_symm_apply]

end SpinThree


section SmallRank

open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.LieType.Universal.Spin

variable {K W : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup W]
  [Module (ZMod 2) W] [Finite W] {b c : K} {e : ℕ}

theorem finrank_isometry_le_two_of_small
    (hirrQ : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (he : 2 ≤ e) (hK : Nat.card K = 2 ^ e)
    (ρ : Representation (ZMod 2) (spinGroup (quadMinus 4 K b c)) W)
    (hfaith : Function.Injective ρ) (a : W ≃ₗ[ZMod 2] W) (ha : a * a = 1)
    (α : MulAut (spinGroup (quadMinus 4 K b c)))
    (s : matrixIsometries (coordinateQuadMinus 4 K (by norm_num) b c)) (hs : s * s = 1)
    (hα : ∀ g, SmallO8mCurtis.coordinateEquiv hirrQ (α g) =
      matrixProjectiveConjugationHom _ (matrixIsometryInclusion _ s)
        (SmallO8mCurtis.coordinateEquiv hirrQ g))
    (heq : ∀ g w, a (ρ g w) = ρ (α g) (a w))
    (hrank : finrank (ZMod 2) (LinearMap.range (a.toLinearMap - 1)) ≤ 2 * e + 1) :
    finrank K (LinearMap.range ((matrixLinearIso s.val).toLinearMap - 1)) ≤ 2 := by
  have hs2 : matrixLinearIso s.val * matrixLinearIso s.val = 1 := by
    rw [← map_mul, show s.val * s.val = 1 from congrArg Subtype.val hs, map_one]
  have hle := CFSG.RankThree.OrthogonalInvolutions.two_mul_finrank_commSpace_le hs2
  have hdim : finrank K (Fin (2 * 4) → K) = 8 := by simp
  rw [hdim] at hle
  by_contra hnot
  have hcases : finrank K (LinearMap.range ((matrixLinearIso s.val).toLinearMap - 1)) = 3 ∨
      finrank K (LinearMap.range ((matrixLinearIso s.val).toLinearMap - 1)) = 4 := by
    change 2 * finrank K (LinearMap.range ((matrixLinearIso s.val).toLinearMap - 1)) ≤ 8 at hle
    omega
  rcases hcases with h3 | h4
  · have h := three_mul_le_finrank_spin_of_rank_three hirrQ he hK ρ hfaith a ha α s hs hα heq h3
    omega
  · have h := four_mul_le_finrank_spin_of_rank_four hirrQ he hK ρ hfaith a ha α s hs hα heq h4
    omega

end SmallRank

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.SmallO8mIsometry
