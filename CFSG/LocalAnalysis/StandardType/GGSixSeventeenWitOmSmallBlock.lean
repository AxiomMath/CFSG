module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmMain
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorScalar
public import CFSG.RankThree.PartOne.KC.OrthogonalQPlusOnePlanes
public import CFSG.RankThree.PartOne.KC.OrthogonalNormPlaneFactors

public section

namespace CFSG.StandardType

namespace SevOmSmall

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal SevOm

section Fixed

open CFSG.LocalAnalysis.ComponentInitial LayerCores LayerFacts OmNonsplit
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {a : V ≃ₗ[K] V}

theorem fixed_case_small_odd (hx : OddOrderIsometry Q p a)
    {L : Subgroup (V ≃ₗ[K] V)} (hL : CFSG.Assembly.IsComponentOf L (isometryCentralizer Q a))
    (hLF : L ≤ supportedBlock Q a (X - 1)) :
    4 ≤ finrank K (fixedSpace a) ∧
      ((∀ u ∈ supportedBlock Q a (X - 1), Odd (orderOf u) → u ∈ L) ∨
        (SplitFour (Q.comp (fixedSpace a).subtype) ∧ 4 ≤ Nat.card K ∧
          Nonempty (↥L ≃* SL(2, K)))) := by
  classical
  set F := supportedBlock Q a (X - 1) with hF
  set R := Q.comp (fixedSpace a).subtype with hR
  set OW := TauCeti.QuadraticMap.orthogonalGroup R with hOW
  have hRnd : (QuadraticMap.polarBilin R).Nondegenerate := hx.polarBilin_fixed_nondegenerate
  set ρ := fixRho hx with hρ
  have hρinj : Function.Injective ρ := fixRho_injective hx
  set T := (L.subgroupOf F).map ρ with hT
  have hLq : CFSG.IsQuasisimple L :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native L).1 hL.2.2
  let eLT : ↥L ≃* ↥T := (Subgroup.subgroupOfEquivOfLe hLF).symm.trans
    ((L.subgroupOf F).equivMapOfInjective ρ hρinj)
  have hTq : CFSG.IsQuasisimple T := CFSG.LocalCores.isQuasisimple_of_mulEquiv eLT hLq
  have hTs : CFSG.Assembly.IsSubnormal T OW := by
    have h1 : CFSG.Assembly.IsSubnormal L F :=
      ggSubnormal_mono hL.2.1 hLF (supportedBlock_le_isometryCentralizer _)
    have h2 := ggSubnormal_comap F.subtype h1
    rw [show F.comap F.subtype = ⊤ from Subgroup.subgroupOf_self F] at h2
    have h3 := ggSubnormal_map ρ h2
    rwa [← MonoidHom.range_eq_map, hρ, range_fixRho] at h3
  have hmemT : ∀ u (hu : u ∈ F), ρ ⟨u, hu⟩ ∈ T → u ∈ L := by
    intro u hu h
    obtain ⟨y, hy, hyu⟩ := h
    have := hρinj hyu
    rw [this] at hy
    exact Subgroup.mem_subgroupOf.mp hy
  obtain ⟨h4, ⟨hns, hTc⟩ | ⟨hsp, hK4, ψ, hψ, hψr⟩⟩ :=
    structure_of_isSubnormal hRnd hTq hTs
  · obtain ⟨-, hodd⟩ := LayerPDiv.isQuasisimple_commutator_of_not_split hRnd (by omega) hns
    refine ⟨h4, Or.inl fun u hu huodd => hmemT u hu ?_⟩
    rw [hTc]
    have hOW : ρ ⟨u, hu⟩ ∈ OW := (fixedBlockEquiv hx ⟨u, hu⟩).2
    have ho : orderOf (ρ ⟨u, hu⟩) = orderOf u := by
      rw [orderOf_injective ρ hρinj, Subgroup.orderOf_mk]
    exact hodd _ hOW (by simpa [ho] using huodd)
  · exact ⟨h4, Or.inr ⟨hsp, hK4,
      ⟨eLT.trans ((MonoidHom.ofInjective hψ).trans (MulEquiv.subgroupCongr hψr)).symm⟩⟩⟩

theorem fixed_case_small (hx : OddOrderIsometry Q p a) (hp : p.Prime) (hp2 : p ≠ 2)
    {L : Subgroup (V ≃ₗ[K] V)} (hL : CFSG.Assembly.IsComponentOf L (isometryCentralizer Q a))
    (hLF : L ≤ supportedBlock Q a (X - 1)) :
    (∀ u ∈ supportedBlock Q a (X - 1), u ^ p = 1 → u ∈ L) ∨
      (4 ≤ Nat.card K ∧ Nonempty (↥L ≃* SL(2, K))) := by
  rcases fixed_case_small_odd hx hL hLF with ⟨-, h | ⟨-, hK4, hL'⟩⟩
  · refine Or.inl fun u hu hup => h u hu ?_
    exact Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hup)
  · exact Or.inr ⟨hK4, hL'⟩

end Fixed

section SelfDual

open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Universal.Unitary
open scoped MatrixGroups

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

omit [CharP K 2] in
theorem selfDual_unitary (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2) {h : K[X]}
    [Fact (Irreducible h)] (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) :
    ∃ (d ℓ f : ℕ) (hU : UnitaryFieldData ℓ (f * d) (AdjoinRoot h))
      (B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar] primaryComponent x.toLinearMap h →ₗ[
        AdjoinRoot h] AdjoinRoot h),
      h.natDegree = 2 * d ∧ AdjoinRoot.root h ^ Nat.card K ^ d = (AdjoinRoot.root h)⁻¹ ∧
      Nat.card K = ℓ ^ f ∧ B.IsSymm ∧ B.SeparatingLeft ∧
      (specialBlockGL Q x h).range = sesqSpecialUnitaryGroup B := by
  classical
  have hpo : Odd p := hp.odd_of_ne_two hp2
  have hirr := irreducible_of_mem_primaryFactors hh
  obtain ⟨d, H, hdeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hpo hh hne1 hself
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
  exact ⟨d, ℓ, f, hU, B, hdeg, hroot, hq, hBsymm, hBl, hrange⟩

omit [CharP K 2] in
theorem exists_smul_of_commute_selfDual (hx : OddOrderIsometry Q p x) (hp : p.Prime)
    (hp2 : p ≠ 2) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) (hm : 2 ≤ primaryMultiplicity x.toLinearMap h)
    {M : V ≃ₗ[K] V} (hMc : M ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)))
    (hMF : ∀ f ∈ specialBlock Q x h, ∀ v, M (f v) = f (M v)) :
    ∃ c : AdjoinRoot h, ∀ v : primaryComponent x.toLinearMap h,
      M (v : V) = ((c • v : primaryComponent x.toLinearMap h) : V) := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  obtain ⟨d, ℓ, f, hU, B, -, -, -, hBs, hBl, hrange⟩ := selfDual_unitary hx hp hp2 hh hne1 hself
  have hq2 : 2 ≤ ℓ ^ (f * d) :=
    le_trans hU.prime.two_le (Nat.le_self_pow (by have := hU.one_le; omega) ℓ)
  have key : ∀ δ ∈ sesqSpecialUnitaryGroup B,
      Commute ((centralizerGL x h ⟨M, hMc⟩ : BlockGL x h) :
        Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h))
        (δ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) := by
    intro δ hδ
    rw [← hrange] at hδ
    obtain ⟨g, hg⟩ := hδ
    have hcomm := hMF g.1 g.2
    refine LinearMap.ext fun w => Subtype.ext ?_
    have hδw : ∀ w : primaryComponent x.toLinearMap h,
        (((δ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) w :
          primaryComponent x.toLinearMap h) : V) = (g : V ≃ₗ[K] V) (w : V) := by
      intro w
      rw [← hg]
      exact coe_blockGL h ⟨g.1, specialBlock_le_supportedBlock h g.2⟩ w
    change (((centralizerGL x h ⟨M, hMc⟩ : BlockGL x h) :
        Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h))
        ((δ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) w) : V) =
      (((δ : Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h))
        (((centralizerGL x h ⟨M, hMc⟩ : BlockGL x h) :
          Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) w) : _) : V)
    rw [coe_centralizerGL, hδw, hδw, coe_centralizerGL]
    exact hcomm w
  obtain ⟨c, hc⟩ := CFSG.RankThree.PartOne.KCUnitary.exists_smul_of_commute_special_unitary hU hBs
    hBl hm hq2 ((centralizerGL x h ⟨M, hMc⟩ : BlockGL x h) :
      Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) key
  refine ⟨c, fun v => ?_⟩
  have := congrArg Subtype.val (hc v)
  rw [coe_centralizerGL] at this
  exact this

omit [CharP K 2] in
theorem exists_specialBlock_equiv_SL2 (hx : OddOrderIsometry Q p x) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) {h : K[X]} (hh : h ∈ primaryFactors x.toLinearMap)
    (hne1 : h ≠ X - 1) (hm : primaryMultiplicity x.toLinearMap h = 2) :
    ∃ (E : Type) (_ : Field E) (_ : Finite E), Nat.card E = Nat.card K ∧
      Nonempty (↥(specialBlock Q x h) ≃* SL(2, E)) := by
  classical
  have hirr := irreducible_of_mem_primaryFactors hh
  have hmon := monic_of_mem_primaryFactors hh
  have : Fact (Irreducible h) := ⟨hirr⟩
  have : Module.Finite K (AdjoinRoot h) := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  have : Finite (AdjoinRoot h) := Module.finite_of_finite K
  have hself : h = reciprocalPolynomial h :=
    (hx.reciprocal_eq_of_dvd_card_succ hp hpq hh hne1).symm
  obtain ⟨d, ℓ, f, hU, B, hdeg, hroot, hq, hBs, hBl, hrange⟩ :=
    selfDual_unitary hx hp hp2 hh hne1 hself
  have hd : finrank K (AdjoinRoot h) = 2 * d := by
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hdeg]
  have hlam1 : AdjoinRoot.root h ≠ 1 := root_ne_one hmon hne1
  have hlamp : AdjoinRoot.root h ^ p = 1 := root_pow_eq_one (hx.dvd_X_pow_sub_one hh)
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf (AdjoinRoot.root h) = p := orderOf_eq_prime hlamp hlam1
  have hlq : AdjoinRoot.root h ^ (Nat.card K + 1) = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (hord ▸ hpq)
  have hlqinv : AdjoinRoot.root h ^ Nat.card K = (AdjoinRoot.root h)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hlq)
  have hd1 : d = 1 := by
    let := Fintype.ofFinite K
    have hfr : frobPow K (AdjoinRoot h) d = frobPow K (AdjoinRoot h) 1 := by
      apply AlgEquiv.coe_toAlgHom_injective
      apply AdjoinRoot.algHom_ext
      show frobPow K (AdjoinRoot h) d (AdjoinRoot.root h) =
        frobPow K (AdjoinRoot h) 1 (AdjoinRoot.root h)
      rw [frobPow_apply, frobPow_apply, hroot, pow_one, hlqinv]
    have hdpos : 0 < d := by
      have := Module.finrank_pos (R := K) (M := AdjoinRoot h)
      omega
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    set fr := FiniteField.frobeniusAlgEquivOfAlgebraic K (AdjoinRoot h) with hfr_def
    have h1 : fr ^ d' = 1 := by
      have h2 : fr ^ (d' + 1) = fr ^ 1 := hfr
      rw [pow_succ, pow_one] at h2
      exact mul_right_cancel (h2.trans (one_mul fr).symm)
    have h3 : orderOf fr ∣ d' := orderOf_dvd_of_pow_eq_one h1
    rw [hfr_def, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, hd] at h3
    have h4 : d' = 0 := Nat.eq_zero_of_dvd_of_lt h3 (by omega)
    omega
  subst hd1
  let e₁ : ↥(specialBlock Q x h) ≃* ↥(sesqSpecialUnitaryGroup B) :=
    (MonoidHom.ofInjective (hx.specialBlockGL_injective hh)).trans
      (MulEquiv.subgroupCongr hrange)
  obtain ⟨e₂⟩ :=
    CFSG.RankThree.Classical.nonempty_sesqSpecialUnitaryGroup_mulEquiv_SL2 hU hBs hBl hm
  have : Finite hU.fixedField := Subtype.finite
  refine ⟨hU.fixedField, inferInstance, inferInstance, ?_, ⟨e₁.trans e₂⟩⟩
  rw [hU.card_fixedField, mul_one, hq]

omit [Finite K] [CharP K 2] in
theorem two_le_primaryMultiplicity (hx : OddOrderIsometry Q p x) {h : K[X]}
    (hh : h ∈ primaryFactors x.toLinearMap) (hq : CFSG.IsQuasisimple ↥(specialBlock Q x h)) :
    2 ≤ primaryMultiplicity x.toLinearMap h := by
  have : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  by_contra hm
  have hpos : 1 ≤ primaryMultiplicity x.toLinearMap h := by
    have hne : primaryComponent x.toLinearMap h ≠ ⊥ :=
      primaryComponent_ne_bot hx.squarefree_minpoly hh
    have : Nontrivial (primaryComponent x.toLinearMap h) :=
      Submodule.nontrivial_iff_ne_bot.mpr hne
    exact Module.finrank_pos
  have h1 := hx.specialBlock_eq_bot_of_finrank_eq_one hh (by omega)
  have hbot : ∀ g : ↥(specialBlock Q x h), g = 1 := fun g => Subtype.ext (by
    have h2 : (g : V ≃ₗ[K] V) ∈ (⊥ : Subgroup (V ≃ₗ[K] V)) := h1 ▸ g.2
    exact Subgroup.mem_bot.mp h2)
  obtain ⟨u, u', huu⟩ := LayerFacts.exists_mul_ne_of_isQuasisimple hq
  exact huu (by rw [hbot u, hbot u'])

end SelfDual

end SevOmSmall

end CFSG.StandardType
