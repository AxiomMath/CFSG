module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentFrame
import CFSG.RankThree.PartOne.K159.RowFourType
import CFSG.RankThree.PartOne.KC.LinearPlaneBlocks
import CFSG.HardMathSupport.Malle.E27Lie.Outer.ClassicalDiagThreeCore
import CFSG.LieType.SeitzGeneration.HeisTorusU84
import CFSG.HardMathSupport.Timmesfeld.CrossChar.OrthQ2Unit
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartOne.KC.OrthogonalBinaryDickson
public import CFSG.RankThree.PartOne.KC.OrthogonalBlockProduct
public import CFSG.RankThree.PartOne.KC.OrthogonalFixedDerived
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import CFSG.RankThree.PartOne.KC.LinearCommutantFactors

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.OmNsRootGen

open Polynomial QuadraticMap Module CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.GLTheoremA.S172C.Cent
  CFSG.RankThree.PartOne.KCPrimary CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.KCLinPlane CFSG.ClassicalGroups.UnitaryFlag

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [FiniteDimensional F V] {Q : QuadraticForm F V} {p : ℕ}

private theorem exists_unitary_model_deg_two {x : V ≃ₗ[F] V} (hx : OddOrderIsometry Q p x)
    (hp2 : Odd p) {h : F[X]} [Fact (Irreducible h)]
    (hh : h ∈ primaryFactors x.toLinearMap) (hne1 : h ≠ X - 1)
    (hself : h = reciprocalPolynomial h) (hdeg : finrank F (AdjoinRoot h) = 2) :
    ∃ (ℓ f : ℕ) (hU : UnitaryFieldData ℓ (f * 1) (AdjoinRoot h))
      (B : primaryComponent x.toLinearMap h →ₛₗ[hU.bar]
        primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h),
      Nat.card F = ℓ ^ f ∧ B.IsSymm ∧ B.SeparatingLeft ∧
      (∀ (u w : primaryComponent x.toLinearMap h) (c : AdjoinRoot h),
        Algebra.trace F (AdjoinRoot h) (B u w * c) =
          QuadraticMap.polar Q (u : V) ((c • w : primaryComponent x.toLinearMap h) : V)) ∧
      (specialBlockGL Q x h).range = sesqSpecialUnitaryGroup B := by
  classical
  have hirr := irreducible_of_mem_primaryFactors hh
  obtain ⟨d, H, hddeg, hroot, hH, hadd1, hadd2, hleft, hright, hsymm⟩ :=
    hx.exists_selfDual_hermitian hp2 hh hne1 hself
  have hd0 : d = 1 := by
    have := hdeg
    rw [(AdjoinRoot.powerBasis hirr.ne_zero).finrank, AdjoinRoot.powerBasis_dim, hddeg] at this
    omega
  subst hd0
  obtain ⟨ℓ, f, hU, hq, hbar⟩ := exists_unitaryFieldData (K := F) (E := AdjoinRoot h)
    (d := 1) hdeg
  have hbar' : ∀ z, frobPow F (AdjoinRoot h) 1 z = hU.bar z := fun z => by
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
  have htr : ∀ (u w : primaryComponent x.toLinearMap h) (c : AdjoinRoot h),
      Algebra.trace F (AdjoinRoot h) (B u w * c) =
        QuadraticMap.polar Q (u : V) ((c • w : primaryComponent x.toLinearMap h) : V) :=
    fun u w c => by rw [hBH]; exact hH u w c
  have hrange : (specialBlockGL Q x h).range = sesqSpecialUnitaryGroup B := by
    rw [range_specialBlockGL, sesqSpecialUnitaryGroup]
    congr 1
    ext γ
    rw [hx.mem_range_blockGL_selfDual_iff hh hne1 hself H hH, mem_sesqUnitaryGroup]
    exact Iff.rfl
  exact ⟨ℓ, f, hU, B, hq, hBsymm, hBl, htr, hrange⟩

private theorem exists_adapted_basis {k : ℕ} {U : Fin k → Submodule F V}
    {x : V ≃ₗ[F] V} {h : F[X]} [Fact (Irreducible h)]
    (hx : OddOrderIsometry Q p x) (hh : h ∈ primaryFactors x.toLinearMap)
    (hdeg2 : h.natDegree = 2)
    (hU : IsPlaneSystem Q U) (hmaps : ∀ j, ∀ v ∈ U j, x v ∈ U j)
    (hUh : ∀ j, U j ≤ primaryComponent x.toLinearMap h)
    (hW : primaryComponent x.toLinearMap h = ⊤)
    {ℓ f : ℕ} {hUd : UnitaryFieldData ℓ (f * 1) (AdjoinRoot h)}
    {B : primaryComponent x.toLinearMap h →ₛₗ[hUd.bar]
      primaryComponent x.toLinearMap h →ₗ[AdjoinRoot h] AdjoinRoot h}
    (hBsymm : B.IsSymm) (hBsep : B.SeparatingLeft)
    (htr : ∀ (u w : primaryComponent x.toLinearMap h) (c : AdjoinRoot h),
      Algebra.trace F (AdjoinRoot h) (B u w * c) =
        polar Q (u : V) ((c • w : primaryComponent x.toLinearMap h) : V))
    (hfinW : finrank (AdjoinRoot h) (primaryComponent x.toLinearMap h) = k) :
    ∃ b : Basis (Fin k) (AdjoinRoot h) (primaryComponent x.toLinearMap h),
      (∀ i j, B (b i) (b j) = if i = j then 1 else 0) ∧
      (∀ j, ((b j : primaryComponent x.toLinearMap h) : V) ∈ U j) := by
  classical
  have hstable : ∀ (j : Fin k) (c : AdjoinRoot h) (v : primaryComponent x.toLinearMap h),
      (v : V) ∈ U j → ((c • v : primaryComponent x.toLinearMap h) : V) ∈ U j := by
    intro j c v hv
    obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective c
    rw [coe_mk_smul_primaryComponent]
    exact aeval_mem_of_stable (hmaps j) g hv
  have hex : ∀ j : Fin k, ∃ v : V, v ∈ U j ∧ v ≠ 0 := fun j =>
    exists_ne_zero_mem_of_finrank_eq_two (U j) (hU.finrank_eq j)
  choose v₀ hv₀U hv₀0 using hex
  let v : Fin k → primaryComponent x.toLinearMap h := fun j => ⟨v₀ j, hUh j (hv₀U j)⟩
  have hv_ne : ∀ j, v j ≠ 0 := by
    intro j h0
    exact hv₀0 j (congrArg Subtype.val h0)
  have hBv_ne : ∀ j, B (v j) (v j) ≠ 0 := by
    intro j h0
    have hx_v : x (v j : V) =
        ((AdjoinRoot.root h • v j : primaryComponent x.toLinearMap h) : V) :=
      (coe_root_smul_primaryComponent (x := x.toLinearMap) (a := h) (v j)).symm
    have hnot : ∀ a : F, x (v j : V) ≠ a • (v j : V) := by
      intro a ha
      have hroot : h.eval a = 0 := by
        have h1 : (aeval x.toLinearMap h) (v j : V) = 0 := mem_primaryComponent.mp (v j).2
        rw [Module.End.aeval_apply_of_mem_apply_eq_smul (f := x.toLinearMap) (p := h)
          (μ := a) (x := (v j : V)) ha] at h1
        rcases smul_eq_zero.mp h1 with h2 | h2
        · exact h2
        · exact absurd h2 (fun h3 => hv_ne j (Subtype.ext h3))
      have hdvd : (X - C a) ∣ h := Polynomial.dvd_iff_isRoot.mpr hroot
      have hirr : Irreducible h := Fact.out
      have hass : Associated h (X - C a) :=
        ((Polynomial.irreducible_X_sub_C a).associated_of_dvd hirr hdvd).symm
      have hdeg1 : h.natDegree = 1 := by
        rw [Polynomial.eq_of_monic_of_associated (monic_of_mem_primaryFactors hh) (monic_X_sub_C a)
          hass, natDegree_X_sub_C]
      omega
    have hspan : Submodule.span F {(v j : V), x (v j : V)} = (U j : Submodule F V) := by
      have hle : Submodule.span F {(v j : V), x (v j : V)} ≤ U j :=
        Submodule.span_le.mpr (by
          intro y hy
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
          rcases hy with rfl | rfl
          · exact hv₀U j
          · exact hmaps j _ (hv₀U j))
      refine Submodule.eq_of_le_of_finrank_eq hle ?_
      have hli : LinearIndependent F ![((v j : V)), x (v j : V)] := by
        rw [LinearIndependent.pair_iff]
        intro s t hst
        by_cases ht : t = 0
        · subst ht
          rw [zero_smul, add_zero] at hst
          exact ⟨(smul_eq_zero.mp hst).resolve_right (fun h3 => hv_ne j (Subtype.ext h3)), rfl⟩
        · exfalso
          have h1 : t • x (v j : V) + s • (v j : V) = 0 := by
            rw [add_comm]; exact hst
          have h2 : t • x (v j : V) = (-s) • (v j : V) := by
            rw [neg_smul, eq_neg_iff_add_eq_zero]; exact h1
          have h3 : x (v j : V) = (-(s / t)) • (v j : V) := by
            have h4 := congrArg (fun z => t⁻¹ • z) h2
            simpa [smul_smul, inv_mul_cancel₀ ht, div_eq_mul_inv, mul_comm, mul_left_comm,
              mul_assoc] using h4
          exact hnot (-(s / t)) h3
      have hspan' : Submodule.span F {(v j : V), x (v j : V)}
          = Submodule.span F (Set.range ![((v j : V)), x (v j : V)]) := by
        congr 1
        ext z
        simp [or_comm]
      rw [hspan', finrank_span_eq_card hli]
      simp [hU.finrank_eq j]
    have hpolar : ∀ y ∈ U j, polar Q (v j : V) y = 0 := by
      intro y hy
      have hy' : y ∈ Submodule.span F {(v j : V), x (v j : V)} := hspan.symm ▸ hy
      refine Submodule.span_induction (p := fun z _ => polar Q (v j : V) z = 0)
        ?_ ?_ ?_ ?_ hy'
      · intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · rw [QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero]
        · rw [hx_v, ← htr (v j) (v j) (AdjoinRoot.root h), h0, zero_mul, map_zero]
      · simp
      · intro a b ha hb hpa hpb; rw [QuadraticMap.polar_add_right, hpa, hpb, add_zero]
      · intro c a ha hpa; rw [QuadraticMap.polar_smul_right, hpa, smul_zero]
    have hsub : (QuadraticMap.polarBilin (Q.comp (U j).subtype)).SeparatingLeft := (hU.nondeg j).1
    have h1 : (⟨v j, hv₀U j⟩ : U j) = 0 := by
      refine hsub ⟨(v j : V), hv₀U j⟩ fun y => ?_
      rw [QuadraticMap.polarBilin_apply_apply, polar_comp_subtype_cent]
      exact hpolar (y : V) y.2
    have h2 : v₀ j = 0 := by
      simpa [v] using congrArg (fun x : U j => (x : V)) h1
    exact hv₀0 j h2
  have hunit : ∀ j : Fin k, ∃ u : primaryComponent x.toLinearMap h,
      ((u : V) ∈ U j) ∧ B u u = 1 := by
    intro j
    have hfix : (B (v j) (v j))⁻¹ ∈ hUd.fixedField := by
      rw [UnitaryFieldData.mem_fixedField]
      have h1 : hUd.bar (B (v j) (v j)) = B (v j) (v j) := hBsymm.eq (v j) (v j)
      rw [map_inv₀, h1]
    obtain ⟨c, hc⟩ := hUd.normHom_surjective ⟨(B (v j) (v j))⁻¹, hfix⟩
    refine ⟨c • v j, ?_, ?_⟩
    · exact hstable j c (v j) (hv₀U j)
    · have hc' : hUd.norm c = (B (v j) (v j))⁻¹ := congrArg Subtype.val hc
      have hcalc : B (c • v j) (c • v j) = hUd.bar c * c * B (v j) (v j) := by
        simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring
      rw [hcalc, mul_comm (hUd.bar c) c, ← UnitaryFieldData.norm, hc',
        inv_mul_cancel₀ (hBv_ne j)]
  choose u huU huB using hunit
  have horth : ∀ i j, i ≠ j → B (u i) (u j) = 0 := by
    intro i j hij
    refine eq_zero_of_trace_mul_eq_zero F (AdjoinRoot h) fun c => ?_
    rw [htr (u i) (u j) c]
    exact hU.perp i j hij (u i) (huU i) ((c • u j : primaryComponent x.toLinearMap h) : V)
      (hstable j c (u j) (huU j))
  have hli : LinearIndependent (AdjoinRoot h) u := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 := congrArg (fun w => B (u i) w) hg
    rw [map_sum, map_zero] at h1
    simp only [map_smul, smul_eq_mul] at h1
    rw [Finset.sum_eq_single i] at h1
    · simpa [huB i] using h1
    · intro j _ hji
      rw [horth i j (Ne.symm hji), mul_zero]
    · intro hi; exact absurd (Finset.mem_univ i) hi
  have hspan : Submodule.span (AdjoinRoot h) (Set.range u) = ⊤ := by
    refine LinearIndependent.span_eq_top_of_card_eq_finrank' hli ?_
    rw [Fintype.card_fin, hfinW]
  refine ⟨Basis.mk hli (le_of_eq hspan.symm), ?_, ?_⟩
  · intro i j
    rw [Basis.mk_apply, Basis.mk_apply]
    by_cases hij : i = j
    · subst hij; simpa using huB i
    · rw [horth i j hij]; simp [hij]
  · intro j
    rw [Basis.mk_apply]
    exact huU j

private theorem plane_smul_mem {k : ℕ} {U : Fin k → Submodule F V}
    {x : V ≃ₗ[F] V} {h : F[X]} [Fact (Irreducible h)]
    (hmaps : ∀ j, ∀ v ∈ U j, x v ∈ U j) (j : Fin k)
    (c : AdjoinRoot h) (v : primaryComponent x.toLinearMap h)
    (hv : (v : V) ∈ U j) : ((c • v : primaryComponent x.toLinearMap h) : V) ∈ U j := by
  obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective c
  rw [coe_mk_smul_primaryComponent]
  exact aeval_mem_of_stable (hmaps j) g hv

private theorem plane_eq_span_basis {k : ℕ} {U : Fin k → Submodule F V}
    {x : V ≃ₗ[F] V} {h : F[X]} [Fact (Irreducible h)]
    (hU : IsPlaneSystem Q U) (hmaps : ∀ j, ∀ v ∈ U j, x v ∈ U j)
    (hE2 : finrank F (AdjoinRoot h) = 2)
    {b : Basis (Fin k) (AdjoinRoot h) (primaryComponent x.toLinearMap h)}
    (hbU : ∀ j, ((b j : primaryComponent x.toLinearMap h) : V) ∈ U j)
    (hb_ne : ∀ j, b j ≠ 0) (j : Fin k) {v : V} (hv : v ∈ U j) :
    ∃ c : AdjoinRoot h, ((c • b j : primaryComponent x.toLinearMap h) : V) = v := by
  classical
  let W := primaryComponent x.toLinearMap h
  let ψ : AdjoinRoot h →ₗ[F] V :=
    { toFun := fun c => ((c • b j : W) : V)
      map_add' := fun c d => by rw [add_smul, Submodule.coe_add]
      map_smul' := fun a c => by
        rw [smul_assoc]
        exact map_smul W.subtype a (c • b j) }
  have hψinj : Function.Injective ψ := by
    intro c d hcd
    have h1 : (c • b j : W) = (d • b j : W) := Subtype.ext hcd
    have h2 : (c - d) • b j = 0 := by
      rw [sub_smul, h1, sub_self]
    have h3 : c - d = 0 := by
      by_contra hne
      have hinv : (c - d)⁻¹ • ((c - d) • b j) = b j := by
        rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
      rw [h2, smul_zero] at hinv
      exact hb_ne j hinv.symm
    exact sub_eq_zero.mp h3
  have hψfin : finrank F (LinearMap.range ψ) = 2 := by
    rw [LinearMap.finrank_range_of_inj hψinj, hE2]
  have hle : LinearMap.range ψ ≤ U j := by
    rintro y ⟨c, rfl⟩
    exact plane_smul_mem hmaps j c (b j) (hbU j)
  have heq : LinearMap.range ψ = U j :=
    Submodule.eq_of_le_of_finrank_eq hle (by rw [hψfin, hU.finrank_eq j])
  have hv' : v ∈ LinearMap.range ψ := by rw [heq]; exact hv
  obtain ⟨c, hc⟩ := LinearMap.mem_range.mp hv'
  exact ⟨c, hc⟩

private theorem apply_eq_on_plane_of_apply_basis {k : ℕ} {U : Fin k → Submodule F V}
    {x : V ≃ₗ[F] V} {h : F[X]} [Fact (Irreducible h)]
    (hU : IsPlaneSystem Q U) (hmaps : ∀ j, ∀ v ∈ U j, x v ∈ U j)
    (hE2 : finrank F (AdjoinRoot h) = 2)
    {b : Basis (Fin k) (AdjoinRoot h) (primaryComponent x.toLinearMap h)}
    (hbU : ∀ j, ((b j : primaryComponent x.toLinearMap h) : V) ∈ U j)
    (hb_ne : ∀ j, b j ≠ 0)
    {z : V ≃ₗ[F] V} (hzG : z ∈ specialBlock Q x h) (j : Fin k)
    (hj : z ((b j : primaryComponent x.toLinearMap h) : V) =
      ((b j : primaryComponent x.toLinearMap h) : V))
    {v : V} (hv : v ∈ U j) : z v = v := by
  obtain ⟨c, hc⟩ := plane_eq_span_basis hU hmaps hE2 hbU hb_ne j hv
  have hzS : z ∈ supportedBlock Q x h := specialBlock_le_supportedBlock h hzG
  let g : ↥(supportedBlock Q x h) := ⟨z, hzS⟩
  have hz_bj : (((blockGL Q x h g : BlockGL x h) :
      Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h))
      (b j) : V) = ((b j : primaryComponent x.toLinearMap h) : V) := by
    rw [coe_blockGL]
    exact hj
  have hM : ((blockGL Q x h g : BlockGL x h) :
      Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) (b j) = b j :=
    Subtype.ext hz_bj
  have hsmul : (((blockGL Q x h g : BlockGL x h) :
      Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) (c • b j) : V) =
      ((c • b j : primaryComponent x.toLinearMap h) : V) := by
    have hlin : ((blockGL Q x h g : BlockGL x h) :
        Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) (c • b j) =
        c • ((blockGL Q x h g : BlockGL x h) :
          Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) (b j) :=
      map_smul _ c (b j)
    rw [hlin, hM]
  have hzact : z ((c • b j : primaryComponent x.toLinearMap h) : V) =
      (((blockGL Q x h g : BlockGL x h) :
        Module.End (AdjoinRoot h) (primaryComponent x.toLinearMap h)) (c • b j) : V) := by
    rw [coe_blockGL]
  rw [← hc, hzact, hsmul, hc]

private theorem polarPerp_pair_eq_iSup {k : ℕ} {U : Fin k → Submodule F V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hU : IsPlaneSystem Q U)
    (hUtop : (⨆ j, U j : Submodule F V) = ⊤) (hdimV : finrank F V = 2 * k)
    (a b : Fin k) (hab : a ≠ b) :
    polarPerp Q (U a ⊔ U b) = ⨆ j ∈ (Finset.univ.erase a).erase b, U j := by
  classical
  have hAeq : (U a ⊔ U b : Submodule F V) = ⨆ j ∈ ({a, b} : Finset (Fin k)), U j := by
    rw [Finset.iSup_insert, Finset.iSup_singleton]
  have hAreg : (QuadraticMap.polarBilin (Q.comp (U a ⊔ U b).subtype)).Nondegenerate := by
    have h := hU.nondeg_biSup ({a, b} : Finset (Fin k))
    rw [show (⨆ j ∈ ({a, b} : Finset (Fin k)), U j) = (U a ⊔ U b) from hAeq.symm] at h
    exact h
  have hdimA : finrank F ↥(U a ⊔ U b : Submodule F V) = 2 * 2 := by
    have h := hU.finrank_biSup ({a, b} : Finset (Fin k))
    rw [show (⨆ j ∈ ({a, b} : Finset (Fin k)), U j) = (U a ⊔ U b) from hAeq.symm,
      Finset.card_pair hab] at h
    simpa using h
  have hdimP : finrank F ↥(polarPerp Q (U a ⊔ U b) : Submodule F V) = 2 * (k - 2) := by
    rw [finrank_polarPerp hQ, hdimA, hdimV]
    omega
  let s : Finset (Fin k) := (Finset.univ.erase a).erase b
  have hb_s : b ∈ Finset.univ.erase a :=
    Finset.mem_erase.mpr ⟨Ne.symm hab, Finset.mem_univ b⟩
  have ha_s : a ∉ s := by simp [s]
  have hb_s' : b ∉ s := by simp [s]
  have hcard_s : s.card = k - 2 := by
    have h1 : (Finset.univ.erase a).card = k - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin]
    have h2 : s.card = (Finset.univ.erase a).card - 1 := by
      dsimp [s]
      rw [Finset.card_erase_of_mem hb_s]
    omega
  have hle : (⨆ j ∈ s, U j) ≤ polarPerp Q (U a ⊔ U b) := by
    refine iSup₂_le fun j hj => ?_
    intro v hv
    refine mem_polarPerp_iff.mpr fun w hw => ?_
    have hja : j ≠ a := fun h => ha_s (h ▸ hj)
    have hjb : j ≠ b := fun h => hb_s' (h ▸ hj)
    obtain ⟨u, hu, w', hw', rfl⟩ := Submodule.mem_sup.mp hw
    have h1 : QuadraticMap.polar Q u v = 0 := hU.perp a j (Ne.symm hja) u hu v hv
    have h2 : QuadraticMap.polar Q w' v = 0 := hU.perp b j (Ne.symm hjb) w' hw' v hv
    rw [QuadraticMap.polar_add_left, h1, h2, add_zero]
  have heq : (⨆ j ∈ s, U j) = polarPerp Q (U a ⊔ U b) :=
    Submodule.eq_of_le_of_finrank_eq hle (by
      rw [hU.finrank_biSup s, hcard_s, hdimP])
  exact heq.symm

private theorem eval_one_ne_zero_of_irreducible {h : F[X]} [Fact (Irreducible h)]
    (hmon : h.Monic) (hne : h ≠ X - 1) : h.eval 1 ≠ 0 := by
  intro h0
  have hdvd : (X - C 1 : F[X]) ∣ h := Polynomial.dvd_iff_isRoot.mpr h0
  have hass := (Polynomial.irreducible_X_sub_C (1 : F)).associated_of_dvd
    (Fact.out : Irreducible h) hdvd
  have heq := Polynomial.eq_of_monic_of_associated (monic_X_sub_C (1 : F)) hmon hass
  exact hne (by simpa using heq.symm)

private theorem primaryComponent_pair_eq {d y : V ≃ₗ[F] V} {h : F[X]} [Fact (Irreducible h)]
    (hself : h = reciprocalPolynomial h) (hne1 : h ≠ X - 1)
    (hmon : h.Monic)
    {A P : Submodule F V} (hAP : IsCompl A P)
    (hA_stable : ∀ x ∈ A, y x ∈ A) (hP_stable : ∀ x ∈ P, y x ∈ P)
    (hyA : ∀ x ∈ A, y x = d x) (hyP : ∀ x ∈ P, y x = x)
    (hA_d : ∀ x ∈ A, d x ∈ A)
    (hA_le_d : A ≤ primaryComponent d.toLinearMap h) :
    primaryComponent y.toLinearMap h = A := by
  classical
  have heval1 : h.eval 1 ≠ 0 := eval_one_ne_zero_of_irreducible hmon hne1
  refine le_antisymm ?_ ?_
  ·
    intro v hv
    have hv0 : aeval y.toLinearMap h v = 0 := mem_primaryComponent.mp hv
    obtain ⟨α, hα, β, hβ, rfl⟩ :=
      Submodule.mem_sup.mp (hAP.sup_eq_top ▸ Submodule.mem_top (x := v))
    rw [map_add] at hv0
    have hαA : aeval y.toLinearMap h α ∈ A := by
      rw [aeval_apply_eq_of_agree hA_stable hyA h hα]
      exact aeval_mem_of_stable hA_d h hα
    have hβP : aeval y.toLinearMap h β ∈ P := aeval_mem_of_stable hP_stable h hβ
    have hα0 : aeval y.toLinearMap h α = 0 := by
      have hmem : aeval y.toLinearMap h α ∈ A ⊓ P := by
        refine ⟨hαA, ?_⟩
        have : aeval y.toLinearMap h α = -(aeval y.toLinearMap h β) := by
          rw [eq_neg_iff_add_eq_zero]; exact hv0
        rw [this]
        exact P.neg_mem hβP
      simpa using hAP.disjoint.le_bot hmem
    have hβ0 : aeval y.toLinearMap h β = 0 := by
      rw [hα0, zero_add] at hv0
      exact hv0
    have hβsmul : aeval y.toLinearMap h β = h.eval 1 • β := by
      rw [Module.End.aeval_apply_of_mem_apply_eq_smul (f := y.toLinearMap) (p := h) (μ := 1)
        (x := β) (by simpa using hyP β hβ)]
    have hβzero : β = 0 := by
      have h1 : h.eval 1 • β = 0 := by rw [← hβsmul]; exact hβ0
      rcases smul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 heval1
      · exact h2
    rw [hβzero, add_zero] at *
    exact hα
  ·
    intro x hx
    refine mem_primaryComponent.mpr ?_
    rw [aeval_apply_eq_of_agree hA_stable hyA h hx]
    exact mem_primaryComponent.mp (hA_le_d hx)

private theorem othersSpace_pair_eq {d y : V ≃ₗ[F] V} {h : F[X]} [Fact (Irreducible h)]
    (hself : h = reciprocalPolynomial h) (hne1 : h ≠ X - 1)
    (hmon : h.Monic)
    {A P : Submodule F V} (hAP : IsCompl A P)
    (hA_stable : ∀ x ∈ A, y x ∈ A) (hP_stable : ∀ x ∈ P, y x ∈ P)
    (hyA : ∀ x ∈ A, y x = d x) (hyP : ∀ x ∈ P, y x = x)
    (hA_d : ∀ x ∈ A, d x ∈ A)
    (hA_le_d : A ≤ primaryComponent d.toLinearMap h) :
    othersSpace y.toLinearMap h = P := by
  classical
  have hrecip : reciprocalPolynomial h = h := hself.symm
  have hP_comp : P ≤ primaryComponent y.toLinearMap (X - (1 : F[X])) := by
    intro v hv
    refine mem_primaryComponent.mpr ?_
    have h1 : aeval y.toLinearMap (X - (1 : F[X])) v = y v - v := by simp
    rw [h1, hyP v hv, sub_self]
  have hP_le : P ≤ othersSpace y.toLinearMap h := by
    rcases eq_or_ne P ⊥ with hPbot | hP_ne
    · rw [hPbot]; exact bot_le
    · obtain ⟨v, hvP, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP_ne
      have hmem : (X - (1 : F[X])) ∈ primaryFactors y.toLinearMap :=
        mem_primaryFactors_of_ne_zero (Polynomial.irreducible_X_sub_C 1) (monic_X_sub_C 1) hv0
          (hP_comp hvP)
      have hne_h : (X - (1 : F[X])) ≠ h := fun hh => hne1 hh.symm
      have hne_recip : (X - (1 : F[X])) ≠ reciprocalPolynomial h := by
        rw [hrecip]; exact hne_h
      exact hP_comp.trans (le_iSup₂_of_le (X - 1) ⟨hmem, hne_h, hne_recip⟩ le_rfl)
  have hothers_le : othersSpace y.toLinearMap h ≤ P := by
    refine iSup_le fun q => iSup_le fun hq => ?_
    intro v hv
    have hq0 : aeval y.toLinearMap q v = 0 := mem_primaryComponent.mp hv
    obtain ⟨α, hαA, β, hβP, rfl⟩ :=
      Submodule.mem_sup.mp (hAP.sup_eq_top ▸ Submodule.mem_top (x := v))
    rw [map_add] at hq0
    have hqα : aeval y.toLinearMap q α = aeval d.toLinearMap q α :=
      aeval_apply_eq_of_agree hA_stable hyA q hαA
    have hqβ : aeval y.toLinearMap q β = q.eval 1 • β := by
      rw [Module.End.aeval_apply_of_mem_apply_eq_smul (f := y.toLinearMap) (p := q) (μ := 1)
        (x := β) (by simpa using hyP β hβP)]
    have hqαA : aeval y.toLinearMap q α ∈ A := aeval_mem_of_stable hA_stable q hαA
    have hqβP : aeval y.toLinearMap q β ∈ P := by
      rw [hqβ]; exact P.smul_mem _ hβP
    have hqα0 : aeval y.toLinearMap q α = 0 := by
      have hmem : aeval y.toLinearMap q α ∈ A ⊓ P := by
        refine ⟨hqαA, ?_⟩
        have : aeval y.toLinearMap q α = -(aeval y.toLinearMap q β) := by
          rw [eq_neg_iff_add_eq_zero]; exact hq0
        rw [this]
        exact P.neg_mem hqβP
      simpa using hAP.disjoint.le_bot hmem
    have hα0 : α = 0 := by
      by_contra hαne
      have hq_irr : Irreducible q := irreducible_of_mem_primaryFactors hq.1
      have hq_mon : q.Monic := monic_of_mem_primaryFactors hq.1
      have hqh : q ≠ h := hq.2.1
      have hnd : ¬ q ∣ h := by
        intro hdvd
        exact hqh (Polynomial.eq_of_monic_of_associated hq_mon hmon
          (hq_irr.associated_of_dvd (Fact.out : Irreducible h) hdvd))
      have hcop : IsCoprime q h := hq_irr.coprime_iff_not_dvd.mpr hnd
      obtain ⟨u, w, huw⟩ := hcop
      have heval := congrArg (fun f : F[X] => aeval d.toLinearMap f α) huw
      simp only [map_add, map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply,
        Module.End.one_apply] at heval
      have hqαd : aeval d.toLinearMap q α = 0 := by rw [← hqα]; exact hqα0
      have hhα : aeval d.toLinearMap h α = 0 := mem_primaryComponent.mp (hA_le_d hαA)
      rw [hqαd, hhα, map_zero, map_zero, add_zero] at heval
      exact hαne heval.symm
    rw [hα0] at hq0
    rw [map_zero, zero_add] at hq0
    rw [hα0, zero_add]
    exact hβP
  exact le_antisymm hothers_le hP_le

private theorem apply_aeval_commute {x z : V ≃ₗ[F] V} (hzx : Commute z x)
    (p : F[X]) (v : V) :
    z (aeval x.toLinearMap p v) = aeval x.toLinearMap p (z v) := by
  have hcommEnd : Commute z.toLinearMap x.toLinearMap := by
    ext w
    exact congrArg (fun e : V ≃ₗ[F] V => e w) hzx.eq
  have h := CFSG.HardMathSupport.Malle.E27Lie.commute_aeval_of_commute
    (f := x.toLinearMap) (g := z.toLinearMap) hcommEnd p
  exact congrArg (fun e : Module.End F V => e v) h.eq

private theorem othersSpace_eq_bot_of_top {d : V ≃ₗ[F] V} {h : F[X]}
    (hd : OddOrderIsometry Q p d)
    (hh : h ∈ primaryFactors d.toLinearMap)
    (hW : primaryComponent d.toLinearMap h = ⊤) :
    othersSpace d.toLinearMap h = ⊥ := by
  rw [eq_bot_iff]
  refine iSup_le fun q => iSup_le fun hq => ?_
  intro v hv
  have hdisj := disjoint_primaryComponent_of_ne hd hq.1 hh hq.2.1
  have hvtop : v ∈ primaryComponent d.toLinearMap h := by
    rw [hW]; exact Submodule.mem_top
  have hmem : v ∈ primaryComponent d.toLinearMap q ⊓ primaryComponent d.toLinearMap h :=
    ⟨hv, hvtop⟩
  simpa using hdisj.le_bot hmem

private theorem blockDet_pair_eq {d y z : V ≃ₗ[F] V} {h : F[X]} [Fact (Irreducible h)]
    (hW : primaryComponent d.toLinearMap h = ⊤)
    {A P : Submodule F V} (hAP : IsCompl A P)
    (hdA : ∀ x ∈ A, d x ∈ A) (hdP : ∀ x ∈ P, d x ∈ P)
    (hyA_stable : ∀ x ∈ A, y x ∈ A) (hyA : ∀ x ∈ A, y x = d x)
    (hAy : primaryComponent y.toLinearMap h = A)
    (hzCent : z ∈ Subgroup.centralizer ({d} : Set (V ≃ₗ[F] V)))
    (hzSd : z ∈ supportedBlock Q d h)
    (hzA : ∀ x ∈ A, z x ∈ A) (hzP : ∀ x ∈ P, z x = x)
    (hzy : Commute z y)
    (hzS : z ∈ supportedBlock Q y h) :
    blockDet Q y h ⟨z, hzS⟩ = blockDet Q d h ⟨z, hzSd⟩ := by
  classical
  let K := AdjoinRoot h
  let W := primaryComponent d.toLinearMap h
  let Ay := primaryComponent y.toLinearMap h
  let zW : W ≃ₗ[K] W :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv K W (centralizerGL d h ⟨z, hzCent⟩)
  have hzW_coe : ∀ x : W, ((zW x : W) : V) = z (x : V) := by
    intro x
    rw [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv]
    exact coe_centralizerGL d h ⟨z, hzCent⟩ x
  let AE : Submodule K W :=
    { carrier := {x | (x : V) ∈ A}
      zero_mem' := A.zero_mem
      add_mem' := by
        intro x y hx hy
        simpa using A.add_mem (x := (x : V)) (y := (y : V)) hx hy
      smul_mem' := fun c x hx => by
        obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective c
        change (((AdjoinRoot.mk h) g • x : W) : V) ∈ A
        rw [coe_mk_smul_primaryComponent]
        exact aeval_mem_of_stable hdA g hx }
  let PE : Submodule K W :=
    { carrier := {x | (x : V) ∈ P}
      zero_mem' := P.zero_mem
      add_mem' := by
        intro x y hx hy
        simpa using P.add_mem (x := (x : V)) (y := (y : V)) hx hy
      smul_mem' := fun c x hx => by
        obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective c
        change (((AdjoinRoot.mk h) g • x : W) : V) ∈ P
        rw [coe_mk_smul_primaryComponent]
        exact aeval_mem_of_stable hdP g hx }
  have hAP_E : IsCompl AE PE := by
    constructor
    · rw [disjoint_iff_inf_le]
      intro x hx
      have hxA : (x : V) ∈ A := by
        have h := hx.1
        dsimp only [AE] at h
        exact h
      have hxP : (x : V) ∈ P := by
        have h := hx.2
        dsimp only [PE] at h
        exact h
      have hxV : (x : V) ∈ A ⊓ P := ⟨hxA, hxP⟩
      have h0 : (x : V) = 0 := by simpa using hAP.disjoint.le_bot hxV
      show x = 0
      exact Subtype.ext h0
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      have hxV : (x : V) ∈ A ⊔ P := by
        simpa [hAP.sup_eq_top] using Submodule.mem_top (x := (x : V))
      obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp hxV
      have huW : u ∈ W := by
        change u ∈ primaryComponent d.toLinearMap h
        rw [hW]; exact Submodule.mem_top
      have hvW : v ∈ W := by
        change v ∈ primaryComponent d.toLinearMap h
        rw [hW]; exact Submodule.mem_top
      have hx_eq : x = (⟨u, huW⟩ : W) + ⟨v, hvW⟩ := Subtype.ext (by simp [huv])
      rw [hx_eq]
      exact Submodule.mem_sup.mpr ⟨⟨u, huW⟩, hu, ⟨v, hvW⟩, hv, rfl⟩
  have hzPE_id : ∀ a ∈ PE, zW a = a := fun a ha => by
    apply Subtype.ext
    rw [hzW_coe]
    exact hzP (a : V) ha
  have hzAE : ∀ a ∈ AE, zW a ∈ AE := by
    intro a ha
    have h1 : ((zW a : W) : V) ∈ A := by
      rw [hzW_coe a]
      exact hzA (a : V) ha
    exact h1
  have hzPE : ∀ a ∈ PE, zW a ∈ PE := by
    intro a ha
    have hz_eq : z (a : V) = (a : V) := by
      rw [← hzW_coe a]
      exact congrArg Subtype.val (hzPE_id a ha)
    have h1 : ((zW a : W) : V) ∈ P := by
      rw [hzW_coe a, hz_eq]
      exact ha
    exact h1
  have hbd : blockDet Q d h ⟨z, hzSd⟩ =
      LinearMap.det (zW : W →ₗ[K] W) := by
    rw [blockDet_apply]
    rfl
  have hdetR : LinearMap.det (zW.toLinearMap.restrict hzAE) =
      LinearMap.det (zW : W →ₗ[K] W) := by
    have h := CFSG.RankThree.PartOne.KCUnitary.det_eq_mul_det_of_isCompl hAP_E
      zW.toLinearMap hzAE hzPE
    have hres : zW.toLinearMap.restrict hzPE = LinearMap.id := by
      ext a
      exact congrArg Subtype.val (hzPE_id a a.2)
    rw [hres, LinearMap.det_id, mul_one] at h
    exact h.symm
  have hzCentY : z ∈ Subgroup.centralizer ({y} : Set (V ≃ₗ[F] V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hzy.symm
  let zAy : Ay ≃ₗ[K] Ay :=
    LinearMap.GeneralLinearGroup.generalLinearEquiv K Ay (centralizerGL y h ⟨z, hzCentY⟩)
  have hzAy_coe : ∀ x : Ay, ((zAy x : Ay) : V) = z (x : V) := by
    intro x
    rw [LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv]
    exact coe_centralizerGL y h ⟨z, hzCentY⟩ x
  have hzAE_inj : Function.Injective (zW.toLinearMap.restrict hzAE) := by
    intro x y hxy
    have hW' : (zW (x : W)) = (zW (y : W)) := congrArg Subtype.val hxy
    exact Subtype.ext (zW.injective hW')
  let zAE : AE ≃ₗ[K] AE :=
    LinearEquiv.ofBijective (zW.toLinearMap.restrict hzAE)
      ⟨hzAE_inj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp hzAE_inj⟩
  have hdet_zAE : LinearMap.det (zAE : AE →ₗ[K] AE) =
      LinearMap.det (zW : W →ₗ[K] W) := by
    have hcoe : (zAE : AE →ₗ[K] AE) = zW.toLinearMap.restrict hzAE := rfl
    rw [hcoe]
    exact hdetR
  let eA : AE ≃ₗ[K] primaryComponent y.toLinearMap h :=
    { toFun := fun x => (⟨(x.1 : V), by
        have hx : (x.1 : V) ∈ A := x.2
        exact hAy.symm ▸ hx⟩ : primaryComponent y.toLinearMap h)
      invFun := fun x =>
        let w : W := ⟨x.1, by
          change x.1 ∈ primaryComponent d.toLinearMap h
          rw [hW]; exact Submodule.mem_top⟩
        (⟨w, by
          show (w : V) ∈ A
          have hx : (x.1 : V) ∈ A := hAy ▸ x.2
          simpa using hx⟩ : AE)
      map_add' := fun x y => by apply Subtype.ext; rfl
      map_smul' := fun c x => by
        obtain ⟨g, rfl⟩ := AdjoinRoot.mk_surjective c
        let yx : primaryComponent y.toLinearMap h :=
          ⟨(x.1 : V), by
            have hx : (x.1 : V) ∈ A := x.2
            exact hAy.symm ▸ hx⟩
        apply Subtype.ext
        change (((AdjoinRoot.mk h) g • (x : W) : W) : V) =
          (((AdjoinRoot.mk h) g • yx : primaryComponent y.toLinearMap h) : V)
        rw [coe_mk_smul_primaryComponent d.toLinearMap h g (x : W)]
        rw [coe_mk_smul_primaryComponent y.toLinearMap h g yx]
        exact (aeval_apply_eq_of_agree hyA_stable hyA g x.2).symm
      left_inv := fun x => by apply Subtype.ext; rfl
      right_inv := fun x => by apply Subtype.ext; rfl }
  have hzAy_eq : zAy = eA.symm.trans (zAE.trans eA) := by
    ext x
    change ((zAy x : Ay) : V) = ((eA (zAE (eA.symm x)) : Ay) : V)
    rw [hzAy_coe x]
    rw [show ((eA (zAE (eA.symm x)) : Ay) : V) =
      ((zW (eA.symm x) : W) : V) from rfl]
    rw [hzW_coe]
    rfl
  have hdet_zAy : LinearMap.det (zAy : Ay →ₗ[K] Ay) =
      LinearMap.det (zW : W →ₗ[K] W) := by
    rw [hzAy_eq, ← LinearEquiv.coe_det (eA.symm.trans (zAE.trans eA))]
    have hconj : LinearEquiv.det (eA.symm.trans (zAE.trans eA)) = LinearEquiv.det zAE := by
      rw [← LinearEquiv.trans_assoc]
      exact LinearEquiv.det_conj zAE eA
    rw [hconj, LinearEquiv.coe_det zAE]
    exact hdet_zAE
  have hbd_y : blockDet Q y h ⟨z, hzS⟩ = LinearMap.det (zAy : Ay →ₗ[K] Ay) := by
    rw [blockDet_apply]
    rfl
  rw [hbd_y, hbd]
  exact hdet_zAy

private theorem blockDet_pair_eq_one {d y z : V ≃ₗ[F] V} {h : F[X]} [Fact (Irreducible h)]
    (hW : primaryComponent d.toLinearMap h = ⊤)
    {A P : Submodule F V} (hAP : IsCompl A P)
    (hdA : ∀ x ∈ A, d x ∈ A) (hdP : ∀ x ∈ P, d x ∈ P)
    (hyA_stable : ∀ x ∈ A, y x ∈ A) (hyA : ∀ x ∈ A, y x = d x)
    (hAy : primaryComponent y.toLinearMap h = A)
    (hzG : z ∈ specialBlock Q d h)
    (hzA : ∀ x ∈ A, z x ∈ A) (hzP : ∀ x ∈ P, z x = x)
    (hzy : Commute z y)
    (hzS : z ∈ supportedBlock Q y h) :
    blockDet Q y h ⟨z, hzS⟩ = 1 := by
  have hzCent : z ∈ Subgroup.centralizer ({d} : Set (V ≃ₗ[F] V)) :=
    (Subgroup.mem_inf.mp (specialBlock_le_isometryCentralizer h hzG)).2
  have hzSd : z ∈ supportedBlock Q d h := specialBlock_le_supportedBlock h hzG
  rw [blockDet_pair_eq hW hAP hdA hdP hyA_stable hyA hAy hzCent hzSd hzA hzP hzy hzS]
  exact blockDet_eq_one_of_mem_specialBlock hzG

private theorem blockDet_d_eq_one_of_mem_pair {d y z : V ≃ₗ[F] V} {h : F[X]}
    [Fact (Irreducible h)]
    (hW : primaryComponent d.toLinearMap h = ⊤)
    {A P : Submodule F V} (hAP : IsCompl A P)
    (hdA : ∀ x ∈ A, d x ∈ A) (hdP : ∀ x ∈ P, d x ∈ P)
    (hyA_stable : ∀ x ∈ A, y x ∈ A) (hyA : ∀ x ∈ A, y x = d x)
    (hAy : primaryComponent y.toLinearMap h = A)
    (hzPair : z ∈ specialBlock Q y h)
    (hzCent : z ∈ Subgroup.centralizer ({d} : Set (V ≃ₗ[F] V)))
    (hzSd : z ∈ supportedBlock Q d h)
    (hzA : ∀ x ∈ A, z x ∈ A) (hzP : ∀ x ∈ P, z x = x)
    (hzy : Commute z y)
    (hzSy : z ∈ supportedBlock Q y h) :
    blockDet Q d h ⟨z, hzSd⟩ = 1 := by
  rw [← blockDet_pair_eq hW hAP hdA hdP hyA_stable hyA hAy hzCent hzSd hzA hzP hzy hzSy]
  exact blockDet_eq_one_of_mem_specialBlock hzPair

private theorem pairBlock_le_specialBlock {d y z : V ≃ₗ[F] V} {h : F[X]}
    [Fact (Irreducible h)] (hd : OddOrderIsometry Q p d)
    (hh : h ∈ primaryFactors d.toLinearMap)
    (hW : primaryComponent d.toLinearMap h = ⊤)
    {A P : Submodule F V} (hAP : IsCompl A P)
    (hdA : ∀ x ∈ A, d x ∈ A) (hdP : ∀ x ∈ P, d x ∈ P)
    (hyA : ∀ x ∈ A, y x = d x) (hyP : ∀ x ∈ P, y x = x)
    (hAy : primaryComponent y.toLinearMap h = A)
    (hothers : othersSpace y.toLinearMap h = P)
    (hzPair : z ∈ specialBlock Q y h) :
    z ∈ specialBlock Q d h := by
  have hzSy : z ∈ supportedBlock Q y h := specialBlock_le_supportedBlock h hzPair
  have hzIsoY := supportedBlock_le_isometryCentralizer (Q := Q) (x := y) h hzSy
  have hzO : z ∈ TauCeti.QuadraticMap.orthogonalGroup Q := (Subgroup.mem_inf.mp hzIsoY).1
  have hzy : Commute z y :=
    ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzIsoY).2) y (by simp)).symm
  have hzP : ∀ x ∈ P, (z : V ≃ₗ[F] V) x = x := by
    intro x hx
    have hx' : x ∈ othersSpace y.toLinearMap h := by rw [hothers]; exact hx
    exact (mem_supportedBlock.mp hzSy).2 x hx'
  have hzA : ∀ x ∈ A, z x ∈ A := by
    intro x hx
    rw [← hAy] at hx ⊢
    refine mem_primaryComponent.mpr ?_
    rw [← apply_aeval_commute hzy h x]
    rw [mem_primaryComponent.mp hx, map_zero]
  have hzCent : Commute z d := by
    ext v
    obtain ⟨α, hαA, β, hβP, hv⟩ :=
      Submodule.mem_sup.mp (hAP.sup_eq_top ▸ Submodule.mem_top (x := v))
    rw [← hv]
    have hdαA : d α ∈ A := hdA α hαA
    have hdβP : d β ∈ P := hdP β hβP
    have hzα : z (d α) = d (z α) := by
      rw [← hyA α hαA]
      exact (congrArg (fun e : V ≃ₗ[F] V => e α) hzy.eq).trans
        (hyA (z α) (hzA α hαA))
    have hzβ : z (d β) = d β := hzP (d β) hdβP
    have hdzβ : d (z β) = d β := by rw [hzP β hβP]
    simp only [LinearEquiv.mul_apply, map_add, hzα, hzβ, hdzβ]
  have hzSd : z ∈ supportedBlock Q d h := by
    refine mem_supportedBlock.mpr ⟨mem_isometryCentralizer.mpr
      ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hzO,
        fun v => congrArg (fun e : V ≃ₗ[F] V => e v) hzCent.eq⟩, ?_⟩
    intro v hv
    rw [othersSpace_eq_bot_of_top hd hh hW] at hv
    have hv0 : v = 0 := by simpa using hv
    rw [hv0, map_zero]
  have hyA_stable : ∀ x ∈ A, y x ∈ A := fun x hx => by rw [hyA x hx]; exact hdA x hx
  have hzCentSub : z ∈ Subgroup.centralizer ({d} : Set (V ≃ₗ[F] V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    exact hzCent.eq.symm
  have hdet : blockDet Q d h ⟨z, hzSd⟩ = 1 :=
    blockDet_d_eq_one_of_mem_pair hW hAP hdA hdP hyA_stable hyA hAy hzPair hzCentSub
      hzSd hzA hzP hzy hzSy
  exact mem_specialBlock.mpr ⟨hzSd, hdet⟩

private theorem mem_pairBlock_of_fixes_perp
    {d : V ≃ₗ[F] V} {h : F[X]} [Fact (Irreducible h)]
    (hne1 : h ≠ X - 1)
    (hW : primaryComponent d.toLinearMap h = ⊤)
    {y z : V ≃ₗ[F] V} {A P : Submodule F V}
    (hAP : IsCompl A P)
    (hyA : ∀ x ∈ A, y x = d x) (hyP : ∀ x ∈ P, y x = x)
    (hA_d : ∀ x ∈ A, d x ∈ A) (hP_d : ∀ x ∈ P, d x ∈ P)
    (hzG : z ∈ specialBlock Q d h)
    (hzA : ∀ x ∈ A, z x ∈ A) (hzP : ∀ x ∈ P, z x = x)
    (hAy : primaryComponent y.toLinearMap h = A)
    (hothers : othersSpace y.toLinearMap h = P) :
    z ∈ specialBlock Q y h := by
  have hzIso := specialBlock_le_isometryCentralizer h hzG
  have hzO : z ∈ TauCeti.QuadraticMap.orthogonalGroup Q := (Subgroup.mem_inf.mp hzIso).1
  have hzd : Commute z d :=
    ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzIso).2) d (by simp)).symm
  have hzA' : ∀ x ∈ A, y x ∈ A := fun x hx => by rw [hyA x hx]; exact hA_d x hx
  have hzP' : ∀ x ∈ P, y x ∈ P := fun x hx => by rw [hyP x hx]; exact hx
  have hcomm_y : (z : V ≃ₗ[F] V) * y = y * z := by
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨α, hαA, β, hβP, hv⟩ :=
      Submodule.mem_sup.mp (hAP.sup_eq_top ▸ Submodule.mem_top (x := v))
    rw [← hv]
    have hzd_app : z (d α) = d (z α) := congrArg (fun e : V ≃ₗ[F] V => e α) hzd.eq
    calc z (y (α + β))
        = z (y α + y β) := by rw [map_add]
      _ = z (d α + β) := by rw [hyA α hαA, hyP β hβP]
      _ = z (d α) + z β := by rw [map_add]
      _ = d (z α) + β := by rw [hzd_app, hzP β hβP]
      _ = y (z α) + y β := by rw [hyA (z α) (hzA α hαA), hyP β hβP]
      _ = y (z α + β) := (map_add y (z α) β).symm
      _ = y (z (α + β)) := by
        rw [map_add z α β, hzP β hβP]
  have hiso_y : z ∈ isometryCentralizer Q y :=
    mem_isometryCentralizer.mpr ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hzO,
      fun v => congrArg (fun e : V ≃ₗ[F] V => e v) hcomm_y⟩
  have hfix_others : ∀ v ∈ othersSpace y.toLinearMap h, z v = v := by
    intro v hv
    rw [hothers] at hv
    exact hzP v hv
  have hsupp : z ∈ supportedBlock Q y h :=
    mem_supportedBlock.mpr ⟨hiso_y, hfix_others⟩
  have hdet : blockDet Q y h ⟨z, hsupp⟩ = 1 :=
    blockDet_pair_eq_one hW hAP hA_d hP_d hzA' hyA hAy hzG hzA hzP hcomm_y hsupp
  exact mem_specialBlock.mpr ⟨hsupp, hdet⟩

theorem specialBlock_le_iSup_specialBlock_pair (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hF4 : 4 ≤ Nat.card F) {k : ℕ}
    (hk : 2 ≤ k) {U : Fin k → Submodule F V} (hU : IsPlaneSystem Q U)
    (htop : (⨆ j, U j : Submodule F V) = ⊤) {d : V ≃ₗ[F] V} (hd : OddOrderIsometry Q p d)
    (hmaps : ∀ j, ∀ x ∈ U j, d x ∈ U j) {h : F[X]} (hh : h ∈ primaryFactors d.toLinearMap)
    (hh1 : h ≠ X - 1) (hUh : ∀ j, U j ≤ primaryComponent d.toLinearMap h)
    (y : Fin k → Fin k → V ≃ₗ[F] V)
    (hy : ∀ a b, a ≠ b → y a b ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
      (∀ x ∈ U a ⊔ U b, y a b x = d x) ∧ ∀ x ∈ polarPerp Q (U a ⊔ U b), y a b x = x) :
    specialBlock Q d h ≤ ⨆ (a : Fin k) (b : Fin k) (_ : a ≠ b), specialBlock Q (y a b) h := by
  classical
  haveI : Fact (Irreducible h) := ⟨irreducible_of_mem_primaryFactors hh⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hself : h = reciprocalPolynomial h :=
    (OddOrderIsometry.reciprocal_eq_of_dvd_card_succ hd hp hpq hh hh1).symm
  have hdeg2 : h.natDegree = 2 :=
    CFSG.RankThree.PartOne.K159.natDegree_eq_two_of_dvd_card_add_one hd hp hp2 hpq hh hh1
  have hW : primaryComponent d.toLinearMap h = ⊤ := by
    rw [eq_top_iff, ← htop]
    exact iSup_le hUh
  have hdimV : finrank F V = 2 * k := by
    have h := hU.finrank_biSup Finset.univ
    have hsup : (⨆ j ∈ Finset.univ, U j : Submodule F V) = ⊤ := by
      rw [← htop]
      simp
    rw [hsup, finrank_top] at h
    simpa using h
  have hE2 : finrank F (AdjoinRoot h) = 2 := by
    rw [CFSG.RankThree.PartOne.KCUnitary.finrank_adjoinRoot, hdeg2]
  obtain ⟨ℓ, f, hUd, B, hcard, hBsymm, hBsep, htr, hrange⟩ :=
    exists_unitary_model_deg_two hd hpodd hh hh1 hself hE2
  haveI : Fact ℓ.Prime := ⟨hUd.prime⟩
  haveI : CharP (AdjoinRoot h) ℓ := hUd.charP
  haveI : Finite (AdjoinRoot h) := hUd.finite
  have hVdim : finrank F (primaryComponent d.toLinearMap h) = 2 * k := by
    rw [hW, finrank_top, hdimV]
  have hfinW : finrank (AdjoinRoot h) (primaryComponent d.toLinearMap h) = k := by
    have hmul := Module.finrank_mul_finrank F (AdjoinRoot h)
      (primaryComponent d.toLinearMap h)
    rw [hE2, hVdim] at hmul
    omega
  obtain ⟨b, hb_orth, hb_U⟩ := exists_adapted_basis hd hh hdeg2 hU hmaps hUh hW
    hBsymm hBsep htr hfinW
  have hb_ne : ∀ j, b j ≠ 0 := by
    intro j hb0
    have h := hb_orth j j
    rw [hb0] at h
    simpa using h
  let G : Subgroup (V ≃ₗ[F] V) := specialBlock Q d h
  let N : Subgroup (V ≃ₗ[F] V) :=
    ⨆ (a : Fin k) (b : Fin k) (_ : a ≠ b), specialBlock Q (y a b) h
  have hmon : h.Monic := monic_of_mem_primaryFactors hh
  have hRG : N ≤ G := by
    refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => ?_
    let A : Submodule F V := U a ⊔ U b
    let P : Submodule F V := polarPerp Q A
    have hAeq : A = ⨆ j ∈ ({a, b} : Finset (Fin k)), U j := by
      dsimp [A]
      rw [Finset.iSup_insert, Finset.iSup_singleton]
    have hAreg : (QuadraticMap.polarBilin (Q.comp A.subtype)).Nondegenerate := by
      have h := hU.nondeg_biSup ({a, b} : Finset (Fin k))
      rwa [← hAeq] at h
    have hAC : IsCompl A P := isCompl_polarPerp hAreg
    have hA_d : ∀ x ∈ A, d x ∈ A := by
      intro x hx
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
      rw [map_add]
      change d u + d w ∈ (U a ⊔ U b : Submodule F V)
      exact Submodule.add_mem _ (Submodule.mem_sup_left (hmaps a u hu))
        (Submodule.mem_sup_right (hmaps b w hw))
    have hA_le : A ≤ primaryComponent d.toLinearMap h := by
      dsimp [A]
      exact sup_le (hUh a) (hUh b)
    have hyA : ∀ x ∈ A, y a b x = d x := fun x hx => (hy a b hab).2.1 x hx
    have hyP : ∀ x ∈ P, y a b x = x := fun x hx => (hy a b hab).2.2 x hx
    have hyA_stable : ∀ x ∈ A, y a b x ∈ A := fun x hx => by
      rw [hyA x hx]; exact hA_d x hx
    have hyP_stable : ∀ x ∈ P, y a b x ∈ P := fun x hx => by rw [hyP x hx]; exact hx
    let s : Finset (Fin k) := (Finset.univ.erase a).erase b
    have hP_eq : P = ⨆ j ∈ s, U j := by
      dsimp [P]
      exact polarPerp_pair_eq_iSup hQ hU htop hdimV a b hab
    have hP_d : ∀ x ∈ P, d x ∈ P := by
      intro x hx
      rw [hP_eq] at hx ⊢
      refine Submodule.iSup_induction _ (motive := fun v => d v ∈ ⨆ j ∈ s, U j) hx
        (fun j v hv => ?_) (by simp) (fun u w hu hw => by
          rw [map_add]; exact Submodule.add_mem _ hu hw)
      refine Submodule.iSup_induction _ (motive := fun v => d v ∈ ⨆ j ∈ s, U j) hv
        (fun hj v hv => ?_) (by simp) (fun u w hu hw => by
          rw [map_add]; exact Submodule.add_mem _ hu hw)
      exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj (hmaps j v hv))
    have hAy : primaryComponent (y a b).toLinearMap h = A :=
      primaryComponent_pair_eq hself hh1 hmon hAC hyA_stable hyP_stable hyA hyP hA_d hA_le
    have hothers : othersSpace (y a b).toLinearMap h = P :=
      othersSpace_pair_eq hself hh1 hmon hAC hyA_stable hyP_stable hyA hyP hA_d hA_le
    intro z hz
    exact pairBlock_le_specialBlock hd hh hW hAC hA_d hP_d hyA hyP hAy hothers
      (z := z) hz

  let Ψ : GL (Fin k) (AdjoinRoot h) ≃*
      LinearMap.GeneralLinearGroup (AdjoinRoot h) (primaryComponent d.toLinearMap h) :=
    Matrix.GeneralLinearGroup.toLin' b
  let θ : ↥(specialBlock Q d h) →* GL (Fin k) (AdjoinRoot h) :=
    Ψ.symm.toMonoidHom.comp (specialBlockGL Q d h)
  let M : Subgroup (GL (Fin k) (AdjoinRoot h)) :=
    (N.subgroupOf (specialBlock Q d h)).map θ
  have hq : 4 ≤ ℓ ^ (f * 1) := by
    rw [show ℓ ^ (f * 1) = ℓ ^ f by rw [mul_one]]
    rw [← hcard]
    exact hF4
  have hθinj : Function.Injective θ := by
    intro z1 z2 hθ
    apply hd.specialBlockGL_injective hh
    have hΨz : ∀ z, Ψ (θ z) = specialBlockGL Q d h z := by
      intro z
      rw [show θ z = Ψ.symm (specialBlockGL Q d h z) from rfl]
      exact Ψ.apply_symm_apply _
    rw [← hΨz z1, ← hΨz z2]
    exact congrArg (fun e => Ψ e) hθ
  let bB : Basis (Fin k) (AdjoinRoot h) (primaryComponent d.toLinearMap h) := b
  have hΨmem : ∀ M : GL (Fin k) (AdjoinRoot h),
      Ψ M ∈ sesqSpecialUnitaryGroup B ↔
        M ∈ CFSG.LieType.Universal.Unitary.SUid hUd.barEquiv k :=
    fun M => toLin'_mem_sesqSpecialUnitaryGroup_iff hUd b hb_orth M
  have hM : ∀ a b : Fin k, a ≠ b → ∀ g ∈ unitarySU ℓ (f * 1) (AdjoinRoot h) k,
      CFSG.LieType.SeitzGeneration.IsCoordBlockOn a b
        (g : Matrix (Fin k) (Fin k) (AdjoinRoot h)) → g ∈ M := by
    intro a b hab g hg hcoord
    have hgSUid : (g : GL (Fin k) (AdjoinRoot h)) ∈
        CFSG.LieType.Universal.Unitary.SUid hUd.barEquiv k := by
      rw [unitarySU, ← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hUd.card_eq_sq k] at hg
      rw [CFSG.RankThree.CentralLiftU.barEquiv_eq_unitaryInvolution hUd]
      exact hg
    have hgsesq : Ψ (g : GL (Fin k) (AdjoinRoot h)) ∈ sesqSpecialUnitaryGroup B :=
      (hΨmem (g : GL (Fin k) (AdjoinRoot h))).mpr hgSUid
    have hg_range : Ψ (g : GL (Fin k) (AdjoinRoot h)) ∈ (specialBlockGL Q d h).range := by
      rw [hrange]; exact hgsesq
    obtain ⟨z, hz_eq⟩ := MonoidHom.mem_range.mp hg_range
    let A : Submodule F V := U a ⊔ U b
    let P : Submodule F V := polarPerp Q A
    have hAeq : A = ⨆ j ∈ ({a, b} : Finset (Fin k)), U j := by
      dsimp [A]
      rw [Finset.iSup_insert, Finset.iSup_singleton]
    have hAreg : (QuadraticMap.polarBilin (Q.comp A.subtype)).Nondegenerate := by
      have h := hU.nondeg_biSup ({a, b} : Finset (Fin k))
      rwa [← hAeq] at h
    have hAC : IsCompl A P := isCompl_polarPerp hAreg
    have hA_d : ∀ x ∈ A, d x ∈ A := by
      intro x hx
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
      rw [map_add]
      change d u + d w ∈ (U a ⊔ U b : Submodule F V)
      exact Submodule.add_mem _ (Submodule.mem_sup_left (hmaps a u hu))
        (Submodule.mem_sup_right (hmaps b w hw))
    have hA_le : A ≤ primaryComponent d.toLinearMap h := by
      dsimp [A]; exact sup_le (hUh a) (hUh b)
    let s : Finset (Fin k) := (Finset.univ.erase a).erase b
    have ha_s : a ∉ s := by simp [s]
    have hb_s' : b ∉ s := by simp [s]
    have hP_eq : P = ⨆ j ∈ s, U j := by
      dsimp [P]; exact polarPerp_pair_eq_iSup hQ hU htop hdimV a b hab
    have hP_d : ∀ x ∈ P, d x ∈ P := by
      intro x hx
      rw [hP_eq] at hx ⊢
      refine Submodule.iSup_induction _ (motive := fun v => d v ∈ ⨆ j ∈ s, U j) hx
        (fun j v hv => ?_) (by simp) (fun u w hu hw => by
          rw [map_add]; exact Submodule.add_mem _ hu hw)
      refine Submodule.iSup_induction _ (motive := fun v => d v ∈ ⨆ j ∈ s, U j) hv
        (fun hj v hv => ?_) (by simp) (fun u w hu hw => by
          rw [map_add]; exact Submodule.add_mem _ hu hw)
      exact Submodule.mem_iSup_of_mem j (Submodule.mem_iSup_of_mem hj (hmaps j v hv))
    have hyA : ∀ x ∈ A, y a b x = d x := fun x hx => (hy a b hab).2.1 x hx
    have hyP : ∀ x ∈ P, y a b x = x := fun x hx => (hy a b hab).2.2 x hx
    have hyA_stable : ∀ x ∈ A, y a b x ∈ A := fun x hx => by
      rw [hyA x hx]; exact hA_d x hx
    have hyP_stable : ∀ x ∈ P, y a b x ∈ P := fun x hx => by rw [hyP x hx]; exact hx
    have hAy : primaryComponent (y a b).toLinearMap h = A :=
      primaryComponent_pair_eq hself hh1 hmon hAC hyA_stable hyP_stable hyA hyP hA_d hA_le
    have hothers : othersSpace (y a b).toLinearMap h = P :=
      othersSpace_pair_eq hself hh1 hmon hAC hyA_stable hyP_stable hyA hyP hA_d hA_le
    have hzG : (z : V ≃ₗ[F] V) ∈ specialBlock Q d h := z.2
    have hz_bj : ∀ j, j ≠ a → j ≠ b →
        (z : V ≃ₗ[F] V) ((bB j : primaryComponent d.toLinearMap h) : V) =
          ((bB j : primaryComponent d.toLinearMap h) : V) := by
      intro j hja hjb
      have hzEnd : ((specialBlockGL Q d h z : BlockGL d h) :
          Module.End (AdjoinRoot h) (primaryComponent d.toLinearMap h)) =
          (Ψ (g : GL (Fin k) (AdjoinRoot h)) :
            Module.End (AdjoinRoot h) (primaryComponent d.toLinearMap h)) := by
        rw [hz_eq]
      have hbΨ : (Ψ (g : GL (Fin k) (AdjoinRoot h)) : Module.End (AdjoinRoot h)
          (primaryComponent d.toLinearMap h)) (bB j) = bB j := by
        apply bB.equivFun.injective
        have hmat : bB.equivFun ((Ψ (g : GL (Fin k) (AdjoinRoot h)) :
            Module.End (AdjoinRoot h) (primaryComponent d.toLinearMap h)) (bB j)) =
            Matrix.mulVec (g : Matrix (Fin k) (Fin k) (AdjoinRoot h)) (bB.equivFun (bB j)) :=
          CFSG.RankThree.CentralLift.equivFun_toLin'_basis_apply bB
            (g : GL (Fin k) (AdjoinRoot h)) (bB j)
        rw [hmat]
        have hsingle : bB.equivFun (bB j) = Pi.single j 1 := by
          funext i
          rw [Module.Basis.equivFun_self, Pi.single_apply]
          by_cases hij : i = j
          · simp [hij]
          · simp [hij, Ne.symm hij]
        rw [hsingle, Matrix.mulVec_single_one]
        funext i
        rw [Matrix.col_apply, hcoord i j (Or.inr ⟨hja, hjb⟩)]
        simp [Pi.single_apply]
      have hzEndApply : ((specialBlockGL Q d h z : BlockGL d h) :
          Module.End (AdjoinRoot h) (primaryComponent d.toLinearMap h)) (bB j) =
          (Ψ (g : GL (Fin k) (AdjoinRoot h)) :
            Module.End (AdjoinRoot h) (primaryComponent d.toLinearMap h)) (bB j) := by
        rw [hzEnd]
      have hcoe : (((specialBlockGL Q d h z : BlockGL d h) :
          Module.End (AdjoinRoot h) (primaryComponent d.toLinearMap h)) (bB j) : V) =
          (z : V ≃ₗ[F] V) (bB j : V) := by
        rw [specialBlockGL, MonoidHom.comp_apply]
        exact coe_blockGL (Q := Q) (x := d) h
          (Subgroup.inclusion (specialBlock_le_supportedBlock (Q := Q) (x := d) h) z) (bB j)
      have hzEndV : (((specialBlockGL Q d h z : BlockGL d h) :
          Module.End (AdjoinRoot h) (primaryComponent d.toLinearMap h)) (bB j) : V) =
          ((Ψ (g : GL (Fin k) (AdjoinRoot h)) :
            Module.End (AdjoinRoot h) (primaryComponent d.toLinearMap h)) (bB j) : V) :=
        congrArg Subtype.val hzEndApply
      have hbΨV : ((Ψ (g : GL (Fin k) (AdjoinRoot h)) :
          Module.End (AdjoinRoot h) (primaryComponent d.toLinearMap h)) (bB j) : V) = (bB j : V) :=
        congrArg Subtype.val hbΨ
      rw [← hcoe]
      exact hzEndV.trans hbΨV
    have hzfix : ∀ j, j ≠ a → j ≠ b → ∀ v ∈ U j, (z : V ≃ₗ[F] V) v = v := by
      intro j hja hjb v hv
      exact apply_eq_on_plane_of_apply_basis (b := bB) hU hmaps hE2 hb_U hb_ne hzG j
        (hz_bj j hja hjb) hv
    have hzP : ∀ x ∈ P, (z : V ≃ₗ[F] V) x = x := by
      intro x hx
      rw [hP_eq] at hx
      refine Submodule.iSup_induction _ (motive := fun v => (z : V ≃ₗ[F] V) v = v) hx
        (fun j v hv => ?_) (by simp) (fun u w hu hw => by rw [map_add, hu, hw])
      refine Submodule.iSup_induction _ (motive := fun v => (z : V ≃ₗ[F] V) v = v) hv
        (fun hj v hv => ?_) (by simp) (fun u w hu hw => by rw [map_add, hu, hw])
      exact hzfix j (fun h => ha_s (h ▸ hj)) (fun h => hb_s' (h ▸ hj)) v hv
    have hzA : ∀ x ∈ A, (z : V ≃ₗ[F] V) x ∈ A := by
      intro x hx
      have hPperp : polarPerp Q P = A := by
        dsimp [P]
        rw [polarPerp, polarPerp,
          LinearMap.BilinForm.orthogonal_orthogonal hQ (isRefl_polarBilin Q) A]
      rw [← hPperp]
      refine mem_polarPerp_iff.mpr fun w hw => ?_
      have hzIso : (z : V ≃ₗ[F] V) ∈ isometryCentralizer Q d :=
        specialBlock_le_isometryCentralizer h z.2
      have hzO : (z : V ≃ₗ[F] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
        (Subgroup.mem_inf.mp hzIso).1
      have h1 : QuadraticMap.polar Q ((z : V ≃ₗ[F] V) x) ((z : V ≃ₗ[F] V) w) =
          QuadraticMap.polar Q x w :=
        TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hzO x w
      rw [QuadraticMap.polar_comm]
      rw [show QuadraticMap.polar Q ((z : V ≃ₗ[F] V) x) w =
          QuadraticMap.polar Q ((z : V ≃ₗ[F] V) x) ((z : V ≃ₗ[F] V) w) by
        rw [hzP w hw], h1]
      exact mem_polarPerp_iff.mp hw x hx
    have hzPair : (z : V ≃ₗ[F] V) ∈ specialBlock Q (y a b) h :=
      mem_pairBlock_of_fixes_perp hh1 hW hAC hyA hyP hA_d hP_d hzG hzA hzP hAy hothers
    have hzN : (z : V ≃ₗ[F] V) ∈ N :=
      Subgroup.mem_iSup_of_mem a (Subgroup.mem_iSup_of_mem b
        (Subgroup.mem_iSup_of_mem hab hzPair))
    refine Subgroup.mem_map.mpr ⟨⟨z, hzG⟩, ?_, ?_⟩
    · exact hzN
    · change Ψ.symm (specialBlockGL Q d h z) = g
      rw [hz_eq]
      exact Ψ.symm_apply_apply g
  have hPhan : unitarySU ℓ (f * 1) (AdjoinRoot h) k ≤ M :=
    CFSG.LieType.SeitzGeneration.unitarySU_le_of_blocks hUd hq hk M hM
  intro g hgG
  have hgSU : θ ⟨g, hgG⟩ ∈ unitarySU ℓ (f * 1) (AdjoinRoot h) k := by
    have hgsesq : Ψ (θ ⟨g, hgG⟩) ∈ sesqSpecialUnitaryGroup B := by
      have hΨθ : Ψ (θ ⟨g, hgG⟩) = specialBlockGL Q d h ⟨g, hgG⟩ := by
        rw [show θ ⟨g, hgG⟩ = Ψ.symm (specialBlockGL Q d h ⟨g, hgG⟩) from rfl]
        exact Ψ.apply_symm_apply _
      rw [hΨθ, ← hrange]
      exact MonoidHom.mem_range.mpr ⟨⟨g, hgG⟩, rfl⟩
    have hSUid : θ ⟨g, hgG⟩ ∈ CFSG.LieType.Universal.Unitary.SUid hUd.barEquiv k :=
      (toLin'_mem_sesqSpecialUnitaryGroup_iff hUd b hb_orth (θ ⟨g, hgG⟩)).mp hgsesq
    rw [unitarySU, ← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hUd.card_eq_sq k,
      ← CFSG.RankThree.CentralLiftU.barEquiv_eq_unitaryInvolution hUd]
    exact hSUid
  have hmemM : θ ⟨g, hgG⟩ ∈ M := hPhan hgSU
  obtain ⟨z, hzN, hzθ⟩ := Subgroup.mem_map.mp hmemM
  have hz_eq : (z : V ≃ₗ[F] V) = g := by
    exact congrArg Subtype.val (hθinj hzθ)
  have hzN' : (z : V ≃ₗ[F] V) ∈ N := Subgroup.mem_subgroupOf.mp hzN
  rw [← hz_eq]
  exact hzN'

end CFSG.StandardType.OmNsRootGen

end
