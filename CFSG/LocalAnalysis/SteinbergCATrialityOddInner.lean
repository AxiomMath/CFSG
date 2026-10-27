module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4Share
import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedComponentPrimes
import CFSG.LocalAnalysis.ComponentInitial.QuasisimpleOddCenterFourGroup
import CFSG.LocalAnalysis.SteinbergCAOddResidualOrderFacts
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTrialityD4CubeReturn
public import CFSG.LieType.Chevalley.OddE7AllInvolutionComponents

public noncomputable section

namespace CFSG.LocalAnalysis.SteinbergCA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.ToralSign CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.ModelFacts CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootDatum

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem d4_exists_datum_isPComponent
    (hp : p ≠ 2)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k) {e : ℕ} (he : 1 ≤ e)
    {x : ModGL TwistTag.D4.tag k}
    (hx : x ∈ fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)))
    (hx1 : x ≠ 1) (hx2 : x ^ 2 = 1) {L : Subgroup (ModGL TwistTag.D4.tag k)}
    (hL : L ≤ ⁅fixedPointsIn (adjointGroup TwistTag.D4.tag k)
        (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)),
        fixedPointsIn (adjointGroup TwistTag.D4.tag k)
          (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k))⁆ ⊓
          Subgroup.centralizer {x})
    (hLc : CFSG.IsPComponent 2 (L.subgroupOf (⁅fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k)),
      fixedPointsIn (adjointGroup TwistTag.D4.tag k)
      (frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k))⁆ ⊓
        Subgroup.centralizer {x}))) :
    ∃ (D : OrthogonalSemilinearFixedRootDatum TwistTag.D4.tag p k)
      (J₀ : Subgroup (adjointGroup TwistTag.D4.tag k)),
      D.χ = signMaskChar TwistTag.D4.tag 4 ∧
      (∀ γ, D.θ (toReal γ) =
        toReal (thetaMap (wordElt TwistTag.D4.tag []) TwistTag.D4.perm γ)) ∧
      Finite D.totalFixedGroup ∧ J₀ ≤ D.totalFixedGroup ∧
      CFSG.IsPComponent 2 (J₀.subgroupOf D.totalFixedGroup) ∧ Nonempty (L ≃* J₀) := by
  classical
  obtain ⟨-, -, h4⟩ := rational_toral_sign_diagram_arithmetic
  obtain ⟨-, -, n4⟩ := rational_toral_twist_semilinear_pinning_normalization (k := k) p hp e he
  obtain ⟨r, hr, g₁, -, -, hg₁x, hcomp⟩ := exists_twisted_toral_reduction p
    TwistTag.D4 hp he d4SignDiagramReps h4.permChar_eq h4.exists_rep (untwistAt_d4 p hp e) hx hx2
  have hrm : r.mask = 4 := by
    rcases List.mem_cons.1 (hr : r ∈ ⟨0, 1, 1, d4OmegaWords0⟩ :: [⟨4, 3, 4, d4OmegaWords4⟩]) with
      rfl | hr'
    · exfalso
      apply hx1
      have h0 : signMaskTuple TwistTag.D4.tag k 0 = 1 := by
        funext j
        simp [signMaskTuple]
      have e0 : g₁ * x * g₁⁻¹ = 1 := by
        rw [hg₁x]
        change rootDiagUnit TwistTag.D4.tag
          (signCharTuple (signMaskChar TwistTag.D4.tag 0)) = 1
        rw [signCharTuple_signMaskChar, h0, rootDiagUnit_one]
      exact mul_left_cancel ((mul_inv_eq_one.1 e0).trans (mul_one g₁).symm)
    · obtain rfl := List.mem_singleton.1 hr'
      rfl
  set χ := signMaskChar TwistTag.D4.tag r.mask with hχ
  set F := frobTwistGL TwistTag.D4.tag k p e (diagramMap TwistTag.D4 k) with hF
  set M := torusGroup TwistTag.D4.tag k ⊔ rootSpan TwistTag.D4.tag k (kernelRoots χ) with hM_def
  obtain ⟨hJle, hJc⟩ := (hcomp L).1 ⟨hL, hLc⟩
  set J := L.map (MulAut.conj g₁).toMonoidHom with hJ_def
  have hD : (adjointGroup TwistTag.D4.tag k).map
      (MulAut.conj (diagramMap TwistTag.D4 k)).toMonoidHom = adjointGroup TwistTag.D4.tag k :=
    map_conj_diagramMap TwistTag.D4 k (Or.inl rfl)
  have hRfin : Finite (fixedPointsIn (adjointGroup TwistTag.D4.tag k) F) :=
    finite_fixedPointsIn_frobTwistGL p he (by decide)
      (units_map_entrywiseHom_diagramMap (t := TwistTag.D4) (iterateFrobenius k p e))
      (diagramMap_pow_order TwistTag.D4 k)
  have hMG : M ≤ adjointGroup TwistTag.D4.tag k :=
    sup_le torusGroup_le_adjointGroup (iSup₂_le fun α _ => rootSubgroup_le_adjointGroup α)
  have hMFle : fixedPointsIn M F ≤ fixedPointsIn (adjointGroup TwistTag.D4.tag k) F :=
    inf_le_inf_right _ hMG
  have hMFfin : Finite (fixedPointsIn M F) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hMFle)
  by_cases hne : (kernelRoots χ).Nonempty
  swap
  · exfalso
    rw [Set.not_nonempty_iff_eq_empty] at hne
    exact not_isPComponent_of_kernelRoots_eq_empty hne (inf_le_left : fixedPointsIn M F ≤ M)
      _ hJc
  have hθ : ThetaProperties TwistTag.D4.perm 3 χ (wordElt TwistTag.D4.tag []) :=
    h4.theta r hr [] (nil_mem_omegaWords_d4 hr)
  obtain ⟨D, h, hhT, hDχ, -, hDθ, -, hX⟩ := exists_pinned_datum p hp hk he
    (τ := TwistTag.D4.tag) (Or.inl rfl) (ρ := TwistTag.D4.perm) (TwistTag.cartan_perm .D4)
    symmetrizedCartan_perm_D4 hθ
    (Q₀ := wordWeylMatrix TwistTag.D4.tag k [] * diagramMap TwistTag.D4 k)
    (fun γ hγ => wordWeylMatrix_mul_diagramMap_conj_pinnedX TwistTag.D4 [] hγ)
    (mul_mem (wordWeylMatrix_mem_normalizer []) (diagramMap_mem_normalizer TwistTag.D4))
    (map_conj_wordWeylMatrix_mul [] hD) (n4 r hr [] (nil_mem_omegaWords_d4 hr)) hne
  have hQ₀ : wordWeylMatrix TwistTag.D4.tag k [] * diagramMap TwistTag.D4 k =
      diagramMap TwistTag.D4 k := by
    rw [wordWeylMatrix_nil, one_mul]
  rw [hQ₀] at hX
  obtain ⟨a₀, ha₀⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
  obtain ⟨s, hs⟩ := exists_rootDiagUnit_frob_eq p TwistTag.D4 he a₀⁻¹
  set u := rootDiagUnit TwistTag.D4.tag s with hu_def
  have hFu : F u = h⁻¹ * u := by
    rw [hs, ← rootDiagUnit_inv, ← ha₀]
  have huM : u ∈ M := Subgroup.mem_sup_left (rootDiagUnit_mem_torusGroup s)
  have hFh : ∀ y, frobTwistGL TwistTag.D4.tag k p e (h * diagramMap TwistTag.D4 k) y =
      h * F y * h⁻¹ := fun y => frobTwistGL_mul_left_apply p e h _ y
  have hconj : (fixedPointsIn M F).map (MulAut.conj u).toMonoidHom =
      fixedPointsIn M (frobTwistGL TwistTag.D4.tag k p e (h * diagramMap TwistTag.D4 k)) :=
    map_conj_fixedPointsIn_eq M F _ huM hFh hFu
  obtain ⟨hJDle, hJDc⟩ := (isPComponent_subgroupOf_map_conj_iff u hconj 2 Nat.prime_two J).1
    ⟨hJle, hJc⟩
  set Mh := fixedPointsIn M (frobTwistGL TwistTag.D4.tag k p e (h * diagramMap TwistTag.D4 k))
    with hMh_def
  set X := D.totalFixedGroup with hX_def
  set JD := J.map (MulAut.conj u).toMonoidHom with hJD_def
  have hJDG : JD ≤ adjointGroup TwistTag.D4.tag k :=
    hJDle.trans ((inf_le_left : Mh ≤ M).trans hMG)
  set J₀ := JD.subgroupOf (adjointGroup TwistTag.D4.tag k) with hJ₀_def
  have hJ₀X : J₀ ≤ X := by
    intro x hx
    have hx' : (x : ModGL TwistTag.D4.tag k) ∈ JD := hx
    have hmem : (x : ModGL TwistTag.D4.tag k) ∈ X.map (adjointGroup TwistTag.D4.tag k).subtype := by
      rw [hX]
      exact hJDle hx'
    obtain ⟨y, hy, hyx⟩ := hmem
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  let eX : X ≃* Mh :=
    (X.equivMapOfInjective (adjointGroup TwistTag.D4.tag k).subtype
      (adjointGroup TwistTag.D4.tag k).subtype_injective).trans (MulEquiv.subgroupCongr hX)
  have heX : ∀ x : X, ((eX x : Mh) : ModGL TwistTag.D4.tag k) =
      (((x : adjointGroup TwistTag.D4.tag k)) : ModGL TwistTag.D4.tag k) := fun x => rfl
  have hMhfin : Finite Mh := by
    rw [← hconj]
    exact Finite.of_equiv _ ((MulAut.conj u).subgroupMap (fixedPointsIn M F)).toEquiv
  have hXfin : Finite X := Finite.of_equiv _ eX.symm.toEquiv
  have hJ₀comp : CFSG.IsPComponent 2 (J₀.subgroupOf X) := by
    have h1 := isPComponent_map_of_isPComponent 2 eX.symm hJDc
    have h2 : (JD.subgroupOf Mh).map eX.symm.toMonoidHom = J₀.subgroupOf X := by
      ext x
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨y, hy, rfl⟩
        have : (((eX.symm y : X) : adjointGroup TwistTag.D4.tag k) : ModGL TwistTag.D4.tag k) =
            (y : ModGL TwistTag.D4.tag k) := by
          have := heX (eX.symm y)
          rw [MulEquiv.apply_symm_apply] at this
          exact this.symm
        change (((eX.symm y : X) : adjointGroup TwistTag.D4.tag k) :
          ModGL TwistTag.D4.tag k) ∈ JD
        rw [this]
        exact hy
      · intro hx
        refine ⟨eX x, ?_, MulEquiv.symm_apply_apply eX x⟩
        change ((eX x : Mh) : ModGL TwistTag.D4.tag k) ∈ JD
        rw [heX]
        exact hx
    rwa [h2] at h1
  refine ⟨D, J₀, by rw [hDχ, hχ, hrm], hDθ, hXfin, hJ₀X, hJ₀comp,
    ⟨(L.equivMapOfInjective _ (MulAut.conj g₁).injective).trans
      ((J.equivMapOfInjective _ (MulAut.conj u).injective).trans
        (Subgroup.subgroupOfEquivOfLe hJDG).symm)⟩⟩

theorem d4_central_mem_orbitGroup
    {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [CharP k p]
    [IsAlgClosed k] (D : OrthogonalSemilinearFixedRootDatum TwistTag.D4.tag p k)
    (hχ : D.χ = signMaskChar TwistTag.D4.tag 4)
    (hDθ : ∀ γ, D.θ (toReal γ) =
      toReal (thetaMap (wordElt TwistTag.D4.tag []) TwistTag.D4.perm γ))
    (J' : Set.range D.classOrbit) (hne : (D.withOrbit J').orbits.Nonempty) :
    rootDiagUnit TwistTag.D4.tag (signMaskTuple TwistTag.D4.tag k 4) ∈
        (D.withOrbit J').orbitGroup ∧
      rootDiagUnit TwistTag.D4.tag (signMaskTuple TwistTag.D4.tag k 4) ≠ 1 ∧
      ∀ y ∈ (D.withOrbit J').orbitGroup,
        rootDiagUnit TwistTag.D4.tag (signMaskTuple TwistTag.D4.tag k 4) * y =
          y * rootDiagUnit TwistTag.D4.tag (signMaskTuple TwistTag.D4.tag k 4) := by
  obtain ⟨-, -, h4⟩ := rational_toral_sign_diagram_arithmetic
  set D' := D.withOrbit J' with hD'
  set d := rootDiagUnit TwistTag.D4.tag (signMaskTuple TwistTag.D4.tag k 4) with hd
  have hk2 : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact D.odd
  obtain ⟨r, hr, hr4⟩ : ∃ r ∈ d4SignDiagramReps, r.mask = 4 :=
    ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), rfl⟩
  have hθ : ThetaProperties TwistTag.D4.perm 3 D'.χ (wordElt TwistTag.D4.tag []) := by
    have h := h4.theta r hr [] (nil_mem_omegaWords_d4 hr)
    rw [hr4] at h
    change ThetaProperties TwistTag.D4.perm 3 D.χ (wordElt TwistTag.D4.tag [])
    rw [hχ]
    exact h
  have hodd : ∀ {O : Set (Fin TwistTag.D4.tag.rank → ℤ)}, O ∈ D'.orbits → Odd (orbitCard O) := by
    intro O hO
    rcases orbitCard_eq_of_thetaProperties D' hθ hDθ hO with h | h <;> rw [h]
    · exact odd_one
    · exact ⟨1, rfl⟩
  have hneg : ∀ {O : Set (Fin TwistTag.D4.tag.rank → ℤ)}, O ∈ D'.orbits →
      D'.orbitMap O (-1) = d :=
    fun hO => orbitMap_neg_one_d4 D' hχ hodd hO
  obtain ⟨O, hO⟩ := hne
  refine ⟨hneg hO ▸ D'.orbitMap_mem_orbitGroup hO (-1), ?_, fun y hy => ?_⟩
  · intro h
    have h1 : rootDiagUnit TwistTag.D4.tag (signMaskTuple TwistTag.D4.tag k 4) =
        rootDiagUnit TwistTag.D4.tag 1 := by
      rw [rootDiagUnit_one]
      exact h
    have h2 := congrFun (rootDiagUnit_injective h1) ⟨2, by decide⟩
    simp only [signMaskTuple, Pi.one_apply] at h2
    have h3 : (-1 : kˣ) = 1 := by simpa using h2
    have h4 : (-1 : k) = 1 := congrArg Units.val h3
    have h5 : (2 : k) = 0 := by linear_combination -h4
    exact Ring.two_ne_zero hk2 h5
  ·
    have hle : D'.orbitGroup ≤ Subgroup.centralizer {d} := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨O', hO', c, rfl | rfl⟩ <;> rw [SetLike.mem_coe,
        Subgroup.mem_centralizer_singleton_iff, ← hneg hO']
      · change D'.orbitMap O' (uSL c) * D'.orbitMap O' (-1) =
          D'.orbitMap O' (-1) * D'.orbitMap O' (uSL c)
        rw [← D'.orbitMap_mul hO', ← D'.orbitMap_mul hO', neg_one_mul, mul_neg_one]
      · change D'.orbitMap O' (vSL c) * D'.orbitMap O' (-1) =
          D'.orbitMap O' (-1) * D'.orbitMap O' (vSL c)
        rw [← D'.orbitMap_mul hO', ← D'.orbitMap_mul hO', neg_one_mul, mul_neg_one]
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm

theorem triality_odd_inner_fixed_no_even_simple
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hf : 1 ≤ f) (F : Type) [Field F] [Finite F] (hF : Nat.card F = (p ^ f) ^ 3)
    (σ : F ≃+* F) (hσ : ∀ c, σ c = c ^ (p ^ f))
    (t : graphFixedRootGroup TwistTag.D4 F σ.toRingHom) (ht1 : t ≠ 1) (ht2 : t * t = 1)
    (S : Subgroup ((MulAut.conj t).toMonoidHom.eqLocus
      (MonoidHom.id (graphFixedRootGroup TwistTag.D4 F σ.toRingHom))))
    (hSn : S.Normal) (hSs : IsSimpleGroup S) (hSnab : ∃ a b : S, a * b ≠ b * a)
    (h2 : 2 ∣ Nat.card S) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd (p ^ f) := (hp.eq_two_or_odd'.resolve_left hp2).pow
  have : CharP F p := finite_field_prime_power_characteristic hp (by omega : 1 ≤ 3 * f)
    (by rw [hF, ← pow_mul, mul_comm])
  have : CharP (AlgebraicClosure F) p :=
    charP_of_injective_algebraMap (algebraMap F (AlgebraicClosure F)).injective p
  have hk := isAlgebraic_zmod_of_isAlgClosure p F (AlgebraicClosure F)
  obtain ⟨-, -, -, -, -, -, hder⟩ := odd_diagram_Frobenius_fixed_derived_root_group TwistTag.D4
    hp hf hodd F hF σ.toRingHom hσ (AlgebraicClosure F) (iterateFrobenius (AlgebraicClosure F) p f)
    (fun c => iterateFrobenius_def p f c)
  obtain ⟨ι, hιdef⟩ : ∃ ι : ModGL TwistTag.D4.tag F →* ModGL TwistTag.D4.tag (AlgebraicClosure F),
      ι = baseChangeGL (algebraMap F (AlgebraicClosure F)) := ⟨_, rfl⟩
  have hιinj : Function.Injective ι := hιdef ▸ baseChangeGL_injective _
  set R := fixedPointsIn (adjointGroup TwistTag.D4.tag (AlgebraicClosure F))
    (frobTwistGL TwistTag.D4.tag (AlgebraicClosure F) p f
      (diagramMap TwistTag.D4 (AlgebraicClosure F))) with hR
  have hRA : ⁅R, R⁆ = (graphFixedRootGroup TwistTag.D4 F σ.toRingHom).map ι := hιdef ▸ hder
  set x := ι t with hx
  let N : Subgroup (ModGL TwistTag.D4.tag (AlgebraicClosure F)) :=
    ⁅R, R⁆ ⊓ Subgroup.centralizer {x}
  have hmemN : ∀ y : (MulAut.conj t).toMonoidHom.eqLocus
      (MonoidHom.id (graphFixedRootGroup TwistTag.D4 F σ.toRingHom)),
      ι ((y : graphFixedRootGroup TwistTag.D4 F σ.toRingHom) : ModGL TwistTag.D4.tag F) ∈ N := by
    intro y
    refine ⟨by rw [hRA]; exact ⟨_, (y : graphFixedRootGroup TwistTag.D4 F σ.toRingHom).2, rfl⟩,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hy : t * (y : graphFixedRootGroup TwistTag.D4 F σ.toRingHom) * t⁻¹ = y := y.2
    have hty : t * (y : graphFixedRootGroup TwistTag.D4 F σ.toRingHom) = y * t :=
      mul_inv_eq_iff_eq_mul.1 hy
    rw [hx, ← map_mul, ← map_mul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hty]
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (MulAut.conj t).toMonoidHom.eqLocus
      (MonoidHom.id (graphFixedRootGroup TwistTag.D4 F σ.toRingHom)) →* N,
      ∀ y, ((Φ y : N) : ModGL TwistTag.D4.tag (AlgebraicClosure F)) =
        ι ((y : graphFixedRootGroup TwistTag.D4 F σ.toRingHom) : ModGL TwistTag.D4.tag F) :=
    ⟨(ι.comp ((graphFixedRootGroup TwistTag.D4 F σ.toRingHom).subtype.comp
      ((MulAut.conj t).toMonoidHom.eqLocus
        (MonoidHom.id (graphFixedRootGroup TwistTag.D4 F σ.toRingHom))).subtype)).codRestrict
      N hmemN, fun _ => rfl⟩
  have hΦinj : Function.Injective Φ := fun y z h =>
    Subtype.ext (Subtype.ext (hιinj (by rw [← hΦ, ← hΦ, h])))
  have hΦsurj : Function.Surjective Φ := by
    rintro ⟨z, hzR, hzx⟩
    rw [hRA] at hzR
    obtain ⟨a, ha, rfl⟩ := hzR
    have hax : ι a * x = x * ι a := Subgroup.mem_centralizer_singleton_iff.1 hzx
    rw [hx, ← map_mul, ← map_mul] at hax
    have hta : t * ⟨a, ha⟩ = ⟨a, ha⟩ * t := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact (hιinj hax).symm
    have hmem : (⟨a, ha⟩ : graphFixedRootGroup TwistTag.D4 F σ.toRingHom) ∈
        (MulAut.conj t).toMonoidHom.eqLocus
          (MonoidHom.id (graphFixedRootGroup TwistTag.D4 F σ.toRingHom)) := by
      change t * ⟨a, ha⟩ * t⁻¹ = ⟨a, ha⟩
      rw [hta, mul_inv_cancel_right]
    exact ⟨⟨⟨a, ha⟩, hmem⟩, Subtype.ext (hΦ _)⟩
  let L' : Subgroup N := S.map Φ
  let eS : S ≃* L' := S.equivMapOfInjective Φ hΦinj
  have := hSs
  have hL'n : L'.Normal := hSn.map Φ hΦsurj
  have hL's : IsSimpleGroup L' := eS.symm.isSimpleGroup
  have hL'nab : ∃ a b : L', a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hSnab
    exact ⟨eS a, eS b, fun h' => hab (eS.injective
      ((MulEquiv.map_mul eS a b).trans (h'.trans (MulEquiv.map_mul eS b a).symm)))⟩
  have hNfin : Finite N := by
    have hRfin : Finite R := finite_fixedPointsIn_frobTwistGL p hf (by decide)
      (units_map_entrywiseHom_diagramMap (t := TwistTag.D4)
        (iterateFrobenius (AlgebraicClosure F) p f))
      (diagramMap_pow_order TwistTag.D4 (AlgebraicClosure F))
    have hNR : N ≤ R := inf_le_left.trans (Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb))
    exact Finite.of_injective _ (Subgroup.inclusion_injective hNR)
  have hL'c : CFSG.IsPComponent 2 L' := isPComponent_two_of_normal_simple L' hL'n hL's hL'nab
    (by rwa [← Nat.card_congr eS.toEquiv])
  have hxR' : x ∈ ⁅R, R⁆ := by
    rw [hRA]
    exact ⟨_, t.2, rfl⟩
  have hxR : x ∈ R := Subgroup.commutator_le.2 (fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)) hxR'
  have hx1 : x ≠ 1 := fun h => ht1 (Subtype.ext (hιinj (h.trans (map_one ι).symm)))
  have hx2 : x ^ 2 = 1 := by
    rw [hx, sq, ← map_mul]
    change ι ((t * t : graphFixedRootGroup TwistTag.D4 F σ.toRingHom) : ModGL TwistTag.D4.tag F) = 1
    rw [ht2]
    exact map_one ι
  have hLsub : (L'.map N.subtype).subgroupOf N = L' :=
    Subgroup.comap_map_eq_self_of_injective N.subtype_injective L'
  obtain ⟨D, J₀, hDχ, hDθ, hXfin, hJ₀X, hJ₀c, ⟨eL⟩⟩ := d4_exists_datum_isPComponent p hp2 hk hf
    hxR hx1 hx2 (L := L'.map N.subtype) (Subgroup.map_subtype_le L') (by rw [hLsub]; exact hL'c)
  let eJ : S ≃* J₀ := (eS.trans (L'.equivMapOfInjective _ N.subtype_injective)).trans eL
  have hJ₀s : IsSimpleGroup J₀ := eJ.symm.isSimpleGroup
  have hJ₀nab : ∃ a b : J₀, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hSnab
    exact ⟨eJ a, eJ b, fun h' => hab (eJ.injective
      ((MulEquiv.map_mul eJ a b).trans (h'.trans (MulEquiv.map_mul eJ b a).symm)))⟩
  have hJ₀comp : CFSG.IsComponent (J₀.subgroupOf D.totalFixedGroup) := by
    obtain ⟨-, -, hsub, -, -⟩ := hJ₀c
    refine ⟨?_, hsub⟩
    have : IsSimpleGroup (J₀.subgroupOf D.totalFixedGroup) :=
      (Subgroup.subgroupOfEquivOfLe hJ₀X).isSimpleGroup
    exact isQuasisimple_of_isSimpleGroup (by
      obtain ⟨a, b, hab⟩ := hJ₀nab
      refine ⟨(Subgroup.subgroupOfEquivOfLe hJ₀X).symm a,
        (Subgroup.subgroupOfEquivOfLe hJ₀X).symm b, fun h' => hab ?_⟩
      apply (Subgroup.subgroupOfEquivOfLe hJ₀X).symm.injective
      rw [map_mul, map_mul, h'])
  obtain ⟨J', hne, hJ₀eq⟩ := D.exists_eq_orbitGroupC_of_isComponent hXfin hJ₀X hJ₀comp
  obtain ⟨hdmem, hd1, hdcomm⟩ := d4_central_mem_orbitGroup D hDχ hDθ J' hne
  have hdJ : (⟨_, (D.withOrbit J').orbitGroup_le_adjointGroup hdmem⟩ :
      adjointGroup TwistTag.D4.tag (AlgebraicClosure F)) ∈ J₀ := by
    rw [hJ₀eq]
    exact (D.withOrbit J').mk_mem_orbitGroupC hdmem
  have hZ := center_eq_bot_of_isSimpleGroup hJ₀nab
  have hdZ : (⟨_, hdJ⟩ : J₀) ∈ Subgroup.center J₀ := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Subtype.ext
    have hy : ((y : adjointGroup TwistTag.D4.tag (AlgebraicClosure F)) :
        ModGL TwistTag.D4.tag (AlgebraicClosure F)) ∈ (D.withOrbit J').orbitGroup := by
      have h1 : (y : adjointGroup TwistTag.D4.tag (AlgebraicClosure F)) ∈
          (D.withOrbit J').orbitGroupC := by
        rw [← hJ₀eq]
        exact y.2
      exact (D.withOrbit J').coe_mem_orbitGroup_of_mem_orbitGroupC h1
    exact (hdcomm _ hy).symm
  rw [hZ, Subgroup.mem_bot] at hdZ
  exact hd1 (congrArg Subtype.val (congrArg Subtype.val hdZ))

end CFSG.LocalAnalysis.SteinbergCA
