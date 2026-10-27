module

public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.PlaneTorus
public import CFSG.ClassicalGroups.Orthogonal.UnitaryOmega.Blocks
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoOmCoord
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9SignOmega
public import CFSG.RankThree.PartOne.S11d.OrthDicksonOmega
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.End.OrderTwoThree
public import CFSG.ClassicalGroups.Orthogonal.RootGroupNormalizer
public import CFSG.HardMathSupport.Dickson.Bal207.OrthD4Loc
public import CFSG.Holt.Fixed
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.Sec5Setup
public import CFSG.RankThree.PartOne.FOC.CompCommutator
public import CFSG.RankThree.PartOne.KC.OrthogonalAnchoredGeneration
public import CFSG.RankThree.PartOne.S15K.FixedWitt
public import CFSG.RankThree.PartOne.S15K.LayerModel

public section

namespace CFSG.StandardType.OrthAnchor

open CFSG.ClassicalGroups.Orthogonal.UnitaryOmega CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.PhanDn
open CFSG.LieType.BorelTits QuadraticMap CFSG.Timmesfeld.ClassicalOrders Module
open CFSG.StandardType.ChoiceTwoOm CFSG.RankThree.OrthogonalInvolutions
open Multiplicative

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {F K : Type} [Field F] [Field K] [Algebra F K] [Finite K] [CharP K 2]
  [CharP F 2]

noncomputable def zetaOfChi (χ : Multiplicative (ZMod 3) →* Kˣ) : K :=
  (χ (Multiplicative.ofAdd (1 : ZMod 3)) : K)

private theorem zetaOfChi_ne_zero (χ : Multiplicative (ZMod 3) →* Kˣ) :
    zetaOfChi χ ≠ 0 := by
  exact (χ (Multiplicative.ofAdd (1 : ZMod 3))).ne_zero

private theorem zetaOfChi_ne_one (χ : Multiplicative (ZMod 3) →* Kˣ)
    (hχ : Function.Injective χ) : zetaOfChi χ ≠ 1 := by
  intro h
  have h1 : χ (Multiplicative.ofAdd (1 : ZMod 3)) = 1 := Units.ext h
  have h2 : Multiplicative.ofAdd (1 : ZMod 3) = 1 := hχ (by rw [h1, map_one])
  have h3 : (1 : ZMod 3) = 0 := by simpa using congrArg Multiplicative.toAdd h2
  exact one_ne_zero h3

private theorem zetaOfChi_pow_three (χ : Multiplicative (ZMod 3) →* Kˣ) :
    zetaOfChi χ ^ 3 = 1 := by
  have h := zmodHom_pow_eq_one_of_dvd (p := 3) (N := 3) (dvd_refl 3) χ
    (Multiplicative.ofAdd (1 : ZMod 3))
  have hval := congrArg Units.val h
  simpa [zetaOfChi, Units.val_pow_eq_pow_val, Units.val_one] using hval

private theorem zetaOfChi_poly (χ : Multiplicative (ZMod 3) →* Kˣ)
    (hχ : Function.Injective χ) : zetaOfChi χ ^ 2 + zetaOfChi χ + 1 = 0 := by
  have h3 : zetaOfChi χ ^ 3 = 1 := zetaOfChi_pow_three χ
  have h1 : zetaOfChi χ ≠ 1 := zetaOfChi_ne_one χ hχ
  have hfac := TauCeti.one_sub_mul_one_add_add_sq_of_pow_three_eq_one h3
  have hne : (1 - zetaOfChi χ) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hp : 1 + zetaOfChi χ + zetaOfChi χ ^ 2 = 0 :=
    (mul_eq_zero.mp hfac).resolve_left hne
  simpa [add_comm, add_left_comm, add_assoc] using hp

private theorem zetaOfChi_outside (E : QuadExt F K (unitaryInvolution K 2 1))
    (χ : Multiplicative (ZMod 3) →* Kˣ) (hχ : Function.Injective χ) :
    zetaOfChi χ ∉ Set.range (algebraMap F K) := by
  rintro ⟨a, ha⟩
  have hζ0 : zetaOfChi χ ≠ 0 := zetaOfChi_ne_zero χ
  have hζ1 : zetaOfChi χ ≠ 1 := zetaOfChi_ne_one χ hχ
  have hfix := E.fix a
  rw [ha, unitaryInvolution_apply] at hfix
  have hsq : zetaOfChi χ ^ 2 = zetaOfChi χ := by
    simpa [show (2 : ℕ) ^ 1 = 2 by norm_num] using hfix
  have hfac : zetaOfChi χ * (zetaOfChi χ - 1) = 0 := by
    rw [mul_sub, mul_one, ← pow_two, hsq, sub_self]
  have hne : zetaOfChi χ - 1 ≠ 0 := sub_ne_zero.mpr hζ1
  exact hζ0 ((mul_eq_zero.mp hfac).resolve_right hne)

private theorem zetaOfChi_pow (χ : Multiplicative (ZMod 3) →* Kˣ) (hχ : Function.Injective χ)
    (a : Multiplicative (ZMod 3)) :
    (χ a : K) = zetaOfChi χ ^ (Multiplicative.toAdd a).val := by
  have hpow : a = (Multiplicative.ofAdd (1 : ZMod 3)) ^ (Multiplicative.toAdd a).val := by
    rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    rfl
  conv_lhs => rw [hpow]
  rw [map_pow]
  rfl

noncomputable def normPlaneEquiv (E : QuadExt F K (unitaryInvolution K 2 1))
    (χ : Multiplicative (ZMod 3) →* Kˣ) (hχ : Function.Injective χ) :
    (F × F) ≃ₗ[F] K :=
  (LinearEquiv.finTwoArrow F F).symm.trans
    (TauCeti.quadraticExtensionBasis F K (zetaOfChi_outside E χ hχ) E.finrank_eq).equivFun.symm

theorem normPlaneEquiv_apply (E : QuadExt F K (unitaryInvolution K 2 1))
    (χ : Multiplicative (ZMod 3) →* Kˣ) (hχ : Function.Injective χ) (c : F × F) :
    normPlaneEquiv E χ hχ c = algebraMap F K c.1 + algebraMap F K c.2 * zetaOfChi χ := by
  simp [normPlaneEquiv, LinearEquiv.finTwoArrow,
    Module.Basis.equivFun_symm_apply, Fin.sum_univ_two,
    TauCeti.quadraticExtensionBasis_zero, TauCeti.quadraticExtensionBasis_one,
    Algebra.smul_def]

private theorem zetaOfChi_bar (χ : Multiplicative (ZMod 3) →* Kˣ)
    (hχ : Function.Injective χ) :
    unitaryInvolution K 2 1 (zetaOfChi χ) = zetaOfChi χ ^ 2 := by
  rw [unitaryInvolution_apply]
  norm_num

private theorem zetaOfChi_sq (χ : Multiplicative (ZMod 3) →* Kˣ)
    (hχ : Function.Injective χ) : zetaOfChi χ ^ 2 = zetaOfChi χ + 1 := by
  have h := zetaOfChi_poly χ hχ
  have h' : zetaOfChi χ ^ 2 + zetaOfChi χ = 1 := by
    have h1 : zetaOfChi χ ^ 2 + zetaOfChi χ + 1 + 1 = 1 := by rw [h, zero_add]
    have h2 : zetaOfChi χ ^ 2 + zetaOfChi χ + (1 + 1) = 1 := by
      simpa [add_assoc] using h1
    simpa [CharTwo.add_self_eq_zero] using h2
  have h3 := congrArg (fun x : K => x + zetaOfChi χ) h'
  have h4 : zetaOfChi χ ^ 2 + zetaOfChi χ + zetaOfChi χ = zetaOfChi χ ^ 2 := by
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [h4] at h3
  simpa [add_comm] using h3

private theorem normQuad_planeEquiv (E : QuadExt F K (unitaryInvolution K 2 1))
    (χ : Multiplicative (ZMod 3) →* Kˣ) (hχ : Function.Injective χ) (c : F × F) :
    normQuad E (normPlaneEquiv E χ hχ c) = nrm c := by
  let A : K := algebraMap F K c.1
  let B : K := algebraMap F K c.2
  let ζ : K := zetaOfChi χ
  have he : normPlaneEquiv E χ hχ c = A + B * ζ := by
    rw [normPlaneEquiv_apply]
  have hbar : unitaryInvolution K 2 1 ζ = ζ ^ 2 := zetaOfChi_bar χ hχ
  have hsq : ζ ^ 2 = ζ + 1 := zetaOfChi_sq χ hχ
  apply (algebraMap F K).injective
  rw [algebraMap_normQuad, he]
  have hσ : unitaryInvolution K 2 1 (A + B * ζ) = A + B * (ζ + 1) := by
    rw [map_add, map_mul, E.fix, E.fix, hbar, hsq]
  rw [hσ]
  simp only [nrm, map_add, map_mul, map_pow]
  have hζ3 : ζ ^ 3 = 1 := zetaOfChi_pow_three χ
  have hpoly : ζ ^ 2 + ζ + 1 = 0 := zetaOfChi_poly χ hχ
  ring_nf
  rw [hsq]
  ring_nf
  rw [show (2 : K) = 0 from CharP.cast_eq_zero K 2]
  ring

private theorem normPlaneEquiv_zL (E : QuadExt F K (unitaryInvolution K 2 1))
    (χ : Multiplicative (ZMod 3) →* Kˣ) (hχ : Function.Injective χ) (c : F × F) :
    normPlaneEquiv E χ hχ (zL F c) =
      zetaOfChi χ * normPlaneEquiv E χ hχ c := by
  rw [normPlaneEquiv_apply, normPlaneEquiv_apply]
  change algebraMap F K c.2 + algebraMap F K (c.1 + c.2) * zetaOfChi χ =
    zetaOfChi χ * (algebraMap F K c.1 + algebraMap F K c.2 * zetaOfChi χ)
  rw [map_add]
  ring_nf
  rw [zetaOfChi_sq χ hχ]
  ring_nf

theorem normPlaneEquiv_σL (E : QuadExt F K (unitaryInvolution K 2 1))
    (χ : Multiplicative (ZMod 3) →* Kˣ) (hχ : Function.Injective χ) (c : F × F) :
    normPlaneEquiv E χ hχ (σL F c) =
      unitaryInvolution K 2 1 (normPlaneEquiv E χ hχ c) := by
  rw [normPlaneEquiv_apply, normPlaneEquiv_apply]
  change algebraMap F K (c.1 + c.2) + algebraMap F K c.2 * zetaOfChi χ =
    unitaryInvolution K 2 1 (algebraMap F K c.1 + algebraMap F K c.2 * zetaOfChi χ)
  have hbar : unitaryInvolution K 2 1 (zetaOfChi χ) = zetaOfChi χ ^ 2 :=
    zetaOfChi_bar χ hχ
  have hsq : zetaOfChi χ ^ 2 = zetaOfChi χ + 1 := zetaOfChi_sq χ hχ
  simp only [map_add, map_mul, E.fix, hbar, hsq]
  ring

private theorem normPlaneEquiv_zpow (E : QuadExt F K (unitaryInvolution K 2 1))
    (χ : Multiplicative (ZMod 3) →* Kˣ) (hχ : Function.Injective χ)
    (a : ZMod 3) (c : F × F) :
    normPlaneEquiv E χ hχ (zpow a c) =
      (χ (Multiplicative.ofAdd a) : K) * normPlaneEquiv E χ hχ c := by
  have hzn : ∀ n : ℕ,
      normPlaneEquiv E χ hχ (((zL F) ^ n) c) =
        zetaOfChi χ ^ n * normPlaneEquiv E χ hχ c := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ', LinearEquiv.mul_apply, normPlaneEquiv_zL, ih, pow_succ]
        ring
  rw [zpow, hzn]
  have hpow := zetaOfChi_pow χ hχ (Multiplicative.ofAdd a)
  simpa using congrArg (fun x : K => x * normPlaneEquiv E χ hχ c) hpow.symm

noncomputable def anchorEquiv (m : ℕ) :
    (F × F) ≃ₗ[F] (LinearMap.range (LinearMap.inl F (F × F) (Fin m → K))) :=
  LinearEquiv.ofInjective (LinearMap.inl F (F × F) (Fin m → K)) LinearMap.inl_injective

private theorem anchorEquiv_apply (m : ℕ) (w : F × F) :
    ((anchorEquiv (F := F) (K := K) m w :
      LinearMap.range (LinearMap.inl F (F × F) (Fin m → K))) :
      (F × F) × (Fin m → K)) = ((w, 0) : (F × F) × (Fin m → K)) := by
  simpa [anchorEquiv, LinearMap.inl] using
    (LinearEquiv.ofInjective_apply (f := LinearMap.inl F (F × F) (Fin m → K))
      (h := LinearMap.inl_injective) w)

private theorem anchorEquiv_symm_apply (m : ℕ)
    (x : LinearMap.range (LinearMap.inl F (F × F) (Fin m → K))) :
    (anchorEquiv (F := F) (K := K) m).symm x = (x : (F × F) × (Fin m → K)).1 := by
  have h := LinearEquiv.ofInjective_symm_apply
    (f := LinearMap.inl F (F × F) (Fin m → K)) (h := LinearMap.inl_injective) x
  simpa [anchorEquiv, LinearMap.inl] using congrArg Prod.fst h

noncomputable def normPlaneCoordEquiv (E : QuadExt F K (unitaryInvolution K 2 1))
    (m : ℕ) (χ : Multiplicative (ZMod 3) →* Kˣ) (hχ : Function.Injective χ) :
    ((Fin m → F × F) ×
        (LinearMap.range (LinearMap.inl F (F × F) (Fin m → K)))) ≃ₗ[F]
      ((F × F) × (Fin m → K)) :=
  ((LinearEquiv.piCongrRight fun _ : Fin m => normPlaneEquiv E χ hχ).prodCongr
      (anchorEquiv (F := F) (K := K) m).symm).trans
    (LinearEquiv.prodComm F (Fin m → K) (F × F))

private theorem normPlaneCoordEquiv_apply (E : QuadExt F K (unitaryInvolution K 2 1))
    (m : ℕ) (χ : Multiplicative (ZMod 3) →* Kˣ) (hχ : Function.Injective χ)
    (d : Fin m → F × F)
    (x : LinearMap.range (LinearMap.inl F (F × F) (Fin m → K))) :
    normPlaneCoordEquiv E m χ hχ (d, x) =
      ((anchorEquiv (F := F) (K := K) m).symm x,
        fun i => normPlaneEquiv E χ hχ (d i)) := by
  simp only [normPlaneCoordEquiv, LinearEquiv.trans_apply, LinearEquiv.prodComm_apply,
    LinearEquiv.prodCongr_apply, Prod.swap_prod_mk]
  refine Prod.ext rfl ?_
  funext i
  change (LinearEquiv.piCongrRight (fun _ : Fin m => normPlaneEquiv E χ hχ) d) i =
    normPlaneEquiv E χ hχ (d i)
  rw [LinearEquiv.piCongrRight_apply]

private theorem normPlaneCoordEquiv_Phi_zero (E : QuadExt F K (unitaryInvolution K 2 1))
    (m : ℕ) (χ : Multiplicative (ZMod 3) →* Kˣ) (hχ : Function.Injective χ)
    (x : LinearMap.range (LinearMap.inl F (F × F) (Fin m → K))) :
    normPlaneCoordEquiv E m χ hχ (0, x) = (x : (F × F) × (Fin m → K)) := by
  have hx := LinearEquiv.ofInjective_symm_apply
    (f := LinearMap.inl F (F × F) (Fin m → K)) (h := LinearMap.inl_injective) x
  have h2 : (x : (F × F) × (Fin m → K)).2 = 0 := by
    simpa [LinearMap.inl] using (congrArg Prod.snd hx).symm
  rw [normPlaneCoordEquiv_apply]
  refine Prod.ext ?_ ?_
  · exact anchorEquiv_symm_apply m x
  · funext i
    rw [h2]
    simp [normPlaneEquiv_apply]

@[expose] noncomputable def normPlaneTorusOmCoord
    (E : QuadExt F K (unitaryInvolution K 2 1)) {m : ℕ} (hm : 2 ≤ m)
    (χ : Multiplicative (ZMod 3) →* Kˣ) (hχ : Function.Injective χ) :
    OmCoord F (normHypForm E m)
      (((normOmega E m).subtype.comp
        (normPlaneTorus E hm (by decide : 3 ∣ 2 ^ 1 + 1) χ)).range) where
  s := m
  W0 := LinearMap.range (LinearMap.inl F (F × F) (Fin m → K))
  Φ := normPlaneCoordEquiv E m χ hχ
  form := by
    intro d x
    rw [normPlaneCoordEquiv_apply, normHypForm_apply_coord]
    simp only [normQuad_planeEquiv]
    have hx : (x : (F × F) × (Fin m → K)) =
        ((anchorEquiv (F := F) (K := K) m).symm x, 0) := by
      have h := anchorEquiv_symm_apply m x
      have hx2 := LinearEquiv.ofInjective_symm_apply
        (f := LinearMap.inl F (F × F) (Fin m → K)) (h := LinearMap.inl_injective) x
      have h2 : (x : (F × F) × (Fin m → K)).2 = 0 := by
        simpa [LinearMap.inl] using (congrArg Prod.snd hx2).symm
      exact Prod.ext h.symm h2
    have hQ : normHypForm E m (x : (F × F) × (Fin m → K)) =
        hypPlane F ((anchorEquiv (F := F) (K := K) m).symm x) := by
      rw [hx, normHypForm_apply_coord]
      simp
    rw [hQ]
    ring
  tor := fun f => ((normPlaneTorus E hm (by decide : 3 ∣ 2 ^ 1 + 1) χ
    (fun i => Multiplicative.ofAdd (f i)) : normOmega E m) :
      ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
  tor_acts := by
    intro f d x
    rw [normPlaneCoordEquiv_apply, normPlaneTorus_apply E hm (by decide : 3 ∣ 2 ^ 1 + 1) χ
      (fun i => Multiplicative.ofAdd (f i))]
    rw [normPlaneCoordEquiv_apply]
    refine Prod.ext rfl (funext fun i => ?_)
    change (χ (Multiplicative.ofAdd (f i)) : K) * normPlaneEquiv E χ hχ (d i) =
      normPlaneEquiv E χ hχ (torC f d i)
    rw [torC_apply, normPlaneEquiv_zpow]
  tor_mem := by
    intro f
    exact (MonoidHom.mem_range).mpr ⟨fun i => Multiplicative.ofAdd (f i), rfl⟩
  mem_tor := by
    intro c hc
    obtain ⟨u, hu⟩ := (MonoidHom.mem_range).mp hc
    refine ⟨fun i => Multiplicative.toAdd (u i), ?_⟩
    have hfun : (fun i => Multiplicative.ofAdd (Multiplicative.toAdd (u i))) = u := by
      funext i
      rfl
    simpa only [hfun, MonoidHom.comp_apply, Subgroup.coe_subtype] using hu

theorem normPlaneTorusOmCoord_s (E : QuadExt F K (unitaryInvolution K 2 1)) {m : ℕ}
    (hm : 2 ≤ m) (χ : Multiplicative (ZMod 3) →* Kˣ) (hχ : Function.Injective χ) :
    (normPlaneTorusOmCoord E hm χ hχ).s = m := rfl

theorem normPlaneTorusOmCoord_W0 (E : QuadExt F K (unitaryInvolution K 2 1)) {m : ℕ}
    (hm : 2 ≤ m) (χ : Multiplicative (ZMod 3) →* Kˣ) (hχ : Function.Injective χ) :
    (normPlaneTorusOmCoord E hm χ hχ).W0 =
      LinearMap.range (LinearMap.inl F (F × F) (Fin m → K)) := rfl

theorem normPlaneTorusOmCoord_tor (E : QuadExt F K (unitaryInvolution K 2 1)) {m : ℕ}
    (hm : 2 ≤ m) (χ : Multiplicative (ZMod 3) →* Kˣ) (hχ : Function.Injective χ)
    (f : Fin m → ZMod 3) :
    (normPlaneTorusOmCoord E hm χ hχ).tor f =
      ((normPlaneTorus E hm (by decide : 3 ∣ 2 ^ 1 + 1) χ
        (fun i => Multiplicative.ofAdd (f i)) : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) := rfl

theorem normPlaneTorusOmCoord_Phi_zero (E : QuadExt F K (unitaryInvolution K 2 1)) {m : ℕ}
    (hm : 2 ≤ m) (χ : Multiplicative (ZMod 3) →* Kˣ) (hχ : Function.Injective χ)
    (x : LinearMap.range (LinearMap.inl F (F × F) (Fin m → K))) :
    (normPlaneTorusOmCoord E hm χ hχ).Φ
      (0, x) = (x : (F × F) × (Fin m → K)) :=
  normPlaneCoordEquiv_Phi_zero E m χ hχ x

theorem normPlaneTorusOmCoord_W0_hyperbolic
    (E : QuadExt F K (unitaryInvolution K 2 1)) {m : ℕ} (hm : 2 ≤ m)
    (χ : Multiplicative (ZMod 3) →* Kˣ) (hχ : Function.Injective χ) :
    let C := normPlaneTorusOmCoord E hm χ hχ
    C.W0 = ⊥ ∨ (finrank F C.W0 = 2 ∧
      ∃ x y : C.W0, normHypForm E m (x : (F × F) × (Fin m → K)) = 0 ∧
        normHypForm E m (y : (F × F) × (Fin m → K)) = 0 ∧
        polar (normHypForm E m) (x : (F × F) × (Fin m → K))
          (y : (F × F) × (Fin m → K)) = 1) := by
  haveI : FiniteDimensional F K :=
    FiniteDimensional.of_finrank_pos (by rw [E.finrank_eq]; norm_num)
  let C := normPlaneTorusOmCoord E hm χ hχ
  right
  have hW : C.W0 = LinearMap.range (LinearMap.inl F (F × F) (Fin m → K)) := rfl
  have hdim : finrank F C.W0 = 2 := by
    rw [hW, ← (anchorEquiv (F := F) (K := K) m).finrank_eq]
    simp [Module.finrank_prod]
  refine ⟨hdim, ?_⟩
  refine ⟨anchorEquiv (F := F) (K := K) m (1, 0),
    anchorEquiv (F := F) (K := K) m (0, 1), ?_, ?_, ?_⟩
  · change normHypForm E m
      (((anchorEquiv (F := F) (K := K) m (1, 0) : C.W0) :
        (F × F) × (Fin m → K))) = 0
    rw [anchorEquiv_apply]
    simp [normHypForm_apply_coord, hypPlane_apply]
  · change normHypForm E m
      (((anchorEquiv (F := F) (K := K) m (0, 1) : C.W0) :
        (F × F) × (Fin m → K))) = 0
    rw [anchorEquiv_apply]
    simp [normHypForm_apply_coord, hypPlane_apply]
  · change polar (normHypForm E m)
      (((anchorEquiv (F := F) (K := K) m (1, 0) : C.W0) :
        (F × F) × (Fin m → K)))
      (((anchorEquiv (F := F) (K := K) m (0, 1) : C.W0) :
        (F × F) × (Fin m → K))) = 1
    rw [anchorEquiv_apply, anchorEquiv_apply]
    simp [normHypForm, polar_hypSum]

theorem normPlaneTorus_even_moveExp_iff_fixes_anchor
    (E : QuadExt F K (unitaryInvolution K 2 1)) {m : ℕ} (hm : 2 ≤ m)
    (hF : Nat.card F = 2)
    (χ : Multiplicative (ZMod 3) →* Kˣ) (hχ : Function.Injective χ)
    {g : normOmega E m}
    (π : Equiv.Perm (Fin m)) (η : Fin m → Bool)
    (hconj : ∀ f : Fin m → ZMod 3,
      g * normPlaneTorus E hm (by decide : 3 ∣ 2 ^ 1 + 1) χ
          (fun i => Multiplicative.ofAdd (f i)) * g⁻¹ =
        normPlaneTorus E hm (by decide : 3 ∣ 2 ^ 1 + 1) χ
          (fun i => Multiplicative.ofAdd (ChoiceTwo.moveExp π η f i))) :
    Even (Finset.univ.filter fun i => η i = true).card ↔
      ∀ w : F × F, (g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
        ((w, 0) : (F × F) × (Fin m → K)) = ((w, 0) : (F × F) × (Fin m → K)) := by
  classical
  haveI : FiniteDimensional F K :=
    FiniteDimensional.of_finrank_pos (by rw [E.finrank_eq]; norm_num)
  let C := normPlaneTorusOmCoord E hm χ hχ
  haveI : FiniteDimensional F ((F × F) × (Fin m → K)) := inferInstance
  have hQ : (polarBilin (normHypForm E m)).Nondegenerate :=
    normHypForm_polarBilin_nondegenerate E m
  have hgω : (g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) ∈
      omegaGroup (normHypForm E m) hQ :=
    CFSG.RankThree.PartOne.FieldFix.orthDerived_le_omegaGroup (Q := normHypForm E m) hQ g.2
  have hW0 : C.W0 = ⊥ ∨ (finrank F C.W0 = 2 ∧
      ∃ x y : C.W0, normHypForm E m (x : (F × F) × (Fin m → K)) = 0 ∧
        normHypForm E m (y : (F × F) × (Fin m → K)) = 0 ∧
        polar (normHypForm E m) (x : (F × F) × (Fin m → K))
          (y : (F × F) × (Fin m → K)) = 1) := by
    simpa only [C] using normPlaneTorusOmCoord_W0_hyperbolic E hm χ hχ
  have hconj' : ∀ f : Fin C.s → ZMod 3,
      (g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) * C.tor f *
          (g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))⁻¹ =
        C.tor (ChoiceTwo.moveExp π η f) := by
    intro f
    change (g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) *
        ((normPlaneTorus E hm (by decide : 3 ∣ 2 ^ 1 + 1) χ
          (fun i => Multiplicative.ofAdd (f i)) : normOmega E m) :
          ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K))) *
        (g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))⁻¹ =
      ((normPlaneTorus E hm (by decide : 3 ∣ 2 ^ 1 + 1) χ
        (fun i => Multiplicative.ofAdd (ChoiceTwo.moveExp π η f i)) : normOmega E m) :
        ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
    have h := congrArg (fun x : normOmega E m =>
      (x : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))) (hconj f)
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h
  have hEven := C.even_moveExp_iff_fixes_W0 hF hQ hW0 hgω π η hconj'
  have hPhi : ∀ x : C.W0, C.Φ (0, x) = (x : (F × F) × (Fin m → K)) := fun x =>
    normPlaneTorusOmCoord_Phi_zero E hm χ hχ x
  have hfix_iff : (∀ x : C.W0, (g : ((F × F) × (Fin m → K)) ≃ₗ[F]
        ((F × F) × (Fin m → K))) (C.Φ (0, x)) = C.Φ (0, x)) ↔
      ∀ w : F × F, (g : ((F × F) × (Fin m → K)) ≃ₗ[F] ((F × F) × (Fin m → K)))
        ((w, 0) : (F × F) × (Fin m → K)) = ((w, 0) : (F × F) × (Fin m → K)) := by
    constructor
    · intro h w
      have hx := h (anchorEquiv (F := F) (K := K) m w)
      rw [hPhi (anchorEquiv (F := F) (K := K) m w)] at hx
      rw [anchorEquiv_apply] at hx
      exact hx
    · intro h x
      have hx : (x : (F × F) × (Fin m → K)) = (((x : (F × F) × (Fin m → K)).1, 0) :
          (F × F) × (Fin m → K)) := by
        have hsymm := anchorEquiv_symm_apply (F := F) (K := K) m x
        have happ := anchorEquiv_apply (F := F) (K := K) m
          ((x : (F × F) × (Fin m → K)).1)
        have hxx : anchorEquiv (F := F) (K := K) m
            ((x : (F × F) × (Fin m → K)).1) = x := by
          rw [← hsymm]
          exact (anchorEquiv (F := F) (K := K) m).apply_symm_apply x
        rw [← happ, hxx]
      rw [hPhi x, hx]
      exact h ((x : (F × F) × (Fin m → K)).1)
  exact hEven.trans hfix_iff

end CFSG.StandardType.OrthAnchor
