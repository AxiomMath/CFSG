module

public import CFSG.ClassicalGroups.Orthogonal.QuadraticExtensionDescent
public import CFSG.LocalAnalysis.StandardType.PhanEStdChoice
public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergSpinPlusField
public import CFSG.LieType.Steinberg.CentralExt.SpinPlusThree
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourLevi
public import CFSG.LocalAnalysis.StandardType.PhanEAdjDescent
public import CFSG.ClassicalGroups.Orthogonal.RootGroupNormalizer
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Anisotropic.Plane
public import CFSG.ClassicalInvolution.Models.OrthogonalPairs.Pairs

public noncomputable section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.PhanDn CFSG.ClassicalGroups.Orthogonal.ExtensionDescent

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

theorem exists_perpSpin_flipLang (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    ∃ s : spinGroup (quadPlus 6 K), ∀ v : Fin 6 ⊕ Fin 6 → K,
      spinAction (quadPlus 6 K) s (PhanDn.dFlip (unitaryInvolution K 2 f) v) =
        fun i => unitaryInvolution K 2 f (spinAction (quadPlus 6 K) s v i) := by
  let : Algebra (GaloisField 2 f) K := (fqEmbed hK hf).toAlgebra
  have E := quadExt_of_card_of_char_two (F := GaloisField 2 f) f
    (GaloisField.card 2 f (by omega)) hK
  exact exists_spin_flipLang E (by decide +kernel) (by decide +kernel)

open CFSG.StandardType.AutOm CFSG.StandardType
open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.SpinFrame CFSG.LieType.RootSystem

open CFSG.LieType.Steinberg.CentralExt.SpinPlusClosed

@[expose] def perpSpinNeg : spinGroup (quadPlus 6 K) :=
  negPair (plusFrame 6 K (by decide +kernel)) (j := 0) (m := 1) (by decide +kernel) *
    negPair (plusFrame 6 K (by decide +kernel)) (j := 2) (m := 3) (by decide +kernel) *
    negPair (plusFrame 6 K (by decide +kernel)) (j := 4) (m := 5) (by decide +kernel)

omit [Finite K] in
theorem spinAction_perpSpinNeg_vec (m : Fin 6) (r : Bool) :
    spinAction (quadPlus 6 K) perpSpinNeg ((plusFrame 6 K (by decide +kernel)).vec m r) =
      (plusFrame 6 K (by decide +kernel)).vec m (!r) := by
  simp only [perpSpinNeg, map_mul, LinearEquiv.mul_apply, spinAction_negPair, map_smul]
  fin_cases m <;> cases r <;> simp [negSign, negBool, CharTwo.neg_eq]

omit [Finite K] in
theorem spinAction_perpSpinNeg (v : Fin 6 ⊕ Fin 6 → K) :
    spinAction (quadPlus 6 K) perpSpinNeg v = PhanDn.dFlip (RingEquiv.refl K) v := by
  let L : (Fin 6 ⊕ Fin 6 → K) →ₗ[K] (Fin 6 ⊕ Fin 6 → K) :=
    { toFun := PhanDn.dFlip (RingEquiv.refl K)
      map_add' := PhanDn.dFlip_add
      map_smul' := fun a w => by simpa using PhanDn.dFlip_smul (σ := RingEquiv.refl K) a w }
  have hL : (spinAction (quadPlus 6 K) perpSpinNeg).toLinearMap = L := by
    apply (Pi.basisFun K (Fin 6 ⊕ Fin 6)).ext
    intro x
    rw [Pi.basisFun_apply]
    rcases x with m | m
    · change spinAction (quadPlus 6 K) perpSpinNeg (PhanDn.stdE m) =
        PhanDn.dFlip (RingEquiv.refl K) (PhanDn.stdE m)
      rw [PhanDn.dFlip_stdE]
      simpa only [plusFrame_vec, plusVec_true, Bool.not_true, plusVec_false, PhanDn.stdE,
        PhanDn.stdF] using spinAction_perpSpinNeg_vec (K := K) m true
    · change spinAction (quadPlus 6 K) perpSpinNeg (PhanDn.stdF m) =
        PhanDn.dFlip (RingEquiv.refl K) (PhanDn.stdF m)
      rw [PhanDn.dFlip_stdF]
      simpa only [plusFrame_vec, plusVec_false, Bool.not_false, plusVec_true, PhanDn.stdE,
        PhanDn.stdF] using spinAction_perpSpinNeg_vec (K := K) m false
  exact congrArg (fun f : (Fin 6 ⊕ Fin 6 → K) →ₗ[K] (Fin 6 ⊕ Fin 6 → K) => f v) hL

omit [Finite K] in
theorem perpSpinNeg_conj_x {γ : Fin 6 → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanD 6) ∅) (c : K) :
    perpSpinNeg * SpinPlus.x 6 K (by decide +kernel) γ c * perpSpinNeg⁻¹ =
      SpinPlus.x 6 K (by decide +kernel) (-γ) c := by
  obtain ⟨i, j, hij, b, t, he⟩ :=
    (SpinPlus.isLong_toStdD_iff (by decide +kernel)).mpr hγ
  obtain ⟨ε, hε, hc⟩ := conj_rootElt_of_signedPerm (plusFrame 6 K (by decide +kernel))
    perpSpinNeg (Equiv.refl _) (fun _ r => !r) (fun _ _ => (1 : ℤ))
    (fun _ _ => Or.inl rfl) (fun m r => by simpa using spinAction_perpSpinNeg_vec (K := K) m r)
    hij he
  have hε' : (ε : K) = 1 := by
    rcases hε with rfl | rfl <;> simp [CharTwo.neg_eq]
  have he' : toStdD 6 (-γ) =
      Pi.single i (boolSign (!b)) + Pi.single j (boolSign (!t)) := by
    rw [toStdD_neg, he]
    ext k
    cases b <;> cases t <;> simp [boolSign, Pi.single_apply] <;> split_ifs <;> ring
  simpa only [SpinPlus.x, Equiv.refl_apply, hε', one_mul, he'] using hc c

theorem exists_perpSpin_lang_fieldAut {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    ∃ s : spinGroup (quadPlus 6 K),
      spinFieldAutP (by decide +kernel) (unitaryInvolution K 2 f) s = s * perpSpinNeg := by
  obtain ⟨s, hs⟩ := exists_perpSpin_flipLang hK hf
  refine ⟨s, ?_⟩
  apply RootCentOmega.spinAction_quadPlus_injective
  apply LinearEquiv.ext
  intro v
  let σ := unitaryInvolution K 2 f
  let w : Fin 6 ⊕ Fin 6 → K := fun i => σ.symm (v i)
  have hw : (fun i => σ (w i)) = v := by ext i; simp [w]
  have hflip : PhanDn.dFlip σ w = PhanDn.dFlip (RingEquiv.refl K) v := by
    ext i
    cases i <;> simp [PhanDn.dFlip, w]
  calc
    spinAction (quadPlus 6 K) (spinFieldAutP (by decide +kernel) σ s) v =
        spinAction (quadPlus 6 K) (spinFieldAutP (by decide +kernel) σ s) (fun i => σ (w i)) :=
      congrArg _ hw.symm
    _ = (fun i => σ (spinAction (quadPlus 6 K) s w i)) :=
      spinAction_spinFieldAutP (by decide +kernel) σ s w
    _ = spinAction (quadPlus 6 K) s (PhanDn.dFlip σ w) := (hs w).symm
    _ = spinAction (quadPlus 6 K) (s * perpSpinNeg) v := by
      rw [map_mul, LinearEquiv.mul_apply, spinAction_perpSpinNeg, hflip]



open CFSG.SeitzReduction.E7Pilot CFSG.Blueprint.Chevalley
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Chevalley

theorem spinToE7_fieldAut (σ : K ≃+* K) :
    (adjointBaseChangeHom .E7 σ.toRingHom).comp (spinToE7 K) =
      (spinToE7 K).comp (spinFieldAutP (n := 6) (by decide +kernel) σ).toMonoidHom := by
  apply hom_ext_of_iSup_eq_top (Φ := SpinPlus.Φ 6 K (by decide +kernel))
    (X := (plusDatum 6 K (by decide +kernel)).rootGroup)
    (plusDatum_iSup_eq_top 6 K (by decide +kernel))
  intro γ hγ x hx
  obtain ⟨c, rfl⟩ := ((SpinPlus.isParametrization (n := 6) (K := K) (by decide +kernel) γ hγ).1 x).mp hx
  change adjointBaseChangeHom .E7 σ.toRingHom (spinToE7 K (SpinPlus.x 6 K (by decide +kernel) γ c)) =
    spinToE7 K (spinFieldAutP (by decide +kernel) σ (SpinPlus.x 6 K (by decide +kernel) γ c))
  rw [spinFieldAutP_x (by decide +kernel) σ hγ c,
    spinToE7_x hγ, spinToE7_x hγ]
  apply Subtype.ext
  simpa only [coe_adjointBaseChangeHom, coe_d6LeviPar, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom] using
    baseChangeGL_pinnedX (f := σ.toRingHom) (τ := .E7) (d6Embed γ) c

theorem spinToE7_perpSpinNeg_conj {γ : Fin 6 → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartanD 6) ∅) (c : K) :
    spinToE7 K perpSpinNeg * d6LeviPar K γ c * (spinToE7 K perpSpinNeg)⁻¹ =
      d6LeviPar K (-γ) c := by
  have hneg : -γ ∈ roots (isFiniteType_cartanD 6) ∅ :=
    isRoot_d6Embed_iff.1 (by rw [d6Embed_neg]; exact IsRoot.neg (isRoot_d6Embed hγ))
  simpa only [map_mul, map_inv, spinToE7_x hγ, spinToE7_x hneg] using
    congrArg (spinToE7 K) (perpSpinNeg_conj_x (K := K) hγ c)

theorem exists_perpLevi_lang {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    ∃ g : adjointGroup .E7 K, g ∈ CFSG.SeitzReduction.EPilot.perpLevi .E7 K ∧
      g⁻¹ * adjointBaseChangeHom .E7 (unitaryInvolution K 2 f).toRingHom g =
        spinToE7 K perpSpinNeg := by
  obtain ⟨s, hs⟩ := exists_perpSpin_lang_fieldAut hK hf
  refine ⟨spinToE7 K s, spinToE7_mem_perpLevi s, ?_⟩
  have h := congrArg (fun φ : spinGroup (quadPlus 6 K) →* adjointGroup .E7 K => φ s)
    (spinToE7_fieldAut (K := K) (unitaryInvolution K 2 f))
  change adjointBaseChangeHom .E7 (unitaryInvolution K 2 f).toRingHom (spinToE7 K s) =
    spinToE7 K (spinFieldAutP (by decide +kernel) (unitaryInvolution K 2 f) s) at h
  rw [hs, map_mul] at h
  rw [h]
  group


end CFSG.ClassicalInvolution.Phan.PhanE
