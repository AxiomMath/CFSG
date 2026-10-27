module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCoverTorus
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.CentralCoverBilinear
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.BinaryUnitaryInvariance

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open scoped Matrix

universe u v

variable {K : Type u} [Field K]

@[expose] def unitaryCoverAbelianEquiv [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (q : ℕ)
    (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Abelianization (unitaryCoverRoot J hJ) ≃* Multiplicative K :=
  unitaryCoverQuotientEquiv J q hcard hfixed hJ

@[simp] theorem unitaryCoverAbelianEquiv_of [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (q : ℕ)
    (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) (r : unitaryCoverRoot J hJ) :
    unitaryCoverAbelianEquiv J q hcard hfixed hJ (Abelianization.of r) =
      unitaryCoverRootFirstCoord J hJ r :=
  unitaryCoverQuotientEquiv_mk J q hcard hfixed hJ r

theorem unitaryCoverNormalizerAction_root (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (k : Kˣ) (z : hermitianUnipotentCoord J) :
    coverNormalizerAction (unitaryCoverRoot J hJ) (unitaryCoverTorus J hJ)
        (unitaryCoverTorus_le_normalizer J hJ)
        ((hermitianTorusPSU J hJ).rangeRestrict k) (unitaryCoverRootEquiv J hJ z) =
      unitaryCoverRootEquiv J hJ (hermitianTorusAction J k z) := by
  apply Subtype.ext
  change hermitianTorusPSU J hJ k * hermitianUnipotentPSU J hJ z *
    (hermitianTorusPSU J hJ k)⁻¹ = _
  exact unitaryCoverTorus_conj_root J hJ k z

theorem unitaryCoverAbelianAction_parameter [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (q : ℕ)
    (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (k : Kˣ) (v : Abelianization (unitaryCoverRoot J hJ)) :
    Multiplicative.toAdd (unitaryCoverAbelianEquiv J q hcard hfixed hJ
      (coverAbelianAction (unitaryCoverRoot J hJ) (unitaryCoverTorus J hJ)
        (unitaryCoverTorus_le_normalizer J hJ)
        ((hermitianTorusPSU J hJ).rangeRestrict k) v)) =
      (unitaryCoverScalar J k : K) *
        Multiplicative.toAdd (unitaryCoverAbelianEquiv J q hcard hfixed hJ v) := by
  obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (commutator (unitaryCoverRoot J hJ)) v
  obtain ⟨z, rfl⟩ := (unitaryCoverRootEquiv J hJ).surjective r
  change Multiplicative.toAdd (unitaryCoverAbelianEquiv J q hcard hfixed hJ
    (Abelianization.map _ (Abelianization.of (unitaryCoverRootEquiv J hJ z)))) = _
  rw [Abelianization.map_of]
  change Multiplicative.toAdd (unitaryCoverAbelianEquiv J q hcard hfixed hJ
    (Abelianization.of (coverNormalizerAction (unitaryCoverRoot J hJ) (unitaryCoverTorus J hJ)
      (unitaryCoverTorus_le_normalizer J hJ)
      ((hermitianTorusPSU J hJ).rangeRestrict k) (unitaryCoverRootEquiv J hJ z)))) =
    (unitaryCoverScalar J k : K) * Multiplicative.toAdd
      (unitaryCoverAbelianEquiv J q hcard hfixed hJ (Abelianization.of (unitaryCoverRootEquiv J hJ z)))
  rw [unitaryCoverNormalizerAction_root,
    unitaryCoverAbelianEquiv_of, unitaryCoverAbelianEquiv_of,
    unitaryCoverRootFirstCoord_apply, unitaryCoverRootFirstCoord_apply]
  change (hermitianTorusAction J k z).1.1 = (unitaryCoverScalar J k : K) * z.1.1
  rw [hermitianTorusAction_fst, unitaryCoverScalar_val]
  ring

theorem unitaryCoverNormalizerAction_coord (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (k : Kˣ) (r : unitaryCoverRoot J hJ) :
    (unitaryCoverRootEquiv J hJ).symm
      (coverNormalizerAction (unitaryCoverRoot J hJ) (unitaryCoverTorus J hJ)
        (unitaryCoverTorus_le_normalizer J hJ)
        ((hermitianTorusPSU J hJ).rangeRestrict k) r) =
      hermitianTorusAction J k ((unitaryCoverRootEquiv J hJ).symm r) := by
  obtain ⟨z, rfl⟩ := (unitaryCoverRootEquiv J hJ).surjective r
  rw [unitaryCoverNormalizerAction_root]
  simp only [MulEquiv.symm_apply_apply]

theorem unitaryCoverDerivedAction_parameter [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (q : ℕ)
    (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (k : Kˣ) (w : commutator (unitaryCoverRoot J hJ)) :
    ((Multiplicative.toAdd (unitaryCoverDerivedEquiv J q hcard hfixed hJ
      (coverDerivedAction (unitaryCoverRoot J hJ) (unitaryCoverTorus J hJ)
        (unitaryCoverTorus_le_normalizer J hJ)
        ((hermitianTorusPSU J hJ).rangeRestrict k) w)) : unitaryCoverFixedField J) : K) =
      (unitaryCoverScalar J k : K) * J.conj (unitaryCoverScalar J k : K) *
        ((Multiplicative.toAdd (unitaryCoverDerivedEquiv J q hcard hfixed hJ w) :
          unitaryCoverFixedField J) : K) := by
  rw [unitaryCoverDerivedEquiv_snd, unitaryCoverDerivedEquiv_snd]
  change ((unitaryCoverRootEquiv J hJ).symm
    (coverNormalizerAction (unitaryCoverRoot J hJ) (unitaryCoverTorus J hJ)
      (unitaryCoverTorus_le_normalizer J hJ)
      ((hermitianTorusPSU J hJ).rangeRestrict k) w.val)).1.2 = _
  rw [unitaryCoverNormalizerAction_coord, hermitianTorusAction_snd, unitaryCoverScalar_norm]
  ring

theorem unitaryCoverAbelianAction_equivariant [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (q : ℕ)
    (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (t : unitaryCoverTorus J hJ) (v : Abelianization (unitaryCoverRoot J hJ)) :
    Multiplicative.toAdd (unitaryCoverAbelianEquiv J q hcard hfixed hJ
      (coverAbelianAction (unitaryCoverRoot J hJ) (unitaryCoverTorus J hJ)
        (unitaryCoverTorus_le_normalizer J hJ) t v)) =
      ((unitaryCoverTorusScalarEquiv J hJ t).val : K) *
        Multiplicative.toAdd (unitaryCoverAbelianEquiv J q hcard hfixed hJ v) := by
  obtain ⟨k, rfl⟩ := (hermitianTorusPSU J hJ).rangeRestrict_surjective t
  rw [unitaryCoverTorusScalarEquiv_apply]
  exact unitaryCoverAbelianAction_parameter J q hcard hfixed hJ k v

theorem unitaryCoverDerivedAction_equivariant [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (q : ℕ)
    (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (t : unitaryCoverTorus J hJ) (w : commutator (unitaryCoverRoot J hJ)) :
    ((Multiplicative.toAdd (unitaryCoverDerivedEquiv J q hcard hfixed hJ
      (coverDerivedAction (unitaryCoverRoot J hJ) (unitaryCoverTorus J hJ)
        (unitaryCoverTorus_le_normalizer J hJ) t w)) : unitaryCoverFixedField J) : K) =
      ((unitaryCoverTorusScalarEquiv J hJ t).val : K) *
        J.conj ((unitaryCoverTorusScalarEquiv J hJ t).val : K) *
          ((Multiplicative.toAdd (unitaryCoverDerivedEquiv J q hcard hfixed hJ w) :
            unitaryCoverFixedField J) : K) := by
  obtain ⟨k, rfl⟩ := (hermitianTorusPSU J hJ).rangeRestrict_surjective t
  rw [unitaryCoverTorusScalarEquiv_apply]
  exact unitaryCoverDerivedAction_parameter J q hcard hfixed hJ k w

theorem unitaryCoverScalarFixedAddHom_eq_zero {A : Type v} [AddGroup A]
    (h : K) (hne : h ≠ 1) (b : K →+ A) (hinvariant : ∀ x, b (h * x) = b x) :
    b = 0 := by
  have hc : h - 1 ≠ 0 := sub_ne_zero.mpr hne
  have hzero (y : K) : b ((h - 1) * y) = 0 := by
    rw [sub_mul, one_mul, map_sub, hinvariant, sub_self]
  ext x
  change b x = 0
  have hx : (h - 1) * ((h - 1)⁻¹ * x) = x := by
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  simpa only [hx] using hzero ((h - 1)⁻¹ * x)

theorem unitaryCoverMixedInvariant_eq_zero [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (b : Additive (commutator (unitaryCoverRoot J hJ)) →+
      Additive (Abelianization (unitaryCoverRoot J hJ)) →+ ZMod 2)
    (hinvariant : CoverMixedInvariant (unitaryCoverRoot J hJ) (unitaryCoverTorus J hJ)
      (unitaryCoverTorus_le_normalizer J hJ) b) : b = 0 := by
  have hq : 2 < 2 ^ f := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) hf
    norm_num at h ⊢
    omega
  obtain ⟨h, hne, hnorm⟩ :=
    unitaryCoverScalarImage_exists_norm_one_ne_one J (2 ^ f) hcard hfixed hJ hq
  let t : unitaryCoverTorus J hJ := (unitaryCoverTorusScalarEquiv J hJ).symm h
  have ht : unitaryCoverTorusScalarEquiv J hJ t = h :=
    (unitaryCoverTorusScalarEquiv J hJ).apply_symm_apply h
  have hfix (w : commutator (unitaryCoverRoot J hJ)) :
      coverDerivedAction (unitaryCoverRoot J hJ) (unitaryCoverTorus J hJ)
        (unitaryCoverTorus_le_normalizer J hJ) t w = w := by
    apply (unitaryCoverDerivedEquiv J (2 ^ f) hcard hfixed hJ).injective
    apply (Multiplicative.toAdd : Multiplicative (unitaryCoverFixedField J) ≃ _).injective
    apply Subtype.ext
    simpa only [ht, hnorm, one_mul] using
      unitaryCoverDerivedAction_equivariant J (2 ^ f) hcard hfixed hJ t w
  let e : Additive (Abelianization (unitaryCoverRoot J hJ)) ≃+ K :=
    MulEquiv.toAdditiveLeft (unitaryCoverAbelianEquiv J (2 ^ f) hcard hfixed hJ)
  have hequiv (v : Abelianization (unitaryCoverRoot J hJ)) :
      e (Additive.ofMul (coverAbelianAction (unitaryCoverRoot J hJ) (unitaryCoverTorus J hJ)
        (unitaryCoverTorus_le_normalizer J hJ) t v)) = (h.val : K) * e (Additive.ofMul v) := by
    exact (unitaryCoverAbelianAction_equivariant J (2 ^ f) hcard hfixed hJ t v).trans
      (congrArg (fun s : unitaryCoverScalarImage J => (s.val : K) * e (Additive.ofMul v)) ht)
  apply AddMonoidHom.ext
  intro w
  apply AddMonoidHom.ext
  intro v
  let c : K →+ ZMod 2 := (b w).comp e.symm.toAddMonoidHom
  have hc : c = 0 := unitaryCoverScalarFixedAddHom_eq_zero (h.val : K) hne c (by
    intro x
    have haction : e.symm ((h.val : K) * x) =
        Additive.ofMul (coverAbelianAction (unitaryCoverRoot J hJ) (unitaryCoverTorus J hJ)
          (unitaryCoverTorus_le_normalizer J hJ) t (Additive.toMul (e.symm x))) := by
      apply e.injective
      rw [AddEquiv.apply_symm_apply]
      have he := (hequiv (Additive.toMul (e.symm x))).symm
      change (h.val : K) * e (e.symm x) = _ at he
      simpa only [AddEquiv.apply_symm_apply] using
        he
    change b w (e.symm ((h.val : K) * x)) = b w (e.symm x)
    rw [haction]
    have hi := hinvariant t (Additive.toMul w) (Additive.toMul (e.symm x))
    rw [hfix] at hi
    exact hi)
  have hz := DFunLike.congr_fun hc (e v)
  change b w v = 0
  simpa only [c, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.symm_apply_apply, AddMonoidHom.zero_apply] using hz

theorem unitaryCoverAbelianInvariant_eq_zero [Finite K] [CharP K 2]
    (J : HermitianForm 3 K) (f : ℕ) (hf : 2 ≤ f)
    (hcard : Nat.card K = (2 ^ f) ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = 2 ^ f)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (b : Additive (Abelianization (unitaryCoverRoot J hJ)) →+
      Additive (Abelianization (unitaryCoverRoot J hJ)) →+ ZMod 2)
    (hinvariant : CoverAbelianInvariant (unitaryCoverRoot J hJ) (unitaryCoverTorus J hJ)
      (unitaryCoverTorus_le_normalizer J hJ) b) : b = 0 := by
  let e : Additive (Abelianization (unitaryCoverRoot J hJ)) ≃+ K :=
    MulEquiv.toAdditiveLeft (unitaryCoverAbelianEquiv J (2 ^ f) hcard hfixed hJ)
  let c : K →+ K →+ ZMod 2 :=
    (b.compl₂ e.symm.toAddMonoidHom).comp e.symm.toAddMonoidHom
  have haction (t : unitaryCoverTorus J hJ) (x : K) :
      e.symm (((unitaryCoverTorusScalarEquiv J hJ t).val : K) * x) =
        Additive.ofMul (coverAbelianAction (unitaryCoverRoot J hJ) (unitaryCoverTorus J hJ)
          (unitaryCoverTorus_le_normalizer J hJ) t (Additive.toMul (e.symm x))) := by
    apply e.injective
    rw [AddEquiv.apply_symm_apply]
    have he := (unitaryCoverAbelianAction_equivariant J (2 ^ f) hcard hfixed hJ
      t (Additive.toMul (e.symm x))).symm
    change ((unitaryCoverTorusScalarEquiv J hJ t).val : K) * e (e.symm x) =
      e (Additive.ofMul (coverAbelianAction (unitaryCoverRoot J hJ) (unitaryCoverTorus J hJ)
        (unitaryCoverTorus_le_normalizer J hJ) t (Additive.toMul (e.symm x)))) at he
    simpa only [AddEquiv.apply_symm_apply] using he
  have hc : ∀ x y, c x y = 0 :=
    binaryUnitaryTorusInvariantAddHom_eq_zero f hf hcard (unitaryCoverScalarImage J)
      (unitaryCoverScalarImage_card J (2 ^ f) hcard hfixed hJ) c (by
        intro h x y
        let t : unitaryCoverTorus J hJ := (unitaryCoverTorusScalarEquiv J hJ).symm h
        have ht : unitaryCoverTorusScalarEquiv J hJ t = h :=
          (unitaryCoverTorusScalarEquiv J hJ).apply_symm_apply h
        change b (e.symm ((h.val : K) * x)) (e.symm ((h.val : K) * y)) =
          b (e.symm x) (e.symm y)
        rw [← ht, haction, haction]
        exact hinvariant t (Additive.toMul (e.symm x)) (Additive.toMul (e.symm y)))
  apply AddMonoidHom.ext
  intro x
  apply AddMonoidHom.ext
  intro y
  change b x y = 0
  have hz := hc (e x) (e y)
  change b (e.symm (e x)) (e.symm (e y)) = 0 at hz
  simpa only [AddEquiv.symm_apply_apply] using hz

end CFSG.ShultStronglyClosedTI
