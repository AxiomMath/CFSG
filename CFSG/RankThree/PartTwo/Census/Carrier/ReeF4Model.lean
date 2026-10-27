module

public import CFSG.RankThree.PartTwo.Census.Carrier.ReeF4Equiv

public noncomputable section

namespace CFSG.TauCetiBridge.ReeF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.TauCetiBridge.BigCell TauCeti TauCeti.F4ShortRoot.PrimeField

section Incl

variable (K L : Type) [Field K] [Field L] [Algebra K L]

@[expose] def incl : adjointGroup .F4 K →* adjointGroup .F4 L :=
  MonoidHom.codRestrict ((baseChangeGL (algebraMap K L)).comp (adjointGroup .F4 K).subtype) _
    fun g => baseChangeGL_mem_adjointGroup (algebraMap K L) g.2

variable {K L}

theorem coe_incl (g : adjointGroup .F4 K) :
    ((incl K L g : adjointGroup .F4 L) : ModGL .F4 L) =
      baseChangeGL (algebraMap K L) (g : ModGL .F4 K) :=
  rfl

theorem incl_injective : Function.Injective (incl K L) := fun _ _ e =>
  Subtype.ext (baseChangeGL_injective (algebraMap K L) (congrArg Subtype.val e))

theorem incl_xElement (i : Fin Tag.F4.rank) (c : K) :
    incl K L (xElement i c) = xElement i (algebraMap K L c) :=
  Subtype.ext (baseChangeGL_xUnit (algebraMap K L) i c)

theorem incl_yElement (i : Fin Tag.F4.rank) (c : K) :
    incl K L (yElement i c) = yElement i (algebraMap K L c) :=
  Subtype.ext (baseChangeGL_yUnit (algebraMap K L) i c)

end Incl

variable (K : Type) [Field K] [Finite K] [CharP K 2]

@[expose] def reeF (m : ℕ) : adjointGroup .F4 K →* adjointGroup .F4 K :=
  haveI : CharP K ReeTag.F4.prime := ‹CharP K 2›
  (ReeTag.F4.reeAut K m).toMonoidHom

variable {K}

theorem reeF_xElement (m : ℕ) (i : Fin Tag.F4.rank) (c : K) :
    reeF K m (xElement i c) = xElement (ReeTag.F4.perm i) (c ^ ReeTag.F4.relationExponent m i) :=
  haveI : CharP K ReeTag.F4.prime := ‹CharP K 2›
  ((exceptional_reeFixedGroup_eq .F4 K m).1 i c).1

theorem reeF_yElement (m : ℕ) (i : Fin Tag.F4.rank) (c : K) :
    reeF K m (yElement i c) = yElement (ReeTag.F4.perm i) (c ^ ReeTag.F4.relationExponent m i) :=
  haveI : CharP K ReeTag.F4.prime := ‹CharP K 2›
  ((exceptional_reeFixedGroup_eq .F4 K m).1 i c).2

theorem fixedSubgroup_reeF (m : ℕ) :
    haveI : CharP K ReeTag.F4.prime := ‹CharP K 2›
    fixedSubgroup (reeF K m) = reeFixed ReeTag.F4 K m :=
  rfl

theorem coe_glMap {A : Type*} [CommRing A] (φ : A →+* A)
    (g : Matrix.GeneralLinearGroup (Fin 26) A) :
    ((Matrix.GeneralLinearGroup.map φ g : Matrix.GeneralLinearGroup (Fin 26) A) :
      Matrix (Fin 26) (Fin 26) A) = φ.mapMatrix (g : Matrix (Fin 26) (Fin 26) A) :=
  rfl

theorem adConj_map {A : Type*} [CommRing A] (φ : A →+* A)
    (g : Matrix.GeneralLinearGroup (Fin 26) A) :
    adConj (Matrix.GeneralLinearGroup.map φ g) = entrywise φ (adConj g) := by
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring (Finsupp.ext fun x => ?_)
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  rw [entrywise_single, Finsupp.mapRange_apply, adOp_single_apply, adOp_single_apply, map_coord,
    ← map_inv, coe_glMap, coe_glMap, ← RingHom.mapMatrix_apply, map_mul, map_mul,
    mapMatrix_bMatR]

theorem adPoints_frobenius {L : Type} [Field L] [Algebra (ZMod 2) L] (n : ℕ) (g : points L) :
    adPoints L (frobenius n L g) =
      Units.map (entrywiseHom (((FiniteField.frobeniusAlgHom (ZMod 2) L) ^ n :
        L →ₐ[ZMod 2] L) : L →+* L)) (adPoints L g) := by
  refine Units.ext ?_
  rw [coe_adPoints, coe_frobenius, adConj_map]
  rfl

variable {L : Type} [Field L] [Algebra K L] [Algebra (ZMod 2) L] (hZ : ZerosInAdjoint L)
variable {m : ℕ} {S : points L →* points L}

theorem nativeSteinberg_comp_incl (hS : IsReeSteinberg m S) :
    (nativeSteinberg hZ S).comp (incl K L) = (incl K L).comp (reeF K m) := by
  refine adjointGroup_hom_ext (fun i c => ?_) fun i c => ?_
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, incl_xElement, nativeSteinberg_xElement hZ hS,
      reeF_xElement]
    exact ((incl_xElement (K := K) (L := L) (ReeTag.F4.perm i)
      (c ^ ReeTag.F4.relationExponent m i)).trans
        (congrArg (xElement (ReeTag.F4.perm i)) (map_pow (algebraMap K L) c _))).symm
  · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, incl_yElement, nativeSteinberg_yElement hZ hS,
      reeF_yElement]
    exact ((incl_yElement (K := K) (L := L) (ReeTag.F4.perm i)
      (c ^ ReeTag.F4.relationExponent m i)).trans
        (congrArg (yElement (ReeTag.F4.perm i)) (map_pow (algebraMap K L) c _))).symm

variable [IsAlgClosed L]

theorem fixedSubgroup_nativeSteinberg (hS : IsReeSteinberg m S)
    (hSS : ∀ g, S (S g) = frobenius (2 * m + 1) L g) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    fixedSubgroup (nativeSteinberg hZ S) = (fixedSubgroup (reeF K m)).map (incl K L) := by
  apply le_antisymm
  · intro x hx
    rw [mem_fixedSubgroup] at hx
    have hxy : adEquiv hZ ((adEquiv hZ).symm x) = x := MulEquiv.apply_symm_apply _ _
    have hSy : S ((adEquiv hZ).symm x) = (adEquiv hZ).symm x := by
      apply (adEquiv hZ).injective
      rw [hxy]
      exact hx
    have hfr : frobenius (2 * m + 1) L ((adEquiv hZ).symm x) = (adEquiv hZ).symm x := by
      rw [← hSS, hSy, hSy]
    set φ : L →+* L := (((FiniteField.frobeniusAlgHom (ZMod 2) L) ^ (2 * m + 1) :
      L →ₐ[ZMod 2] L) : L →+* L) with hφdef
    have hφ : ∀ c, φ c = c ^ Nat.card K := fun c => by
      rw [hK, hφdef]
      simpa using TauCeti.FiniteField.frobeniusAlgHom_pow_apply (ZMod 2) L (2 * m + 1) c
    have hfix : Units.map (entrywiseHom φ) (x : ModGL .F4 L) = x := by
      have h := adPoints_frobenius (2 * m + 1) ((adEquiv hZ).symm x)
      rw [hfr, ← coe_adEquiv hZ, hxy] at h
      exact h.symm
    obtain ⟨g, hg, hgx⟩ := mem_map_adjointGroup_F4_of_frobenius_fixed φ hφ x.2 hfix
    have hincl : incl K L ⟨g, hg⟩ = x := Subtype.ext hgx
    refine ⟨⟨g, hg⟩, ?_, hincl⟩
    rw [SetLike.mem_coe, mem_fixedSubgroup]
    apply incl_injective (K := K) (L := L)
    have e := congrArg (fun f => f ⟨g, hg⟩) (nativeSteinberg_comp_incl hZ hS)
    simp only [MonoidHom.comp_apply] at e
    rw [← e, hincl, hx]
  · rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, mem_fixedSubgroup] at hg
    rw [mem_fixedSubgroup]
    have e := congrArg (fun f => f g) (nativeSteinberg_comp_incl hZ hS)
    simp only [MonoidHom.comp_apply] at e
    rw [e, hg]

@[expose] def fixedPointCandidateNativeEquiv (hS : IsReeSteinberg m S)
    (hSS : ∀ g, S (S g) = frobenius (2 * m + 1) L g) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    FixedPointCandidate (reeF K m) ≃* FixedPointCandidate (nativeSteinberg hZ S) :=
  TauCeti.DerivedCentralQuotient.congr
    (((fixedSubgroup (reeF K m)).equivMapOfInjective (incl K L) incl_injective).trans
      (MulEquiv.subgroupCongr (fixedSubgroup_nativeSteinberg hZ hS hSS hK).symm))

include hZ in
theorem nonempty_candidate_equiv (hS : IsReeSteinberg m S)
    (hSS : ∀ g, S (S g) = frobenius (2 * m + 1) L g) (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    Nonempty (FixedPointCandidate S ≃* FixedPointCandidate (reeF K m)) :=
  ⟨(fixedPointCandidateEquiv hZ S).trans (fixedPointCandidateNativeEquiv hZ hS hSS hK).symm⟩

end CFSG.TauCetiBridge.ReeF4
