module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTriD4Conj
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.LieType.Chevalley.AmbientTwistedFrobeniusFixedNormalizer

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace RecipeExcLang

set_option linter.unusedSectionVars false

section Compat

variable {R : Type} [Field R] (σ : R →+* R)

@[expose] def IsCompatE6 (b : Fin TwistTag.E6.tag.rank → Rˣ) : Prop :=
  ∀ i, b (TwistTag.E6.perm i) = Units.map σ.toMonoidHom (b i)

variable {σ}

theorem IsCompatE6.inv {b : Fin TwistTag.E6.tag.rank → Rˣ} (h : IsCompatE6 σ b) :
    IsCompatE6 σ b⁻¹ := fun i => by
  simp only [Pi.inv_apply, h i, map_inv]

theorem twistHom_rootDiagUnit_of_compat {b : Fin TwistTag.E6.tag.rank → Rˣ}
    (h : IsCompatE6 σ b) : twistHom TwistTag.E6 R σ (rootDiagUnit TwistTag.E6.tag b) =
      rootDiagUnit TwistTag.E6.tag b := by
  rw [twistHom_rootDiagUnit_eq]
  congr 1
  funext i
  have := h (TwistTag.E6.perm.symm i)
  rw [Equiv.apply_symm_apply] at this
  exact this.symm

end Compat

section Closure

variable {K : Type} [Field K] [Finite K] {L : Type} [Field L] [Algebra K L]

theorem baseChangeGL_rootDiagUnit_mem_twistedFixed [IsAlgClosed L] {σ : K →+* K}
    {Fr : L →+* L} (hcomm : (algebraMap K L).comp σ = Fr.comp (algebraMap K L))
    {b : Fin TwistTag.E6.tag.rank → Kˣ} (hb : IsCompatE6 σ b) :
    baseChangeGL (algebraMap K L) (rootDiagUnit TwistTag.E6.tag b) ∈
      twistedFixedGroup TwistTag.E6 L Fr := by
  refine ⟨?_, ?_⟩
  · rw [baseChangeGL_rootDiagUnit]
    exact (exceptional_Lang_adjoint_diagonal_lift _ L _).1
  · change twistHom TwistTag.E6 L Fr (baseChangeGL (algebraMap K L)
      (rootDiagUnit TwistTag.E6.tag b)) = baseChangeGL (algebraMap K L)
        (rootDiagUnit TwistTag.E6.tag b)
    rw [twistHom_baseChangeGL (algebraMap K L) hcomm, twistHom_rootDiagUnit_of_compat hb]

theorem exists_compat_of_mem_graphFixedTorus {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    {t : ModGL TwistTag.E6.tag L} (ht : t ∈ graphFixedTorus TwistTag.E6 L Fr) :
    ∃ b : Fin TwistTag.E6.tag.rank → Kˣ, IsCompatE6 σ.toRingHom b ∧
      baseChangeGL (algebraMap K L) (rootDiagUnit TwistTag.E6.tag b) = t := by
  obtain ⟨hT, -, hF⟩ := ht
  obtain ⟨bL, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hT
  have hF' : twistHom TwistTag.E6 L Fr (rootDiagUnit TwistTag.E6.tag bL) =
      rootDiagUnit TwistTag.E6.tag bL := hF
  rw [twistHom_rootDiagUnit_eq] at hF'
  have hc := rootDiagUnit_injective hF'
  have hcomp : ∀ i, bL (TwistTag.E6.perm i) = Units.map Fr.toMonoidHom (bL i) := fun i => by
    have := congrFun hc (TwistTag.E6.perm i)
    rw [Equiv.symm_apply_apply] at this
    exact this.symm
  have hperm2 : ∀ i, TwistTag.E6.perm (TwistTag.E6.perm i) = i := fun i => by
    have h2 := TwistTag.E6.perm_pow_order
    change TwistTag.E6.perm ^ 2 = 1 at h2
    rw [← Equiv.Perm.mul_apply, ← pow_two, h2, Equiv.Perm.one_apply]
  have hfix : ∀ i, ((bL i : Lˣ) : L) ^ Nat.card K = bL i := fun i => by
    have h1 := congrArg (fun u : Lˣ => (u : L)) (hcomp (TwistTag.E6.perm i))
    have h2 := congrArg (fun u : Lˣ => (u : L)) (hcomp i)
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, hperm2] at h1 h2
    rw [h2, hFr, hFr, ← pow_mul] at h1
    rw [hK, show (2 ^ n) ^ 2 = 2 ^ n * 2 ^ n by ring]
    exact h1.symm
  have hK' : ∀ i, ∃ k : Kˣ, algebraMap K L k = ((bL i : Lˣ) : L) := fun i => by
    obtain ⟨k, hk⟩ := mem_range_algebraMap_of_pow_card_eq (k := K) (hfix i)
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [map_zero] at hk
      exact (bL i).ne_zero hk.symm
    exact ⟨Units.mk0 k hk0, hk⟩
  choose b hb using hK'
  have hι : ∀ i, Units.map (algebraMap K L).toMonoidHom (b i) = bL i := fun i =>
    Units.ext (hb i)
  refine ⟨b, fun i => ?_, ?_⟩
  · apply Units.ext
    apply (algebraMap K L).injective
    have h1 := congrArg (fun u : Lˣ => (u : L)) (hcomp i)
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass] at h1
    rw [← hb, ← hb, hFr] at h1
    rw [h1]
    change _ = algebraMap K L (σ (b i : K))
    rw [hσ, map_pow]
  · rw [baseChangeGL_rootDiagUnit]
    congr 1
    funext i
    exact hι i

end Closure

section Group

variable {K : Type} [Field K] [Finite K]

variable (K) in
@[expose] noncomputable def twInndiagGroup (σ : K ≃+* K) : Subgroup (ModGL TwistTag.E6.tag K) :=
  Subgroup.closure
    ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom : Set (ModGL TwistTag.E6.tag K)) ∪
      {w | ∃ b, IsCompatE6 σ.toRingHom b ∧ w = rootDiagUnit TwistTag.E6.tag b})

theorem graphFixedRootGroup_le_twInndiag (σ : K ≃+* K) :
    graphFixedRootGroup TwistTag.E6 K σ.toRingHom ≤ twInndiagGroup K σ :=
  fun _ hc => Subgroup.subset_closure (Or.inl hc)

theorem rootDiagUnit_mem_twInndiag {σ : K ≃+* K} {b : Fin TwistTag.E6.tag.rank → Kˣ}
    (hb : IsCompatE6 σ.toRingHom b) : rootDiagUnit TwistTag.E6.tag b ∈ twInndiagGroup K σ :=
  Subgroup.subset_closure (Or.inr ⟨b, hb, rfl⟩)

theorem twistHom_eq_of_mem_twInndiag {σ : K ≃+* K} {w : ModGL TwistTag.E6.tag K}
    (hw : w ∈ twInndiagGroup K σ) : twistHom TwistTag.E6 K σ.toRingHom w = w := by
  have hle : twInndiagGroup K σ ≤
      (twistHom TwistTag.E6 K σ.toRingHom).eqLocus (MonoidHom.id _) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (hc | ⟨b, hb, rfl⟩)
    · exact (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom hc).2
    · exact twistHom_rootDiagUnit_of_compat hb
  exact hle hw

theorem diagramMap_conj_E6 {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K}
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) {w : ModGL TwistTag.E6.tag K} (hw : w ∈ twInndiagGroup K σ) :
    diagramMap TwistTag.E6 K * w * (diagramMap TwistTag.E6 K)⁻¹ =
      Units.map (entrywiseHom σ.toRingHom) w := by
  have : Fintype K := Fintype.ofFinite K
  have hσ2 : σ.toRingHom.comp σ.toRingHom = RingHom.id K := RingHom.ext fun c => by
    change σ (σ c) = c
    rw [hσ, hσ, ← pow_mul, show 2 ^ n * 2 ^ n = (2 ^ n) ^ 2 by ring, ← hK,
      Nat.card_eq_fintype_card, FiniteField.pow_card]
  have hF := twistHom_eq_of_mem_twInndiag hw
  conv_rhs => rw [← hF]
  rw [twistHom_apply, map_mul, map_mul, map_inv, units_map_entrywiseHom_diagramMap,
    units_map_entrywiseHom_comp, hσ2, units_map_entrywiseHom_id]

theorem entrywise_mem_twInndiag {σ : K ≃+* K} (δ : K ≃+* K) {w : ModGL TwistTag.E6.tag K}
    (hw : w ∈ twInndiagGroup K σ) :
    Units.map (entrywiseHom δ.toRingHom) w ∈ twInndiagGroup K σ := by
  have hle : twInndiagGroup K σ ≤ (twInndiagGroup K σ).comap (exactEntrywiseAut TwistTag.E6.tag
      δ).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ (hc | ⟨b, hb, rfl⟩)
    · exact graphFixedRootGroup_le_twInndiag σ
        (fieldActor (t := TwistTag.E6) σ δ ⟨_, hc⟩).2
    · rw [SetLike.mem_coe, Subgroup.mem_comap]
      change Units.map (entrywiseHom δ.toRingHom) (rootDiagUnit TwistTag.E6.tag b) ∈
        twInndiagGroup K σ
      rw [units_map_entrywiseHom_rootDiagUnit_ringEquiv]
      refine rootDiagUnit_mem_twInndiag fun i => ?_
      have hδσ : δ.toRingHom.comp σ.toRingHom = σ.toRingHom.comp δ.toRingHom :=
        congrArg RingEquiv.toRingHom (ringEquiv_mul_comm_of_finite δ σ)
      apply Units.ext
      simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
      rw [hb i]
      simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass]
      exact congrFun (congrArg DFunLike.coe hδσ) _
  exact hle hw

theorem map_exactEntrywiseAut_twInndiag {σ : K ≃+* K} (δ : K ≃+* K) :
    (twInndiagGroup K σ).map (exactEntrywiseAut TwistTag.E6.tag δ).toMonoidHom =
      twInndiagGroup K σ := by
  refine le_antisymm ?_ fun w hw => ?_
  · rintro _ ⟨w, hw, rfl⟩
    exact entrywise_mem_twInndiag δ hw
  · refine ⟨exactEntrywiseAut TwistTag.E6.tag δ.symm w, entrywise_mem_twInndiag δ.symm hw, ?_⟩
    exact (exactEntrywiseAut TwistTag.E6.tag δ).apply_symm_apply w

variable (K) in
@[expose] noncomputable def twInndiagFieldAut (σ : K ≃+* K) :
    (K ≃+* K) →* MulAut (twInndiagGroup K σ) where
  toFun δ := mulAutRestrict (twInndiagGroup K σ) (exactEntrywiseAut TwistTag.E6.tag δ)
    (map_exactEntrywiseAut_twInndiag δ)
  map_one' := by
    have h1 : (1 : K ≃+* K).toRingHom = RingHom.id K := RingHom.ext fun _ => rfl
    refine MulEquiv.ext fun w => Subtype.ext (Units.ext ?_)
    rw [coe_mulAutRestrict, exactEntrywiseAut_apply, MulAut.one_apply, Units.coe_map, h1]
    exact entrywise_id (R := K) _
  map_mul' δ δ' := MulEquiv.ext fun w => Subtype.ext
    (units_map_entrywiseHom_mul_ringEquiv δ δ' (w : ModGL TwistTag.E6.tag K))

theorem coe_twInndiagFieldAut (σ δ : K ≃+* K) (w : twInndiagGroup K σ) :
    ((twInndiagFieldAut K σ δ w : twInndiagGroup K σ) : ModGL TwistTag.E6.tag K) =
      Units.map (entrywiseHom δ.toRingHom) (w : ModGL TwistTag.E6.tag K) :=
  rfl

end Group

end RecipeExcLang

end CFSG.StandardType
