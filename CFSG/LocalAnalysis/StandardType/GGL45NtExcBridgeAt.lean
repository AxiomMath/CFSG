module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeE6
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeTwE6
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangInj

public section

noncomputable section

namespace CFSG.HardMathSupport.C14ExcBridgeE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType CFSG.Assembly
  CFSG.StandardType.RecipeExcLang CFSG.HardMathSupport.C14ExcBridgeU
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.C14ExcBridgeTwE6

@[expose] def BridgeConclAt (τ : Tag) (L : Type) [Field L] [CharP L 2] (p : ℕ) {R : Type}
    [Group R] (I F : Set (MulAut R)) (e : ℕ) (Q : ModGL τ L) (ρ : R →* ModGL τ L) : Prop :=
  1 ≤ e ∧ IsDiagramTwistMatrix τ L Q ∧
    ((∀ g ∈ adjointGroup τ L, frobTwistGL τ L 2 e Q g ∈ adjointGroup τ L) ∧
     ∃ Θ : ↥(adjointGroup τ L ⊓ (endPowU (frobTwistGL τ L 2 e Q) p).eqLocus (MonoidHom.id _)) →*
        MulAut R,
      Function.Injective ρ ∧
      (∀ r, ρ r ∈ adjointGroup τ L ⊓
        (endPowU (frobTwistGL τ L 2 e Q) p).eqLocus (MonoidHom.id _)) ∧
      Function.Injective Θ ∧ (∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ) ∧
      (∀ g r, ρ (Θ g r) = g * ρ r * (g : ModGL τ L)⁻¹) ∧
      ∀ f ∈ F, orderOf f = p →
        ∃ j : ℕ, ¬ p ∣ j ∧ ∀ r, ρ (f r) = (endPowU (frobTwistGL τ L 2 e Q) j) (ρ r)) ∧
    IsSteinbergEnd τ L ((2 ^ e) ^ p) (endPowU (frobTwistGL τ L 2 e Q) p) ∧
    Finite ↥(adjointGroup τ L ⊓ (endPowU (frobTwistGL τ L 2 e Q) p).eqLocus (MonoidHom.id _))

private noncomputable def bridgeAtE
    (τ : Tag) (K : Type) [Field K] [Finite K] :
    LargeEvenCenterQuot (adjointGroup τ K) ≃* ↥(adjointGroup τ K) :=
  centerQuotEquivOfBot center_adjointGroup_eq_bot

private noncomputable def bridgeAtRho
    (τ : Tag) (K : Type) [Field K] [Finite K]
    (L : Type) [Field L] [Algebra K L] :
    LargeEvenCenterQuot (adjointGroup τ K) →* ModGL τ L :=
  (baseChangeGL (algebraMap K L)).comp
    ((adjointGroup τ K).subtype.comp (bridgeAtE τ K).toMonoidHom)

private noncomputable def bridgeAtTheta
    (τ : Tag) (K : Type) [Field K] [Finite K]
    (L : Type) [Field L] [CharP L 2] {e p : ℕ}
    (ψ : inndiagGroup τ K ≃* ↥(adjointGroup τ L ⊓
      (endPowU (frobTwistGL τ L 2 e 1) p).eqLocus (MonoidHom.id _))) :
    ↥(adjointGroup τ L ⊓ (endPowU (frobTwistGL τ L 2 e 1) p).eqLocus (MonoidHom.id _)) →*
      MulAut (LargeEvenCenterQuot (adjointGroup τ K)) :=
  (autEquiv τ K).symm.toMonoidHom.comp ((inndiagConj τ K).comp ψ.symm.toMonoidHom)

private theorem bridgeAtE_apply
    {τ : Tag} {K : Type} [Field K] [Finite K]
    (φ : MulAut (LargeEvenCenterQuot (adjointGroup τ K)))
    (r : LargeEvenCenterQuot (adjointGroup τ K)) :
    bridgeAtE τ K (φ r) = autEquiv τ K φ (bridgeAtE τ K r) := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective r
  change bridgeAtE τ K (φ (LargeEvenCenterMk _ h)) =
    autEquiv τ K φ (bridgeAtE τ K (LargeEvenCenterMk _ h))
  rw [← autEquiv_apply]
  simp only [bridgeAtE, centerQuotEquivOfBot_mk]

private theorem bridgeAt_frob
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {p : ℕ} (hp : p.Prime)
    {E : LargeEvenCenterQuot (adjointGroup τ K) ≃* ↥(adjointGroup τ K)}
    (hE : ∀ (φ : MulAut (LargeEvenCenterQuot (adjointGroup τ K))) r,
      E (φ r) = autEquiv τ K φ (E r))
    {f : MulAut (LargeEvenCenterQuot (adjointGroup τ K))}
    (hf : f ∈ RecipeFieldExcInn.markFieldImage (IsRoot τ) K (adjointGroup τ K))
    (hfp : orderOf f = p) :
    p ∣ n ∧ ∃ j : ℕ, ¬ p ∣ j ∧ ∀ r,
      (E (f r) : ModGL τ K) = baseChangeGL (iterateFrobenius K 2 (n / p * j)) (E r) := by
  have hfield : ∃ σ : K ≃+* K, ∀ r, (E (f r) : ModGL τ K) =
      Units.map (entrywiseHom (σ : K →+* K)) (E r) := by
    obtain ⟨σ, hσ⟩ := autEquiv_eq_entrywise_of_mem_markField hf
    exact ⟨σ, fun r => by rw [hE, hσ, coe_entrywiseAdjointAut]; rfl⟩
  obtain ⟨σ, hσ⟩ := hfield
  exact frob_of_equiv hn hK hp E f σ hσ hfp

private theorem bridgeAt_hrat
    {τ : Tag} {K : Type} [Field K] [Finite K]
    {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] [Algebra K L] {p e : ℕ}
    (he : n = e * p) :
    adjointGroup τ L ⊓ (endPowU (frobTwistGL τ L 2 e 1) p).eqLocus (MonoidHom.id _) =
      (inndiagGroup τ K).map (baseChangeGL (algebraMap K L)) := by
  have hFr : ∀ c : L, iterateFrobenius L 2 (e * p) c = c ^ Nat.card K := fun c => by
    rw [iterateFrobenius_def, hK, he]
  have hbij : Function.Bijective (iterateFrobenius L 2 (e * p)) := by
    rw [← coe_iterateFrobeniusEquiv]
    exact (iterateFrobeniusEquiv L 2 (e * p)).bijective
  rw [← fixed_eq_map_inndiag _ hFr hbij]
  ext g
  change g ∈ adjointGroup τ L ∧ endPowU (frobTwistGL τ L 2 e 1) p g = g ↔
    g ∈ adjointGroup τ L ∧ Units.map (entrywiseHom (iterateFrobenius L 2 (e * p))) g = g
  rw [endPow_frobTwist_one]

private theorem bridgeAt_psi
    {τ : Tag} {K : Type} [Field K]
    {L : Type} [Field L] [CharP L 2] [Algebra K L] {e p : ℕ}
    (hrat : adjointGroup τ L ⊓ (endPowU (frobTwistGL τ L 2 e 1) p).eqLocus (MonoidHom.id _) =
      (inndiagGroup τ K).map (baseChangeGL (algebraMap K L))) :
    ∃ ψ : inndiagGroup τ K ≃* ↥(adjointGroup τ L ⊓
        (endPowU (frobTwistGL τ L 2 e 1) p).eqLocus (MonoidHom.id _)),
      ∀ g, baseChangeGL (algebraMap K L) ((ψ.symm g : inndiagGroup τ K) : ModGL τ K) =
        (g : ModGL τ L) := by
  have hmemΓ : ∀ w : inndiagGroup τ K, baseChangeGL (algebraMap K L) (w : ModGL τ K) ∈
      adjointGroup τ L ⊓ (endPowU (frobTwistGL τ L 2 e 1) p).eqLocus (MonoidHom.id _) :=
    fun w => by rw [hrat]; exact ⟨_, w.2, rfl⟩
  let ψ : inndiagGroup τ K ≃* ↥(adjointGroup τ L ⊓
      (endPowU (frobTwistGL τ L 2 e 1) p).eqLocus (MonoidHom.id _)) :=
    MulEquiv.ofBijective
      (((baseChangeGL (algebraMap K L)).comp (inndiagGroup τ K).subtype).codRestrict _ hmemΓ)
      ⟨fun w w' h => Subtype.ext (baseChangeGL_injective _ (congrArg Subtype.val h)),
        fun g => by
          have hg : (g : ModGL τ L) ∈ (inndiagGroup τ K).map (baseChangeGL (algebraMap K L)) := by
            rw [← hrat]; exact g.2
          obtain ⟨w, hw, hwg⟩ := hg
          exact ⟨⟨w, hw⟩, Subtype.ext hwg⟩⟩
  exact ⟨ψ, fun g => congrArg Subtype.val (ψ.apply_symm_apply g)⟩

private theorem bridgeAtTheta_injective
    {τ : Tag} {K : Type} [Field K] [Finite K]
    {L : Type} [Field L] [CharP L 2] {e p : ℕ}
    {ψ : inndiagGroup τ K ≃* ↥(adjointGroup τ L ⊓
      (endPowU (frobTwistGL τ L 2 e 1) p).eqLocus (MonoidHom.id _))}
    (hinj : Function.Injective (inndiagConj τ K)) :
    Function.Injective (bridgeAtTheta τ K L ψ) :=
  (autEquiv τ K).symm.injective.comp (hinj.comp ψ.symm.injective)

private theorem bridgeAtTheta_range
    {τ : Tag} {K : Type} [Field K] [Finite K]
    {L : Type} [Field L] [CharP L 2] {e p : ℕ}
    {ψ : inndiagGroup τ K ≃* ↥(adjointGroup τ L ⊓
      (endPowU (frobTwistGL τ L 2 e 1) p).eqLocus (MonoidHom.id _))} :
    ∀ φ, φ ∈ markIDImage (IsRoot τ) K (adjointGroup τ K) ↔
      ∃ g, (autEquiv τ K).symm (inndiagConj τ K (ψ.symm g)) = φ := by
  intro φ'
  constructor
  · intro hφ'
    obtain ⟨w, hw⟩ := exists_inndiagConj_of_mem_markID hφ'
    refine ⟨ψ w, ?_⟩
    show (autEquiv τ K).symm (inndiagConj τ K (ψ.symm (ψ w))) = φ'
    rw [ψ.symm_apply_apply, ← hw, MulEquiv.symm_apply_apply]
  · rintro ⟨g, rfl⟩
    exact inndiagConj_mem_markID _

private theorem bridgeAtTheta_action
    {τ : Tag} {K : Type} [Field K] [Finite K]
    {L : Type} [Field L] [CharP L 2] [Algebra K L] {e p : ℕ}
    {E : LargeEvenCenterQuot (adjointGroup τ K) ≃* ↥(adjointGroup τ K)}
    (hE : ∀ (φ : MulAut (LargeEvenCenterQuot (adjointGroup τ K))) r,
      E (φ r) = autEquiv τ K φ (E r))
    {ψ : inndiagGroup τ K ≃* ↥(adjointGroup τ L ⊓
      (endPowU (frobTwistGL τ L 2 e 1) p).eqLocus (MonoidHom.id _))}
    (hψs : ∀ g, baseChangeGL (algebraMap K L) ((ψ.symm g : inndiagGroup τ K) : ModGL τ K) =
      (g : ModGL τ L)) :
    ∀ g r, ((baseChangeGL (algebraMap K L)).comp
        ((adjointGroup τ K).subtype.comp E.toMonoidHom))
          ((autEquiv τ K).symm (inndiagConj τ K (ψ.symm g)) r) =
      (g : ModGL τ L) * ((baseChangeGL (algebraMap K L)).comp
        ((adjointGroup τ K).subtype.comp E.toMonoidHom)) r * (g : ModGL τ L)⁻¹ := by
  have hEs : ∀ (α : MulAut (adjointGroup τ K)) r, E ((autEquiv τ K).symm α r) = α (E r) :=
    fun α r => by rw [hE, MulEquiv.apply_symm_apply]
  intro g r
  change baseChangeGL (algebraMap K L)
    ((E ((autEquiv τ K).symm (inndiagConj τ K (ψ.symm g)) r) : adjointGroup τ K) : ModGL τ K) = _
  rw [hEs, coe_inndiagConj, map_mul, map_mul, map_inv, hψs]
  rfl

private theorem bridgeAtRho_injective
    {τ : Tag} {K : Type} [Field K] [Finite K]
    {L : Type} [Field L] [Algebra K L] :
    Function.Injective (bridgeAtRho τ K L) := by
  intro r r' h
  simp only [bridgeAtRho] at h
  apply (bridgeAtE τ K).injective
  apply Subtype.ext
  exact baseChangeGL_injective (algebraMap K L) h

private theorem bridgeAtRho_mem
    {τ : Tag} {K : Type} [Field K] [Finite K]
    {L : Type} [Field L] [CharP L 2] [Algebra K L] {e p : ℕ}
    (hrat : adjointGroup τ L ⊓ (endPowU (frobTwistGL τ L 2 e 1) p).eqLocus (MonoidHom.id _) =
      (inndiagGroup τ K).map (baseChangeGL (algebraMap K L))) :
    ∀ r, bridgeAtRho τ K L r ∈
      adjointGroup τ L ⊓ (endPowU (frobTwistGL τ L 2 e 1) p).eqLocus (MonoidHom.id _) := by
  intro r
  simp only [bridgeAtRho]
  rw [hrat]
  exact ⟨_, adjointGroup_le_inndiagGroup (bridgeAtE τ K r).2, rfl⟩

private theorem bridgeAt_first
    {τ : Tag} {L : Type} [Field L] [CharP L 2] (e : ℕ) :
    ∀ g ∈ adjointGroup τ L, frobTwistGL τ L 2 e 1 g ∈ adjointGroup τ L := by
  intro g hg
  rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
  exact CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ hg

private theorem bridgeAt_steinberg
    {τ : Tag} {L : Type} [Field L] [CharP L 2] (e p : ℕ) :
    IsSteinbergEnd τ L ((2 ^ e) ^ p) (endPowU (frobTwistGL τ L 2 e 1) p) := by
  refine ⟨iterateFrobenius L 2 (e * p), fun c => by rw [iterateFrobenius_def, pow_mul], 1,
    Or.inl rfl, fun g => ?_⟩
  rw [endPow_frobTwist_one, one_mul, inv_one, mul_one]

private theorem bridgeAt_finite
    {τ : Tag} {K : Type} [Field K] [Finite K]
    {L : Type} [Field L] [CharP L 2] [Algebra K L] {e p : ℕ}
    (hrat : adjointGroup τ L ⊓ (endPowU (frobTwistGL τ L 2 e 1) p).eqLocus (MonoidHom.id _) =
      (inndiagGroup τ K).map (baseChangeGL (algebraMap K L))) :
    Finite ↥(adjointGroup τ L ⊓ (endPowU (frobTwistGL τ L 2 e 1) p).eqLocus (MonoidHom.id _)) := by
  rw [hrat]
  haveI : Finite (inndiagGroup τ K) := finite_inndiagGroup
  exact Finite.of_surjective _ (MonoidHom.subgroupMap_surjective
    (baseChangeGL (algebraMap K L)) (inndiagGroup τ K))

private theorem bridgeAt_field_action
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {L : Type} [Field L] [CharP L 2] [Algebra K L] {p e : ℕ} (hp : p.Prime)
    (he : n = e * p) :
    ∀ f' ∈ RecipeFieldExcInn.markFieldImage (IsRoot τ) K (adjointGroup τ K),
      orderOf f' = p → ∃ j : ℕ, ¬ p ∣ j ∧ ∀ r, bridgeAtRho τ K L (f' r) =
        (endPowU (frobTwistGL τ L 2 e 1) j) (bridgeAtRho τ K L r) := by
  intro f' hf' hf'p
  have hE : ∀ (φ : MulAut (LargeEvenCenterQuot (adjointGroup τ K))) r,
      bridgeAtE τ K (φ r) = autEquiv τ K φ (bridgeAtE τ K r) := fun φ r => bridgeAtE_apply φ r
  have he' : n / p = e := by rw [he, Nat.mul_div_cancel _ hp.pos]
  obtain ⟨-, j, hpj, hj⟩ := bridgeAt_frob hn hK hp hE hf' hf'p
  rw [he'] at hj
  have hρ : ∀ r, bridgeAtRho τ K L r = baseChangeGL (algebraMap K L) (bridgeAtE τ K r) :=
    fun r => rfl
  refine ⟨j, hpj, fun r => ?_⟩
  rw [hρ, hρ, hj, baseChangeGL_baseChangeGL, endPow_frobTwist_one]
  change _ = baseChangeGL _ (baseChangeGL (algebraMap K L) _)
  rw [baseChangeGL_baseChangeGL]
  have hc : (algebraMap K L).comp (iterateFrobenius K 2 (e * j)) =
      (iterateFrobenius L 2 (e * j)).comp (algebraMap K L) := by
    ext c
    simp only [RingHom.comp_apply, iterateFrobenius_def, map_pow]
  rw [hc]

private theorem bridgeAt_model
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] [Algebra K L] {p : ℕ} (hp : p.Prime) :
    (∃ f ∈ RecipeFieldExcInn.markFieldImage (IsRoot τ) K (adjointGroup τ K), orderOf f = p) →
      ∃ e : ℕ, e * p = n ∧
        BridgeConclAt τ L p (markIDImage (IsRoot τ) K (adjointGroup τ K))
          (RecipeFieldExcInn.markFieldImage (IsRoot τ) K (adjointGroup τ K)) e 1
          (bridgeAtRho τ K L) := by
  classical
  rintro ⟨f, hfF, hfp⟩
  have hE : ∀ (φ : MulAut (LargeEvenCenterQuot (adjointGroup τ K))) r,
      bridgeAtE τ K (φ r) = autEquiv τ K φ (bridgeAtE τ K r) := fun φ r => bridgeAtE_apply φ r
  obtain ⟨hpn, -⟩ := bridgeAt_frob hn hK hp hE hfF hfp
  set e := n / p with he
  have hnpe : n = e * p := (Nat.div_mul_cancel hpn).symm
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · rw [h, zero_mul] at hnpe; omega
    · exact h
  have hK4 : 4 ≤ Nat.card K := by
    have h2n : 2 ≤ n := le_trans hp.two_le (Nat.le_of_dvd (by omega) hpn)
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2n
  have hrat : adjointGroup τ L ⊓
      (endPowU (frobTwistGL τ L 2 e 1) p).eqLocus (MonoidHom.id _) =
      (inndiagGroup τ K).map (baseChangeGL (algebraMap K L)) :=
    bridgeAt_hrat hK hnpe
  obtain ⟨ψ, hψs⟩ := bridgeAt_psi hrat
  have hinj : Function.Injective (inndiagConj τ K) := inndiagConj_injective_of_four_le hK4
  refine ⟨e, hnpe.symm, he1, Or.inl rfl,
    ⟨bridgeAt_first (τ := τ) (L := L) e, bridgeAtTheta τ K L ψ, bridgeAtRho_injective,
      bridgeAtRho_mem hrat, bridgeAtTheta_injective hinj, bridgeAtTheta_range,
      bridgeAtTheta_action hE hψs, bridgeAt_field_action hn hK hp hnpe⟩,
    bridgeAt_steinberg (τ := τ) (L := L) e p, bridgeAt_finite hrat⟩

private theorem bridgeAt_chev_mark
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] [Algebra K L] {p : ℕ} (hp : p.Prime) :
∀ (S : (Fin τ.rank → ℤ) → Prop), S = IsRoot τ →
      (∃ f ∈ RecipeFieldExcInn.markFieldImage S K (MarkChev.chevH τ.cartan S K false),
        orderOf f = p) →
      ∃ e : ℕ, e * p = n ∧
        ∃ ε : LargeEvenCenterQuot (MarkChev.chevH τ.cartan S K false) ≃* ↥(adjointGroup τ K),
          BridgeConclAt τ L p (markIDImage S K (MarkChev.chevH τ.cartan S K false))
            (RecipeFieldExcInn.markFieldImage S K (MarkChev.chevH τ.cartan S K false)) e 1
            ((baseChangeGL (algebraMap K L)).comp
              ((adjointGroup τ K).subtype.comp ε.toMonoidHom)) := by
    intro S hS
    subst hS
    suffices key : ∀ (H : Subgroup (MarkChev.GLS (IsRoot τ) K)), H = adjointGroup τ K →
        (∃ f ∈ RecipeFieldExcInn.markFieldImage (IsRoot τ) K H, orderOf f = p) →
        ∃ e : ℕ, e * p = n ∧
          ∃ ε : LargeEvenCenterQuot H ≃* ↥(adjointGroup τ K),
            BridgeConclAt τ L p (markIDImage (IsRoot τ) K H)
              (RecipeFieldExcInn.markFieldImage (IsRoot τ) K H) e 1
              ((baseChangeGL (algebraMap K L)).comp
                ((adjointGroup τ K).subtype.comp ε.toMonoidHom)) from
      key _ (chevH_false_eq_adjointGroup K τ)
    intro H hH
    subst hH
    intro hfH
    obtain ⟨e, hep, hconcl⟩ := bridgeAt_model hn hK L hp hfH
    exact ⟨e, hep, bridgeAtE τ K, hconcl⟩

private noncomputable def bridgeAtTwE6E
    (K : Type) [Field K] (σ : K ≃+* K) :
    LargeEvenCenterQuot (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃*
      ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :=
  centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ)

private noncomputable def bridgeAtTwE6Rho
    (K : Type) [Field K] (σ : K ≃+* K)
    (L : Type) [Field L] [Algebra K L] :
    LargeEvenCenterQuot (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →*
      ModGL TwistTag.E6.tag L :=
  (baseChangeGL (algebraMap K L)).comp
    ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype.comp (bridgeAtTwE6E K σ).toMonoidHom)

private noncomputable def bridgeAtTwE6Theta
    (K : Type) [Field K] [Finite K] (σ : K ≃+* K)
    (L : Type) [Field L] [CharP L 2] {e p : ℕ}
    (ψ : twInndiagGroup K σ ≃* ↥(adjointGroup TwistTag.E6.tag L ⊓
      (endPowU (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) p).eqLocus
        (MonoidHom.id _))) :
    ↥(adjointGroup TwistTag.E6.tag L ⊓
      (endPowU (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) p).eqLocus
        (MonoidHom.id _)) →*
      MulAut (LargeEvenCenterQuot (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :=
  (MulAut.congr (bridgeAtTwE6E K σ)).symm.toMonoidHom.comp
    ((twConj K σ).comp ψ.symm.toMonoidHom)

private theorem bridgeAtTwE6E_apply
    {K : Type} [Field K] {σ : K ≃+* K}
    (φ : MulAut (LargeEvenCenterQuot (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)))
    (r : LargeEvenCenterQuot (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
    bridgeAtTwE6E K σ (φ r) =
      MulAut.congr (bridgeAtTwE6E K σ) φ (bridgeAtTwE6E K σ r) := by
  show bridgeAtTwE6E K σ (φ r) =
    bridgeAtTwE6E K σ (φ ((bridgeAtTwE6E K σ).symm (bridgeAtTwE6E K σ r)))
  rw [MulEquiv.symm_apply_apply]

private theorem bridgeAtTwE6_frob
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {f : MulAut (LargeEvenCenterQuot (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))}
    (hf : f ∈ RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.E6.tag) K
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
    (hfp : orderOf f = p) :
    p ∣ n ∧ ∃ j : ℕ, ¬ p ∣ j ∧ ∀ r,
      (bridgeAtTwE6E K σ (f r) : ModGL TwistTag.E6.tag K) =
        baseChangeGL (iterateFrobenius K 2 (2 * (n / p) * j)) (bridgeAtTwE6E K σ r) := by
  have hK2 : Nat.card K = 2 ^ (n * 2) := by rw [hK, ← pow_mul]
  haveI : CharP K 2 := charP_two_of_card hK2
  have hE : ∀ (φ : MulAut (LargeEvenCenterQuot (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))) r,
      bridgeAtTwE6E K σ (φ r) =
        MulAut.congr (bridgeAtTwE6E K σ) φ (bridgeAtTwE6E K σ r) :=
    fun φ r => bridgeAtTwE6E_apply φ r
  obtain ⟨-, -, -, -, -, -, hfield, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hn K hK σ hσ
  have hfieldE : ∀ f' ∈ RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.E6.tag) K
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom), ∃ δ : K ≃+* K,
      MulAut.congr (bridgeAtTwE6E K σ) f' = fieldActor σ δ := by
    rintro f' ⟨δ, hG⟩
    refine ⟨δ, MulEquiv.ext fun c => ?_⟩
    show bridgeAtTwE6E K σ (f' ((bridgeAtTwE6E K σ).symm c)) = fieldActor σ δ c
    rw [show bridgeAtTwE6E K σ = centerQuotEquivOfBot
        (exceptional_fixed_center_trivial TwistTag.E6 K σ) from rfl,
      centerQuotEquivOfBot_symm]
    rw [hG c (fieldActor σ δ c) (by
      show (((fieldActor σ δ c : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :
        ModGL TwistTag.E6.tag K) : Module.End K (RootModule TwistTag.E6.tag K)) = _
      rw [hfield]
      rfl), centerQuotEquivOfBot_mk]
  obtain ⟨δ, hδ⟩ := hfieldE f hf
  obtain ⟨hpn, j, hpj, hδj⟩ := field_of_order hn hK σ hσ hp hp2 (bridgeAtTwE6E K σ) f δ hδ hfp
  refine ⟨hpn, j, hpj, fun r => ?_⟩
  rw [hE, hδ, hfield]
  have hthis : δ.toRingHom = iterateFrobenius K 2 (2 * (n / p) * j) :=
    RingHom.ext fun c => by rw [iterateFrobenius_def]; exact hδj c
  rw [hthis]
  rfl

private theorem bridgeAtTwE6_hrat
    {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    [Algebra K L] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : n = e * p) :
    adjointGroup TwistTag.E6.tag L ⊓
      (endPowU (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) p).eqLocus
        (MonoidHom.id _) =
      (twInndiagGroup K σ).map (baseChangeGL (algebraMap K L)) := by
  have hK2 : Nat.card K = 2 ^ (n * 2) := by rw [hK, ← pow_mul]
  haveI : CharP K 2 := charP_two_of_card hK2
  have hP2 : (diagramMap TwistTag.E6 L) ^ 2 = 1 := diagramMap_pow_order TwistTag.E6 L
  have hPfix : ∀ k, Units.map (entrywiseHom (iterateFrobenius L 2 k))
      (diagramMap TwistTag.E6 L) = diagramMap TwistTag.E6 L :=
    fun k => units_map_entrywiseHom_diagramMap (σ := iterateFrobenius L 2 k)
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have hPp : (diagramMap TwistTag.E6 L) ^ p = diagramMap TwistTag.E6 L := by
    rw [hk, pow_succ, pow_mul, hP2, one_pow, one_mul]
  have hΦ : ∀ g, endPowU (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) p g =
      twistHom TwistTag.E6 L (iterateFrobenius L 2 n) g := fun g => by
    rw [endPow_frobTwist_of_fixed e p (hPfix e), hPp, ← he, twistHom_apply]
  rw [← twisted_fixed_eq_map hn hK σ hσ (iterateFrobenius L 2 n)
    (fun c => by rw [iterateFrobenius_def])]
  ext g
  change g ∈ adjointGroup TwistTag.E6.tag L ∧
      endPowU (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) p g = g ↔
    g ∈ adjointGroup TwistTag.E6.tag L ∧
      twistHom TwistTag.E6 L (iterateFrobenius L 2 n) g = g
  rw [hΦ]

private theorem bridgeAtTwE6_psi
    {K : Type} [Field K] {σ : K ≃+* K}
    {L : Type} [Field L] [CharP L 2] [Algebra K L] {e p : ℕ}
    (hrat : adjointGroup TwistTag.E6.tag L ⊓
        (endPowU (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) p).eqLocus
          (MonoidHom.id _) =
      (twInndiagGroup K σ).map (baseChangeGL (algebraMap K L))) :
    ∃ ψ : twInndiagGroup K σ ≃* ↥(adjointGroup TwistTag.E6.tag L ⊓
        (endPowU (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) p).eqLocus
          (MonoidHom.id _)),
      ∀ g, baseChangeGL (algebraMap K L) ((ψ.symm g : twInndiagGroup K σ) :
        ModGL TwistTag.E6.tag K) = (g : ModGL TwistTag.E6.tag L) := by
  have hmemΓ : ∀ w : twInndiagGroup K σ,
      baseChangeGL (algebraMap K L) (w : ModGL TwistTag.E6.tag K) ∈
        adjointGroup TwistTag.E6.tag L ⊓
          (endPowU (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) p).eqLocus
            (MonoidHom.id _) :=
    fun w => by rw [hrat]; exact ⟨_, w.2, rfl⟩
  let ψ : twInndiagGroup K σ ≃* ↥(adjointGroup TwistTag.E6.tag L ⊓
      (endPowU (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) p).eqLocus
        (MonoidHom.id _)) :=
    MulEquiv.ofBijective
      (((baseChangeGL (algebraMap K L)).comp (twInndiagGroup K σ).subtype).codRestrict _
        hmemΓ)
      ⟨fun w w' h => Subtype.ext (baseChangeGL_injective _ (congrArg Subtype.val h)),
        fun g => by
          have hg : (g : ModGL TwistTag.E6.tag L) ∈
              (twInndiagGroup K σ).map (baseChangeGL (algebraMap K L)) := by
            rw [← hrat]; exact g.2
          obtain ⟨w, hw, hwg⟩ := hg
          exact ⟨⟨w, hw⟩, Subtype.ext hwg⟩⟩
  exact ⟨ψ, fun g => congrArg Subtype.val (ψ.apply_symm_apply g)⟩

private theorem bridgeAtTwE6_conj_injective
    {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) (hq3 : 3 ≤ 2 ^ n) :
    Function.Injective (twConj K σ) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro w hw
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  show (w : ModGL TwistTag.E6.tag K) = 1
  refine eq_one_of_commute_C0 hn hK hσ hq3 w.2 fun c hc => ?_
  have := congrArg (fun α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) =>
    ((α ⟨c, hc⟩ : graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :
      ModGL TwistTag.E6.tag K)) (MonoidHom.mem_ker.1 hw)
  change (w : ModGL TwistTag.E6.tag K) * c * (w : ModGL TwistTag.E6.tag K)⁻¹ = c at this
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this

private theorem bridgeAtTwE6Theta_injective
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {L : Type} [Field L] [CharP L 2] {e p : ℕ}
    {ψ : twInndiagGroup K σ ≃* ↥(adjointGroup TwistTag.E6.tag L ⊓
      (endPowU (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) p).eqLocus
        (MonoidHom.id _))}
    (hinj : Function.Injective (twConj K σ)) :
    Function.Injective (bridgeAtTwE6Theta K σ L ψ) :=
  (MulAut.congr (bridgeAtTwE6E K σ)).symm.injective.comp (hinj.comp ψ.symm.injective)

private theorem bridgeAtTwE6Theta_range
    {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) (hq3 : 3 ≤ 2 ^ n)
    {L : Type} [Field L] [CharP L 2] {e p : ℕ}
    {ψ : twInndiagGroup K σ ≃* ↥(adjointGroup TwistTag.E6.tag L ⊓
      (endPowU (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) p).eqLocus
        (MonoidHom.id _))} :
    ∀ φ, φ ∈ markIDImage (IsRoot TwistTag.E6.tag) K
        (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ↔
      ∃ g, (MulAut.congr (bridgeAtTwE6E K σ)).symm (twConj K σ (ψ.symm g)) = φ := by
  intro φ'
  constructor
  · intro hφ'
    obtain ⟨w, hw⟩ := markID_subset_range hn hK σ hσ hq3 hφ'
    refine ⟨ψ w, ?_⟩
    show (MulAut.congr (bridgeAtTwE6E K σ)).symm
      (twConj K σ (ψ.symm (ψ w))) = φ'
    rw [ψ.symm_apply_apply, ← hw,
      show bridgeAtTwE6E K σ = centerQuotEquivOfBot
        (exceptional_fixed_center_trivial TwistTag.E6 K σ) from rfl,
      MulEquiv.symm_apply_apply]
  · rintro ⟨g, rfl⟩
    exact twConj_mem_markID hn hK σ hσ _

private theorem bridgeAtTwE6Theta_action
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {L : Type} [Field L] [CharP L 2] [Algebra K L] {e p : ℕ}
    {ψ : twInndiagGroup K σ ≃* ↥(adjointGroup TwistTag.E6.tag L ⊓
      (endPowU (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) p).eqLocus
        (MonoidHom.id _))}
    (hψs : ∀ g, baseChangeGL (algebraMap K L) ((ψ.symm g : twInndiagGroup K σ) :
      ModGL TwistTag.E6.tag K) = (g : ModGL TwistTag.E6.tag L)) :
    ∀ g r, ((baseChangeGL (algebraMap K L)).comp
        ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype.comp
          (bridgeAtTwE6E K σ).toMonoidHom))
          ((MulAut.congr (bridgeAtTwE6E K σ)).symm (twConj K σ (ψ.symm g)) r) =
      (g : ModGL TwistTag.E6.tag L) * ((baseChangeGL (algebraMap K L)).comp
        ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype.comp
          (bridgeAtTwE6E K σ).toMonoidHom)) r *
          (g : ModGL TwistTag.E6.tag L)⁻¹ := by
  have hE : ∀ (φ : MulAut (LargeEvenCenterQuot (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))) r,
      bridgeAtTwE6E K σ (φ r) =
        MulAut.congr (bridgeAtTwE6E K σ) φ (bridgeAtTwE6E K σ r) :=
    fun φ r => bridgeAtTwE6E_apply φ r
  have hEs : ∀ (α : MulAut (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) r,
      bridgeAtTwE6E K σ ((MulAut.congr (bridgeAtTwE6E K σ)).symm α r) = α (bridgeAtTwE6E K σ r) :=
    fun α r => by rw [hE, MulEquiv.apply_symm_apply]
  intro g r
  change baseChangeGL (algebraMap K L)
    ((bridgeAtTwE6E K σ ((MulAut.congr (bridgeAtTwE6E K σ)).symm
      (twConj K σ (ψ.symm g)) r) :
        graphFixedRootGroup TwistTag.E6 K σ.toRingHom) : ModGL TwistTag.E6.tag K) = _
  rw [hEs, coe_twConj, map_mul, map_mul, map_inv, hψs]
  rfl

private theorem bridgeAtTwE6Rho_injective
    {K : Type} [Field K] {σ : K ≃+* K}
    {L : Type} [Field L] [Algebra K L] :
    Function.Injective (bridgeAtTwE6Rho K σ L) := by
  intro r r' h
  simp only [bridgeAtTwE6Rho] at h
  apply (bridgeAtTwE6E K σ).injective
  apply Subtype.ext
  exact baseChangeGL_injective (algebraMap K L) h

private theorem bridgeAtTwE6Rho_mem
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {L : Type} [Field L] [CharP L 2] [Algebra K L] {e p : ℕ}
    (hrat : adjointGroup TwistTag.E6.tag L ⊓
        (endPowU (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) p).eqLocus
          (MonoidHom.id _) =
      (twInndiagGroup K σ).map (baseChangeGL (algebraMap K L))) :
    ∀ r, bridgeAtTwE6Rho K σ L r ∈ adjointGroup TwistTag.E6.tag L ⊓
      (endPowU (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) p).eqLocus
        (MonoidHom.id _) := by
  intro r
  simp only [bridgeAtTwE6Rho]
  rw [hrat]
  exact ⟨_, graphFixedRootGroup_le_twInndiag σ (bridgeAtTwE6E K σ r).2, rfl⟩

private theorem bridgeAtTwE6_first
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2] (e : ℕ) :
    ∀ g ∈ adjointGroup TwistTag.E6.tag L,
      frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L) g ∈
        adjointGroup TwistTag.E6.tag L := by
  have hD : IsDiagramTwistMatrix TwistTag.E6.tag L (diagramMap TwistTag.E6 L) :=
    Or.inr ⟨TwistTag.E6, 1, rfl, by rw [zpow_one]⟩
  intro g hg
  rw [frobTwistGL_apply, ← hD.map_conj_eq]
  exact ⟨_, entrywiseFrobGL_mem 2 e hg, rfl⟩

private theorem bridgeAtTwE6_finite
    {K : Type} [Field K] [Finite K] {σ : K ≃+* K}
    {L : Type} [Field L] [CharP L 2] [Algebra K L] {e p : ℕ}
    (hrat : adjointGroup TwistTag.E6.tag L ⊓
        (endPowU (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) p).eqLocus
          (MonoidHom.id _) =
      (twInndiagGroup K σ).map (baseChangeGL (algebraMap K L))) :
    Finite ↥(adjointGroup TwistTag.E6.tag L ⊓
      (endPowU (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) p).eqLocus
        (MonoidHom.id _)) := by
  rw [hrat]
  haveI : Finite (inndiagGroup TwistTag.E6.tag K) := finite_inndiagGroup
  haveI : Finite (twInndiagGroup K σ) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (twInndiag_le_inndiag σ))
  exact Finite.of_surjective _ (MonoidHom.subgroupMap_surjective
    (baseChangeGL (algebraMap K L)) (twInndiagGroup K σ))

private theorem bridgeAtTwE6_field_action
    {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) {L : Type} [Field L] [CharP L 2]
    [Algebra K L] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : n = e * p) :
    ∀ f' ∈ RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.E6.tag) K
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      orderOf f' = p → ∃ j : ℕ, ¬ p ∣ j ∧ ∀ r, bridgeAtTwE6Rho K σ L (f' r) =
        (endPowU (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) j)
          (bridgeAtTwE6Rho K σ L r) := by
  intro f' hf' hf'p
  have hK2 : Nat.card K = 2 ^ (n * 2) := by rw [hK, ← pow_mul]
  haveI : CharP K 2 := charP_two_of_card hK2
  have he' : n / p = e := by rw [he, Nat.mul_div_cancel _ hp.pos]
  obtain ⟨-, j, hpj, hj⟩ := bridgeAtTwE6_frob hn hK σ hσ hp hp2 hf' hf'p
  rw [he'] at hj
  have hP2 : (diagramMap TwistTag.E6 L) ^ 2 = 1 := diagramMap_pow_order TwistTag.E6 L
  have hPfix : ∀ k, Units.map (entrywiseHom (iterateFrobenius L 2 k))
      (diagramMap TwistTag.E6 L) = diagramMap TwistTag.E6 L :=
    fun k => units_map_entrywiseHom_diagramMap (σ := iterateFrobenius L 2 k)
  have hρ : ∀ r, bridgeAtTwE6Rho K σ L r =
      baseChangeGL (algebraMap K L) (bridgeAtTwE6E K σ r) := fun r => rfl
  refine ⟨2 * j, fun h => ?_, fun r => ?_⟩
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
    · exact hpj h
  rw [hρ, hρ, hj, baseChangeGL_baseChangeGL, endPow_frobTwist_of_fixed e (2 * j) (hPfix e),
    pow_mul, hP2, one_pow, one_mul, inv_one, mul_one]
  change _ = baseChangeGL _ (baseChangeGL (algebraMap K L) _)
  rw [baseChangeGL_baseChangeGL]
  have hc : (algebraMap K L).comp (iterateFrobenius K 2 (2 * e * j)) =
      (iterateFrobenius L 2 (e * (2 * j))).comp (algebraMap K L) := by
    ext c
    simp only [RingHom.comp_apply, iterateFrobenius_def, map_pow]
    ring_nf
  rw [hc]

private theorem bridgeAtTwE6_steinberg
    {L : Type}
    [Field L] [CharP L 2] {n : ℕ} {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : n = e * p) :
    IsSteinbergEnd TwistTag.E6.tag L ((2 ^ e) ^ p)
      (endPowU (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) p) := by
  have hP2 : (diagramMap TwistTag.E6 L) ^ 2 = 1 := diagramMap_pow_order TwistTag.E6 L
  have hPfix : ∀ k, Units.map (entrywiseHom (iterateFrobenius L 2 k))
      (diagramMap TwistTag.E6 L) = diagramMap TwistTag.E6 L :=
    fun k => units_map_entrywiseHom_diagramMap (σ := iterateFrobenius L 2 k)
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have hPp : (diagramMap TwistTag.E6 L) ^ p = diagramMap TwistTag.E6 L := by
    rw [hk, pow_succ, pow_mul, hP2, one_pow, one_mul]
  have hΦ : ∀ g, endPowU (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) p g =
      twistHom TwistTag.E6 L (iterateFrobenius L 2 n) g := fun g => by
    rw [endPow_frobTwist_of_fixed e p (hPfix e), hPp, ← he, twistHom_apply]
  refine ⟨iterateFrobenius L 2 (e * p), fun c => by rw [iterateFrobenius_def, pow_mul],
    diagramMap TwistTag.E6 L, Or.inr ⟨TwistTag.E6, rfl, rfl⟩, fun g => ?_⟩
  rw [hΦ, twistHom_apply, ← he]

private theorem bridgeAtTwE6_model
    {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] [Algebra K L] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) :
    (∃ f ∈ RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.E6.tag) K
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom), orderOf f = p) →
      ∃ e : ℕ, e * p = n ∧
        ∃ ε : LargeEvenCenterQuot (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃*
          ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
          BridgeConclAt TwistTag.E6.tag L p
            (markIDImage (IsRoot TwistTag.E6.tag) K
              (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
            (RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.E6.tag) K
              (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) e
            (diagramMap TwistTag.E6 L)
            ((baseChangeGL (algebraMap K L)).comp
              ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype.comp ε.toMonoidHom)) := by
  classical
  have hK2 : Nat.card K = 2 ^ (n * 2) := by rw [hK, ← pow_mul]
  haveI : CharP K 2 := charP_two_of_card hK2
  rintro ⟨f, hfF, hfp⟩
  obtain ⟨hpn, -⟩ := bridgeAtTwE6_frob hn hK σ hσ hp hp2 hfF hfp
  set e := n / p with he
  have hnpe : n = e * p := (Nat.div_mul_cancel hpn).symm
  have he1 : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with h | h
    · rw [h, zero_mul] at hnpe; omega
    · exact h
  have hq3 : 3 ≤ 2 ^ n := by
    have h2n : 2 ≤ n := le_trans hp.two_le (Nat.le_of_dvd (by omega) hpn)
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h2n
  have hrat : adjointGroup TwistTag.E6.tag L ⊓
      (endPowU (frobTwistGL TwistTag.E6.tag L 2 e (diagramMap TwistTag.E6 L)) p).eqLocus
        (MonoidHom.id _) =
      (twInndiagGroup K σ).map (baseChangeGL (algebraMap K L)) :=
    bridgeAtTwE6_hrat hn hK σ hσ hp hp2 hnpe
  obtain ⟨ψ, hψs⟩ := bridgeAtTwE6_psi hrat
  have hinj : Function.Injective (twConj K σ) :=
    bridgeAtTwE6_conj_injective hn hK σ hσ hq3
  have hD : IsDiagramTwistMatrix TwistTag.E6.tag L (diagramMap TwistTag.E6 L) :=
    Or.inr ⟨TwistTag.E6, 1, rfl, by rw [zpow_one]⟩
  have hstein := bridgeAtTwE6_steinberg (L := L) hp hp2 hnpe
  refine ⟨e, hnpe.symm, bridgeAtTwE6E K σ, he1, hD,
    ⟨bridgeAtTwE6_first e, bridgeAtTwE6Theta K σ L ψ, bridgeAtTwE6Rho_injective,
      bridgeAtTwE6Rho_mem hrat, bridgeAtTwE6Theta_injective hinj,
      bridgeAtTwE6Theta_range hn hK σ hσ hq3,
      bridgeAtTwE6Theta_action hψs, bridgeAtTwE6_field_action hn hK σ hσ hp hp2 hnpe⟩,
    hstein, bridgeAtTwE6_finite hrat⟩


private theorem bridgeAtTwE6_chev_mark
    {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2]
    [Algebra K L] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hH : MarkChev.twistedH TwistTag.E6.tag.cartan (IsRoot TwistTag.E6.tag) K
      TwistTag.E6.perm n = graphFixedRootGroup TwistTag.E6 K σ.toRingHom) :
∀ (S : (Fin TwistTag.E6.tag.rank → ℤ) → Prop), S = IsRoot TwistTag.E6.tag →
      (∃ f ∈ RecipeFieldExcInn.markFieldImage S K
        (MarkChev.twistedH TwistTag.E6.tag.cartan S K TwistTag.E6.perm n), orderOf f = p) →
      ∃ e : ℕ, e * p = n ∧
        ∃ ε : LargeEvenCenterQuot (MarkChev.twistedH TwistTag.E6.tag.cartan S K
            TwistTag.E6.perm n) ≃* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
          BridgeConclAt TwistTag.E6.tag L p
            (markIDImage S K (MarkChev.twistedH TwistTag.E6.tag.cartan S K TwistTag.E6.perm n))
            (RecipeFieldExcInn.markFieldImage S K
              (MarkChev.twistedH TwistTag.E6.tag.cartan S K TwistTag.E6.perm n))
            e (diagramMap TwistTag.E6 L)
            ((baseChangeGL (algebraMap K L)).comp
              ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype.comp ε.toMonoidHom)) := by
    intro S hS
    subst hS
    suffices key : ∀ (H : Subgroup (MarkChev.GLS (IsRoot TwistTag.E6.tag) K)),
        H = graphFixedRootGroup TwistTag.E6 K σ.toRingHom →
        (∃ f ∈ RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.E6.tag) K H,
          orderOf f = p) →
        ∃ e : ℕ, e * p = n ∧
          ∃ ε : LargeEvenCenterQuot H ≃* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
            BridgeConclAt TwistTag.E6.tag L p (markIDImage (IsRoot TwistTag.E6.tag) K H)
              (RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.E6.tag) K H) e
              (diagramMap TwistTag.E6 L)
              ((baseChangeGL (algebraMap K L)).comp
                ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype.comp ε.toMonoidHom)) from
      key _ hH
    intro H hH'
    subst hH'
    intro hfH
    exact bridgeAtTwE6_model hn hK σ hσ L hp hp2 hfH


theorem bridge_chev_spec
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] [Algebra K L]
    {p : ℕ} (hp : p.Prime)
    (hf : ∃ f ∈ LargeEvenChevFieldImage τ.cartan K (LargeEvenChevH τ.cartan K false),
      orderOf f = p) :
    ∃ e : ℕ, e * p = n ∧
      ∃ ε : LargeEvenCenterQuot (LargeEvenChevH τ.cartan K false) ≃* ↥(adjointGroup τ K),
        BridgeConclAt τ L p (LargeEvenChevIDImage τ.cartan K (LargeEvenChevH τ.cartan K false))
          (LargeEvenChevFieldImage τ.cartan K (LargeEvenChevH τ.cartan K false)) e 1
          ((baseChangeGL (algebraMap K L)).comp
            ((adjointGroup τ K).subtype.comp ε.toMonoidHom)) := by
  have h2 := bridgeAt_chev_mark hn hK L hp _ (largeEvenIsRoot_eq_isRoot τ)
  suffices key : ∀ (H : Subgroup (LargeEvenChevGL τ.cartan K)),
      H = MarkChev.chevH τ.cartan (LargeEvenIsRoot τ.cartan) K false →
      (∃ f ∈ LargeEvenChevFieldImage τ.cartan K H, orderOf f = p) →
      ∃ e : ℕ, e * p = n ∧
        ∃ ε : LargeEvenCenterQuot H ≃* ↥(adjointGroup τ K),
          BridgeConclAt τ L p (LargeEvenChevIDImage τ.cartan K H)
            (LargeEvenChevFieldImage τ.cartan K H) e 1
            ((baseChangeGL (algebraMap K L)).comp
              ((adjointGroup τ K).subtype.comp ε.toMonoidHom)) from
    key _ (largeEvenChevH_eq τ.cartan K false) hf
  intro H hH
  subst hH
  rw [largeEvenChevIDImage_eq]
  exact h2


theorem bridge_twE6_chev_spec
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] [Algebra K L] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2)
    (hf : ∃ f ∈ LargeEvenChevFieldImage TwistTag.E6.tag.cartan K
        (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n), orderOf f = p) :
    ∃ e : ℕ, e * p = n ∧
      ∃ ε : LargeEvenCenterQuot (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n) ≃*
          ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
        BridgeConclAt TwistTag.E6.tag L p
          (LargeEvenChevIDImage TwistTag.E6.tag.cartan K
            (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n))
          (LargeEvenChevFieldImage TwistTag.E6.tag.cartan K
            (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n))
          e (diagramMap TwistTag.E6 L)
          ((baseChangeGL (algebraMap K L)).comp
            ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype.comp ε.toMonoidHom)) := by
  have hK2 : Nat.card K = 2 ^ (n * 2) := by rw [hK, ← pow_mul]
  haveI : CharP K 2 := charP_two_of_card hK2
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hperf, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hn K hK σ hσ
  have hH : MarkChev.twistedH TwistTag.E6.tag.cartan (IsRoot TwistTag.E6.tag) K
      TwistTag.E6.perm n = graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    (twistedH_eq_commutator K TwistTag.E6 n σ.toRingHom hσ).trans hperf
  have h2 := bridgeAtTwE6_chev_mark hn hK σ hσ L hp hp2 hH _
    (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag)
  suffices key : ∀ (H : Subgroup (LargeEvenChevGL TwistTag.E6.tag.cartan K)),
      H = MarkChev.twistedH TwistTag.E6.tag.cartan (LargeEvenIsRoot TwistTag.E6.tag.cartan) K
        TwistTag.E6.perm n →
      (∃ f ∈ LargeEvenChevFieldImage TwistTag.E6.tag.cartan K H, orderOf f = p) →
      ∃ e : ℕ, e * p = n ∧
        ∃ ε : LargeEvenCenterQuot H ≃* ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
          BridgeConclAt TwistTag.E6.tag L p (LargeEvenChevIDImage TwistTag.E6.tag.cartan K H)
            (LargeEvenChevFieldImage TwistTag.E6.tag.cartan K H) e (diagramMap TwistTag.E6 L)
            ((baseChangeGL (algebraMap K L)).comp
              ((graphFixedRootGroup TwistTag.E6 K σ.toRingHom).subtype.comp ε.toMonoidHom)) from
    key _ (largeEvenTwistedH_eq _ K _ n) hf
  intro H hH'
  subst hH'
  rw [largeEvenChevIDImage_eq]
  exact h2


end CFSG.HardMathSupport.C14ExcBridgeE6
