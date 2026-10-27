module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeU
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangModel
public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup

public section

namespace CFSG.HardMathSupport.C14ExcBridgeE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType CFSG.Assembly
  CFSG.StandardType.RecipeExcLang CFSG.HardMathSupport.C14ExcBridgeU
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Torality

noncomputable section

@[expose] def BridgeConcl (τ : Tag) (L : Type) [Field L] [CharP L 2] (p : ℕ) {R : Type} [Group R]
    (I F : Set (MulAut R)) : Prop :=
  (∃ f ∈ F, orderOf f = p) →
    ∃ (e : ℕ) (Q : ModGL τ L),
      1 ≤ e ∧ IsDiagramTwistMatrix τ L Q ∧
      ((∀ g ∈ adjointGroup τ L, frobTwistGL τ L 2 e Q g ∈ adjointGroup τ L) ∧
       ∃ (ρ : R →* ModGL τ L)
        (Θ : ↥(adjointGroup τ L ⊓ (endPowU (frobTwistGL τ L 2 e Q) p).eqLocus (MonoidHom.id _)) →*
          MulAut R),
        Function.Injective ρ ∧
        (∀ r, ρ r ∈ adjointGroup τ L ⊓
          (endPowU (frobTwistGL τ L 2 e Q) p).eqLocus (MonoidHom.id _)) ∧
        Function.Injective Θ ∧ (∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ) ∧
        (∀ g r, ρ (Θ g r) = g * ρ r * (g : ModGL τ L)⁻¹) ∧
        ∀ f ∈ F, orderOf f = p →
          ∃ j : ℕ, ¬ p ∣ j ∧ ∀ r, ρ (f r) = (endPowU (frobTwistGL τ L 2 e Q) j) (ρ r)) ∧
      IsSteinbergEnd τ L ((2 ^ e) ^ p) (endPowU (frobTwistGL τ L 2 e Q) p) ∧
      Finite ↥(adjointGroup τ L ⊓ (endPowU (frobTwistGL τ L 2 e Q) p).eqLocus (MonoidHom.id _))

theorem frob_of_equiv
  {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) {p : ℕ} (hp : p.Prime)
    {R : Type} [Group R] (E : R ≃* adjointGroup τ K) (f : MulAut R) (σ : K ≃+* K)
    (hσE : ∀ r, (E (f r) : ModGL τ K) = Units.map (entrywiseHom (σ : K →+* K)) (E r))
    (hfp : orderOf f = p) :
    p ∣ n ∧ ∃ j, ¬ p ∣ j ∧ ∀ r, (E (f r) : ModGL τ K) =
      baseChangeGL (iterateFrobenius K 2 (n / p * j)) (E r) := by
  obtain ⟨σ₀, hσ₀, hord, hzp, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two hn hK
  have hfin₀ : IsOfFinOrder σ₀ := by
    rw [← orderOf_pos_iff, hord]; omega
  obtain ⟨a, ha⟩ : ∃ a : ℕ, σ₀ ^ a = σ := by
    have : σ ∈ Subgroup.zpowers σ₀ := hzp ▸ Subgroup.mem_top σ
    rw [← hfin₀.mem_powers_iff_mem_zpowers] at this
    exact this
  have hσa : ∀ c, σ c = c ^ 2 ^ a := fun c => by rw [← ha, frob_pow_apply σ₀ hσ₀]
  have hfk : ∀ (k : ℕ) (r : R),
      (E ((f ^ k) r) : ModGL τ K) = baseChangeGL (iterateFrobenius K 2 (a * k)) (E r) := by
    intro k
    induction k with
    | zero =>
      intro r
      rw [mul_zero, iterateFrobenius_zero, pow_zero]
      exact (CFSG.LieType.Chevalley.baseChangeGL_id _ _).symm
    | succ k ih =>
      intro r
      rw [pow_succ', MulAut.mul_apply, hσE, ih]
      change baseChangeGL _ (baseChangeGL _ _) = _
      rw [baseChangeGL_baseChangeGL]
      have : (σ : K →+* K).comp (iterateFrobenius K 2 (a * k)) =
          iterateFrobenius K 2 (a * (k + 1)) := by
        ext c
        change σ (iterateFrobenius K 2 (a * k) c) = _
        rw [hσa, iterateFrobenius_def, iterateFrobenius_def, ← pow_mul, ← pow_add, mul_add_one]
      rw [this]
  have hrank : 0 < τ.rank := by cases τ <;> decide
  have hfix : ∀ m, (∀ r, (E ((f ^ m) r) : ModGL τ K) = E r) → n ∣ a * m := by
    intro m hm
    have hc : ∀ c : K, c ^ 2 ^ (a * m) = c := by
      intro c
      have := hm (E.symm ⟨xUnit τ K ⟨0, hrank⟩ c, xUnit_mem_adjointGroup _ c⟩)
      rw [hfk, MulEquiv.apply_symm_apply] at this
      change baseChangeGL _ (xUnit τ K ⟨0, hrank⟩ c) = xUnit τ K ⟨0, hrank⟩ c at this
      rw [baseChangeGL_xUnit] at this
      have := xOp_injective _ (congrArg Units.val this)
      rwa [iterateFrobenius_def] at this
    have : σ₀ ^ (a * m) = 1 := RingEquiv.ext fun c => by
      rw [frob_pow_apply σ₀ hσ₀, hc]; rfl
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one this
  have h1 : n ∣ a * p := hfix p fun r => by
    rw [← hfp, pow_orderOf_eq_one]; rfl
  have h2 : ¬ n ∣ a := by
    intro hna
    have hσ1 : σ₀ ^ a = 1 := orderOf_dvd_iff_pow_eq_one.1 (hord ▸ hna)
    have hid : iterateFrobenius K 2 (a * 1) = RingHom.id K := RingHom.ext fun c => by
      rw [iterateFrobenius_def, mul_one, ← frob_pow_apply σ₀ hσ₀, hσ1]; rfl
    have hf1 : f = 1 := by
      ext r
      apply E.injective
      apply Subtype.ext
      have := hfk 1 r
      rw [pow_one, hid, CFSG.LieType.Chevalley.baseChangeGL_id] at this
      exact this
    rw [hf1, orderOf_one] at hfp
    exact hp.one_lt.ne hfp
  obtain ⟨hpn, j, haj, hpj⟩ := exists_e_j hp (by omega) h1 h2
  refine ⟨hpn, j, hpj, fun r => ?_⟩
  have := hfk 1 r
  rwa [pow_one, mul_one, haj] at this

section Fixed

theorem fixed_eq_map_inndiag
  {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
  {τ : Tag} [IsAlgClosed L] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (hbij : Function.Bijective Fr) :
    adjointGroup τ L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) =
      (inndiagGroup τ K).map (baseChangeGL (algebraMap K L)) := by
  refine le_antisymm (fun g hg => ?_) ?_
  · obtain ⟨hgC, hfix⟩ := hg
    set σ : L ≃+* L := RingEquiv.ofBijective Fr hbij
    have hσ : σ.toRingHom = Fr := RingHom.ext fun _ => rfl
    have hσfix : ∀ c, σ c = c → c ∈ Set.range (algebraMap K L) := fun c hc =>
      CFSG.RankThree.PartOne.KE.mem_range_algebraMap_of_pow_card_eq (by rw [← hFr]; exact hc)
    have hg' : g ∈ entrywiseFixedGroup τ σ := ⟨hgC, by
      change Units.map (entrywiseHom σ.toRingHom) g = g
      rw [hσ]
      exact hfix⟩
    obtain ⟨h, hh, j, hj, rfl⟩ := mem_mul_of_mem_entrywiseFixedGroup hg'
    obtain ⟨hhT, -, hhF⟩ := hh
    obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hhT
    have hbσ : (fun i => Units.map σ.toRingHom.toMonoidHom (b i)) = b := by
      apply rootDiagUnit_injective (τ := τ) (K := L)
      rw [← baseChangeGL_rootDiagUnit, ← units_map_entrywiseHom_eq_baseChangeGL]
      exact hhF
    have hbK : ∀ i, ∃ c : Kˣ, Units.map (algebraMap K L).toMonoidHom c = b i := by
      intro i
      obtain ⟨c, hc⟩ := hσfix (b i : L) (by
        have := congrArg Units.val (congrFun hbσ i)
        simpa using this)
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [map_zero] at hc
        exact (b i).ne_zero hc.symm
      exact ⟨Units.mk0 c hc0, Units.ext (by simpa using hc)⟩
    choose bK hbK using hbK
    have hjK : j ∈ (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) := by
      rw [fixedFieldImage_eq_closure] at hj
      refine (Subgroup.closure_le _).2 ?_ hj
      rintro _ ⟨i, c, hc, rfl | rfl⟩
      · obtain ⟨c', rfl⟩ := hσfix c hc
        exact ⟨xUnit τ K i c', xUnit_mem_adjointGroup i c', baseChangeGL_xUnit _ i c'⟩
      · obtain ⟨c', rfl⟩ := hσfix c hc
        exact ⟨yUnit τ K i c', yUnit_mem_adjointGroup i c', baseChangeGL_yUnit _ i c'⟩
    obtain ⟨jK, hjKC, rfl⟩ := hjK
    have hb : rootDiagUnit τ b = baseChangeGL (algebraMap K L) (rootDiagUnit τ bK) := by
      rw [baseChangeGL_rootDiagUnit]
      congr 1
      funext i
      exact (hbK i).symm
    rw [hb]
    exact ⟨rootDiagUnit τ bK * jK, ⟨bK, jK, hjKC, rfl⟩, map_mul _ _ _⟩
  · rintro _ ⟨w, hw, rfl⟩
    exact ⟨baseChangeGL_mem_adjointGroup_of_mem_inndiag _ hw,
      units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr w⟩

end Fixed

theorem finite_inndiagGroup




   {τ : Tag} {K : Type} [Field K] [Finite K] :
    Finite (inndiagGroup τ K) := by
  haveI : Finite (adjointGroup τ K) := CFSG.LieType.Chevalley.generated_group_finite τ K
  refine Finite.of_surjective (fun x : (Fin τ.rank → Kˣ) × adjointGroup τ K =>
    (⟨rootDiagUnit τ x.1 * x.2, x.1, x.2, x.2.2, rfl⟩ : inndiagGroup τ K)) ?_
  rintro ⟨w, b, j, hj, rfl⟩
  exact ⟨(b, ⟨j, hj⟩), rfl⟩

theorem bridge_model
  {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ} (hp : p.Prime) :
    BridgeConcl τ L p (markIDImage (IsRoot τ) K (adjointGroup τ K))
      (RecipeFieldExcInn.markFieldImage (IsRoot τ) K (adjointGroup τ K)) := by
  classical
  rintro ⟨f, hfF, hfp⟩
  set E : LargeEvenCenterQuot (adjointGroup τ K) ≃* adjointGroup τ K :=
    centerQuotEquivOfBot center_adjointGroup_eq_bot with hEdef
  have hE : ∀ (φ : MulAut (LargeEvenCenterQuot (adjointGroup τ K))) r,
      E (φ r) = autEquiv τ K φ (E r) := by
    intro φ r
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective r
    change E (φ (LargeEvenCenterMk _ h)) = autEquiv τ K φ (E (LargeEvenCenterMk _ h))
    rw [← autEquiv_apply, hEdef, centerQuotEquivOfBot_mk, centerQuotEquivOfBot_mk]
  have hEs : ∀ (α : MulAut (adjointGroup τ K)) r, E ((autEquiv τ K).symm α r) = α (E r) :=
    fun α r => by rw [hE, MulEquiv.apply_symm_apply]
  have hfield : ∀ f' ∈ RecipeFieldExcInn.markFieldImage (IsRoot τ) K (adjointGroup τ K),
      ∃ σ : K ≃+* K, ∀ r, (E (f' r) : ModGL τ K) =
        Units.map (entrywiseHom (σ : K →+* K)) (E r) := by
    intro f' hf'
    obtain ⟨σ, hσ⟩ := autEquiv_eq_entrywise_of_mem_markField hf'
    exact ⟨σ, fun r => by rw [hE, hσ, coe_entrywiseAdjointAut]; rfl⟩
  obtain ⟨σf, hσf⟩ := hfield f hfF
  obtain ⟨hpn, -⟩ := frob_of_equiv hn hK hp E f σf hσf hfp
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
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  let _ : Algebra (ZMod 2) L := ZMod.algebra L 2
  obtain ⟨φ⟩ : Nonempty (K →ₐ[ZMod 2] L) := ⟨IsAlgClosed.lift⟩
  let _ : Algebra K L := φ.toRingHom.toAlgebra
  have hFr : ∀ c : L, iterateFrobenius L 2 (e * p) c = c ^ Nat.card K := fun c => by
    rw [iterateFrobenius_def, hK, hnpe]
  have hbij : Function.Bijective (iterateFrobenius L 2 (e * p)) := by
    rw [← coe_iterateFrobeniusEquiv]; exact (iterateFrobeniusEquiv L 2 (e * p)).bijective
  set Γ := adjointGroup τ L ⊓ (endPowU (frobTwistGL τ L 2 e 1) p).eqLocus (MonoidHom.id _) with hΓ
  have hrat : Γ = (inndiagGroup τ K).map (baseChangeGL (algebraMap K L)) := by
    rw [← fixed_eq_map_inndiag _ hFr hbij]
    ext g
    change g ∈ adjointGroup τ L ∧ endPowU (frobTwistGL τ L 2 e 1) p g = g ↔
      g ∈ adjointGroup τ L ∧ Units.map (entrywiseHom (iterateFrobenius L 2 (e * p))) g = g
    rw [endPow_frobTwist_one]
  let ρ : LargeEvenCenterQuot (adjointGroup τ K) →* ModGL τ L :=
    (baseChangeGL (algebraMap K L)).comp ((adjointGroup τ K).subtype.comp E.toMonoidHom)
  have hρ : ∀ r, ρ r = baseChangeGL (algebraMap K L) (E r) := fun r => rfl
  have hρinj : Function.Injective ρ := fun r r' h =>
    E.injective (Subtype.ext (baseChangeGL_injective (algebraMap K L) h))
  have hρmem : ∀ r, ρ r ∈ Γ := fun r => by
    rw [hrat]; exact ⟨_, adjointGroup_le_inndiagGroup (E r).2, rfl⟩
  have hmemΓ : ∀ w : inndiagGroup τ K, baseChangeGL (algebraMap K L) (w : ModGL τ K) ∈ Γ :=
    fun w => by rw [hrat]; exact ⟨_, w.2, rfl⟩
  let ψ : inndiagGroup τ K ≃* Γ :=
    MulEquiv.ofBijective
      (((baseChangeGL (algebraMap K L)).comp (inndiagGroup τ K).subtype).codRestrict _ hmemΓ)
      ⟨fun w w' h => Subtype.ext (baseChangeGL_injective _ (congrArg Subtype.val h)),
        fun g => by
          have hg : (g : ModGL τ L) ∈ (inndiagGroup τ K).map (baseChangeGL (algebraMap K L)) := by
            rw [← hrat]; exact g.2
          obtain ⟨w, hw, hwg⟩ := hg
          exact ⟨⟨w, hw⟩, Subtype.ext hwg⟩⟩
  have hψs : ∀ g : Γ, baseChangeGL (algebraMap K L) ((ψ.symm g : inndiagGroup τ K) : ModGL τ K) =
      g := fun g => congrArg Subtype.val (ψ.apply_symm_apply g)
  have hinj : Function.Injective (inndiagConj τ K) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    show (w : ModGL τ K) = 1
    refine eq_one_of_commute_adjointGroup hK4 w.2 fun h hh => ?_
    have := congrArg (fun α : MulAut (adjointGroup τ K) => ((α ⟨h, hh⟩ : adjointGroup τ K) :
      ModGL τ K)) (MonoidHom.mem_ker.1 hw)
    simp only [coe_inndiagConj, MulAut.one_apply] at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  let Θ : Γ →* MulAut (LargeEvenCenterQuot (adjointGroup τ K)) :=
    (autEquiv τ K).symm.toMonoidHom.comp ((inndiagConj τ K).comp ψ.symm.toMonoidHom)
  refine ⟨e, 1, he1, Or.inl rfl, ⟨fun g hg => ?_, ρ, Θ, hρinj, hρmem,
    (autEquiv τ K).symm.injective.comp (hinj.comp ψ.symm.injective), ?_, ?_, ?_⟩,
    ⟨iterateFrobenius L 2 (e * p), fun c => by rw [iterateFrobenius_def, pow_mul], 1, Or.inl rfl,
      fun g => ?_⟩, ?_⟩
  · rw [frobTwistGL_apply, one_mul, inv_one, mul_one]
    exact CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup _ hg
  · intro φ'
    constructor
    · intro hφ'
      obtain ⟨w, hw⟩ := exists_inndiagConj_of_mem_markID hφ'
      refine ⟨ψ w, ?_⟩
      show (autEquiv τ K).symm (inndiagConj τ K (ψ.symm (ψ w))) = φ'
      rw [ψ.symm_apply_apply, ← hw, MulEquiv.symm_apply_apply]
    · rintro ⟨g, rfl⟩
      exact inndiagConj_mem_markID _
  · intro g r
    change baseChangeGL (algebraMap K L)
      ((E ((autEquiv τ K).symm (inndiagConj τ K (ψ.symm g)) r) : adjointGroup τ K) : ModGL τ K) = _
    rw [hEs, coe_inndiagConj, map_mul, map_mul, map_inv, hψs]
    rfl
  · intro f' hf' hf'p
    obtain ⟨σ', hσ'⟩ := hfield f' hf'
    obtain ⟨-, j, hpj, hj⟩ := frob_of_equiv hn hK hp E f' σ' hσ' hf'p
    refine ⟨j, hpj, fun r => ?_⟩
    rw [hρ, hρ, hj, baseChangeGL_baseChangeGL, endPow_frobTwist_one]
    change _ = baseChangeGL _ (baseChangeGL (algebraMap K L) _)
    rw [baseChangeGL_baseChangeGL]
    have hc : (algebraMap K L).comp (iterateFrobenius K 2 (e * j)) =
        (iterateFrobenius L 2 (e * j)).comp (algebraMap K L) := by
      ext c
      simp only [RingHom.comp_apply, iterateFrobenius_def, map_pow]
    rw [hc]
  · rw [endPow_frobTwist_one, one_mul, inv_one, mul_one]
  · change Finite Γ
    rw [hrat]
    haveI : Finite (inndiagGroup τ K) := finite_inndiagGroup
    exact Finite.of_surjective _ (MonoidHom.subgroupMap_surjective
      (baseChangeGL (algebraMap K L)) (inndiagGroup τ K))

theorem bridge_chev
  {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ} (hp : p.Prime) :
    BridgeConcl τ L p (LargeEvenChevIDImage τ.cartan K (LargeEvenChevH τ.cartan K false))
      (LargeEvenChevFieldImage τ.cartan K (LargeEvenChevH τ.cartan K false)) := by
  have h1 : ∀ S : (Fin τ.rank → ℤ) → Prop, S = IsRoot τ →
      BridgeConcl τ L p (markIDImage S K (MarkChev.chevH τ.cartan S K false))
        (RecipeFieldExcInn.markFieldImage S K (MarkChev.chevH τ.cartan S K false)) := by
    intro S hS
    subst hS
    suffices key : ∀ H : Subgroup (MarkChev.GLS (IsRoot τ) K), H = adjointGroup τ K →
        BridgeConcl τ L p (markIDImage (IsRoot τ) K H)
          (RecipeFieldExcInn.markFieldImage (IsRoot τ) K H) from
      key _ (chevH_false_eq_adjointGroup K τ)
    intro H hH
    subst hH
    exact bridge_model hn hK L hp
  have h2 := h1 _ (largeEvenIsRoot_eq_isRoot τ)
  suffices key : ∀ H : Subgroup (LargeEvenChevGL τ.cartan K),
      H = MarkChev.chevH τ.cartan (LargeEvenIsRoot τ.cartan) K false →
      BridgeConcl τ L p (LargeEvenChevIDImage τ.cartan K H) (LargeEvenChevFieldImage τ.cartan K H)
    from key _ (largeEvenChevH_eq τ.cartan K false)
  intro H hH
  subst hH
  rw [largeEvenChevIDImage_eq]
  exact h2

end

end CFSG.HardMathSupport.C14ExcBridgeE6
