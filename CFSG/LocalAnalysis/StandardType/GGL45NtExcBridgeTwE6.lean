module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeE6
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangTwisted
public import CFSG.LieType.Chevalley.EvenDiagramFixedAmbientCentralizer

public section

namespace CFSG.HardMathSupport.C14ExcBridgeTwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType CFSG.Assembly
  CFSG.StandardType.RecipeExcLang CFSG.HardMathSupport.C14ExcBridgeU CFSG.HardMathSupport.C14ExcBridgeE6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Torality

noncomputable section

theorem endPow_frobTwist_of_fixed
    {τ : Tag} {L : Type} [Field L] [CharP L 2] (e m : ℕ)
    {Q : ModGL τ L} (hQ : Units.map (entrywiseHom (iterateFrobenius L 2 e)) Q = Q)
    (g : ModGL τ L) :
    endPowU (frobTwistGL τ L 2 e Q) m g =
      Q ^ m * Units.map (entrywiseHom (iterateFrobenius L 2 (e * m))) g * (Q ^ m)⁻¹ := by
  induction m with
  | zero =>
    rw [mul_zero, endPow_zero', pow_zero, one_mul, inv_one, mul_one]
    ext : 1
    change _ = entrywise _ _
    rw [iterateFrobenius_zero, entrywise_id]
  | succ m ih =>
    rw [endPow_succ', ih, frobTwistGL_apply]
    change Q * baseChangeGL _ (Q ^ m * baseChangeGL _ g * (Q ^ m)⁻¹) * Q⁻¹ = _
    have hQe : baseChangeGL (iterateFrobenius L 2 e) Q = Q := hQ
    rw [map_mul, map_mul, map_inv, map_pow, hQe, baseChangeGL_baseChangeGL, iterateFrobenius_comp,
      show e + e * m = e * (m + 1) by ring, pow_succ']
    change _ = Q * Q ^ m * baseChangeGL _ g * (Q * Q ^ m)⁻¹
    group

theorem twInndiag_le_inndiag
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) :
    twInndiagGroup K σ ≤ inndiagGroup TwistTag.E6.tag K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (hc | ⟨b, -, rfl⟩)
  · exact adjointGroup_le_inndiagGroup (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom hc).1
  · exact rootDiagUnit_mem_inndiagGroup b

theorem conj_eq_iff






    {G : Type*} [Group G] {P x y : G} : P * x * P⁻¹ = y ↔ x = P⁻¹ * y * P := by
  constructor
  · rintro rfl; group
  · rintro rfl; group

theorem twisted_fixed_eq_map
    {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n)) {L : Type} [Field L] [IsAlgClosed L]
    [Algebra K L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ (2 ^ n)) :
    twistedFixedGroup TwistTag.E6 L Fr =
      (twInndiagGroup K σ).map (baseChangeGL (algebraMap K L)) := by
  classical
  have hK2 : Nat.card K = 2 ^ (n * 2) := by rw [hK, ← pow_mul]
  haveI : CharP K 2 := charP_two_of_card hK2
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) :=
    RingHom.ext fun c => by
      simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hσ, hFr,
        map_pow]
  set P := diagramMap TwistTag.E6 L with hPdef
  have hP2 : P ^ 2 = 1 := diagramMap_pow_order TwistTag.E6 L
  have hPinv : P⁻¹ = P := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, hP2]
  refine le_antisymm (fun g hg => ?_) ?_
  · obtain ⟨hgC, hgF⟩ := hg
    have h1 : P * Units.map (entrywiseHom Fr) g * P⁻¹ = g := hgF
    have hPF : Units.map (entrywiseHom Fr) P = P := units_map_entrywiseHom_diagramMap (σ := Fr)
    have h3 : P * Units.map (entrywiseHom (Fr.comp Fr)) g * P⁻¹ = Units.map (entrywiseHom Fr) g := by
      have := congrArg (Units.map (entrywiseHom Fr)) h1
      rwa [map_mul, map_mul, map_inv, hPF, units_map_entrywiseHom_comp] at this
    have hPP : P * P = 1 := by rw [← pow_two, hP2]
    have h2 : Units.map (entrywiseHom (Fr.comp Fr)) g = g := by
      rw [conj_eq_iff.1 h3, conj_eq_iff.1 h1, hPinv,
        show P * (P * g * P) * P = (P * P) * g * (P * P) by group, hPP, one_mul, mul_one]
    have hFr2 : ∀ c, (Fr.comp Fr) c = c ^ Nat.card K := fun c => by
      rw [RingHom.comp_apply, hFr, hFr, ← pow_mul, hK, ← pow_two]
    have hbij : Function.Bijective (Fr.comp Fr) := by
      have hsurj : Function.Surjective Fr := fun y => by
        obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq y (pow_pos (by norm_num : 0 < 2) n)
        exact ⟨z, by rw [hFr, hz]⟩
      exact ⟨Fr.injective.comp Fr.injective, hsurj.comp hsurj⟩
    have hg' : g ∈ (inndiagGroup TwistTag.E6.tag K).map (baseChangeGL (algebraMap K L)) := by
      rw [← fixed_eq_map_inndiag _ hFr2 hbij]
      exact ⟨hgC, h2⟩
    obtain ⟨w, hw, rfl⟩ := hg'
    have hwF : twistHom TwistTag.E6 K σ.toRingHom w = w := by
      apply baseChangeGL_injective (algebraMap K L)
      rw [← twistHom_baseChangeGL (algebraMap K L) hcomm]
      exact hgF
    set L' := AlgebraicClosure K
    haveI : CharP L' 2 := charP_of_injective_algebraMap (algebraMap K L').injective 2
    have hcomm' : (algebraMap K L').comp σ.toRingHom =
        (iterateFrobenius L' 2 n).comp (algebraMap K L') :=
      RingHom.ext fun c => by
        simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hσ,
          iterateFrobenius_def, map_pow]
    obtain ⟨w', hw', hww'⟩ := exists_mem_twInndiag_of_twist_fixed hn hK hσ
      (L := L') (Fr := iterateFrobenius L' 2 n) (fun c => by rw [iterateFrobenius_def])
      (baseChangeGL_mem_adjointGroup_of_mem_inndiag _ hw)
      (by rw [twistHom_baseChangeGL (algebraMap K L') hcomm', hwF])
    rw [baseChangeGL_injective _ hww'] at hw'
    exact ⟨w, hw', rfl⟩
  · rintro _ ⟨w, hw, rfl⟩
    refine ⟨baseChangeGL_mem_adjointGroup_of_mem_inndiag _ (twInndiag_le_inndiag σ hw), ?_⟩
    change twistHom TwistTag.E6 L Fr (baseChangeGL (algebraMap K L) w) = _
    rw [twistHom_baseChangeGL (algebraMap K L) hcomm, twistHom_eq_of_mem_twInndiag hw]
    rfl

theorem congr_conj






    {G H : Type*} [Group G] [Group H] (e : G ≃* H) (g : G) :
    MulAut.congr e (MulAut.conj g) = MulAut.conj (e g) :=
  MulEquiv.ext fun y => by
    show e (g * e.symm y * g⁻¹) = e g * y * (e g)⁻¹
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem markID_subset_range
    {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hq3 : 3 ≤ 2 ^ n)
    {φ : MulAut (LargeEvenCenterQuot (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))}
    (hφ : φ ∈ markIDImage (IsRoot TwistTag.E6.tag) K
      (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) :
    ∃ w : twInndiagGroup K σ,
      MulAut.congr (centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ)) φ =
        twConj K σ w := by
  classical
  have hK2 : Nat.card K = 2 ^ (n * 2) := by rw [hK, ← pow_mul]
  haveI : CharP K 2 := charP_two_of_card hK2
  set C₀ := graphFixedRootGroup TwistTag.E6 K σ.toRingHom with hC₀
  set E : LargeEvenCenterQuot C₀ ≃* C₀ :=
    centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ) with hEdef
  set L' := AlgebraicClosure K
  haveI : CharP L' 2 := charP_of_injective_algebraMap (algebraMap K L').injective 2
  set ι := algebraMap K L'
  set Fr := iterateFrobenius L' 2 n
  have hcomm : ι.comp σ.toRingHom = Fr.comp ι :=
    RingHom.ext fun c => by
      simp only [ι, Fr, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hσ,
        iterateFrobenius_def, map_pow]
  obtain ⟨-, -, hC, -⟩ := diagram_fixed_ambient_centralizer_trivial_of_three_le TwistTag.E6
    Nat.prime_two hn hq3 K hK σ.toRingHom hσ L' ι
  have hle : Subgroup.closure (LargeEvenInnSet _ ∪ markDiagImage (IsRoot TwistTag.E6.tag) K C₀) ≤
      (twConj K σ).range.comap (MulAut.congr E).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro φ (⟨x, rfl⟩ | ⟨a, ha1, -, hG⟩)
    · refine ⟨⟨E x, graphFixedRootGroup_le_twInndiag σ (E x).2⟩, ?_⟩
      exact (twConj_of_mem_C0 σ (E x)).trans (congr_conj E x).symm
    · set d := rootDiagUnit TwistTag.E6.tag a with hd
      have hN : ∀ c ∈ C₀, d * c * d⁻¹ ∈ C₀ := fun c hc => by
        obtain ⟨h', hh'⟩ := ha1 ⟨c, hc⟩
        have := (markDiag_rel_iff a _ _).1 hh'
        rw [← this]; exact h'.2
      have hdI : d ∈ inndiagGroup TwistTag.E6.tag K := rootDiagUnit_mem_inndiagGroup a
      set D := baseChangeGL ι d with hD
      have hDC : D ∈ adjointGroup TwistTag.E6.tag L' :=
        baseChangeGL_mem_adjointGroup_of_mem_inndiag _ hdI
      have hΦD : twistHom TwistTag.E6 L' Fr D = baseChangeGL ι (twistHom TwistTag.E6 K σ.toRingHom d) :=
        twistHom_baseChangeGL ι hcomm d
      have hΦDC : twistHom TwistTag.E6 L' Fr D ∈ adjointGroup TwistTag.E6.tag L' := by
        rw [hΦD, hd, twistHom_rootDiagUnit_eq]
        exact baseChangeGL_mem_adjointGroup_of_mem_inndiag _ (rootDiagUnit_mem_inndiagGroup _)
      have hfixC : ∀ c ∈ C₀, twistHom TwistTag.E6 L' Fr (baseChangeGL ι c) = baseChangeGL ι c :=
        fun c hc => by
          rw [twistHom_baseChangeGL ι hcomm, (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom hc).2]
          rfl
      have hz : D⁻¹ * twistHom TwistTag.E6 L' Fr D = 1 := by
        refine hC _ (mul_mem (inv_mem hDC) hΦDC) fun h hh => ?_
        obtain ⟨c, hc, rfl⟩ := hh
        have e1 := hfixC _ (hN c hc)
        simp only [map_mul, map_inv] at e1
        rw [hfixC c hc] at e1
        change twistHom TwistTag.E6 L' Fr D * baseChangeGL ι c * (twistHom TwistTag.E6 L' Fr D)⁻¹ =
          D * baseChangeGL ι c * D⁻¹ at e1
        calc D⁻¹ * twistHom TwistTag.E6 L' Fr D * baseChangeGL ι c
            = D⁻¹ * (twistHom TwistTag.E6 L' Fr D * baseChangeGL ι c *
                (twistHom TwistTag.E6 L' Fr D)⁻¹) * twistHom TwistTag.E6 L' Fr D := by group
          _ = baseChangeGL ι c * (D⁻¹ * twistHom TwistTag.E6 L' Fr D) := by rw [e1]; group
      have hΦ : twistHom TwistTag.E6 L' Fr D = D := by
        rw [inv_mul_eq_one] at hz; exact hz.symm
      obtain ⟨w', hw', hww'⟩ := exists_mem_twInndiag_of_twist_fixed hn hK hσ (L := L') (Fr := Fr)
        (fun c => by rw [iterateFrobenius_def]) hDC hΦ
      have hdw : w' = d := baseChangeGL_injective ι hww'
      rw [hdw] at hw'
      refine ⟨⟨d, hw'⟩, MulEquiv.ext fun c => Subtype.ext ?_⟩
      rw [coe_twConj]
      change (d * (c : ModGL TwistTag.E6.tag K) * d⁻¹) = (E (φ (E.symm c)) : ModGL TwistTag.E6.tag K)
      obtain ⟨h', hh'⟩ := ha1 c
      rw [hEdef, centerQuotEquivOfBot_symm, hG c h' hh', centerQuotEquivOfBot_mk]
      exact ((markDiag_rel_iff a _ _).1 hh').symm
  obtain ⟨w, hw⟩ := hle hφ
  exact ⟨w, hw.symm⟩

theorem field_of_order
    {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {R : Type} [Group R] (E : R ≃* graphFixedRootGroup TwistTag.E6 K σ.toRingHom)
    (f : MulAut R) (δ : K ≃+* K) (hfδ : MulAut.congr E f = fieldActor σ δ)
    (hfp : orderOf f = p) :
    p ∣ n ∧ ∃ j, ¬ p ∣ j ∧ ∀ c, δ c = c ^ 2 ^ (2 * (n / p) * j) := by
  have hK2 : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, -⟩, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hn K hK σ hσ
  have hΘfa : ∀ δ', Θ (fieldActor σ δ') = δ' := fun δ' =>
    hΘ _ 1 1 δ' (by rw [map_one, map_one, one_mul, one_mul])
  have hinj : Function.Injective (fieldActorHom (t := TwistTag.E6) σ) := fun δ₁ δ₂ h => by
    rw [← hΘfa δ₁, ← hΘfa δ₂]
    exact congrArg Θ h
  have hord : orderOf δ = p := by
    rw [← hfp, ← orderOf_injective (MulAut.congr E).toMonoidHom (MulAut.congr E).injective f,
      ← orderOf_injective _ hinj δ]
    exact congrArg orderOf hfδ.symm
  obtain ⟨σ₀, hσ₀, hordσ₀, hzp, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 2 * n) hK2
  have hfin₀ : IsOfFinOrder σ₀ := by
    rw [← orderOf_pos_iff, hordσ₀]; omega
  obtain ⟨a, ha⟩ : ∃ a : ℕ, σ₀ ^ a = δ := by
    have : δ ∈ Subgroup.zpowers σ₀ := hzp ▸ Subgroup.mem_top δ
    rw [← hfin₀.mem_powers_iff_mem_zpowers] at this
    exact this
  have h1 : 2 * n ∣ a * p := by
    rw [← hordσ₀]
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, ha, ← hord, pow_orderOf_eq_one]
  have h2 : ¬ 2 * n ∣ a := by
    intro h
    have : δ = 1 := by
      rw [← ha]; exact orderOf_dvd_iff_pow_eq_one.1 (hordσ₀ ▸ h)
    rw [this, orderOf_one] at hord
    exact hp.one_lt.ne hord
  obtain ⟨hp2n, j, haj, hpj⟩ := exists_e_j hp (by omega) h1 h2
  have hpn : p ∣ n :=
    Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hp Nat.prime_two).2 hp2) hp2n
  refine ⟨hpn, j, hpj, fun c => ?_⟩
  rw [← ha, frob_pow_apply σ₀ hσ₀, haj, Nat.mul_div_assoc 2 hpn]

theorem bridge_twE6_model
    {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    BridgeConcl TwistTag.E6.tag L p
      (markIDImage (IsRoot TwistTag.E6.tag) K (graphFixedRootGroup TwistTag.E6 K σ.toRingHom))
      (RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.E6.tag) K
        (graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) := by
  classical
  have hK2 : Nat.card K = 2 ^ (n * 2) := by rw [hK, ← pow_mul]
  haveI : CharP K 2 := charP_two_of_card hK2
  set C₀ := graphFixedRootGroup TwistTag.E6 K σ.toRingHom with hC₀
  set E : LargeEvenCenterQuot C₀ ≃* C₀ :=
    centerQuotEquivOfBot (exceptional_fixed_center_trivial TwistTag.E6 K σ) with hEdef
  rintro ⟨f, hfF, hfp⟩
  have hE : ∀ (φ : MulAut (LargeEvenCenterQuot C₀)) r, E (φ r) = MulAut.congr E φ (E r) :=
    fun φ r => by
      show E (φ r) = E (φ (E.symm (E r)))
      rw [E.symm_apply_apply]
  have hEs : ∀ (α : MulAut C₀) r, E ((MulAut.congr E).symm α r) = α (E r) :=
    fun α r => by rw [hE, MulEquiv.apply_symm_apply]
  obtain ⟨-, -, -, -, -, -, hfield, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hn K hK σ hσ
  have hfieldE : ∀ f' ∈ RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.E6.tag) K C₀,
      ∃ δ : K ≃+* K, MulAut.congr E f' = fieldActor σ δ := by
    rintro f' ⟨δ, hG⟩
    refine ⟨δ, MulEquiv.ext fun c => ?_⟩
    show E (f' (E.symm c)) = fieldActor σ δ c
    rw [hEdef, centerQuotEquivOfBot_symm, hG c (fieldActor σ δ c) (by
      show (((fieldActor σ δ c : C₀) : ModGL TwistTag.E6.tag K) :
        Module.End K (RootModule TwistTag.E6.tag K)) = _
      rw [hfield]
      rfl), centerQuotEquivOfBot_mk]
  have hfrob : ∀ f' ∈ RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.E6.tag) K C₀,
      orderOf f' = p → p ∣ n ∧ ∃ j, ¬ p ∣ j ∧ ∀ r, (E (f' r) : ModGL TwistTag.E6.tag K) =
        baseChangeGL (iterateFrobenius K 2 (2 * (n / p) * j)) (E r) := by
    intro f' hf' hf'p
    obtain ⟨δ, hδ⟩ := hfieldE f' hf'
    obtain ⟨hpn, j, hpj, hδj⟩ := field_of_order hn hK σ hσ hp hp2 E f' δ hδ hf'p
    refine ⟨hpn, j, hpj, fun r => ?_⟩
    rw [hE, hδ, hfield]
    have : δ.toRingHom = iterateFrobenius K 2 (2 * (n / p) * j) :=
      RingHom.ext fun c => by rw [iterateFrobenius_def]; exact hδj c
    rw [this]
    rfl
  obtain ⟨hpn, -⟩ := hfrob f hfF hfp
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
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  let _ : Algebra (ZMod 2) L := ZMod.algebra L 2
  obtain ⟨φ⟩ : Nonempty (K →ₐ[ZMod 2] L) := ⟨IsAlgClosed.lift⟩
  let _ : Algebra K L := φ.toRingHom.toAlgebra
  set ι := algebraMap K L
  set P := diagramMap TwistTag.E6 L with hPdef
  have hP2 : P ^ 2 = 1 := diagramMap_pow_order TwistTag.E6 L
  have hPfix : ∀ k, Units.map (entrywiseHom (iterateFrobenius L 2 k)) P = P := fun k =>
    units_map_entrywiseHom_diagramMap (σ := iterateFrobenius L 2 k)
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have hPp : P ^ p = P := by rw [hk, pow_succ, pow_mul, hP2, one_pow, one_mul]
  have hΦ : ∀ g, endPowU (frobTwistGL TwistTag.E6.tag L 2 e P) p g =
      twistHom TwistTag.E6 L (iterateFrobenius L 2 n) g := fun g => by
    rw [endPow_frobTwist_of_fixed e p (hPfix e), hPp, ← hnpe, twistHom_apply]
  set Γ := adjointGroup TwistTag.E6.tag L ⊓
    (endPowU (frobTwistGL TwistTag.E6.tag L 2 e P) p).eqLocus (MonoidHom.id _) with hΓ
  have hrat : Γ = (twInndiagGroup K σ).map (baseChangeGL ι) := by
    rw [← twisted_fixed_eq_map hn hK σ hσ (iterateFrobenius L 2 n)
      (fun c => by rw [iterateFrobenius_def])]
    ext g
    change g ∈ adjointGroup TwistTag.E6.tag L ∧ endPowU _ p g = g ↔
      g ∈ adjointGroup TwistTag.E6.tag L ∧ twistHom TwistTag.E6 L (iterateFrobenius L 2 n) g = g
    rw [hΦ]
  let ρ : LargeEvenCenterQuot C₀ →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL ι).comp (C₀.subtype.comp E.toMonoidHom)
  have hρ : ∀ r, ρ r = baseChangeGL ι (E r) := fun r => rfl
  have hρinj : Function.Injective ρ := fun r r' h =>
    E.injective (Subtype.ext (baseChangeGL_injective ι h))
  have hρmem : ∀ r, ρ r ∈ Γ := fun r => by
    rw [hrat]; exact ⟨_, graphFixedRootGroup_le_twInndiag σ (E r).2, rfl⟩
  have hmemΓ : ∀ w : twInndiagGroup K σ, baseChangeGL ι (w : ModGL TwistTag.E6.tag K) ∈ Γ :=
    fun w => by rw [hrat]; exact ⟨_, w.2, rfl⟩
  let ψ : twInndiagGroup K σ ≃* Γ :=
    MulEquiv.ofBijective
      (((baseChangeGL ι).comp (twInndiagGroup K σ).subtype).codRestrict _ hmemΓ)
      ⟨fun w w' h => Subtype.ext (baseChangeGL_injective _ (congrArg Subtype.val h)),
        fun g => by
          have hg : (g : ModGL TwistTag.E6.tag L) ∈ (twInndiagGroup K σ).map (baseChangeGL ι) := by
            rw [← hrat]; exact g.2
          obtain ⟨w, hw, hwg⟩ := hg
          exact ⟨⟨w, hw⟩, Subtype.ext hwg⟩⟩
  have hψs : ∀ g : Γ, baseChangeGL ι ((ψ.symm g : twInndiagGroup K σ) : ModGL TwistTag.E6.tag K) =
      g := fun g => congrArg Subtype.val (ψ.apply_symm_apply g)
  have hinj : Function.Injective (twConj K σ) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro w hw
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    show (w : ModGL TwistTag.E6.tag K) = 1
    refine eq_one_of_commute_C0 hn hK hσ hq3 w.2 fun c hc => ?_
    have := congrArg (fun α : MulAut C₀ => ((α ⟨c, hc⟩ : C₀) : ModGL TwistTag.E6.tag K))
      (MonoidHom.mem_ker.1 hw)
    change (w : ModGL TwistTag.E6.tag K) * c * (w : ModGL TwistTag.E6.tag K)⁻¹ = c at this
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  let Θ : Γ →* MulAut (LargeEvenCenterQuot C₀) :=
    (MulAut.congr E).symm.toMonoidHom.comp ((twConj K σ).comp ψ.symm.toMonoidHom)
  have hD : IsDiagramTwistMatrix TwistTag.E6.tag L P :=
    Or.inr ⟨TwistTag.E6, 1, rfl, by rw [zpow_one]⟩
  refine ⟨e, P, he1, hD, ⟨fun g hg => ?_, ρ, Θ, hρinj, hρmem,
    (MulAut.congr E).symm.injective.comp (hinj.comp ψ.symm.injective), ?_, ?_, ?_⟩,
    ⟨iterateFrobenius L 2 (e * p), fun c => by rw [iterateFrobenius_def, pow_mul], P,
      Or.inr ⟨TwistTag.E6, rfl, rfl⟩, fun g => ?_⟩, ?_⟩
  · rw [frobTwistGL_apply, ← hD.map_conj_eq]
    exact ⟨_, entrywiseFrobGL_mem 2 e hg, rfl⟩
  · intro φ'
    constructor
    · intro hφ'
      obtain ⟨w, hw⟩ := markID_subset_range hn hK σ hσ hq3 hφ'
      refine ⟨ψ w, ?_⟩
      show (MulAut.congr E).symm (twConj K σ (ψ.symm (ψ w))) = φ'
      rw [ψ.symm_apply_apply, ← hw, MulEquiv.symm_apply_apply]
    · rintro ⟨g, rfl⟩
      exact twConj_mem_markID hn hK σ hσ _
  · intro g r
    change baseChangeGL ι
      ((E ((MulAut.congr E).symm (twConj K σ (ψ.symm g)) r) : C₀) : ModGL TwistTag.E6.tag K) = _
    rw [hEs, coe_twConj, map_mul, map_mul, map_inv, hψs]
    rfl
  · intro f' hf' hf'p
    obtain ⟨-, j, hpj, hj⟩ := hfrob f' hf' hf'p
    refine ⟨2 * j, fun h => ?_, fun r => ?_⟩
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
      · exact hpj h
    rw [hρ, hρ, hj, baseChangeGL_baseChangeGL, endPow_frobTwist_of_fixed e (2 * j) (hPfix e),
      pow_mul, hP2, one_pow, one_mul, inv_one, mul_one]
    change _ = baseChangeGL _ (baseChangeGL ι _)
    rw [baseChangeGL_baseChangeGL]
    have hc : ι.comp (iterateFrobenius K 2 (2 * e * j)) =
        (iterateFrobenius L 2 (e * (2 * j))).comp ι := by
      ext c
      simp only [RingHom.comp_apply, iterateFrobenius_def, map_pow]
      ring_nf
    rw [hc]
  · rw [hΦ, twistHom_apply, ← hnpe]
  · change Finite Γ
    rw [hrat]
    haveI : Finite (inndiagGroup TwistTag.E6.tag K) := finite_inndiagGroup
    haveI : Finite (twInndiagGroup K σ) :=
      Finite.of_injective _ (Subgroup.inclusion_injective (twInndiag_le_inndiag σ))
    exact Finite.of_surjective _ (MonoidHom.subgroupMap_surjective
      (baseChangeGL ι) (twInndiagGroup K σ))

theorem bridge_twE6_chev
    {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    BridgeConcl TwistTag.E6.tag L p
      (LargeEvenChevIDImage TwistTag.E6.tag.cartan K
        (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n))
      (LargeEvenChevFieldImage TwistTag.E6.tag.cartan K
        (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n)) := by
  have hK2 : Nat.card K = 2 ^ (n * 2) := by rw [hK, ← pow_mul]
  haveI : CharP K 2 := charP_two_of_card hK2
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hperf, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hn K hK σ hσ
  have hH : MarkChev.twistedH TwistTag.E6.tag.cartan (IsRoot TwistTag.E6.tag) K
      TwistTag.E6.perm n = graphFixedRootGroup TwistTag.E6 K σ.toRingHom :=
    (twistedH_eq_commutator K TwistTag.E6 n σ.toRingHom hσ).trans hperf
  have h1 : ∀ S : (Fin TwistTag.E6.tag.rank → ℤ) → Prop, S = IsRoot TwistTag.E6.tag →
      BridgeConcl TwistTag.E6.tag L p
        (markIDImage S K (MarkChev.twistedH TwistTag.E6.tag.cartan S K TwistTag.E6.perm n))
        (RecipeFieldExcInn.markFieldImage S K
          (MarkChev.twistedH TwistTag.E6.tag.cartan S K TwistTag.E6.perm n)) := by
    intro S hS
    subst hS
    suffices key : ∀ H : Subgroup (MarkChev.GLS (IsRoot TwistTag.E6.tag) K),
        H = graphFixedRootGroup TwistTag.E6 K σ.toRingHom →
        BridgeConcl TwistTag.E6.tag L p (markIDImage (IsRoot TwistTag.E6.tag) K H)
          (RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.E6.tag) K H) from key _ hH
    intro H hH'
    subst hH'
    exact bridge_twE6_model hn hK σ hσ L hp hp2
  have h2 := h1 _ (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag)
  suffices key : ∀ H : Subgroup (LargeEvenChevGL TwistTag.E6.tag.cartan K),
      H = MarkChev.twistedH TwistTag.E6.tag.cartan (LargeEvenIsRoot TwistTag.E6.tag.cartan) K
        TwistTag.E6.perm n →
      BridgeConcl TwistTag.E6.tag L p (LargeEvenChevIDImage TwistTag.E6.tag.cartan K H)
        (LargeEvenChevFieldImage TwistTag.E6.tag.cartan K H) from
    key _ (largeEvenTwistedH_eq _ K _ n)
  intro H hH
  subst hH
  rw [largeEvenChevIDImage_eq]
  exact h2

end

end CFSG.HardMathSupport.C14ExcBridgeTwE6
