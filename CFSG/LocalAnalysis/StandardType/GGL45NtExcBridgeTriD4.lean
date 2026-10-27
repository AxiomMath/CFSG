module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeTwE6
public import CFSG.LieType.Chevalley.TrialityFullAmbientFixedGroup
public import CFSG.LieType.Chevalley.EvenTrialityAutomorphismNormalForm
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTriDiag

public section

namespace CFSG.HardMathSupport.C14ExcBridgeTriD4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType CFSG.Assembly
  CFSG.StandardType.RecipeExcLang CFSG.HardMathSupport.C14ExcBridgeU CFSG.HardMathSupport.C14ExcBridgeE6
  CFSG.HardMathSupport.C14ExcBridgeTwE6
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Torality

noncomputable section

theorem field_of_order_D4
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n)) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    {R : Type} [Group R] (E : R ≃* graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (f : MulAut R) (δ : K ≃+* K) (hfδ : MulAut.congr E f = fieldActor σ δ)
    (hfp : orderOf f = p) :
    p ∣ n ∧ ∃ j, ¬ p ∣ j ∧ ∀ c, δ c = c ^ 2 ^ (3 * (n / p) * j) := by
  have hK3 : Nat.card K = 2 ^ (3 * n) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨-, -, ⟨Θ, hΘ, -⟩, -⟩ := even_triality_exact_automorphism_normal_form hn K hK σ hσ
  have hΘfa : ∀ δ', Θ (fieldActor σ δ') = δ' := fun δ' =>
    hΘ _ 1 δ' (by rw [map_one, one_mul])
  have hinj : Function.Injective (fieldActorHom (t := TwistTag.D4) σ) := fun δ₁ δ₂ h => by
    rw [← hΘfa δ₁, ← hΘfa δ₂]
    exact congrArg Θ h
  have hord : orderOf δ = p := by
    rw [← hfp, ← orderOf_injective (MulAut.congr E).toMonoidHom (MulAut.congr E).injective f,
      ← orderOf_injective _ hinj δ]
    exact congrArg orderOf hfδ.symm
  obtain ⟨σ₀, hσ₀, hordσ₀, hzp, -, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_two (by omega : 1 ≤ 3 * n) hK3
  have hfin₀ : IsOfFinOrder σ₀ := by
    rw [← orderOf_pos_iff, hordσ₀]; omega
  obtain ⟨a, ha⟩ : ∃ a : ℕ, σ₀ ^ a = δ := by
    have : δ ∈ Subgroup.zpowers σ₀ := hzp ▸ Subgroup.mem_top δ
    rw [← hfin₀.mem_powers_iff_mem_zpowers] at this
    exact this
  have h1 : 3 * n ∣ a * p := by
    rw [← hordσ₀]
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_mul, ha, ← hord, pow_orderOf_eq_one]
  have h2 : ¬ 3 * n ∣ a := by
    intro h
    have : δ = 1 := by
      rw [← ha]; exact orderOf_dvd_iff_pow_eq_one.1 (hordσ₀ ▸ h)
    rw [this, orderOf_one] at hord
    exact hp.one_lt.ne hord
  obtain ⟨hp3n, j, haj, hpj⟩ := exists_e_j hp (by omega) h1 h2
  have hpn : p ∣ n :=
    Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hp Nat.prime_three).2 hp3) hp3n
  refine ⟨hpn, j, hpj, fun c => ?_⟩
  rw [← ha, frob_pow_apply σ₀ hσ₀, haj, Nat.mul_div_assoc 3 hpn]

theorem mul_mod_three






    {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) : p % 3 * p % 3 = 1 := by
  have h3 : ¬ 3 ∣ p := fun h => hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h).symm
  have : p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases this with h | h <;> rw [Nat.mul_mod, h] <;> norm_num [h]

theorem bridge_triD4_model
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ n))
    (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hI : markIDImage (IsRoot TwistTag.D4.tag) K (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ⊆
      LargeEvenInnSet _) :
    BridgeConcl TwistTag.D4.tag L p
      (markIDImage (IsRoot TwistTag.D4.tag) K (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      (RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.D4.tag) K
        (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  classical
  have hK3 : Nat.card K = 2 ^ (n * 3) := by rw [hK, ← pow_mul]
  haveI : CharP K 2 := charP_two_of_card hK3
  set C₀ := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC₀
  have hZ : Subgroup.center C₀ = ⊥ := exceptional_fixed_center_trivial TwistTag.D4 K σ
  set E : LargeEvenCenterQuot C₀ ≃* C₀ := centerQuotEquivOfBot hZ with hEdef
  rintro ⟨f, hfF, hfp⟩
  have hE : ∀ (φ : MulAut (LargeEvenCenterQuot C₀)) r, E (φ r) = MulAut.congr E φ (E r) :=
    fun φ r => by
      show E (φ r) = E (φ (E.symm (E r)))
      rw [E.symm_apply_apply]
  have hEs : ∀ (α : MulAut C₀) r, E ((MulAut.congr E).symm α r) = α (E r) :=
    fun α r => by rw [hE, MulEquiv.apply_symm_apply]
  obtain ⟨hfield, -⟩ := even_triality_exact_automorphism_normal_form hn K hK σ hσ
  have hfieldE : ∀ f' ∈ RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.D4.tag) K C₀,
      ∃ δ : K ≃+* K, MulAut.congr E f' = fieldActor σ δ := by
    rintro f' ⟨δ, hG⟩
    refine ⟨δ, MulEquiv.ext fun c => ?_⟩
    show E (f' (E.symm c)) = fieldActor σ δ c
    rw [hEdef, centerQuotEquivOfBot_symm, hG c (fieldActor σ δ c) (by
      show (((fieldActor σ δ c : C₀) : ModGL TwistTag.D4.tag K) :
        Module.End K (RootModule TwistTag.D4.tag K)) = _
      rw [hfield]
      rfl), centerQuotEquivOfBot_mk]
  have hfrob : ∀ f' ∈ RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.D4.tag) K C₀,
      orderOf f' = p → p ∣ n ∧ ∃ j, ¬ p ∣ j ∧ ∀ r, (E (f' r) : ModGL TwistTag.D4.tag K) =
        baseChangeGL (iterateFrobenius K 2 (3 * (n / p) * j)) (E r) := by
    intro f' hf' hf'p
    obtain ⟨δ, hδ⟩ := hfieldE f' hf'
    obtain ⟨hpn, j, hpj, hδj⟩ := field_of_order_D4 hn hK σ hσ hp hp3 E f' δ hδ hf'p
    refine ⟨hpn, j, hpj, fun r => ?_⟩
    rw [hE, hδ, hfield]
    have : δ.toRingHom = iterateFrobenius K 2 (3 * (n / p) * j) :=
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
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  let _ : Algebra (ZMod 2) L := ZMod.algebra L 2
  obtain ⟨φ⟩ : Nonempty (K →ₐ[ZMod 2] L) := ⟨IsAlgClosed.lift⟩
  let _ : Algebra K L := φ.toRingHom.toAlgebra
  set ι := algebraMap K L
  set P := diagramMap TwistTag.D4 L with hPdef
  have hP3 : P ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 L
  have hPfix : ∀ k, Units.map (entrywiseHom (iterateFrobenius L 2 k)) P = P := fun k =>
    units_map_entrywiseHom_diagramMap (σ := iterateFrobenius L 2 k)
  set c := p % 3 with hc
  set Q := P ^ c with hQdef
  have hQfix : ∀ k, Units.map (entrywiseHom (iterateFrobenius L 2 k)) Q = Q := fun k => by
    rw [hQdef, map_pow, hPfix]
  have hQp : Q ^ p = P := by
    rw [hQdef, ← pow_mul, pow_eq_pow_mod _ hP3, mul_mod_three hp hp3, pow_one]
  have hQ3 : ∀ j, Q ^ (3 * j) = 1 := fun j => by
    rw [hQdef, ← pow_mul, show c * (3 * j) = 3 * (c * j) by ring, pow_mul, hP3, one_pow]
  have hΦ : ∀ g, endPowU (frobTwistGL TwistTag.D4.tag L 2 e Q) p g =
      P * Units.map (entrywiseHom (iterateFrobenius L 2 n)) g * P⁻¹ := fun g => by
    rw [endPow_frobTwist_of_fixed e p (hQfix e), hQp, ← hnpe]
  have hfs := fixedSet_D4_eq_map_baseChangeGL Nat.prime_two hn hK (Ω := L) 1 (Or.inl rfl)
    σ.toRingHom (fun c => by rw [pow_one]; exact hσ c) (iterateFrobenius L 2 n)
    (fun c => by rw [iterateFrobenius_def])
  set Γ := adjointGroup TwistTag.D4.tag L ⊓
    (endPowU (frobTwistGL TwistTag.D4.tag L 2 e Q) p).eqLocus (MonoidHom.id _) with hΓ
  have hrat : Γ = C₀.map (baseChangeGL ι) := by
    ext g
    change g ∈ adjointGroup TwistTag.D4.tag L ∧ endPowU _ p g = g ↔ _
    have := Set.ext_iff.1 hfs g
    simp only [pow_one, Set.mem_setOf_eq, SetLike.mem_coe] at this
    rw [hΦ]
    exact this
  let ρ : LargeEvenCenterQuot C₀ →* ModGL TwistTag.D4.tag L :=
    (baseChangeGL ι).comp (C₀.subtype.comp E.toMonoidHom)
  have hρ : ∀ r, ρ r = baseChangeGL ι (E r) := fun r => rfl
  have hρinj : Function.Injective ρ := fun r r' h =>
    E.injective (Subtype.ext (baseChangeGL_injective ι h))
  have hmemΓ : ∀ w : C₀, baseChangeGL ι (w : ModGL TwistTag.D4.tag K) ∈ Γ :=
    fun w => by rw [hrat]; exact ⟨_, w.2, rfl⟩
  have hρmem : ∀ r, ρ r ∈ Γ := fun r => hmemΓ (E r)
  let ψ : C₀ ≃* Γ :=
    MulEquiv.ofBijective (((baseChangeGL ι).comp C₀.subtype).codRestrict _ hmemΓ)
      ⟨fun w w' h => Subtype.ext (baseChangeGL_injective _ (congrArg Subtype.val h)),
        fun g => by
          have hg : (g : ModGL TwistTag.D4.tag L) ∈ C₀.map (baseChangeGL ι) := by
            rw [← hrat]; exact g.2
          obtain ⟨w, hw, hwg⟩ := hg
          exact ⟨⟨w, hw⟩, Subtype.ext hwg⟩⟩
  have hψs : ∀ g : Γ, baseChangeGL ι ((ψ.symm g : C₀) : ModGL TwistTag.D4.tag K) = g :=
    fun g => congrArg Subtype.val (ψ.apply_symm_apply g)
  have hinj : Function.Injective (MulAut.conj : C₀ →* MulAut C₀) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro w hw
    have hwZ : w ∈ Subgroup.center C₀ := Subgroup.mem_center_iff.2 fun g => by
      have := congrArg (fun α : MulAut C₀ => α g) (MonoidHom.mem_ker.1 hw)
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    rw [hZ] at hwZ
    exact hwZ
  let Θ : Γ →* MulAut (LargeEvenCenterQuot C₀) :=
    (MulAut.congr E).symm.toMonoidHom.comp (MulAut.conj.comp ψ.symm.toMonoidHom)
  have hD : IsDiagramTwistMatrix TwistTag.D4.tag L Q :=
    Or.inr ⟨TwistTag.D4, c, rfl, by rw [zpow_natCast]⟩
  refine ⟨e, Q, he1, hD, ⟨fun g hg => ?_, ρ, Θ, hρinj, hρmem,
    (MulAut.congr E).symm.injective.comp (hinj.comp ψ.symm.injective), ?_, ?_, ?_⟩,
    ⟨iterateFrobenius L 2 (e * p), fun c => by rw [iterateFrobenius_def, pow_mul], P,
      Or.inr ⟨TwistTag.D4, rfl, rfl⟩, fun g => ?_⟩, ?_⟩
  · rw [frobTwistGL_apply, ← hD.map_conj_eq]
    exact ⟨_, entrywiseFrobGL_mem 2 e hg, rfl⟩
  · intro φ'
    constructor
    · intro hφ'
      obtain ⟨x, rfl⟩ := hI hφ'
      refine ⟨ψ (E x), ?_⟩
      show (MulAut.congr E).symm (MulAut.conj (ψ.symm (ψ (E x)))) = MulAut.conj x
      rw [ψ.symm_apply_apply, ← C14ExcBridgeTwE6.congr_conj, MulEquiv.symm_apply_apply]
    · rintro ⟨g, rfl⟩
      refine Subgroup.subset_closure (Or.inl ⟨E.symm (ψ.symm g), ?_⟩)
      show MulAut.conj (E.symm (ψ.symm g)) = (MulAut.congr E).symm (MulAut.conj (ψ.symm g))
      rw [MulEquiv.eq_symm_apply, C14ExcBridgeTwE6.congr_conj, MulEquiv.apply_symm_apply]
  · intro g r
    change baseChangeGL ι
      ((E ((MulAut.congr E).symm (MulAut.conj (ψ.symm g)) r) : C₀) : ModGL TwistTag.D4.tag K) = _
    rw [hEs, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hψs]
    rfl
  · intro f' hf' hf'p
    obtain ⟨-, j, hpj, hj⟩ := hfrob f' hf' hf'p
    refine ⟨3 * j, fun h => ?_, fun r => ?_⟩
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
      · exact hpj h
    rw [hρ, hρ, hj, baseChangeGL_baseChangeGL, endPow_frobTwist_of_fixed e (3 * j) (hQfix e),
      hQ3, one_mul, inv_one, mul_one]
    change _ = baseChangeGL _ (baseChangeGL ι _)
    rw [baseChangeGL_baseChangeGL]
    have hc : ι.comp (iterateFrobenius K 2 (3 * e * j)) =
        (iterateFrobenius L 2 (e * (3 * j))).comp ι := by
      ext c
      simp only [RingHom.comp_apply, iterateFrobenius_def, map_pow]
      ring_nf
    rw [hc]
  · rw [hΦ, ← hnpe]
  · change Finite Γ
    rw [hrat]
    haveI : Finite (adjointGroup TwistTag.D4.tag K) :=
      CFSG.LieType.Chevalley.generated_group_finite _ K
    haveI : Finite C₀ := Finite.of_injective _ (Subgroup.inclusion_injective
      (fun x hx => (graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom hx).1))
    exact Finite.of_surjective _ (MonoidHom.subgroupMap_surjective (baseChangeGL ι) C₀)

theorem bridge_triD4_chev
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 3)
    (L : Type) [Field L] [IsAlgClosed L] [CharP L 2] {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    BridgeConcl TwistTag.D4.tag L p
      (LargeEvenChevIDImage TwistTag.D4.tag.cartan K
        (LargeEvenTwistedH TwistTag.D4.tag.cartan K TwistTag.D4.perm n))
      (LargeEvenChevFieldImage TwistTag.D4.tag.cartan K
        (LargeEvenTwistedH TwistTag.D4.tag.cartan K TwistTag.D4.perm n)) := by
  have hK3 : Nat.card K = 2 ^ (n * 3) := by rw [hK, ← pow_mul]
  haveI : CharP K 2 := charP_two_of_card hK3
  set σ := iterateFrobeniusEquiv K 2 n with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => by
    rw [hσdef, iterateFrobeniusEquiv_apply, iterateFrobenius_def]
  obtain ⟨-, -, -, -, -, hperf, -, -⟩ := even_triality_exact_automorphism_normal_form hn K hK σ hσ
  have hH : MarkChev.twistedH TwistTag.D4.tag.cartan (IsRoot TwistTag.D4.tag) K
      TwistTag.D4.perm n = graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
    (twistedH_eq_commutator K TwistTag.D4 n σ.toRingHom hσ).trans hperf
  have h1 : ∀ S : (Fin TwistTag.D4.tag.rank → ℤ) → Prop, S = IsRoot TwistTag.D4.tag →
      markIDImage S K (MarkChev.twistedH TwistTag.D4.tag.cartan S K TwistTag.D4.perm n) ⊆
        LargeEvenInnSet _ →
      BridgeConcl TwistTag.D4.tag L p
        (markIDImage S K (MarkChev.twistedH TwistTag.D4.tag.cartan S K TwistTag.D4.perm n))
        (RecipeFieldExcInn.markFieldImage S K
          (MarkChev.twistedH TwistTag.D4.tag.cartan S K TwistTag.D4.perm n)) := by
    intro S hS
    subst hS
    suffices key : ∀ H : Subgroup (MarkChev.GLS (IsRoot TwistTag.D4.tag) K),
        H = graphFixedRootGroup TwistTag.D4 K σ.toRingHom →
        markIDImage (IsRoot TwistTag.D4.tag) K H ⊆ LargeEvenInnSet _ →
        BridgeConcl TwistTag.D4.tag L p (markIDImage (IsRoot TwistTag.D4.tag) K H)
          (RecipeFieldExcInn.markFieldImage (IsRoot TwistTag.D4.tag) K H) from key _ hH
    intro H hH' hI
    subst hH'
    exact bridge_triD4_model hn hK σ hσ L hp hp3 hI
  have h2 := h1 _ (largeEvenIsRoot_eq_isRoot TwistTag.D4.tag)
  suffices key : ∀ H : Subgroup (LargeEvenChevGL TwistTag.D4.tag.cartan K),
      H = MarkChev.twistedH TwistTag.D4.tag.cartan (LargeEvenIsRoot TwistTag.D4.tag.cartan) K
        TwistTag.D4.perm n →
      LargeEvenChevIDImage TwistTag.D4.tag.cartan K H ⊆ LargeEvenInnSet _ →
      BridgeConcl TwistTag.D4.tag L p (LargeEvenChevIDImage TwistTag.D4.tag.cartan K H)
        (LargeEvenChevFieldImage TwistTag.D4.tag.cartan K H) from
    key _ (largeEvenTwistedH_eq _ K _ n) fun φ hφ => by
      obtain ⟨x, hx⟩ := TableBExcSmallRest.chevIDImage_subset_inn_triD4 hn K hK hφ
      exact ⟨x, hx⟩
  intro H hH hI
  subst hH
  rw [largeEvenChevIDImage_eq] at hI ⊢
  exact h2 hI

end

end CFSG.HardMathSupport.C14ExcBridgeTriD4
