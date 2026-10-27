module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcBridgeTriD4
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcLangReeF4
public import CFSG.LocalAnalysis.StandardType.GGTwistedF4Diag
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcRee
public import CFSG.RankThree.PartOne.RF4.Closure

public section

namespace CFSG.HardMathSupport.C14ExcBridgeTwF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.StandardType CFSG.Assembly CFSG.StandardType.RecipeExcLang CFSG.HardMathSupport.C14ExcBridgeU
  CFSG.HardMathSupport.C14ExcBridgeE6 CFSG.HardMathSupport.C14ExcBridgeTwE6 CFSG.ComponentClassification.UnbalancedCatalog
  CFSG.LocalAnalysis.ComponentInitial

noncomputable section

@[expose] def BridgeSub (p : ℕ) {R : Type} [Group R] (I F : Set (MulAut R)) (τ : Tag) (L : Type)
    [Field L] (F₀ : adjointGroup τ L →* adjointGroup τ L) : Prop :=
  ∃ (ρ : R →* adjointGroup τ L)
    (Θ : (endPowU F₀ p).eqLocus (MonoidHom.id (adjointGroup τ L)) →* MulAut R),
    Function.Injective ρ ∧ (∀ r, endPowU F₀ p (ρ r) = ρ r) ∧
    Function.Injective Θ ∧ (∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ) ∧
    (∀ g r, ρ (Θ g r) = (g : adjointGroup τ L) * ρ r * (g : adjointGroup τ L)⁻¹) ∧
    ∀ f ∈ F, orderOf f = p → ∃ j : ℕ, ¬ p ∣ j ∧ ∀ r, ρ (f r) = (endPowU F₀ j) (ρ r)

theorem endPowU_apply_eq_iterate





    {G : Type*} [Monoid G] (S : G →* G) (n : ℕ) (x : G) :
    endPowU S n x = S^[n] x := by
  induction n with
  | zero => rw [endPow_zero']; rfl
  | succ n ih => rw [endPow_succ', ih, Function.iterate_succ_apply']

section BaseChange

@[expose] def bcA
    {K L : Type} [Field K] [Field L] (ι : K →+* L) (τ : Tag) :
    adjointGroup τ K →* adjointGroup τ L :=
  ((baseChangeGL ι).comp (adjointGroup τ K).subtype).codRestrict _ fun g =>
    CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup ι g.2

theorem coe_bcA




    {K L : Type} [Field K] [Field L] (ι : K →+* L)
    {τ : Tag} (g : adjointGroup τ K) :
    (bcA ι τ g : ModGL τ L) = baseChangeGL ι (g : ModGL τ K) := rfl

theorem bcA_injective




    {K L : Type} [Field K] [Field L]
    (ι : K →+* L) {τ : Tag} : Function.Injective (bcA ι τ) := fun _ _ h =>
  Subtype.ext (baseChangeGL_injective ι (congrArg Subtype.val h))

theorem bcA_xElement




    {K L : Type} [Field K] [Field L]
    (ι : K →+* L) {τ : Tag} (i : Fin τ.rank) (c : K) :
    bcA ι τ (xElement i c) = xElement i (ι c) :=
  Subtype.ext (baseChangeGL_xUnit ι i c)

theorem bcA_yElement




    {K L : Type} [Field K] [Field L]
    (ι : K →+* L) {τ : Tag} (i : Fin τ.rank) (c : K) :
    bcA ι τ (yElement i c) = yElement i (ι c) :=
  Subtype.ext (baseChangeGL_yUnit ι i c)

theorem reeEndo_bcA
    {K L : Type} [Field K] [Field L]
    (ι : K →+* L) [CharP K ReeTag.F4.prime] [CharP L ReeTag.F4.prime]
    (hfK : ReeTag.F4.ShortFaithful K) (hfL : ReeTag.F4.ShortFaithful L) (b : ℕ)
    (g : adjointGroup ReeTag.F4.tag K) :
    ReeTag.F4.reeEndo L hfL b (bcA ι _ g) = bcA ι _ (ReeTag.F4.reeEndo K hfK b g) := by
  have h : (ReeTag.F4.reeEndo L hfL b).comp (bcA ι _) =
      (bcA ι _).comp (ReeTag.F4.reeEndo K hfK b) :=
    adjointGroup_hom_ext (fun i c => by
      simp only [MonoidHom.comp_apply]
      rw [bcA_xElement, ReeTag.reeEndo_xElement, ReeTag.reeEndo_xElement, bcA_xElement, map_pow])
      (fun i c => by
      simp only [MonoidHom.comp_apply]
      rw [bcA_yElement, ReeTag.reeEndo_yElement, ReeTag.reeEndo_yElement, bcA_yElement, map_pow])
  exact DFunLike.congr_fun h g

end BaseChange

theorem iterate_two_mul
    {L : Type} [Field L] [CharP L ReeTag.F4.prime]
    (hf : ReeTag.F4.ShortFaithful L) (b j : ℕ) (g : adjointGroup ReeTag.F4.tag L) :
    (((ReeTag.F4.reeEndo L hf b)^[2 * j] g : adjointGroup ReeTag.F4.tag L) :
        ModGL ReeTag.F4.tag L) =
      Units.map (entrywiseHom (iterateFrobenius L ReeTag.F4.prime ((2 * b + 1) * j))) g := by
  induction j with
  | zero =>
    rw [mul_zero, mul_zero, Function.iterate_zero, id]
    ext : 1
    change _ = entrywise _ _
    rw [iterateFrobenius_zero, entrywise_id]
  | succ j ih =>
    rw [show 2 * (j + 1) = 2 + 2 * j by ring, Function.iterate_add_apply]
    have h2 : ∀ x, (ReeTag.F4.reeEndo L hf b)^[2] x =
        frobeniusTwist ReeTag.F4.tag L (iterateFrobenius L ReeTag.F4.prime (2 * b + 1)) x :=
      fun x => by
        rw [← CFSG.HardMathSupport.C14ExcRee.reeEndo_comp_self hf b]
        rfl
    rw [h2, coe_frobeniusTwist, ih]
    change baseChangeGL _ (baseChangeGL _ _) = baseChangeGL _ _
    rw [baseChangeGL_baseChangeGL, iterateFrobenius_comp,
      show 2 * b + 1 + (2 * b + 1) * j = (2 * b + 1) * (j + 1) by ring]

theorem bridge_twF4_model
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (L : Type) [Field L] [IsAlgClosed L] [CharP L ReeTag.F4.prime] [Algebra (ZMod 2) L]
    [Algebra.IsAlgebraic (ZMod 2) L] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : markIDImage (IsRoot ReeTag.F4.tag) K (ReeTag.F4.reeGamma K a) ⊆ LargeEvenInnSet _) :
    (∃ f ∈ RecipeFieldExcInn.markFieldImage (IsRoot ReeTag.F4.tag) K (ReeTag.F4.reeGamma K a),
      orderOf f = p) →
    ∃ (hf : ReeTag.F4.ShortFaithful L) (a₀ : ℕ),
      BridgeSub p (markIDImage (IsRoot ReeTag.F4.tag) K (ReeTag.F4.reeGamma K a))
        (RecipeFieldExcInn.markFieldImage (IsRoot ReeTag.F4.tag) K (ReeTag.F4.reeGamma K a))
        ReeTag.F4.tag L (ReeTag.F4.reeEndo L hf a₀) := by
  classical
  set C₀ := ReeTag.F4.reeGamma K a with hC₀
  have hZ : Subgroup.center C₀ = ⊥ := ReeTag.large_Ree_fixed_group_center_trivial a K hK
  set E : LargeEvenCenterQuot C₀ ≃* C₀ := centerQuotEquivOfBot hZ with hEdef
  have hE : ∀ (φ : MulAut (LargeEvenCenterQuot C₀)) r, E (φ r) = MulAut.congr E φ (E r) :=
    fun φ r => by
      show E (φ r) = E (φ (E.symm (E r)))
      rw [E.symm_apply_apply]
  have hEs : ∀ (α : MulAut C₀) r, E ((MulAut.congr E).symm α r) = α (E r) :=
    fun α r => by rw [hE, MulEquiv.apply_symm_apply]
  rintro ⟨f, hfF, hfp⟩
  obtain ⟨hfield, -, ⟨Ψ', hΨ'⟩, -⟩ := large_Ree_full_inner_field_automorphism_normal_form a ha K hK
  have hfieldE : ∀ f' ∈ RecipeFieldExcInn.markFieldImage (IsRoot ReeTag.F4.tag) K C₀,
      ∃ δ : K ≃+* K, MulAut.congr E f' = ReeTag.F4.reeGammaFieldAut K a δ := by
    rintro f' ⟨δ, hG⟩
    refine ⟨δ, MulEquiv.ext fun c => ?_⟩
    show E (f' (E.symm c)) = ReeTag.F4.reeGammaFieldAut K a δ c
    rw [hEdef, centerQuotEquivOfBot_symm, hG c (ReeTag.F4.reeGammaFieldAut K a δ c) (by
      show (((ReeTag.F4.reeGammaFieldAut K a δ c : C₀) : ModGL ReeTag.F4.tag K) :
        Module.End K (RootModule ReeTag.F4.tag K)) = _
      rw [(hfield δ).1]
      rfl), centerQuotEquivOfBot_mk]
  have hordδ : ∀ (f' : MulAut (LargeEvenCenterQuot C₀)) (δ : K ≃+* K),
      MulAut.congr E f' = ReeTag.F4.reeGammaFieldAut K a δ → orderOf f' = orderOf δ := by
    intro f' δ h
    have hφ : ReeTag.F4.reeGammaFieldAut K a δ = Ψ' ⟨1, δ⟩ := by rw [hΨ', map_one, one_mul]
    rw [← MulEquiv.orderOf_eq (MulAut.congr E) f', h, hφ, MulEquiv.orderOf_eq]
    have hinr : (⟨1, δ⟩ : ReeTag.F4.reeGamma K a ⋊[ReeTag.F4.reeGammaFieldAutHom K a]
        (K ≃+* K)) = SemidirectProduct.inr δ := rfl
    rw [hinr, orderOf_injective SemidirectProduct.inr SemidirectProduct.inr_injective]
  have hfrob : ∀ f' ∈ RecipeFieldExcInn.markFieldImage (IsRoot ReeTag.F4.tag) K C₀,
      orderOf f' = p → p ∣ 2 * a + 1 ∧ ∃ j, ¬ p ∣ j ∧ ∀ r,
        (E (f' r) : ModGL ReeTag.F4.tag K) =
          baseChangeGL (iterateFrobenius K ReeTag.F4.prime ((2 * a + 1) / p * j)) (E r) := by
    intro f' hf' hf'p
    obtain ⟨δ, hδ⟩ := hfieldE f' hf'
    have hord : orderOf δ = p := (hordδ f' δ hδ).symm.trans hf'p
    obtain ⟨σ₀, hσ₀, hordσ₀, hzp, -, -⟩ :=
      finite_field_automorphism_fixed_field_cardinality Nat.prime_two (by omega : 1 ≤ 2 * a + 1) hK
    have hfin₀ : IsOfFinOrder σ₀ := by
      rw [← orderOf_pos_iff, hordσ₀]; omega
    obtain ⟨b, hb⟩ : ∃ b : ℕ, σ₀ ^ b = δ := by
      have : δ ∈ Subgroup.zpowers σ₀ := hzp ▸ Subgroup.mem_top δ
      rw [← hfin₀.mem_powers_iff_mem_zpowers] at this
      exact this
    have h1 : 2 * a + 1 ∣ b * p := by
      rw [← hordσ₀]
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul, hb, ← hord, pow_orderOf_eq_one]
    have h2 : ¬ 2 * a + 1 ∣ b := by
      intro h
      have : δ = 1 := by
        rw [← hb]; exact orderOf_dvd_iff_pow_eq_one.1 (hordσ₀ ▸ h)
      rw [this, orderOf_one] at hord
      exact hp.one_lt.ne hord
    obtain ⟨hpn, j, hbj, hpj⟩ := exists_e_j hp (by omega) h1 h2
    refine ⟨hpn, j, hpj, fun r => ?_⟩
    rw [hE, hδ, (hfield δ).1]
    have : δ.toRingHom = iterateFrobenius K ReeTag.F4.prime ((2 * a + 1) / p * j) :=
      RingHom.ext fun c => by
        rw [iterateFrobenius_def]
        change δ c = c ^ 2 ^ ((2 * a + 1) / p * j)
        rw [← hb, frob_pow_apply σ₀ hσ₀, hbj]
    rw [this]
    rfl
  obtain ⟨hpn, -⟩ := hfrob f hfF hfp
  set m := (2 * a + 1) / p with hm
  have hmp : 2 * a + 1 = m * p := (Nat.div_mul_cancel hpn).symm
  have hmodd : Odd m := (Nat.odd_mul.1 (hmp ▸ odd_two_mul_add_one a)).1
  obtain ⟨a₀, ha₀⟩ := hmodd
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have haa : a₀ + k * (2 * a₀ + 1) = a := by
    have : 2 * a + 1 = (2 * a₀ + 1) * (2 * k + 1) := by rw [hmp, ha₀, hk]
    nlinarith
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  obtain ⟨φ⟩ : Nonempty (K →ₐ[ZMod 2] L) := ⟨IsAlgClosed.lift⟩
  let _ : Algebra K L := φ.toRingHom.toAlgebra
  set ι := algebraMap K L
  have hfL : ReeTag.F4.ShortFaithful L := CFSG.RankThree.PartOne.RF4.shortFaithful_F4_of_isAlgebraic
  have hfK : ReeTag.F4.ShortFaithful K :=
    ReeTag.shortFaithful (t := ReeTag.F4) (CharP.cast_eq_zero K ReeTag.F4.prime)
  set F₀ := ReeTag.F4.reeEndo L hfL a₀ with hF₀
  have hΦ : ∀ g, endPowU F₀ p g = ReeTag.F4.reeEndo L hfL a g := fun g => by
    rw [endPowU_apply_eq_iterate, hk, ← haa]
    exact CFSG.HardMathSupport.C14ExcRee.reeEndo_iterate_odd hfL a₀ k g
  have hC₀le : C₀ ≤ adjointGroup ReeTag.F4.tag K := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  let incl : C₀ →* adjointGroup ReeTag.F4.tag K := Subgroup.inclusion hC₀le
  have hfixK : ∀ c : C₀, ReeTag.F4.reeEndo K hfK a (incl c) = incl c := by
    rintro ⟨_, y, hy, rfl⟩
    show ReeTag.F4.reeEndo K hfK a y = y
    exact (DFunLike.congr_fun (ReeTag.finiteReeAut_toMonoidHom (t := ReeTag.F4) (K := K) a)
      y).symm.trans hy
  have hFr : ∀ c : L, iterateFrobenius L ReeTag.F4.prime (2 * a + 1) c = c ^ Nat.card K :=
    fun c => by rw [iterateFrobenius_def, hK]; rfl
  have hbij : Function.Bijective (iterateFrobenius L ReeTag.F4.prime (2 * a + 1)) := by
    rw [← coe_iterateFrobeniusEquiv]; exact (iterateFrobeniusEquiv L ReeTag.F4.prime _).bijective
  have hfixed : adjointGroup ReeTag.F4.tag L ⊓
      (Units.map (entrywiseHom (iterateFrobenius L ReeTag.F4.prime (2 * a + 1)))).eqLocus
        (MonoidHom.id _) = (adjointGroup ReeTag.F4.tag K).map (baseChangeGL ι) := by
    haveI : CharP K 2 := ‹CharP K ReeTag.F4.prime›
    exact fixed_eq_map (K := K) (L := L) (τ := ReeTag.F4.tag) (Or.inr (Or.inl rfl)) _ hFr hbij
  set Γ := (endPowU F₀ p).eqLocus (MonoidHom.id (adjointGroup ReeTag.F4.tag L)) with hΓ
  have hmemΓ : ∀ c : C₀, bcA ι _ (incl c) ∈ Γ := fun c => by
    show endPowU F₀ p _ = _
    rw [hΦ, reeEndo_bcA ι hfK hfL, hfixK]
    rfl
  have hsurj : ∀ g : Γ, ∃ c : C₀, bcA ι _ (incl c) = g := by
    intro g
    have hg' : ReeTag.F4.reeEndo L hfL a g = g := by rw [← hΦ]; exact g.2
    have hg2 : frobeniusTwist ReeTag.F4.tag L (iterateFrobenius L ReeTag.F4.prime (2 * a + 1))
        (g : adjointGroup ReeTag.F4.tag L) = g := by
      rw [← CFSG.HardMathSupport.C14ExcRee.reeEndo_comp_self hfL a, MonoidHom.comp_apply, hg', hg']
    have hmem : ((g : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) ∈
        adjointGroup ReeTag.F4.tag L ⊓
          (Units.map (entrywiseHom (iterateFrobenius L ReeTag.F4.prime (2 * a + 1)))).eqLocus
            (MonoidHom.id _) :=
      ⟨(g : adjointGroup ReeTag.F4.tag L).2, congrArg Subtype.val hg2⟩
    rw [hfixed] at hmem
    obtain ⟨y, hy, hyg⟩ := hmem
    set y' : adjointGroup ReeTag.F4.tag K := ⟨y, hy⟩ with hy'
    have hy'g : bcA ι _ y' = g := Subtype.ext hyg
    have hfy : ReeTag.F4.reeEndo K hfK a y' = y' :=
      bcA_injective ι (by rw [← reeEndo_bcA ι hfK hfL, hy'g, hg'])
    have hfy' : y' ∈ ReeTag.F4.finiteReeFixedGroup K a :=
      (DFunLike.congr_fun (ReeTag.finiteReeAut_toMonoidHom (t := ReeTag.F4) (K := K) a) y').trans hfy
    have hyC : y ∈ C₀ := Subgroup.mem_map_of_mem _ hfy'
    exact ⟨⟨y, hyC⟩, hy'g⟩
  let ψ : C₀ ≃* Γ :=
    MulEquiv.ofBijective (((bcA ι _).comp incl).codRestrict _ hmemΓ)
      ⟨fun c c' h => Subgroup.inclusion_injective hC₀le (bcA_injective ι
          (congrArg Subtype.val h)),
        fun g => (hsurj g).imp fun c hc => Subtype.ext hc⟩
  have hψs : ∀ g : Γ, bcA ι _ (incl (ψ.symm g)) = g :=
    fun g => congrArg Subtype.val (ψ.apply_symm_apply g)
  let ρ : LargeEvenCenterQuot C₀ →* adjointGroup ReeTag.F4.tag L :=
    (bcA ι _).comp (incl.comp E.toMonoidHom)
  have hρ : ∀ r, ρ r = bcA ι _ (incl (E r)) := fun r => rfl
  have hρinj : Function.Injective ρ := fun r r' h =>
    E.injective (Subgroup.inclusion_injective hC₀le (bcA_injective ι h))
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
  have hc : ∀ n, ι.comp (iterateFrobenius K ReeTag.F4.prime n) =
      (iterateFrobenius L ReeTag.F4.prime n).comp ι := fun n => by
    ext c
    simp only [RingHom.comp_apply, iterateFrobenius_def, map_pow]
  refine ⟨hfL, a₀, ρ, Θ, hρinj, fun r => hmemΓ (E r),
    (MulAut.congr E).symm.injective.comp (hinj.comp ψ.symm.injective), ?_, ?_, ?_⟩
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
    change bcA ι _ (incl (E ((MulAut.congr E).symm (MulAut.conj (ψ.symm g)) r))) = _
    rw [hEs, MulAut.conj_apply]
    simp only [map_mul, map_inv, hψs]
    rfl
  · intro f' hf' hf'p
    obtain ⟨-, j, hpj, hj⟩ := hfrob f' hf' hf'p
    refine ⟨2 * j, fun h => ?_, fun r => ?_⟩
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
      · exact hpj h
    apply Subtype.ext
    rw [endPowU_apply_eq_iterate, iterate_two_mul hfL a₀ j (ρ r), hρ, hρ]
    change baseChangeGL ι (E (f' r) : ModGL ReeTag.F4.tag K) =
      baseChangeGL (iterateFrobenius L ReeTag.F4.prime ((2 * a₀ + 1) * j))
        (baseChangeGL ι (E r : ModGL ReeTag.F4.tag K))
    rw [hj, baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hc, ha₀]

theorem bridge_twF4_chev
    {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (L : Type) [Field L] [IsAlgClosed L] [CharP L ReeTag.F4.prime] [Algebra (ZMod 2) L]
    [Algebra.IsAlgebraic (ZMod 2) L] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    (∃ f ∈ LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H a K), orderOf f = p) →
    ∃ (hf : ReeTag.F4.ShortFaithful L) (a₀ : ℕ),
      BridgeSub p (LargeEvenChevIDImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))
        (LargeEvenChevFieldImage LargeEvenCartanF4 K (LargeEvenTwF4H a K))
        ReeTag.F4.tag L (ReeTag.F4.reeEndo L hf a₀) := by
  haveI : CharP K ReeTag.F4.prime := charP_two_of_card hK
  have hH := TwistedF4Diag.twF4H_isRoot_eq_reeGamma ha hK
  have h1 : ∀ S : (Fin 4 → ℤ) → Prop, S = IsRoot .F4 →
      markIDImage S K (MarkChev.twF4H S a K) ⊆ LargeEvenInnSet _ →
      (∃ f ∈ RecipeFieldExcInn.markFieldImage S K (MarkChev.twF4H S a K), orderOf f = p) →
      ∃ (hf : ReeTag.F4.ShortFaithful L) (a₀ : ℕ),
        BridgeSub p (markIDImage S K (MarkChev.twF4H S a K))
          (RecipeFieldExcInn.markFieldImage S K (MarkChev.twF4H S a K))
          ReeTag.F4.tag L (ReeTag.F4.reeEndo L hf a₀) := by
    intro S hS
    subst hS
    suffices key : ∀ H : Subgroup (MarkChev.GLS (IsRoot .F4) K), H = ReeTag.F4.reeGamma K a →
        markIDImage (IsRoot .F4) K H ⊆ LargeEvenInnSet _ →
        (∃ f ∈ RecipeFieldExcInn.markFieldImage (IsRoot .F4) K H, orderOf f = p) →
        ∃ (hf : ReeTag.F4.ShortFaithful L) (a₀ : ℕ),
          BridgeSub p (markIDImage (IsRoot .F4) K H)
            (RecipeFieldExcInn.markFieldImage (IsRoot .F4) K H)
            ReeTag.F4.tag L (ReeTag.F4.reeEndo L hf a₀) from key _ hH
    intro H hH' hI
    subst hH'
    exact bridge_twF4_model ha hK L hp hp2 hI
  have h2 := h1 _ (largeEvenIsRoot_eq_isRoot .F4)
  suffices key : ∀ H : Subgroup (LargeEvenChevGL LargeEvenCartanF4 K),
      H = MarkChev.twF4H (LargeEvenIsRoot LargeEvenCartanF4) a K →
      LargeEvenChevIDImage LargeEvenCartanF4 K H ⊆ LargeEvenInnSet _ →
      (∃ f ∈ LargeEvenChevFieldImage LargeEvenCartanF4 K H, orderOf f = p) →
      ∃ (hf : ReeTag.F4.ShortFaithful L) (a₀ : ℕ),
        BridgeSub p (LargeEvenChevIDImage LargeEvenCartanF4 K H)
          (LargeEvenChevFieldImage LargeEvenCartanF4 K H)
          ReeTag.F4.tag L (ReeTag.F4.reeEndo L hf a₀) from
    key _ (largeEvenTwF4H_eq a K) fun φ hφ => by
      obtain ⟨x, hx⟩ := chevIDImage_subset_inn_twF4 ha K hK hφ
      exact ⟨x, hx⟩
  intro H hH hI
  subst hH
  rw [largeEvenChevIDImage_eq] at hI ⊢
  exact h2 hI

end

end CFSG.HardMathSupport.C14ExcBridgeTwF4
