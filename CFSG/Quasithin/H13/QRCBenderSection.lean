module

public import CFSG.Quasithin.H13.QRCBenderLift
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagData
public import CFSG.Quasithin.H13.QRCBenderAmbient
public import CFSG.Quasithin.H13.QRCBenderPairModel

public section

namespace CFSG.Quasithin.H13.QRC

open Subgroup CFSG.ABGLocalTools CFSG.Quasithin.SteinbergBS CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup CFSG.Blueprint CFSG.LieType.Ree CFSG.ShultStronglyClosedTI
  CFSG.GorensteinWalter CFSG.BenderSuzuki.MatrixGroups
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField CFSG.Glauberman.Dickson
open scoped MatrixGroups

section Helpers

theorem map_symm_eq_of_map_eq {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    {X : Subgroup G} {Y : Subgroup G'} (h : X.map e.toMonoidHom = Y) :
    Y.map e.symm.toMonoidHom = X := by
  rw [← h, map_map]
  convert map_id X
  ext g
  simp

theorem map_mulEquiv_trans {G₁ G₂ G₃ : Type*} [Group G₁] [Group G₂] [Group G₃]
    (X : Subgroup G₁) (e₁ : G₁ ≃* G₂) (e₂ : G₂ ≃* G₃) :
    X.map (e₁.trans e₂).toMonoidHom = (X.map e₁.toMonoidHom).map e₂.toMonoidHom := by
  rw [map_map]
  rfl

variable {k : Type} [Field k]

theorem upperTriangular_two_eq_sl2Borel : upperTriangular 2 k = sl2Borel k := by
  ext A
  rw [mem_upperTriangular, sl2Borel, sl2_mem_stabilizer_infinity_iff]
  constructor
  · intro h
    exact h 1 0 (by decide)
  · intro h i j hij
    fin_cases i <;> fin_cases j <;> simp_all

theorem unitriangular_two_eq_sl2UpperUnipotent :
    unitriangular 2 k = sl2UpperUnipotentSubgroup k := by
  ext A
  rw [mem_unitriangular, mem_sl2UpperUnipotentSubgroup_iff]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨A 0 1, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j
    · simpa [sl2UpperUnipotent] using h1 0
    · simp [sl2UpperUnipotent]
    · simpa [sl2UpperUnipotent] using h0 1 0 (by decide)
    · simpa [sl2UpperUnipotent] using h1 1
  · rintro ⟨x, rfl⟩
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · fin_cases i <;> fin_cases j <;> simp_all [sl2UpperUnipotent]
    · fin_cases i <;> simp [sl2UpperUnipotent]

@[expose] noncomputable def p2PSLEquiv (k : Type) [Field k] :
    projectiveSL 2 k ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k :=
  QuotientGroup.quotientMulEquivOfEq (scalars_eq_center 2 k)

theorem map_p2Equiv_projUpperTriangular :
    (projUpperTriangular 2 k).map
      (p2PSLEquiv k).toMonoidHom = psl2Borel k := by
  rw [projUpperTriangular, map_map, psl2Borel_eq_map, upperTriangular_two_eq_sl2Borel]
  rfl

theorem map_p2Equiv_projUnitriangular :
    (projUnitriangular 2 k).map
      (p2PSLEquiv k).toMonoidHom = psl2UpperUnipotentSubgroup k := by
  rw [projUnitriangular, map_map, psl2UpperUnipotentSubgroup, psl2UpperUnipotentHom,
    MonoidHom.range_comp, unitriangular_two_eq_sl2UpperUnipotent]
  rfl

variable [CharP k 2]

@[expose] noncomputable def projSLEquiv : SL(2, k) ≃* projectiveSL 2 k :=
  MulEquiv.ofBijective (proj 2 k) ⟨by
    rw [← MonoidHom.ker_eq_bot_iff, ker_proj, scalars_eq_center, sl2_center_eq_bot],
    proj_surjective 2 k⟩

theorem projSLEquiv_apply (g : SL(2, k)) : projSLEquiv g = proj 2 k g := rfl

end Helpers

section Cases

theorem not_linear_and_suzuki
    {X : Type*} [Group X] [Finite X] {k₁ k₂ : Type} [Field k₁]
    [Field k₂] {n a : ℕ} (h₁ : Nat.card k₁ = 2 ^ n) (ha : 1 ≤ a)
    (h₂ : Nat.card k₂ = 2 ^ (2 * a + 1)) (e₁ : X ≃* projectiveSL 2 k₁)
    (e₂ : X ≃* suzukiGroup a k₂) : False := by
  have : Finite k₁ := Nat.finite_of_card_ne_zero (by rw [h₁]; positivity)
  have : Finite k₂ := Nat.finite_of_card_ne_zero (by rw [h₂]; positivity)
  have : CharP k₁ 2 := LinearModel.charP_two_of_card h₁
  have : Finite (suzukiGroup a k₂) := Finite.of_injective _ e₂.symm.injective
  have : Finite (PSL2MatrixGroup k₁) := Finite.of_injective _
    ((e₁.trans (p2PSLEquiv k₁)).symm.injective)
  set e := e₂.symm.trans (e₁.trans (p2PSLEquiv k₁))
  have hS := benderData_suzuki ha h₂
  have hL := benderData_psl2 h₁
  obtain ⟨e', he', -⟩ := exists_mulEquiv_map_sylow e hS.isPGroup hS.not_dvd_index hL.isPGroup
    hL.not_dvd_index
  have hab : ∀ u ∈ suzukiU a k₂, ∀ v ∈ suzukiU a k₂, u * v = v * u := by
    intro u hu v hv
    apply e'.injective
    have hu' : e' u ∈ psl2UpperUnipotentSubgroup k₁ := he' ▸ ⟨u, hu, rfl⟩
    have hv' : e' v ∈ psl2UpperUnipotentSubgroup k₁ := he' ▸ ⟨v, hv, rfl⟩
    rw [map_mul, map_mul]
    exact psl2_rootGroup_comm hu' hv'
  have htop : center (suzukiU a k₂) = ⊤ :=
    eq_top_iff.2 fun z _ => mem_center_iff.2 fun g => Subtype.ext (hab _ g.2 _ z.2)
  have h1 := congrArg (fun H : Subgroup (suzukiU a k₂) => Nat.card H) htop
  rw [SuzukiRootAutomorphism.center_suzukiU h₂ ha, card_top,
    Nat.card_congr (subgroupOfEquivOfLe (suzukiZ0_le_suzukiU (a := a) (K := k₂))).toEquiv,
    SuzukiModel.card_suzukiZ0 h₂, (suzuki_unipotent_structure h₂).2.1] at h1
  have h3 : 2 ^ (2 * a + 1) < (2 ^ (2 * a + 1)) ^ 2 := by
    have : 1 < 2 ^ (2 * a + 1) := Nat.one_lt_two_pow (by omega)
    nlinarith
  omega

variable {A : Type*} [Group A] [Finite A] {K S : Subgroup A} [K.Normal]

omit [Finite A] in
theorem suzuki_quotient_eq_top
    (hCK : ∀ a : A, (∀ x ∈ K, a * x = x * a) → a = 1)
    (hKS : K ⊔ S = ⊤) (hS : IsPGroup 2 S) {a : ℕ} {k : Type} [Field k] (ha : 1 ≤ a)
    (hk : Nat.card k = 2 ^ (2 * a + 1)) (θ : K ≃* suzukiGroup a k) : K = ⊤ := by
  set φ : A →* MulAut (suzukiGroup a k) :=
    (MulAut.congr θ).toMonoidHom.comp MulAut.conjNormal with hφdef
  have hP := (CFSG.ProperTwoGeneratedCore.HighRankPair.suzuki_outer_automorphism_group_has_odd_order
    ha hk).2 (S.map φ) (hS.map φ)
  have hφK : ∀ x : K, φ (x : A) = MulAut.conj (θ x) := by
    intro x
    ext g : 1
    have h2 : MulAut.conjNormal (x : A) (θ.symm g) = x * θ.symm g * x⁻¹ :=
      Subtype.ext (by rw [MulAut.conjNormal_apply]; simp)
    simp only [hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
      MulEquiv.trans_apply, MulAut.conj_apply]
    rw [h2, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hSK : S ≤ K := by
    intro s hs
    obtain ⟨y, hy⟩ := hP ⟨s, hs, rfl⟩
    have h1 : φ (s * ((θ.symm y : K) : A)⁻¹) = 1 := by
      rw [map_mul, map_inv, hφK, MulEquiv.apply_symm_apply, ← hy, mul_inv_cancel]
    have h2 : s * ((θ.symm y : K) : A)⁻¹ = 1 := by
      apply hCK
      intro x hx
      have h3 := congrArg (fun ψ : MulAut (suzukiGroup a k) => θ.symm (ψ (θ ⟨x, hx⟩))) h1
      simp only [hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.congr_apply,
        MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.one_apply] at h3
      have h4 := congrArg Subtype.val h3
      rw [MulAut.conjNormal_apply] at h4
      calc s * ((θ.symm y : K) : A)⁻¹ * x =
          s * ((θ.symm y : K) : A)⁻¹ * x * (s * ((θ.symm y : K) : A)⁻¹)⁻¹ *
            (s * ((θ.symm y : K) : A)⁻¹) := by group
        _ = x * (s * ((θ.symm y : K) : A)⁻¹) := by rw [h4]
    have h5 : s = ((θ.symm y : K) : A) := by
      rw [← mul_inv_eq_one]
      exact h2
    rw [h5]
    exact (θ.symm y).2
  exact eq_top_iff.2 (hKS ▸ sup_le le_rfl hSK)

variable {k : Type} [Field k] {n : ℕ}

omit [Finite A] in
theorem bender_linear_complement (hcard : Nat.card k = 2 ^ n) (θ : K ≃* SL(2, k))
    (hCK : ∀ a : A, (∀ x ∈ K, a * x = x * a) → a = 1) (hKS : K ⊔ S = ⊤)
    (hS : IsPGroup 2 S) :
    ∃ (F : Subgroup A) (τ : F →* RingAut k), IsCyclic F ∧ IsPGroup 2 F ∧ K ⊓ F = ⊥ ∧
      K ⊔ F = ⊤ ∧ Function.Injective τ ∧
      ∀ (f : F) (x : K), θ (MulAut.conjNormal (f : A) x) =
        Matrix.SpecialLinearGroup.map (τ f).toRingHom (θ x) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hcard]; positivity)
  have hγinj := semilinearCoord_injective hcard θ hCK
  set F : Subgroup A :=
    (SemidirectProduct.inr : RingAut k →* Gamma k).range.comap (semilinearCoord hcard θ) with hFdef
  set τ : F →* RingAut k :=
    SemidirectProduct.rightHom.comp ((semilinearCoord hcard θ).comp F.subtype) with hτdef
  have hleft : ∀ f : F, (semilinearCoord hcard θ f).left = 1 := by
    rintro ⟨f, σ, hσ⟩
    change (semilinearCoord hcard θ f).left = 1
    rw [← hσ, SemidirectProduct.left_inr]
  have hτinj : Function.Injective τ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro f hf
    rw [MonoidHom.mem_ker] at hf
    rw [mem_bot]
    apply Subtype.ext
    apply hγinj
    rw [OneMemClass.coe_one, map_one]
    exact SemidirectProduct.ext (by rw [hleft]; rfl) hf
  have hKF : K ⊓ F = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxK, hxF⟩
    rw [mem_bot]
    have h1 := hleft ⟨x, hxF⟩
    change (semilinearCoord hcard θ x).left = 1 at h1
    have h2 := semilinearCoord_of_mem hcard θ ⟨x, hxK⟩
    change semilinearCoord hcard θ x = _ at h2
    rw [h2, SemidirectProduct.left_inl, map_eq_one_iff _ θ.injective] at h1
    exact congrArg Subtype.val h1
  have hKFtop : K ⊔ F = ⊤ := by
    rw [eq_top_iff]
    intro y _
    set x : K := θ.symm (semilinearCoord hcard θ y).left
    have hf : (x : A)⁻¹ * y ∈ F := by
      refine ⟨(semilinearCoord hcard θ y).right, ?_⟩
      rw [map_mul, map_inv, semilinearCoord_of_mem hcard θ x, MulEquiv.apply_symm_apply]
      exact SemidirectProduct.ext (by simp) (by simp)
    have h1 := mul_mem_sup x.2 hf
    rwa [mul_inv_cancel_left] at h1
  have hF2 : IsPGroup 2 F := by
    rintro ⟨f, hf⟩
    have hfKS : f ∈ K ⊔ S := hKS ▸ mem_top f
    rw [← SetLike.mem_coe, normal_mul K S] at hfKS
    obtain ⟨x, hx, s, hs, rfl⟩ := hfKS
    obtain ⟨m, hm⟩ := hS ⟨s, hs⟩
    have hsm : s ^ 2 ^ m = 1 := congrArg Subtype.val hm
    have h1 : (x * s) ^ 2 ^ m ∈ K := by
      have h2 : (QuotientGroup.mk (x * s) : A ⧸ K) ^ 2 ^ m = 1 := by
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff x).2 hx, one_mul,
          ← QuotientGroup.mk_pow, hsm, QuotientGroup.mk_one]
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h2
      exact h2
    have h3 : (x * s) ^ 2 ^ m ∈ K ⊓ F := ⟨h1, F.pow_mem hf _⟩
    rw [hKF, mem_bot] at h3
    exact ⟨m, Subtype.ext (by simpa using h3)⟩
  have : IsCyclic (RingAut k) := (ringAut_card_and_cyclic hcard).2
  refine ⟨F, τ, isCyclic_of_injective τ hτinj, hF2, hKF, hKFtop, hτinj, fun f x => ?_⟩
  rw [semilinearCoord_spec hcard θ (f : A) x]
  rw [hleft, one_mul, inv_one, mul_one]
  rfl

end Cases

section Quotient

variable {A : Type*} [Group A] [Finite A]

theorem bender_pair_in_quotient
    {K S B E : Subgroup A} {n : ℕ} {U₁ : Subgroup K}
    (hU₁ : U₁ = (S ⊓ K).subgroupOf K) (hD : BenderData K U₁ n)
    (hBK : B ⊓ K = (normalizer (U₁ : Set K)).map K.subtype) [IsElementaryAbelian 2 E]
    (hEU : E ≤ S ⊓ K) (hE4 : 4 ≤ Nat.card E) :
    ∃ x : K, x ∉ normalizer (U₁ : Set K) ∧
      x ∈ E.subgroupOf K ⊔ conjugate (E.subgroupOf K) x ∧
      ((x : A) ∈ (E.subgroupOf K ⊔ conjugate (E.subgroupOf K) x).map K.subtype) ∧
      (E.subgroupOf K ⊔ conjugate (E.subgroupOf K) x).map K.subtype = E ⊔ conjugate E (x : A) ∧
      (E.subgroupOf K ⊔ conjugate (E.subgroupOf K) x).map K.subtype ≤ K ∧
      IsSylowOf 2 (S ⊓ (E.subgroupOf K ⊔ conjugate (E.subgroupOf K) x).map K.subtype)
        ((E.subgroupOf K ⊔ conjugate (E.subgroupOf K) x).map K.subtype) ∧
      kerIn (B ⊓ (E.subgroupOf K ⊔ conjugate (E.subgroupOf K) x).map K.subtype)
        ((E.subgroupOf K ⊔ conjugate (E.subgroupOf K) x).map K.subtype) = ⊥ ∧
      inSubgroup (pCore 2) ((E.subgroupOf K ⊔ conjugate (E.subgroupOf K) x).map K.subtype) = ⊥ ∧
      inSubgroup (pCore 2) (B ⊓ (E.subgroupOf K ⊔ conjugate (E.subgroupOf K) x).map K.subtype) =
        S ⊓ (E.subgroupOf K ⊔ conjugate (E.subgroupOf K) x).map K.subtype ∧
      B ⊓ (E.subgroupOf K ⊔ conjugate (E.subgroupOf K) x).map K.subtype =
        ((E.subgroupOf K ⊔ conjugate (E.subgroupOf K) x) ⊓
          normalizer (U₁ : Set K)).map K.subtype ∧
      S ⊓ (E.subgroupOf K ⊔ conjugate (E.subgroupOf K) x).map K.subtype =
        (U₁ ⊓ (E.subgroupOf K ⊔ conjugate (E.subgroupOf K) x)).map K.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hEK : E ≤ K := hEU.trans inf_le_right
  have : IsElementaryAbelian 2 (E.subgroupOf K) := IsElementaryAbelian.subgroupOf hEK
  have hE'U : E.subgroupOf K ≤ U₁ := by
    rw [hU₁]
    exact fun y hy => hEU hy
  have hE'4 : 4 ≤ Nat.card (E.subgroupOf K) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv]
  have hE'2 : IsPGroup 2 (E.subgroupOf K) := IsElementaryAbelian.isPGroup 2 _
  have hE'1 : E.subgroupOf K ≠ ⊥ := by
    intro h
    rw [h, card_bot] at hE'4
    omega
  have hC : ∀ e ∈ E.subgroupOf K, e ≠ 1 → IsPGroup 2 (centralizer ({e} : Set K)) :=
    fun e he he1 => hD.centralizer_isPGroup e
      (orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian e he) he1)
  obtain ⟨x, hxN, hxL⟩ := exists_mem_sup_conjugate hD.stronglyEmbedded
    (hE'U.trans le_normalizer) hE'2 hE'1
  obtain ⟨-, hsyl, -, -, hcore, hO2, hO2P⟩ :=
    bender_pair_props hD.isPGroup hD.not_dvd_index hD.stronglyEmbedded hC hE'U hE'4 hxN
  set L' := E.subgroupOf K ⊔ conjugate (E.subgroupOf K) x with hL'def
  set N := normalizer (U₁ : Set K) with hNdef
  have hinj := K.subtype_injective
  have hLmap : L'.map K.subtype = E ⊔ conjugate E (x : A) := by
    rw [hL'def, Subgroup.map_sup, map_conjugate, map_subgroupOf_eq_of_le hEK]
    rfl
  have hBL : B ⊓ L'.map K.subtype = (L' ⊓ N).map K.subtype := by
    rw [map_inf_eq _ _ _ hinj, inf_comm (L'.map K.subtype), ← hBK, inf_assoc,
      inf_eq_right.2 (map_subtype_le L')]
  have hSL : S ⊓ L'.map K.subtype = (U₁ ⊓ L').map K.subtype := by
    rw [map_inf_eq _ _ _ hinj, hU₁, map_subgroupOf_eq_of_le inf_le_right, inf_assoc,
      inf_eq_right.2 (map_subtype_le L')]
  refine ⟨x, hxN, hxL, ⟨x, hxL, rfl⟩, hLmap, map_subtype_le _, ?_, ?_, ?_, ?_, hBL, hSL⟩
  · rw [hSL, isSylowOf_map_subtype_iff]
    exact hsyl
  · rw [hBL, kerIn_map_subtype, hcore, Subgroup.map_bot]
  · rw [inSubgroup_pCore_map_subtype, hO2, Subgroup.map_bot]
  · rw [hBL, inSubgroup_pCore_map_subtype, hSL, hO2P]

end Quotient

section Main

variable {H : Type} [Group H] [Finite H]

theorem qrc_single_Bender_section_produces_original_higher_image_pair
    (hns : ¬ Group.IsSolvable H) (hchar : IsCharacteristicP 2 H) (T : Sylow 2 H)
    (hTn : ¬ (T : Subgroup H).Normal) {M : Subgroup H} (hTM : (T : Subgroup H) ≤ M)
    (hMH : M < ⊤) (hmax : ∀ Y : Subgroup H, (T : Subgroup H) ≤ Y → Y < ⊤ → Y ≤ M)
    {V : Subgroup H} [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hTV : (T : Subgroup H) ≤ normalizer (V : Set H)) (hVM : V ≤ inSubgroup (pCore 2) M)
    (hVQ : 4 ≤ (V ⊓ pCore 2 H).relIndex V) {n : ℕ} {k : Type} [Field k]
    (hk : Nat.card k = 2 ^ n)
    (hK : (2 ≤ n ∧ Nonempty (↥((oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤))) ≃*
        projectiveSL 2 k)) ∨
      ∃ a : ℕ, 1 ≤ a ∧ n = 2 * a + 1 ∧
        Nonempty (↥((oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤))) ≃*
          suzukiGroup a k)) :
    let D := kerIn M ⊤
    let π := QuotientGroup.mk' D
    let Q := pCore 2 H
    let K := (oddResidualPreimage H).map π
    (∃ ι : H ⧸ D →* MulAut ↥K, Function.Injective ι ∧ (∀ a x, (ι a x : H ⧸ D) = a * x * a⁻¹) ∧
      (2 ≤ n → Nonempty (↥K ≃* projectiveSL 2 k) →
        ∃ (F : Subgroup (H ⧸ D)) (θ : ↥K ≃* projectiveSL 2 k) (τ : F →* RingAut k),
          IsCyclic F ∧ IsPGroup 2 F ∧ K ⊓ F = ⊥ ∧ K ⊔ F = ⊤ ∧ Function.Injective τ ∧
          ∀ (f : F) (x : K) (g : SL(2, k)), θ x = proj 2 k g →
            θ (ι f x) = proj 2 k (Matrix.SpecialLinearGroup.map (τ f).toRingHom g))) ∧
    ((∃ a : ℕ, 1 ≤ a ∧ n = 2 * a + 1 ∧ Nonempty (↥K ≃* suzukiGroup a k)) → K = ⊤) ∧
    ∃ (m : ℕ) (L : Subgroup (H ⧸ D)) (g : H), 1 < m ∧ m ∣ n ∧ L ≤ K ∧
      let I := V ⊔ conjugate V g
      let H₀ := L.comap π
      let J := kerIn (M ⊓ I) I
      g ∈ I ∧ I ≤ oddResidualPreimage H ∧ V < I ∧ I.map π = L ∧
      L = V.map π ⊔ conjugate (V.map π) (π g) ∧ π g ∈ L ∧
      H₀ = D ⊔ I ∧ (I.subgroupOf (Q ⊔ I)).Normal ∧ Q ⊔ I ≤ H₀ ∧
      ((Q ⊔ I).subgroupOf H₀).Normal ∧ Q ≤ normalizer (I : Set H) ∧ ⁅D, I⁆ ≤ Q ∧
      IsSylowOf 2 ((T : Subgroup H) ⊓ I) I ∧ I ⊓ normalizer (V : Set H) ≤ M ⊓ I ∧
      inSubgroup (pCore 2) (M ⊓ I) = (T : Subgroup H) ⊓ I ∧
      J = inSubgroup (pCore 2) I ∧ J = I ⊓ D ∧ J = I ⊓ Q ∧
      inSubgroup (pCore 2) (Q ⊔ I) = Q ∧ IsCharacteristicP 2 I ∧
      ∃ ψ : I →* L, Function.Surjective ψ ∧ ψ.ker = J.subgroupOf I ∧
        (∀ i : I, (ψ i : H ⧸ D) = π i) ∧
        (V.subgroupOf I).map ψ = (V.map π).subgroupOf L ∧
        V.map π ≤ ((T : Subgroup H) ⊓ I).map π ∧
        (∀ v ∈ V.map π, ∀ t ∈ ((T : Subgroup H) ⊓ I).map π, v * t = t * v) ∧
        Nat.card ↥(V.map π) = (V ⊓ Q).relIndex V ∧ (V ⊓ Q).relIndex V ≤ 2 ^ m ∧
        (2 ≤ n → Nonempty (↥K ≃* projectiveSL 2 k) →
          ∃ (k' : Type) (_ : Field k'), Nat.card k' = 2 ^ m ∧
            ∃ e : ↥L ≃* projectiveSL 2 k',
              ((M ⊓ I).subgroupOf I).map (e.toMonoidHom.comp ψ) = projUpperTriangular 2 k' ∧
              (((T : Subgroup H) ⊓ I).subgroupOf I).map (e.toMonoidHom.comp ψ) =
                projUnitriangular 2 k') ∧
        ((∃ a : ℕ, 1 ≤ a ∧ n = 2 * a + 1 ∧ Nonempty (↥K ≃* suzukiGroup a k)) →
          Odd m ∧ 3 ≤ m ∧ ∃ (b : ℕ) (k' : Type) (_ : Field k'), m = 2 * b + 1 ∧
            Nat.card k' = 2 ^ m ∧ ∃ e : ↥L ≃* suzukiGroup b k',
              ((M ⊓ I).subgroupOf I).map (e.toMonoidHom.comp ψ) = suzukiB b k' ∧
              (((T : Subgroup H) ⊓ I).subgroupOf I).map (e.toMonoidHom.comp ψ) =
                suzukiU b k') := by
  intro D π Q K
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : CharP k 2 := LinearModel.charP_two_of_card hk
  obtain ⟨-, -, hDK₀, hKn, hCK, hKS, ⟨hSB, hBtop, hBmax⟩, -, hEcard, hEO⟩ :=
    bender_section_setup hns T hTn hTM hMH hmax hVT hVM
  have := hKn
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective D
  set S := (T : Subgroup H).map π with hSdef
  set B := M.map π with hBdef
  set E := V.map π with hEdef
  have hS2 : IsPGroup 2 S := T.isPGroup'.map π
  have hSsyl : IsSylowOf 2 S ⊤ := isSylowOf_iff.2 ⟨le_top, hS2, by
    rw [relIndex_top_right, hSdef, ← Sylow.coe_mapSurjective hπs T]
    exact (T.mapSurjective hπs).not_dvd_index⟩
  have hUsyl : IsSylowOf 2 (S ⊓ K) K :=
    hSsyl.inf_of_le_normalizer le_top (by rw [normalizer_eq_top])
  obtain ⟨U₁, hU₁⟩ := hUsyl.exists_sylow_eq_subgroupOf
  have hE4 : 4 ≤ Nat.card E := hEcard ▸ hVQ
  have hEel : IsElementaryAbelian 2 E := IsElementaryAbelian.map π
  have hES : E ≤ S := map_mono hVT
  have hCK' : ∀ a : H ⧸ D, (∀ x ∈ K, a * x = x * a) → a = 1 := hCK
  have hι : Function.Injective (MulAut.conjNormal : H ⧸ D →* MulAut ↥K) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    rw [mem_bot]
    refine hCK' a fun x hx => ?_
    have h1 := congrArg (fun φ : MulAut ↥K => ((φ ⟨x, hx⟩ : ↥K) : H ⧸ D)) ha
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc a * x = a * x * a⁻¹ * a := by group
      _ = x * a := by rw [h1]
  have hιapp : ∀ a x, ((MulAut.conjNormal a x : ↥K) : H ⧸ D) = a * x * a⁻¹ :=
    fun a x => MulAut.conjNormal_apply a x
  have hexcl : ∀ a, 1 ≤ a → n = 2 * a + 1 → Nonempty (↥K ≃* suzukiGroup a k) →
      Nonempty (↥K ≃* projectiveSL 2 k) → False := by
    rintro a ha rfl ⟨e₂⟩ ⟨e₁⟩
    exact not_linear_and_suzuki hk ha hk e₁ e₂
  have hUidx : ¬ 2 ∣ (S ⊓ K).relIndex K := (isSylowOf_iff.1 hUsyl).2.2
  rcases hK with ⟨hn, ⟨θ₀⟩⟩ | ⟨a, ha, hna, ⟨θ₀⟩⟩
  ·
    have hdSL := benderData_sl2 hk
    obtain ⟨θ, hθU, hθN⟩ := exists_mulEquiv_map_sylow (θ₀.trans projSLEquiv.symm)
      U₁.isPGroup' U₁.not_dvd_index hdSL.isPGroup hdSL.not_dvd_index
    have hD : BenderData ↥K (U₁ : Subgroup K) n := by
      have h := hdSL.map θ.symm
      rwa [map_symm_eq_of_map_eq θ hθU] at h
    have hθmem : ∀ y : K, θ y ∈ sl2UpperUnipotentSubgroup k ↔ y ∈ (U₁ : Subgroup K) := by
      intro y
      rw [← hθU]
      exact ⟨fun ⟨z, hz, hzy⟩ => (θ.injective hzy) ▸ hz, fun hy => ⟨y, hy, rfl⟩⟩
    have hmemU : ∀ y : K, y ∈ (U₁ : Subgroup K) ↔ (y : H ⧸ D) ∈ S ⊓ K := fun y => by
      rw [hU₁]
      rfl
    have hab : ∀ u ∈ (U₁ : Subgroup K), ∀ v ∈ (U₁ : Subgroup K), u * v = v * u := by
      intro u hu v hv
      apply θ.injective
      obtain ⟨x, hx⟩ := (hθmem u).2 hu
      obtain ⟨y, hy⟩ := (hθmem v).2 hv
      rw [map_mul, map_mul, ← hx, ← hy, ← map_mul, ← map_mul, mul_comm]
    obtain ⟨hBK, hBN⟩ := bender_borel_eq hU₁ hD hKS hSB hBtop hBmax
    have hR2 : IsPGroup 2 (inSubgroup (pCore 2) B) := (pCore_isPGroup (p := 2) (G := B)).map _
    have hRKU : inSubgroup (pCore 2) B ⊓ K ≤ S ⊓ K := by
      refine le_of_isPGroup_of_not_dvd_relIndex hS2.to_inf_left (inf_le_inf_right K hSB)
        (fun h => hUidx (h.trans (Dvd.intro _ (relIndex_mul_relIndex (S ⊓ K) (B ⊓ K) K
          (inf_le_inf_right K hSB) inf_le_right)))) hR2.to_inf_left
        (inf_le_inf_right K (map_subtype_le _)) ?_
      exact inf_le_left.trans ((map_subtype_le _).trans hBN)
    have hRK : inSubgroup (pCore 2) B ≤ K := by
      intro r hr
      have hrB : r ∈ B := map_subtype_le _ hr
      have hRn : B ≤ normalizer (inSubgroup (pCore 2) B : Set (H ⧸ D)) :=
        le_normalizer.trans (normalizer_le_normalizer_map_characteristic B (pCore 2 B))
      refine mem_of_semilinearCoord_right hk θ hCK' (semilinearCoord_right_eq_one hk θ ?_ ?_ ?_)
      · intro y hy
        rw [hθmem, hmemU] at hy ⊢
        rw [hιapp]
        exact (mem_normalizer_iff.1 (hBN hrB) _).1 hy
      · intro y hy
        rw [hθmem, hmemU] at hy ⊢
        rw [hιapp]
        exact (mem_normalizer_iff.1 (hBN (B.inv_mem hrB)) _).1 hy
      · intro y hy
        have hyN : y ∈ normalizer ((U₁ : Subgroup K) : Set K) := by
          rw [← sl2_normalizer_upperUnipotent, ← hθN] at hy
          obtain ⟨z, hz, hzy⟩ := hy
          rwa [← θ.injective hzy]
        have hyBK : (y : H ⧸ D) ∈ B ⊓ K := hBK ▸ ⟨y, hyN, rfl⟩
        rw [hθmem, hmemU]
        have hcoe : ((MulAut.conjNormal r y * y⁻¹ : K) : H ⧸ D) =
            r * y * r⁻¹ * (y : H ⧸ D)⁻¹ := by
          rw [coe_mul, hιapp, coe_inv]
        rw [hcoe]
        refine hRKU ⟨?_, K.mul_mem (hKn.conj_mem _ y.2 r) (K.inv_mem y.2)⟩
        have h1 := (mem_normalizer_iff.1 (hRn hyBK.1) r⁻¹).1
          ((inSubgroup (pCore 2) B).inv_mem hr)
        have h2 := (inSubgroup (pCore 2) B).mul_mem hr h1
        rwa [show r * ((y : H ⧸ D) * r⁻¹ * (y : H ⧸ D)⁻¹) = r * y * r⁻¹ * (y : H ⧸ D)⁻¹ by
          group] at h2
    have hEK : E ≤ K := hEO.trans hRK
    have hEU : E ≤ S ⊓ K := le_inf hES hEK
    have : IsElementaryAbelian 2 (E.subgroupOf K) := IsElementaryAbelian.subgroupOf hEK
    have hE'U : E.subgroupOf K ≤ (U₁ : Subgroup K) := by
      rw [hU₁]
      exact fun y hy => hEU hy
    have hE'4 : 4 ≤ Nat.card (E.subgroupOf K) := by
      rwa [Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv]
    obtain ⟨x, hxN, -, hxL, hLeq, hLK, hSF, hcore, hO2, hO2P, hBL, hSL⟩ :=
      bender_pair_in_quotient hU₁ hD hBK hEU hE4
    have hmodel := bender_pair_linear hD hab hE'U hE'4 hxN
    generalize hL'def : E.subgroupOf K ⊔ conjugate (E.subgroupOf K) x = L' at *
    obtain ⟨f, hf, hfn, hEf, e₁, he₁B, he₁U⟩ := hmodel
    have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
    obtain ⟨g, hgx, hgI, hIK₀, hVI, hIL, hLg, hH₀, hIn, hQIH₀, hQIn, hQN, hcomm, hTIsyl, hNV,
      hO2MI, hJO, hJD, hJQ, hQIO, hcharI, ψ, hψs, hψker, hψπ, hψM, hψT, hψV⟩ :=
      bender_lift hchar T hTn hTM hMH hmax hVT hTV hVM hVQ hDK₀ (L := L'.map K.subtype)
        (x := (x : H ⧸ D)) hxL hLeq hLK (Or.inl ⟨f, GaloisField 2 f, inferInstance, hf, hcardF,
          ⟨(L'.equivMapOfInjective K.subtype K.subtype_injective).symm.trans e₁⟩⟩)
        hSF hcore hO2 hO2P
    have hπψ : ∀ X : Subgroup H, X ≤ V ⊔ conjugate V g →
        X.map π = ((X.subgroupOf (V ⊔ conjugate V g)).map ψ).map (L'.map K.subtype).subtype := by
      intro X hX
      rw [map_map, show (L'.map K.subtype).subtype.comp ψ = π.comp (V ⊔ conjugate V g).subtype from
        MonoidHom.ext fun i => hψπ i, ← map_map, map_subgroupOf_eq_of_le hX]
    have hTImap : ((T : Subgroup H) ⊓ (V ⊔ conjugate V g)).map π = S ⊓ L'.map K.subtype := by
      rw [hπψ _ inf_le_right, hψT, map_subgroupOf_eq_of_le inf_le_right]
    have hEL : E ≤ L'.map K.subtype := hLeq ▸ le_sup_left
    refine ⟨⟨MulAut.conjNormal, hι, hιapp, fun _ _ => ?_⟩, fun ⟨a, ha, hna, he₂⟩ =>
      (hexcl a ha hna he₂ ⟨θ₀⟩).elim, f, L'.map K.subtype, g, by omega, hfn, hLK, ?_⟩
    · obtain ⟨F, τ, hFcyc, hF2, hKF, hKFt, hτ, hact⟩ := bender_linear_complement hk θ hCK' hKS hS2
      refine ⟨F, θ.trans projSLEquiv, τ, hFcyc, hF2, hKF, hKFt, hτ, fun f x g hxg => ?_⟩
      have hxg' : θ x = g := projSLEquiv.injective hxg
      change projSLEquiv (θ (MulAut.conjNormal (f : H ⧸ D) x)) = _
      rw [hact, hxg', projSLEquiv_apply]
    · intro I H₀ J
      refine ⟨hgI, hIK₀, hVI, hIL, hLg, hgx ▸ hxL, hH₀, hIn, hQIH₀, hQIn, hQN, hcomm, hTIsyl,
        hNV, hO2MI, hJO, hJD, hJQ, hQIO, hcharI, ψ, hψs, hψker, hψπ, hψV, ?_, ?_, hEcard, ?_,
        fun _ _ => ?_, fun ⟨a, ha, hna, he₂⟩ => (hexcl a ha hna he₂ ⟨θ₀⟩).elim⟩
      · rw [hTImap]
        exact le_inf hES hEL
      · intro v hv t ht
        rw [hTImap] at ht
        have hv' : (⟨v, hEK hv⟩ : K) ∈ (U₁ : Subgroup K) := (hmemU _).2 (hEU hv)
        have ht' : (⟨t, hLK ht.2⟩ : K) ∈ (U₁ : Subgroup K) := (hmemU _).2 ⟨ht.1, hLK ht.2⟩
        exact congrArg Subtype.val (hab _ hv' _ ht')
      · rw [← hEcard, ← Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv]
        exact hEf
      · refine ⟨GaloisField 2 f, inferInstance, hcardF,
          ((L'.equivMapOfInjective K.subtype K.subtype_injective).symm.trans e₁).trans
            (p2PSLEquiv _).symm, ?_, ?_⟩
        · rw [← map_map, hψM, hBL, map_mulEquiv_trans, map_mulEquiv_trans,
            map_subgroupOf_equivMapOfInjective, he₁B]
          exact map_symm_eq_of_map_eq _ map_p2Equiv_projUpperTriangular
        · rw [← map_map, hψT, hSL, map_mulEquiv_trans, map_mulEquiv_trans,
            map_subgroupOf_equivMapOfInjective, he₁U]
          exact map_symm_eq_of_map_eq _ map_p2Equiv_projUnitriangular
  ·
    subst hna
    have hdSz := benderData_suzuki ha hk
    obtain ⟨θ, hθU, -⟩ := exists_mulEquiv_map_sylow θ₀ U₁.isPGroup' U₁.not_dvd_index
      hdSz.isPGroup hdSz.not_dvd_index
    have hD : BenderData ↥K (U₁ : Subgroup K) (2 * a + 1) := by
      have h := hdSz.map θ.symm
      rwa [map_symm_eq_of_map_eq θ hθU] at h
    have hmemU : ∀ y : K, y ∈ (U₁ : Subgroup K) ↔ (y : H ⧸ D) ∈ S ⊓ K := fun y => by
      rw [hU₁]
      rfl
    have h3 : ¬ 3 ∣ Nat.card ↥K := by
      rw [Nat.card_congr θ.toEquiv]
      exact not_three_dvd_card_suzukiGroup hk
    have hKtop : K = ⊤ := suzuki_quotient_eq_top hCK' hKS hS2 ha hk θ
    obtain ⟨hBK, -⟩ := bender_borel_eq hU₁ hD hKS hSB hBtop hBmax
    have hEK : E ≤ K := by rw [hKtop]; exact le_top
    have hEU : E ≤ S ⊓ K := le_inf hES hEK
    have : IsElementaryAbelian 2 (E.subgroupOf K) := IsElementaryAbelian.subgroupOf hEK
    have hE'U : E.subgroupOf K ≤ (U₁ : Subgroup K) := by
      rw [hU₁]
      exact fun y hy => hEU hy
    have hE'4 : 4 ≤ Nat.card (E.subgroupOf K) := by
      rwa [Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv]
    obtain ⟨x, hxN, -, hxL, hLeq, hLK, hSF, hcore, hO2, hO2P, hBL, hSL⟩ :=
      bender_pair_in_quotient hU₁ hD hBK hEU hE4
    have hmodel := bender_pair_suzuki hD h3 hE'U hE'4 hxN
    generalize hL'def : E.subgroupOf K ⊔ conjugate (E.subgroupOf K) x = L' at *
    obtain ⟨b, hb, hbn, hEb, e₁, he₁B, he₁U⟩ := hmodel
    have hcardF : Nat.card (GaloisField 2 (2 * b + 1)) = 2 ^ (2 * b + 1) :=
      GaloisField.card 2 (2 * b + 1) (by omega)
    obtain ⟨g, hgx, hgI, hIK₀, hVI, hIL, hLg, hH₀, hIn, hQIH₀, hQIn, hQN, hcomm, hTIsyl, hNV,
      hO2MI, hJO, hJD, hJQ, hQIO, hcharI, ψ, hψs, hψker, hψπ, hψM, hψT, hψV⟩ :=
      bender_lift hchar T hTn hTM hMH hmax hVT hTV hVM hVQ hDK₀ (L := L'.map K.subtype)
        (x := (x : H ⧸ D)) hxL hLeq hLK (Or.inr ⟨b, GaloisField 2 (2 * b + 1), inferInstance,
          hb, hcardF, ⟨(L'.equivMapOfInjective K.subtype K.subtype_injective).symm.trans e₁⟩⟩)
        hSF hcore hO2 hO2P
    have hπψ : ∀ X : Subgroup H, X ≤ V ⊔ conjugate V g →
        X.map π = ((X.subgroupOf (V ⊔ conjugate V g)).map ψ).map (L'.map K.subtype).subtype := by
      intro X hX
      rw [map_map, show (L'.map K.subtype).subtype.comp ψ = π.comp (V ⊔ conjugate V g).subtype from
        MonoidHom.ext fun i => hψπ i, ← map_map, map_subgroupOf_eq_of_le hX]
    have hTImap : ((T : Subgroup H) ⊓ (V ⊔ conjugate V g)).map π = S ⊓ L'.map K.subtype := by
      rw [hπψ _ inf_le_right, hψT, map_subgroupOf_eq_of_le inf_le_right]
    have hEL : E ≤ L'.map K.subtype := hLeq ▸ le_sup_left
    refine ⟨⟨MulAut.conjNormal, hι, hιapp, fun _ hlin => (hexcl a ha rfl ⟨θ₀⟩ hlin).elim⟩,
      fun _ => hKtop, 2 * b + 1, L'.map K.subtype, g, by omega, hbn, hLK, ?_⟩
    intro I H₀ J
    refine ⟨hgI, hIK₀, hVI, hIL, hLg, hgx ▸ hxL, hH₀, hIn, hQIH₀, hQIn, hQN, hcomm, hTIsyl,
      hNV, hO2MI, hJO, hJD, hJQ, hQIO, hcharI, ψ, hψs, hψker, hψπ, hψV, ?_, ?_, hEcard, ?_,
      fun _ hlin => (hexcl a ha rfl ⟨θ₀⟩ hlin).elim, fun _ => ?_⟩
    · rw [hTImap]
      exact le_inf hES hEL
    · intro v hv t ht
      rw [hTImap] at ht
      have hv' : (⟨v, hEK hv⟩ : K) ∈ (U₁ : Subgroup K) := (hmemU _).2 (hEU hv)
      have ht' : (⟨t, hLK ht.2⟩ : K) ∈ (U₁ : Subgroup K) := (hmemU _).2 ⟨ht.1, hLK ht.2⟩
      have hv2 : (⟨v, hEK hv⟩ : K) ^ 2 = 1 :=
        Subtype.ext (by simpa using elemPow_eq_one_of_isElementaryAbelian v hv)
      exact congrArg Subtype.val (hD.sq_comm _ hv' hv2 _ ht')
    · rw [← hEcard, ← Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv]
      exact hEb
    · refine ⟨⟨b, by ring⟩, by omega, b, GaloisField 2 (2 * b + 1), inferInstance, rfl, hcardF,
        (L'.equivMapOfInjective K.subtype K.subtype_injective).symm.trans e₁, ?_, ?_⟩
      · rw [← map_map, hψM, hBL, map_mulEquiv_trans, map_subgroupOf_equivMapOfInjective, he₁B]
      · rw [← map_map, hψT, hSL, map_mulEquiv_trans, map_subgroupOf_equivMapOfInjective, he₁U]

end Main

end CFSG.Quasithin.H13.QRC
