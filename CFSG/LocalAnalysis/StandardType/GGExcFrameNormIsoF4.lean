module

public import CFSG.LocalAnalysis.StandardType.GGExcFrameLang
public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoTBInputs
public import CFSG.LocalAnalysis.StandardType.GGNoTransvectionAutForm
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesCore
public import CFSG.LocalAnalysis.StandardType.GGTableBExcRank
public import CFSG.RankThree.Chevalley.SteinbergCAF4SplitPrimeTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc TableBExcTwoFusion
  TableBF4Two TableBF4TwoTB Matrix

namespace ExcFrameIso

section F4


@[expose] noncomputable def frameProdF4 (L : Type) [Field L] (A : SL2 L) :
    adjointGroup .F4 L :=
  (List.ofFn fun i : Fin 4 => TableBF4Two.rho L i A).prod

theorem frameProdF4_conj_rho {L : Type} [Field L] (i : Fin 4) (A B : SL2 L) :
    frameProdF4 L A * rho L i B * (frameProdF4 L A)⁻¹ = rho L i (A * B * A⁻¹) := by
  have h := list_prod_conj_eq (fun j => rho L j A) (rho L i B) i (List.finRange 4)
    (List.nodup_finRange _) (List.mem_finRange i) fun j _ hji =>
      ⟨commute_rho hji A B, commute_rho hji A A⟩
  rw [frameProdF4, List.ofFn_eq_map, h]
  simp only [map_mul, map_inv]

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem adjointMap_rhoF4 {L : Type} [Field L] (f : K →+* L) (i : Fin 4) (A : SL2 K) :
    TableBExcTwo.adjointMap .F4 f (rho K i A) = rho L i (Matrix.SpecialLinearGroup.map f A) :=
  Subtype.ext (by
    rw [TableBExcTwo.coe_adjointMap, TableBF4Two.coe_rho, TableBF4Two.coe_rho]
    exact CFSG.RankThree.Chevalley.baseChangeGL_rootSL2_of_charTwo f (isRoot_orthRoot i) A)

@[expose] noncomputable def langEltF4 {ω : (FiniteField.Extension K 2 2)ˣ} (hω : orderOf ω = 3) :
    adjointGroup .F4 (FiniteField.Extension K 2 2) :=
  frameProdF4 _ (langP (sq_add_self_add_one_eq_zero hω))

theorem langEltF4_conj_rho_HSL {ω : (FiniteField.Extension K 2 2)ˣ} (hω : orderOf ω = 3)
    (i : Fin 4) :
    langEltF4 hω * rho (FiniteField.Extension K 2 2) i (HSL ω) * (langEltF4 hω)⁻¹ =
      TableBExcTwo.adjointMap .F4 (algebraMap K (FiniteField.Extension K 2 2)) (tGen K i) := by
  have hP : langP (sq_add_self_add_one_eq_zero hω) * HSL ω *
      (langP (sq_add_self_add_one_eq_zero hω))⁻¹ = uSL 1 * vSL 1 := by
    rw [langP_mul_HSL, mul_inv_cancel_right]
  rw [langEltF4, frameProdF4_conj_rho, hP, tGen, adjointMap_rhoF4, map_uSL_mul_vSL]

omit
  [Finite K] [CharP K 2] in
theorem orthRoot_iform_even :
    ∀ i k : Fin 4, (Tag.F4.symmetrizedCartan *ᵥ orthRoot i) k % 2 = 0 := by
  decide +kernel


omit [Finite K] [CharP K 2] in
theorem rootSL2_HSL_orthRoot_eq_frameDiag {L : Type} [Field L] {ω : Lˣ} (hωo : orderOf ω = 3)
    (hω3 : ω ^ 3 = 1) (i : Fin 4) :
    rootSL2 .F4 L (orthRoot i) (HSL ω) =
      ExcFrames.frameDiag ω hω3 (redMod .F4 3 (2 • orthRoot i)) := by
  change rootTorusSL2 .F4 L (orthRoot i) ω = _
  rw [CFSG.LieType.SeitzGeneration.ExcHighThree.rootTorusSL2_eq_rootDiagUnit_corootPair
    (isRoot_orthRoot i), ExcFrames.frameDiag]
  congr 1
  funext k
  rw [E6Three.zetaVec_apply, ExcFrames.frameCoord_redMod]
  show ω ^ (2 * CFSG.LieType.Steinberg.Adjoint.iform (orthRoot i) (Pi.single k 1) /
      CFSG.LieType.Steinberg.Adjoint.iform (orthRoot i) (orthRoot i)) =
    ω ^ ((((Tag.F4.symmetrizedCartan *ᵥ (2 • orthRoot i)) k : ℤ) : ZMod 3).val)
  have hnorm : CFSG.LieType.Steinberg.Adjoint.iform (orthRoot i) (orthRoot i) = 4 := by
    rw [← dotProduct_mulVec_eq_iform]
    exact orthRoot_norm i
  have hev := orthRoot_iform_even i k
  rw [pow_val_intCast_eq_zpow hωo, hnorm, Matrix.mulVec_smul, Pi.smul_apply,
    mulVec_symmetrizedCartan_apply]
  rw [zpow_eq_zpow_iff_modEq, hωo]
  rw [mulVec_symmetrizedCartan_apply] at hev
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  unfold Int.ModEq
  push_cast
  omega

@[expose] def frameCoordHomF4 : (Fin 4 → ZMod 3) →+ (Fin Tag.F4.rank → ZMod 3) :=
  AddMonoidHom.mk' (fun v k => ∑ i, v i * ((2 * orthRoot i k : ℤ) : ZMod 3)) fun v w => by
    funext k
    simp [add_mul, Finset.sum_add_distrib]

theorem frameCoordHomF4_single (i : Fin 4) (c : ZMod 3) :
    frameCoordHomF4 (Pi.single i c) = c.val • redMod .F4 3 (2 • orthRoot i) := by
  funext k
  simp [frameCoordHomF4, Pi.single_apply, redMod, nsmul_eq_mul]

theorem adjointMap_tE_eqF4 {ω : (FiniteField.Extension K 2 2)ˣ} (hω : orderOf ω = 3)
    (hω3 : ω ^ 3 = 1)
    (hfull : ∀ a : Fin Tag.F4.rank → (FiniteField.Extension K 2 2)ˣ,
      rootDiagUnit .F4 a ∈ torusGroup .F4 (FiniteField.Extension K 2 2))
    (v : Fin 4 → ZMod 3) :
    TableBExcTwo.adjointMap .F4 (algebraMap K (FiniteField.Extension K 2 2))
        (tE K (Multiplicative.ofAdd v)) =
      langEltF4 hω *
        ⟨ExcFrames.frameDiag ω hω3 (frameCoordHomF4 v),
          ExcFrames.frameDiag_mem_adjointGroup hfull ω hω3 _⟩ * (langEltF4 hω)⁻¹ := by
  classical
  set L := FiniteField.Extension K 2 2 with hL
  set G := langEltF4 hω with hG
  have hrho : ∀ i : Fin 4, ((rho L i (HSL ω) : adjointGroup .F4 L) : ModGL .F4 L) =
      ExcFrames.frameDiag ω hω3 (redMod .F4 3 (2 • orthRoot i)) := fun i =>
    rootSL2_HSL_orthRoot_eq_frameDiag hω hω3 i
  have key : (TableBExcTwo.adjointMap .F4 (algebraMap K L)).comp (tD K) =
      (ExcFrames.frameHom hfull ω hω3 G⁻¹).comp
        ((AddMonoidHom.toMultiplicative frameCoordHomF4).comp
          (MulEquiv.piMultiplicative fun _ : Fin 4 => ZMod 3).symm.toMonoidHom) := by
    refine MonoidHom.pi_ext fun i a => ?_
    have hL1 : tD K (Pi.mulSingle i a) = tGen K i ^ (Multiplicative.toAdd a).val := by
      rw [tD, MonoidHom.noncommPiCoprod_mulSingle, tC_apply]
    have hR1 : (MulEquiv.piMultiplicative fun _ : Fin 4 => ZMod 3).symm (Pi.mulSingle i a) =
        Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd a) : Fin 4 → ZMod 3) := by
      refine Multiplicative.toAdd.injective ?_
      funext j
      simp only [MulEquiv.piMultiplicative_symm_apply, toAdd_ofAdd, Pi.mulSingle_apply,
        Pi.single_apply]
      split_ifs <;> rfl
    have hm : (⟨ExcFrames.frameDiag ω hω3
          ((Multiplicative.toAdd a).val • redMod .F4 3 (2 • orthRoot i)),
          ExcFrames.frameDiag_mem_adjointGroup hfull ω hω3 _⟩ : adjointGroup .F4 L) =
        rho L i (HSL ω) ^ (Multiplicative.toAdd a).val := by
      refine Subtype.ext ?_
      rw [Subgroup.coe_pow, hrho i]
      exact frameDiag_nsmul' ω hω3 _ _
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hL1, hR1, map_pow]
    show (TableBExcTwo.adjointMap .F4 (algebraMap K L) (tGen K i)) ^
        (Multiplicative.toAdd a).val =
      G⁻¹⁻¹ * ⟨ExcFrames.frameDiag ω hω3
        (frameCoordHomF4 (Pi.single i (Multiplicative.toAdd a))),
        ExcFrames.frameDiag_mem_adjointGroup hfull ω hω3 _⟩ * G⁻¹
    rw [frameCoordHomF4_single, hm, ← langEltF4_conj_rho_HSL hω i, conj_pow, inv_inv]
  have h := congrArg (fun f => f (fun j => Multiplicative.ofAdd (v j))) key
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
  rw [tE_apply, h]
  rfl

theorem frameCoordHomF4_form (x y : Fin 4 → ZMod 3) :
    frameCoordHomF4 x ⬝ᵥ (NoTvAut.cartanMod .F4 3 *ᵥ frameCoordHomF4 y) = x ⬝ᵥ y := by
  have hΛ : ∀ z : Fin 4 → ZMod 3,
      frameCoordHomF4 z = ∑ i, z i • redMod .F4 3 (2 • orthRoot i) := by
    intro z
    funext k
    simp [frameCoordHomF4, Finset.sum_apply, redMod, nsmul_eq_mul]
  have hform : ∀ i j, redMod .F4 3 (2 • orthRoot i) ⬝ᵥ
      (NoTvAut.cartanMod .F4 3 *ᵥ redMod .F4 3 (2 • orthRoot j)) = if i = j then 1 else 0 := by
    intro i j
    rw [NoTvAut.redMod_form]
    have h4 : (2 • orthRoot i) ⬝ᵥ (Tag.F4.symmetrizedCartan *ᵥ (2 • orthRoot j)) =
        4 * (orthRoot i ⬝ᵥ (Tag.F4.symmetrizedCartan *ᵥ orthRoot j)) := by
      rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul]
      simp only [nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul]
      ring
    rw [h4]
    by_cases hij : i = j
    · subst hij
      rw [orthRoot_norm i]
      simp only [if_true]
      decide
    · rw [orthRoot_orth i j hij]
      simp [hij]
  have key : frameCoordHomF4 x ⬝ᵥ (NoTvAut.cartanMod .F4 3 *ᵥ frameCoordHomF4 y) =
      ∑ j, ∑ i, x i * y j * (redMod .F4 3 (2 • orthRoot i) ⬝ᵥ
        (NoTvAut.cartanMod .F4 3 *ᵥ redMod .F4 3 (2 • orthRoot j))) := by
    rw [hΛ x, hΛ y]
    simp only [Matrix.mulVec_sum, Matrix.mulVec_smul, sum_dotProduct, dotProduct_sum,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
  rw [key]
  simp only [hform, mul_ite, mul_zero, mul_one, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [dotProduct]

theorem normIsometry_F4 (hK : Nat.card K = 2) (g : adjointGroup .F4 K)
    (hg : ∀ x ∈ (tE K).range, g * x * g⁻¹ ∈ (tE K).range) :
    ∃ M : (Fin 4 → ZMod 3) →+ (Fin 4 → ZMod 3),
      (∀ v, g * tE K (Multiplicative.ofAdd v) * g⁻¹ = tE K (Multiplicative.ofAdd (M v))) ∧
        ∀ v w, M v ⬝ᵥ M w = v ⬝ᵥ w := by
  classical
  set L := FiniteField.Extension K 2 2 with hL
  have h3 : 3 ∣ Nat.card L - 1 := three_dvd_natCard_ext_sub_one hK
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hωo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := L) (p := 3) h3
  have hω3 : ω ^ 3 = 1 := hωo ▸ pow_orderOf_eq_one ω
  have hfull : ∀ a : Fin Tag.F4.rank → Lˣ, rootDiagUnit .F4 a ∈ torusGroup .F4 L :=
    fun a => CFSG.RankThree.Chevalley.F4_rootDiagUnit_mem_torusGroup a
  have hdet : IsUnit ((Tag.F4.symmetrizedCartan.det : ℤ) : ZMod 3) :=
    ExcFrames.isUnit_det_symmetrizedCartan (Or.inl rfl) (by norm_num)
  have hV : Nat.card (TableBExc.torusPow .F4 L 3) = 3 ^ Tag.F4.rank :=
    TableBExc.card_torusPow_of_full hfull Nat.prime_three h3
  have hfinL : Finite (adjointGroup .F4 L) := generated_group_finite .F4 L
  have hfinK : Finite (adjointGroup .F4 K) := generated_group_finite .F4 K
  set G := langEltF4 hωo with hG
  set ι := TableBExcTwo.adjointMap .F4 (algebraMap K L) with hι
  have hιinj : Function.Injective ι := TableBExcTwo.adjointMap_injective _
  set D : (Fin Tag.F4.rank → ZMod 3) → adjointGroup .F4 L := fun s =>
    ⟨ExcFrames.frameDiag ω hω3 s, ExcFrames.frameDiag_mem_adjointGroup hfull ω hω3 s⟩ with hD
  have hKI : ∀ v, ι (tE K (Multiplicative.ofAdd v)) = G * D (frameCoordHomF4 v) * G⁻¹ :=
    fun v => adjointMap_tE_eqF4 hωo hω3 hfull v
  set T := (tE K).range with hT
  have hle : T.map (MulAut.conj g).toMonoidHom ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    exact hg x hx
  have hTeq : T.map (MulAut.conj g).toMonoidHom = T :=
    Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  have hgT : ∀ x, x ∈ T ↔ g * x * g⁻¹ ∈ T := by
    intro x
    constructor
    · intro hx
      exact hle ⟨x, hx, rfl⟩
    · intro hx
      rw [← hTeq] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have hxy : y = x := by
        have h1 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
        exact mul_right_cancel (mul_left_cancel h1)
      exact hxy ▸ hy
  have hTcard : Nat.card T = 3 ^ Tag.F4.rank := by
    have e : Multiplicative (Fin 4 → ZMod 3) ≃ T :=
      (MonoidHom.ofInjective (tE_injective (K := K))).toEquiv
    show Nat.card T = 3 ^ 4
    rw [← Nat.card_congr e, Nat.card_congr (Multiplicative.toAdd),
      Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  set T' : Subgroup (adjointGroup .F4 L) := (T.map ι).map (MulAut.conj G⁻¹).toMonoidHom with hT'
  have hT'le : T' ≤ TableBExc.torusPow .F4 L 3 := by
    rintro _ ⟨_, ⟨y, ⟨u, rfl⟩, rfl⟩, rfl⟩
    have hu : ι (tE K u) = G * D (frameCoordHomF4 (Multiplicative.toAdd u)) * G⁻¹ := by
      have := hKI (Multiplicative.toAdd u)
      rwa [ofAdd_toAdd] at this
    have e : (MulAut.conj G⁻¹).toMonoidHom (ι (tE K u)) =
        D (frameCoordHomF4 (Multiplicative.toAdd u)) := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hu]
      group
    rw [e]
    exact ExcFrames.mem_torusPow_iff_coe.mpr (ExcFrames.frameDiag_mem hfull ω hω3 _)
  have hT'eq : T' = TableBExc.torusPow .F4 L 3 :=
    Subgroup.eq_of_le_of_card_ge hT'le (by
      rw [hV, hT', Subgroup.card_map_of_injective (MulAut.conj G⁻¹).injective,
        Subgroup.card_map_of_injective hιinj, hTcard])
  set a : adjointGroup .F4 L := G⁻¹ * ι g * G with ha
  have hmemV : ∀ x : adjointGroup .F4 L,
      x ∈ TableBExc.torusPow .F4 L 3 ↔ ∃ y ∈ T, x = G⁻¹ * ι y * G := by
    intro x
    rw [← hT'eq]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨ι y, ⟨y, hy, rfl⟩, by simp [MulAut.conj_apply]⟩
  have hnorm : ∀ x : adjointGroup .F4 L,
      x ∈ TableBExc.torusPow .F4 L 3 ↔ a * x * a⁻¹ ∈ TableBExc.torusPow .F4 L 3 := by
    intro x
    rw [hmemV, hmemV]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨g * y * g⁻¹, (hgT y).mp hy, ?_⟩
      simp only [ha, map_mul, map_inv]
      group
    · rintro ⟨z, hz, hzx⟩
      have hgz : g * (g⁻¹ * z * g) * g⁻¹ = z := by group
      refine ⟨g⁻¹ * z * g, (hgT _).mpr (by rw [hgz]; exact hz), ?_⟩
      have h1 : x = a⁻¹ * (a * x * a⁻¹) * a := by group
      rw [h1, hzx]
      simp only [ha, map_mul, map_inv]
      group
  obtain ⟨w, hw⟩ := ExcFrames.exists_weyl_of_normalizes hnorm
  have hex : ∀ v : Fin 4 → ZMod 3, ∃ v' : Fin 4 → ZMod 3,
      tE K (Multiplicative.ofAdd v') = g * tE K (Multiplicative.ofAdd v) * g⁻¹ := by
    intro v
    obtain ⟨u, hu⟩ := hg _ ⟨Multiplicative.ofAdd v, rfl⟩
    exact ⟨Multiplicative.toAdd u, by rw [ofAdd_toAdd, hu]⟩
  choose M0 hM0 using hex
  have hM0add : ∀ v v', M0 (v + v') = M0 v + M0 v' := by
    intro v v'
    apply Multiplicative.ofAdd.injective
    apply tE_injective (K := K)
    rw [hM0, ofAdd_add, map_mul, ofAdd_add, map_mul, hM0, hM0]
    group
  have hΛ : ∀ v, frameCoordHomF4 (M0 v) = TableBExc.torusAct .F4 3 w (frameCoordHomF4 v) := by
    intro v
    refine ExcFrames.frameDiag_injective hωo hω3 hdet ?_
    have e1 : D (frameCoordHomF4 (M0 v)) = G⁻¹ * ι (tE K (Multiplicative.ofAdd (M0 v))) * G := by
      rw [hKI]
      group
    have e2 : G⁻¹ * ι (tE K (Multiplicative.ofAdd (M0 v))) * G =
        a * D (frameCoordHomF4 v) * a⁻¹ := by
      rw [hM0 v, map_mul, map_mul, map_inv, hKI v]
      simp only [ha]
      group
    have e3 := congrArg (Subtype.val : adjointGroup .F4 L → ModGL .F4 L) (e1.trans e2)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at e3
    refine e3.trans ?_
    show (a : ModGL .F4 L) * ExcFrames.frameDiag ω hω3 (frameCoordHomF4 v) *
      (a : ModGL .F4 L)⁻¹ = _
    rw [hw _ (ExcFrames.frameDiag_mem hfull ω hω3 _), ExcFrames.canonicalRep_conj_frameDiag]
  refine ⟨AddMonoidHom.mk' M0 hM0add, fun v => (hM0 v).symm, fun v v' => ?_⟩
  show M0 v ⬝ᵥ M0 v' = v ⬝ᵥ v'
  have h1 := frameCoordHomF4_form (M0 v) (M0 v')
  rw [hΛ v, hΛ v', NoTvAut.torusAct_form] at h1
  exact h1.symm.trans (frameCoordHomF4_form v v')

theorem ggF4TwoNormIsometry_holds (hK : Nat.card K = 2) : GGF4TwoNormIsometry K :=
  fun g hg => normIsometry_F4 hK g hg

theorem ggF4TwoNormIsometryInput_holds : GGF4TwoNormIsometryInput :=
  fun _ _ _ _ hK => ggF4TwoNormIsometry_holds hK

end F4

end ExcFrameIso

end CFSG.StandardType

end
