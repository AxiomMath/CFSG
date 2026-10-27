module

public import CFSG.LocalAnalysis.StandardType.GGRealKGExcNegDefs
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRootJ
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwRootJ
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCore
public import CFSG.RankThree.PartOne.KE.CTLang
public import CFSG.LieType.Chevalley.GraphFixedF4GroupDescent
public import CFSG.RankThree.Classical2.MatrixFrobeniusLang

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.RootOps CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.RankThree.PartOne.KE


private noncomputable def ggRKN_w0 (τ : Tag) : WeylGroup τ :=
  (coxeterSystem τ).wordProd ((RootOps.longestWord τ).map τ.idx)

private theorem ggRKN_w0_single {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4) (i : Fin τ.rank) :
    ggRKN_w0 τ • (Pi.single i 1 : Fin τ.rank → ℤ) = -Pi.single i 1 := by
  rcases hτ with rfl | rfl | rfl <;>
    fin_cases i <;> (rw [ggRKN_w0, wordProd_smul] <;> decide +kernel)

private theorem ggRKN_w0_reversesSigns {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4) :
    ReversesSigns (ggRKN_w0 τ) := by
  have hsingle : ∀ i : Fin τ.rank,
      height (ggRKN_w0 τ • (Pi.single i 1 : Fin τ.rank → ℤ)) < 0 := by
    intro i
    rw [ggRKN_w0_single hτ i]
    simp [height]
  intro α hα hpos
  exact height_smul_neg_of_forall_single hsingle hα hpos

private theorem ggRKN_eq_w0 {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {w : WeylGroup τ}
    (hw : ExcIsLongest τ w) : w = ggRKN_w0 τ := by
  refine ReversesSigns.eq ?_ (ggRKN_w0_reversesSigns hτ)
  exact fun α hα hpos => (IsRoot.height_neg_iff (IsRoot.smul hα w)).2 fun j =>
    hw α hα ((IsRoot.height_pos_iff hα).1 hpos) j

private theorem ggRKN_smul_zsmul {τ : Tag} (w : WeylGroup τ) (n : ℤ) (x : Fin τ.rank → ℤ) :
    w • (n • x) = n • (w • x) :=
  AddMonoidHom.map_zsmul (DistribMulAction.toAddMonoidEnd (WeylGroup τ) (Fin τ.rank → ℤ) w) n x

private theorem ggRKN_sum_single {τ : Tag} (β : Fin τ.rank → ℤ) :
    ∑ i, β i • (Pi.single i 1 : Fin τ.rank → ℤ) = β := by
  funext j
  rw [Finset.sum_apply, Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    rw [Pi.smul_apply]
    simp [Pi.single_apply, Ne.symm hi]
  · intro hj
    simp at hj

theorem ggRealKGNeg_smul_eq_neg {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {w : WeylGroup τ}
    (hw : ExcIsLongest τ w) (β : Fin τ.rank → ℤ) : w • β = -β := by
  rw [ggRKN_eq_w0 hτ hw]
  conv_lhs => rw [← ggRKN_sum_single β]
  rw [Finset.smul_sum]
  simp only [ggRKN_smul_zsmul, ggRKN_w0_single hτ, smul_neg]
  rw [Finset.sum_neg_distrib, ggRKN_sum_single β]

private theorem ggRKN_WSL_uSL_WSL {L : Type} [Field L] [CharP L 2] (c : L) :
    WSL * uSL c * WSL = (vSL c : SL2 L) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [WSL, uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]

private theorem ggRKN_WSL_vSL_WSL {L : Type} [Field L] [CharP L 2] (c : L) :
    WSL * vSL c * WSL = (uSL c : SL2 L) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [WSL, uSL, vSL, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]

private theorem ggRKN_conj_WSL {L : Type} [Field L] [CharP L 2] (y : SL2 L) :
    (MulAut.conj WSL).toMonoidHom y = WSL * y * WSL := by
  show WSL * y * WSL⁻¹ = WSL * y * WSL
  rw [ggKGTj_WSL_inv_eq]

theorem ggRealKGNeg_step_rootSL2 {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (F : ExcFrame τ K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    {γ δ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hneg : F.w • γ = -δ) (M : SL2 (AlgebraicClosure K)) :
    F.D.step (rootSL2 τ (AlgebraicClosure K) γ M) =
      rootSL2 τ (AlgebraicClosure K) δ (WSL * Matrix.SpecialLinearGroup.map Fr M * WSL) := by
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  have h2L : (2 : AlgebraicClosure K) = 0 := CharP.cast_eq_zero (AlgebraicClosure K) 2
  have hδ : IsRoot τ δ := by
    have h := IsRoot.neg (IsRoot.smul hγ F.w)
    rwa [hneg, neg_neg] at h
  have hX : ∀ {α α' : Fin τ.rank → ℤ}, IsRoot τ α → F.w • α = -α' →
      ∀ c : AlgebraicClosure K, F.D.step (pinnedX τ (AlgebraicClosure K) α c) =
        pinnedX τ (AlgebraicClosure K) (-α') (Fr c) := by
    intro α α' hα hαneg c
    have hU : F.D.Φ (pinnedX τ (AlgebraicClosure K) α c) =
        pinnedX τ (AlgebraicClosure K) α (Fr c) := by
      rw [hΦ]
      exact Units.ext (entrywise_pinnedX Fr α c)
    show F.D.n * F.D.Φ (pinnedX τ (AlgebraicClosure K) α c) * F.D.n⁻¹ = _
    rw [hU, F.n_eq, canonicalRep_mul_pinnedX_mul_inv_of_two h2L F.w hα (Fr c),
      hαneg]
  have h : F.D.step.comp (rootSL2 τ (AlgebraicClosure K) γ) =
      (rootSL2 τ (AlgebraicClosure K) δ).comp
        ((MulAut.conj WSL).toMonoidHom.comp (Matrix.SpecialLinearGroup.map Fr)) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower (K := AlgebraicClosure K)) ?_
    intro g hg
    rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · rw [show CFSG.LocalAnalysis.ComponentInitial.sl2Upper (AlgebraicClosure K) c =
          (uSL c : SL2 (AlgebraicClosure K)) from rfl]
      simp only [MonoidHom.comp_apply, ggRKN_conj_WSL]
      rw [CFSG.RankThree.Chevalley.rootSL2_uSL_of_charTwo hγ c, hX hγ hneg c,
        CFSG.LieType.Chevalley.map_uSL, ggRKN_WSL_uSL_WSL,
        CFSG.RankThree.Chevalley.rootSL2_vSL_of_charTwo hδ (Fr c)]
    · rw [show CFSG.LocalAnalysis.ComponentInitial.sl2Lower (AlgebraicClosure K) c =
          (vSL c : SL2 (AlgebraicClosure K)) from rfl]
      simp only [MonoidHom.comp_apply, ggRKN_conj_WSL]
      rw [CFSG.RankThree.Chevalley.rootSL2_vSL_of_charTwo hγ c,
        hX (IsRoot.neg hγ) (by rw [smul_neg, hneg]) c, neg_neg,
        CFSG.LieType.Chevalley.map_vSL, ggRKN_WSL_vSL_WSL,
        CFSG.RankThree.Chevalley.rootSL2_uSL_of_charTwo hδ (Fr c)]
  have hM := congrArg (fun f : SL2 (AlgebraicClosure K) →*
    ModGL τ (AlgebraicClosure K) => f M) h
  simpa only [MonoidHom.comp_apply, ggRKN_conj_WSL] using hM

theorem ggRealKGNeg_step_Y {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (F : ExcFrame τ K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g) (x : adjointGroup τ K) :
    F.D.step (ggKGExcY F x) = ggKGExcY F x := by
  have hBx : F.D.Φ (baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K)) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) := by
    rw [hΦ]
    exact units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr (x : ModGL τ K)
  show F.D.n * F.D.Φ (ggKGExcY F x) * F.D.n⁻¹ = ggKGExcY F x
  rw [ggKGExcY_apply, map_mul, map_mul, map_inv, F.D.lang, hBx]
  group

theorem ggRealKGNeg_exists_P {K : Type} [Field K] [Finite K] [CharP K 2]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K) :
    ∃ P : SL2 (AlgebraicClosure K), Matrix.SpecialLinearGroup.map Fr P = WSL * P := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hm]
  obtain ⟨-, hlang⟩ := CFSG.RankThree.Classical2.matrix_frobenius_lang (K := K)
    (Ω := AlgebraicClosure K) Nat.prime_two m.pos hK (n := 2) (by norm_num)
    (Matrix.SpecialLinearGroup.toGL (WSL : SL2 (AlgebraicClosure K)))
  obtain ⟨H, hHdet, hH⟩ := hlang (WSL : SL2 (AlgebraicClosure K)).2
  let Hs : SL2 (AlgebraicClosure K) := ⟨(H : Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)), hHdet⟩
  have hmap : (H : Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)).map Fr =
      (H : Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)).map (· ^ 2 ^ (m : ℕ)) := by
    ext i j
    simp only [Matrix.map_apply, hFr, hK]
  have hHs : Matrix.SpecialLinearGroup.map Fr Hs = Hs * WSL := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.SpecialLinearGroup.coe_mul]
    change (H : Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)).map Fr =
      (H : Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)) *
        ((WSL : SL2 (AlgebraicClosure K)) : Matrix (Fin 2) (Fin 2) (AlgebraicClosure K))
    have hW : ((WSL : SL2 (AlgebraicClosure K)) : Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)) =
        ((Matrix.SpecialLinearGroup.toGL (WSL : SL2 (AlgebraicClosure K)) :
          GL (Fin 2) (AlgebraicClosure K)) : Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)) := rfl
    rw [hW, hH, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mul, hmap]
  refine ⟨Hs⁻¹, ?_⟩
  rw [map_inv, hHs, mul_inv_rev, ggKGTj_WSL_inv_eq]

private noncomputable def ggRKN_phi {K : Type} [Field K] (P : SL2 (AlgebraicClosure K)) :
    SL2 K →* SL2 (AlgebraicClosure K) :=
  (MulAut.conj P).toMonoidHom.comp
    (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)))

private theorem ggRKN_phi_apply {K : Type} [Field K] (P : SL2 (AlgebraicClosure K)) (N : SL2 K) :
    ggRKN_phi P N =
      P * Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) N * P⁻¹ :=
  rfl

private theorem ggRKN_phi_injective {K : Type} [Field K] (P : SL2 (AlgebraicClosure K)) :
    Function.Injective (ggRKN_phi P) := by
  refine (MulAut.conj P).injective.comp ?_
  intro X Y h
  apply Subtype.ext
  apply Matrix.map_injective (algebraMap K (AlgebraicClosure K)).injective
  exact congrArg Subtype.val h

private theorem ggRKN_map_algebraMap_fixed {K : Type} [Field K] [Finite K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (N : SL2 K) :
    Matrix.SpecialLinearGroup.map Fr
        (Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) N) =
      Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) N := by
  ext i j
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    hFr, ← map_pow, ggKGTj_pow_card']

private theorem ggRKN_phi_fixed {K : Type} [Field K] [Finite K] [CharP K 2]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {P : SL2 (AlgebraicClosure K)} (hPq : Matrix.SpecialLinearGroup.map Fr P = WSL * P)
    (N : SL2 K) :
    WSL * Matrix.SpecialLinearGroup.map Fr (ggRKN_phi P N) * WSL = ggRKN_phi P N := by
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  rw [ggRKN_phi_apply, map_mul, map_mul, map_inv, hPq, ggRKN_map_algebraMap_fixed hFr N,
    mul_inv_rev, ggKGTj_WSL_inv_eq]
  rw [show WSL * (WSL * P *
        Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) N * (P⁻¹ * WSL)) * WSL =
      (WSL * WSL) * P * Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) N *
        P⁻¹ * (WSL * WSL) from by group, ggKGTj_WSL_sq_one]
  group

private theorem ggRKN_SL2_descent {K : Type} [Field K] [Finite K]
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {M : SL2 (AlgebraicClosure K)} (hM : Matrix.SpecialLinearGroup.map Fr M = M) :
    ∃ M₀ : SL2 K, Matrix.SpecialLinearGroup.map (algebraMap K (AlgebraicClosure K)) M₀ = M := by
  classical
  have hentry : ∀ i j, (M : Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)) i j ^ Nat.card K =
      (M : Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)) i j := by
    intro i j
    have h := congrFun (congrFun (congrArg Subtype.val hM) i) j
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
      hFr] at h
    exact h
  choose b hb using fun i j => Set.mem_range.1
    (CFSG.LieType.Chevalley.mem_range_algebraMap_of_pow_card_eq (k := K)
      (L := AlgebraicClosure K) (hentry i j))
  let B : Matrix (Fin 2) (Fin 2) K := fun i j => b i j
  have hBmap : B.map (algebraMap K (AlgebraicClosure K)) =
      (M : Matrix (Fin 2) (Fin 2) (AlgebraicClosure K)) := by
    ext i j
    rw [Matrix.map_apply]
    exact hb i j
  have hdet : B.det = 1 := by
    apply (algebraMap K (AlgebraicClosure K)).injective
    rw [map_one, RingHom.map_det]
    change (B.map (algebraMap K (AlgebraicClosure K))).det = 1
    rw [hBmap]
    exact M.2
  exact ⟨⟨B, hdet⟩, Subtype.ext hBmap⟩

private theorem ggRKN_range {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (F : ExcFrame τ K p E)
    {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hneg : F.w • γ = -γ)
    {P : SL2 (AlgebraicClosure K)}
    (hPq : Matrix.SpecialLinearGroup.map Fr P = WSL * P) :
    ((rootSL2 τ (AlgebraicClosure K) γ).comp (ggRKN_phi P)).range = ggRealKGNegLhat F γ := by
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  refine le_antisymm ?_ ?_
  · rintro x ⟨N, rfl⟩
    refine Subgroup.mem_inf.2 ⟨⟨ggRKN_phi P N, rfl⟩, ?_⟩
    change F.D.step (rootSL2 τ (AlgebraicClosure K) γ (ggRKN_phi P N)) =
      rootSL2 τ (AlgebraicClosure K) γ (ggRKN_phi P N)
    rw [ggRealKGNeg_step_rootSL2 F hΦ hγ hneg, ggRKN_phi_fixed hFr hPq N]
  · intro x hx
    obtain ⟨hxL, hxF⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨M, rfl⟩ := hxL
    have hM : WSL * Matrix.SpecialLinearGroup.map Fr M * WSL = M := by
      have h := ggRealKGNeg_step_rootSL2 F hΦ hγ hneg M
      exact (CFSG.RankThree.Chevalley.rootSL2_injective_of_field
        (K := AlgebraicClosure K) (β := γ)) (h.symm.trans hxF)
    have hM' : Matrix.SpecialLinearGroup.map Fr M = WSL * M * WSL := by
      calc Matrix.SpecialLinearGroup.map Fr M
          = (WSL * WSL) * Matrix.SpecialLinearGroup.map Fr M * (WSL * WSL) := by
            rw [ggKGTj_WSL_sq_one, one_mul, mul_one]
        _ = WSL * (WSL * Matrix.SpecialLinearGroup.map Fr M * WSL) * WSL := by group
        _ = WSL * M * WSL := by rw [hM]
    have hYfix : Matrix.SpecialLinearGroup.map Fr (P⁻¹ * M * P) = P⁻¹ * M * P := by
      rw [map_mul, map_mul, map_inv, hPq, hM', mul_inv_rev, ggKGTj_WSL_inv_eq]
      rw [show P⁻¹ * WSL * (WSL * M * WSL) * (WSL * P) =
          P⁻¹ * (WSL * WSL) * M * (WSL * WSL) * P from by group, ggKGTj_WSL_sq_one]
      group
    obtain ⟨N, hN⟩ := ggRKN_SL2_descent hFr hYfix
    refine ⟨N, ?_⟩
    change rootSL2 τ (AlgebraicClosure K) γ (ggRKN_phi P N) = rootSL2 τ (AlgebraicClosure K) γ M
    rw [ggRKN_phi_apply, hN]
    group

theorem ggRealKGNeg_Lhat_le_range {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4 ∨ τ = .E6)
    (F : ExcFrame τ K p E) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hneg : F.w • γ = -γ)
    (hq : 4 ≤ Nat.card K) :
    ggRealKGNegLhat F γ ≤ (ggKGExcY F).range := by
  obtain ⟨Fr, hFr, hΦ⟩ := F.frob
  obtain ⟨P, hPq⟩ := ggRealKGNeg_exists_P hFr
  have hrange := ggRKN_range F hFr hΦ hγ hneg hPq
  let ψ : SL2 K →* ModGL τ (AlgebraicClosure K) :=
    (MulAut.conj F.D.g0).toMonoidHom.comp
      ((rootSL2 τ (AlgebraicClosure K) γ).comp (ggRKN_phi P))
  have hψ : ∀ N, ψ N = F.D.g0 * rootSL2 τ (AlgebraicClosure K) γ (ggRKN_phi P N) * F.D.g0⁻¹ :=
    fun _ => rfl
  have hψinj : Function.Injective ψ :=
    (MulAut.conj F.D.g0).injective.comp
      ((CFSG.RankThree.Chevalley.rootSL2_injective_of_field (K := AlgebraicClosure K)
        (β := γ)).comp (ggRKN_phi_injective P))
  haveI : Finite ψ.range := by
    rw [MonoidHom.range_eq_map]
    exact Finite.of_surjective (fun x : (⊤ : Subgroup (SL2 K)) =>
      (⟨ψ x, Subgroup.mem_map_of_mem ψ x.2⟩ : (⊤ : Subgroup (SL2 K)).map ψ))
      (by rintro ⟨_, x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩)
  have hSL : CFSG.IsQuasisimple (SL2 K) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 2 K
      (by norm_num) (Or.inr (by omega)) (Or.inr (by omega))
  have hperf : ⁅ψ.range, ψ.range⁆ = ψ.range :=
    LayerFacts.ggCommutator_eq_of_isQuasisimple
      ((CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
        (MonoidHom.ofInjective hψinj)).mp hSL)
  have hXC : ψ.range ≤ adjointGroup τ (AlgebraicClosure K) := by
    rintro _ ⟨N, rfl⟩
    rw [hψ]
    exact mul_mem (mul_mem F.D.g0_mem
      ((CFSG.LieType.Chevalley.exceptional_Lang_root_rank_one_data τ (AlgebraicClosure K)
        γ).2.2.2.2.1 _)) (inv_mem F.D.g0_mem)
  have hXF : ∀ x ∈ ψ.range, Units.map (entrywiseHom Fr) x = x := by
    rintro _ ⟨N, rfl⟩
    have hy : rootSL2 τ (AlgebraicClosure K) γ (ggRKN_phi P N) ∈ ggRealKGNegLhat F γ := by
      rw [← hrange]
      exact ⟨N, rfl⟩
    have hyF : F.D.n * F.D.Φ (rootSL2 τ (AlgebraicClosure K) γ (ggRKN_phi P N)) * F.D.n⁻¹ =
        rootSL2 τ (AlgebraicClosure K) γ (ggRKN_phi P N) := (Subgroup.mem_inf.1 hy).2
    rw [hψ, ← hΦ, map_mul, map_mul, map_inv, F.D.lang]
    calc F.D.g0 * F.D.n * F.D.Φ (rootSL2 τ (AlgebraicClosure K) γ (ggRKN_phi P N)) *
          (F.D.g0 * F.D.n)⁻¹
        = F.D.g0 * (F.D.n * F.D.Φ (rootSL2 τ (AlgebraicClosure K) γ (ggRKN_phi P N)) *
            F.D.n⁻¹) * F.D.g0⁻¹ := by group
      _ = _ := by rw [hyF]
  have hdesc : ψ.range ≤
      (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K))) := by
    rcases hτ with rfl | rfl | rfl | rfl
    · exact (finite_fixed_subgroup_rational_perfect 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) Fr hFr
        ψ.range hXC hXF).2.2 _ le_rfl hperf
    · exact (finite_fixed_subgroup_rational_perfect 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) Fr hFr
        ψ.range hXC hXF).2.2 _ le_rfl hperf
    · intro x hx
      have hM : x ∈ adjointGroup Tag.F4 (AlgebraicClosure K) ⊓
          (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) := ⟨hXC hx, hXF x hx⟩
      rwa [F4_frobenius_fixed_eq_map Fr hFr] at hM
    · exact (finite_fixed_subgroup_rational_perfect 3 (Or.inl ⟨rfl, rfl⟩) Fr hFr
        ψ.range hXC hXF).2.2 _ le_rfl hperf
  intro y hy
  rw [← hrange] at hy
  obtain ⟨N, rfl⟩ := hy
  obtain ⟨r, hr, hrx⟩ := Subgroup.mem_map.1 (hdesc ⟨N, rfl⟩)
  refine ⟨⟨r, hr⟩, ?_⟩
  rw [ggKGExcY_apply]
  change F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) r * F.D.g0 = _
  rw [hrx, hψ]
  change F.D.g0⁻¹ * (F.D.g0 * rootSL2 τ (AlgebraicClosure K) γ (ggRKN_phi P N) * F.D.g0⁻¹) *
    F.D.g0 = rootSL2 τ (AlgebraicClosure K) γ (ggRKN_phi P N)
  group

theorem ggKGExcY_injective {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (F : ExcFrame τ K p E) :
    Function.Injective (ggKGExcY F) := by
  intro x y h
  apply Subtype.ext
  apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
  have h3 : F.D.g0 * ggKGExcY F x * F.D.g0⁻¹ = F.D.g0 * ggKGExcY F y * F.D.g0⁻¹ := by rw [h]
  rw [ggKGExcY_apply, ggKGExcY_apply] at h3
  calc baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K)
      = F.D.g0 * (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) *
          F.D.g0) * F.D.g0⁻¹ := by group
    _ = F.D.g0 * (F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL τ K) *
          F.D.g0) * F.D.g0⁻¹ := h3
    _ = baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL τ K) := by group

theorem ggRealKGNegJ_eq_comap_rootRankOneGroup {τ : Tag} {K : Type} [Field K] [Finite K]
    {p : ℕ} {E : Subgroup (adjointGroup τ K)} (F : ExcFrame τ K p E)
    (γ : Fin τ.rank → ℤ) :
    ggRealKGNegJ F γ = (rootRankOneGroup τ (AlgebraicClosure K) γ).comap (ggKGExcY F) := by
  obtain ⟨Fr, hFr, hΦ⟩ := F.frob
  ext x
  change (ggKGExcY F x ∈ rootRankOneGroup τ (AlgebraicClosure K) γ ∧
    F.D.step (ggKGExcY F x) = ggKGExcY F x) ↔
    ggKGExcY F x ∈ rootRankOneGroup τ (AlgebraicClosure K) γ
  exact and_iff_left (ggRealKGNeg_step_Y F hFr hΦ x)

theorem ggRealKGNegJ_map_eq {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4 ∨ τ = .E6)
    (F : ExcFrame τ K p E) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hneg : F.w • γ = -γ)
    (hq : 4 ≤ Nat.card K) :
    (ggRealKGNegJ F γ).map (ggKGExcY F) = ggRealKGNegLhat F γ := by
  refine le_antisymm ?_ ?_
  · rw [ggRealKGNegJ]
    exact Subgroup.map_comap_le _ _
  · rw [ggRealKGNegJ, Subgroup.map_comap_eq]
    exact le_inf (ggRealKGNeg_Lhat_le_range hτ F hγ hneg hq) le_rfl

private noncomputable def ggRKN_equiv_SL2 {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2]
    {p : ℕ} {E : Subgroup (adjointGroup τ K)}
    (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4 ∨ τ = .E6) (F : ExcFrame τ K p E)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hneg : F.w • γ = -γ)
    (hq : 4 ≤ Nat.card K) {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (hΦ : ∀ g, F.D.Φ g = Units.map (entrywiseHom Fr) g)
    {P : SL2 (AlgebraicClosure K)} (hPq : Matrix.SpecialLinearGroup.map Fr P = WSL * P) :
    ggRealKGNegJ F γ ≃* SL2 K :=
  ((Subgroup.equivMapOfInjective (ggRealKGNegJ F γ) (ggKGExcY F) (ggKGExcY_injective F)).trans
    (MulEquiv.subgroupCongr (ggRealKGNegJ_map_eq hτ F hγ hneg hq))).trans
    ((MonoidHom.ofInjective
      (f := (rootSL2 τ (AlgebraicClosure K) γ).comp (ggRKN_phi P))
      ((CFSG.RankThree.Chevalley.rootSL2_injective_of_field
        (K := AlgebraicClosure K) (β := γ)).comp (ggRKN_phi_injective P))).trans
      (MulEquiv.subgroupCongr (ggRKN_range F hFr hΦ hγ hneg hPq))).symm

theorem ggRealKGNegJ_quasisimple {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4 ∨ τ = .E6)
    (F : ExcFrame τ K p E) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hneg : F.w • γ = -γ)
    (hq : 4 ≤ Nat.card K) : CFSG.IsQuasisimple (ggRealKGNegJ F γ) := by
  obtain ⟨Fr, hFr, hΦ⟩ := F.frob
  obtain ⟨P, hPq⟩ := ggRealKGNeg_exists_P hFr
  exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
    (ggRKN_equiv_SL2 hτ F hγ hneg hq hFr hΦ hPq)).mpr
    (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 2 K
      (by norm_num) (Or.inr (by omega)) (Or.inr (by omega)))

theorem ggRealKGNegJ_dvd_card {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4 ∨ τ = .E6)
    (F : ExcFrame τ K p E) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hneg : F.w • γ = -γ)
    (hq : 4 ≤ Nat.card K) (hpq : p ∣ Nat.card K + 1) : p ∣ Nat.card (ggRealKGNegJ F γ) := by
  obtain ⟨Fr, hFr, hΦ⟩ := F.frob
  obtain ⟨P, hPq⟩ := ggRealKGNeg_exists_P hFr
  rw [Nat.card_congr (ggRKN_equiv_SL2 hτ F hγ hneg hq hFr hΦ hPq).toEquiv,
    CFSG.Wreathed.CentralSL2.card_SL_two]
  have h1 : Nat.card K + 1 ∣ Nat.card K ^ 2 - 1 := by
    have hsq : Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
      simpa using (Nat.sq_sub_sq (Nat.card K) 1)
    rw [hsq]
    exact dvd_mul_right _ _
  exact (hpq.trans h1).trans (dvd_mul_left _ _)

theorem ggRealKGNegJ_weyl {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (hτ : τ = .E7 ∨ τ = .E8 ∨ τ = .F4 ∨ τ = .E6)
    (F : ExcFrame τ K p E) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hneg : F.w • γ = -γ)
    (hq : 4 ≤ Nat.card K) :
    ∃ r ∈ ggRealKGNegJ F γ, ggKGExcY F r =
      canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection γ) := by
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  obtain ⟨Fr, hFr, hΦ⟩ := F.frob
  have hwsl : rootWeylSL2 τ (AlgebraicClosure K) γ 1 = rootSL2 τ (AlgebraicClosure K) γ WSL := by
    simp only [rootWeylSL2, nSL_one]
  have hmem : rootWeylSL2 τ (AlgebraicClosure K) γ 1 ∈ ggRealKGNegLhat F γ := by
    rw [hwsl]
    refine Subgroup.mem_inf.2 ⟨⟨WSL, rfl⟩, ?_⟩
    change F.D.step (rootSL2 τ (AlgebraicClosure K) γ WSL) = rootSL2 τ (AlgebraicClosure K) γ WSL
    rw [ggRealKGNeg_step_rootSL2 F hΦ hγ hneg WSL, CFSG.LieType.Chevalley.map_WSL,
      ggKGTj_WSL_sq_one, one_mul]
  have hcanon : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection γ) ∈
      ggRealKGNegLhat F γ :=
    (CFSG.RankThree.Chevalley.EvenF4QPlus.rootWeylSL2_one_eq_canonicalRep_of_charTwo
      (M := AlgebraicClosure K) hγ) ▸ hmem
  rw [← ggRealKGNegJ_map_eq hτ F hγ hneg hq] at hcanon
  obtain ⟨r, hr, hrY⟩ := Subgroup.mem_map.1 hcanon
  exact ⟨r, hr, hrY⟩

end CFSG.StandardType
