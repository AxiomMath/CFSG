module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcRootDefs
public import CFSG.LocalAnalysis.StandardType.GGLangModelIndex

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus

private theorem ggKGEj_Y_injective
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (F : ExcFrame τ K p E) :
    Function.Injective (ggKGExcY F) := by
  intro a b h
  have h' := congrArg (fun g : ModGL τ (AlgebraicClosure K) =>
    F.D.g0 * g * F.D.g0⁻¹) h
  simp only [ggKGExcY_apply] at h'
  have h2 : baseChangeGL (algebraMap K (AlgebraicClosure K)) (a : ModGL τ K) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (b : ModGL τ K) := by
    have h3 := h'
    group at h3
    exact h3
  exact Subtype.ext (baseChangeGL_injective (algebraMap K (AlgebraicClosure K)) h2)

private theorem ggKGEj_Phi_g0_eq
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (F : ExcFrame τ K p E) (hw : F.w = 1) :
    F.D.Φ F.D.g0 = F.D.g0 := by
  rw [F.D.lang, F.n_eq, hw, canonicalRep_one, mul_one]

private theorem ggKGEj_uSL_sq {K : Type} [Field K] [CharP K 2] (c : K) :
    uSL c * uSL c = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uSL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, CharTwo.add_self_eq_zero]

private theorem ggKGEj_vSL_sq {K : Type} [Field K] [CharP K 2] (c : K) :
    vSL c * vSL c = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [vSL, Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, CharTwo.add_self_eq_zero]

private theorem ggKGEj_rootSL2_range_eq_closure
    {τ : Tag} {K : Type} [Field K] (γ : Fin τ.rank → ℤ) :
    (rootSL2 τ K γ).range =
      Subgroup.closure (Set.range (fun c : K => rootSL2 τ K γ (uSL c)) ∪
                        Set.range (fun c : K => rootSL2 τ K γ (vSL c))) := by
  have htop : Subgroup.closure (Set.range (uSL (K := K)) ∪ Set.range (vSL (K := K))) = ⊤ := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower]
    congr 1
  rw [MonoidHom.range_eq_map, ← htop, MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact Or.inl ⟨c, rfl⟩
    · exact Or.inr ⟨c, rfl⟩
  · rintro (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨uSL c, Or.inl ⟨c, rfl⟩, rfl⟩
    · exact ⟨vSL c, Or.inr ⟨c, rfl⟩, rfl⟩

private theorem ggKGEj_mem_range_of_sq_one
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    (F : ExcFrame τ K p E) (hw : F.w = 1) {γ : Fin τ.rank → ℤ}
    {A : SL2 K} (hA2 : A * A = 1) :
    baseChangeGL (algebraMap K (AlgebraicClosure K)) (rootSL2 τ K γ A) ∈
      (ggKGExcY F).range := by
  obtain ⟨Fr, hFr, hΦ⟩ := F.frob
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_ringHom (algebraMap K (AlgebraicClosure K)).injective 2
  have hmem : rootSL2 τ K γ A ∈ adjointGroup τ K :=
    (exceptional_Lang_root_rank_one_data τ K γ).2.2.2.2.1 A
  let t : adjointGroup τ K := ⟨rootSL2 τ K γ A, hmem⟩
  have ht2 : t * t = 1 := by
    apply Subtype.ext
    change rootSL2 τ K γ A * rootSL2 τ K γ A = 1
    rw [← map_mul, hA2, map_one]
  let x : ModGL τ (AlgebraicClosure K) :=
    F.D.g0 * baseChangeGL (algebraMap K (AlgebraicClosure K)) (t : ModGL τ K) * F.D.g0⁻¹
  have hxC : x ∈ adjointGroup τ (AlgebraicClosure K) :=
    mul_mem (mul_mem F.D.g0_mem
      (CFSG.LieType.Chevalley.baseChangeGL_mem_adjointGroup
        (algebraMap K (AlgebraicClosure K)) t.property))
      (inv_mem F.D.g0_mem)
  have hxF : Units.map (entrywiseHom Fr) x = x := by
    have hg0 : Units.map (entrywiseHom Fr) F.D.g0 = F.D.g0 := by
      rw [← hΦ, ggKGEj_Phi_g0_eq F hw]
    have hBt : Units.map (entrywiseHom Fr)
        (baseChangeGL (algebraMap K (AlgebraicClosure K)) (t : ModGL τ K)) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (t : ModGL τ K) :=
      units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr (t : ModGL τ K)
    change Units.map (entrywiseHom Fr)
      (F.D.g0 * baseChangeGL (algebraMap K (AlgebraicClosure K)) (t : ModGL τ K) *
        F.D.g0⁻¹) = _
    rw [map_mul, map_mul, map_inv, hg0, hBt]
  have hx2 : x * x = 1 := by
    change (F.D.g0 * baseChangeGL (algebraMap K (AlgebraicClosure K)) (t : ModGL τ K) *
        F.D.g0⁻¹) * (F.D.g0 * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (t : ModGL τ K) * F.D.g0⁻¹) = 1
    rw [show (F.D.g0 * baseChangeGL (algebraMap K (AlgebraicClosure K)) (t : ModGL τ K) *
        F.D.g0⁻¹) * (F.D.g0 * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (t : ModGL τ K) * F.D.g0⁻¹) =
        F.D.g0 * (baseChangeGL (algebraMap K (AlgebraicClosure K)) (t : ModGL τ K) *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (t : ModGL τ K)) * F.D.g0⁻¹
        from by group]
    rw [← map_mul, show (t : ModGL τ K) * (t : ModGL τ K) = 1 from congrArg Subtype.val ht2,
      map_one]
    group
  have hoddK : ¬ 2 ∣ Nat.card K - 1 := by
    haveI : Fintype K := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hn]
    obtain ⟨j, hj⟩ : ∃ j, (n : ℕ) = j + 1 := ⟨(n : ℕ) - 1, by have := n.pos; omega⟩
    rw [hj, pow_succ]
    have : 0 < 2 ^ j := by positivity
    omega
  have hτ' : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
    rcases hτ with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inl h
  have hN : ∀ (E' : Type) [Field E'] [Finite E'] (σ : E' ≃+* E'),
      Nat.card (fixSubfield σ) = Nat.card K →
        ((fixedFieldImage τ σ).subgroupOf (entrywiseFixedGroup τ σ)).index ∣ 3 :=
    fun E' _ _ σ hcard =>
      LangRat.fixedFieldImage_index_dvd_three hτ' σ (by rw [hcard]; exact hoddK)
  have hx3 : x ^ 3 ∈ (adjointGroup τ K).map
      (baseChangeGL (algebraMap K (AlgebraicClosure K))) :=
    LangRat.pow_mem_map_adjointGroup_of_fixed Fr hFr 3 hN hxC hxF
  have hxmem : x ∈ (adjointGroup τ K).map
      (baseChangeGL (algebraMap K (AlgebraicClosure K))) := by
    rwa [show x ^ 3 = x by rw [pow_succ, pow_two, hx2, one_mul]] at hx3
  obtain ⟨r, hrG, hrx⟩ := Subgroup.mem_map.1 hxmem
  refine ⟨⟨r, hrG⟩, ?_⟩
  rw [ggKGExcY_apply]
  change F.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (r : ModGL τ K) *
    F.D.g0 = baseChangeGL (algebraMap K (AlgebraicClosure K)) (rootSL2 τ K γ A)
  rw [hrx]
  change F.D.g0⁻¹ * (F.D.g0 *
    baseChangeGL (algebraMap K (AlgebraicClosure K)) (t : ModGL τ K) * F.D.g0⁻¹) *
    F.D.g0 = baseChangeGL (algebraMap K (AlgebraicClosure K)) (rootSL2 τ K γ A)
  rw [show F.D.g0⁻¹ * (F.D.g0 *
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (t : ModGL τ K) * F.D.g0⁻¹) *
      F.D.g0 = baseChangeGL (algebraMap K (AlgebraicClosure K)) (t : ModGL τ K) from by group]

private noncomputable def ggKGEj_equiv_SL2
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (F : ExcFrame τ K p E) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ)
    (hmap : (ggKGExcJ F γ).map (ggKGExcY F) = ggKGExcLhat τ K γ) :
    ggKGExcJ F γ ≃* SL2 K := by
  classical
  have hYinj : Function.Injective (ggKGExcY F) := ggKGEj_Y_injective F
  let Yj : ggKGExcJ F γ →* ggKGExcLhat τ K γ :=
    { toFun := fun r => ⟨ggKGExcY F r, r.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun a b =>
        Subtype.ext (map_mul (ggKGExcY F) (a : adjointGroup τ K) (b : adjointGroup τ K)) }
  have hYj_inj : Function.Injective Yj := fun a b h =>
    Subtype.ext (hYinj (congrArg Subtype.val h))
  have hYj_surj : Function.Surjective Yj := by
    intro s
    have hs : (s : ModGL τ (AlgebraicClosure K)) ∈ (ggKGExcJ F γ).map (ggKGExcY F) := by
      rw [hmap]; exact s.2
    obtain ⟨r, hr, hrY⟩ := hs
    exact ⟨⟨r, hr⟩, Subtype.ext hrY⟩
  let e : ggKGExcJ F γ ≃* ggKGExcLhat τ K γ := MulEquiv.ofBijective Yj ⟨hYj_inj, hYj_surj⟩
  have hcongr : rootRankOneGroup τ K γ = rootSubgroup τ K γ ⊔ rootSubgroup τ K (-γ) :=
    CFSG.RankThree.Chevalley.range_rootSL2_of_isRoot (K := K) hγ
  exact e.trans <|
    (Subgroup.equivMapOfInjective (rootRankOneGroup τ K γ)
      (baseChangeGL (algebraMap K (AlgebraicClosure K)))
      (baseChangeGL_injective (algebraMap K (AlgebraicClosure K)))).symm.trans <|
      (MulEquiv.subgroupCongr hcongr).trans (CFSG.RankThree.Chevalley.rootSL2Equiv hγ).symm

theorem ggKGExcJ_map_eq
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    (F : ExcFrame τ K p E) (hw : F.w = 1) {γ : Fin τ.rank → ℤ} :
    (ggKGExcJ F γ).map (ggKGExcY F) = ggKGExcLhat τ K γ := by
  have hgen : ggKGExcLhat τ K γ ≤ (ggKGExcY F).range := by
    rw [ggKGExcLhat, rootRankOneGroup, ggKGEj_rootSL2_range_eq_closure (γ := γ),
      MonoidHom.map_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro z ⟨y, hy, rfl⟩
    rcases hy with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact ggKGEj_mem_range_of_sq_one hτ F hw (ggKGEj_uSL_sq c)
    · exact ggKGEj_mem_range_of_sq_one hτ F hw (ggKGEj_vSL_sq c)
  refine le_antisymm ?_ ?_
  · rw [ggKGExcJ]
    exact Subgroup.map_comap_le _ _
  · rw [ggKGExcJ, Subgroup.map_comap_eq]
    exact le_inf hgen le_rfl

theorem ggKGExcJ_quasisimple
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    (F : ExcFrame τ K p E) (hw : F.w = 1) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hq : 4 ≤ Nat.card K) : IsQuasisimple (ggKGExcJ F γ) := by
  let e := ggKGEj_equiv_SL2 F hγ (ggKGExcJ_map_eq hτ F hw)
  have hqSL2 : IsQuasisimple (SL2 K) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 2 K
      (by norm_num) (Or.inr (by omega)) (Or.inr (by omega))
  exact (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr e).mpr hqSL2

theorem ggKGExcJ_weyl
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    (F : ExcFrame τ K p E) (hw : F.w = 1) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    ∃ r ∈ ggKGExcJ F γ, ggKGExcY F r =
      canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection γ) := by
  have hmem : rootWeylSL2 τ (AlgebraicClosure K) γ 1 ∈ ggKGExcLhat τ K γ := by
    rw [ggKGExcLhat, rootRankOneGroup]
    refine Subgroup.mem_map.2 ⟨rootWeylSL2 τ K γ 1, ?_, ?_⟩
    · exact ⟨WSL, by rw [rootWeylSL2, nSL_one]⟩
    · have hbc : baseChangeGL (algebraMap K (AlgebraicClosure K))
          (rootSL2 τ K γ WSL) = rootSL2 τ (AlgebraicClosure K) γ WSL := by
        rw [CFSG.RankThree.Chevalley.baseChangeGL_rootSL2_of_field, map_WSL]
      simpa only [rootWeylSL2, nSL_one] using hbc
  have hcanon : canonicalRep (coxeterSystem τ) (AlgebraicClosure K) (rootReflection γ) ∈
      ggKGExcLhat τ K γ := by
    rw [← CFSG.RankThree.Chevalley.EvenF4QPlus.rootWeylSL2_one_eq_canonicalRep_of_charTwo
      (M := AlgebraicClosure K) hγ]
    exact hmem
  rw [← ggKGExcJ_map_eq hτ F hw] at hcanon
  obtain ⟨r, hr, hrY⟩ := Subgroup.mem_map.1 hcanon
  exact ⟨r, hr, hrY⟩

theorem ggKGExcJ_dvd_card
    {τ : Tag} {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    {E : Subgroup (adjointGroup τ K)} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4)
    (F : ExcFrame τ K p E) (hw : F.w = 1) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ)
    (hpq : p ∣ Nat.card K - 1) : p ∣ Nat.card (ggKGExcJ F γ) := by
  let e := ggKGEj_equiv_SL2 F hγ (ggKGExcJ_map_eq hτ F hw)
  rw [Nat.card_congr e.toEquiv, CFSG.Wreathed.CentralSL2.card_SL_two]
  have h1 : Nat.card K - 1 ∣ Nat.card K ^ 2 - 1 := by
    have hsq : Nat.card K ^ 2 - 1 = (Nat.card K + 1) * (Nat.card K - 1) := by
      simpa using (Nat.sq_sub_sq (Nat.card K) 1)
    rw [hsq]
    exact dvd_mul_left _ _
  exact (hpq.trans h1).trans (dvd_mul_left _ _)

end CFSG.StandardType
