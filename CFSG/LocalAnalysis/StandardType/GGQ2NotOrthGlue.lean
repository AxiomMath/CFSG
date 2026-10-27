module

public import CFSG.LocalAnalysis.StandardType.GGWAutProp898
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrLineStab
public import CFSG.LocalAnalysis.StandardType.GGQTwoI1FailGlue
public import CFSG.LocalAnalysis.StandardType.GGQ2HeartBI1
public import CFSG.LocalAnalysis.StandardType.GGOrthEichler
public import CFSG.LocalAnalysis.StandardType.GGQ2ShapeDNoForm
public import CFSG.LocalAnalysis.StandardType.GGQ2WNoEichler
public import CFSG.LocalAnalysis.StandardType.GGQ2ThreeEltNormW

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggNG_card_Bs {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    (M : GGQ2LDatum 3 Bs L x) :
    Nat.card ↥Bs = 3 ^ Module.finrank (ZMod 3) M.V := by
  have hE : Finite (Additive ↥Bs) :=
    Finite.of_injective (Additive.ofMul.symm : Additive ↥Bs → ↥Bs)
      Additive.ofMul.symm.injective
  have hVfin : Finite M.V :=
    Finite.of_injective (M.model.toEquiv.symm : M.V → Additive ↥Bs)
      M.model.toEquiv.symm.injective
  have hVft : Fintype M.V := Fintype.ofFinite M.V
  have hNZ : NeZero 3 := ⟨by norm_num⟩
  have hcard : Nat.card ↥Bs = Nat.card M.V :=
    Nat.card_congr (Additive.ofMul.trans M.model.toEquiv)
  rw [hcard, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 3), ZMod.card]

private theorem ggNG_orthType_map_conj {p : ℕ} [Fact p.Prime] {V V' : Type} [AddCommGroup V]
    [Module (ZMod p) V] [AddCommGroup V'] [Module (ZMod p) V']
    (τ : V ≃ₗ[ZMod p] V') {R : Subgroup (V ≃ₗ[ZMod p] V)} (h : GGOrthType R) :
    GGOrthType (R.map (ggLinConj τ).toMonoidHom) := by
  obtain ⟨Q, hQnd, hiso, hcomm⟩ := h
  let Q' : QuadraticForm (ZMod p) V' := Q.comp (τ.symm : V' ≃ₗ[ZMod p] V).toLinearMap
  have hQ'nd : (QuadraticMap.polarBilin Q').Nondegenerate := by
    have heq : QuadraticMap.polarBilin Q' =
        (LinearMap.BilinForm.congr τ) (QuadraticMap.polarBilin Q) := by
      ext x y
      dsimp only [Q']
      rw [LinearMap.BilinForm.congr_apply, QuadraticMap.polarBilin_comp]
      simp only [LinearEquiv.coe_toLinearMap, LinearMap.compl₁₂_apply]
    rw [heq]
    exact LinearMap.BilinForm.Nondegenerate.congr τ hQnd
  refine ⟨Q', hQ'nd, ?_, ?_⟩
  · rintro g ⟨g₀, hg₀, rfl⟩ v
    change Q (τ.symm (ggLinConj τ g₀ v)) = Q (τ.symm v)
    rw [ggLinConj_apply, LinearEquiv.symm_apply_apply]
    exact hiso g₀ hg₀ (τ.symm v)
  · intro g' h' hg' hh'
    have hisom_back : ∀ g' : V' ≃ₗ[ZMod p] V', ZS.IsIsom p Q' g' →
        ZS.IsIsom p Q ((ggLinConj τ).symm g') := by
      intro g'' hg'' v
      have h1 : τ ((ggLinConj τ).symm g'' v) = g'' (τ v) := by
        have h2 := congrArg (fun T : V' ≃ₗ[ZMod p] V' => T (τ v))
          ((ggLinConj τ).apply_symm_apply g'')
        rw [ggLinConj_apply, LinearEquiv.symm_apply_apply] at h2
        exact h2
      calc Q ((ggLinConj τ).symm g'' v)
          = Q (τ.symm (τ ((ggLinConj τ).symm g'' v))) := by
            rw [LinearEquiv.symm_apply_apply]
        _ = Q (τ.symm (g'' (τ v))) := by rw [h1]
        _ = Q' (g'' (τ v)) := rfl
        _ = Q' (τ v) := hg'' (τ v)
        _ = Q v := by
            change Q (τ.symm (τ v)) = Q v
            rw [LinearEquiv.symm_apply_apply]
    have hg₀ : ZS.IsIsom p Q ((ggLinConj τ).symm g') := hisom_back g' hg'
    have hh₀ : ZS.IsIsom p Q ((ggLinConj τ).symm h') := hisom_back h' hh'
    have hmem := hcomm ((ggLinConj τ).symm g') ((ggLinConj τ).symm h') hg₀ hh₀
    have heq : g' * h' * g'⁻¹ * h'⁻¹ =
        (ggLinConj τ) ((ggLinConj τ).symm g' * (ggLinConj τ).symm h'
          * ((ggLinConj τ).symm g')⁻¹ * ((ggLinConj τ).symm h')⁻¹) := by
      have h1 : (ggLinConj τ) ((ggLinConj τ).symm g') = g' :=
        (ggLinConj τ).apply_symm_apply g'
      have h2 : (ggLinConj τ) ((ggLinConj τ).symm h') = h' :=
        (ggLinConj τ).apply_symm_apply h'
      simp only [map_mul, map_inv, h1, h2]
    rw [heq]
    exact Subgroup.mem_map_of_mem (ggLinConj τ).toMonoidHom hmem

theorem ggQ2Prop898NotOrth_of_pieces (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (hF : GGQ2CavOfTBFull) (hH : GGQ2CavOfTBHeart)
    (hT : GGQ2TableBI1Fail) (hI : GGQ2HeartBI1) (hE7 : GGWeylE7NoEichler) :
    GGQ2Prop898NotOrth := by
  intro G _ _ p B Bs x L D J hS hp hI1 _ m hm hEven V _ _ ι hOrth
  subst p
  have hCav := ggQ2_cav_of_tableB hF hH hT hS rfl hI1
  have hAJ : ggAutomizer J Bs ≠ ⊥ := by
    intro hbot
    rw [hbot] at hCav
    simp at hCav
  obtain ⟨labL, hlabQ, hTB, hmark, M, hweyl, hshape, hlast⟩ := hT hS rfl hI1
  have hSst : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hxne : x ≠ 1 := hSst.2.2.1
  have hNT : GGNoTransvection 3 Bs := hS.1.2.2.2.1
  obtain ⟨m', hm'5, hm'⟩ := ggQ2_prop898_m_ge_five (p := 3) hS rfl hI1
  have hmm : m = m' :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 3) (hm.symm.trans hm')
  have h5 : 5 ≤ m := by rw [hmm]; exact hm'5
  have h6 : 6 ≤ m := by
    obtain ⟨k, hk⟩ := hEven
    omega
  have hfin : Module.finrank (ZMod 3) M.V = m :=
    (Nat.pow_right_injective (by norm_num : 2 ≤ 3)
      (hm.symm.trans (ggNG_card_Bs M))).symm
  have h6M : 6 ≤ Module.finrank (ZMod 3) M.V := by rw [hfin]; exact h6
  have hev : Even (Module.finrank (ZMod 3) M.V) := by rw [hfin]; exact hEven
  have hxV0 : M.xV ≠ 0 := by
    intro h
    have h' : M.model (Additive.ofMul (⟨x, M.hx⟩ : ↥Bs)) = 0 := by
      simpa only [GGQ2LDatum.xV] using h
    have h3 : (⟨x, M.hx⟩ : ↥Bs) = 1 := by
      apply Additive.ofMul.injective
      apply M.model.injective
      rw [h']
      simp
    exact hxne (by simpa using congrArg Subtype.val h3)
  let em : V ≃+ M.V := ι.symm.trans M.model
  let τ : V ≃ₗ[ZMod 3] M.V :=
    LinearEquiv.ofBijective (em.toAddMonoidHom.toZModLinearMap 3) em.bijective
  have hτ : ∀ a : Additive ↥Bs, τ (ι a) = M.model a := by
    intro a
    change (em.toAddMonoidHom.toZModLinearMap 3) (ι a) = M.model a
    change em (ι a) = M.model a
    simp [em]
  have hconj : ggLin (p := 3) M.model =
      (ggLinConj τ).toMonoidHom.comp (ggLin (p := 3) ι) := by
    refine MonoidHom.ext fun ψ => ?_
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨a, rfl⟩ := M.model.surjective v
    obtain ⟨b, rfl⟩ := Additive.ofMul.surjective a
    rw [ggLin_apply_ofMul]
    change M.model (Additive.ofMul (ψ b)) =
      ggLinConj τ ((ggLin ι) ψ) (M.model (Additive.ofMul b))
    rw [ggLinConj_apply]
    rw [← hτ (Additive.ofMul b), LinearEquiv.symm_apply_apply, ggLin_apply_ofMul, hτ]
  have hmap : (ggReflGp 3 Bs).map (ggLin (p := 3) M.model) =
      ((ggReflGp 3 Bs).map (ggLin (p := 3) ι)).map (ggLinConj τ).toMonoidHom := by
    rw [hconj]
    exact (Subgroup.map_map (ggReflGp 3 Bs) (ggLinConj τ).toMonoidHom
      (ggLin (p := 3) ι)).symm
  have hOrthM : GGOrthType ((ggReflGp 3 Bs).map (ggLin (p := 3) M.model)) := by
    rw [hmap]
    exact ggNG_orthType_map_conj τ hOrth
  have hrefl_le : ggReflGp 3 Bs ≤ ggAutomizer ⊤ Bs := by
    rw [ggReflGp]
    exact (Subgroup.closure_le (ggAutomizer ⊤ Bs)).mpr (fun φ hφ => hφ.1)
  have hle : ggAutomizer L Bs ≤ ggReflGp 3 Bs := by
    rw [M.automizer_L]
    apply (Subgroup.closure_le (ggReflGp 3 Bs)).mpr
    rintro _ ⟨i, rfl⟩
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · have hL : M.simple i ∈ ggAutomizer L Bs :=
        (by rw [M.automizer_L]; exact Subgroup.subset_closure (Set.mem_range_self i))
      exact ggAutomizer_mono Bs le_top hL
    · have hfx : M.root i (M.coroot i) = 2 := by
        rw [M.pairing i i, M.isCartan.1 i]
        norm_num
      have hlin : ggLin (p := 3) M.model (M.simple i) = reflection hfx :=
        ggLin_eq_reflection (p := 3) M.model hfx (M.simple_apply i)
      exact ggIsReflection_of_eq_reflection (p := 3) (by norm_num : 3 ≠ 2) M.model hfx hlin
  have hRM : ∀ φ ∈ ggAutomizer L Bs, ggLin (p := 3) M.model φ ∈
      (ggReflGp 3 Bs).map (ggLin (p := 3) M.model) :=
    fun φ hφ => Subgroup.mem_map_of_mem _ (hle hφ)
  by_cases hD : M.ShapeD
  · obtain ⟨Q', hQ'nd, hisoM, -⟩ := hOrthM
    exact ggQ2_shapeD_noForm M hD hxV0
      ⟨Q', hQ'nd, fun φ hφ => hisoM (ggLin (p := 3) M.model φ) (hRM φ hφ)⟩
  · by_cases htag : labL.tag = .twE6
    · have hcard : Fintype.card M.Λ = 6 := by
        have h := ggQ2LD_card_lie hweyl hTB
        rw [h]
        simp [GGQ2LieRank, htag]
      rcases hshape with hF | hA | hB | hC | hD'
      · have hdim := ggQ2LD_dim_nonheart M (Or.inl hF)
        rw [hcard] at hdim
        rw [hdim] at hev
        obtain ⟨k, hk⟩ := hev
        omega
      · have hdim := ggQ2LD_dim_nonheart M (Or.inr (Or.inl hA))
        rw [hcard] at hdim
        rw [hdim] at hev
        obtain ⟨k, hk⟩ := hev
        omega
      · exact hI1 (hI hS htag hlabQ hmark M hweyl hB)
      · have hdim := ggQ2LD_dim_nonheart M (Or.inr (Or.inr hC))
        rw [hcard] at hdim
        rw [hdim] at hev
        obtain ⟨k, hk⟩ := hev
        omega
      · exact absurd hD' hD
    · have hVfin : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
      have hVmod : Module.Finite (ZMod 3) M.V := Module.Finite.of_finite
      obtain ⟨Q', hQ'nd, -, hcommM⟩ := hOrthM
      obtain ⟨g, hgΩ, hgx, hgE⟩ := ggOrth_eichler_exists h6M Q' hQ'nd hxV0
      have hOmega_le : ggOmega Q' ≤ (ggReflGp 3 Bs).map (ggLin (p := 3) M.model) := by
        apply (Subgroup.closure_le ((ggReflGp 3 Bs).map (ggLin (p := 3) M.model))).mpr
        rintro c ⟨g₁, g₂, hg₁, hg₂, rfl⟩
        exact hcommM g₁ g₂ hg₁ hg₂
      obtain ⟨ψ, hψrefl, hgψ⟩ := Subgroup.mem_map.mp (hOmega_le hgΩ)
      have hψA : ψ ∈ ggAutomizer ⊤ Bs := hrefl_le hψrefl
      have hlin_fix : ggLin (p := 3) M.model ψ M.xV = M.xV := by
        rw [hgψ]
        exact hgx
      have hfix : ψ ⟨x, M.hx⟩ = ⟨x, M.hx⟩ :=
        (ggLin_fix_iff (p := 3) M.model ψ ⟨x, M.hx⟩).mpr hlin_fix
      have hψx : ψ ⟨x, M.hx⟩ ∈ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) := by
        rw [hfix]
        exact Subgroup.mem_zpowers _
      have hψN : ψ ∈ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs)) :=
        ggQ2_lineStab_normalizes_L hLB hP hS.1 hAJ M.hx hψA hψx
      have hg3 : g ^ 3 = 1 := by
        ext v
        have hsum : g (g v) + g v = -v := add_eq_zero_iff_eq_neg.mp (hgE.2 v)
        have h3v := hgE.2 (g v)
        rw [add_assoc, hsum, add_neg_eq_zero] at h3v
        rw [pow_three, LinearEquiv.mul_apply, LinearEquiv.mul_apply]
        change g (g (g v)) = v
        exact h3v
      have h3 : ψ ^ 3 = 1 := by
        apply ggLin_injective (p := 3) M.model
        rw [map_pow, map_one, hgψ, hg3]
      have hψN3 := ggQ2_threeElt_normW M hweyl hTB htag hshape hxV0 hev h6M hlast hNT ψ
        hψA hψN hlin_fix h3
      exact (ggQ2_W_noEichler M hweyl hTB htag hshape hxV0 hev h6M hlast hE7 ψ hψN3)
        (by rw [hgψ]; exact hgE)

end CFSG.StandardType

end
