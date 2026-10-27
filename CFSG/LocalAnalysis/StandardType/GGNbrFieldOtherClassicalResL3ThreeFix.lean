module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalResL3ThreeSub
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownLinear
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinear

public section

namespace CFSG.StandardType.L3Three

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.FQ CFSG.StandardType.LinearFieldFix
  CFSG.ComponentClassification

theorem false_of_isComponentOf_le_isSolvable {G : Type*} [Group G] {J H S : Subgroup G}
    (hJ : IsComponentOf J H) (hS : Group.IsSolvable S) (hJS : J ≤ S) : False := by
  have hperf : commutator J = ⊤ := hJ.2.2.1
  haveI : Group.IsSolvable J :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hJS)
      (Subgroup.inclusion_injective hJS)
  obtain ⟨n, hn⟩ := (Group.isSolvable_def J).mp this
  have htop : ∀ k, derivedSeries J k = ⊤ := by
    intro k
    induction k with
    | zero => exact derivedSeries_zero J
    | succ k ih => rw [derivedSeries_succ, ih, ← _root_.commutator_def]; exact hperf
  have hbot : (⊤ : Subgroup J) = ⊥ := (htop n).symm.trans hn
  haveI : Subsingleton J := ⟨fun a b => by
    have ha : a ∈ (⊥ : Subgroup J) := hbot ▸ Subgroup.mem_top a
    have hb : b ∈ (⊥ : Subgroup J) := hbot ▸ Subgroup.mem_top b
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb]⟩
  have hs := hJ.2.2.2
  haveI : Subsingleton (J ⧸ Subgroup.center J) := QuotientGroup.mk_surjective.subsingleton
  exact not_nontrivial_iff_subsingleton.mpr this hs.toNontrivial

theorem isSolvable_ggFix_conjAut {K : Type*} [Field K] {B : GL (Fin 3) K}
    (hB : IsReg (B : Matrix (Fin 3) (Fin 3) K)) : Group.IsSolvable (ggFix (conjAut 3 K B)) := by
  set c := CatalogueBHigherLinearAction.slConjugation 3 K B with hc
  set S : Subgroup (SpecialLinearGroup (Fin 3) K) := (ggFix (conjAut 3 K B)).comap (proj 3 K)
    with hS
  have hSz : ∀ s ∈ S, s⁻¹ * c s ∈ Subgroup.center (SpecialLinearGroup (Fin 3) K) := by
    intro s hs
    have h1 : conjAut 3 K B (proj 3 K s) = proj 3 K s := hs
    rw [conjAut_proj] at h1
    rw [← scalars_eq_center]
    exact proj_eq_proj_iff.mp h1.symm
  let χ : S →* Subgroup.center (SpecialLinearGroup (Fin 3) K) :=
    { toFun := fun s => ⟨(s : SpecialLinearGroup (Fin 3) K)⁻¹ * c s, hSz s s.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun s t => by
        apply Subtype.ext
        have hz := Subgroup.mem_center_iff.mp (hSz s s.2)
        simp only [Subgroup.coe_mul, map_mul, _root_.mul_inv_rev]
        calc (t : SpecialLinearGroup (Fin 3) K)⁻¹ * (s : SpecialLinearGroup (Fin 3) K)⁻¹ *
              (c s * c t)
            = (t : SpecialLinearGroup (Fin 3) K)⁻¹ *
                ((s : SpecialLinearGroup (Fin 3) K)⁻¹ * c s) * c t := by group
          _ = ((s : SpecialLinearGroup (Fin 3) K)⁻¹ * c s) *
                (t : SpecialLinearGroup (Fin 3) K)⁻¹ * c t := by rw [hz]
          _ = ((s : SpecialLinearGroup (Fin 3) K)⁻¹ * c s) *
                ((t : SpecialLinearGroup (Fin 3) K)⁻¹ * c t) := by group }
  have hcomm : ∀ u : χ.ker, Commute (((u : S) : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) (B : Matrix (Fin 3) (Fin 3) K) := by
    intro u
    have h1 : ((u : S) : SpecialLinearGroup (Fin 3) K)⁻¹ * c (u : S) = 1 :=
      congrArg Subtype.val u.2
    have h2 : c (u : S) = (u : S) := (inv_mul_eq_one.mp h1).symm
    have h3 := congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h2
    simp only [hc, CatalogueBHigherLinearAction.slConjugation_matrix] at h3
    have h4 : (B : Matrix (Fin 3) (Fin 3) K) * (((u : S) : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = (((u : S) : SpecialLinearGroup (Fin 3) K) :
          Matrix (Fin 3) (Fin 3) K) * (B : Matrix (Fin 3) (Fin 3) K) := by
      calc (B : Matrix (Fin 3) (Fin 3) K) * (((u : S) : SpecialLinearGroup (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K)
          = (B : Matrix (Fin 3) (Fin 3) K) * (((u : S) : SpecialLinearGroup (Fin 3) K) :
              Matrix (Fin 3) (Fin 3) K) * ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
                (B : Matrix (Fin 3) (Fin 3) K) := by
            rw [Matrix.mul_assoc _ ((B⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
              Units.inv_mul, Matrix.mul_one]
        _ = _ := by rw [h3]
    exact h4.symm
  have hker : ∀ s t : χ.ker, s * t = t * s := by
    intro s t
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact (hB.commute (hcomm s) (hcomm t)).eq
  haveI : Group.IsSolvable χ.ker := Group.isSolvable_of_comm hker
  haveI : Group.IsSolvable (Subgroup.center (SpecialLinearGroup (Fin 3) K)) :=
    Group.isSolvable_of_comm fun a b => Subtype.ext ((Subgroup.mem_center_iff.mp a.2) b).symm
  haveI : Group.IsSolvable S :=
    Group.isSolvable_of_ker_le_range χ.ker.subtype χ (by rw [Subgroup.range_subtype])
  have hmap : S.map (proj 3 K) = ggFix (conjAut 3 K B) :=
    Subgroup.map_comap_eq_self_of_surjective (proj_surjective 3 K) _
  rw [← hmap]
  exact Group.isSolvable_of_surjective (f := (proj 3 K).subgroupMap S)
    ((proj 3 K).subgroupMap_surjective S)

variable {K : Type} [Field K]

theorem toGL_slKerEquiv {d : ℕ} (h : LargeEvenSLGroup (Fin d) K) :
    SpecialLinearGroup.toGL (TypeA.slKerEquiv d K h) = (h : GL (Fin d) K) :=
  Units.ext rfl

theorem ggFixNoCompOn_linear [Finite K] {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m)
    {σ : K ≃+* K} {f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 3) K))} (hf : Induced σ f) :
    GGFixNoCompOn (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 3) K)) Set.univ) f
      ((subfieldEquiv le_rfl hm hK hf).symm.trans (TypeA.recipeEquiv 3 (fixF σ)))
      (conjAut 3 (fixF σ) '' {B | IsReg (B : Matrix (Fin 3) (Fin 3) (fixF σ))}) := by
  intro φ hφ hcomm φ₀ hφ₀ hrestr J hJ
  obtain ⟨B, hBreg, rfl⟩ := hφ₀
  set e := TypeA.recipeEquiv 3 K with he
  set e₀ := TypeA.recipeEquiv 3 (fixF σ) with he₀
  set θ := (subfieldEquiv le_rfl hm hK hf).symm.trans e₀ with hθdef
  set ι : fixF σ →+* K := (fixF σ).subtype with hι
  set B' : GL (Fin 3) K := Matrix.GeneralLinearGroup.map ι B with hB'
  set ψB : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 3) K)) :=
    (MulAut.congr e).symm (conjAut 3 K B') with hψBdef
  have hψB : MulAut.congr e ψB = conjAut 3 K B' := MulEquiv.apply_symm_apply _ _
  have hψBapp : ∀ r, e (ψB r) = conjAut 3 K B' (e r) := by
    intro r
    rw [← hψB, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  have hmemD : ∀ g : LargeEvenSLGroup (Fin 3) (fixF σ), subfieldHom σ g ∈ ggFixDer f := by
    intro g
    rw [← range_subfieldHom le_rfl hm hK hf]
    exact ⟨g, rfl⟩
  have hθ : ∀ g : LargeEvenSLGroup (Fin 3) (fixF σ),
      θ ⟨subfieldHom σ g, hmemD g⟩ = proj 3 (fixF σ) (TypeA.slKerEquiv 3 (fixF σ) g) := by
    intro g
    rw [hθdef, MulEquiv.trans_apply]
    have h1 : (subfieldEquiv le_rfl hm hK hf).symm ⟨subfieldHom σ g, hmemD g⟩ =
        QuotientGroup.mk g := by
      rw [MulEquiv.symm_apply_eq]
      exact Subtype.ext (coe_subfieldEquiv_mk le_rfl hm hK hf g).symm
    rw [h1]
    exact TypeA.recipeEquiv_mk g
  have hagree : ∀ g, φ (subfieldHom σ g) = ψB (subfieldHom σ g) := by
    intro g
    set g' : LargeEvenSLGroup (Fin 3) (fixF σ) := (TypeA.slKerEquiv 3 (fixF σ)).symm
      (CatalogueBHigherLinearAction.slConjugation 3 (fixF σ) B (TypeA.slKerEquiv 3 (fixF σ) g))
      with hg'
    have h1 : φ (subfieldHom σ g) = subfieldHom σ g' := by
      have h2 := hrestr (subfieldHom σ g) (hmemD g)
      rw [hθ, conjAut_proj] at h2
      have h3 : θ ⟨φ (subfieldHom σ g), ggFixDer_map_mem hcomm (hmemD g)⟩ =
          θ ⟨subfieldHom σ g', hmemD g'⟩ := by
        rw [h2, hθ, hg', MulEquiv.apply_symm_apply]
      exact congrArg Subtype.val (θ.injective h3)
    rw [h1]
    have hg'GL : ((g' : LargeEvenSLGroup (Fin 3) (fixF σ)) : GL (Fin 3) (fixF σ)) =
        B * (g : GL (Fin 3) (fixF σ)) * B⁻¹ := by
      rw [hg']
      change SpecialLinearGroup.toGL (CatalogueBHigherLinearAction.slConjugation 3 (fixF σ) B
        (TypeA.slKerEquiv 3 (fixF σ) g)) = _
      rw [CatalogueBHigherLinearAction.toGL_slConjugation, toGL_slKerEquiv]
    have h4 : e (ψB (subfieldHom σ g)) = e (subfieldHom σ g') := by
      rw [hψBapp]
      change conjAut 3 K B' (e (LargeEvenProjMk _ (subfieldInclusion σ g))) =
        e (LargeEvenProjMk _ (subfieldInclusion σ g'))
      rw [TypeA.recipeEquiv_mk, TypeA.recipeEquiv_mk, conjAut_proj]
      congr 1
      apply SpecialLinearGroup.toGL_injective
      rw [CatalogueBHigherLinearAction.toGL_slConjugation, toGL_slKerEquiv, toGL_slKerEquiv,
        coe_subfieldInclusion, coe_subfieldInclusion, hg'GL, map_mul, map_mul, map_inv]
    exact (e.injective h4).symm
  have hφψ : φ = ψB := by
    have hψI : ψB ∈ RecipeFieldLinear.recI 3 K := by
      rw [RecipeFieldLinear.mem_recI_iff, hψB]
      exact conjAut_mem_linearAutGroup _
    have hφI : φ ∈ RecipeFieldLinear.recI 3 K := by
      rw [← SetLike.mem_coe, RecipeFieldLinear.coe_recI]
      exact hφ
    have hI : ψB⁻¹ * φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 3) K))
        Set.univ := by
      rw [← RecipeFieldLinear.coe_recI]
      exact (RecipeFieldLinear.recI 3 K).mul_mem ((RecipeFieldLinear.recI 3 K).inv_mem hψI) hφI
    have h1 := eq_one_of_fixes_subfield le_rfl σ hI fun g => by
      rw [MulAut.mul_apply, hagree]
      exact ψB.symm_apply_apply _
    exact (inv_mul_eq_one.mp h1).symm
  have hfix : ∀ r, r ∈ ggFix ψB ↔ e r ∈ ggFix (conjAut 3 K B') := by
    intro r
    change ψB r = r ↔ conjAut 3 K B' (e r) = e r
    rw [← hψBapp]
    exact e.injective.eq_iff.symm
  let j : ggFix ψB →* ggFix (conjAut 3 K B') :=
    { toFun := fun r => ⟨e (r : LargeEvenProj (LargeEvenSLGroup (Fin 3) K)), (hfix r).mp r.2⟩
      map_one' := Subtype.ext (map_one e)
      map_mul' := fun r s => Subtype.ext (map_mul e (r : LargeEvenProj (LargeEvenSLGroup (Fin 3) K))
        (s : LargeEvenProj (LargeEvenSLGroup (Fin 3) K))) }
  have hreg' : IsReg (B' : Matrix (Fin 3) (Fin 3) K) := hBreg.map ι
  haveI := isSolvable_ggFix_conjAut hreg'
  haveI : Group.IsSolvable (ggFix ψB) :=
    Group.isSolvable_of_isSolvable_injective (f := j) fun r s h =>
      Subtype.ext (e.injective (congrArg Subtype.val h))
  rw [hφψ] at hJ
  exact false_of_isComponentOf_le_isSolvable hJ this hJ.1

theorem ggFixGeom_trans {R : Type} [Group R] {I : Set (MulAut R)} {x : MulAut R} {R₀ R₀' : Type}
    [Group R₀] [Group R₀'] {I₀ : Set (MulAut R₀)} {I₀' : Set (MulAut R₀')}
    {θ₀ : ggFixDer x ≃* R₀} (e : R₀ ≃* R₀') (hI : ∀ φ ∈ I₀, MulAut.congr e φ ∈ I₀')
    (h : GGFixGeom I x I₀ θ₀) : GGFixGeom I x I₀' (θ₀.trans e) := by
  refine ⟨fun φ hφ hc => ?_, h.2⟩
  obtain ⟨φ₀, hφ₀, hφ₀eq⟩ := h.1 φ hφ hc
  refine ⟨MulAut.congr e φ₀, hI φ₀ hφ₀, fun g hg => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hφ₀eq g hg, MulAut.congr_apply,
    MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

theorem ggFixDataKX_linear_of_sub [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (h1 : 1 ≤ n / 3) {Kp : ℕ → Prop}
    (hsub : ∀ (K₀ : Type) [Field K₀] [Finite K₀] [CharP K₀ 2], Nat.card K₀ = 2 ^ (n / 3) →
      GGTorusNoLineTwoKX 3 Kp (projectiveSL 3 K₀) (Set.range (conjAut 3 K₀))
        (conjAut 3 K₀ '' {B | IsReg (B : Matrix (Fin 3) (Fin 3) K₀)}))
    {f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 3) K))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 3) K)))
    (hord : orderOf f = 3) :
    GGFixDataKX 3 Kp (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 3) K))
      Set.univ) f := by
  obtain ⟨σ, hσ⟩ := exists_induced hf
  have hσord : orderOf σ = 3 :=
    (orderOf_eq_of_mk_matAct (by norm_num) (slMapStable 3 K) hσ).trans hord
  obtain ⟨-, hcard⟩ := card_fixedPoints_field hn hK σ
  have hk : Nat.card (fixF σ) = 2 ^ (n / 3) := by rw [card_fixF, hcard, hσord]
  haveI : CharP (fixF σ) 2 := NbrInnerMore.charP_two_of_card_pow h1 hk
  set e₀ := TypeA.recipeEquiv 3 (fixF σ) with he₀
  refine ⟨projectiveSL 3 (fixF σ), inferInstance, Set.range (conjAut 3 (fixF σ)),
    conjAut 3 (fixF σ) '' {B | IsReg (B : Matrix (Fin 3) (Fin 3) (fixF σ))},
    (subfieldEquiv le_rfl hn hK hσ).symm.trans e₀, ?_, ?_, ?_, ?_, hsub _ hk, ?_⟩
  · haveI := isSimpleGroup_proj le_rfl (fixF σ)
    exact e₀.symm.isSimpleGroup
  · obtain ⟨a, b, hab⟩ := exists_noncomm_proj le_rfl (fixF σ)
    exact ⟨e₀ a, e₀ b, fun h => hab (e₀.injective (by rw [map_mul, map_mul, h]))⟩
  · exact ggFixGeom_trans e₀ (fun _ hφ => TypeA.congr_recipeEquiv_mem hφ)
      (ggFixGeom_linear le_rfl hn hK hσ)
  · exact TypeA.ggTorusLift_zero (TypeA.two_dvd_card_projectiveSL (by norm_num))
  · exact ggFixNoCompOn_linear hn hK hσ

theorem ggFixDataKX_linear [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (h3 : 3 ∣ 2 ^ (n / 3) - 1) (h1 : 1 ≤ n / 3) (h2 : n / 3 ≠ 1) (h4 : n / 3 ≠ 2)
    (Kp : ℕ → Prop) {f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin 3) K))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 3) K)))
    (hord : orderOf f = 3) :
    GGFixDataKX 3 Kp (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 3) K))
      Set.univ) f := by
  refine ggFixDataKX_linear_of_sub hn hK h1 (fun K₀ _ _ _ hk => ?_) hf hord
  refine ggTorusNoLineTwoKX_projectiveSL (by rwa [hk]) ?_ ?_ Kp
  · rw [hk]
    intro h
    apply h2
    have h' : 2 ^ (n / 3) = 2 ^ 1 := by rw [h, pow_one]
    exact Nat.pow_right_injective le_rfl h'
  · rw [hk]
    intro h
    apply h4
    have h' : 2 ^ (n / 3) = 2 ^ 2 := by rw [h]; norm_num
    exact Nat.pow_right_injective le_rfl h'

end CFSG.StandardType.L3Three

end
