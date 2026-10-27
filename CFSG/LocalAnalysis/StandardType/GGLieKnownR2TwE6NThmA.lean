module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6NCoord

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.Blueprint.Chevalley
open scoped commutatorElement

private theorem teNThmA_cartan_mul_alpha_rat (l : Fin (Tag.rank .F4)) :
    (∑ k, (Tag.cartan .F4 l k : ℚ) * (twE6Alpha k : ℚ)) =
      if l = twE6Last then 1 else 0 := by
  fin_cases l <;> decide +kernel

private theorem teNThmA_level_le_two :
    ∀ v ∈ rootFinset Tag.F4, v twE6Last ≤ 2 := by decide +kernel

private theorem teNThmA_level_pos_of_positive :
    ∀ v ∈ rootFinset Tag.F4, 0 < (∑ i, v i) → 0 ≤ v twE6Last := by decide +kernel

private theorem teNThmA_alpha_level : twE6Alpha twE6Last = 2 := by decide +kernel

private theorem teNThmA_alpha_isRoot : IsRoot .F4 twE6Alpha :=
  mem_rootFinset.1 (by decide +kernel)

private theorem teNThmA_linDep_minors :
    ∀ v ∈ rootFinset Tag.F4, ∀ w ∈ rootFinset Tag.F4,
      (∀ i j : Fin (Tag.rank .F4), v i * w j - v j * w i = 0) → v = w ∨ v = -w := by
  decide +kernel

private theorem teNThmA_linIndepPair_of_ne_neg {v w : Fin (Tag.rank .F4) → ℤ}
    (hv : v ∈ rootFinset Tag.F4) (hw : w ∈ rootFinset Tag.F4)
    (h1 : v ≠ w) (h2 : v ≠ -w) : LinIndepPair v w := by
  by_contra h
  rw [LinIndepPair] at h
  push Not at h
  obtain ⟨a, b, hab, hne⟩ := h
  have hmin : ∀ i j : Fin (Tag.rank .F4), v i * w j - v j * w i = 0 := by
    intro i j
    have hi : a * v i + b * w i = 0 := by
      have h := congrFun hab i
      simp only [Pi.add_apply, Pi.smul_apply, zsmul_eq_mul] at h
      simpa using h
    have hj : a * v j + b * w j = 0 := by
      have h := congrFun hab j
      simp only [Pi.add_apply, Pi.smul_apply, zsmul_eq_mul] at h
      simpa using h
    rcases eq_or_ne a 0 with ha | ha
    · have hb : b ≠ 0 := by rintro rfl; exact hne ha rfl
      have hm : b * (v i * w j - v j * w i) = 0 := by
        linear_combination (-(v j)) * hi + (v i) * hj
      exact (mul_eq_zero.mp hm).resolve_left hb
    · have hm : a * (v i * w j - v j * w i) = 0 := by
        linear_combination (w j) * hi - (w i) * hj
      exact (mul_eq_zero.mp hm).resolve_left ha
  rcases teNThmA_linDep_minors v hv w hw hmin with h | h
  · exact h1 h
  · exact h2 h

private theorem teNThmA_form_alpha_eq
    (v : Fin (Tag.rank .F4) → ℤ) :
    form (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) (toRat v) (toRat twE6Alpha) =
      symmetrizer (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) twE6Last *
        (v twE6Last : ℚ) := by
  have hsingle : ∀ l : Fin (Tag.rank .F4),
      form (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) (toRat twE6Alpha) (Pi.single l 1) =
        symmetrizer (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) l *
          (if l = twE6Last then 1 else 0) := by
    intro l
    rw [form_single_right]
    congr 1
    simp only [toRat_apply]
    exact teNThmA_cartan_mul_alpha_rat l
  calc form (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) (toRat v) (toRat twE6Alpha)
      = form (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) (toRat twE6Alpha) (toRat v) :=
        form_comm _ _ _
    _ = ∑ l, (toRat v) l * form (CFSG.LieType.Chevalley.isFiniteType_cartan .F4)
          (toRat twE6Alpha) (Pi.single l 1) := form_eq_sum _ _ _
    _ = ∑ l, (v l : ℚ) * (symmetrizer (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) l *
          (if l = twE6Last then 1 else 0)) := by
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [hsingle l]
        simp only [toRat_apply]
    _ = symmetrizer (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) twE6Last *
          (v twE6Last : ℚ) := by
        rw [Finset.sum_eq_single twE6Last]
        · simp [mul_comm]
        · intro l _ hl; simp [hl]
        · intro h; exact absurd (Finset.mem_univ twE6Last) h

private theorem teNThmA_weylAction_last_eq_of_fix_alpha
    {k : Type} [Field k] (θ : k →+* k)
    (w : twE6W k θ)
    (hw : weylAction (twistedDatum k θ).isFiniteType w twE6Alpha = twE6Alpha)
    (γ : Fin (Tag.rank .F4) → ℤ) :
    (weylAction (twistedDatum k θ).isFiniteType w γ) twE6Last = γ twE6Last := by
  change (weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) w γ) twE6Last =
    γ twE6Last
  have hw' : weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) w twE6Alpha =
      twE6Alpha := hw
  have hform :=
    form_weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) w γ twE6Alpha
  rw [hw'] at hform
  rw [teNThmA_form_alpha_eq (weylAction (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) w γ),
    teNThmA_form_alpha_eq γ] at hform
  have hd : symmetrizer (CFSG.LieType.Chevalley.isFiniteType_cartan .F4) twE6Last ≠ 0 :=
    ne_of_gt (symmetrizer_pos _ _)
  exact Int.cast_injective (mul_left_cancel₀ hd hform)

private theorem teNThmA_openCone_le_rad
    {k : Type} [Field k] (θ : k →+* k)
    {δ γ : Fin (Tag.rank .F4) → ℤ}
    (hδ : IsRoot .F4 δ) (hδp : 0 < ht δ)
    (hγl : 1 ≤ γ twE6Last) :
    (⨆ ε ∈ openCone {β : Fin (Tag.rank .F4) → ℤ | IsRoot .F4 β} δ γ,
      twistedRootGroup k θ ε) ≤ twE6Rad θ := by
  refine iSup₂_le fun ε hε => ?_
  obtain ⟨hεroot, a, b, ha, hb, rfl⟩ := hε
  refine rootGroup_le_ggSub (D := twistedDatum k θ)
    (S := {γ | γ ∈ (twistedDatum k θ).roots ∧ 1 ≤ γ twE6Last})
    ⟨by rw [twistedDatum_roots]; exact hεroot, ?_⟩
  have hδlev : 0 ≤ δ twE6Last :=
    teNThmA_level_pos_of_positive δ (mem_rootFinset.2 hδ) hδp
  have hlev : (a • δ + b • γ) twE6Last =
      (a : ℤ) * δ twE6Last + (b : ℤ) * γ twE6Last := by
    simp only [Pi.add_apply, Pi.smul_apply]
    rw [nsmul_eq_mul, nsmul_eq_mul]
  rw [hlev]
  have ha1 : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
  have hb0 : (0 : ℤ) ≤ (b : ℤ) := by positivity
  nlinarith

private theorem teNThmA_borel_le_normalizer_rad
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    twE6Borel θ ≤ Subgroup.normalizer ((twE6Rad θ : Subgroup (fixedGroup k θ)) : Set _) := by
  have hct := twE6_hct θ hθ
  change (⨆ i, hHat k θ i) ⊔ posUnipotent (twistedDatum k θ) ≤ _
  refine sup_le ?_ ?_
  · refine iSup_le fun i => Subgroup.le_normalizer_iff.2 fun t ht x hx => ?_
    exact conj_mem_of_forall_mem (fun γ hγ z hz =>
      rootGroup_le_ggSub hγ (hct.H_conj_mem i γ hγ.1 t ht z hz)) hx
  · refine iSup₂_le fun δ hδ => Subgroup.le_normalizer_iff.2 fun x hx z hz => ?_
    refine conj_mem_of_forall_mem (fun γ hγ y hy => ?_) hz
    rcases eq_or_ne γ δ with rfl | hne
    · exact rootGroup_le_ggSub hγ (mul_mem (mul_mem hx hy) (inv_mem hx))
    · have hδroot : IsRoot .F4 δ := isRoot_of_mem_twistedDatum_roots θ hδ.1
      have hγroot : IsRoot .F4 γ := isRoot_of_mem_twistedDatum_roots θ hγ.1
      have hδlev : 0 ≤ δ twE6Last :=
        teNThmA_level_pos_of_positive δ (mem_rootFinset.2 hδroot) hδ.2
      have hne_neg : γ ≠ -δ := by
        intro h
        have hγl : 1 ≤ γ twE6Last := hγ.2
        have hlast : γ twE6Last = -δ twE6Last := by rw [h]; rfl
        omega
      have hlin : LinIndepPair γ δ :=
        teNThmA_linIndepPair_of_ne_neg (mem_rootFinset.2 hγroot) (mem_rootFinset.2 hδroot)
          hne hne_neg
      have hlin' : LinIndepPair δ γ :=
        fun a b hab => (hlin b a (by rw [add_comm]; exact hab)).symm
      have hcu := commutator_mem_iSup_twistedRootGroup hlin' hx hy
      have hmem : ⁅x, y⁆ ∈ twE6Rad θ :=
        teNThmA_openCone_le_rad θ hδroot hδ.2 hγ.2 hcu
      have hyQ : y ∈ twE6Rad θ := rootGroup_le_ggSub hγ hy
      rw [show x * y * x⁻¹ = ⁅x, y⁆ * y by rw [commutatorElement_def]; group]
      exact mul_mem hmem hyQ

private theorem teNThmA_N_mem_normalizer_rad
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    (w : twE6W k θ)
    (hw : weylAction (twistedDatum k θ).isFiniteType w twE6Alpha = twE6Alpha) :
    twE6N θ hθ w ∈ Subgroup.normalizer ((twE6Rad θ : Subgroup (fixedGroup k θ)) : Set _) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hlast := teNThmA_weylAction_last_eq_of_fix_alpha θ w hw
  have hS : ∀ γ : Fin (Tag.rank .F4) → ℤ,
      γ ∈ {γ | γ ∈ (twistedDatum k θ).roots ∧ 1 ≤ γ twE6Last} ↔
        weylAction (twistedDatum k θ).isFiniteType w γ ∈
          {γ | γ ∈ (twistedDatum k θ).roots ∧ 1 ≤ γ twE6Last} := by
    intro γ
    constructor
    · intro hγ
      exact ⟨weylAction_mem_roots (twistedDatum k θ).isFiniteType w hγ.1,
        by rw [hlast γ]; exact hγ.2⟩
    · intro hγ
      refine ⟨?_, ?_⟩
      · have hmem := weylAction_mem_roots (twistedDatum k θ).isFiniteType w⁻¹ hγ.1
        have heq : weylAction (twistedDatum k θ).isFiniteType w⁻¹
            (weylAction (twistedDatum k θ).isFiniteType w γ) = γ :=
          weylAction_inv_apply_apply (twistedDatum k θ).isFiniteType w γ
        rwa [heq] at hmem
      · rw [← hlast γ]; exact hγ.2
  have hmap : ∀ γ ∈ {γ | γ ∈ (twistedDatum k θ).roots ∧ 1 ≤ γ twE6Last},
      ((twistedDatum k θ).rootGroup γ).map (MulAut.conj (twE6N θ hθ w)).toMonoidHom =
        (twistedDatum k θ).rootGroup (weylAction (twistedDatum k θ).isFiniteType w γ) :=
    fun γ hγ => actsAs_nrep (twE6_hct θ hθ) w γ hγ.1
  change (⨆ γ ∈ {γ | γ ∈ (twistedDatum k θ).roots ∧ 1 ≤ γ twE6Last},
      (twistedDatum k θ).rootGroup γ).map (MulAut.conj (twE6N θ hθ w)).toMonoidHom =
    ⨆ γ ∈ {γ | γ ∈ (twistedDatum k θ).roots ∧ 1 ≤ γ twE6Last}, (twistedDatum k θ).rootGroup γ
  simp only [Subgroup.map_iSup]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun γ => ?_
    refine iSup_le fun hγ => ?_
    rw [hmap γ hγ]
    exact le_iSup₂_of_le (f := fun δ (_ : δ ∈ {γ | γ ∈ (twistedDatum k θ).roots ∧
        1 ≤ γ twE6Last}) => (twistedDatum k θ).rootGroup δ)
      (weylAction (twistedDatum k θ).isFiniteType w γ) ((hS γ).1 hγ) le_rfl
  · refine iSup₂_le fun δ hδ => ?_
    have hpre : weylAction (twistedDatum k θ).isFiniteType w⁻¹ δ ∈
        {γ | γ ∈ (twistedDatum k θ).roots ∧ 1 ≤ γ twE6Last} := by
      apply (hS (weylAction (twistedDatum k θ).isFiniteType w⁻¹ δ)).2
      rwa [weylAction_apply_inv_apply]
    exact le_iSup₂_of_le
      (f := fun γ (_ : γ ∈ {γ | γ ∈ (twistedDatum k θ).roots ∧ 1 ≤ γ twE6Last}) =>
        ((twistedDatum k θ).rootGroup γ).map (MulAut.conj (twE6N θ hθ w)).toMonoidHom)
      (weylAction (twistedDatum k θ).isFiniteType w⁻¹ δ) hpre
      (by rw [hmap (weylAction (twistedDatum k θ).isFiniteType w⁻¹ δ) hpre,
        weylAction_apply_inv_apply])

private theorem teNThmA_weylAction_fix_alpha_of_conj
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {w : twE6W k θ} {b₁ b₂ : fixedGroup k θ}
    (hb₁ : b₁ ∈ twE6Borel θ) (hb₂ : b₂ ∈ twE6Borel θ)
    (hx : b₁ * twE6N θ hθ w * b₂ ∈ twE6NA θ) :
    weylAction (twistedDatum k θ).isFiniteType w twE6Alpha = twE6Alpha := by
  have hαmem : twE6Alpha ∈ (twistedDatum k θ).roots := by
    rw [twistedDatum_roots]; exact teNThmA_alpha_isRoot
  have hRAne : twE6RA θ ≠ ⊥ := (twistedDatum_steinbergExtras θ hθ).ne_bot twE6Alpha hαmem
  have hYVa : twE6Cj b₂ (twE6RA θ) ≤ twE6Va θ := twE6_conj_alpha_le_Va θ hθ hb₂
  have hYV : twE6Cj b₂ (twE6RA θ) ⊓ twE6V θ = ⊥ := twE6_conj_alpha_inf_V θ hθ hb₂
  obtain ⟨z₀, hz₀, hz₀1⟩ : ∃ z₀ ∈ twE6RA θ, z₀ ≠ 1 := by
    by_contra h
    push Not at h
    exact hRAne (le_antisymm (fun x hx => Subgroup.mem_bot.2 (h x hx)) bot_le)
  have hyY : b₂ * z₀ * b₂⁻¹ ∈ twE6Cj b₂ (twE6RA θ) := Subgroup.mem_map.2 ⟨z₀, hz₀, rfl⟩
  have hy1 : b₂ * z₀ * b₂⁻¹ ≠ 1 := by
    intro h
    apply hz₀1
    have := congrArg (fun t => b₂⁻¹ * t * b₂) h
    simpa [mul_assoc] using this
  have hyV : b₂ * z₀ * b₂⁻¹ ∉ twE6V θ := by
    intro hyV'
    have hmem : b₂ * z₀ * b₂⁻¹ ∈ twE6Cj b₂ (twE6RA θ) ⊓ twE6V θ := ⟨hyY, hyV'⟩
    rw [hYV, Subgroup.mem_bot] at hmem
    exact hy1 hmem
  have hyVa : b₂ * z₀ * b₂⁻¹ ∈ twE6Va θ := hYVa hyY
  obtain ⟨z, hzX, v, hvV, hyzv⟩ := (mem_twE6Va_iff θ hθ).1 hyVa
  have hz1 : z ≠ 1 := by
    intro hz
    apply hyV
    rw [hyzv, hz, one_mul]
    exact hvV
  have hmem : twE6N θ hθ w * (z * v) * (twE6N θ hθ w)⁻¹ ∈ twE6Va θ := by
    rw [← hyzv]
    have hx_conj : b₁ * (twE6N θ hθ w * (b₂ * z₀ * b₂⁻¹) * (twE6N θ hθ w)⁻¹) * b₁⁻¹ ∈
        twE6RA θ := by
      have h := (Subgroup.mem_normalizer_iff.1 hx z₀).1 hz₀
      rwa [show (b₁ * twE6N θ hθ w * b₂) * z₀ * (b₁ * twE6N θ hθ w * b₂)⁻¹ =
        b₁ * (twE6N θ hθ w * (b₂ * z₀ * b₂⁻¹) * (twE6N θ hθ w)⁻¹) * b₁⁻¹ by group] at h
    have hmem' : twE6N θ hθ w * (b₂ * z₀ * b₂⁻¹) * (twE6N θ hθ w)⁻¹ ∈
        twE6Cj b₁⁻¹ (twE6RA θ) :=
      Subgroup.mem_map.2 ⟨_, hx_conj, by
        change b₁⁻¹ * (b₁ * (twE6N θ hθ w * (b₂ * z₀ * b₂⁻¹) * (twE6N θ hθ w)⁻¹) * b₁⁻¹) * b₁ =
          twE6N θ hθ w * (b₂ * z₀ * b₂⁻¹) * (twE6N θ hθ w)⁻¹
        group⟩
    exact (twE6_conj_alpha_le_Va θ hθ (inv_mem hb₁)) hmem'
  exact twE6_weyl_fix_alpha_of_conj_mem θ hθ w hzX hz1 hvV hmem

private theorem teNThmA_rootGroup_le_normalizer_alpha
    {k : Type} [Field k] (θ : k →+* k)
    {γ : Fin (Tag.rank .F4) → ℤ}
    (hγ : γ ∈ (twistedDatum k θ).roots) (hγl : 1 ≤ γ twE6Last) :
    (twistedDatum k θ).rootGroup γ ≤ twE6NA θ := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx y hy
  rcases eq_or_ne γ twE6Alpha with rfl | hne
  · exact mul_mem (mul_mem hx hy) (inv_mem hx)
  · have hγroot : IsRoot .F4 γ := isRoot_of_mem_twistedDatum_roots θ hγ
    have hαmem : twE6Alpha ∈ (twistedDatum k θ).roots := by
      rw [twistedDatum_roots]; exact teNThmA_alpha_isRoot
    have hne_neg : γ ≠ -twE6Alpha := by
      intro h
      have hlast : γ twE6Last = -twE6Alpha twE6Last := by rw [h]; rfl
      have := teNThmA_alpha_level
      omega
    have hlin : LinIndepPair γ twE6Alpha :=
      teNThmA_linIndepPair_of_ne_neg (mem_rootFinset.2 hγroot)
        (mem_rootFinset.2 teNThmA_alpha_isRoot) hne hne_neg
    have hcu := commutator_mem_iSup_twistedRootGroup hlin hx hy
    have hempty : openCone {β : Fin (Tag.rank .F4) → ℤ | IsRoot .F4 β} γ twE6Alpha = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro ε hε
      obtain ⟨hεroot, a, b, ha, hb, rfl⟩ := hε
      have hle := teNThmA_level_le_two (a • γ + b • twE6Alpha) (mem_rootFinset.2 hεroot)
      have hlev : (a • γ + b • twE6Alpha) twE6Last =
          (a : ℤ) * γ twE6Last + (b : ℤ) * twE6Alpha twE6Last := by
        simp only [Pi.add_apply, Pi.smul_apply]
        rw [nsmul_eq_mul, nsmul_eq_mul]
      rw [hlev, teNThmA_alpha_level] at hle
      have ha1 : (1 : ℤ) ≤ (a : ℤ) := by exact_mod_cast ha
      have hb1 : (1 : ℤ) ≤ (b : ℤ) := by exact_mod_cast hb
      nlinarith
    rw [hempty, iSup_emptyset, Subgroup.mem_bot] at hcu
    rw [show x * y * x⁻¹ = ⁅x, y⁆ * y by rw [commutatorElement_def]; group, hcu, one_mul]
    exact hy

theorem twE6_normalizer_alpha_le
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    twE6NA θ ≤
      Subgroup.normalizer ((twE6Rad θ : Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ)) := by
  intro x hx
  obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩ :=
    exists_mem_bruhatCell (twE6_hct θ hθ) (twistedDatum_steinbergExtras θ hθ) x
  have hb1N := teNThmA_borel_le_normalizer_rad θ hθ hb₁
  have hb2N := teNThmA_borel_le_normalizer_rad θ hθ hb₂
  have hfix := teNThmA_weylAction_fix_alpha_of_conj θ hθ hb₁ hb₂ hx
  have hnwN := teNThmA_N_mem_normalizer_rad θ hθ w hfix
  exact mul_mem (mul_mem hb1N hnwN) hb2N

theorem twE6Rad_le_normalizer_alpha
    {k : Type} [Field k] (θ : k →+* k) :
    twE6Rad θ ≤ twE6NA θ := by
  refine iSup₂_le fun γ hγ => ?_
  exact teNThmA_rootGroup_le_normalizer_alpha θ hγ.1 hγ.2

end CFSG.StandardType.LieKnownR2.Short
