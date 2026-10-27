module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2TwE6NDefs

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley
open scoped commutatorElement

private def teOpp_w0lword : List (Fin (Tag.rank .F4)) :=
  [nf 0, nf 1, nf 2, nf 0, nf 1, nf 2, nf 0, nf 1, nf 2]

private def teOpp_vword : List (Fin (Tag.rank .F4)) :=
  [nf 2, nf 0, nf 1, nf 2, nf 0, nf 1, nf 2, nf 0, nf 1, nf 2]

private abbrev teOpp_refl :
    Fin (Tag.rank .F4) → (Fin (Tag.rank .F4) → ℤ) →+ (Fin (Tag.rank .F4) → ℤ) :=
  fun i => (reflection (Tag.cartan .F4) i).toAddMonoidHom

private abbrev teOpp_last
    {k : Type} [Field k] (θ : k →+* k) : Fin (twistedDatum k θ).rank := twE6Last

private def teOpp_P0
    {k : Type} [Field k] (θ : k →+* k) : Set (Fin (twistedDatum k θ).rank → ℤ) :=
  {γ | γ ∈ (twistedDatum k θ).roots ∧ 0 < ht γ ∧ γ (teOpp_last θ) = 0}

private def teOpp_Q
    {k : Type} [Field k] (θ : k →+* k) : Set (Fin (twistedDatum k θ).rank → ℤ) :=
  {γ | γ ∈ (twistedDatum k θ).roots ∧ 1 ≤ γ (teOpp_last θ)}

private def teOpp_P
    {k : Type} [Field k] (θ : k →+* k) : Set (Fin (twistedDatum k θ).rank → ℤ) :=
  {γ | γ ∈ (twistedDatum k θ).roots ∧ 0 < ht γ}

private def teOpp_Pnonneg
    {k : Type} [Field k] (θ : k →+* k) : Set (Fin (twistedDatum k θ).rank → ℤ) :=
  {γ | γ ∈ (twistedDatum k θ).roots ∧ 0 ≤ γ (teOpp_last θ)}

private theorem teOpp_f2_level_nonneg :
    ∀ g ∈ rootFinset Tag.F4, 0 < ht g → 0 ≤ g twE6Last := by
  decide +kernel

private theorem teOpp_f2_pos_of_level_pos :
    ∀ g ∈ rootFinset Tag.F4, 1 ≤ g twE6Last → 0 < ht g := by
  decide +kernel

private theorem teOpp_f8_w0l_pos :
    ∀ g ∈ rootFinset Tag.F4, 0 < ht g → 1 ≤ g twE6Last →
      0 < ht (wordAct teOpp_refl teOpp_w0lword g) := by
  decide +kernel

private theorem teOpp_f8_w0l_neg :
    ∀ g ∈ rootFinset Tag.F4, 0 < ht g → g twE6Last = 0 →
      ht (wordAct teOpp_refl teOpp_w0lword g) < 0 := by
  decide +kernel

private theorem teOpp_f8_w0l_level :
    ∀ g ∈ rootFinset Tag.F4,
      (wordAct teOpp_refl teOpp_w0lword g) twE6Last = g twE6Last := by
  decide +kernel

private theorem teOpp_w0l_invol :
    ∀ v ∈ rootFinset Tag.F4,
      wordAct teOpp_refl teOpp_w0lword (wordAct teOpp_refl teOpp_w0lword v) = v := by
  decide +kernel

private theorem teOpp_f11_v :
    0 < ht (wordAct teOpp_refl teOpp_vword.reverse (Pi.single (nf 2) 1 :
      Fin (Tag.rank .F4) → ℤ)) := by
  decide +kernel

private theorem teOpp_ggSub_mono
    {k : Type} [Field k] (θ : k →+* k)
    {S T : Set (Fin (twistedDatum k θ).rank → ℤ)} (h : S ⊆ T) :
    ggSub (twistedDatum k θ) S ≤ ggSub (twistedDatum k θ) T :=
  iSup₂_le fun _ hγ => rootGroup_le_ggSub (h hγ)

private theorem teOpp_level_smul_add
    {k : Type} [Field k] (θ : k →+* k) (a b : ℕ)
    (γ δ : Fin (twistedDatum k θ).rank → ℤ) :
    (a • γ + b • δ) (teOpp_last θ) = (a : ℤ) * γ (teOpp_last θ) + (b : ℤ) * δ (teOpp_last θ) := by
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [nsmul_eq_mul, nsmul_eq_mul]

private theorem teOpp_two_smul_notMem
    {k : Type} [Field k] (θ : k →+* k) {γ : Fin (twistedDatum k θ).rank → ℤ}
    (hγ : γ ∈ (twistedDatum k θ).roots) : 2 • γ ∉ (twistedDatum k θ).roots :=
  two_smul_notMem_roots (twistedDatum k θ).isFiniteType
    (show (twistedDatum k θ).divisible = ∅ from rfl) hγ

private theorem teOpp_mem_roots
    {k : Type} [Field k] (θ : k →+* k) {γ : Fin (Tag.rank .F4) → ℤ} (hγ : IsRoot .F4 γ) :
    γ ∈ (twistedDatum k θ).roots := by
  rwa [twistedDatum_roots]

private theorem teOpp_w0l_action
    {k : Type} [Field k] (θ : k →+* k)
    (v : Fin (twistedDatum k θ).rank → ℤ) :
    weylAction (twistedDatum k θ).isFiniteType (twE6W0L k θ) v =
      wordAct teOpp_refl teOpp_w0lword v := by
  have h : twE6W0L k θ =
      (coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.wordProd
        teOpp_w0lword := rfl
  rw [h]
  exact OfCartan.weylAction_wordProd (hA := (twistedDatum k θ).isFiniteType) teOpp_w0lword v

private theorem teOpp_w0l_mul_self
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    twE6W0L k θ * twE6W0L k θ = 1 := by
  apply eq_one_of_forall_rootGroup_eq (twistedDatum_steinbergExtras θ hθ)
    (v := twE6W0L k θ * twE6W0L k θ)
  intro γ hγ
  have hγ' : γ ∈ rootFinset Tag.F4 :=
    mem_rootFinset.2 (isRoot_of_mem_twistedDatum_roots θ hγ)
  have hfix : weylAction (twistedDatum k θ).isFiniteType (twE6W0L k θ)
      (weylAction (twistedDatum k θ).isFiniteType (twE6W0L k θ) γ) = γ := by
    rw [teOpp_w0l_action θ
          (weylAction (twistedDatum k θ).isFiniteType (twE6W0L k θ) γ),
        teOpp_w0l_action θ γ]
    exact teOpp_w0l_invol γ hγ'
  rw [weylAction_mul_apply, hfix]

private theorem teOpp_conj_mem_rad_gen
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {δ γ : Fin (twistedDatum k θ).rank → ℤ}
    (hδ : δ ∈ (twistedDatum k θ).roots) (hδl : 0 ≤ δ (teOpp_last θ))
    (hγ : γ ∈ (twistedDatum k θ).roots) (hγl : 1 ≤ γ (teOpp_last θ))
    {x y : fixedGroup k θ}
    (hx : x ∈ (twistedDatum k θ).rootGroup δ) (hy : y ∈ (twistedDatum k θ).rootGroup γ) :
    x * y * x⁻¹ ∈ twE6Rad θ := by
  by_cases heq : δ = γ
  · subst heq
    have hcomm : Commute x y := by
      have hmem : ⁅x, y⁆ ∈
          ⁅(twistedDatum k θ).rootGroup δ, (twistedDatum k θ).rootGroup δ⁆ :=
        Subgroup.commutator_mem_commutator hx hy
      rw [(twistedDatum_rootGroupCommutators θ).commutator_eq_bot δ hδ
        (teOpp_two_smul_notMem θ hδ), Subgroup.mem_bot] at hmem
      exact commutatorElement_eq_one_iff_commute.1 hmem
    have e : x * y * x⁻¹ = y := by rw [hcomm.eq]; group
    rw [e]
    exact rootGroup_le_ggSub (S := teOpp_Q θ) ⟨hδ, hγl⟩ hy
  · have hli : LinIndepPair δ γ := by
      by_contra h
      rcases OfCartan.proportional (twistedDatum k θ).isFiniteType hδ hγ h with
        h' | h' | h' | h' | h' | h'
      · exact heq h'
      · have : δ (teOpp_last θ) = -γ (teOpp_last θ) := by rw [h']; rfl
        omega
      · exact absurd (h' ▸ hδ) (teOpp_two_smul_notMem θ hγ)
      · have : δ (teOpp_last θ) = -2 * γ (teOpp_last θ) := by
          rw [h']; simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]; ring
        omega
      · exact absurd (h' ▸ hγ) (teOpp_two_smul_notMem θ hδ)
      · have : γ (teOpp_last θ) = -2 * δ (teOpp_last θ) := by
          rw [h']; simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]; ring
        omega
    have hc := (twistedDatum_steinbergExtras θ hθ).commutator_mem δ hδ γ hγ hli x hx y hy
    have hle : ⨆ ε ∈ openCone (twistedDatum k θ).roots δ γ,
        (twistedDatum k θ).rootGroup ε ≤ twE6Rad θ := by
      refine iSup₂_le fun ε hε => ?_
      obtain ⟨hεroot, a, b, ha, hb, rfl⟩ := hε
      refine rootGroup_le_ggSub (S := teOpp_Q θ) ⟨hεroot, ?_⟩
      rw [teOpp_level_smul_add θ]
      have ha1 : (1 : ℤ) ≤ a := by exact_mod_cast ha
      have hb1 : (1 : ℤ) ≤ b := by exact_mod_cast hb
      nlinarith
    have hxy : ⁅x, y⁆ ∈ twE6Rad θ := hle hc
    have hyQ : y ∈ twE6Rad θ := rootGroup_le_ggSub (S := teOpp_Q θ) ⟨hγ, hγl⟩ hy
    have e : x * y * x⁻¹ = ⁅x, y⁆ * y := by rw [commutatorElement_def]; group
    rw [e]
    exact mul_mem hxy hyQ

private theorem teOpp_rootGroup_le_normalizer_rad
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c)
    {δ : Fin (twistedDatum k θ).rank → ℤ}
    (hδ : δ ∈ (twistedDatum k θ).roots) (hδl : 0 ≤ δ (teOpp_last θ)) :
    (twistedDatum k θ).rootGroup δ ≤
      Subgroup.normalizer ((twE6Rad θ : Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ)) := by
  refine le_normalizer_of_map_conj_le fun x hx => ?_
  rw [map_conj_le_iff]
  intro y hy
  refine CFSG.LieType.TitsSimplicity.iSup₂_induction
    (X := fun γ => (twistedDatum k θ).rootGroup γ)
    (P := teOpp_Q θ)
    (C := fun y => x * y * x⁻¹ ∈ twE6Rad θ) hy ?_ ?_ ?_
  · intro γ hγ y hy
    exact teOpp_conj_mem_rad_gen θ hθ hδ hδl hγ.1 hγ.2 hx hy
  · rw [mul_one, mul_inv_cancel]; exact (twE6Rad θ).one_mem
  · intro y z hy hz
    have e : x * (y * z) * x⁻¹ = (x * y * x⁻¹) * (x * z * x⁻¹) := by group
    rw [e]; exact mul_mem hy hz

private theorem teOpp_ggSub_level_le_normalizer_rad
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    ggSub (twistedDatum k θ) (teOpp_Pnonneg θ) ≤
      Subgroup.normalizer ((twE6Rad θ : Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ)) :=
  iSup₂_le fun γ hγ => teOpp_rootGroup_le_normalizer_rad θ hθ hγ.1 hγ.2

private theorem teOpp_posUnipotent_le_normalizer_rad
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    twE6PosUnip θ ≤
      Subgroup.normalizer ((twE6Rad θ : Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ)) := by
  change ggSub (twistedDatum k θ) (teOpp_P θ) ≤ _
  exact (teOpp_ggSub_mono (S := teOpp_P θ) (T := teOpp_Pnonneg θ) θ fun γ hγ =>
    ⟨hγ.1, by
      have h := teOpp_f2_level_nonneg γ (mem_rootFinset.2
        (isRoot_of_mem_twistedDatum_roots θ hγ.1)) hγ.2
      exact h⟩).trans
    (teOpp_ggSub_level_le_normalizer_rad θ hθ)

private theorem teOpp_rad_le_posUnipotent
    {k : Type} [Field k] (θ : k →+* k) :
    twE6Rad θ ≤ twE6PosUnip θ := by
  change ggSub (twistedDatum k θ) (teOpp_Q θ) ≤ ggSub (twistedDatum k θ) (teOpp_P θ)
  exact teOpp_ggSub_mono (S := teOpp_Q θ) (T := teOpp_P θ) θ fun γ hγ =>
    ⟨hγ.1, by
      have h := teOpp_f2_pos_of_level_pos γ (mem_rootFinset.2
        (isRoot_of_mem_twistedDatum_roots θ hγ.1)) hγ.2
      exact h⟩

private theorem teOpp_rankOne_le_normalizer_rad
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    rankOne (twistedDatum k θ).rootGroup (nf 2) ≤
      Subgroup.normalizer ((twE6Rad θ : Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ)) := by
  have hα : IsRoot .F4 (Pi.single (nf 2) 1 : Fin (Tag.rank .F4) → ℤ) := IsRoot.basis (nf 2)
  have hneg : IsRoot .F4 (-(Pi.single (nf 2) 1) : Fin (Tag.rank .F4) → ℤ) :=
    isRoot_neg_single .F4 (nf 2)
  have hαl : 0 ≤ (Pi.single (nf 2) 1 : Fin (Tag.rank .F4) → ℤ) twE6Last := by decide +kernel
  have hnegl : 0 ≤ (-(Pi.single (nf 2) 1) : Fin (Tag.rank .F4) → ℤ) twE6Last := by decide +kernel
  exact sup_le (teOpp_rootGroup_le_normalizer_rad θ hθ (teOpp_mem_roots θ hα) hαl)
    (teOpp_rootGroup_le_normalizer_rad θ hθ (teOpp_mem_roots θ hneg) hnegl)

private theorem teOpp_borel_le_normalizer_rad
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    twE6Borel θ ≤
      Subgroup.normalizer ((twE6Rad θ : Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ)) := by
  refine sup_le ?_ (teOpp_posUnipotent_le_normalizer_rad θ hθ)
  refine iSup_le fun i => ?_
  refine le_normalizer_of_map_conj_le fun h hh => ?_
  rw [map_conj_le_iff]
  intro y hy
  refine CFSG.LieType.TitsSimplicity.iSup₂_induction
    (X := fun γ => (twistedDatum k θ).rootGroup γ)
    (P := teOpp_Q θ)
    (C := fun y => h * y * h⁻¹ ∈ twE6Rad θ) hy ?_ ?_ ?_
  · intro γ hγ y hy
    have hmem := iSup_le_normalizer_rootGroup (twE6_hct θ hθ) hγ.1
      (le_iSup (hHat k θ) i hh)
    have := (Subgroup.mem_normalizer_iff.1 hmem y).1 hy
    exact rootGroup_le_ggSub (S := teOpp_Q θ) ⟨hγ.1, hγ.2⟩ this
  · rw [mul_one, mul_inv_cancel]; exact (twE6Rad θ).one_mem
  · intro y z hy hz
    have e : h * (y * z) * h⁻¹ = (h * y * h⁻¹) * (h * z * h⁻¹) := by group
    rw [e]; exact mul_mem hy hz

private theorem teOpp_U_eq_rad_sup
    {k : Type} [Field k] (θ : k →+* k) :
    twE6PosUnip θ = twE6Rad θ ⊔ ggSub (twistedDatum k θ) (teOpp_P0 θ) := by
  apply le_antisymm
  · change ggSub (twistedDatum k θ) (teOpp_P θ) ≤
      twE6Rad θ ⊔ ggSub (twistedDatum k θ) (teOpp_P0 θ)
    refine iSup₂_le fun γ hγ => ?_
    have hlev := teOpp_f2_level_nonneg γ
      (mem_rootFinset.2 (isRoot_of_mem_twistedDatum_roots θ hγ.1)) hγ.2
    rw [show γ (teOpp_last θ) = γ twE6Last from rfl] at hlev
    rcases eq_or_lt_of_le hlev with h0 | h1
    · exact (rootGroup_le_ggSub (S := teOpp_P0 θ) ⟨hγ.1, hγ.2, h0.symm⟩).trans le_sup_right
    · refine (rootGroup_le_ggSub (S := teOpp_Q θ) ⟨hγ.1, ?_⟩).trans le_sup_left
      show 1 ≤ γ twE6Last
      omega
  · refine sup_le ?_ ?_
    · change ggSub (twistedDatum k θ) (teOpp_Q θ) ≤ ggSub (twistedDatum k θ) (teOpp_P θ)
      exact teOpp_ggSub_mono (S := teOpp_Q θ) (T := teOpp_P θ) θ fun γ hγ => ⟨hγ.1, by
        have h := teOpp_f2_pos_of_level_pos γ (mem_rootFinset.2
          (isRoot_of_mem_twistedDatum_roots θ hγ.1)) (by simpa [teOpp_last] using hγ.2)
        exact h⟩
    · change ggSub (twistedDatum k θ) (teOpp_P0 θ) ≤ ggSub (twistedDatum k θ) (teOpp_P θ)
      exact teOpp_ggSub_mono (S := teOpp_P0 θ) (T := teOpp_P θ) θ fun γ hγ => ⟨hγ.1, hγ.2.1⟩

private theorem teOpp_conj_n0_UL_le_negUnipotent
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    (ggSub (twistedDatum k θ) (teOpp_P0 θ)).map
        (MulAut.conj ((twE6N θ hθ (twE6W0L k θ))⁻¹)).toMonoidHom ≤
      negUnipotent (twistedDatum k θ) := by
  rw [map_conj_le_iff]
  intro u hu
  refine conj_mem_of_forall_mem (M := negUnipotent (twistedDatum k θ))
    (c := (twE6N θ hθ (twE6W0L k θ))⁻¹) ?_ hu
  intro γ hγ y hy
  have hγmem : γ ∈ (twistedDatum k θ).roots := hγ.1
  have hγroot : IsRoot .F4 γ := isRoot_of_mem_twistedDatum_roots θ hγmem
  have hγpos : 0 < ht γ := hγ.2.1
  have hγlev : γ (teOpp_last θ) = 0 := hγ.2.2
  have hwneg := teOpp_f8_w0l_neg γ (mem_rootFinset.2 hγroot) hγpos
    (by simpa [teOpp_last] using hγlev)
  rw [← teOpp_w0l_action θ γ] at hwneg
  have hconj := nrep_inv_conj_mem (twE6_hct θ hθ) (twE6W0L k θ) hγmem hy
  have hinv : (twE6W0L k θ)⁻¹ = twE6W0L k θ := by
    rw [← mul_right_inj (twE6W0L k θ)]
    rw [mul_inv_cancel, teOpp_w0l_mul_self θ hθ]
  rw [hinv] at hconj
  exact rootGroup_le_negUnipotent (weylAction_mem_roots _ _ hγmem) hwneg hconj

private theorem teOpp_inv_conj_n0_rad_le
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    (twE6Rad θ).map (MulAut.conj ((twE6N θ hθ (twE6W0L k θ))⁻¹)).toMonoidHom ≤ twE6Rad θ := by
  rw [map_conj_le_iff]
  intro u hu
  refine conj_mem_of_forall_mem (M := twE6Rad θ)
    (c := (twE6N θ hθ (twE6W0L k θ))⁻¹) ?_ hu
  intro γ hγ y hy
  have hγmem : γ ∈ (twistedDatum k θ).roots := hγ.1
  have hγroot : IsRoot .F4 γ := isRoot_of_mem_twistedDatum_roots θ hγmem
  have hγl : 1 ≤ γ (teOpp_last θ) := hγ.2
  have hconj := nrep_inv_conj_mem (twE6_hct θ hθ) (twE6W0L k θ) hγmem hy
  have hinv : (twE6W0L k θ)⁻¹ = twE6W0L k θ := by
    rw [← mul_right_inj (twE6W0L k θ)]
    rw [mul_inv_cancel, teOpp_w0l_mul_self θ hθ]
  rw [hinv] at hconj
  have hlev := teOpp_f8_w0l_level γ (mem_rootFinset.2 hγroot)
  rw [← teOpp_w0l_action θ γ] at hlev
  refine rootGroup_le_ggSub (S := teOpp_Q θ) ⟨weylAction_mem_roots _ _ hγmem, ?_⟩ hconj
  rw [hlev]
  exact hγl

private theorem teOpp_rad_le_conj_n0
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    twE6Rad θ ≤ twE6Cj (twE6N θ hθ (twE6W0L k θ)) (twE6PosUnip θ) := by
  change twE6Rad θ ≤ (twE6PosUnip θ).map
    (MulAut.conj (twE6N θ hθ (twE6W0L k θ))).toMonoidHom
  refine iSup₂_le fun g hg => ?_
  have hgmem : g ∈ (twistedDatum k θ).roots := hg.1
  have hgroot : IsRoot .F4 g := isRoot_of_mem_twistedDatum_roots θ hgmem
  have hgl : 1 ≤ g (teOpp_last θ) := hg.2
  have hgl' : 1 ≤ g twE6Last := by simpa [teOpp_last] using hgl
  have hgpos : 0 < ht g := teOpp_f2_pos_of_level_pos g (mem_rootFinset.2 hgroot) hgl'
  have hwpos := teOpp_f8_w0l_pos g (mem_rootFinset.2 hgroot) hgpos hgl'
  rw [← teOpp_w0l_action θ g] at hwpos
  have hinv : weylAction (twistedDatum k θ).isFiniteType (twE6W0L k θ)
      (weylAction (twistedDatum k θ).isFiniteType (twE6W0L k θ) g) = g := by
    rw [teOpp_w0l_action θ
          (weylAction (twistedDatum k θ).isFiniteType (twE6W0L k θ) g),
        teOpp_w0l_action θ g]
    exact teOpp_w0l_invol g (mem_rootFinset.2 hgroot)
  have hX : (twistedDatum k θ).rootGroup g =
      ((twistedDatum k θ).rootGroup (weylAction (twistedDatum k θ).isFiniteType
        (twE6W0L k θ) g)).map
        (MulAut.conj (twE6N θ hθ (twE6W0L k θ))).toMonoidHom := by
    simp only [twE6N]
    have hA := (actsAs_nrep (twE6_hct θ hθ) (twE6W0L k θ))
      (weylAction (twistedDatum k θ).isFiniteType (twE6W0L k θ) g)
      (weylAction_mem_roots _ _ hgmem)
    rw [hA, hinv]
  rw [hX]
  exact Subgroup.map_mono (rootGroup_le_posUnipotent
    (weylAction_mem_roots _ _ hgmem) hwpos)

theorem twE6_posUnipotent_inf_conj_n0
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    twE6PosUnip θ ⊓ twE6Cj (twE6N θ hθ (twE6W0L k θ)) (twE6PosUnip θ) = twE6Rad θ := by

  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxU, hxN⟩ := hx
    have hxU' : (twE6N θ hθ (twE6W0L k θ))⁻¹ * x * (twE6N θ hθ (twE6W0L k θ)) ∈
        twE6PosUnip θ := by
      rw [Subgroup.mem_map_equiv] at hxN
      simpa [MulAut.conj_symm_apply] using hxN
    have hnorm : ggSub (twistedDatum k θ) (teOpp_P0 θ) ≤
        Subgroup.normalizer ((twE6Rad θ : Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ)) :=
      (teOpp_ggSub_mono (S := teOpp_P0 θ) (T := teOpp_P θ) θ fun γ hγ =>
        ⟨hγ.1, hγ.2.1⟩).trans
        (teOpp_posUnipotent_le_normalizer_rad θ hθ)
    have hxprod : x ∈ twE6Rad θ ⊔ ggSub (twistedDatum k θ) (teOpp_P0 θ) :=
      (teOpp_U_eq_rad_sup θ).symm ▸ hxU
    have hxprod' : x ∈ (↑(twE6Rad θ ⊔ ggSub (twistedDatum k θ) (teOpp_P0 θ) :
        Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ)) := hxprod
    rw [Subgroup.coe_mul_of_right_le_normalizer_left (twE6Rad θ)
      (ggSub (twistedDatum k θ) (teOpp_P0 θ)) hnorm] at hxprod'
    rw [Set.mem_mul] at hxprod'
    obtain ⟨q, hq, uL, huL, hxu⟩ := hxprod' 
    have hq' : (twE6N θ hθ (twE6W0L k θ))⁻¹ * q * (twE6N θ hθ (twE6W0L k θ)) ∈
        twE6Rad θ := (map_conj_le_iff.1 (teOpp_inv_conj_n0_rad_le θ hθ)) q hq
    have huL' : (twE6N θ hθ (twE6W0L k θ))⁻¹ * uL * (twE6N θ hθ (twE6W0L k θ)) ∈
        negUnipotent (twistedDatum k θ) :=
      (map_conj_le_iff.1 (teOpp_conj_n0_UL_le_negUnipotent θ hθ)) uL huL
    have huL'' : (twE6N θ hθ (twE6W0L k θ))⁻¹ * uL * (twE6N θ hθ (twE6W0L k θ)) ∈
        twE6PosUnip θ := by
      have e : (twE6N θ hθ (twE6W0L k θ))⁻¹ * uL * (twE6N θ hθ (twE6W0L k θ)) =
          ((twE6N θ hθ (twE6W0L k θ))⁻¹ * q * (twE6N θ hθ (twE6W0L k θ)))⁻¹ *
            ((twE6N θ hθ (twE6W0L k θ))⁻¹ * x * (twE6N θ hθ (twE6W0L k θ))) := by
        rw [← hxu]; group
      rw [e]
      exact mul_mem (inv_mem (teOpp_rad_le_posUnipotent θ hq')) hxU'
    have hone : (twE6N θ hθ (twE6W0L k θ))⁻¹ * uL * (twE6N θ hθ (twE6W0L k θ)) = 1 := by
      have hmem : (twE6N θ hθ (twE6W0L k θ))⁻¹ * uL * (twE6N θ hθ (twE6W0L k θ)) ∈
          twE6PosUnip θ ⊓ negUnipotent (twistedDatum k θ) := ⟨huL'', huL'⟩
      rwa [posUnipotent_inf_negUnipotent (twistedDatum_steinbergExtras θ hθ),
        Subgroup.mem_bot] at hmem
    have huL1 : uL = 1 := by
      calc uL = (twE6N θ hθ (twE6W0L k θ)) *
            ((twE6N θ hθ (twE6W0L k θ))⁻¹ * uL * (twE6N θ hθ (twE6W0L k θ))) *
              (twE6N θ hθ (twE6W0L k θ))⁻¹ := by group
        _ = 1 := by rw [hone]; group
    rw [← hxu, huL1, mul_one]
    exact hq
  · exact le_inf (teOpp_rad_le_posUnipotent θ) (teOpp_rad_le_conj_n0 θ hθ)

private theorem teOpp_opposition_core
    {k : Type} [Field k] {θ : k →+* k}
    {B U Q L : Subgroup (fixedGroup k θ)} {n₃ nv n₀ : fixedGroup k θ}
    (hBU : B ≤ Subgroup.normalizer (U : Set (fixedGroup k θ)))
    (hUQ : U ⊓ twE6Cj n₀ U = Q)
    (hLQ : L ≤ Subgroup.normalizer (Q : Set (fixedGroup k θ)))
    (hBQ : B ≤ Subgroup.normalizer (Q : Set (fixedGroup k θ)))
    (hLB : ∀ g ∈ L, g ∈ B ∨ ∃ b ∈ B, ∃ b' ∈ B, g = b * n₃ * b')
    (hprod : ∀ b' ∈ B, ∃ c ∈ B, ∃ c' ∈ B, n₃ * b' * nv = c * n₀ * c')
    {l₁ l₂ : fixedGroup k θ} (h₁ : l₁ ∈ L) (h₂ : l₂ ∈ L) (h : l₁⁻¹ * l₂ ∉ B) :
    twE6Cj l₁ U ⊓ twE6Cj (l₂ * nv) U = Q := by
  have hmem : l₁⁻¹ * l₂ ∈ L := L.mul_mem (L.inv_mem h₁) h₂
  rcases hLB (l₁⁻¹ * l₂) hmem with hB | ⟨b, hb, b', hb', he⟩
  · exact absurd hB h
  · obtain ⟨c, hc, c', hc', hprod'⟩ := hprod b' hb'
    set x : fixedGroup k θ := l₁ * b * c with hx
    have hbU : Subgroup.map (MulAut.conj b).toMonoidHom U = U :=
      mem_normalizer_iff_map_conj.1 (hBU hb)
    have hcU : Subgroup.map (MulAut.conj c).toMonoidHom U = U :=
      mem_normalizer_iff_map_conj.1 (hBU hc)
    have hc'U : Subgroup.map (MulAut.conj c').toMonoidHom U = U :=
      mem_normalizer_iff_map_conj.1 (hBU hc')
    have hxU : twE6Cj l₁ U = twE6Cj x U := by
      rw [hx]
      change Subgroup.map (MulAut.conj l₁).toMonoidHom U =
        Subgroup.map (MulAut.conj (l₁ * b * c)).toMonoidHom U
      rw [map_conj_mul (l₁ * b) c U, hcU, map_conj_mul l₁ b U, hbU]
    have hnv : twE6Cj (l₂ * nv) U = twE6Cj x (twE6Cj n₀ U) := by
      have h2' : l₂ * nv = x * n₀ * c' := by
        rw [hx]
        calc l₂ * nv = l₁ * (l₁⁻¹ * l₂) * nv := by group
          _ = l₁ * (b * n₃ * b') * nv := by rw [he]
          _ = l₁ * b * (n₃ * b' * nv) := by group
          _ = l₁ * b * (c * n₀ * c') := by rw [hprod']
          _ = (l₁ * b * c) * n₀ * c' := by group
      rw [h2']
      change Subgroup.map (MulAut.conj (x * n₀ * c')).toMonoidHom U =
        Subgroup.map (MulAut.conj x).toMonoidHom
          (Subgroup.map (MulAut.conj n₀).toMonoidHom U)
      rw [map_conj_mul (x * n₀) c' U, hc'U, map_conj_mul x n₀ U]
    have hxQ : twE6Cj x Q = Q := by
      apply mem_normalizer_iff_map_conj.1
      rw [hx]
      exact mul_mem (mul_mem (hLQ h₁) (hBQ hb)) (hBQ hc)
    rw [hxU, hnv, ← Subgroup.map_inf U (twE6Cj n₀ U) (MulAut.conj x).toMonoidHom
      (MulAut.conj x).injective, hUQ]
    exact hxQ

private theorem teOpp_v3_simple_mul
    {k : Type} [Field k] (θ : k →+* k) :
    (coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.simple (nf 2) *
        twE6V3 k θ = twE6W0L k θ := by
  show (coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.simple (nf 2) *
    ((coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.simple (nf 2) *
      twE6W0L k θ) = twE6W0L k θ
  exact
    (coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.simple_mul_simple_cancel_left
      (nf 2)

private theorem teOpp_not_isLeftDescent_v3
    {k : Type} [Field k] (θ : k →+* k) :
    ¬ (coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.IsLeftDescent
      (twE6V3 k θ) (nf 2) := by
  intro hd
  have hd' : (coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.IsRightDescent
      (twE6V3 k θ)⁻¹ (nf 2) :=
    ((coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.isRightDescent_inv_iff).2 hd
  have hneg := ht_weylAction_single_neg (D := twistedDatum k θ) hd'
  have hρ : weylAction (twistedDatum k θ).isFiniteType (twE6V3 k θ)⁻¹
      (Pi.single (nf 2) 1 : Fin (twistedDatum k θ).rank → ℤ) =
      wordAct teOpp_refl teOpp_vword.reverse (Pi.single (nf 2) 1 : Fin (Tag.rank .F4) → ℤ) := by
    rw [show twE6V3 k θ =
        (coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.wordProd teOpp_vword
        from rfl,
      ← (coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.wordProd_reverse
        teOpp_vword]
    exact OfCartan.weylAction_wordProd (hA := (twistedDatum k θ).isFiniteType) teOpp_vword.reverse _
  rw [hρ] at hneg
  exact absurd hneg (not_lt.mpr (le_of_lt teOpp_f11_v))

private theorem teOpp_rankOne_mem_borel_or
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {g : fixedGroup k θ}
    (hg : g ∈ rankOne (twistedDatum k θ).rootGroup (nf 2)) :
    g ∈ twE6Borel θ ∨ ∃ b ∈ twE6Borel θ, ∃ b' ∈ twE6Borel θ, g = b * nHat θ (nf 2) * b' := by
  have hα : (Pi.single (nf 2) 1 : Fin (twistedDatum k θ).rank → ℤ) ∈
      (twistedDatum k θ).roots := by
    rw [twistedDatum_roots]; exact IsRoot.basis (nf 2)
  have hαpos : 0 < ht (Pi.single (nf 2) 1 : Fin (twistedDatum k θ).rank → ℤ) :=
    ht_single_pos (D := twistedDatum k θ) (nf 2)
  rcases (twistedDatum_steinbergExtras θ hθ).rankOne_bruhat (nf 2) g hg with
    ⟨hh, hhh, u, hu, he⟩ | ⟨u, hu, hh, hhh, v, hv, he⟩
  · left
    rw [he]
    exact mul_mem (iSup_le_borel (le_iSup (hHat k θ) (nf 2) hhh))
      (rootGroup_le_borel hα hαpos hu)
  · right
    refine ⟨u, rootGroup_le_borel hα hαpos hu, hh * v,
      mul_mem (iSup_le_borel (le_iSup (hHat k θ) (nf 2) hhh))
        (rootGroup_le_borel hα hαpos hv), ?_⟩
    rw [he]; group

private theorem teOpp_nrep_v3_eq
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    nrep (twE6_hct θ hθ)
        ((coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.simple (nf 2) *
          twE6V3 k θ) =
      nrep (twE6_hct θ hθ) (twE6W0L k θ) := by
  congr 1
  exact teOpp_v3_simple_mul θ

private theorem teOpp_n3_mul_borel_mul_nv_mem
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) :
    ∀ b' ∈ twE6Borel θ, ∃ c ∈ twE6Borel θ, ∃ c' ∈ twE6Borel θ,
      nHat θ (nf 2) * b' * twE6N θ hθ (twE6V3 k θ) =
        c * nrep (twE6_hct θ hθ)
          ((coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.simple (nf 2) *
            twE6V3 k θ) * c' := by
  intro b' hb'
  have hnd := teOpp_not_isLeftDescent_v3 θ
  obtain ⟨c, hc, x, hx, he⟩ := exists_n_mul_mul_nrep (twE6_hct θ hθ)
    (twistedDatum_steinbergExtras θ hθ) (w := twE6V3 k θ) (i := nf 2) hnd hb'
  have hα : (Pi.single (nf 2) 1 : Fin (twistedDatum k θ).rank → ℤ) ∈
      (twistedDatum k θ).roots := by
    rw [twistedDatum_roots]; exact IsRoot.basis (nf 2)
  have hαw : weylAction (twistedDatum k θ).isFiniteType (twE6V3 k θ)⁻¹
      (Pi.single (nf 2) 1 : Fin (twistedDatum k θ).rank → ℤ) ∈ (twistedDatum k θ).roots :=
    weylAction_mem_roots _ _ hα
  have hx' : x ∈ twE6Borel θ :=
    rootGroup_le_borel hαw (ht_weylAction_inv_single_pos hnd) hx
  exact ⟨c, hc, x, hx', he⟩

theorem twE6_opposition
    {k : Type} [Field k] (θ : k →+* k) (hθ : ∀ c, θ (θ c) = c) {l₁ l₂ : fixedGroup k θ}
    (h₁ : l₁ ∈ rankOne (twistedDatum k θ).rootGroup (nf 2))
    (h₂ : l₂ ∈ rankOne (twistedDatum k θ).rootGroup (nf 2))
    (h : l₁⁻¹ * l₂ ∉ twE6Borel θ) :
    twE6Cj l₁ (twE6PosUnip θ) ⊓ twE6Cj (l₂ * twE6N θ hθ (twE6V3 k θ)) (twE6PosUnip θ) =
      twE6Rad θ := by
  have hUQ : twE6PosUnip θ ⊓ twE6Cj (nrep (twE6_hct θ hθ)
      ((coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.simple (nf 2) *
        twE6V3 k θ)) (twE6PosUnip θ) = twE6Rad θ :=
    (congrArg (fun z => twE6PosUnip θ ⊓ twE6Cj z (twE6PosUnip θ)) (teOpp_nrep_v3_eq θ hθ)).trans
      (twE6_posUnipotent_inf_conj_n0 θ hθ)
  exact teOpp_opposition_core
    (B := twE6Borel θ) (U := twE6PosUnip θ) (Q := twE6Rad θ)
    (L := rankOne (twistedDatum k θ).rootGroup (nf 2))
    (n₃ := nHat θ (nf 2)) (nv := twE6N θ hθ (twE6V3 k θ))
    (n₀ := nrep (twE6_hct θ hθ)
      ((coxeterMatrix (twistedDatum k θ).isFiniteType).toCoxeterSystem.simple (nf 2) *
        twE6V3 k θ))
    (borel_le_normalizer_posUnipotent (twE6_hct θ hθ))
    hUQ
    (teOpp_rankOne_le_normalizer_rad θ hθ)
    (teOpp_borel_le_normalizer_rad θ hθ)
    (fun _ hg => teOpp_rankOne_mem_borel_or θ hθ hg)
    (teOpp_n3_mul_borel_mul_nv_mem θ hθ)
    h₁ h₂ h

end CFSG.StandardType.LieKnownR2.Short
