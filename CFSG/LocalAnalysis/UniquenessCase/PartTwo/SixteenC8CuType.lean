module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuZero

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis

open Matrix CFSG.Quasithin.SmithCurtis

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G6 V)

theorem hW_of_forall {y : V} {l : List (Fin 3)} (h : ∀ s ∈ l, Th ρ s y = 0) : hW ρ l y = y := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    rw [hW_cons, ih fun t ht => h t (List.mem_cons_of_mem s ht), h s (by simp), add_zero]

theorem hW_of_exists {y : V} (hy : ∀ s : Fin 3, Th ρ s y = 0 ∨ Th ρ s y = y) {l : List (Fin 3)}
    (h : ∃ s ∈ l, Th ρ s y ≠ 0) : hW ρ l y = 0 := by
  induction l with
  | nil =>
    obtain ⟨s, hs, -⟩ := h
    simp at hs
  | cons s l ih =>
    rw [hW_cons]
    by_cases hl : ∃ t ∈ l, Th ρ t y ≠ 0
    · rw [ih hl, map_zero, add_zero]
    · push Not at hl
      rw [hW_of_forall ρ hl]
      obtain ⟨t, ht, hne⟩ := h
      rcases List.mem_cons.mp ht with hts | ht'
      · rw [hts] at hne
        rcases hy s with h' | h'
        · exact absurd h' hne
        · rw [h', add_self_zmod2]
      · exact absurd (hl t ht') hne

theorem eigen_of_simple {ρ : Representation (ZMod 2) G6 V} (hρ : IsSimpleRep ρ) [Finite V]
    {y : V} (hy : y ∈ fixU ρ) (hy0 : y ≠ 0) : ∀ s : Fin 3, Th ρ s y = 0 ∨ Th ρ s y = y := by
  have := hρ.1
  obtain ⟨y₀, hy₀, hy₀0, heig⟩ := exists_eigen ρ
  rcases fixU_eq hρ hy₀ hy₀0 heig hy with h | rfl
  · exact absurd h hy0
  · exact heig

theorem exists_form {ρ : Representation (ZMod 2) G6 V} (hρ : IsSimpleRep ρ) [Finite V] {y : V}
    (hy : y ∈ fixU ρ) (hy0 : y ≠ 0) :
    ∃ f : Module.Dual (ZMod 2) V, (∀ z ∈ augL ρ, f z = 0) ∧ f y = 1 := by
  have hyn : y ∉ augL ρ := fun h => hy0 (fixU_inf_augL hρ hy h)
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hyn inferInstance
  refine ⟨f, fun z hz => ?_, (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ hf⟩
  have h := Submodule.mem_map_of_mem (f := f) hz
  rw [hmap] at h
  exact (Submodule.mem_bot _).mp h

theorem form_wE {f : Module.Dual (ZMod 2) V} (hf : ∀ z ∈ augL ρ, f z = 0) {y : V}
    (hy : y ∈ fixU ρ) (k : Fin 48) : f (ρ (wE k) y) = f (hW ρ (canW k) y) := by
  have h := hf _ (coinv_formula ρ hy k)
  rwa [map_sub, sub_eq_zero] at h

theorem form_cell {f : Module.Dual (ZMod 2) V} (hf : ∀ z ∈ augL ρ, f z = 0) {y : V}
    (hy : y ∈ fixU ρ) {g q u : G6} {k : Fin 48} (hq : q ∈ Lgrp) (hu : u ∈ Ugrp)
    (e : g = q * wE k * u) : f (ρ g y) = f (hW ρ (canW k) y) := by
  rw [cell_act ρ e, hy u hu]
  have h := hf _ (sub_mem_augL ρ hq (ρ (wE k) y))
  rw [map_sub, sub_eq_zero] at h
  rw [h, form_wE ρ hf hy k]

theorem coeff_eq_of_type {V' : Type*} [AddCommGroup V'] [Module (ZMod 2) V']
    {ρ' : Representation (ZMod 2) G6 V'} {f : Module.Dual (ZMod 2) V}
    {f' : Module.Dual (ZMod 2) V'} (hf : ∀ z ∈ augL ρ, f z = 0)
    (hf' : ∀ z ∈ augL ρ', f' z = 0) {y : V} {y' : V'} (hy : y ∈ fixU ρ) (hy' : y' ∈ fixU ρ')
    (hfy : f y = 1) (hfy' : f' y' = 1) (heig : ∀ s : Fin 3, Th ρ s y = 0 ∨ Th ρ s y = y)
    (heig' : ∀ s : Fin 3, Th ρ' s y' = 0 ∨ Th ρ' s y' = y')
    (htype : ∀ s : Fin 3, Th ρ s y = 0 ↔ Th ρ' s y' = 0) (g : G6) :
    f (ρ g y) = f' (ρ' g y') := by
  obtain ⟨q, hq, k, u, hu, e⟩ := bruhat_cover g
  rw [form_cell ρ hf hy hq hu e, form_cell ρ' hf' hy' hq hu e]
  by_cases h : ∀ s ∈ canW k, Th ρ s y = 0
  · rw [hW_of_forall ρ h, hW_of_forall ρ' fun s hs => (htype s).mp (h s hs), hfy, hfy']
  · push Not at h
    obtain ⟨s, hs, hne⟩ := h
    rw [hW_of_exists ρ heig ⟨s, hs, hne⟩,
      hW_of_exists ρ' heig' ⟨s, hs, fun h' => hne ((htype s).mpr h')⟩, map_zero, map_zero]

@[expose] def coeffMap (f : Module.Dual (ZMod 2) V) : V →ₗ[ZMod 2] (G6 → ZMod 2) where
  toFun v g := f (ρ g v)
  map_add' a b := funext fun g => by simp only [map_add, Pi.add_apply]
  map_smul' c a := funext fun g => by simp only [map_smul, Pi.smul_apply, RingHom.id_apply]

theorem coeffMap_apply (f : Module.Dual (ZMod 2) V) (v : V) (g : G6) :
    coeffMap ρ f v g = f (ρ g v) := rfl

theorem coeffMap_act (f : Module.Dual (ZMod 2) V) (h : G6) (v : V) (g : G6) :
    coeffMap ρ f (ρ h v) g = coeffMap ρ f v (g * h) := by
  rw [coeffMap_apply, coeffMap_apply, act_mul]

theorem coeffMap_injective {ρ : Representation (ZMod 2) G6 V} (hρ : IsSimpleRep ρ)
    {f : Module.Dual (ZMod 2) V} {y : V} (hfy : f y = 1) :
    Function.Injective (coeffMap ρ f) := by
  rw [← LinearMap.ker_eq_bot]
  have hst : ∀ (h : G6), ∀ v ∈ LinearMap.ker (coeffMap ρ f),
      ρ h v ∈ LinearMap.ker (coeffMap ρ f) := by
    intro h v hv
    rw [LinearMap.mem_ker] at hv ⊢
    funext g
    rw [coeffMap_act, hv]
    rfl
  rcases hρ.2 _ hst with hk | hk
  · exact hk
  · exfalso
    have hy : y ∈ LinearMap.ker (coeffMap ρ f) := hk ▸ Submodule.mem_top
    have h1 := congrFun (LinearMap.mem_ker.mp hy) 1
    rw [coeffMap_apply, map_one, Module.End.one_apply, hfy, Pi.zero_apply] at h1
    exact one_ne_zero h1

theorem range_coeffMap_le {V' : Type*} [AddCommGroup V'] [Module (ZMod 2) V']
    {ρ : Representation (ZMod 2) G6 V} {ρ' : Representation (ZMod 2) G6 V'} (hρ : IsSimpleRep ρ)
    {f : Module.Dual (ZMod 2) V} {f' : Module.Dual (ZMod 2) V'} {y : V} {y' : V'} (hy0 : y ≠ 0)
    (hc : ∀ g, f (ρ g y) = f' (ρ' g y')) :
    LinearMap.range (coeffMap ρ f) ≤ LinearMap.range (coeffMap ρ' f') := by
  rintro _ ⟨v, rfl⟩
  have hv : v ∈ orbitSpan ρ y := by
    rw [orbitSpan_eq_top hρ hy0]
    exact Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨h, rfl⟩ := hv
    refine ⟨ρ' h y', funext fun g => ?_⟩
    rw [coeffMap_act, coeffMap_act, coeffMap_apply, coeffMap_apply, hc]
  | zero => rw [map_zero]; exact zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem iso_of_type {V' : Type*} [AddCommGroup V'] [Module (ZMod 2) V']
    {ρ : Representation (ZMod 2) G6 V} {ρ' : Representation (ZMod 2) G6 V'}
    (hρ : IsSimpleRep ρ) (hρ' : IsSimpleRep ρ') [Finite V] [Finite V'] {y : V} {y' : V'}
    (hy : y ∈ fixU ρ) (hy0 : y ≠ 0) (hy' : y' ∈ fixU ρ') (hy0' : y' ≠ 0)
    (htype : ∀ s : Fin 3, Th ρ s y = 0 ↔ Th ρ' s y' = 0) :
    ∃ β : V ≃ₗ[ZMod 2] V', ∀ (g : G6) (v : V), β (ρ g v) = ρ' g (β v) := by
  obtain ⟨f, hf, hfy⟩ := exists_form hρ hy hy0
  obtain ⟨f', hf', hfy'⟩ := exists_form hρ' hy' hy0'
  have hc := coeff_eq_of_type ρ hf hf' hy hy' hfy hfy' (eigen_of_simple hρ hy hy0)
    (eigen_of_simple hρ' hy' hy0') htype
  have hi := coeffMap_injective hρ hfy
  have hi' := coeffMap_injective hρ' hfy'
  have hR : LinearMap.range (coeffMap ρ f) = LinearMap.range (coeffMap ρ' f') :=
    le_antisymm (range_coeffMap_le hρ hy0 hc) (range_coeffMap_le hρ' hy0' fun g => (hc g).symm)
  let β : V ≃ₗ[ZMod 2] V' := (LinearEquiv.ofInjective _ hi).trans
    ((LinearEquiv.ofEq _ _ hR).trans (LinearEquiv.ofInjective _ hi').symm)
  have hβ : ∀ v, coeffMap ρ' f' (β v) = coeffMap ρ f v := fun v => by
    have h1 : LinearEquiv.ofInjective _ hi' (β v) =
        LinearEquiv.ofEq _ _ hR (LinearEquiv.ofInjective _ hi v) :=
      LinearEquiv.apply_symm_apply _ _
    have h2 := congrArg Subtype.val h1
    rwa [LinearEquiv.ofInjective_apply, LinearEquiv.coe_ofEq_apply,
      LinearEquiv.ofInjective_apply] at h2
  refine ⟨β, fun g v => hi' ?_⟩
  rw [hβ]
  funext h
  rw [coeffMap_act, coeffMap_act, hβ]

theorem wE_inv_mul {a b c : Fin 48}
    (h : bmul (bword (canW a).reverse) (bword (canW b)) = bword (canW c)) :
    (wE a)⁻¹ * wE b = wE c := by
  unfold wE
  rw [wordProd_inv]
  apply gM_injective
  change gM (wordProd (canW a).reverse) * gM (wordProd (canW b)) = gM (wordProd (canW c))
  rw [wordProd_coe, wordProd_coe, wordProd_coe, ← toMat_bmul, h]

theorem card_le_finrank {ρ : Representation (ZMod 2) G6 V} (hρ : IsSimpleRep ρ) [Finite V]
    {y : V} (hy : y ∈ fixU ρ) (hy0 : y ≠ 0) {m : ℕ} (b : Fin m → Fin 48)
    (c : Fin m → Fin m → Fin 48) (hc : ∀ i j, (wE (b i))⁻¹ * wE (b j) = wE (c i j))
    (hd : ∀ i, c i i = 0) (ho : ∀ i j, i ≠ j → ∃ s ∈ canW (c i j), Th ρ s y ≠ 0) :
    m ≤ Module.finrank (ZMod 2) V := by
  obtain ⟨f, hf, hfy⟩ := exists_form hρ hy hy0
  have heig := eigen_of_simple hρ hy hy0
  have hval : ∀ i j, f (ρ (wE (b i))⁻¹ (ρ (wE (b j)) y)) = if i = j then 1 else 0 := by
    intro i j
    rw [act_mul, hc, form_wE ρ hf hy]
    split_ifs with h
    · rw [h, hd, canW_zero, hW_nil, hfy]
    · rw [hW_of_exists ρ heig (ho i j h), map_zero]
  have hli : LinearIndependent (ZMod 2) fun j => ρ (wE (b j)) y := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have h1 := congrArg (fun z => f (ρ (wE (b i))⁻¹ z)) hg
    simpa [map_sum, map_smul, hval] using h1
  simpa using hli.fintype_card_le_finrank

theorem isSimpleRep_of_fixU [Finite V] [Nontrivial V] {y : V}
    (hfix : ∀ x ∈ fixU ρ, x = 0 ∨ x = y) (hgen : orbitSpan ρ y = ⊤) : IsSimpleRep ρ := by
  refine ⟨inferInstance, fun W hW => ?_⟩
  by_cases hne : W = ⊥
  · exact Or.inl hne
  · right
    obtain ⟨x, hxW, hx0, hx⟩ := exists_fixed_mem ρ isPGroup_Ugrp hW hne
    rcases hfix x hx with h | rfl
    · exact absurd h hx0
    · rw [eq_top_iff, ← hgen, orbitSpan, Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      exact hW g x hxW

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis
