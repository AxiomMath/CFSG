module

public import CFSG.LocalAnalysis.SteinbergBVSp6LayerStatements
public import CFSG.LocalAnalysis.ComponentInitial.KProperOddCoreFreeLayer

public section

namespace CFSG.LocalAnalysis.SteinbergBV

open Subgroup CFSG.LocalCores
open scoped commutatorElement

namespace OneOrTwoLayer

section General

variable {G : Type*} [Group G]

theorem isQuasisimple_of_simple [IsSimpleGroup G] (hna : ∃ x y : G, x * y ≠ y * x) :
    CFSG.IsQuasisimple G := by
  obtain ⟨x, y, hxy⟩ := hna
  have hZ : center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
    · exact h
    · exact absurd (mem_center_iff.1 (h ▸ mem_top y) x) hxy
  have hperf : Group.IsPerfect G := by
    rw [Group.isPerfect_def]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
    · exfalso
      have hm : ⁅x, y⁆ ∈ commutator G := commutator_mem_commutator (mem_top x) (mem_top y)
      rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
      exact hxy hm
    · exact h
  let e : G ≃* G ⧸ center G :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  have : IsSimpleGroup (G ⧸ center G) := e.symm.isSimpleGroup
  refine ⟨hperf, this, e x, e y, fun h => hxy (e.injective ?_)⟩
  rw [map_mul, map_mul, h]

theorem eq_one_or_eq_of_mem_zpowers {a x : G} (ha : orderOf a = 2) (hx : x ∈ zpowers a) :
    x = 1 ∨ x = a := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
  rw [← zpow_mod_orderOf, ha]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [Nat.cast_ofNat, h, zpow_zero]
  · right
    rw [Nat.cast_ofNat, h, zpow_one]

theorem le_normalizer_of_le_centralizer {N X : Subgroup G}
    (h : X ≤ centralizer (N : Set G)) : X ≤ normalizer (N : Set G) :=
  h.trans (centralizer_le_normalizer _)

theorem not_four_dvd_card {a : G} (ha : orderOf a = 2) {C : Subgroup G} (haC : a ∈ C)
    (hidx : ¬ 2 ∣ (zpowers a).relIndex C) : ¬ 4 ∣ Nat.card C := by
  have h1 := relIndex_mul_card (H := zpowers a) (K := C)
  rw [inf_eq_left.2 ((zpowers_le (G := G)).2 haC), Nat.card_zpowers, ha] at h1
  intro h4
  rw [← h1] at h4
  have : 2 ∣ (zpowers a).relIndex C := by
    obtain ⟨m, hm⟩ := h4
    exact ⟨m, by omega⟩
  exact hidx this

end General

section Centerless

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem center_layer_eq_bot (hF : CFSG.fittingSubgroup G = ⊥) :
    (center (CFSG.layer G)).map (CFSG.layer G).subtype = ⊥ := by
  have := layer_characteristic (G := G)
  have hZeq : (center (CFSG.layer G)).map (CFSG.layer G).subtype =
      CFSG.layer G ⊓ centralizer (CFSG.layer G : Set G) := by
    ext g
    rw [mem_map_center_iff, mem_inf]
  have hZn : ((center (CFSG.layer G)).map (CFSG.layer G).subtype).Normal := by
    rw [hZeq]
    infer_instance
  have hZnil : Group.IsNilpotent ((center (CFSG.layer G)).map (CFSG.layer G).subtype) :=
    Group.nilpotent_of_mulEquiv (_h := inferInstance)
      ((center (CFSG.layer G)).equivMapOfInjective _ (CFSG.layer G).subtype_injective)
  have hZF := (fitting_characteristic (G := G)).2.2 _ hZn hZnil
  rwa [hF, le_bot_iff] at hZF

theorem center_eq_bot_of_fitting_eq_bot (hF : CFSG.fittingSubgroup G = ⊥) {K : Subgroup G}
    (hK : CFSG.IsComponent K) : center K = ⊥ := by
  have h := (layer_center (G := G)).2 K hK
  rw [center_layer_eq_bot hF, inf_bot_eq] at h
  exact (map_eq_bot_iff_of_injective _ K.subtype_injective).1 h.symm

omit [Finite G] in
theorem isSimpleGroup_of_isComponent {K : Subgroup G} (hK : CFSG.IsComponent K)
    (hZ : center K = ⊥) : IsSimpleGroup K ∧ ∃ x y : K, x * y ≠ y * x := by
  obtain ⟨-, hs, a, b, hab⟩ := hK.1
  let e : K ≃* K ⧸ center K :=
    QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
  refine ⟨e.isSimpleGroup, e.symm a, e.symm b, fun h => hab ?_⟩
  have h' := congrArg e h
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h'

variable (hZ : ∀ K : Subgroup G, CFSG.IsComponent K → center K = ⊥)
include hZ

theorem layerMulOnto_injective : Function.Injective (layerMulOnto G) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  obtain ⟨hc, -⟩ := ((layer_multiplication (G := G)).2.2.2.1 x).1 hx
  rw [mem_bot]
  funext K
  have h := hc K
  rw [hZ K.1 K.2, mem_bot] at h
  exact h

omit hZ in
noncomputable def layerCoord (hZ : ∀ K : Subgroup G, CFSG.IsComponent K → center K = ⊥)
    (K : ComponentIndex G) : CFSG.layer G →* K.1 :=
  (Pi.evalMonoidHom (fun K : ComponentIndex G => (K.1 : Subgroup G)) K).comp
    (MulEquiv.ofBijective (layerMulOnto G)
      ⟨layerMulOnto_injective hZ, layerMulOnto_surjective⟩).symm.toMonoidHom

theorem layerCoord_eq_one_iff (K : ComponentIndex G) (e : CFSG.layer G) :
    layerCoord hZ K e = 1 ↔ ∀ k ∈ K.1, k * e = e * k := by
  set φ := MulEquiv.ofBijective (layerMulOnto G)
    ⟨layerMulOnto_injective hZ, layerMulOnto_surjective⟩ with hφ
  have he : (e : G) = layerMul G (φ.symm e) := by
    have h := congrArg Subtype.val (φ.apply_symm_apply e)
    exact h.symm
  show φ.symm e K = 1 ↔ _
  constructor
  · intro h k hk
    rw [he]
    have hc := (commute_layerMul_iff (φ.symm e) K hk).2 (by rw [h]; exact Commute.one_right k)
    exact hc.eq
  · intro h
    have hc : φ.symm e K ∈ center K.1 := mem_center_iff.2 fun k => Subtype.ext (by
      have hk := h k k.2
      rw [he] at hk
      exact ((commute_layerMul_iff (φ.symm e) K k.2).1 hk).eq)
    rw [hZ K.1 K.2, mem_bot] at hc
    exact hc

end Centerless

section NormalLayer

variable {G : Type*} [Group G] [Finite G]

theorem eq_iSup_components_of_normal
    (hZE : (center (CFSG.layer G)).map (CFSG.layer G).subtype = ⊥)
    {V : Subgroup G} [V.Normal] (hVE : V ≤ CFSG.layer G) :
    V = ⨆ (K : Subgroup G) (_ : CFSG.IsComponent K ∧ K ≤ V), K := by
  refine le_antisymm ?_ (iSup₂_le fun K hK => hK.2)
  set V' := ⨆ (K : Subgroup G) (_ : CFSG.IsComponent K ∧ K ≤ V), K with hV'
  set V'' := ⨆ (K : Subgroup G) (_ : CFSG.IsComponent K ∧ ¬ K ≤ V), K with hV''
  have hE : CFSG.layer G = V' ⊔ V'' := by
    apply le_antisymm
    · refine sSup_le fun K hK => ?_
      by_cases h : K ≤ V
      · exact le_sup_of_le_left (le_iSup₂_of_le K ⟨hK, h⟩ le_rfl)
      · exact le_sup_of_le_right (le_iSup₂_of_le K ⟨hK, h⟩ le_rfl)
    · exact sup_le (iSup₂_le fun K hK => component_le_layer hK.1)
        (iSup₂_le fun K hK => component_le_layer hK.1)
  have hV''C : V'' ≤ centralizer (V : Set G) := iSup₂_le fun K hK => by
    rcases component_normal_subgroup hK.1 (inferInstance : V.Normal) with h | h
    · exact absurd h hK.2
    · exact commutator_eq_bot_iff_le_centralizer.1 h
  have hV''V' : V'' ≤ centralizer (V' : Set G) := by
    rw [le_centralizer_iff]
    refine iSup₂_le fun K' hK' => ?_
    rw [← le_centralizer_iff]
    refine iSup₂_le fun K hK => ?_
    rcases distinct_components_commute hK.1 hK'.1 with h | h
    · exact absurd (h ▸ hK'.2) hK.2
    · exact commutator_eq_bot_iff_le_centralizer.1 h
  intro x hx
  have hxE := hVE hx
  rw [hE, ← SetLike.mem_coe,
    coe_mul_of_right_le_normalizer_left V' V'' (le_normalizer_of_le_centralizer hV''V')] at hxE
  obtain ⟨y, hy, z, hz, rfl⟩ := hxE
  have hyV : y ∈ V := (iSup₂_le fun K hK => hK.2 : V' ≤ V) hy
  have hzV : z ∈ V := by
    have := V.mul_mem (V.inv_mem hyV) hx
    rwa [inv_mul_cancel_left] at this
  have hzZ : z ∈ (center (CFSG.layer G)).map (CFSG.layer G).subtype := by
    rw [mem_map_center_iff]
    refine ⟨hE ▸ mem_sup_right hz, ?_⟩
    rw [mem_centralizer_iff]
    intro g hg
    rw [hE] at hg
    have hle : V' ⊔ V'' ≤ centralizer ({z} : Set G) := by
      refine sup_le (fun w hw => ?_) (fun w hw => ?_)
      · rw [mem_centralizer_singleton_iff]
        exact mem_centralizer_iff.1 (hV''V' hz) w hw
      · rw [mem_centralizer_singleton_iff]
        exact (mem_centralizer_iff.1 (hV''C hw) z hzV).symm
    exact mem_centralizer_singleton_iff.1 (hle hg)
  rw [hZE, mem_bot] at hzZ
  show y * z ∈ V'
  rw [hzZ, mul_one]
  exact hy

end NormalLayer

section Core

variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
theorem map_center_le_fitting (N : Subgroup H) [N.Normal] :
    (center N).map N.subtype ≤ CFSG.fittingSubgroup H := by
  have hZeq : (center N).map N.subtype = N ⊓ centralizer (N : Set H) := by
    ext g
    rw [mem_map_center_iff, mem_inf]
  have hZn : ((center N).map N.subtype).Normal := by
    rw [hZeq]
    infer_instance
  have hZnil : Group.IsNilpotent ((center N).map N.subtype) :=
    Group.nilpotent_of_mulEquiv (_h := inferInstance)
      ((center N).equivMapOfInjective _ N.subtype_injective)
  exact (fitting_characteristic (G := H)).2.2 _ hZn hZnil

variable {J : Subgroup H} [IsSimpleGroup J]
  (hZ : ∀ K : Subgroup H, CFSG.IsComponent K → center K = ⊥)

include hZ in
theorem le_centralizer_or_inf_eq_bot (hJE : J ≤ CFSG.layer H) {L : Subgroup H}
    (hL : CFSG.IsComponent L) :
    J ≤ centralizer (L : Set H) ∨ (J ⊓ centralizer (L : Set H) = ⊥ ∧ Nat.card J ∣ Nat.card L) := by
  set f : J →* L := (layerCoord hZ ⟨L, hL⟩).comp (inclusion hJE) with hf
  have hker : ∀ j : J, f j = 1 ↔ (j : H) ∈ centralizer (L : Set H) := by
    intro j
    rw [hf, MonoidHom.comp_apply, layerCoord_eq_one_iff hZ ⟨L, hL⟩, mem_centralizer_iff]
    rfl
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · right
    refine ⟨eq_bot_iff.2 fun x hx => ?_, card_dvd_of_injective f ((MonoidHom.ker_eq_bot_iff f).1 h)⟩
    have hx' : (⟨x, hx.1⟩ : J) ∈ f.ker := (hker _).2 hx.2
    rw [h, mem_bot] at hx'
    exact mem_bot.2 (congrArg Subtype.val hx')
  · left
    intro j hj
    have hj' : (⟨j, hj⟩ : J) ∈ f.ker := h ▸ mem_top _
    exact (hker _).1 hj'

include hZ in
theorem inf_centralizer_eq_bot (hJ4 : 4 ∣ Nat.card J) (hJE : J ≤ CFSG.layer H)
    (hB4 : ¬ 4 ∣ Nat.card (centralizer (J : Set H))) {L : Subgroup H} (hL : CFSG.IsComponent L)
    (hLD : L ≤ normalClosure (J : Set H)) : J ⊓ centralizer (L : Set H) = ⊥ := by
  rcases le_centralizer_or_inf_eq_bot hZ hJE hL with hJL | h
  · exfalso
    have hex : ∃ g : H,
        ¬ J ≤ centralizer ((L.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup H) : Set H) := by
      by_contra hall
      push Not at hall
      have hD : normalClosure (J : Set H) ≤ centralizer (L : Set H) := by
        rw [normalClosure, closure_le]
        intro y hy
        obtain ⟨x, hx, hxy⟩ := Group.mem_conjugatesOfSet_iff.1 hy
        obtain ⟨c, rfl⟩ := isConj_iff.1 hxy
        rw [SetLike.mem_coe, mem_centralizer_iff]
        intro l hl
        have hl' : c⁻¹ * l * c ∈ L.map (MulAut.conj c⁻¹).toMonoidHom :=
          ⟨l, hl, by simp⟩
        have hcomm := mem_centralizer_iff.1 (hall c hx) _ hl'
        calc l * (c * x * c⁻¹) = c * ((c⁻¹ * l * c) * x) * c⁻¹ := by group
          _ = c * (x * (c⁻¹ * l * c)) * c⁻¹ := by rw [hcomm]
          _ = c * x * c⁻¹ * l := by group
      obtain ⟨x, y, hxy⟩ := (isSimpleGroup_of_isComponent hL (hZ L hL)).2
      exact hxy (Subtype.ext (mem_centralizer_iff.1 (hD (hLD y.2)) x x.2))
    obtain ⟨g, hg⟩ := hex
    have hL' := isComponent_map_mulEquiv (MulAut.conj g⁻¹) hL
    rcases le_centralizer_or_inf_eq_bot hZ hJE hL' with h' | ⟨-, hdvd⟩
    · exact hg h'
    · have h4 := hJ4.trans hdvd
      rw [card_map_of_injective (MulAut.conj g⁻¹).injective] at h4
      exact hB4 (h4.trans (card_dvd_of_le (le_centralizer_iff.1 hJL)))
  · exact h.1

omit [Finite H] [IsSimpleGroup J] in
theorem mem_centralizer_sup {A B : Subgroup H} {x : H} (hA : x ∈ centralizer (A : Set H))
    (hB : x ∈ centralizer (B : Set H)) : x ∈ centralizer ((A ⊔ B : Subgroup H) : Set H) := by
  rw [← zpowers_le, le_centralizer_iff] at hA hB ⊢
  exact sup_le hA hB

omit [Finite H] [IsSimpleGroup J] in
theorem conj_conj_of_orderOf_two {a : H} (ha : orderOf a = 2) (x : H) :
    (MulAut.conj a⁻¹).toMonoidHom ((MulAut.conj a⁻¹).toMonoidHom x) = x := by
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hainv]
  calc a * (a * x * a) * a = (a * a) * x * (a * a) := by group
    _ = x := by rw [haa, one_mul, mul_one]

omit [IsSimpleGroup J] in
theorem components_le_pair (hJna : ∃ x y : J, x * y ≠ y * x) (hJE : J ≤ CFSG.layer H)
    {a : H} (ha : orderOf a = 2) (hJa : J ≤ centralizer ({a} : Set H))
    (hJn : centralizer ({a} : Set H) ≤ normalizer (J : Set H))
    (hA : ∀ L : Subgroup H, CFSG.IsComponent L → L ≤ normalClosure (J : Set H) →
      J ⊓ centralizer (L : Set H) = ⊥)
    (hDZ : normalClosure (J : Set H) ⊓ centralizer (normalClosure (J : Set H) : Set H) = ⊥)
    (hDeq : normalClosure (J : Set H) =
      ⨆ (K : Subgroup H) (_ : CFSG.IsComponent K ∧ K ≤ normalClosure (J : Set H)), K)
    {K₀ : Subgroup H} (hK₀ : CFSG.IsComponent K₀) (hK₀D : K₀ ≤ normalClosure (J : Set H))
    {L : Subgroup H} (hL : CFSG.IsComponent L) (hLD : L ≤ normalClosure (J : Set H)) :
    L = K₀ ∨ L = K₀.map (MulAut.conj a⁻¹).toMonoidHom := by
  by_contra hne
  push Not at hne
  obtain ⟨hLK₀, hLK₁⟩ := hne
  set D := normalClosure (J : Set H) with hDdef
  set c : H →* H := (MulAut.conj a⁻¹).toMonoidHom with hc
  have hcc : ∀ x, c (c x) = x := conj_conj_of_orderOf_two ha
  have hc_apply : ∀ x, c x = a⁻¹ * x * a := fun x => by
    rw [hc]
    simp
  set K₁ := K₀.map c with hK₁
  have hK₁c : CFSG.IsComponent K₁ := isComponent_map_mulEquiv _ hK₀
  have hDc : ∀ x ∈ D, c x ∈ D := fun x hx => by
    rw [hc_apply]
    have := (normalClosure_normal (s := (J : Set H))).conj_mem x hx a⁻¹
    rwa [inv_inv] at this
  have hK₁D : K₁ ≤ D := by
    rintro _ ⟨x, hx, rfl⟩
    exact hDc x (hK₀D hx)
  have hmapc : ∀ K : Subgroup H, (K.map c).map c = K := fun K => by
    rw [Subgroup.map_map]
    convert Subgroup.map_id K
    ext x
    exact hcc x
  set M := K₀ ⊔ K₁ with hM
  set M' := ⨆ (K : Subgroup H) (_ : CFSG.IsComponent K ∧ K ≤ D ∧ K ≠ K₀ ∧ K ≠ K₁), K with hM'
  have hDMM : D = M ⊔ M' := by
    apply le_antisymm
    · calc D = ⨆ (K : Subgroup H) (_ : CFSG.IsComponent K ∧ K ≤ D), K := hDeq
        _ ≤ M ⊔ M' := by
          refine iSup₂_le fun K hK => ?_
          by_cases h0 : K = K₀
          · rw [h0]
            exact le_sup_of_le_left le_sup_left
          by_cases h1 : K = K₁
          · rw [h1]
            exact le_sup_of_le_left le_sup_right
          exact le_sup_of_le_right (le_iSup₂_of_le K ⟨hK.1, hK.2, h0, h1⟩ le_rfl)
    · exact sup_le (sup_le hK₀D hK₁D) (iSup₂_le fun K hK => hK.2.1)
  have hcomp : ∀ K K' : Subgroup H, CFSG.IsComponent K → CFSG.IsComponent K' → K ≠ K' →
      K ≤ centralizer (K' : Set H) := fun K K' hK hK' hne => by
    rcases distinct_components_commute hK hK' with h | h
    · exact absurd h hne
    · exact commutator_eq_bot_iff_le_centralizer.1 h
  have hM'M : M' ≤ centralizer (M : Set H) := by
    refine iSup₂_le fun K hK => ?_
    rw [le_centralizer_iff]
    exact sup_le (le_centralizer_iff.1 (hcomp K K₀ hK.1 hK₀ hK.2.2.1))
      (le_centralizer_iff.1 (hcomp K K₁ hK.1 hK₁c hK.2.2.2))
  have hcomm1 : ∀ m ∈ M, ∀ m' ∈ M', m * m' = m' * m := fun m hm m' hm' =>
    mem_centralizer_iff.1 (hM'M hm') m hm
  have hML : M ≤ centralizer (L : Set H) :=
    sup_le (hcomp _ _ hK₀ hL (Ne.symm hLK₀)) (hcomp _ _ hK₁c hL (Ne.symm hLK₁))
  have hM'K₀ : M' ≤ centralizer (K₀ : Set H) :=
    iSup₂_le fun K hK => hcomp K K₀ hK.1 hK₀ hK.2.2.1
  have hMM' : ∀ x ∈ M, x ∈ M' → x = 1 := fun x hxM hxM' => by
    have hx : x ∈ D ⊓ centralizer (D : Set H) := by
      refine ⟨hDMM ▸ mem_sup_left hxM, ?_⟩
      rw [hDMM]
      refine mem_centralizer_sup (hM'M hxM') ?_
      exact (le_centralizer_iff.1 hM'M) hxM
    rw [hDZ, mem_bot] at hx
    exact hx
  have hcM : ∀ x ∈ M, c x ∈ M := by
    have h : M.map c ≤ M := by
      rw [hM, Subgroup.map_sup, hmapc]
      exact sup_le le_sup_right le_sup_left
    exact fun x hx => h (mem_map_of_mem c hx)
  have hcM' : ∀ x ∈ M', c x ∈ M' := by
    have h : M'.map c ≤ M' := by
      rw [hM', Subgroup.map_iSup]
      refine iSup_le fun K => ?_
      rw [Subgroup.map_iSup]
      refine iSup_le fun hK => ?_
      refine le_iSup₂_of_le (K.map c) ⟨isComponent_map_mulEquiv _ hK.1, ?_, ?_, ?_⟩ le_rfl
      · rintro _ ⟨x, hx, rfl⟩
        exact hDc x (hK.2.1 hx)
      · intro h
        apply hK.2.2.2
        rw [← hmapc K, h]
      · intro h
        exact hK.2.2.1 (Subgroup.map_injective (MulAut.conj a⁻¹).injective h)
    exact fun x hx => h (mem_map_of_mem c hx)
  have hsplit : ∀ j ∈ J, ∃ m ∈ M, ∃ m' ∈ M', j = m * m' ∧ c m = m := by
    intro j hj
    have hjD : j ∈ D := le_normalClosure hj
    have hcj : c j = j := by
      rw [hc_apply]
      have := mem_centralizer_singleton_iff.1 (hJa hj)
      rw [mul_assoc, this, inv_mul_cancel_left]
    rw [hDMM, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right M M'
      (le_normalizer_of_le_centralizer (le_centralizer_iff.1 hM'M))] at hjD
    obtain ⟨m, hm, m', hm', rfl⟩ := hjD
    refine ⟨m, hm, m', hm', rfl, ?_⟩
    rw [map_mul] at hcj
    have hmm : m⁻¹ * c m = m' * (c m')⁻¹ := by
      calc m⁻¹ * c m = m⁻¹ * (c m * c m') * (c m')⁻¹ := by group
        _ = m⁻¹ * (m * m') * (c m')⁻¹ := by rw [hcj]
        _ = m' * (c m')⁻¹ := by group
    have h1 := hMM' (m⁻¹ * c m) (M.mul_mem (M.inv_mem hm) (hcM m hm))
      (hmm ▸ M'.mul_mem hm' (M'.inv_mem (hcM' m' hm')))
    calc c m = m * (m⁻¹ * c m) := by group
      _ = m := by rw [h1, mul_one]
  have hJM : ∀ x ∈ J, x ∈ M → x = 1 := fun x hxJ hxM => by
    have hx : x ∈ J ⊓ centralizer (L : Set H) := ⟨hxJ, hML hxM⟩
    rw [hA L hL hLD, mem_bot] at hx
    exact hx
  have hJM' : ∀ x ∈ J, x ∈ M' → x = 1 := fun x hxJ hxM' => by
    have hx : x ∈ J ⊓ centralizer (K₀ : Set H) := ⟨hxJ, hM'K₀ hxM'⟩
    rw [hA K₀ hK₀ hK₀D, mem_bot] at hx
    exact hx
  have hJcomm : ∀ j ∈ J, ∀ m ∈ M, c m = m → j * m = m * j := by
    intro j hj m hm hcm
    have hma : m ∈ centralizer ({a} : Set H) := by
      rw [mem_centralizer_singleton_iff]
      rw [hc_apply] at hcm
      calc m * a = a * (a⁻¹ * m * a) := by group
        _ = a * m := by rw [hcm]
    have h1 : j * m * j⁻¹ * m⁻¹ ∈ J := by
      have h := (mem_normalizer_iff.1 (hJn hma) j⁻¹).1 (J.inv_mem hj)
      have h' := J.mul_mem hj h
      rwa [← mul_assoc, ← mul_assoc] at h'
    have h2 : j * m * j⁻¹ * m⁻¹ ∈ M := by
      have hjn : j ∈ normalizer (M : Set H) := inf_normalizer_le_normalizer_sup K₀ K₁
        ⟨layer_le_normalizer hK₀ (hJE hj), layer_le_normalizer hK₁c (hJE hj)⟩
      exact M.mul_mem ((mem_normalizer_iff.1 hjn m).1 hm) (M.inv_mem hm)
    have h3 := hJM _ h1 h2
    calc j * m = (j * m * j⁻¹ * m⁻¹) * (m * j) := by group
      _ = m * j := by rw [h3, one_mul]
  obtain ⟨x, y, hxy⟩ := hJna
  apply hxy
  obtain ⟨m₁, hm₁, m₁', hm₁', hx, hcm₁⟩ := hsplit x x.2
  obtain ⟨m₂, hm₂, m₂', hm₂', hy, hcm₂⟩ := hsplit y y.2
  have hc12 : m₁ * m₂ = m₂ * m₁ := by
    have h := hJcomm x x.2 m₂ hm₂ hcm₂
    rw [hx] at h
    have h' : m₁ * m₂ * m₁' = m₂ * m₁ * m₁' := by
      calc m₁ * m₂ * m₁' = m₁ * (m₂ * m₁') := by group
        _ = m₁ * (m₁' * m₂) := by rw [hcomm1 m₂ hm₂ m₁' hm₁']
        _ = m₁ * m₁' * m₂ := by group
        _ = m₂ * (m₁ * m₁') := h
        _ = m₂ * m₁ * m₁' := by group
    exact mul_right_cancel h'
  have exy : (x : H) * y = (m₁ * m₂) * (m₁' * m₂') := by
    rw [hx, hy]
    calc m₁ * m₁' * (m₂ * m₂') = m₁ * (m₁' * m₂) * m₂' := by group
      _ = m₁ * (m₂ * m₁') * m₂' := by rw [← hcomm1 m₂ hm₂ m₁' hm₁']
      _ = m₁ * m₂ * (m₁' * m₂') := by group
  have eyx : (y : H) * x = (m₁ * m₂) * (m₂' * m₁') := by
    rw [hx, hy]
    calc m₂ * m₂' * (m₁ * m₁') = m₂ * (m₂' * m₁) * m₁' := by group
      _ = m₂ * (m₁ * m₂') * m₁' := by rw [← hcomm1 m₁ hm₁ m₂' hm₂']
      _ = m₂ * m₁ * (m₂' * m₁') := by group
      _ = m₁ * m₂ * (m₂' * m₁') := by rw [← hc12]
  have hmem : ((y : H) * x)⁻¹ * (x * y) ∈ M' := by
    rw [exy, eyx]
    have e : (m₁ * m₂ * (m₂' * m₁'))⁻¹ * (m₁ * m₂ * (m₁' * m₂')) =
        (m₂' * m₁')⁻¹ * (m₁' * m₂') := by group
    rw [e]
    exact M'.mul_mem (M'.inv_mem (M'.mul_mem hm₂' hm₁')) (M'.mul_mem hm₁' hm₂')
  have h1 := hJM' _ (J.mul_mem (J.inv_mem (J.mul_mem y.2 x.2)) (J.mul_mem x.2 y.2)) hmem
  apply Subtype.ext
  show (x : H) * y = y * x
  calc (x : H) * y = (y * x) * (((y : H) * x)⁻¹ * (x * y)) := by group
    _ = y * x := by rw [h1, mul_one]

include hZ in
theorem two_factor_data {a : H} (ha : orderOf a = 2) (hJa : J ≤ centralizer ({a} : Set H))
    (hJn : centralizer ({a} : Set H) ≤ normalizer (J : Set H)) {D D₁ : Subgroup H}
    (hD₁ : CFSG.IsComponent D₁) (hne : D₁ ≠ D₁.map (MulAut.conj a⁻¹).toMonoidHom)
    (hD : D = D₁ ⊔ D₁.map (MulAut.conj a⁻¹).toMonoidHom) (hJD : J ≤ D) :
    J = D ⊓ centralizer ({a} : Set H) ∧
      ∃ ψ : D ≃* J × J,
        (∀ (j : H) (hjJ : j ∈ J) (hjD : j ∈ D), ψ ⟨j, hjD⟩ = (⟨j, hjJ⟩, ⟨j, hjJ⟩)) ∧
        ∀ (d : H) (hd : d ∈ D) (hda : a⁻¹ * d * a ∈ D),
          ψ ⟨a⁻¹ * d * a, hda⟩ = (ψ ⟨d, hd⟩).swap := by
  classical
  set c : H →* H := (MulAut.conj a⁻¹).toMonoidHom with hc
  have hcc : ∀ x, c (c x) = x := conj_conj_of_orderOf_two ha
  have hc_apply : ∀ x, c x = a⁻¹ * x * a := fun x => by
    rw [hc]
    simp
  have hcfix : ∀ z, c z = z ↔ z ∈ centralizer ({a} : Set H) := fun z => by
    rw [hc_apply, mem_centralizer_singleton_iff]
    constructor
    · intro h
      calc z * a = a * (a⁻¹ * z * a) := by group
        _ = a * z := by rw [h]
    · intro h
      rw [mul_assoc, h, inv_mul_cancel_left]
  set D₂ := D₁.map c with hD₂def
  have hD₂ : CFSG.IsComponent D₂ := isComponent_map_mulEquiv _ hD₁
  have hcomm : ∀ x ∈ D₁, ∀ y ∈ D₂, x * y = y * x := by
    intro x hx y hy
    rcases distinct_components_commute hD₁ hD₂ with h | h
    · exact absurd h hne
    · exact (mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 h hx) y hy).symm
  have hcap : ∀ x ∈ D₁, x ∈ D₂ → x = 1 := by
    intro x hx₁ hx₂
    have hz : (⟨x, hx₁⟩ : D₁) ∈ center D₁ := mem_center_iff.2 fun g =>
      Subtype.ext (hcomm g g.2 x hx₂)
    rw [hZ D₁ hD₁, mem_bot] at hz
    exact congrArg Subtype.val hz
  have hc₁ : ∀ x ∈ D₁, c x ∈ D₂ := fun x hx => mem_map_of_mem c hx
  have hc₂ : ∀ y ∈ D₂, c y ∈ D₁ := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hcc]
    exact hx
  have hD₁D : D₁ ≤ D := hD ▸ le_sup_left
  have hD₂D : D₂ ≤ D := hD ▸ le_sup_right
  have hsplit : ∀ d ∈ D, ∃ x ∈ D₁, ∃ y ∈ D₂, d = x * y := by
    intro d hd
    rw [hD, ← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right D₁ D₂
      (le_normalizer_of_le_centralizer fun x hx => mem_centralizer_iff.2 fun y hy =>
        (hcomm x hx y hy).symm)] at hd
    obtain ⟨x, hx, y, hy, rfl⟩ := hd
    exact ⟨x, hx, y, hy, rfl⟩
  let δ : D₁ →* H :=
    { toFun := fun x => (x : H) * c x
      map_one' := by simp
      map_mul' := fun x y => by
        show ((x : H) * y) * c ((x : H) * y) = ((x : H) * c x) * ((y : H) * c y)
        rw [map_mul]
        calc (x : H) * y * (c x * c y) = x * (y * c x) * c y := by group
          _ = x * (c x * y) * c y := by rw [hcomm y y.2 (c x) (hc₁ x x.2)]
          _ = x * c x * (y * c y) := by group }
  have hδ : ∀ x : D₁, δ x = (x : H) * c x := fun x => rfl
  have hδinj : Function.Injective δ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, hδ] at hx
    have hx' : (x : H) = (c x)⁻¹ := eq_inv_of_mul_eq_one_left hx
    have h1 := hcap x x.2 (hx' ▸ D₂.inv_mem (hc₁ x x.2))
    exact mem_bot.2 (Subtype.ext h1)
  have hδrange : δ.range = D ⊓ centralizer ({a} : Set H) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      refine ⟨D.mul_mem (hD₁D x.2) (hD₂D (hc₁ x x.2)), (hcfix _).1 ?_⟩
      rw [hδ, map_mul, hcc]
      exact (hcomm x x.2 (c x) (hc₁ x x.2)).symm
    · rintro d ⟨hd, hda⟩
      obtain ⟨x, hx, y, hy, rfl⟩ := hsplit d hd
      have hcd := (hcfix _).2 hda
      rw [map_mul] at hcd
      have h1 : x⁻¹ * c y = y * (c x)⁻¹ := by
        calc x⁻¹ * c y = x⁻¹ * (c y * c x) * (c x)⁻¹ := by group
          _ = x⁻¹ * (c x * c y) * (c x)⁻¹ := by rw [hcomm (c y) (hc₂ y hy) (c x) (hc₁ x hx)]
          _ = x⁻¹ * (x * y) * (c x)⁻¹ := by rw [hcd]
          _ = y * (c x)⁻¹ := by group
      have h2 := hcap _ (D₁.mul_mem (D₁.inv_mem hx) (hc₂ y hy))
        (h1 ▸ D₂.mul_mem hy (D₂.inv_mem (hc₁ x hx)))
      have hyx : y = c x := by
        have : c y = x := by
          calc c y = x * (x⁻¹ * c y) := by group
            _ = x := by rw [h2, mul_one]
        rw [← this, hcc]
      exact ⟨⟨x, hx⟩, by rw [hδ, hyx]⟩
  have hJC : J ≤ D ⊓ centralizer ({a} : Set H) := le_inf hJD hJa
  have hsimpleC : IsSimpleGroup (D ⊓ centralizer ({a} : Set H) : Subgroup H) := by
    have := (isSimpleGroup_of_isComponent hD₁ (hZ D₁ hD₁)).1
    exact ((MonoidHom.ofInjective hδinj).trans
      (MulEquiv.subgroupCongr hδrange)).symm.isSimpleGroup
  have hJeq : J = D ⊓ centralizer ({a} : Set H) := by
    refine le_antisymm hJC ?_
    have hn : (J.subgroupOf (D ⊓ centralizer ({a} : Set H))).Normal :=
      (normal_subgroupOf_iff_le_normalizer hJC).2 (inf_le_right.trans hJn)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (J.subgroupOf (D ⊓ centralizer ({a} : Set H))) with h | h
    · exfalso
      obtain ⟨j, hj1⟩ := exists_ne (1 : J)
      have hj : (⟨j, hJC j.2⟩ : (D ⊓ centralizer ({a} : Set H) : Subgroup H)) ∈
          J.subgroupOf (D ⊓ centralizer ({a} : Set H)) := j.2
      rw [h, mem_bot] at hj
      have h' : (j : H) = 1 := congrArg Subtype.val hj
      exact hj1 (Subtype.ext h')
    · intro x hx
      have : (⟨x, hx⟩ : (D ⊓ centralizer ({a} : Set H) : Subgroup H)) ∈
          J.subgroupOf (D ⊓ centralizer ({a} : Set H)) := h ▸ mem_top _
      exact this
  refine ⟨hJeq, ?_⟩
  let e : D₁ ≃* J :=
    (MonoidHom.ofInjective hδinj).trans (MulEquiv.subgroupCongr (hδrange.trans hJeq.symm))
  have he : ∀ x : D₁, ((e x : J) : H) = (x : H) * c x := fun x => rfl
  have he' : ∀ j : J, ((e.symm j : D₁) : H) * c (e.symm j) = j := fun j => by
    rw [← he, MulEquiv.apply_symm_apply]
  let f : J →* H := D₁.subtype.comp e.symm.toMonoidHom
  have hf1 : ∀ j, f j ∈ D₁ := fun j => (e.symm j).2
  let g : J →* H := c.comp f
  have hcfg : ∀ j k, Commute (f j) (g k) := fun j k => hcomm _ (hf1 j) _ (hc₁ _ (hf1 k))
  let Φ₀ : J × J →* H := f.noncommCoprod g hcfg
  have hΦ₀ : ∀ p : J × J, Φ₀ p = f p.1 * c (f p.2) := fun p => rfl
  have hΦD : ∀ p, Φ₀ p ∈ D := fun p => D.mul_mem (hD₁D (hf1 p.1)) (hD₂D (hc₁ _ (hf1 p.2)))
  let Φ : J × J →* D := Φ₀.codRestrict D hΦD
  have hΦinj : Function.Injective Φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨j₁, j₂⟩ hp
    have hp' : f j₁ * c (f j₂) = 1 := congrArg Subtype.val hp
    have hx : f j₁ = (c (f j₂))⁻¹ := eq_inv_of_mul_eq_one_left hp'
    have h1 : f j₁ = 1 := hcap _ (hf1 j₁) (hx ▸ D₂.inv_mem (hc₁ _ (hf1 j₂)))
    rw [h1, one_mul] at hp'
    have h2 : f j₂ = 1 := by rw [← hcc (f j₂), hp', map_one]
    have hj : ∀ j : J, f j = 1 → j = 1 := fun j hj => by
      have : e.symm j = 1 := Subtype.ext hj
      rw [← e.apply_symm_apply j, this, map_one]
    rw [mem_bot, hj j₁ h1, hj j₂ h2]
    rfl
  have hΦsurj : Function.Surjective Φ := by
    rintro ⟨d, hd⟩
    obtain ⟨x, hx, y, hy, rfl⟩ := hsplit d hd
    refine ⟨(e ⟨x, hx⟩, e ⟨c y, hc₂ y hy⟩), Subtype.ext ?_⟩
    show f (e ⟨x, hx⟩) * c (f (e ⟨c y, hc₂ y hy⟩)) = x * y
    simp only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      Subgroup.coe_subtype]
    rw [hcc]
  set Ψ := MulEquiv.ofBijective Φ ⟨hΦinj, hΦsurj⟩ with hΨ
  refine ⟨Ψ.symm, fun j hjJ hjD => ?_, fun d hd hda => ?_⟩
  · rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    show j = f ⟨j, hjJ⟩ * c (f ⟨j, hjJ⟩)
    exact (he' ⟨j, hjJ⟩).symm
  · rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    set p := Ψ.symm ⟨d, hd⟩ with hp
    have hpd : f p.1 * c (f p.2) = d := by
      have := congrArg Subtype.val (Ψ.apply_symm_apply ⟨d, hd⟩)
      exact this
    show a⁻¹ * d * a = f p.2 * c (f p.1)
    rw [← hc_apply, ← hpd, map_mul, hcc]
    exact hcomm _ (hf1 p.2) _ (hc₁ _ (hf1 p.1)) |>.symm

end Core

end OneOrTwoLayer

open OneOrTwoLayer in
theorem nonnormal_involution_component_layer_of_schreier
    (hS : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Blueprint.Catalog) :
    NonnormalInvolutionComponentLayerStmt := by
  intro H _ _ hK hcore J hJs hJna hJ4 a ha hJa hJn hsyl hJnn
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have haB : a ∈ centralizer (J : Set H) := mem_centralizer_iff.2 fun j hj =>
    mem_centralizer_singleton_iff.1 (hJa hj)
  have hB4 := not_four_dvd_card ha haB hsyl
  have hJ4' : 4 ∣ Nat.card J := by
    obtain ⟨E, hEJ, -, hE4⟩ := hJ4
    rw [← hE4]
    exact card_dvd_of_le hEJ
  have hJ1 : ∃ j : J, j ≠ 1 := exists_ne 1
  set L₀ := J.subgroupOf (centralizer ({a} : Set H)) with hL₀def
  have hL₀ : CFSG.IsComponent L₀ :=
    ⟨isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hJa).symm (isQuasisimple_of_simple hJna),
      ((normal_subgroupOf_iff_le_normalizer hJa).2 hJn).isSubnormal⟩
  have hL₀map : L₀.map (centralizer ({a} : Set H)).subtype = J := by
    rw [hL₀def, subgroupOf_map_subtype, inf_eq_left.2 hJa]
  set B := centralizer (J : Set H) with hBdef
  have hza : IsPGroup 2 (zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  have hP2 : IsPGroup 2 ((zpowers a).subgroupOf B) :=
    hza.comap_of_injective _ B.subtype_injective
  have hsyl' : ¬ 2 ∣ ((zpowers a).subgroupOf B).index := by
    rwa [Subgroup.relIndex] at hsyl
  set S₀ := hP2.toSylow hsyl' with hS₀def
  have hmemS₀ : ∀ x : B, x ∈ S₀ → (x : H) = 1 ∨ (x : H) = a := fun x hx => by
    rw [hS₀def, IsPGroup.mem_toSylow] at hx
    exact eq_one_or_eq_of_mem_zpowers ha hx
  have hO2 : CFSG.pCore 2 H = ⊥ := by
    have hcomm := CFSG.LocalAnalysis.ComponentInitial.involution_component_centralizes_two_core
      ha L₀ hL₀
    rw [hL₀map, commutator_comm] at hcomm
    have hQB : CFSG.pCore 2 H ≤ B := commutator_eq_bot_iff_le_centralizer.1 hcomm
    have hN2 : IsPGroup 2 ((CFSG.pCore 2 H).subgroupOf B) :=
      CFSG.pCore_isPGroup.comap_of_injective _ B.subtype_injective
    have hle := hN2.le_sylow_of_normal S₀
    have hQa : ∀ q ∈ CFSG.pCore 2 H, q = 1 ∨ q = a := fun q hq =>
      hmemS₀ ⟨q, hQB hq⟩ (hle hq)
    by_contra hne
    obtain ⟨⟨q, hq⟩, hq1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    have hqa : q = a := (hQa q hq).resolve_left fun h => hq1 (Subtype.ext h)
    rw [hqa] at hq
    apply hJnn
    have htop : centralizer ({a} : Set H) = ⊤ := by
      refine eq_top_iff.2 fun g _ => mem_centralizer_singleton_iff.2 ?_
      have hm : g * a * g⁻¹ ∈ CFSG.pCore 2 H :=
        (inferInstance : (CFSG.pCore 2 H).Normal).conj_mem a hq g
      rcases hQa _ hm with h | h
      · exfalso
        have h1 : a = 1 := by
          calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
            _ = 1 := by rw [h]; group
        rw [h1, orderOf_one] at ha
        exact absurd ha (by norm_num)
      · calc g * a = g * a * g⁻¹ * g := by group
          _ = a * g := by rw [h]
    exact normalizer_eq_top_iff.1 (top_le_iff.1 (htop ▸ hJn))
  have hF : CFSG.fittingSubgroup H = ⊥ := by
    rw [fittingSubgroup_eq_iSup_pCore, eq_bot_iff]
    refine iSup_le fun p => ?_
    have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    by_cases hp2 : (p : ℕ) = 2
    · rw [hp2, hO2]
    · rw [← hcore]
      have : Fact (p : ℕ).Prime := ⟨hp⟩
      refine le_sSup ⟨inferInstance, ?_⟩
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := (p : ℕ)) (G := H))
      rw [hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have hJE : J ≤ CFSG.layer H := by
    have h := ComponentInitial.kProper_odd_core_free_involution_component_enters_layer hS hK
      hcore ha L₀ hL₀
    rwa [hL₀map] at h
  have hZ : ∀ K : Subgroup H, CFSG.IsComponent K → center K = ⊥ := fun K hK =>
    center_eq_bot_of_fitting_eq_bot hF hK
  have hZE := center_layer_eq_bot hF
  set D := normalClosure (J : Set H) with hDdef
  have hJD : J ≤ D := le_normalClosure
  have hDE : D ≤ CFSG.layer H := by
    have := layer_characteristic (G := H)
    exact normalClosure_le_normal hJE
  have hDeq := eq_iSup_components_of_normal hZE hDE
  have hDZ : D ⊓ centralizer (D : Set H) = ⊥ := by
    have h := map_center_le_fitting D
    rw [hF, le_bot_iff] at h
    refine eq_bot_iff.2 fun x hx => ?_
    have hx' : x ∈ (center D).map D.subtype := (mem_map_center_iff D).2 ⟨hx.1, hx.2⟩
    rwa [h] at hx'
  have hA : ∀ L : Subgroup H, CFSG.IsComponent L → L ≤ D → J ⊓ centralizer (L : Set H) = ⊥ :=
    fun L hL hLD => inf_centralizer_eq_bot hZ hJ4' hJE hB4 hL hLD
  have hcomp_ne : ∀ K : Subgroup H, CFSG.IsComponent K → K ≠ ⊥ := fun K hK =>
    (Subgroup.nontrivial_iff_ne_bot K).1 (isQuasisimple_nontrivial hK.1)
  obtain ⟨K₀, hK₀, hK₀D⟩ : ∃ K₀ : Subgroup H, CFSG.IsComponent K₀ ∧ K₀ ≤ D := by
    by_contra hno
    push Not at hno
    have hDbot : D = ⊥ := hDeq.trans (iSup₂_eq_bot.2 fun K hK => absurd hK.2 (hno K hK.1))
    obtain ⟨j, hj1⟩ := hJ1
    have hj := hJD j.2
    rw [hDbot, mem_bot] at hj
    exact hj1 (Subtype.ext hj)
  set c : H →* H := (MulAut.conj a⁻¹).toMonoidHom with hc
  have hc_apply : ∀ x, c x = a⁻¹ * x * a := fun x => by
    rw [hc]
    simp
  set K₁ := K₀.map c with hK₁def
  have hK₁ : CFSG.IsComponent K₁ := isComponent_map_mulEquiv _ hK₀
  have hK₁D : K₁ ≤ D := by
    rintro _ ⟨x, hx, rfl⟩
    rw [hc_apply]
    have := (normalClosure_normal (s := (J : Set H))).conj_mem x (hK₀D hx) a⁻¹
    rwa [inv_inv] at this
  have hpair : ∀ L : Subgroup H, CFSG.IsComponent L → L ≤ D → L = K₀ ∨ L = K₁ :=
    fun L hL hLD => components_le_pair hJna hJE ha hJa hJn hA hDZ hDeq hK₀ hK₀D hL hLD
  have hDK : D = K₀ ⊔ K₁ := by
    apply le_antisymm
    · calc D = ⨆ (K : Subgroup H) (_ : CFSG.IsComponent K ∧ K ≤ D), K := hDeq
        _ ≤ K₀ ⊔ K₁ := iSup₂_le fun K hK => by
          rcases hpair K hK.1 hK.2 with h | h
          · rw [h]
            exact le_sup_left
          · rw [h]
            exact le_sup_right
    · exact sup_le hK₀D hK₁D
  have hsimple₀ := isSimpleGroup_of_isComponent hK₀ (hZ K₀ hK₀)
  have hsimple₁ := isSimpleGroup_of_isComponent hK₁ (hZ K₁ hK₁)
  have hJDne : J ≠ D := fun h => hJnn (h ▸ normalClosure_normal)
  have halt : OneOrTwoLayerAlternatives J D a ∧ ∃ d ∈ D, a⁻¹ * d * a ≠ d := by
    by_cases h01 : K₁ = K₀
    · have hD0 : D = K₀ := by rw [hDK, h01, sup_idem]
      have hDs : IsSimpleGroup D := by
        rw [hD0]
        exact hsimple₀.1
      have hnt : ∃ d ∈ D, a⁻¹ * d * a ≠ d := by
        by_contra hall
        push Not at hall
        have hDa : D ≤ centralizer ({a} : Set H) := fun d hd => by
          rw [mem_centralizer_singleton_iff]
          calc d * a = a * (a⁻¹ * d * a) := by group
            _ = a * d := by rw [hall d hd]
        have hn : (J.subgroupOf D).Normal :=
          (normal_subgroupOf_iff_le_normalizer hJD).2 (hDa.trans hJn)
        rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (J.subgroupOf D) with h | h
        · obtain ⟨j, hj1⟩ := hJ1
          have hj : (⟨j, hJD j.2⟩ : D) ∈ J.subgroupOf D := j.2
          rw [h, mem_bot] at hj
          have hj' : (j : H) = 1 := congrArg Subtype.val hj
          exact hj1 (Subtype.ext hj')
        · apply hJDne
          refine le_antisymm hJD fun x hx => ?_
          have : (⟨x, hx⟩ : D) ∈ J.subgroupOf D := h ▸ mem_top _
          exact this
      refine ⟨Or.inl ⟨⟨hDs, ?_, lt_of_le_of_ne hJD hJDne, hnt⟩, ?_⟩, hnt⟩
      · obtain ⟨x, y, hxy⟩ := hsimple₀.2
        refine ⟨⟨x, hD0 ▸ x.2⟩, ⟨y, hD0 ▸ y.2⟩, fun h => ?_⟩
        have h' : (x : H) * y = y * x := congrArg Subtype.val h
        exact hxy (Subtype.ext h')
      · rintro ⟨D₁, D₂, hD₁, hD₂, hne, -, -, -, -, hsup, -⟩
        have h1 := hpair D₁ hD₁ (hsup ▸ le_sup_left)
        have h2 := hpair D₂ hD₂ (hsup ▸ le_sup_right)
        rw [h01] at h1 h2
        exact hne ((h1.elim id id).trans (h2.elim id id).symm)
    · obtain ⟨hJeq, ψ, hψ1, hψ2⟩ := two_factor_data hZ ha hJa hJn hK₀ (Ne.symm h01) hDK hJD
      have hcomm : ⁅K₀, K₁⁆ = ⊥ :=
        (distinct_components_commute hK₀ hK₁).resolve_left (Ne.symm h01)
      have hinf : K₀ ⊓ K₁ = ⊥ := by
        refine eq_bot_iff.2 fun x hx => ?_
        have hz : (⟨x, hx.1⟩ : K₀) ∈ center K₀ := mem_center_iff.2 fun g => Subtype.ext
          (mem_centralizer_iff.1 (commutator_eq_bot_iff_le_centralizer.1 hcomm g.2) x hx.2).symm
        rw [hZ K₀ hK₀, mem_bot] at hz
        exact mem_bot.2 (congrArg Subtype.val hz)
      have hnt : ∃ d ∈ D, a⁻¹ * d * a ≠ d := by
        by_contra hall
        push Not at hall
        apply h01
        refine le_antisymm ?_ ?_
        · rintro _ ⟨x, hx, rfl⟩
          rw [hc_apply, hall x (hK₀D hx)]
          exact hx
        · intro x hx
          refine ⟨x, hx, ?_⟩
          rw [hc_apply, hall x (hK₀D hx)]
      refine ⟨Or.inr ⟨⟨K₀, K₁, hK₀, hK₁, Ne.symm h01, hsimple₀.1, hsimple₀.2, hsimple₁.1,
        hsimple₁.2, hDK.symm, hinf, hcomm, rfl, hJeq, ψ, hψ1, hψ2⟩, ?_⟩, hnt⟩
      rintro ⟨hDs, -⟩
      have hn : (K₀.subgroupOf D).Normal :=
        (normal_subgroupOf_iff_le_normalizer hK₀D).2 (hDE.trans (layer_le_normalizer hK₀))
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K₀.subgroupOf D) with h | h
      · apply hcomp_ne K₀ hK₀
        refine eq_bot_iff.2 fun x hx => ?_
        have : (⟨x, hK₀D hx⟩ : D) ∈ K₀.subgroupOf D := hx
        rw [h, mem_bot] at this
        exact mem_bot.2 (congrArg Subtype.val this)
      · apply hcomp_ne K₁ hK₁
        refine eq_bot_iff.2 fun x hx => ?_
        have hxK₀ : x ∈ K₀ := by
          have : (⟨x, hK₁D hx⟩ : D) ∈ K₀.subgroupOf D := h ▸ mem_top _
          exact this
        have : x ∈ K₀ ⊓ K₁ := ⟨hxK₀, hx⟩
        rwa [hinf] at this
  obtain ⟨halt, hnt⟩ := halt
  have hCD : centralizer (D : Set H) = ⊥ := by
    set CD := centralizer (D : Set H) with hCDdef
    have hCDB : CD ≤ B := centralizer_le hJD
    have haCD : a ∉ CD := fun h => by
      obtain ⟨d, hd, hda⟩ := hnt
      apply hda
      have := mem_centralizer_iff.1 h d hd
      calc a⁻¹ * d * a = a⁻¹ * (d * a) := by group
        _ = a⁻¹ * (a * d) := by rw [this]
        _ = d := by group
    have hodd : ¬ 2 ∣ Nat.card CD := by
      intro h2
      obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := CD) 2 h2
      have hbB : (b : H) ∈ B := hCDB b.2
      have hbo : orderOf (⟨(b : H), hbB⟩ : B) = 2 := by
        rw [← Subgroup.orderOf_coe, show ((⟨(b : H), hbB⟩ : B) : H) = b from rfl,
          Subgroup.orderOf_coe, hb]
      have hb2 : IsPGroup 2 (zpowers (⟨b, hbB⟩ : B)) := IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, hbo, pow_one])
      obtain ⟨S, hS⟩ := hb2.exists_le_sylow
      obtain ⟨g, hg⟩ := MulAction.exists_smul_eq B S₀ S
      have hbS : (⟨b, hbB⟩ : B) ∈ (S : Subgroup B) := hS (mem_zpowers _)
      rw [← hg, Sylow.coe_subgroup_smul, mem_smul_pointwise_iff_exists] at hbS
      obtain ⟨s, hs, hsb⟩ := hbS
      rw [MulAut.smul_def, MulAut.conj_apply] at hsb
      have hsb' : (g : H) * s * (g : H)⁻¹ = b := congrArg Subtype.val hsb
      rcases hmemS₀ s hs with h | h
      · rw [h, mul_one, mul_inv_cancel] at hsb'
        have hb1 : b = 1 := Subtype.ext hsb'.symm
        rw [hb1, orderOf_one] at hb
        exact absurd hb (by norm_num)
      · apply haCD
        have hmem : (g : H)⁻¹ * b * (g : H)⁻¹⁻¹ ∈ CD :=
          (inferInstance : CD.Normal).conj_mem _ b.2 _
        rw [← hsb', h, inv_inv] at hmem
        have e : (g : H)⁻¹ * ((g : H) * a * (g : H)⁻¹) * (g : H) = a := by group
        rwa [e] at hmem
    rw [eq_bot_iff, ← hcore]
    refine le_sSup ⟨inferInstance, ?_⟩
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd
  have hDE' : D = CFSG.layer H := by
    refine le_antisymm hDE (sSup_le fun K hK => ?_)
    rcases component_normal_subgroup hK (normalClosure_normal (s := (J : Set H))) with h | h
    · exact h
    · exfalso
      apply hcomp_ne K hK
      have hKC : K ≤ centralizer (D : Set H) := commutator_eq_bot_iff_le_centralizer.1 h
      rwa [hCD, le_bot_iff] at hKC
  refine ⟨hO2, hF, hJE, hDE', hCD, halt, fun h hh => ?_⟩
  have hhC : h ∈ centralizer (D : Set H) := mem_centralizer_iff.2 fun d hd => by
    calc d * h = h * (h⁻¹ * d * h) := by group
      _ = h * d := by rw [hh d hd]
  rw [hCD] at hhC
  exact mem_bot.1 hhC

end CFSG.LocalAnalysis.SteinbergBV
