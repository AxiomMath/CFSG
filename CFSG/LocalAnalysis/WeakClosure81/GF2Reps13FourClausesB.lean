module

import CFSG.LocalAnalysis.WeakClosure81.GF2RepsIrr
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13FoundA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13FoundB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

private theorem w16g_commSub_map_conj (g : MulAut W) (J : Subgroup W)
    (A : Subgroup (MulAut W)) :
    commSub (J.map g.toMonoidHom) (A.map (MulAut.conj g).toMonoidHom) =
      (commSub J A).map g.toMonoidHom := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨x', ⟨x, hx, rfl⟩, w', ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨x w * w⁻¹, ⟨x, hx, w, hw, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, MulAut.mul_apply]
  · rintro ⟨c₀, ⟨x, hx, w, hw, rfl⟩, rfl⟩
    refine ⟨(MulAut.conj g).toMonoidHom x, ⟨x, hx, rfl⟩, g w, ⟨w, hw, rfl⟩, ?_⟩
    simp [MulAut.conj_apply, MulAut.mul_apply]

private theorem w16g_map_conj_inv (U : Subgroup W) (g : MulAut W) :
    (U.map g.toMonoidHom).map (g⁻¹).toMonoidHom = U := by
  rw [Subgroup.map_map]
  have h : (g⁻¹).toMonoidHom.comp g.toMonoidHom = MonoidHom.id W := by
    ext w
    exact MulEquiv.symm_apply_apply g w
  rw [h, Subgroup.map_id]

private theorem w16g_map_conj_inv' (U : Subgroup W) (g : MulAut W) :
    (U.map (g⁻¹).toMonoidHom).map g.toMonoidHom = U := by
  rw [Subgroup.map_map]
  have h : g.toMonoidHom.comp (g⁻¹).toMonoidHom = MonoidHom.id W := by
    ext w
    exact MulEquiv.apply_symm_apply g w
  rw [h, Subgroup.map_id]

private theorem w16g_commute_of_commutator_eq_bot {A C : Subgroup (MulAut W)}
    (h : ⁅A, C⁆ = ⊥) {a c : MulAut W} (ha : a ∈ A) (hc : c ∈ C) : Commute a c := by
  rw [commute_iff_eq]
  exact (Subgroup.mem_centralizer_iff.mp
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h ha) c hc).symm

private theorem w16g_conj_mem_of_commutator_eq_bot {A C : Subgroup (MulAut W)}
    (h : ⁅A, C⁆ = ⊥) {a c : MulAut W} (ha : a ∈ A) (hc : c ∈ C) :
    a * c * a⁻¹ ∈ C := by
  have hcomm : Commute a c := w16g_commute_of_commutator_eq_bot h ha hc
  rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
  exact hc

private theorem w16g_centralizer_sup (A B : Subgroup (MulAut W)) :
    Subgroup.centralizer ((A ⊔ B : Subgroup (MulAut W)) : Set (MulAut W)) =
      Subgroup.centralizer (A : Set (MulAut W)) ⊓
        Subgroup.centralizer (B : Set (MulAut W)) := by
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
  ext x
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨fun y hy => h y (Or.inl hy), fun y hy => h y (Or.inr hy)⟩
  · rintro ⟨h1, h2⟩ y (hy | hy)
    · exact h1 y hy
    · exact h2 y hy

private theorem w16g_commutator_sup_eq_bot {A B C : Subgroup (MulAut W)}
    (hAC : ⁅A, C⁆ = ⊥) (hBC : ⁅B, C⁆ = ⊥) : ⁅A ⊔ B, C⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAC)
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hBC)

private theorem w16g_commutator_sup_sup_eq_bot {A B C D : Subgroup (MulAut W)}
    (hAC : ⁅A, C⁆ = ⊥) (hAD : ⁅A, D⁆ = ⊥) (hBC : ⁅B, C⁆ = ⊥) (hBD : ⁅B, D⁆ = ⊥) :
    ⁅A ⊔ B, C ⊔ D⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, w16g_centralizer_sup]
  exact le_inf (sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAC)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hBC))
    (sup_le (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAD)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hBD))

private theorem w16g_commutator_sup_sup_self {A B : Subgroup (MulAut W)}
    (hA : ⁅A, A⁆ = A) (hB : ⁅B, B⁆ = B) : ⁅A ⊔ B, A ⊔ B⁆ = A ⊔ B := by
  refine le_antisymm (Subgroup.commutator_le_of_le le_rfl le_rfl) (sup_le ?_ ?_)
  · calc A = ⁅A, A⁆ := hA.symm
      _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
  · calc B = ⁅B, B⁆ := hB.symm
      _ ≤ ⁅A ⊔ B, A ⊔ B⁆ := Subgroup.commutator_mono le_sup_right le_sup_right

private theorem w16g_commSub_top_ne_bot {H : Subgroup (MulAut W)} (hH : H ≠ ⊥) :
    commSub ⊤ H ≠ ⊥ := by
  intro hbot
  apply hH
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  ext w
  have hw : w ∈ fixV H := by
    rw [mem_fixV]
    intro y hy
    have hmem : y w * w⁻¹ ∈ commSub ⊤ H :=
      Subgroup.subset_closure ⟨y, hy, w, by simp, rfl⟩
    rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hmem
  exact (mem_fixV.mp hw) x hx

private theorem w16g_inf_fixV_commSub_eq_bot {H : Subgroup (MulAut W)}
    (hperf : ⁅H, H⁆ = H) (hirr : IsIrrOn H (commSub ⊤ H) ⊥) :
    commSub ⊤ H ⊓ fixV H = ⊥ := by
  have hstabFix : StableUnder H (fixV H) :=
    stableUnder_fixV (fun y hy h hh => H.mul_mem (H.mul_mem hy hh) (H.inv_mem hy))
  have hJstab : StableUnder H (commSub ⊤ H ⊓ fixV H) :=
    stableUnder_inf hirr.2.1 hstabFix
  rcases hirr.2.2.2 (commSub ⊤ H ⊓ fixV H) hJstab bot_le inf_le_left with h | h
  · exact h
  · exfalso
    have hle : commSub ⊤ H ≤ fixV H := by rw [← h]; exact inf_le_right
    have hbot : commSub (commSub ⊤ H) H = ⊥ := commSub_eq_bot_iff.mpr hle
    have hchain := s13_perfect_chain H hperf ⊥ (commSub ⊤ H) ⊤ (le_of_eq hbot) le_rfl
    exact (not_lt_of_ge hchain) hirr.1

private theorem w16g_isComponentOf_map_conj {A B : Subgroup (MulAut W)} (e : MulAut W)
    (h : IsComponentOf A B) :
    IsComponentOf (A.map (MulAut.conj e).toMonoidHom) (B.map (MulAut.conj e).toMonoidHom) :=
  ⟨Subgroup.map_mono h.1,
    CFSG.ComponentClassification.Components.chain_map (MulAut.conj e).toMonoidHom h.2.1,
    CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (A.equivMapOfInjective (MulAut.conj e).toMonoidHom (MulAut.conj e).injective).symm h.2.2⟩

private theorem w16g_isComponentOf_subgroupOf_top {A Y : Subgroup (MulAut W)}
    (hA : IsComponentOf A Y) : IsComponentOf (A.subgroupOf Y) ⊤ := by
  refine ⟨le_top, ?_, CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (Subgroup.subgroupOfEquivOfLe hA.1) hA.2.2⟩
  exact CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hA.2.1.subgroupOf

private theorem w16g_commutator_eq_bot_of_components {Y A B : Subgroup (MulAut W)}
    (hA : IsComponentOf A Y) (hB : IsComponentOf B Y) (hne : A ≠ B) : ⁅A, B⁆ = ⊥ := by
  haveI : Finite ↥Y := Subtype.finite
  have hA' := w16g_isComponentOf_subgroupOf_top hA
  have hB' := w16g_isComponentOf_subgroupOf_top hB
  have hne' : A.subgroupOf Y ≠ B.subgroupOf Y := by
    intro h
    apply hne
    have h' := congrArg (Subgroup.map Y.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hA.1, Subgroup.map_subgroupOf_eq_of_le hB.1] at h'
  have h := CFSG.ComponentClassification.LocalComponents.commute_of_ne
    (A.subgroupOf Y) (B.subgroupOf Y) hA' hB' hne'
  have hmap := congrArg (Subgroup.map Y.subtype) h
  rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA.1,
    Subgroup.map_subgroupOf_eq_of_le hB.1, Subgroup.map_bot] at hmap

private theorem w16g_isIrrOn_map_conj {X : Subgroup (MulAut W)} {U : Subgroup W}
    (h : IsIrrOn X U ⊥) (g : MulAut W) :
    IsIrrOn (X.map (MulAut.conj g).toMonoidHom) (U.map g.toMonoidHom) ⊥ := by
  obtain ⟨hlt, hUstab, -, hirr⟩ := h
  have hlt' : ⊥ < U.map g.toMonoidHom := by
    have h' := (Subgroup.map_lt_map_iff_of_injective (f := g.toMonoidHom) g.injective
      (H := (⊥ : Subgroup W)) (K := U)).mpr hlt
    rwa [Subgroup.map_bot] at h'
  have hstab' : StableUnder (X.map (MulAut.conj g).toMonoidHom) (U.map g.toMonoidHom) := by
    intro x' hx' u' hu'
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hx'
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hu'
    refine Subgroup.mem_map.mpr ⟨x u, hUstab x hx u hu, ?_⟩
    simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  refine ⟨hlt', hstab', ?_, ?_⟩
  · intro x hx u hu
    rw [Subgroup.mem_bot] at hu ⊢
    rw [hu, map_one]
  · intro J hJstab hbotJ hJle
    have hJ'stab : StableUnder X (J.map (g⁻¹).toMonoidHom) := by
      intro x hx v hv
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hv
      have hx' : g * x * g⁻¹ ∈ X.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
      have hu' : (g * x * g⁻¹) w ∈ J := hJstab _ hx' w hw
      refine Subgroup.mem_map.mpr ⟨(g * x * g⁻¹) w, hu', ?_⟩
      simp [MulAut.mul_apply, MulAut.inv_apply_self]
    have hJ'le : J.map (g⁻¹).toMonoidHom ≤ U := by
      have hmono := Subgroup.map_mono (f := (g⁻¹).toMonoidHom) hJle
      rwa [w16g_map_conj_inv] at hmono
    rcases hirr (J.map (g⁻¹).toMonoidHom) hJ'stab bot_le hJ'le with h | h
    · left
      have h' : (J.map (g⁻¹).toMonoidHom).map g.toMonoidHom = (⊥ : Subgroup W) := by
        rw [h, Subgroup.map_bot]
      rwa [w16g_map_conj_inv'] at h'
    · right
      have h' : (J.map (g⁻¹).toMonoidHom).map g.toMonoidHom = U.map g.toMonoidHom := by
        rw [h]
      rwa [w16g_map_conj_inv'] at h'

private theorem w16g_factor_commSub_eq {H K₁ K₂ : Subgroup (MulAut W)}
    (hH : H = K₁ ⊔ K₂) (hcomm : ⁅K₁, K₂⁆ = ⊥) (hK₁ne : K₁ ≠ ⊥)
    (hirr : IsIrrOn H (commSub ⊤ H) ⊥) : commSub ⊤ K₁ = commSub ⊤ H := by
  have hK₂c : ⁅K₂, K₁⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hcomm
  have hHle : H ≤ Subgroup.normalizer (K₁ : Set (MulAut W)) := by
    rw [hH]
    refine sup_le ?_ ?_
    · exact (Subgroup.le_normalizer_iff).mpr
        (fun h hh x hx => K₁.mul_mem (K₁.mul_mem hh hx) (K₁.inv_mem hh))
    · exact (Subgroup.le_normalizer_iff).mpr
        (fun h hh x hx => w16g_conj_mem_of_commutator_eq_bot hK₂c hh hx)
  have hn : ∀ h ∈ H, ∀ x ∈ K₁, h * x * h⁻¹ ∈ K₁ :=
    fun h hh x hx => (Subgroup.le_normalizer_iff.mp hHle h hh) x hx
  have hstab : StableUnder H (commSub ⊤ K₁) :=
    stableUnder_commSub hn (fun x _ u _ => trivial)
  have hle : commSub ⊤ K₁ ≤ commSub ⊤ H :=
    commSub_mono le_rfl (by rw [hH]; exact le_sup_left)
  have hne : commSub ⊤ K₁ ≠ ⊥ := w16g_commSub_top_ne_bot hK₁ne
  rcases hirr.2.2.2 (commSub ⊤ K₁) hstab bot_le hle with h | h
  · exact absurd h hne
  · exact h

private theorem w16g_shared_factor_false (hW : ∀ w : W, w * w = 1)
    {A B C : Subgroup (MulAut W)}
    (hAperf : ⁅A, A⁆ = A) (hBperf : ⁅B, B⁆ = B) (hCperf : ⁅C, C⁆ = C)
    (hAB : ⁅A, B⁆ = ⊥) (hCA : ⁅C, A⁆ = ⊥) (hCB : ⁅C, B⁆ = ⊥)
    (hAne : A ≠ ⊥) (hCne : C ≠ ⊥)
    (hirrAB : IsIrrOn (A ⊔ B) (commSub ⊤ (A ⊔ B)) ⊥)
    (hirrAC : IsIrrOn (A ⊔ C) (commSub ⊤ (A ⊔ C)) ⊥) : False := by
  have hLperf : ⁅A ⊔ B, A ⊔ B⁆ = A ⊔ B := w16g_commutator_sup_sup_self hAperf hBperf
  have hWfix : commSub ⊤ (A ⊔ B) ⊓ fixV (A ⊔ B) = ⊥ :=
    w16g_inf_fixV_commSub_eq_bot hLperf hirrAB
  have hWA : commSub ⊤ A = commSub ⊤ (A ⊔ B) :=
    w16g_factor_commSub_eq rfl hAB hAne hirrAB
  have hWgA : commSub ⊤ A = commSub ⊤ (A ⊔ C) :=
    w16g_factor_commSub_eq rfl (by rw [Subgroup.commutator_comm]; exact hCA) hAne hirrAC
  have hWgC : commSub ⊤ C = commSub ⊤ (A ⊔ C) :=
    w16g_factor_commSub_eq (by rw [sup_comm]) hCA hCne hirrAC
  have hLCcomm : ⁅A ⊔ B, C⁆ = ⊥ :=
    w16g_commutator_sup_eq_bot (by rw [Subgroup.commutator_comm]; exact hCA)
      (by rw [Subgroup.commutator_comm]; exact hCB)
  have hCLcomm : ⁅C, A ⊔ B⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hLCcomm
  have hYR : StableUnder C (commSub ⊤ (A ⊔ B)) := by
    refine stableUnder_commSub ?_ (fun x _ u _ => trivial)
    intro h hh x hx
    have hcomm : Commute h x := w16g_commute_of_commutator_eq_bot hCLcomm hh hx
    rw [hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
    exact hx
  have hschur := s13_schur_perfect hW (A ⊔ B) C hLCcomm hCperf (commSub ⊤ (A ⊔ B))
    hirrAB.2.1 hYR (by rw [hWfix]; exact hirrAB)
  rw [hWfix] at hschur
  have hW'Cbot : commSub (commSub ⊤ (A ⊔ B)) C = ⊥ := le_bot_iff.mp hschur
  have hWgCbot : commSub (commSub ⊤ (A ⊔ C)) C = ⊥ := by
    rw [← hWgA, hWA]
    exact hW'Cbot
  have hWCCbot : commSub (commSub ⊤ C) C = ⊥ := by
    rw [hWgC]
    exact hWgCbot
  have hchain := s13_perfect_chain C hCperf ⊥ (commSub ⊤ C) ⊤ (le_of_eq hWCCbot) le_rfl
  have hCbot : C = ⊥ := by
    by_contra hCne'
    exact w16g_commSub_top_ne_bot hCne' (le_bot_iff.mp hchain)
  exact hCne hCbot

private theorem w16g_sup_eq_of_mem {K K' Kg K'g : Subgroup (MulAut W)}
    (hKg_ne_K'g : Kg ≠ K'g) (hKg : Kg = K ∨ Kg = K') (hK'g : K'g = K ∨ K'g = K') :
    Kg ⊔ K'g = K ⊔ K' := by
  rcases hKg with h1 | h1 <;> rcases hK'g with h2 | h2
  · exact absurd (h1.trans h2.symm) hKg_ne_K'g
  · rw [h1, h2]
  · rw [h1, h2, sup_comm]
  · exact absurd (h1.trans h2.symm) hKg_ne_K'g

theorem s134_clause_one (hW : ∀ w : W, w * w = 1) {Y K : Subgroup (MulAut W)}
    (hK : IsComponentOf K Y) {t : MulAut W} (ht : t ∈ Y)
    (hmove : K.map (MulAut.conj t).toMonoidHom ≠ K)
    (hirr : IsIrrOn (K ⊔ K.map (MulAut.conj t).toMonoidHom)
      (commSub ⊤ (K ⊔ K.map (MulAut.conj t).toMonoidHom)) ⊥)
    {g : MulAut W} (hg : g ∈ Y)
    (hgL : g ∉ normalizer ((K ⊔ K.map (MulAut.conj t).toMonoidHom : Subgroup (MulAut W)) :
      Set (MulAut W))) :
    commSub ((commSub ⊤ (K ⊔ K.map (MulAut.conj t).toMonoidHom)).map g.toMonoidHom)
      (K ⊔ K.map (MulAut.conj t).toMonoidHom) = ⊥ := by
  classical
  let K' : Subgroup (MulAut W) := K.map (MulAut.conj t).toMonoidHom
  let L : Subgroup (MulAut W) := K ⊔ K'
  let W' : Subgroup W := commSub ⊤ L
  let Kg : Subgroup (MulAut W) := K.map (MulAut.conj g).toMonoidHom
  let K'g : Subgroup (MulAut W) := K'.map (MulAut.conj g).toMonoidHom
  let Lg : Subgroup (MulAut W) := L.map (MulAut.conj g).toMonoidHom
  let W'g : Subgroup W := W'.map g.toMonoidHom
  have hirrL : IsIrrOn L W' ⊥ := hirr
  have hKK' : K ≠ K' := fun h => hmove h.symm
  have hYmapt : Y.map (MulAut.conj t).toMonoidHom = Y :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (H := Y) ht)
  have hYmapg : Y.map (MulAut.conj g).toMonoidHom = Y :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (H := Y) hg)
  have hK'comp : IsComponentOf K' Y := by
    have hmap := w16g_isComponentOf_map_conj t hK
    rwa [hYmapt] at hmap
  have hKg_comp : IsComponentOf Kg Y := by
    have hmap := w16g_isComponentOf_map_conj g hK
    rwa [hYmapg] at hmap
  have hK'g_comp : IsComponentOf K'g Y := by
    have hmap := w16g_isComponentOf_map_conj g hK'comp
    rwa [hYmapg] at hmap
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hK.2.2.1)
  have hK'perf : ⁅K', K'⁆ = K' :=
    Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hK'comp.2.2.1)
  have hKgperf : ⁅Kg, Kg⁆ = Kg :=
    Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hKg_comp.2.2.1)
  have hK'gperf : ⁅K'g, K'g⁆ = K'g :=
    Subgroup.isPerfect_iff.mp (Group.isPerfect_def.mpr hK'g_comp.2.2.1)
  have hKne : K ≠ ⊥ :=
    K.nontrivial_iff_ne_bot.mp (CFSG.ComponentClassification.Quasisimple.nontrivial hK.2.2)
  have hK'ne : K' ≠ ⊥ :=
    K'.nontrivial_iff_ne_bot.mp (CFSG.ComponentClassification.Quasisimple.nontrivial hK'comp.2.2)
  have hKgne : Kg ≠ ⊥ :=
    Kg.nontrivial_iff_ne_bot.mp
      (CFSG.ComponentClassification.Quasisimple.nontrivial hKg_comp.2.2)
  have hK'gne : K'g ≠ ⊥ :=
    K'g.nontrivial_iff_ne_bot.mp
      (CFSG.ComponentClassification.Quasisimple.nontrivial hK'g_comp.2.2)
  have hLperf : ⁅L, L⁆ = L := w16g_commutator_sup_sup_self hKperf hK'perf
  have hLg_eq : Lg = Kg ⊔ K'g := by
    dsimp only [Lg, Kg, K'g, L, K']
    rw [Subgroup.map_sup]
  have hLgperf : ⁅Lg, Lg⁆ = Lg := by
    rw [hLg_eq]
    exact w16g_commutator_sup_sup_self hKgperf hK'gperf
  have hW'g_eq : W'g = commSub ⊤ Lg := by
    change (commSub ⊤ L).map g.toMonoidHom =
      commSub ⊤ (L.map (MulAut.conj g).toMonoidHom)
    rw [← w16g_commSub_map_conj g ⊤ L, Subgroup.map_top_of_surjective g.toMonoidHom g.surjective]
  have hIrG : IsIrrOn Lg W'g ⊥ := w16g_isIrrOn_map_conj hirrL g
  have hIrG' : IsIrrOn (Kg ⊔ K'g) (commSub ⊤ (Kg ⊔ K'g)) ⊥ := by
    rw [← hLg_eq, ← hW'g_eq]
    exact hIrG
  have hIrGc : IsIrrOn Lg (commSub ⊤ Lg) ⊥ := by
    rw [← hW'g_eq]
    exact hIrG
  have hLg_ne_L : Lg ≠ L := by
    intro h
    exact hgL (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  have hKg_ne_K'g : Kg ≠ K'g := by
    intro h
    exact hKK' (Subgroup.map_injective (MulAut.conj g).injective h)
  have mem_pair : ∀ x : Subgroup (MulAut W),
      x ∈ ({K, K'} : Set (Subgroup (MulAut W))) ↔ x = K ∨ x = K' := by
    intro x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  by_cases hKgm : Kg ∈ ({K, K'} : Set (Subgroup (MulAut W)))
  · have hKgm' : Kg = K ∨ Kg = K' := (mem_pair Kg).mp hKgm
    by_cases hK'gm : K'g ∈ ({K, K'} : Set (Subgroup (MulAut W)))
    · exfalso
      have hK'gm' : K'g = K ∨ K'g = K' := (mem_pair K'g).mp hK'gm
      have hLgL : Lg = L := by
        rw [hLg_eq, w16g_sup_eq_of_mem hKg_ne_K'g hKgm' hK'gm']
      exact hLg_ne_L hLgL
    · have hK'gm_neg : K'g ≠ K ∧ K'g ≠ K' := by
        constructor <;> intro hh
        · exact hK'gm ((mem_pair K'g).mpr (Or.inl hh))
        · exact hK'gm ((mem_pair K'g).mpr (Or.inr hh))
      rcases hKgm' with h1 | h1
      · exfalso
        have hAB : ⁅Kg, K'⁆ = ⊥ :=
          w16g_commutator_eq_bot_of_components hKg_comp hK'comp (by rw [h1]; exact hKK')
        have hCA : ⁅K'g, Kg⁆ = ⊥ :=
          w16g_commutator_eq_bot_of_components hK'g_comp hKg_comp
            (by rw [h1]; exact hK'gm_neg.1)
        have hCB : ⁅K'g, K'⁆ = ⊥ :=
          w16g_commutator_eq_bot_of_components hK'g_comp hK'comp hK'gm_neg.2
        exact w16g_shared_factor_false hW hKgperf hK'perf hK'gperf hAB hCA hCB
          hKgne hK'gne (by rw [h1]; exact hirrL) hIrG'
      · exfalso
        have hAB : ⁅Kg, K⁆ = ⊥ :=
          w16g_commutator_eq_bot_of_components hKg_comp hK
            (by rw [h1]; exact hKK'.symm)
        have hCA : ⁅K'g, Kg⁆ = ⊥ :=
          w16g_commutator_eq_bot_of_components hK'g_comp hKg_comp
            (by rw [h1]; exact hK'gm_neg.2)
        have hCB : ⁅K'g, K⁆ = ⊥ :=
          w16g_commutator_eq_bot_of_components hK'g_comp hK hK'gm_neg.1
        exact w16g_shared_factor_false hW hKgperf hKperf hK'gperf hAB hCA hCB
          hKgne hK'gne (by rw [h1, sup_comm]; exact hirrL) hIrG'
  · have hKgm_neg : Kg ≠ K ∧ Kg ≠ K' := by
      constructor <;> intro hh
      · exact hKgm ((mem_pair Kg).mpr (Or.inl hh))
      · exact hKgm ((mem_pair Kg).mpr (Or.inr hh))
    by_cases hK'gm : K'g ∈ ({K, K'} : Set (Subgroup (MulAut W)))
    · have hK'gm' : K'g = K ∨ K'g = K' := (mem_pair K'g).mp hK'gm
      rcases hK'gm' with h1 | h1
      · exfalso
        have hAB : ⁅K'g, K'⁆ = ⊥ :=
          w16g_commutator_eq_bot_of_components hK'g_comp hK'comp (by rw [h1]; exact hKK')
        have hCA : ⁅Kg, K'g⁆ = ⊥ :=
          w16g_commutator_eq_bot_of_components hKg_comp hK'g_comp
            (by rw [h1]; exact hKgm_neg.1)
        have hCB : ⁅Kg, K'⁆ = ⊥ :=
          w16g_commutator_eq_bot_of_components hKg_comp hK'comp hKgm_neg.2
        exact w16g_shared_factor_false hW hK'gperf hK'perf hKgperf hAB hCA hCB
          hK'gne hKgne (by rw [h1]; exact hirrL) (by rw [sup_comm]; exact hIrG')
      · exfalso
        have hAB : ⁅K'g, K⁆ = ⊥ :=
          w16g_commutator_eq_bot_of_components hK'g_comp hK
            (by rw [h1]; exact hKK'.symm)
        have hCA : ⁅Kg, K'g⁆ = ⊥ :=
          w16g_commutator_eq_bot_of_components hKg_comp hK'g_comp
            (by rw [h1]; exact hKgm_neg.2)
        have hCB : ⁅Kg, K⁆ = ⊥ :=
          w16g_commutator_eq_bot_of_components hKg_comp hK hKgm_neg.1
        exact w16g_shared_factor_false hW hK'gperf hKperf hKgperf hAB hCA hCB
          hK'gne hKgne (by rw [h1, sup_comm]; exact hirrL) (by rw [sup_comm]; exact hIrG')
    · have hK'gm_neg : K'g ≠ K ∧ K'g ≠ K' := by
        constructor <;> intro hh
        · exact hK'gm ((mem_pair K'g).mpr (Or.inl hh))
        · exact hK'gm ((mem_pair K'g).mpr (Or.inr hh))
      have hKKg : ⁅K, Kg⁆ = ⊥ :=
        w16g_commutator_eq_bot_of_components hK hKg_comp hKgm_neg.1.symm
      have hKK'g : ⁅K, K'g⁆ = ⊥ :=
        w16g_commutator_eq_bot_of_components hK hK'g_comp hK'gm_neg.1.symm
      have hK'Kg : ⁅K', Kg⁆ = ⊥ :=
        w16g_commutator_eq_bot_of_components hK'comp hKg_comp hKgm_neg.2.symm
      have hK'K'g : ⁅K', K'g⁆ = ⊥ :=
        w16g_commutator_eq_bot_of_components hK'comp hK'g_comp hK'gm_neg.2.symm
      have hLLg : ⁅L, Lg⁆ = ⊥ := by
        rw [hLg_eq]
        rw [show L = K ⊔ K' from rfl]
        exact w16g_commutator_sup_sup_eq_bot hKKg hKK'g hK'Kg hK'K'g
      have hLgL : ⁅Lg, L⁆ = ⊥ := by
        rwa [Subgroup.commutator_comm] at hLLg
      have hYMg : StableUnder Lg W'g := by
        rw [hW'g_eq]
        refine stableUnder_commSub ?_ (fun x _ u _ => trivial)
        intro h hh x hx
        exact Lg.mul_mem (Lg.mul_mem hh hx) (Lg.inv_mem hh)
      have hYRg : StableUnder L W'g := by
        rw [hW'g_eq]
        refine stableUnder_commSub ?_ (fun x _ u _ => trivial)
        intro h hh x hx
        exact w16g_conj_mem_of_commutator_eq_bot (A := L) (C := Lg) hLLg hh hx
      have hW'g_fix : W'g ⊓ fixV Lg = ⊥ := by
        have := w16g_inf_fixV_commSub_eq_bot hLgperf hIrGc
        rwa [← hW'g_eq] at this
      have hschur := s13_schur_perfect hW Lg L hLgL hLperf W'g hYMg hYRg
        (by rw [hW'g_fix]; exact hIrG)
      rw [hW'g_fix] at hschur
      exact le_bot_iff.mp hschur

end CFSG.LocalAnalysis.WeakClosure81
