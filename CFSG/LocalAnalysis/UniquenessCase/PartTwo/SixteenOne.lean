module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenMod
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenSmallDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16_One_wStarConj_exists (D : Data G) {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hV : IsElemAbelian 2 V) {X : Subgroup (vStar D.M V₀ V hV L)}
    (hX : X ∈ wStarConj D.M V₀ V hV L) :
    ∃ e ∈ Mbar D.M (v1Sub D.M V₀ V hV L) V hV,
      X = (wStar D.M V₀ V hV L).map e.toMonoidHom := by
  obtain ⟨m, hm, rfl⟩ := hX
  have hM₁ : D.M ≤ normalizer (v1Sub D.M V₀ V hV L : Set G) :=
    s15_Infra_le_normalizer_v1Sub h hV
  have hms : m ∈ stabTil (v1Sub D.M V₀ V hV L) V :=
    le_stabTil h.pairFacts.le_normalizer hM₁ hm
  refine ⟨(actTil (v1Sub D.M V₀ V hV L) V hV ⟨m, hms⟩)⁻¹, ?_, ?_⟩
  · exact Subgroup.inv_mem _ (actTil_mem_barSub (v1Sub D.M V₀ V hV L) V hV hm hms)
  · rw [wStar,
      s15_Infra_imgTil_conjSubgroup (v1Sub D.M V₀ V hV L) V (wSub V₀ V hV L) hV hms]

theorem s16_One_exists_star_transvection (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    (hm : mBar D.M V₀ V hV = 1) :
    ∃ φ ∈ Mbar D.M (v1Sub D.M V₀ V hV L) V hV,
      InducesTransvection φ (⊤ : Subgroup (vStar D.M V₀ V hV L)) := by
  have hM : D.M ≤ normalizer (V : Set G) := h.hyp125.pairFacts.le_normalizer
  have hM₁ : D.M ≤ normalizer (v1Sub D.M V₀ V hV L : Set G) :=
    s15_Infra_le_normalizer_v1Sub h.hyp125 hV
  have hMs₁ : D.M ≤ stabTil (v1Sub D.M V₀ V hV L) V := le_stabTil hM hM₁
  have hA : Mbar D.M V₀ V hV ≠ ⊥ := by
    intro hbot
    apply hL
    exact le_bot_iff.mp ((barSub_mono V₀ V hV h.le).trans (le_of_eq hbot))
  obtain ⟨t, ht, htorder, htcomm⟩ :=
    s16_Mod_exists_involution_transvection (W := Vtil V₀ V hV)
      (s15_Infra_vtil_sq_eq_one V₀ V hV) hA hm
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at htorder
    exact absurd htorder (by norm_num)
  obtain ⟨g, hgM, hgφ⟩ := (mem_barSub V₀ V hV D.M t).1 ht
  let g₁ : ↥(stabTil (v1Sub D.M V₀ V hV L) V) := ⟨(g : G), hMs₁ hgM⟩
  have hφne : actTil (v1Sub D.M V₀ V hV L) V hV g₁ ≠ 1 := by
    intro hφ1
    have hgc : (g : G) ∈ F11.CTilde D.M (v1Sub D.M V₀ V hV L) V :=
      (mem_cTilde_iff (M := D.M) hV hM).2 ⟨hgM, hMs₁ hgM, hφ1⟩
    have hgc' : (g : G) ∈ F11.CTilde D.M V₀ V := by
      rwa [fifteen_two_cent D h1217 h hV] at hgc
    obtain ⟨hgs, hact⟩ := ((mem_cTilde_iff (M := D.M) hV hM).1 hgc').2
    have hsub : (⟨(g : G), hgs⟩ : ↥(stabTil V₀ V)) = g := Subtype.ext rfl
    exact ht1 (by rw [← hgφ, ← hsub, hact])
  have hker : modNull V₀ V hV ≤
      (modNull (v1Sub D.M V₀ V hV L) V hV).comap (MonoidHom.id _) := fun x hx => by
    rw [Subgroup.mem_comap]
    exact (mem_modNull (v1Sub D.M V₀ V hV L) V hV x).2
      (s15_Infra_le_v1Sub D.M V₀ V hV L ((mem_modNull V₀ V hV x).1 hx))
  let π : Vtil V₀ V hV →* Vtil (v1Sub D.M V₀ V hV L) V hV :=
    QuotientGroup.map (N := modNull V₀ V hV) (modNull (v1Sub D.M V₀ V hV L) V hV)
      (MonoidHom.id _) hker
  have hπmk : ∀ x : IntMod V hV,
      π (mkTil V₀ V hV x) = mkTil (v1Sub D.M V₀ V hV L) V hV x := fun x =>
    QuotientGroup.map_mk' (N := modNull V₀ V hV)
      (modNull (v1Sub D.M V₀ V hV L) V hV) (MonoidHom.id _) hker x
  have hπsurj : Function.Surjective π := by
    intro q
    obtain ⟨x, rfl⟩ := mkTil_surjective (v1Sub D.M V₀ V hV L) V hV q
    exact ⟨mkTil V₀ V hV x, hπmk x⟩
  have hπt : ∀ w, π (t w) = actTil (v1Sub D.M V₀ V hV L) V hV g₁ (π w) := by
    intro w
    obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV w
    have hval : actStab V₀ V hV g x = actStab (v1Sub D.M V₀ V hV L) V hV g₁ x := by
      apply IntMod.val_injective
      rw [actStab_apply_val, actStab_apply_val]
    calc π (t (mkTil V₀ V hV x))
        = π (mkTil V₀ V hV (actStab V₀ V hV g x)) := by rw [← hgφ, actTil_mk]
      _ = mkTil (v1Sub D.M V₀ V hV L) V hV (actStab V₀ V hV g x) := hπmk _
      _ = mkTil (v1Sub D.M V₀ V hV L) V hV
            (actStab (v1Sub D.M V₀ V hV L) V hV g₁ x) := by rw [hval]
      _ = actTil (v1Sub D.M V₀ V hV L) V hV g₁
            (mkTil (v1Sub D.M V₀ V hV L) V hV x) := (actTil_mk _ _ _ g₁ x).symm
      _ = actTil (v1Sub D.M V₀ V hV L) V hV g₁ (π (mkTil V₀ V hV x)) := by rw [hπmk x]
  have hcomm := s16_Mod_commSub_zpowers_map π hπsurj hπt
  have hle : rk ↥(commSub ⊤ (Subgroup.zpowers (actTil (v1Sub D.M V₀ V hV L) V hV g₁))) ≤
      rk ↥(commSub ⊤ (Subgroup.zpowers t)) := by
    rw [hcomm]
    have h := CFSG.Quasithin.rk_map_add_rk_inf_ker π (commSub ⊤ (Subgroup.zpowers t))
    omega
  have hne : commSub ⊤ (Subgroup.zpowers (actTil (v1Sub D.M V₀ V hV L) V hV g₁)) ≠ ⊥ := by
    intro hbot
    apply hφne
    refine MulEquiv.ext fun v => ?_
    exact (commSub_eq_bot_iff.1 hbot) (Subgroup.mem_top v)
      (actTil (v1Sub D.M V₀ V hV L) V hV g₁) (Subgroup.mem_zpowers _)
  have hrk : rk ↥(commSub ⊤ (Subgroup.zpowers (actTil (v1Sub D.M V₀ V hV L) V hV g₁))) = 1 := by
    have hpos : rk ↥(commSub ⊤
        (Subgroup.zpowers (actTil (v1Sub D.M V₀ V hV L) V hV g₁))) ≠ 0 := by
      intro h0
      exact hne ((rk_eq_zero_iff
        (s15_Infra_vtil_sq_eq_one (v1Sub D.M V₀ V hV L) V hV)).1 h0)
    have h1 : rk ↥(commSub ⊤
        (Subgroup.zpowers (actTil (v1Sub D.M V₀ V hV L) V hV g₁))) ≤ 1 := by
      rw [htcomm] at hle
      exact hle
    omega
  refine ⟨actTil (v1Sub D.M V₀ V hV L) V hV g₁,
    actTil_mem_barSub (v1Sub D.M V₀ V hV L) V hV hgM (hMs₁ hgM), fun u => Iff.rfl, hrk⟩

theorem sixteen_one (D : Data G) (h1217 : R1217 D) (h153 : R15_3Small D) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hsmall : mSub V₀ ≤ 2) (hV : IsElemAbelian 2 V)
    (hL : barSub V₀ V hV L ≠ ⊥) (hm : mBar D.M V₀ V hV = 1) :
    Desc153 D V₀ V hV L := by
  obtain ⟨φ, hφmem, hφind⟩ := s16_One_exists_star_transvection D h1217 h hV hL hm
  have ht : rk ↥(commSub ⊤ (Subgroup.zpowers φ)) = 1 := hφind.2
  obtain ⟨hind, hspan⟩ := fifteen_two_directSum D h1217 h hV hL
  have hrk : ∀ X ∈ wStarConj D.M V₀ V hV L, 2 ≤ rk ↥X := by
    intro X hX
    obtain ⟨e, -, rfl⟩ := s16_One_wStarConj_exists D h.hyp125 hV hX
    rw [s15_Lin_rk_map]
    exact two_le_gamma15 D h hV hL
  have hperm : ∀ X ∈ wStarConj D.M V₀ V hV L,
      X.map φ.toMonoidHom ∈ wStarConj D.M V₀ V hV L := by
    intro X hX
    obtain ⟨e, he, rfl⟩ := s16_One_wStarConj_exists D h.hyp125 hV hX
    rw [Subgroup.map_map]
    have hmul : φ.toMonoidHom.comp e.toMonoidHom = (φ * e).toMonoidHom := rfl
    rw [hmul]
    exact s15_Infra_map_wStar_mem_wStarConj h.hyp125 hV (Subgroup.mul_mem _ hφmem he)
  obtain ⟨X, hXS, hXind⟩ :=
    s16_Mod_transvection_summand (W := vStar D.M V₀ V hV L)
      (s15_Infra_vtil_sq_eq_one (v1Sub D.M V₀ V hV L) V hV) hind hspan hrk hperm ht
  obtain ⟨e, he, rfl⟩ := s16_One_wStarConj_exists D h.hyp125 hV hXS
  have hconj : InducesTransvection (e⁻¹ * φ * e) (wStar D.M V₀ V hV L) :=
    (s16_Mod_inducesTransvection_conj e φ (wStar D.M V₀ V hV L)).1 hXind
  have hmem : e⁻¹ * φ * e ∈ Mbar D.M (v1Sub D.M V₀ V hV L) V hV :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ he) hφmem) he
  exact h153 V₀ V L h hsmall ⟨e⁻¹ * φ * e, hmem, hconj⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
