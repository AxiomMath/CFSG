module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKStarNatMap

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}
  {hV : IsElemAbelian 2 V}

private theorem s16k_le_stabTil (h : S16kBase D ⊥ V L hV) : D.M ≤ stabTil ⊥ V :=
  le_stabTil h.setting.hyp151.hyp125.pairFacts.le_normalizer
    h.setting.hyp151.hyp125.pairFacts.le_normalizer₀

private theorem s16k_wSub_eq (h : S16kBase D ⊥ V L hV) : wSub ⊥ V hV L = V := by
  have hcomm : commSub ⊤ (barSub ⊥ V hV L) = ⊤ := h.comm_top
  unfold wSub wTil
  rw [hcomm, preTil_top]

private theorem s16k_inf_le_preTil_fixV (h : S16kBase D ⊥ V L hV) :
    V ⊓ centralizer (L : Set G) ≤ preTil ⊥ V hV (fixV (lBar ⊥ V hV L)) := by
  rintro g ⟨hgV, hgC⟩
  rw [mem_preTil_iff_of_mem ⊥ V hV _ hgV, mem_fixV]
  intro φ hφ
  obtain ⟨⟨l, hlstab⟩, hlL, hlact⟩ := (mem_barSub ⊥ V hV L φ).1 hφ
  rw [← hlact, actTil_mk, mkTil_eq_iff, actStab_apply_val, Subgroup.mem_bot, mul_inv_eq_one]
  change l * g * l⁻¹ = g
  have hc := Subgroup.mem_centralizer_iff.1 hgC l hlL
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]

private theorem s16k_preTil_fixV_le_inf (h : S16kBase D ⊥ V L hV) :
    preTil ⊥ V hV (fixV (lBar ⊥ V hV L)) ≤ V ⊓ centralizer (L : Set G) := by
  refine le_inf (preTil_le ⊥ V hV _) fun g hg => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro l hlL
  have hgV : g ∈ V := preTil_le ⊥ V hV _ hg
  have hq : mkTil ⊥ V hV (IntMod.mk hV ⟨g, hgV⟩) ∈ fixV (lBar ⊥ V hV L) :=
    (mem_preTil_iff_of_mem ⊥ V hV _ hgV).1 hg
  have hlM : l ∈ D.M := h.setting.hyp151.le hlL
  have hls : l ∈ stabTil ⊥ V := s16k_le_stabTil h hlM
  have hfix := (mem_fixV.1 hq) (actTil ⊥ V hV ⟨l, hls⟩)
    (actTil_mem_barSub ⊥ V hV hlL hls)
  rw [actTil_mk, mkTil_eq_iff, actStab_apply_val, Subgroup.mem_bot, mul_inv_eq_one] at hfix
  change l * g * l⁻¹ = g at hfix
  exact (mul_inv_eq_iff_eq_mul).1 hfix

private theorem s16k_stableUnder_fixV (h : S16kBase D ⊥ V L hV) :
    StableUnder (Mbar D.M ⊥ V hV) (fixV (lBar ⊥ V hV L)) := by
  intro φ hφ v hv
  have hmap : (fixV (lBar ⊥ V hV L)).map φ.toMonoidHom = fixV (lBar ⊥ V hV L) := by
    rw [← fixV_map_conj_eq (lBar ⊥ V hV L) φ, h.conj_eq hφ]
  rw [← hmap]
  exact Subgroup.mem_map.mpr ⟨v, hv, rfl⟩

private theorem s16k_conjSubgroup_preTil_fixV (h : S16kBase D ⊥ V L hV) {m : G}
    (hm : m ∈ D.M) :
    conjSubgroup (preTil ⊥ V hV (fixV (lBar ⊥ V hV L))) m =
      preTil ⊥ V hV (fixV (lBar ⊥ V hV L)) :=
  conjSubgroup_eq_iff_mem_normalizer.mpr
    (TwelveSeventeen.le_normalizer_preTil hV (s16k_le_stabTil h)
      (s16k_stableUnder_fixV h) hm)

private theorem s16k_v1Sub_eq_preTil_fixV (h : S16kBase D ⊥ V L hV) :
    v1Sub D.M ⊥ V hV L = preTil ⊥ V hV (fixV (lBar ⊥ V hV L)) := by
  have hw := s16k_wSub_eq h
  have hV₁ := v1Sub_of_eq_bot D.M ⊥ V hV L rfl
  rw [hw] at hV₁
  rw [hV₁]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun m => ?_
    calc conjSubgroup (V ⊓ centralizer (L : Set G)) (m : G)
        ≤ conjSubgroup (preTil ⊥ V hV (fixV (lBar ⊥ V hV L))) (m : G) :=
          Subgroup.map_mono (s16k_inf_le_preTil_fixV h)
      _ = preTil ⊥ V hV (fixV (lBar ⊥ V hV L)) :=
          s16k_conjSubgroup_preTil_fixV h m.2
  · calc preTil ⊥ V hV (fixV (lBar ⊥ V hV L))
        ≤ V ⊓ centralizer (L : Set G) := s16k_preTil_fixV_le_inf h
      _ = conjSubgroup (V ⊓ centralizer (L : Set G)) 1 := (conjSubgroup_one _).symm
      _ ≤ ⨆ m : D.M, conjSubgroup (V ⊓ centralizer (L : Set G)) (m : G) := by
          simpa [conjSubgroup_one] using
            (le_iSup (fun m : D.M =>
              conjSubgroup (V ⊓ centralizer (L : Set G)) (m : G)) (1 : D.M))

theorem s16k_natMap_ker_of_eq_bot (h : S16kBase D V₀ V L hV) (hV₀ : V₀ = ⊥) :
    (s16kNatMap D V₀ V L hV).ker =
      commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L) := by
  subst hV₀
  have hV₁ := s16k_v1Sub_eq_preTil_fixV h
  rw [h.comm_top, top_inf_eq]
  ext q
  rw [MonoidHom.mem_ker]
  obtain ⟨x, rfl⟩ := mkTil_surjective ⊥ V hV q
  rw [s16kNatMap_mk]
  have h1 : mkTil (v1Sub D.M ⊥ V hV L) V hV x = 1 ↔ x.val ∈ v1Sub D.M ⊥ V hV L := by
    constructor
    · intro hx
      exact (mem_modNull _ _ _ _).1
        ((QuotientGroup.eq_one_iff (N := modNull (v1Sub D.M ⊥ V hV L) V hV) x).1 hx)
    · intro hx
      exact (QuotientGroup.eq_one_iff (N := modNull (v1Sub D.M ⊥ V hV L) V hV) x).2
        ((mem_modNull _ _ _ _).2 hx)
  rw [h1, hV₁]
  have hiff := mem_preTil_iff_of_mem ⊥ V hV (fixV (lBar ⊥ V hV L)) x.val_mem
  rw [show IntMod.mk hV ⟨x.val, x.val_mem⟩ = x from IntMod.val_injective rfl] at hiff
  exact hiff

theorem s16k_star_of_eq_bot (h : S16kBase D V₀ V L hV) (hV₀ : V₀ = ⊥) :
    S16kStar D V₀ V L hV :=
  s16k_star_of_natMap h (s16k_natMap_ker_of_eq_bot h hV₀)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
