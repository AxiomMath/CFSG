module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private noncomputable def s168e3_starnat_natMap (D : Data G) (V₀ V L : Subgroup G)
    (hV : IsElemAbelian 2 V) : Vtil V₀ V hV →* vStar D.M V₀ V hV L :=
  QuotientGroup.map (modNull V₀ V hV) (modNull (v1Sub D.M V₀ V hV L) V hV) (MonoidHom.id _)
    fun _ hx => (mem_modNull _ _ _ _).2
      (s15_Infra_le_v1Sub D.M V₀ V hV L ((mem_modNull _ _ _ _).1 hx))

private theorem s168e3_starnat_natMap_mk (D : Data G) (V₀ V L : Subgroup G)
    (hV : IsElemAbelian 2 V) (x : IntMod V hV) :
    s168e3_starnat_natMap D V₀ V L hV (mkTil V₀ V hV x) =
      mkTil (v1Sub D.M V₀ V hV L) V hV x :=
  rfl

private theorem s168e3_starnat_imgTil_preTil_map (D : Data G) (V₀ V L : Subgroup G)
    (hV : IsElemAbelian 2 V) (S : Subgroup (Vtil V₀ V hV)) :
    imgTil (v1Sub D.M V₀ V hV L) V hV (preTil V₀ V hV S) =
      S.map (s168e3_starnat_natMap D V₀ V L hV) := by
  ext q
  rw [Subgroup.mem_map]
  constructor
  · intro hq
    obtain ⟨x, hx, hxq⟩ :=
      (mem_imgTil (v1Sub D.M V₀ V hV L) V hV (preTil V₀ V hV S) q).1 hq
    refine ⟨mkTil V₀ V hV x, (mem_preTil_iff_of_mem V₀ V hV S x.val_mem).1 hx, ?_⟩
    rw [← hxq, s168e3_starnat_natMap_mk]
  · rintro ⟨p, hp, hp'⟩
    obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV p
    rw [s168e3_starnat_natMap_mk] at hp'
    rw [← hp']
    exact (mem_imgTil (v1Sub D.M V₀ V hV L) V hV (preTil V₀ V hV S)
      (mkTil (v1Sub D.M V₀ V hV L) V hV x)).2
      ⟨x, (mem_preTil_iff_of_mem V₀ V hV S x.val_mem).2 hp, rfl⟩

private theorem s168e3_starnat_le_stabTil {D : Data G} {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D ⊥ V L hV) : D.M ≤ stabTil ⊥ V :=
  le_stabTil c.setting.hyp151.hyp125.pairFacts.le_normalizer
    c.setting.hyp151.hyp125.pairFacts.le_normalizer₀

private theorem s168e3_starnat_wSub_eq {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D ⊥ V L hV) (hs : s15 D.M ⊥ V hV L = 1) : wSub ⊥ V hV L = V := by
  have hcomm : commSub ⊤ (barSub ⊥ V hV L) = ⊤ := wTil_eq_top_of_case163_2 c.conc hs
  unfold wSub wTil
  rw [hcomm, preTil_top]

private theorem s168e3_starnat_inf_le_preTil_fixV {D : Data G} {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D ⊥ V L hV) (hs : s15 D.M ⊥ V hV L = 1) :
    V ⊓ centralizer (L : Set G) ≤ preTil ⊥ V hV (fixV (lBar ⊥ V hV L)) := by
  rintro g ⟨hgV, hgC⟩
  rw [mem_preTil_iff_of_mem ⊥ V hV _ hgV, mem_fixV]
  intro φ hφ
  obtain ⟨⟨l, hlstab⟩, hlL, hlact⟩ := (mem_barSub ⊥ V hV L φ).1 hφ
  rw [← hlact, actTil_mk, mkTil_eq_iff, actStab_apply_val, Subgroup.mem_bot, mul_inv_eq_one]
  change l * g * l⁻¹ = g
  have hc := Subgroup.mem_centralizer_iff.1 hgC l hlL
  rw [hc, mul_assoc, mul_inv_cancel, mul_one]

private theorem s168e3_starnat_preTil_fixV_le_inf {D : Data G} {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D ⊥ V L hV) (hs : s15 D.M ⊥ V hV L = 1) :
    preTil ⊥ V hV (fixV (lBar ⊥ V hV L)) ≤ V ⊓ centralizer (L : Set G) := by
  refine le_inf (preTil_le ⊥ V hV _) fun g hg => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro l hlL
  have hgV : g ∈ V := preTil_le ⊥ V hV _ hg
  have hq : mkTil ⊥ V hV (IntMod.mk hV ⟨g, hgV⟩) ∈ fixV (lBar ⊥ V hV L) :=
    (mem_preTil_iff_of_mem ⊥ V hV _ hgV).1 hg
  have hlM : l ∈ D.M := c.setting.hyp151.le hlL
  have hls : l ∈ stabTil ⊥ V := s168e3_starnat_le_stabTil c hlM
  have hfix := (mem_fixV.1 hq) (actTil ⊥ V hV ⟨l, hls⟩)
    (actTil_mem_barSub ⊥ V hV hlL hls)
  rw [actTil_mk, mkTil_eq_iff, actStab_apply_val, Subgroup.mem_bot, mul_inv_eq_one] at hfix
  change l * g * l⁻¹ = g at hfix
  exact (mul_inv_eq_iff_eq_mul).1 hfix

private theorem s168e3_starnat_stableUnder_fixV {D : Data G} {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D ⊥ V L hV) (hs : s15 D.M ⊥ V hV L = 1) :
    StableUnder (Mbar D.M ⊥ V hV) (fixV (lBar ⊥ V hV L)) := by
  intro φ hφ v hv
  have hmap : (fixV (lBar ⊥ V hV L)).map φ.toMonoidHom = fixV (lBar ⊥ V hV L) := by
    rw [← fixV_map_conj_eq (lBar ⊥ V hV L) φ, lBar_conj_eq_of_s15_eq_one hs hφ]
  rw [← hmap]
  exact Subgroup.mem_map.mpr ⟨v, hv, rfl⟩

private theorem s168e3_starnat_conjSubgroup_preTil_fixV {D : Data G} {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D ⊥ V L hV) (hs : s15 D.M ⊥ V hV L = 1)
    {m : G} (hm : m ∈ D.M) :
    conjSubgroup (preTil ⊥ V hV (fixV (lBar ⊥ V hV L))) m =
      preTil ⊥ V hV (fixV (lBar ⊥ V hV L)) :=
  conjSubgroup_eq_iff_mem_normalizer.mpr
    (TwelveSeventeen.le_normalizer_preTil hV (s168e3_starnat_le_stabTil c)
      (s168e3_starnat_stableUnder_fixV c hs) hm)

private theorem s168e3_starnat_v1Sub_eq_preTil_fixV {D : Data G} {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D ⊥ V L hV) (hs : s15 D.M ⊥ V hV L = 1) :
    v1Sub D.M ⊥ V hV L = preTil ⊥ V hV (fixV (lBar ⊥ V hV L)) := by
  have hw := s168e3_starnat_wSub_eq c hs
  have hV₁ := v1Sub_of_eq_bot D.M ⊥ V hV L rfl
  rw [hw] at hV₁
  rw [hV₁]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun m => ?_
    calc conjSubgroup (V ⊓ centralizer (L : Set G)) (m : G)
        ≤ conjSubgroup (preTil ⊥ V hV (fixV (lBar ⊥ V hV L))) (m : G) :=
          Subgroup.map_mono (s168e3_starnat_inf_le_preTil_fixV c hs)
      _ = preTil ⊥ V hV (fixV (lBar ⊥ V hV L)) :=
          s168e3_starnat_conjSubgroup_preTil_fixV c hs m.2
  · calc preTil ⊥ V hV (fixV (lBar ⊥ V hV L))
        ≤ V ⊓ centralizer (L : Set G) := s168e3_starnat_preTil_fixV_le_inf c hs
      _ = conjSubgroup (V ⊓ centralizer (L : Set G)) 1 := (conjSubgroup_one _).symm
      _ ≤ ⨆ m : D.M, conjSubgroup (V ⊓ centralizer (L : Set G)) (m : G) := by
          simpa [conjSubgroup_one] using
            (le_iSup (fun m : D.M =>
              conjSubgroup (V ⊓ centralizer (L : Set G)) (m : G)) (1 : D.M))

private theorem s168e3_starnat_natMap_ker_of_eq_bot {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    (hV₀ : V₀ = ⊥) :
    (s168e3_starnat_natMap D V₀ V L hV).ker =
      commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L) := by
  subst hV₀
  have hV₁ := s168e3_starnat_v1Sub_eq_preTil_fixV c hs
  have hcomm : commSub ⊤ (lBar ⊥ V hV L) = ⊤ := wTil_eq_top_of_case163_2 c.conc hs
  rw [hcomm, top_inf_eq]
  ext q
  rw [MonoidHom.mem_ker]
  obtain ⟨x, rfl⟩ := mkTil_surjective ⊥ V hV q
  rw [s168e3_starnat_natMap_mk]
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

private theorem s168e3_starnat_mBar_le_normalizer {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1) :
    Mbar D.M V₀ V hV ≤ Subgroup.normalizer
      (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
  fun _ hg => Subgroup.mem_normalizer_iff_map_conj_eq.2 (lBar_conj_eq_of_s15_eq_one hs hg)

private theorem s168e3_starnat_natMap_ker_of_ne_bot {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    (hV₀ : V₀ ≠ ⊥) :
    (s168e3_starnat_natMap D V₀ V L hV).ker =
      commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L) := by
  have hV₁ : v1Sub D.M V₀ V hV L = V₀ := v1Sub_of_ne_bot D.M V₀ V hV L hV₀
  have hker : (s168e3_starnat_natMap D V₀ V L hV).ker = ⊥ := by
    rw [eq_bot_iff]
    rintro q hq
    obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV q
    rw [MonoidHom.mem_ker, s168e3_starnat_natMap_mk] at hq
    have hx : x.val ∈ v1Sub D.M V₀ V hV L :=
      (mem_modNull (v1Sub D.M V₀ V hV L) V hV x).1
        ((QuotientGroup.eq_one_iff (N := modNull (v1Sub D.M V₀ V hV L) V hV) x).1 hq)
    rw [hV₁] at hx
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff (N := modNull V₀ V hV) x).2
      ((mem_modNull V₀ V hV x).2 hx)
  have hYM : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV c.setting.hyp151.le
  have hYn : ((lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).2
      (s168e3_starnat_mBar_le_normalizer c hs)
  have hfix : fixV (lBar V₀ V hV L) = ⊥ :=
    s15_Kbar_fixV_eq_bot_of_ne_bot c.setting.hyp151.hyp125 hV₀ hYM hYn c.ne
  rw [hker, hfix, inf_bot_eq]

private theorem s168e3_starnat_ker {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1) :
    (s168e3_starnat_natMap D V₀ V L hV).ker = fixV (lBar V₀ V hV L) := by
  have hcomm : commSub ⊤ (lBar V₀ V hV L) = ⊤ := wTil_eq_top_of_case163_2 c.conc hs
  have hker : (s168e3_starnat_natMap D V₀ V L hV).ker =
      commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L) := by
    by_cases h0 : V₀ = ⊥
    · exact s168e3_starnat_natMap_ker_of_eq_bot c hs h0
    · exact s168e3_starnat_natMap_ker_of_ne_bot c hs h0
  rw [hker, hcomm, top_inf_eq]

private theorem s168e3_starnat_surj {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1) :
    Function.Surjective (s168e3_starnat_natMap D V₀ V L hV) := by
  have hcomm : commSub ⊤ (lBar V₀ V hV L) = ⊤ := wTil_eq_top_of_case163_2 c.conc hs
  have hstar : wStar D.M V₀ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D c.std.h1217 c.setting.hyp151 hV c.ne hs
  have himg : (commSub ⊤ (lBar V₀ V hV L)).map (s168e3_starnat_natMap D V₀ V L hV) =
      wStar D.M V₀ V hV L :=
    (s168e3_starnat_imgTil_preTil_map D V₀ V L hV (commSub ⊤ (lBar V₀ V hV L))).symm
  have htop : (⊤ : Subgroup (Vtil V₀ V hV)).map (s168e3_starnat_natMap D V₀ V L hV) = ⊤ := by
    rw [← hcomm, himg, hstar]
  have hrange : (s168e3_starnat_natMap D V₀ V L hV).range = ⊤ := by
    rw [MonoidHom.range_eq_map, htop]
  exact MonoidHom.range_eq_top.1 hrange

theorem s168e3_starnat_exists {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1) :
    ∃ ρ : Vtil V₀ V hV →* vStar D.M V₀ V hV L, Function.Surjective ρ ∧
      ρ.ker = fixV (lBar V₀ V hV L) ∧
      ∀ (x : G) (h₀ : x ∈ stabTil V₀ V) (h₁ : x ∈ stabTil (v1Sub D.M V₀ V hV L) V)
        (w : Vtil V₀ V hV),
        ρ ((actTil V₀ V hV ⟨x, h₀⟩ : MulAut (Vtil V₀ V hV)) w) =
          ((actTil (v1Sub D.M V₀ V hV L) V hV ⟨x, h₁⟩ : MulAut (vStar D.M V₀ V hV L)) (ρ w)) := by
  refine ⟨s168e3_starnat_natMap D V₀ V L hV, s168e3_starnat_surj c hs,
    s168e3_starnat_ker c hs, ?_⟩
  intro x h₀ h₁ w
  obtain ⟨y, rfl⟩ := mkTil_surjective V₀ V hV w
  simp only [actTil_mk, s168e3_starnat_natMap_mk]
  have hstab : actStab V₀ V hV ⟨x, h₀⟩ y =
      actStab (v1Sub D.M V₀ V hV L) V hV ⟨x, h₁⟩ y := by
    refine IntMod.val_injective ?_
    rw [actStab_apply_val, actStab_apply_val]
  rw [hstab]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
