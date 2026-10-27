module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1Star
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private noncomputable def s168e3_starNatMap (D : Data G) (V₀ V L : Subgroup G)
    (hV : IsElemAbelian 2 V) : Vtil V₀ V hV →* vStar D.M V₀ V hV L :=
  QuotientGroup.map (modNull V₀ V hV) (modNull (v1Sub D.M V₀ V hV L) V hV) (MonoidHom.id _)
    fun _ hx => (mem_modNull _ _ _ _).2
      (s15_Infra_le_v1Sub D.M V₀ V hV L ((mem_modNull _ _ _ _).1 hx))

private theorem s168e3_starNatMap_mk (D : Data G) (V₀ V L : Subgroup G)
    (hV : IsElemAbelian 2 V) (x : IntMod V hV) :
    s168e3_starNatMap D V₀ V L hV (mkTil V₀ V hV x) =
      mkTil (v1Sub D.M V₀ V hV L) V hV x :=
  rfl

private theorem s168e3_star_imgTil_preTil_map (D : Data G) (V₀ V L : Subgroup G)
    (hV : IsElemAbelian 2 V) (S : Subgroup (Vtil V₀ V hV)) :
    imgTil (v1Sub D.M V₀ V hV L) V hV (preTil V₀ V hV S) =
      S.map (s168e3_starNatMap D V₀ V L hV) := by
  ext q
  rw [Subgroup.mem_map]
  constructor
  · intro hq
    obtain ⟨x, hx, hxq⟩ :=
      (mem_imgTil (v1Sub D.M V₀ V hV L) V hV (preTil V₀ V hV S) q).1 hq
    refine ⟨mkTil V₀ V hV x, (mem_preTil_iff_of_mem V₀ V hV S x.val_mem).1 hx, ?_⟩
    rw [← hxq, s168e3_starNatMap_mk]
  · rintro ⟨p, hp, hp'⟩
    obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV p
    rw [s168e3_starNatMap_mk] at hp'
    rw [← hp']
    exact (mem_imgTil (v1Sub D.M V₀ V hV L) V hV (preTil V₀ V hV S)
      (mkTil (v1Sub D.M V₀ V hV L) V hV x)).2
      ⟨x, (mem_preTil_iff_of_mem V₀ V hV S x.val_mem).2 hp, rfl⟩

private theorem s168e3_star_le_stabTil {D : Data G} {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D ⊥ V L hV) : D.M ≤ stabTil ⊥ V :=
  le_stabTil c.setting.hyp151.hyp125.pairFacts.le_normalizer
    c.setting.hyp151.hyp125.pairFacts.le_normalizer₀

private theorem s168e3_star_wSub_eq {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D ⊥ V L hV) (hs : s15 D.M ⊥ V hV L = 1) : wSub ⊥ V hV L = V := by
  have hcomm : commSub ⊤ (barSub ⊥ V hV L) = ⊤ := wTil_eq_top_of_case163_2 c.conc hs
  unfold wSub wTil
  rw [hcomm, preTil_top]

private theorem s168e3_star_inf_le_preTil_fixV {D : Data G} {V L : Subgroup G}
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

private theorem s168e3_star_preTil_fixV_le_inf {D : Data G} {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D ⊥ V L hV) (hs : s15 D.M ⊥ V hV L = 1) :
    preTil ⊥ V hV (fixV (lBar ⊥ V hV L)) ≤ V ⊓ centralizer (L : Set G) := by
  refine le_inf (preTil_le ⊥ V hV _) fun g hg => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro l hlL
  have hgV : g ∈ V := preTil_le ⊥ V hV _ hg
  have hq : mkTil ⊥ V hV (IntMod.mk hV ⟨g, hgV⟩) ∈ fixV (lBar ⊥ V hV L) :=
    (mem_preTil_iff_of_mem ⊥ V hV _ hgV).1 hg
  have hlM : l ∈ D.M := c.setting.hyp151.le hlL
  have hls : l ∈ stabTil ⊥ V := s168e3_star_le_stabTil c hlM
  have hfix := (mem_fixV.1 hq) (actTil ⊥ V hV ⟨l, hls⟩)
    (actTil_mem_barSub ⊥ V hV hlL hls)
  rw [actTil_mk, mkTil_eq_iff, actStab_apply_val, Subgroup.mem_bot, mul_inv_eq_one] at hfix
  change l * g * l⁻¹ = g at hfix
  exact (mul_inv_eq_iff_eq_mul).1 hfix

private theorem s168e3_star_stableUnder_fixV {D : Data G} {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D ⊥ V L hV) (hs : s15 D.M ⊥ V hV L = 1) :
    StableUnder (Mbar D.M ⊥ V hV) (fixV (lBar ⊥ V hV L)) := by
  intro φ hφ v hv
  have hmap : (fixV (lBar ⊥ V hV L)).map φ.toMonoidHom = fixV (lBar ⊥ V hV L) := by
    rw [← fixV_map_conj_eq (lBar ⊥ V hV L) φ, lBar_conj_eq_of_s15_eq_one hs hφ]
  rw [← hmap]
  exact Subgroup.mem_map.mpr ⟨v, hv, rfl⟩

private theorem s168e3_star_conjSubgroup_preTil_fixV {D : Data G} {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D ⊥ V L hV) (hs : s15 D.M ⊥ V hV L = 1)
    {m : G} (hm : m ∈ D.M) :
    conjSubgroup (preTil ⊥ V hV (fixV (lBar ⊥ V hV L))) m =
      preTil ⊥ V hV (fixV (lBar ⊥ V hV L)) :=
  conjSubgroup_eq_iff_mem_normalizer.mpr
    (TwelveSeventeen.le_normalizer_preTil hV (s168e3_star_le_stabTil c)
      (s168e3_star_stableUnder_fixV c hs) hm)

private theorem s168e3_star_v1Sub_eq_preTil_fixV {D : Data G} {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D ⊥ V L hV) (hs : s15 D.M ⊥ V hV L = 1) :
    v1Sub D.M ⊥ V hV L = preTil ⊥ V hV (fixV (lBar ⊥ V hV L)) := by
  have hw := s168e3_star_wSub_eq c hs
  have hV₁ := v1Sub_of_eq_bot D.M ⊥ V hV L rfl
  rw [hw] at hV₁
  rw [hV₁]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun m => ?_
    calc conjSubgroup (V ⊓ centralizer (L : Set G)) (m : G)
        ≤ conjSubgroup (preTil ⊥ V hV (fixV (lBar ⊥ V hV L))) (m : G) :=
          Subgroup.map_mono (s168e3_star_inf_le_preTil_fixV c hs)
      _ = preTil ⊥ V hV (fixV (lBar ⊥ V hV L)) :=
          s168e3_star_conjSubgroup_preTil_fixV c hs m.2
  · calc preTil ⊥ V hV (fixV (lBar ⊥ V hV L))
        ≤ V ⊓ centralizer (L : Set G) := s168e3_star_preTil_fixV_le_inf c hs
      _ = conjSubgroup (V ⊓ centralizer (L : Set G)) 1 := (conjSubgroup_one _).symm
      _ ≤ ⨆ m : D.M, conjSubgroup (V ⊓ centralizer (L : Set G)) (m : G) := by
          simpa [conjSubgroup_one] using
            (le_iSup (fun m : D.M =>
              conjSubgroup (V ⊓ centralizer (L : Set G)) (m : G)) (1 : D.M))

private theorem s168e3_star_natMap_ker_of_eq_bot {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    (hV₀ : V₀ = ⊥) :
    (s168e3_starNatMap D V₀ V L hV).ker =
      commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L) := by
  subst hV₀
  have hV₁ := s168e3_star_v1Sub_eq_preTil_fixV c hs
  have hcomm : commSub ⊤ (lBar ⊥ V hV L) = ⊤ := wTil_eq_top_of_case163_2 c.conc hs
  rw [hcomm, top_inf_eq]
  ext q
  rw [MonoidHom.mem_ker]
  obtain ⟨x, rfl⟩ := mkTil_surjective ⊥ V hV q
  rw [s168e3_starNatMap_mk]
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

private theorem s168e3_star_mBar_le_normalizer {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1) :
    Mbar D.M V₀ V hV ≤ Subgroup.normalizer
      (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
  fun _ hg => Subgroup.mem_normalizer_iff_map_conj_eq.2 (lBar_conj_eq_of_s15_eq_one hs hg)

private theorem s168e3_star_natMap_ker_of_ne_bot {D : Data G} {V₀ V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1)
    (hV₀ : V₀ ≠ ⊥) :
    (s168e3_starNatMap D V₀ V L hV).ker =
      commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L) := by
  have hV₁ : v1Sub D.M V₀ V hV L = V₀ := v1Sub_of_ne_bot D.M V₀ V hV L hV₀
  have hker : (s168e3_starNatMap D V₀ V L hV).ker = ⊥ := by
    rw [eq_bot_iff]
    rintro q hq
    obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV q
    rw [MonoidHom.mem_ker, s168e3_starNatMap_mk] at hq
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
      (s168e3_star_mBar_le_normalizer c hs)
  have hfix : fixV (lBar V₀ V hV L) = ⊥ :=
    s15_Kbar_fixV_eq_bot_of_ne_bot c.setting.hyp151.hyp125 hV₀ hYM hYn c.ne
  rw [hker, hfix, inf_bot_eq]

private theorem s168e3_star_exists {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hker : (s168e3_starNatMap D V₀ V L hV).ker =
      commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) :
    ∃ (ρ : Vtil V₀ V hV →* vStar D.M V₀ V hV L)
      (θ : ↥(lBar V₀ V hV L) →* ↥(lStar D.M V₀ V hV L)),
      Function.Surjective θ ∧ Function.Injective θ ∧
      (∀ (h : ↥(lBar V₀ V hV L)) (w : Vtil V₀ V hV),
        ρ ((h : MulAut (Vtil V₀ V hV)) w) =
          ((θ h : ↥(lStar D.M V₀ V hV L)) : MulAut (vStar D.M V₀ V hV L)) (ρ w)) ∧
      ρ.ker = commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L) ∧
      (commSub ⊤ (lBar V₀ V hV L)).map ρ = wStar D.M V₀ V hV L := by
  obtain ⟨ρM, hcompat, hLmap⟩ :=
    s16e_star_equiv D c.std.h1217 c.setting.hyp151 hV
  have h125 : Hyp125 D V₀ V := c.setting.hyp151.hyp125
  have hM : D.M ≤ normalizer (V : Set G) := h125.pairFacts.le_normalizer
  have hM₁ : D.M ≤ normalizer (v1Sub D.M V₀ V hV L : Set G) :=
    s15_Infra_le_normalizer_v1Sub h125 hV
  have hLM : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV c.setting.hyp151.le
  have hmemθ : ∀ l : ↥(lBar V₀ V hV L),
      (ρM (Subgroup.inclusion hLM l) : MulAut (Vtil (v1Sub D.M V₀ V hV L) V hV))
        ∈ lStar D.M V₀ V hV L := by
    intro l
    have hl : Subgroup.inclusion hLM l ∈
        (lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV) :=
      Subgroup.mem_subgroupOf.2 l.2
    have hmem : ρM (Subgroup.inclusion hLM l) ∈
        (lStar D.M V₀ V hV L).subgroupOf
          (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) := by
      rw [← hLmap]
      exact Subgroup.mem_map.2 ⟨Subgroup.inclusion hLM l, hl, rfl⟩
    exact Subgroup.mem_subgroupOf.1 hmem
  let θ : ↥(lBar V₀ V hV L) →* ↥(lStar D.M V₀ V hV L) :=
    (((Mbar D.M (v1Sub D.M V₀ V hV L) V hV).subtype.comp
      (ρM.toMonoidHom.comp (Subgroup.inclusion hLM))).codRestrict
        (lStar D.M V₀ V hV L) hmemθ)
  have hθact : ∀ (l : ↥(lBar V₀ V hV L)) (g : ↥(stabTil V₀ V)) (hgL : (g : G) ∈ L)
      (h₁ : (g : G) ∈ stabTil (v1Sub D.M V₀ V hV L) V),
      actTil V₀ V hV g = (l : MulAut (Vtil V₀ V hV)) →
      (θ l : MulAut (vStar D.M V₀ V hV L)) =
        actTil (v1Sub D.M V₀ V hV L) V hV ⟨(g : G), h₁⟩ := by
    intro l g hgL h₁ hgact
    have hxM : (g : G) ∈ D.M := c.setting.hyp151.le hgL
    have hρ : ρM ⟨(l : MulAut (Vtil V₀ V hV)), hLM l.2⟩ =
        ⟨actTil (v1Sub D.M V₀ V hV L) V hV ⟨(g : G), h₁⟩,
          actTil_mem_barSub (v1Sub D.M V₀ V hV L) V hV hxM h₁⟩ := by
      have h2 := hcompat (g : G) hxM g.2 h₁
      have h3 : (⟨(l : MulAut (Vtil V₀ V hV)), hLM l.2⟩ :
            ↥(Mbar D.M V₀ V hV)) =
          ⟨actTil V₀ V hV ⟨(g : G), g.2⟩,
            actTil_mem_barSub V₀ V hV hxM g.2⟩ := by
        refine Subtype.ext ?_
        exact hgact.symm
      rw [h3]
      exact h2
    change (ρM ⟨(l : MulAut (Vtil V₀ V hV)), hLM l.2⟩ :
        ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV)).1 =
      actTil (v1Sub D.M V₀ V hV L) V hV ⟨(g : G), h₁⟩
    rw [hρ]
  have hequiv : ∀ (l : ↥(lBar V₀ V hV L)) (w : Vtil V₀ V hV),
      s168e3_starNatMap D V₀ V L hV ((l : MulAut (Vtil V₀ V hV)) w) =
        ((θ l : ↥(lStar D.M V₀ V hV L)) : MulAut (vStar D.M V₀ V hV L))
          (s168e3_starNatMap D V₀ V L hV w) := by
    intro l w
    obtain ⟨g, hgL, hgact⟩ :=
      (mem_barSub V₀ V hV L (l : MulAut (Vtil V₀ V hV))).1 l.2
    have hxM : (g : G) ∈ D.M := c.setting.hyp151.le hgL
    have h₁ : (g : G) ∈ stabTil (v1Sub D.M V₀ V hV L) V := le_stabTil hM hM₁ hxM
    obtain ⟨y, rfl⟩ := mkTil_surjective V₀ V hV w
    rw [← hgact, hθact l g hgL h₁ hgact]
    simp only [actTil_mk, s168e3_starNatMap_mk]
    have hstab : actStab V₀ V hV g y =
        actStab (v1Sub D.M V₀ V hV L) V hV ⟨(g : G), h₁⟩ y := by
      refine IntMod.val_injective ?_
      rw [actStab_apply_val, actStab_apply_val]
    rw [hstab]
  have hθsurj : Function.Surjective θ := by
    intro y
    have hyM : (y : MulAut (Vtil (v1Sub D.M V₀ V hV L) V hV)) ∈
        Mbar D.M (v1Sub D.M V₀ V hV L) V hV :=
      barSub_mono (v1Sub D.M V₀ V hV L) V hV c.setting.hyp151.le y.2
    have hyS : (⟨(y : MulAut (Vtil (v1Sub D.M V₀ V hV L) V hV)), hyM⟩ :
        ↥(Mbar D.M (v1Sub D.M V₀ V hV L) V hV)) ∈
        (lStar D.M V₀ V hV L).subgroupOf
          (Mbar D.M (v1Sub D.M V₀ V hV L) V hV) :=
      Subgroup.mem_subgroupOf.2 y.2
    rw [← hLmap] at hyS
    obtain ⟨φ, hφ, hφy⟩ := Subgroup.mem_map.1 hyS
    have hφy' : ρM φ = ⟨(y : MulAut (Vtil (v1Sub D.M V₀ V hV L) V hV)), hyM⟩ := hφy
    refine ⟨⟨(φ : MulAut (Vtil V₀ V hV)), Subgroup.mem_subgroupOf.1 hφ⟩, ?_⟩
    refine Subtype.ext ?_
    change (ρM (Subgroup.inclusion hLM ⟨(φ : MulAut (Vtil V₀ V hV)),
        Subgroup.mem_subgroupOf.1 hφ⟩)).1 =
      (y : MulAut (Vtil (v1Sub D.M V₀ V hV L) V hV))
    rw [show Subgroup.inclusion hLM ⟨(φ : MulAut (Vtil V₀ V hV)),
        Subgroup.mem_subgroupOf.1 hφ⟩ = φ from Subtype.ext rfl]
    exact congrArg Subtype.val hφy'
  have hθinj : Function.Injective θ := by
    intro l l' hll'
    have h1 : (ρM (Subgroup.inclusion hLM l) :
        MulAut (Vtil (v1Sub D.M V₀ V hV L) V hV)) =
        (ρM (Subgroup.inclusion hLM l') :
        MulAut (Vtil (v1Sub D.M V₀ V hV L) V hV)) := by
      simpa [θ] using congrArg Subtype.val hll'
    exact Subgroup.inclusion_injective hLM (ρM.injective (Subtype.ext h1))
  have himg : (commSub ⊤ (lBar V₀ V hV L)).map (s168e3_starNatMap D V₀ V L hV) =
      wStar D.M V₀ V hV L :=
    (s168e3_star_imgTil_preTil_map D V₀ V L hV (commSub ⊤ (lBar V₀ V hV L))).symm
  exact ⟨s168e3_starNatMap D V₀ V L hV, θ, hθsurj, hθinj, hequiv, hker, himg⟩

private theorem s168e3_realizesVia_pullback {W W' : Type} [CommGroup W] [CommGroup W']
    {D : FFModel} {A : Subgroup (MulAut W)} {A' : Subgroup (MulAut W')}
    {π : D.Gam →* ↥A'} (hR : D.RealizesVia A' ⊤ ⊥ π)
    (ρ : W →* W') (hρ : Function.Surjective ρ) (θ : ↥A ≃* ↥A')
    (hequiv : ∀ (x : ↥A) (w : W),
      ρ ((x : MulAut W) w) = ((θ x : ↥A') : MulAut W') (ρ w)) :
    D.RealizesVia A ⊤ ρ.ker (θ.symm.toMonoidHom.comp π) := by
  obtain ⟨hsurj, -, hkersec, -, -, hsec, hkerinv, β, hβs, hβk, hβe⟩ := hR
  let ρ₀ : ↥(⊤ : Subgroup W) →* ↥(⊤ : Subgroup W') :=
    (ρ.comp (⊤ : Subgroup W).subtype).codRestrict (⊤ : Subgroup W') (fun _ => trivial)
  have hρ₀ : ∀ u : ↥(⊤ : Subgroup W), ((ρ₀ u : ↥(⊤ : Subgroup W')) : W') = ρ (u : W) :=
    fun _ => rfl
  have hρs : Function.Surjective ρ₀ := by
    intro v
    obtain ⟨w, hw⟩ := hρ (v : W')
    exact ⟨⟨w, trivial⟩, Subtype.ext hw⟩
  let β' : ↥(⊤ : Subgroup W) →* ↥D.sec ⧸ D.ker.subgroupOf D.sec := β.comp ρ₀
  have hβ' : ∀ u : ↥(⊤ : Subgroup W), β' u = β (ρ₀ u) := fun _ => rfl
  refine ⟨θ.symm.surjective.comp hsurj, le_top, hkersec, ?_, ?_, hsec, hkerinv, β',
    hβs.comp hρs, ?_, ?_⟩
  · intro _ _ _
    exact Subgroup.mem_top _
  · intro h z hz
    rw [MonoidHom.mem_ker]
    rw [hequiv h z, MonoidHom.mem_ker.1 hz, map_one]
  · intro u
    simp only [hβ' u, hβk (ρ₀ u), hρ₀ u, Subgroup.mem_bot, MonoidHom.mem_ker]
  · intro γ u m hu hm hbu
    change β' ⟨((θ.symm (π γ) : ↥A) : MulAut W) (u : W), hu⟩ =
      QuotientGroup.mk ⟨D.act γ (m : D.Amb), hm⟩
    set v : ↥(⊤ : Subgroup W') := ρ₀ u with hvdef
    have hβv : β v = QuotientGroup.mk m := by
      rw [hvdef]
      have h := hbu
      rwa [hβ'] at h
    have h := hβe γ v m trivial hm hβv
    have hsub : ρ₀ ⟨((θ.symm (π γ) : ↥A) : MulAut W) (u : W), hu⟩ =
        ⟨((π γ : ↥A') : MulAut W') (v : W'), trivial⟩ := by
      refine Subtype.ext ?_
      show ρ (((θ.symm (π γ) : ↥A) : MulAut W) (u : W)) =
        ((π γ : ↥A') : MulAut W') (v : W')
      rw [hvdef]
      show ρ (((θ.symm (π γ) : ↥A) : MulAut W) (u : W)) =
        ((π γ : ↥A') : MulAut W') (((ρ₀ u : ↥(⊤ : Subgroup W')) : W'))
      rw [hρ₀ u, hequiv (θ.symm (π γ)) (u : W)]
      simp
    rw [hβ', hsub]
    exact h

theorem s168e3_star {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV) (hs : s15 D.M V₀ V hV L = 1) :
    ∃ (ρ : Vtil V₀ V hV →* vStar D.M V₀ V hV L)
      (θ : ↥(lBar V₀ V hV L) ≃* ↥(lStar D.M V₀ V hV L)),
      Function.Surjective ρ ∧
      (∀ (h : ↥(lBar V₀ V hV L)) (w : Vtil V₀ V hV),
        ρ ((h : MulAut (Vtil V₀ V hV)) w) =
          ((θ h : ↥(lStar D.M V₀ V hV L)) : MulAut (vStar D.M V₀ V hV L)) (ρ w)) ∧
      ρ.ker = fixV (lBar V₀ V hV L) := by
  have hcomm : commSub ⊤ (lBar V₀ V hV L) = ⊤ := wTil_eq_top_of_case163_2 c.conc hs
  have hstar : wStar D.M V₀ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D c.std.h1217 c.setting.hyp151 hV c.ne hs
  have hker : (s168e3_starNatMap D V₀ V L hV).ker =
      commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L) := by
    by_cases h0 : V₀ = ⊥
    · exact s168e3_star_natMap_ker_of_eq_bot c hs h0
    · exact s168e3_star_natMap_ker_of_ne_bot c hs h0
  obtain ⟨ρ, θ₀, hθsurj, hθinj, hequiv, hker₀, himg₀⟩ := s168e3_star_exists c hker
  have hρtop : (⊤ : Subgroup (Vtil V₀ V hV)).map ρ = ⊤ := by
    rw [← hcomm, himg₀, hstar]
  refine ⟨ρ, MulEquiv.ofBijective θ₀ ⟨hθinj, hθsurj⟩, ?_, ?_, ?_⟩
  · have hρrange : ρ.range = ⊤ := by rw [MonoidHom.range_eq_map, hρtop]
    exact MonoidHom.range_eq_top.1 hρrange
  · intro h w
    exact hequiv h w
  · rw [hker₀, hcomm, top_inf_eq]

theorem s168e3_natOmegaMinus_pullback {W W' : Type} [CommGroup W] [CommGroup W']
    {A : Subgroup (MulAut W)} {A' : Subgroup (MulAut W')} {n a : ℕ}
    (h : NatOmegaMinus A' ⊤ ⊥ n a) (ρ : W →* W') (hρ : Function.Surjective ρ)
    (θ : ↥A ≃* ↥A')
    (hequiv : ∀ (x : ↥A) (w : W), ρ ((x : MulAut W) w) = ((θ x : ↥A') : MulAut W') (ρ w)) :
    NatOmegaMinus A ⊤ ρ.ker n a := by
  obtain ⟨he, K, hK, hFin, b, c, hcard, hirr, hR⟩ := h
  obtain ⟨π, hπ⟩ := hR
  exact ⟨he, K, hK, hFin, b, c, hcard, hirr,
    ⟨θ.symm.toMonoidHom.comp π, s168e3_realizesVia_pullback hπ ρ hρ θ hequiv⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
