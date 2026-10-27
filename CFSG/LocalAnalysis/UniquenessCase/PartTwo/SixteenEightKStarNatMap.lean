module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKStarDef
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1Star
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKCtx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def s16kNatMap (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V) :
    Vtil V₀ V hV →* vStar D.M V₀ V hV L :=
  QuotientGroup.map (modNull V₀ V hV) (modNull (v1Sub D.M V₀ V hV L) V hV) (MonoidHom.id _)
    fun _ hx => (mem_modNull _ _ _ _).2
      (s15_Infra_le_v1Sub D.M V₀ V hV L ((mem_modNull _ _ _ _).1 hx))

theorem s16kNatMap_mk (D : Data G) (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V)
    (x : IntMod V hV) :
    s16kNatMap D V₀ V L hV (mkTil V₀ V hV x) = mkTil (v1Sub D.M V₀ V hV L) V hV x :=
  rfl

variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

private theorem s16k_imgTil_preTil_map (D : Data G) (V₀ V L : Subgroup G)
    (hV : IsElemAbelian 2 V) (S : Subgroup (Vtil V₀ V hV)) :
    imgTil (v1Sub D.M V₀ V hV L) V hV (preTil V₀ V hV S) =
      S.map (s16kNatMap D V₀ V L hV) := by
  ext q
  rw [Subgroup.mem_map]
  constructor
  · intro hq
    obtain ⟨x, hx, hxq⟩ :=
      (mem_imgTil (v1Sub D.M V₀ V hV L) V hV (preTil V₀ V hV S) q).1 hq
    refine ⟨mkTil V₀ V hV x, (mem_preTil_iff_of_mem V₀ V hV S x.val_mem).1 hx, ?_⟩
    rw [← hxq, s16kNatMap_mk]
  · rintro ⟨p, hp, hp'⟩
    obtain ⟨x, rfl⟩ := mkTil_surjective V₀ V hV p
    rw [s16kNatMap_mk] at hp'
    rw [← hp']
    exact (mem_imgTil (v1Sub D.M V₀ V hV L) V hV (preTil V₀ V hV S)
      (mkTil (v1Sub D.M V₀ V hV L) V hV x)).2
      ⟨x, (mem_preTil_iff_of_mem V₀ V hV S x.val_mem).2 hp, rfl⟩

private theorem s16k_star_exists (h : S16kBase D V₀ V L hV)
    (hker : (s16kNatMap D V₀ V L hV).ker =
      commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) :
    ∃ (ρ : Vtil V₀ V hV →* vStar D.M V₀ V hV L)
      (θ : ↥(lBar V₀ V hV L) →* ↥(lStar D.M V₀ V hV L)),
      Function.Surjective θ ∧
      (∀ (h : ↥(lBar V₀ V hV L)) (w : Vtil V₀ V hV),
        ρ ((h : MulAut (Vtil V₀ V hV)) w) =
          ((θ h : ↥(lStar D.M V₀ V hV L)) : MulAut (vStar D.M V₀ V hV L)) (ρ w)) ∧
      ρ.ker = commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L) ∧
      (commSub ⊤ (lBar V₀ V hV L)).map ρ = wStar D.M V₀ V hV L := by
  obtain ⟨ρM, hcompat, hLmap⟩ :=
    s16e_star_equiv D h.std.h1217 h.setting.hyp151 hV
  have h125 : Hyp125 D V₀ V := h.setting.hyp151.hyp125
  have hM : D.M ≤ normalizer (V : Set G) := h125.pairFacts.le_normalizer
  have hM₁ : D.M ≤ normalizer (v1Sub D.M V₀ V hV L : Set G) :=
    s15_Infra_le_normalizer_v1Sub h125 hV
  have hLM : lBar V₀ V hV L ≤ Mbar D.M V₀ V hV :=
    barSub_mono V₀ V hV h.setting.hyp151.le
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
    have hxM : (g : G) ∈ D.M := h.setting.hyp151.le hgL
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
      s16kNatMap D V₀ V L hV ((l : MulAut (Vtil V₀ V hV)) w) =
        ((θ l : ↥(lStar D.M V₀ V hV L)) : MulAut (vStar D.M V₀ V hV L))
          (s16kNatMap D V₀ V L hV w) := by
    intro l w
    obtain ⟨g, hgL, hgact⟩ :=
      (mem_barSub V₀ V hV L (l : MulAut (Vtil V₀ V hV))).1 l.2
    have hxM : (g : G) ∈ D.M := h.setting.hyp151.le hgL
    have h₁ : (g : G) ∈ stabTil (v1Sub D.M V₀ V hV L) V := le_stabTil hM hM₁ hxM
    obtain ⟨y, rfl⟩ := mkTil_surjective V₀ V hV w
    rw [← hgact, hθact l g hgL h₁ hgact]
    simp only [actTil_mk, s16kNatMap_mk]
    have hstab : actStab V₀ V hV g y =
        actStab (v1Sub D.M V₀ V hV L) V hV ⟨(g : G), h₁⟩ y := by
      refine IntMod.val_injective ?_
      rw [actStab_apply_val, actStab_apply_val]
    rw [hstab]
  have hθsurj : Function.Surjective θ := by
    intro y
    have hyM : (y : MulAut (Vtil (v1Sub D.M V₀ V hV L) V hV)) ∈
        Mbar D.M (v1Sub D.M V₀ V hV L) V hV :=
      barSub_mono (v1Sub D.M V₀ V hV L) V hV h.setting.hyp151.le y.2
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
  have himg : (commSub ⊤ (lBar V₀ V hV L)).map (s16kNatMap D V₀ V L hV) =
      wStar D.M V₀ V hV L :=
    (s16k_imgTil_preTil_map D V₀ V L hV (commSub ⊤ (lBar V₀ V hV L))).symm
  exact ⟨s16kNatMap D V₀ V L hV, θ, hθsurj, hequiv, hker, himg⟩

theorem s16k_star_of_natMap (h : S16kBase D V₀ V L hV)
    (hker : (s16kNatMap D V₀ V L hV).ker =
      commSub ⊤ (lBar V₀ V hV L) ⊓ fixV (lBar V₀ V hV L)) :
    S16kStar D V₀ V L hV :=
  s16k_star_exists h hker

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
