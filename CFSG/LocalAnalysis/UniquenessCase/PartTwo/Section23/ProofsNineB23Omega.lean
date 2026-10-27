module

public import CFSG.GroupTheory.ProdFactors
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineB23Lines
public import CFSG.Quasithin.Background.F420Orders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup CFSG.GroupTheory
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

private theorem b23Shape_of_isComponent (c : Ctx23L D Ch) (h8 : S23_8 D Ch)
    (h1930 : H1930 D) {C : Subgroup (Bar2 D.M)} (hC : CFSG.IsComponent C) : B23Shape C := by
  obtain ⟨X, hX, hXC⟩ := uc22p21c_exists_calC_of_component D.M hC
  rw [← hXC]
  exact shape_barImage_of_mem_calC (c := c) h8 h1930 hX

private theorem center_component_eq_bot (c : Ctx23L D Ch) (h8 : S23_8 D Ch) (h1930 : H1930 D)
    {C : Subgroup (Bar2 D.M)} (hC : CFSG.IsComponent C) : Subgroup.center C = ⊥ := by
  have hshape := b23Shape_of_isComponent c h8 h1930 hC
  exact center_eq_bot_of_b23Shape hshape ⟨Group.isPerfect_def.mp hC.1.1, hC.1.2.1⟩

private theorem center_layer_eq_bot (c : Ctx23L D Ch) (h8 : S23_8 D Ch) (h1930 : H1930 D) :
    Subgroup.center (CFSG.layer (Bar2 D.M)) = ⊥ := by
  have hZ : ∀ C : Subgroup (Bar2 D.M), CFSG.IsComponent C → Subgroup.center C = ⊥ :=
    fun C hC => center_component_eq_bot c h8 h1930 hC
  have hmap : (Subgroup.center (CFSG.layer (Bar2 D.M))).map
      (CFSG.layer (Bar2 D.M)).subtype = ⊥ := by
    rw [(CFSG.LocalCores.layer_center (G := Bar2 D.M)).1]
    rw [iSup_eq_bot]
    intro K
    rw [hZ K.1 K.2, Subgroup.map_bot]
  exact (Subgroup.map_eq_bot_iff_of_injective (H := Subgroup.center (CFSG.layer (Bar2 D.M)))
    (Subgroup.subtype_injective (CFSG.layer (Bar2 D.M)))).mp hmap

theorem RKbar_eq_bot_of_omega (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h8 : S23_8 D Ch) (hB1 : S23_9_B1 D Ch) (hS : KSub23) (hK : KOrdNatural)
    (h1930 : H1930 D) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z)) :
    RKbar c hV = ⊥ := by
  have hY : Kbar c ≤ CFSG.layer (Bar2 D.M) := c.barImage_Hinf_inf_L_le_layer hB1 h1930 h3
  have hcent : ∀ C : Subgroup (Bar2 D.M), CFSG.IsComponent C →
      (RKbar c hV).map (Kbar c).subtype ≤ Subgroup.centralizer (C : Set (Bar2 D.M)) :=
    fun C hC => map_RKbar_le_centralizer c hV h8 hB1 hS hK h1930 h3 hnat hC
  have hcenter := center_layer_eq_bot c h8 h1930
  have hmem : ∀ r : ↥(Kbar c), r ∈ RKbar c hV →
      (r : Bar2 D.M) ∈ (Subgroup.center (CFSG.layer (Bar2 D.M))).map
        (CFSG.layer (Bar2 D.M)).subtype := by
    intro r hr
    rw [CFSG.LocalCores.mem_map_center_iff]
    refine ⟨hY r.2, ?_⟩
    obtain ⟨x, hx⟩ := CFSG.LocalCores.exists_layerMul_eq (hY r.2)
    rw [← hx]
    rw [CFSG.LocalCores.layerMul_mem_centralizer_iff]
    intro K
    have hKcomm : ∀ k : K.1, Commute (k : Bar2 D.M) (r : Bar2 D.M) := fun k =>
      Subgroup.mem_centralizer_iff.mp
        (hcent K.1 K.2 (Subgroup.mem_map_of_mem (Kbar c).subtype hr)) k k.2
    refine Subgroup.mem_center_iff.mpr fun k => ?_
    have hk : Commute (k : Bar2 D.M) (CFSG.LocalCores.layerMul (Bar2 D.M) x) := by
      rw [hx]
      exact hKcomm k
    exact Subtype.ext (((CFSG.LocalCores.commute_layerMul_iff x K k.2).mp hk).eq)
  ext r
  constructor
  · intro hr
    have h1 := hmem r hr
    rw [hcenter, Subgroup.map_bot, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  · intro hr
    rw [Subgroup.mem_bot] at hr
    rw [hr]
    exact Subgroup.one_mem _

theorem toKbar_ker_le_psiK_ker (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    (toKbar c).ker ≤ (psiK c hV).ker := by
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hxbar : toBar2M c x = 1 := by
    have := congrArg Subtype.val hx
    simpa [toKbar] using this
  have hxM : Subgroup.inclusion (K_le_M c) x ∈ CFSG.pCore 2 ↥D.M :=
    (QuotientGroup.eq_one_iff _).mp hxbar
  let Q : Subgroup ↥(K c) := (CFSG.pCore 2 ↥D.M).comap (Subgroup.inclusion (K_le_M c))
  have hxQ : x ∈ Q := Subgroup.mem_comap.mpr hxM
  have hQnormal : Q.Normal :=
    (CFSG.pCore_normal (p := 2) (G := ↥D.M)).comap (Subgroup.inclusion (K_le_M c))
  have hQp : IsPGroup 2 Q :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M)).comap_of_injective
      (Subgroup.inclusion (K_le_M c)) (Subgroup.inclusion_injective (K_le_M c))
  let R : Subgroup ↥(Kstar c hV) := Q.map (phiK c hV)
  have hRnormal : R.Normal :=
    hQnormal.map (phiK c hV) (MonoidHom.rangeRestrict_surjective _)
  have hRp : IsPGroup 2 R := hQp.map (phiK c hV)
  have hRle : R ≤ CFSG.pCore 2 ↥(Kstar c hV) :=
    le_sSup (s := CFSG.normalPSubgroups 2 ↥(Kstar c hV)) ⟨hRnormal, hRp⟩
  rw [psiK_ker c hV]
  exact Subgroup.mem_comap.mpr (hRle (Subgroup.mem_map_of_mem (phiK c hV) hxQ))

@[expose] noncomputable def KbarToKstarBar (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) : ↥(Kbar c) →* KstarBar c hV :=
  let hker := c.toKbar_ker_le_psiK_ker hV
  let g : ↥(K c) ⧸ (toKbar c).ker →* KstarBar c hV :=
    QuotientGroup.lift (toKbar c).ker (psiK c hV) hker
  let e : ↥(K c) ⧸ (toKbar c).ker ≃* ↥(Kbar c) :=
    QuotientGroup.quotientKerEquivOfSurjective (toKbar c) (toKbar_surjective c)
  g.comp e.symm.toMonoidHom

private theorem KbarToKstarBar_apply_toKbar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (x : ↥(K c)) : KbarToKstarBar c hV (toKbar c x) = psiK c hV x := by
  have he : (QuotientGroup.quotientKerEquivOfSurjective (toKbar c) (toKbar_surjective c)).symm
      (toKbar c x) = (QuotientGroup.mk' (toKbar c).ker x : ↥(K c) ⧸ (toKbar c).ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [KbarToKstarBar, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
    Function.comp_apply, he]
  exact QuotientGroup.lift_mk' (toKbar c).ker (c.toKbar_ker_le_psiK_ker hV) x

private theorem KbarToKstarBar_surjective (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    Function.Surjective (KbarToKstarBar c hV) := by
  intro z
  obtain ⟨x, rfl⟩ := psiK_surjective c hV z
  exact ⟨toKbar c x, c.KbarToKstarBar_apply_toKbar hV x⟩

private theorem KbarToKstarBar_ker (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    (KbarToKstarBar c hV).ker = RKbar c hV := by
  ext r
  constructor
  · intro hr
    obtain ⟨x, rfl⟩ := toKbar_surjective c r
    have hpsi : psiK c hV x = 1 := by
      rw [← c.KbarToKstarBar_apply_toKbar hV x]
      exact hr
    refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
    rw [← psiK_ker c hV]
    exact MonoidHom.mem_ker.mpr hpsi
  · rintro ⟨x, hx, rfl⟩
    have hx' : x ∈ (psiK c hV).ker := by
      rw [psiK_ker c hV]
      exact hx
    rw [MonoidHom.mem_ker]
    rw [c.KbarToKstarBar_apply_toKbar hV x]
    exact MonoidHom.mem_ker.mp hx'

private theorem isL2Square_KstarBar_of_Omega (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (ha : KTab23a) (hd : KTab23d) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (hline : IsOmegaPlus ↥(c.H hV) 6 (CFSG.Open.pRank 2 D.Z) ∧
      NatOmegaPlus (c.H hV) ⊤ ⊥ 6 (CFSG.Open.pRank 2 D.Z)) :
    IsL2Square (KstarBar c hV) (CFSG.Open.pRank 2 D.Z) := by
  have hd' := hd (c.W hV) (c.H hV) (CFSG.Open.pRank 2 D.Z) hnat
    (c.commutator_H_eq hV) h3 (c.sylowStar hV)
  have hEq := c.Kstar_eq_Hinf_stabilizer_sylowStar hV ha h4 h1930 hnat
  rcases hd' with ⟨-, -, -, -, -, -, -, -, hOp6, -, -⟩
  exact bar2_congr (P := fun T _ => IsL2Square T (CFSG.Open.pRank 2 D.Z)) hEq (hOp6 hline)

theorem nonempty_mulEquiv_Kbar_KstarBar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h8 : S23_8 D Ch) (hB1 : S23_9_B1 D Ch) (hS : KSub23) (hK : KOrdNatural)
    (h1930 : H1930 D) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z)) :
    Nonempty (↥(Kbar c) ≃* KstarBar c hV) := by
  have hk : (KbarToKstarBar c hV).ker = ⊥ := by
    rw [KbarToKstarBar_ker c hV]
    exact RKbar_eq_bot_of_omega c hV h8 hB1 hS hK h1930 h3 hnat
  exact ⟨MulEquiv.ofBijective _
    ⟨(MonoidHom.ker_eq_bot_iff _).mp hk, KbarToKstarBar_surjective c hV⟩⟩

theorem isL2Square_Kbar_of_Omega (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (ha : KTab23a) (hd : KTab23d) (h4 : S23_4 D Ch) (h8 : S23_8 D Ch)
    (hB1 : S23_9_B1 D Ch) (hS : KSub23) (hK : KOrdNatural) (h1930 : H1930 D)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (hline : IsOmegaPlus ↥(c.H hV) 6 (CFSG.Open.pRank 2 D.Z) ∧
      NatOmegaPlus (c.H hV) ⊤ ⊥ 6 (CFSG.Open.pRank 2 D.Z)) :
    IsL2Square ↥(Kbar c) (CFSG.Open.pRank 2 D.Z) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_Kbar_KstarBar c hV h8 hB1 hS hK h1930 h3 hnat
  exact IsL2Square.of_mulEquiv e.symm
    (isL2Square_KstarBar_of_Omega c hV ha hd h4 h1930 h3 hnat hline)

private theorem isPerfect_of_normal_sup_eq_top {P : Type*} [Group P]
    {F₁ F₂ : Subgroup P} (h₁ : F₁.Normal) (h₂ : F₂.Normal)
    (hsup : F₁ ⊔ F₂ = ⊤) (hinf : F₁ ⊓ F₂ = ⊥)
    (hP : Group.IsPerfect P) : Group.IsPerfect ↥F₁ := by
  haveI : F₂.Normal := h₂
  haveI : Group.IsPerfect P := hP
  haveI : Group.IsPerfect (P ⧸ F₂) := inferInstance
  let φ : ↥F₁ →* P ⧸ F₂ := (QuotientGroup.mk' F₂).comp F₁.subtype
  have hφsurj : Function.Surjective φ := by
    intro q
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective F₂ q
    have hp : p ∈ F₁ ⊔ F₂ := by rw [hsup]; exact Subgroup.mem_top p
    rw [Subgroup.mem_sup_of_normal_right] at hp
    obtain ⟨a, ha, b, hb, hab⟩ := hp
    refine ⟨⟨a, ha⟩, ?_⟩
    change (QuotientGroup.mk' F₂) a = (QuotientGroup.mk' F₂) p
    have hb' : (QuotientGroup.mk' F₂) b = 1 := (QuotientGroup.eq_one_iff _).mpr hb
    rw [← hab, map_mul, hb', mul_one]
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have hxy' : (QuotientGroup.mk' F₂) (x : P) = (QuotientGroup.mk' F₂) (y : P) := hxy
    have hmem : (x : P)⁻¹ * (y : P) ∈ F₂ := by
      have h1 : (QuotientGroup.mk' F₂) ((x : P)⁻¹ * (y : P)) = 1 := by
        rw [map_mul, map_inv, hxy', inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hmem1 : (x : P)⁻¹ * (y : P) ∈ F₁ := F₁.mul_mem (F₁.inv_mem x.2) y.2
    have hbot : (x : P)⁻¹ * (y : P) ∈ (⊥ : Subgroup P) := by
      rw [← hinf]
      exact Subgroup.mem_inf.mpr ⟨hmem1, hmem⟩
    have hone : (x : P)⁻¹ * (y : P) = 1 := Subgroup.mem_bot.mp hbot
    exact Subtype.ext (by
      have h := congrArg (fun z => (x : P) * z) hone
      simpa using h.symm)
  let e := MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

private theorem image_eq_bot_or_image_eq_bot_of_surjective {P Q : Type*} [Group P] [Group Q]
    [Finite Q] (σ : P →* Q) (hσ : Function.Surjective σ) (hQ : IsSimpleGroup Q)
    (hP : Group.IsPerfect P) {F₁ F₂ : Subgroup P} (h₁ : F₁.Normal) (h₂ : F₂.Normal)
    (hsup : F₁ ⊔ F₂ = ⊤)
    (hcomm : ∀ x ∈ F₁, ∀ y ∈ F₂, Commute x y) :
    F₁.map σ = ⊥ ∨ F₂.map σ = ⊥ := by
  by_contra h
  push Not at h
  obtain ⟨hne₁, hne₂⟩ := h
  haveI : Group.IsPerfect P := hP
  haveI : Group.IsPerfect Q := Group.IsPerfect.ofSurjective (f := σ) hσ
  haveI : (F₁.map σ).Normal := h₁.map σ hσ
  haveI : (F₂.map σ).Normal := h₂.map σ hσ
  have hI₁ : F₁.map σ = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (F₁.map σ)).resolve_left hne₁
  have hI₂ : F₂.map σ = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (F₂.map σ)).resolve_left hne₂
  have hle : (⊤ : Subgroup Q) ≤ Subgroup.centralizer (⊤ : Set Q) := by
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    have hx : x ∈ F₁.map σ := by rw [hI₁]; exact Subgroup.mem_top x
    have hy : y ∈ F₂.map σ := by rw [hI₂]; exact Subgroup.mem_top y
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    exact ((hcomm a ha b hb).map σ).symm
  have htop : ⁅(⊤ : Subgroup Q), ⊤⁆ = ⊤ := Group.IsPerfect.commutator_eq_top
  have hbot : (⊤ : Subgroup Q) = ⊥ :=
    eq_bot_of_commutator_eq_self_of_le_centralizer htop hle
  exact hne₁ (by rw [hI₁, hbot])

private theorem eq_one_of_map_eq_bot_of_sup_eq_top {P Q : Type*} [Group P] [Group Q]
    (σ : P →* Q) (hσ : Function.Surjective σ) {F₁ F₂ : Subgroup P}
    (h₂ : F₂.Normal) (hsup : F₁ ⊔ F₂ = ⊤)
    (hb₁ : F₁.map σ = ⊥) (hb₂ : F₂.map σ = ⊥) : ∀ z : Q, z = 1 := by
  haveI : F₂.Normal := h₂
  intro z
  obtain ⟨y, rfl⟩ := hσ z
  have hy : y ∈ F₁ ⊔ F₂ := by rw [hsup]; exact Subgroup.mem_top y
  rw [Subgroup.mem_sup_of_normal_right] at hy
  obtain ⟨a, ha, b, hb, hab⟩ := hy
  have ha' : σ a = 1 :=
    Subgroup.mem_bot.mp (by rw [← hb₁]; exact Subgroup.mem_map_of_mem σ ha)
  have hb' : σ b = 1 :=
    Subgroup.mem_bot.mp (by rw [← hb₂]; exact Subgroup.mem_map_of_mem σ hb)
  rw [← hab, map_mul, ha', hb', mul_one]

private theorem componentProjection_eq_one_of_factor_swap (c : Ctx23L D Ch)
    {C : Subgroup (Bar2 D.M)} (hC : CFSG.IsComponent C)
    (hY : Kbar c ≤ CFSG.layer (Bar2 D.M)) (hZ : Subgroup.center C = ⊥) {t : ↥C}
    (ht : ((t : ↥C) : Bar2 D.M) ∈
      Subgroup.normalizer (Kbar c : Set (Bar2 D.M)))
    {α : MulAut ↥(Kbar c)}
    (hα : ∀ y : ↥(Kbar c), ((α y : ↥(Kbar c)) : Bar2 D.M) =
      (t : Bar2 D.M) * (y : Bar2 D.M) * (t : Bar2 D.M)⁻¹)
    {F₁ F₂ : Subgroup ↥(Kbar c)} (hswap : F₁.map α.toMonoidHom = F₂)
    (hρ : ∀ z ∈ F₁, componentProjection hC hY hZ z = 1) :
    ∀ y ∈ F₂, componentProjection hC hY hZ y = 1 := by
  intro y hy
  have hy' : y ∈ F₁.map α.toMonoidHom := by rw [hswap]; exact hy
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy'
  have hzy' : α.symm y = z := by
    rw [← hzy]
    exact MulEquiv.symm_apply_apply α z
  have hconj := componentProjection_conj_normalizer hC hY hZ (α.symm y) t ht
  have heq : ((⟨(t : Bar2 D.M) * ((α.symm y : ↥(Kbar c)) : Bar2 D.M) *
      (t : Bar2 D.M)⁻¹, (Subgroup.mem_normalizer_iff.mp ht ((α.symm y : ↥(Kbar c)) : Bar2 D.M)).mp
        (α.symm y).2⟩ : ↥(Kbar c))) = y := by
    apply Subtype.ext
    simpa using (hα (α.symm y)).symm
  rw [heq, hzy'] at hconj
  rw [hρ z hz] at hconj
  simpa using hconj

private theorem mem_normalizer_of_map_factor_eq (c : Ctx23L D Ch) {C : Subgroup (Bar2 D.M)}
    {t : ↥C} {α : MulAut ↥(Kbar c)}
    (hα : ∀ y : ↥(Kbar c), ((α y : ↥(Kbar c)) : Bar2 D.M) =
      (t : Bar2 D.M) * (y : Bar2 D.M) * (t : Bar2 D.M)⁻¹)
    {F : Subgroup ↥(Kbar c)} (hF : F.map α.toMonoidHom = F) :
    ((t : ↥C) : Bar2 D.M) ∈
      Subgroup.normalizer ((F.map (Kbar c).subtype) : Set (Bar2 D.M)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hcomp : (MulAut.conj ((t : ↥C) : Bar2 D.M)).toMonoidHom.comp (Kbar c).subtype =
      (Kbar c).subtype.comp α.toMonoidHom := by
    ext y
    show (MulAut.conj ((t : ↥C) : Bar2 D.M)) (y : Bar2 D.M) = (α y : Bar2 D.M)
    rw [MulAut.conj_apply]
    exact (hα y).symm
  calc
    (F.map (Kbar c).subtype).map (MulAut.conj ((t : ↥C) : Bar2 D.M)).toMonoidHom =
        F.map ((MulAut.conj ((t : ↥C) : Bar2 D.M)).toMonoidHom.comp (Kbar c).subtype) := by
      rw [Subgroup.map_map]
    _ = F.map ((Kbar c).subtype.comp α.toMonoidHom) := by rw [hcomp]
    _ = (F.map α.toMonoidHom).map (Kbar c).subtype := by rw [← Subgroup.map_map]
    _ = F.map (Kbar c).subtype := by rw [hF]

private structure FactorPair (c : Ctx23L D Ch) {A : Type} [Group A] [Finite A]
    (e : ↥(Kbar c) ≃* A × A) where
  normalFirst : (prodFirstFactor e).Normal
  normalSecond : (prodSecondFactor e).Normal
  sup_eq_top : prodFirstFactor e ⊔ prodSecondFactor e = ⊤
  inf_eq_bot : prodFirstFactor e ⊓ prodSecondFactor e = ⊥
  commute : ∀ x ∈ prodFirstFactor e, ∀ y ∈ prodSecondFactor e, Commute x y
  perfectFirst : Group.IsPerfect ↥(prodFirstFactor e)
  perfectSecond : Group.IsPerfect ↥(prodSecondFactor e)
  simpleFirst : IsSimpleGroup ↥(prodFirstFactor e)
  simpleSecond : IsSimpleGroup ↥(prodSecondFactor e)

private def factorPair (c : Ctx23L D Ch) {A : Type} [Group A] [Finite A]
    (e : ↥(Kbar c) ≃* A × A) (hL2A : IsL2 A (CFSG.Open.pRank 2 D.Z))
    (hYp : ⁅Kbar c, Kbar c⁆ = Kbar c) : FactorPair c e := by
  haveI : Group.IsPerfect ↥(Kbar c) := Subgroup.isPerfect_iff.mpr hYp
  haveI : IsSimpleGroup A := isSimpleGroup_of_isL2 hL2A
  have h₁ := prodFirstFactor_normal e
  have h₂ := prodSecondFactor_normal e
  have hsup := prodFirstFactor_sup_prodSecondFactor e
  have hinf := prodFirstFactor_inf_prodSecondFactor e
  refine
    { normalFirst := h₁
      normalSecond := h₂
      sup_eq_top := hsup
      inf_eq_bot := hinf
      commute := fun x hx y hy => commute_prodFirstFactor_prodSecondFactor e hx hy
      perfectFirst := ?_
      perfectSecond := ?_
      simpleFirst := ?_
      simpleSecond := ?_ }
  · exact isPerfect_of_normal_sup_eq_top h₁ h₂ hsup hinf inferInstance
  · exact isPerfect_of_normal_sup_eq_top h₂ h₁ (by rw [sup_comm]; exact hsup)
      (by rw [inf_comm]; exact hinf) inferInstance
  · exact MulEquiv.isSimpleGroup (prodFirstFactorMulEquiv e)
  · exact MulEquiv.isSimpleGroup (prodSecondFactorMulEquiv e)

private noncomputable def componentProjectionRange (c : Ctx23L D Ch)
    {C : Subgroup (Bar2 D.M)} (hC : CFSG.IsComponent C)
    (hY : Kbar c ≤ CFSG.layer (Bar2 D.M)) (hZ : Subgroup.center C = ⊥) :
    ↥(Kbar c) →* ↥(componentProjection hC hY hZ).range :=
  (componentProjection hC hY hZ).codRestrict (componentProjection hC hY hZ).range
    fun x => ⟨x, rfl⟩

private theorem componentProjectionRange_surjective (c : Ctx23L D Ch)
    {C : Subgroup (Bar2 D.M)} (hC : CFSG.IsComponent C)
    (hY : Kbar c ≤ CFSG.layer (Bar2 D.M)) (hZ : Subgroup.center C = ⊥) :
    Function.Surjective (componentProjectionRange c hC hY hZ) := by
  intro y
  obtain ⟨x, hx⟩ := y.2
  exact ⟨x, Subtype.ext hx⟩

private theorem componentProjection_range_perfect (c : Ctx23L D Ch)
    {C : Subgroup (Bar2 D.M)} (hC : CFSG.IsComponent C)
    (hY : Kbar c ≤ CFSG.layer (Bar2 D.M)) (hZ : Subgroup.center C = ⊥)
    (hYp : ⁅Kbar c, Kbar c⁆ = Kbar c) :
    ⁅(componentProjection hC hY hZ).range, (componentProjection hC hY hZ).range⁆ =
      (componentProjection hC hY hZ).range := by
  haveI : Group.IsPerfect ↥(Kbar c) := Subgroup.isPerfect_iff.mpr hYp
  haveI : Group.IsPerfect ↥(componentProjection hC hY hZ).range :=
    Group.IsPerfect.range (componentProjection hC hY hZ)
  exact Subgroup.isPerfect_iff.mp inferInstance

private theorem normalizerMonoidHom_eq_one_of_componentProjection_range_eq_bot
    (c : Ctx23L D Ch) {C : Subgroup (Bar2 D.M)} (hC : CFSG.IsComponent C)
    (hY : Kbar c ≤ CFSG.layer (Bar2 D.M)) (hZ : Subgroup.center C = ⊥)
    (hRbot : (componentProjection hC hY hZ).range = ⊥)
    {t : ↥C} (ht : ((t : ↥C) : Bar2 D.M) ∈
      Subgroup.normalizer (Kbar c : Set (Bar2 D.M))) :
    (Kbar c).normalizerMonoidHom ⟨((t : ↥C) : Bar2 D.M), ht⟩ = 1 := by
  let α : MulAut ↥(Kbar c) := (Kbar c).normalizerMonoidHom ⟨((t : ↥C) : Bar2 D.M), ht⟩
  have hα : ∀ y : ↥(Kbar c), ((α y : ↥(Kbar c)) : Bar2 D.M) =
      (t : Bar2 D.M) * (y : Bar2 D.M) * (t : Bar2 D.M)⁻¹ :=
    fun y => Subgroup.normalizerMonoidHom_apply_apply_coe (Kbar c) _ y
  change α = 1
  ext y
  simp only [MulAut.one_apply]
  rw [hα]
  have hρy : componentProjection hC hY hZ y = 1 := by
    have hmem : componentProjection hC hY hZ y ∈ (componentProjection hC hY hZ).range :=
      ⟨y, rfl⟩
    rw [hRbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hconj := componentProjection_conj hC hY hZ y (m := ((t : ↥C) : Bar2 D.M)) (t : ↥C).2
  rw [hρy] at hconj
  have hconj' : (y : Bar2 D.M) * ((t : ↥C) : Bar2 D.M) * (y : Bar2 D.M)⁻¹ =
      ((t : ↥C) : Bar2 D.M) := by simpa using hconj
  have hyc : (y : Bar2 D.M) * ((t : ↥C) : Bar2 D.M) =
      ((t : ↥C) : Bar2 D.M) * (y : Bar2 D.M) := by
    calc (y : Bar2 D.M) * ((t : ↥C) : Bar2 D.M) =
        ((y : Bar2 D.M) * ((t : ↥C) : Bar2 D.M) * (y : Bar2 D.M)⁻¹) *
          (y : Bar2 D.M) := by group
      _ = ((t : ↥C) : Bar2 D.M) * (y : Bar2 D.M) := by rw [hconj']
  calc ((t : ↥C) : Bar2 D.M) * (y : Bar2 D.M) * ((t : ↥C) : Bar2 D.M)⁻¹ =
      ((y : Bar2 D.M) * ((t : ↥C) : Bar2 D.M)) * ((t : ↥C) : Bar2 D.M)⁻¹ := by rw [hyc]
    _ = (y : Bar2 D.M) := by group

private theorem false_of_factor_swap_of_componentProjection_eq_bot
    (c : Ctx23L D Ch) {C : Subgroup (Bar2 D.M)} (hC : CFSG.IsComponent C)
    (hY : Kbar c ≤ CFSG.layer (Bar2 D.M)) (hZ : Subgroup.center C = ⊥)
    {t : ↥C} (ht : ((t : ↥C) : Bar2 D.M) ∈
      Subgroup.normalizer (Kbar c : Set (Bar2 D.M)))
    {α : MulAut ↥(Kbar c)}
    (hα : ∀ y : ↥(Kbar c), ((α y : ↥(Kbar c)) : Bar2 D.M) =
      (t : Bar2 D.M) * (y : Bar2 D.M) * (t : Bar2 D.M)⁻¹)
    {F₁ F₂ : Subgroup ↥(Kbar c)} (h₂ : F₂.Normal) (hsup : F₁ ⊔ F₂ = ⊤)
    (hswap : F₁.map α.toMonoidHom = F₂)
    (hRsimple : IsSimpleGroup ↥(componentProjection hC hY hZ).range)
    (hb₁ : F₁.map (componentProjectionRange c hC hY hZ) = ⊥) :
    False := by
  have hb₁' : F₁.map (componentProjectionRange c hC hY hZ) = ⊥ := hb₁
  have hb₂ : F₂.map (componentProjectionRange c hC hY hZ) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hw
    exact Subgroup.mem_bot.mpr (Subtype.ext
      (componentProjection_eq_one_of_factor_swap c hC hY hZ ht hα hswap
        (fun u hu => by
          have humem : componentProjectionRange c hC hY hZ u ∈
              F₁.map (componentProjectionRange c hC hY hZ) :=
            Subgroup.mem_map_of_mem _ hu
          rw [hb₁'] at humem
          exact congrArg Subtype.val (Subgroup.mem_bot.mp humem)) y hy))
  have hall := eq_one_of_map_eq_bot_of_sup_eq_top (componentProjectionRange c hC hY hZ)
    (componentProjectionRange_surjective c hC hY hZ) h₂ hsup hb₁' hb₂
  obtain ⟨a, b, hab⟩ := hRsimple.toNontrivial.exists_pair_ne
  exact hab (by rw [hall a, hall b])

private theorem exists_sylow_le_normalizer_factors (c : Ctx23L D Ch) (h8 : S23_8 D Ch)
    (hB1 : S23_9_B1 D Ch) (hSS : KSub23Simple) (h1930 : H1930 D)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z) {A : Type} [Group A] [Finite A]
    (e : ↥(Kbar c) ≃* A × A) (hL2A : IsL2 A (CFSG.Open.pRank 2 D.Z))
    (hsimpleA : ∀ N : Subgroup A, N.Normal → N = ⊥ ∨ N = ⊤)
    (hcentralA : ∀ a : A, (∀ c, a * c = c * a) → a = 1)
    (hntA : ∃ a : A, a ≠ 1) {C : Subgroup (Bar2 D.M)} (hC : CFSG.IsComponent C) :
    ∃ T : Sylow 2 ↥C, ∀ t : T,
      ((t : ↥C) : Bar2 D.M) ∈ Subgroup.normalizer
        ((prodFirstFactor e).map (Kbar c).subtype : Set (Bar2 D.M)) ∧
      ((t : ↥C) : Bar2 D.M) ∈ Subgroup.normalizer
        ((prodSecondFactor e).map (Kbar c).subtype : Set (Bar2 D.M)) := by
  have hshape := b23Shape_of_isComponent c h8 h1930 hC
  have hZ : Subgroup.center C = ⊥ := center_component_eq_bot c h8 h1930 hC
  have hY : Kbar c ≤ CFSG.layer (Bar2 D.M) := c.barImage_Hinf_inf_L_le_layer hB1 h1930 h3
  have hYp : ⁅Kbar c, Kbar c⁆ = Kbar c := c.barImage_Hinf_inf_L_perfect
  haveI : Group.IsPerfect ↥(Kbar c) := Subgroup.isPerfect_iff.mpr hYp
  obtain ⟨hF₁n, hF₂n, hsup, -, hcomm, -, -, -, -⟩ := factorPair c e hL2A hYp
  let ρ := componentProjection hC hY hZ
  let ρr := componentProjectionRange c hC hY hZ
  have hρr : Function.Surjective ρr := componentProjectionRange_surjective c hC hY hZ
  have hRperf : ⁅ρ.range, ρ.range⁆ = ρ.range :=
    componentProjection_range_perfect c hC hY hZ hYp
  obtain ⟨T, hT⟩ := c.exists_sylow_component_le_normalizer_Kbar h8 h1930 hC
  refine ⟨T, fun t => ?_⟩
  let τ : ↥(Subgroup.normalizer (Kbar c : Set (Bar2 D.M))) := ⟨((t : ↥C) : Bar2 D.M), hT t⟩
  let α : MulAut ↥(Kbar c) := (Kbar c).normalizerMonoidHom τ
  have hα : ∀ y : ↥(Kbar c), ((α y : ↥(Kbar c)) : Bar2 D.M) =
      (t : Bar2 D.M) * (y : Bar2 D.M) * (t : Bar2 D.M)⁻¹ :=
    fun y => Subgroup.normalizerMonoidHom_apply_apply_coe (Kbar c) τ y
  have hnorm : ∀ {F : Subgroup ↥(Kbar c)}, F.map α.toMonoidHom = F →
      ((t : ↥C) : Bar2 D.M) ∈
        Subgroup.normalizer ((F.map (Kbar c).subtype) : Set (Bar2 D.M)) :=
    fun hF => mem_normalizer_of_map_factor_eq c hα hF
  rcases hSS C hshape ρ.range hRperf with hRbot | hRsimple
  · have hαid : α = 1 :=
      normalizerMonoidHom_eq_one_of_componentProjection_range_eq_bot c hC hY hZ hRbot (hT t)
    exact ⟨hnorm (by rw [hαid]; exact Subgroup.map_id _),
      hnorm (by rw [hαid]; exact Subgroup.map_id _)⟩
  · have htriv : (prodFirstFactor e).map ρr = ⊥ ∨ (prodSecondFactor e).map ρr = ⊥ :=
      image_eq_bot_or_image_eq_bot_of_surjective ρr hρr hRsimple inferInstance hF₁n hF₂n hsup
        hcomm
    have hpres : (prodFirstFactor e).map α.toMonoidHom = prodFirstFactor e ∧
        (prodSecondFactor e).map α.toMonoidHom = prodSecondFactor e := by
      rcases prodFirstFactor_map_mulAut_eq_or hsimpleA hcentralA hntA e α with h | h
      · exact h
      · obtain ⟨h1, h2⟩ := h
        rcases htriv with hb | hb
        · exact (false_of_factor_swap_of_componentProjection_eq_bot c hC hY hZ (hT t) hα hF₂n
            hsup h1 hRsimple hb).elim
        · exact (false_of_factor_swap_of_componentProjection_eq_bot c hC hY hZ (hT t) hα hF₁n
            (by rw [sup_comm]; exact hsup) h2 hRsimple hb).elim
    exact ⟨hnorm hpres.1, hnorm hpres.2⟩

private theorem exists_component_eq_of_isL2_factor (c : Ctx23L D Ch) (h8 : S23_8 D Ch)
    (hS : KSub23) (h1930 : H1930 D) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z)
    {Y : Subgroup (Bar2 D.M)} (hY : Y ≤ CFSG.layer (Bar2 D.M)) (hYp : ⁅Y, Y⁆ = Y)
    (hsimple : IsSimpleGroup ↥Y) (hne : Y ≠ ⊥) {m : ℕ} (hm : 3 ≤ m) (hL2 : IsL2 ↥Y m)
    (hT : ∀ C : Subgroup (Bar2 D.M), CFSG.IsComponent C → ∃ T : Sylow 2 ↥C,
      ∀ t : T, ((t : ↥C) : Bar2 D.M) ∈ Subgroup.normalizer (Y : Set (Bar2 D.M))) :
    ∃ C : Subgroup (Bar2 D.M), CFSG.IsComponent C ∧ Y = C := by
  have hRmax : ∀ N : Subgroup ↥Y, (⊥ : Subgroup (Bar2 D.M)).subgroupOf Y ≤ N → N.Normal →
      N = (⊥ : Subgroup (Bar2 D.M)).subgroupOf Y ∨ N = ⊤ := by
    intro N _ hN
    haveI : N.Normal := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact Or.inl (by rw [h]; simp)
    · exact Or.inr h
  have hcenter : ∀ C : Subgroup (Bar2 D.M), CFSG.IsComponent C → Subgroup.center C = ⊥ :=
    fun C hC => center_component_eq_bot c h8 h1930 hC
  rcases eq_bot_or_le_component_of_perfect_le_layer hY hYp (R := ⊥) bot_le hRmax
    (fun _ _ => bot_le) hcenter hT with hbot | ⟨C, hC, hle⟩
  · exact absurd hbot hne
  · have hshape : B23Shape C := by
      obtain ⟨X, hX, hXC⟩ := uc22p21c_exists_calC_of_component D.M hC
      rw [← hXC]
      exact shape_barImage_of_mem_calC (c := c) h8 h1930 hX
    let j : ↥Y →* ↥(Y.subgroupOf C) := (Subgroup.subgroupOfEquivOfLe hle).symm.toMonoidHom
    have hj : Function.Surjective j := (Subgroup.subgroupOfEquivOfLe hle).symm.surjective
    obtain ⟨T, hTC⟩ := hT C hC
    have hTC' : ∀ t : T, (t : ↥C) ∈
        Subgroup.normalizer ((Y.subgroupOf C : Subgroup ↥C) : Set ↥C) := by
      intro t
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        rw [Subgroup.mem_subgroupOf] at hy ⊢
        exact (Subgroup.mem_normalizer_iff.mp (hTC t) (y : Bar2 D.M)).1 hy
      · intro hy
        rw [Subgroup.mem_subgroupOf] at hy ⊢
        exact (Subgroup.mem_normalizer_iff.mp (hTC t) (y : Bar2 D.M)).2 hy
    rcases hS.1 ↥Y C m hm hL2 hshape (Y.subgroupOf C) ⟨j, hj⟩ ⟨T, hTC'⟩ with hsub | htop
    · exfalso
      apply hne
      rw [← Subgroup.map_subgroupOf_eq_of_le hle, hsub, Subgroup.map_bot]
    · refine ⟨C, hC, ?_⟩
      rw [← Subgroup.map_subgroupOf_eq_of_le hle, htop, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]

private noncomputable def barImageFirst (c : Ctx23L D Ch) {A : Type} [Group A] [Finite A]
    (e : ↥(Kbar c) ≃* A × A) : Subgroup (Bar2 D.M) :=
  (prodFirstFactor e).map (Kbar c).subtype

private noncomputable def barImageSecond (c : Ctx23L D Ch) {A : Type} [Group A] [Finite A]
    (e : ↥(Kbar c) ≃* A × A) : Subgroup (Bar2 D.M) :=
  (prodSecondFactor e).map (Kbar c).subtype

private structure FactorImageBasic (c : Ctx23L D Ch) {A : Type} [Group A] [Finite A]
    (e : ↥(Kbar c) ≃* A × A) where
  sup_eq : barImageFirst c e ⊔ barImageSecond c e = Kbar c
  inf_eq : barImageFirst c e ⊓ barImageSecond c e = ⊥
  first_ne : barImageFirst c e ≠ ⊥
  second_ne : barImageSecond c e ≠ ⊥
  first_layer : barImageFirst c e ≤ CFSG.layer (Bar2 D.M)
  second_layer : barImageSecond c e ≤ CFSG.layer (Bar2 D.M)

private def factorImageBasic (c : Ctx23L D Ch) {A : Type} [Group A] [Finite A]
    (e : ↥(Kbar c) ≃* A × A) (hY : Kbar c ≤ CFSG.layer (Bar2 D.M))
    (FP : FactorPair c e) : FactorImageBasic c e := by
  haveI : IsSimpleGroup ↥(prodFirstFactor e) := FP.simpleFirst
  haveI : IsSimpleGroup ↥(prodSecondFactor e) := FP.simpleSecond
  have hF₁ne : prodFirstFactor e ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot (prodFirstFactor e)).mp inferInstance
  have hF₂ne : prodSecondFactor e ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot (prodSecondFactor e)).mp inferInstance
  have hsup : barImageFirst c e ⊔ barImageSecond c e = Kbar c := by
    rw [barImageFirst, barImageSecond, ← Subgroup.map_sup, FP.sup_eq_top,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hinf : barImageFirst c e ⊓ barImageSecond c e = ⊥ := by
    rw [barImageFirst, barImageSecond,
      ← Subgroup.map_inf _ _ _ (Kbar c).subtype_injective, FP.inf_eq_bot, Subgroup.map_bot]
  have hfirst_ne : barImageFirst c e ≠ ⊥ := by
    intro h
    apply hF₁ne
    apply Subgroup.map_injective (Kbar c).subtype_injective
    have h' : (prodFirstFactor e).map (Kbar c).subtype = ⊥ := h
    rw [h', Subgroup.map_bot]
  have hsecond_ne : barImageSecond c e ≠ ⊥ := by
    intro h
    apply hF₂ne
    apply Subgroup.map_injective (Kbar c).subtype_injective
    have h' : (prodSecondFactor e).map (Kbar c).subtype = ⊥ := h
    rw [h', Subgroup.map_bot]
  have hfirst_layer : barImageFirst c e ≤ CFSG.layer (Bar2 D.M) := by
    rw [barImageFirst]
    exact (Subgroup.map_subtype_le _).trans hY
  have hsecond_layer : barImageSecond c e ≤ CFSG.layer (Bar2 D.M) := by
    rw [barImageSecond]
    exact (Subgroup.map_subtype_le _).trans hY
  exact
    { sup_eq := hsup
      inf_eq := hinf
      first_ne := hfirst_ne
      second_ne := hsecond_ne
      first_layer := hfirst_layer
      second_layer := hsecond_layer }

private structure FactorImageFacts (c : Ctx23L D Ch) {A : Type} [Group A] [Finite A]
    (e : ↥(Kbar c) ≃* A × A) extends FactorImageBasic c e where
  first_perfect : ⁅barImageFirst c e, barImageFirst c e⁆ = barImageFirst c e
  second_perfect : ⁅barImageSecond c e, barImageSecond c e⁆ = barImageSecond c e
  first_simple : IsSimpleGroup ↥(barImageFirst c e)
  second_simple : IsSimpleGroup ↥(barImageSecond c e)
  first_L2 : IsL2 ↥(barImageFirst c e) (CFSG.Open.pRank 2 D.Z)
  second_L2 : IsL2 ↥(barImageSecond c e) (CFSG.Open.pRank 2 D.Z)

private def factorImageFacts (c : Ctx23L D Ch) {A : Type} [Group A] [Finite A]
    (e : ↥(Kbar c) ≃* A × A) (hY : Kbar c ≤ CFSG.layer (Bar2 D.M))
    (FP : FactorPair c e) (hL2A : IsL2 A (CFSG.Open.pRank 2 D.Z)) :
    FactorImageFacts c e := by
  haveI : Group.IsPerfect ↥(prodFirstFactor e) := FP.perfectFirst
  haveI : Group.IsPerfect ↥(prodSecondFactor e) := FP.perfectSecond
  haveI : IsSimpleGroup A := isSimpleGroup_of_isL2 hL2A
  let e₁ : ↥(prodFirstFactor e) ≃* ↥(barImageFirst c e) :=
    Subgroup.equivMapOfInjective _ (Kbar c).subtype (Kbar c).subtype_injective
  let e₂ : ↥(prodSecondFactor e) ≃* ↥(barImageSecond c e) :=
    Subgroup.equivMapOfInjective _ (Kbar c).subtype (Kbar c).subtype_injective
  let eA : A ≃* ↥(barImageFirst c e) := (prodFirstFactorMulEquiv e).symm.trans e₁
  let eB : A ≃* ↥(barImageSecond c e) := (prodSecondFactorMulEquiv e).symm.trans e₂
  have hperf₁ : Group.IsPerfect ↥(barImageFirst c e) :=
    Group.IsPerfect.ofSurjective (f := e₁.toMonoidHom) e₁.surjective
  have hperf₂ : Group.IsPerfect ↥(barImageSecond c e) :=
    Group.IsPerfect.ofSurjective (f := e₂.toMonoidHom) e₂.surjective
  exact
    { factorImageBasic c e hY FP with
      first_perfect := Subgroup.isPerfect_iff.mp hperf₁
      second_perfect := Subgroup.isPerfect_iff.mp hperf₂
      first_simple := MulEquiv.isSimpleGroup eA.symm
      second_simple := MulEquiv.isSimpleGroup eB.symm
      first_L2 := CFSG.Blueprint.LieModel.of_mulEquiv eA hL2A
      second_L2 := CFSG.Blueprint.LieModel.of_mulEquiv eB hL2A }

private theorem exists_two_components_of_Omega (c : Ctx23L D Ch) (h8 : S23_8 D Ch)
    (hB1 : S23_9_B1 D Ch) (hS : KSub23) (hSS : KSub23Simple) (h1930 : H1930 D)
    (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z) (hKbar : Kbar c ≠ ⊥)
    {A : Type} [Group A] [Finite A] (e : ↥(Kbar c) ≃* A × A)
    (hL2A : IsL2 A (CFSG.Open.pRank 2 D.Z))
    (hsimpleA : ∀ N : Subgroup A, N.Normal → N = ⊥ ∨ N = ⊤)
    (hcentralA : ∀ a : A, (∀ c, a * c = c * a) → a = 1)
    (hntA : ∃ a : A, a ≠ 1) :
    ∃ X₁ X₂ : Subgroup G, X₁ ∈ calC D.M ∧ X₂ ∈ calC D.M ∧ X₁ ≠ X₂ ∧
      Kbar c = barImage D.M X₁ ⊔ barImage D.M X₂ := by
  have hY : Kbar c ≤ CFSG.layer (Bar2 D.M) := c.barImage_Hinf_inf_L_le_layer hB1 h1930 h3
  have hYp : ⁅Kbar c, Kbar c⁆ = Kbar c := c.barImage_Hinf_inf_L_perfect
  let FP := factorPair c e hL2A hYp
  let FI := factorImageFacts c e hY FP hL2A
  have hTYA : ∀ C : Subgroup (Bar2 D.M), CFSG.IsComponent C → ∃ T : Sylow 2 ↥C,
      ∀ t : T, ((t : ↥C) : Bar2 D.M) ∈
        Subgroup.normalizer ((barImageFirst c e) : Set (Bar2 D.M)) := by
    intro C hC
    obtain ⟨T, hT⟩ := exists_sylow_le_normalizer_factors c h8 hB1 hSS h1930 h3 e hL2A
      hsimpleA hcentralA hntA hC
    exact ⟨T, fun t => (hT t).1⟩
  have hTYB : ∀ C : Subgroup (Bar2 D.M), CFSG.IsComponent C → ∃ T : Sylow 2 ↥C,
      ∀ t : T, ((t : ↥C) : Bar2 D.M) ∈
        Subgroup.normalizer ((barImageSecond c e) : Set (Bar2 D.M)) := by
    intro C hC
    obtain ⟨T, hT⟩ := exists_sylow_le_normalizer_factors c h8 hB1 hSS h1930 h3 e hL2A
      hsimpleA hcentralA hntA hC
    exact ⟨T, fun t => (hT t).2⟩
  obtain ⟨CA, hCA, hYAeq⟩ := exists_component_eq_of_isL2_factor c h8 hS h1930 h3
    FI.first_layer FI.first_perfect FI.first_simple FI.first_ne h3 FI.first_L2 hTYA
  obtain ⟨CB, hCB, hYBeq⟩ := exists_component_eq_of_isL2_factor c h8 hS h1930 h3
    FI.second_layer FI.second_perfect FI.second_simple FI.second_ne h3 FI.second_L2 hTYB
  have hCne : CA ≠ CB := by
    intro h
    have hYAYB : barImageFirst c e = barImageSecond c e := by rw [hYAeq, h, hYBeq]
    have hinf := FI.inf_eq
    rw [← hYAYB, inf_idem] at hinf
    exact FI.first_ne hinf
  obtain ⟨X₁, hX₁cal, hX₁C⟩ := uc22p21c_exists_calC_of_component D.M hCA
  obtain ⟨X₂, hX₂cal, hX₂C⟩ := uc22p21c_exists_calC_of_component D.M hCB
  refine ⟨X₁, X₂, hX₁cal, hX₂cal, ?_, ?_⟩
  · intro h
    apply hCne
    rw [← hX₁C, ← hX₂C, h]
  · rw [← FI.sup_eq, hYAeq, hYBeq, ← hX₁C, ← hX₂C]

end Ctx23L

theorem s23_9_B23Omega_of (D : Data G) (Ch : Choice2011 G) (h2 : S23_2_natural D Ch)
    (h3 : S23_3 D Ch) (h4 : S23_4 D Ch) (h8 : S23_8 D Ch) (hB1 : S23_9_B1 D Ch)
    (ha : KTab23a) (hd : KTab23d) (hK : KOrdNatural) (hS : KSub23) (hSS : KSub23Simple) :
    S23_9_B23Omega D Ch := by
  intro h1930 c h3rank hV hOplus hNatPlus
  obtain ⟨hV₀, hnat₀⟩ := Ctx23L.exists_isNaturalClassicalModule D Ch h2 h3 h4 h1930 c
  have hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z) := hnat₀
  have hsq : IsL2Square ↥(Ctx23L.Kbar c) (CFSG.Open.pRank 2 D.Z) :=
    Ctx23L.isL2Square_Kbar_of_Omega c hV ha hd h4 h8 hB1 hS hK h1930 h3rank hnat
      ⟨hOplus, hNatPlus⟩
  by_cases hKbar : Ctx23L.Kbar c = ⊥
  · exact Or.inl (Ctx23L.Hinf_inf_L_eq_bot_of_Kbar_eq_bot c hKbar)
  · refine Or.inr (Or.inr ?_)
    obtain ⟨A, B, gA, gB, ⟨e₀⟩, hL2A, hL2B⟩ := hsq
    letI := gA
    letI := gB
    have hSCA := hL2A.statedClassicalModel (by decide)
    have hSCB := hL2B.statedClassicalModel (by decide)
    obtain ⟨eBA⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hSCB hSCA
    let e : ↥(Ctx23L.Kbar c) ≃* A × A := e₀.trans (MulEquiv.prodCongr (MulEquiv.refl A) eBA)
    haveI : Finite (A × A) := Finite.of_equiv ↥(Ctx23L.Kbar c) e.toEquiv
    haveI : Finite A := Finite.of_injective (fun a : A => (a, (1 : A)))
      (fun a b h => by simpa using h)
    haveI : IsSimpleGroup A := isSimpleGroup_of_isL2 hL2A
    have hsimple : ∀ N : Subgroup A, N.Normal → N = ⊥ ∨ N = ⊤ := by
      intro N hN
      haveI : N.Normal := hN
      exact IsSimpleGroup.eq_bot_or_eq_top_of_normal N
    have hcenter : Subgroup.center A = ⊥ :=
      CFSG.Quasithin.F420.center_eq_bot_of_statedPSL hSCA
    have hcentral : ∀ a : A, (∀ c, a * c = c * a) → a = 1 := by
      intro a ha'
      have hmem : a ∈ Subgroup.center A := Subgroup.mem_center_iff.mpr (fun g => (ha' g).symm)
      rw [hcenter] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hnt : ∃ a : A, a ≠ 1 := by
      obtain ⟨a, ha'⟩ := exists_ne (1 : A)
      exact ⟨a, ha'⟩
    obtain ⟨X₁, X₂, hX₁, hX₂, hne, heq⟩ :=
      Ctx23L.exists_two_components_of_Omega c h8 hB1 hS hSS h1930 h3rank hKbar e hL2A
        hsimple hcentral hnt
    exact ⟨X₁, X₂, hX₁, hX₂, hne, heq⟩

theorem s23_9_B23_of (D : Data G) (Ch : Choice2011 G) (h2 : S23_2_natural D Ch)
    (h3 : S23_3 D Ch) (h4 : S23_4 D Ch) (h8 : S23_8 D Ch) (hB1 : S23_9_B1 D Ch)
    (ha : KTab23a) (hd : KTab23d) (hK : KOrdNatural) (hS : KSub23) (hSS : KSub23Simple) :
    S23_9_B23 D Ch := by
  intro h1930 c h3rank
  dsimp only
  by_cases hO : ∃ hV : IsElemAbelian 2 c.V,
      IsOmegaPlus ↥(barSub ⊥ c.V hV c.L) 6 (CFSG.Open.pRank 2 D.Z) ∧
        NatOmegaPlus (barSub ⊥ c.V hV c.L) ⊤ ⊥ 6 (CFSG.Open.pRank 2 D.Z)
  · obtain ⟨hV, hOplus, hNatPlus⟩ := hO
    rcases s23_9_B23Omega_of D Ch h2 h3 h4 h8 hB1 ha hd hK hS hSS h1930 c h3rank hV
      hOplus hNatPlus with hbot | hcal | hsplit
    · exact Or.inl hbot
    · exact Or.inr (Or.inl hcal)
    · exact Or.inr (Or.inr (Or.inl ⟨⟨hV, hOplus, hNatPlus⟩, hsplit⟩))
  · rcases s23_9_B23_nonOmega_of D Ch h2 h3 h4 h8 hB1 ha hd hK hS h1930 c h3rank hO with
      hbot | hcal | hsu
    · exact Or.inl hbot
    · exact Or.inr (Or.inl hcal)
    · exact Or.inr (Or.inr (Or.inr hsu))

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
