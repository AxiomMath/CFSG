module

public import CFSG.Quasithin.Background.RonanF918Dict
public import CFSG.Quasithin.Background.B1MoreElevenF

public section

namespace CFSG.Quasithin.RonanF918

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

section Sec

attribute [local instance] CFSG.Quasithin.commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

theorem kbarOf_mem_hat_of_mem (h : HypF918 T V L V₁ Vp H K) {X : Subgroup G} (hXH : X ≤ H)
    {x : G} (hx : x ∈ X) : kbarOf h (hXH hx) ∈ hat' V₁ Vp H K T X :=
  mem_secImg.mpr ⟨⟨secMk (Subgroup.normalizer (V₁ : Set G)) V₁
      ⟨x, h.H_le_normalizer_V₁ (hXH hx)⟩,
    tilde_mem_normalizer_CcOf (h.H_le_normalizer_V₁ (hXH hx))
      (le_normalizer_conjClosure Vp H (hXH hx)) (h.K₀_normal (hXH hx))⟩,
    secMk_mem_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁) (X := X)
      (x := ⟨x, h.H_le_normalizer_V₁ (hXH hx)⟩) hx, rfl⟩

theorem kbarOf_inv (h : HypF918 T V L V₁ Vp H K) {x : G} (hx : x ∈ H) :
    kbarOf h (H.inv_mem hx) = (kbarOf h hx)⁻¹ := by
  unfold kbarOf
  rw [← map_inv]
  congr 1

theorem mem_fixV_of_thetaMap_eq_one [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    {w : ↥(tildeOf V₁ (conjClosure I H))} (hw : thetaMap h hIU w = 1) :
    w ∈ fixV (autIH V₁ I H (conjClosure K T)) := by
  rw [thetaMap_eq_one_iff] at hw
  intro a ha
  obtain ⟨x, hx, hxa⟩ : a ∈ ((conjClosure K T).subgroupOf H).map
      (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)) := by
    rw [← autIH_eq_map h h.K₀_le_H]
    exact ha
  have hx' : (x : G) ∈ conjClosure K T := Subgroup.mem_subgroupOf.mp hx
  rw [← hxa]
  apply Subtype.ext
  rw [actH_apply_coe]
  have hcomm := Subgroup.mem_centralizer_iff.mp hw.2
    (secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨x, h.H_le_normalizer_V₁ x.2⟩)
    (secMk_mem_secImg (A := Subgroup.normalizer (V₁ : Set G)) (B := V₁)
      (X := conjClosure K T) (x := ⟨x, h.H_le_normalizer_V₁ x.2⟩) hx')
  calc secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨x, h.H_le_normalizer_V₁ x.2⟩ *
        (w : GtOf V₁) * (secMk (Subgroup.normalizer (V₁ : Set G)) V₁
          ⟨x, h.H_le_normalizer_V₁ x.2⟩)⁻¹
      = (w : GtOf V₁) * secMk (Subgroup.normalizer (V₁ : Set G)) V₁
          ⟨x, h.H_le_normalizer_V₁ x.2⟩ * (secMk (Subgroup.normalizer (V₁ : Set G)) V₁
          ⟨x, h.H_le_normalizer_V₁ x.2⟩)⁻¹ := by rw [hcomm]
    _ = (w : GtOf V₁) := by group

theorem thetaMap_eq_one_of_mem_fixV [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    {w : ↥(tildeOf V₁ (conjClosure I H))} (hw : w ∈ fixV (autIH V₁ I H (conjClosure K T))) :
    thetaMap h hIU w = 1 :=
  modFix_le_ker_thetaMap h hIU ⊤ ⟨trivial, fun a => hw a a.2⟩

@[expose] noncomputable def thetaV [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) :
    ↥(subM V₁ (conjClosure I H) I) →* ↥(hat' V₁ Vp H K T I) :=
  ((thetaMap h hIU).comp (subM V₁ (conjClosure I H) I).subtype).codRestrict
    (hat' V₁ Vp H K T I) (fun v => by
      rw [hat_eq_map_theta h hIU (le_conjClosure I H)]
      exact ⟨v, v.2, rfl⟩)

theorem thetaV_coe [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (v : ↥(subM V₁ (conjClosure I H) I)) :
    ((thetaV (T := T) (V := V) (L := L) (Vp := Vp) (K := K) h hIU v :
      ↥(hat' V₁ Vp H K T I)) : GhOf V₁ (conjClosure Vp H) (conjClosure K T)) =
      thetaMap h hIU (v : ↥(tildeOf V₁ (conjClosure I H))) := rfl

theorem thetaV_surjective [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) :
    Function.Surjective (thetaV (T := T) (V := V) (L := L) (Vp := Vp) (K := K) h hIU) := by
  rintro ⟨y, hy⟩
  rw [hat_eq_map_theta h hIU (le_conjClosure I H)] at hy
  obtain ⟨v, hv, rfl⟩ := hy
  exact ⟨⟨v, hv⟩, rfl⟩

theorem ker_thetaV [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) :
    (thetaV (T := T) (V := V) (L := L) (Vp := Vp) (K := K) h hIU).ker =
      (fixV (autIH V₁ I H (conjClosure K T))).subgroupOf (subM V₁ (conjClosure I H) I) := by
  ext v
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h1
    exact mem_fixV_of_thetaMap_eq_one h hIU (congrArg Subtype.val h1)
  · intro h1
    exact Subtype.ext (thetaMap_eq_one_of_mem_fixV h hIU h1)

@[expose] noncomputable def psiSec [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) :
    Sec (subM V₁ (conjClosure I H) I) (fixV (autIH V₁ I H (conjClosure K T))) ≃*
      ↥(hat' V₁ Vp H K T I) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_thetaV h hIU).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (thetaV_surjective h hIU))

theorem psiSec_mk [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (u : ↥(subM V₁ (conjClosure I H) I)) :
    psiSec h hIU (QuotientGroup.mk u) = thetaV h hIU u := rfl


theorem isFFInt_hat_of_isFFModule [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]
    (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hFF : IsFFModule (autSec (autIH V₁ I H (conjClosure K T) ⊔ autIH V₁ I H T)
      (subM V₁ (conjClosure I H) I) (fixV (autIH V₁ I H (conjClosure K T))))) :
    ∃ hV : IsElemAbelian 2 (hat' V₁ Vp H K T I),
      IsFFInt (hat' V₁ Vp H K T (conjClosure K T ⊔ T)) (hat' V₁ Vp H K T I) hV := by
  have hel : IsElemAbelian 2 (hat' V₁ Vp H K T I) :=
    isElemAbelian_secImg (h.isElemAbelian_tilde_of_le hIU)
  refine ⟨hel, ?_⟩
  letI : CommGroup ↥(hat' V₁ Vp H K T I) := commGroupOfElemAbelian hel
  show @IsFFModule ↥(hat' V₁ Vp H K T I) (commGroupOfElemAbelian hel)
    (autOn (hat' V₁ Vp H K T (conjClosure K T ⊔ T)) (hat' V₁ Vp H K T I))
  have h1 := B1Red.isFFModule_map_congr' (W' := ↥(hat' V₁ Vp H K T I)) (psiSec h hIU) hFF
  refine B1Red.isFFModule_mono ?_ h1
  rintro _ ⟨g', hg', rfl⟩
  obtain ⟨⟨g, hgst⟩, hgX, rfl⟩ := mem_autQuot.mp hg'
  obtain ⟨⟨x, hxst⟩, hxX, hxg⟩ := mem_autSub.mp hgX
  have hXle : autIH V₁ I H (conjClosure K T) ⊔ autIH V₁ I H T ≤
      autIH V₁ I H (conjClosure K T ⊔ T) :=
    sup_le (autOn_le_autOn _ (secImg_mono le_sup_left)) (autOn_le_autOn _ (secImg_mono le_sup_right))
  have hxm : x ∈ autIH V₁ I H (conjClosure K T ⊔ T) := hXle hxX
  rw [autIH_eq_map h h.K₀T_le_H] at hxm
  obtain ⟨y, hy, hyx⟩ := hxm
  have hyKT : (y : G) ∈ conjClosure K T ⊔ T := Subgroup.mem_subgroupOf.mp hy
  set yb := kbarOf h y.2 with hyb
  have hybX : yb ∈ hat' V₁ Vp H K T (conjClosure K T ⊔ T) :=
    kbarOf_mem_hat_of_mem h h.K₀T_le_H hyKT
  have hact : ∀ u : ↥(tildeOf V₁ (conjClosure I H)),
      thetaMap h hIU (x u) = yb * thetaMap h hIU u * yb⁻¹ := by
    intro u
    rw [← hyx]
    exact thetaMap_actH h hIU y.2 u
  have hactinv : ∀ u : ↥(tildeOf V₁ (conjClosure I H)),
      thetaMap h hIU (x⁻¹ u) = yb⁻¹ * thetaMap h hIU u * yb := by
    intro u
    have h2 := thetaMap_actH h hIU (H.inv_mem y.2) u
    rw [kbarOf_inv h y.2, inv_inv] at h2
    have e : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
        ⟨(y : G)⁻¹, H.inv_mem y.2⟩ = x⁻¹ := by
      rw [← hyx, ← map_inv]
      rfl
    rw [e] at h2
    exact h2
  have hmapθ := hat_eq_map_theta h hIU (le_conjClosure I H)
  have hxinvst : x⁻¹ ∈ stabSub (subM V₁ (conjClosure I H) I) := (stabSub _).inv_mem hxst
  have hbN : yb ∈ Subgroup.normalizer ((hat' V₁ Vp H K T I : Subgroup
      (GhOf V₁ (conjClosure Vp H) (conjClosure K T))) :
      Set (GhOf V₁ (conjClosure Vp H) (conjClosure K T))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    rw [hmapθ]
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨x u, (hxst u).2 hu, hact u⟩
    · rintro ⟨u', hu', hu'e⟩
      refine ⟨x⁻¹ u', (hxinvst u').2 hu', ?_⟩
      rw [hactinv u', hu'e]
      group
  rw [mem_autOn_iff]
  refine ⟨⟨yb, hbN⟩, hybX, ?_⟩
  refine MulEquiv.ext fun z => ?_
  obtain ⟨q, rfl⟩ := (psiSec h hIU).surjective z
  induction q using QuotientGroup.induction_on with
  | H u =>
    apply Subtype.ext
    rw [conjAct_apply_coe']
    have e1 : ((MulAut.congr (psiSec h hIU)).toMonoidHom
        (quotHom ((fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I)) ⟨g, hgst⟩)) ((psiSec h hIU) (QuotientGroup.mk u)) =
        psiSec h hIU (quotHom ((fixV (autIH V₁ I H (conjClosure K T))).subgroupOf
          (subM V₁ (conjClosure I H) I)) ⟨g, hgst⟩ (QuotientGroup.mk u)) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply]
    rw [e1, quotHom_mk]
    have hgx : ((g u : ↥(subM V₁ (conjClosure I H) I)) : ↥(tildeOf V₁ (conjClosure I H))) =
        x (u : ↥(tildeOf V₁ (conjClosure I H))) := by
      have := congrArg (fun φ : MulAut ↥(subM V₁ (conjClosure I H) I) =>
        ((φ u : ↥(subM V₁ (conjClosure I H) I)) : ↥(tildeOf V₁ (conjClosure I H)))) hxg
      exact this.symm
    show yb * thetaMap h hIU (u : ↥(tildeOf V₁ (conjClosure I H))) * yb⁻¹ =
      thetaMap h hIU ((g u : ↥(subM V₁ (conjClosure I H) I)) : ↥(tildeOf V₁ (conjClosure I H)))
    rw [hgx]
    exact (hact _).symm

end Sec

end CFSG.Quasithin.RonanF918
