module

public import CFSG.Quasithin.Vol2.Ch12Sec6Final

public section

namespace CFSG.Quasithin.H13.F126

open CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G] {T V L V₁ Vp H : Subgroup G}

abbrev N1 (V₁ : Subgroup G) : Subgroup G := Subgroup.normalizer (V₁ : Set G)

abbrev UT (V₁ Vp H : Subgroup G) : Subgroup (SecQuot (N1 V₁) V₁) :=
  tildeOf V₁ (conjClosure Vp H)

theorem le_N1 (h : HypF91 T V L V₁ Vp H) : H ≤ N1 V₁ := h.H_normalizes_V₁

@[expose] noncomputable def toSec (h : HypF91 T V L V₁ Vp H) : ↥H →* SecQuot (N1 V₁) V₁ :=
  (secMk (N1 V₁) V₁).comp (Subgroup.inclusion (le_N1 h))

theorem toSec_mem_normalizer (h : HypF91 T V L V₁ Vp H) (x : ↥H) :
    toSec h x ∈ Subgroup.normalizer (UT V₁ Vp H : Set (SecQuot (N1 V₁) V₁)) :=
  HypF91.tilde_le_normalizer (Vp := Vp) le_rfl (secMk_mem_secImg x.2)

@[expose] noncomputable def thetaH (h : HypF91 T V L V₁ Vp H) : ↥H →* MulAut ↥(UT V₁ Vp H) :=
  (conjAct (UT V₁ Vp H)).comp
    { toFun := fun x => ⟨toSec h x, toSec_mem_normalizer h x⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun x y => Subtype.ext (map_mul _ x y) }

theorem thetaH_apply (h : HypF91 T V L V₁ Vp H) (x : ↥H) (w : ↥(UT V₁ Vp H)) :
    ((thetaH h x w : ↥(UT V₁ Vp H)) : SecQuot (N1 V₁) V₁) = toSec h x * w * (toSec h x)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe _ _ w

theorem thetaH_apply_secMk (h : HypF91 T V L V₁ Vp H) (x : ↥H) {u : G} (hu : u ∈ N1 V₁) :
    toSec h x * secMk (N1 V₁) V₁ ⟨u, hu⟩ * (toSec h x)⁻¹ =
      secMk (N1 V₁) V₁ ⟨x * u * (x : G)⁻¹, (N1 V₁).mul_mem ((N1 V₁).mul_mem (le_N1 h x.2) hu)
        ((N1 V₁).inv_mem (le_N1 h x.2))⟩ := by
  rw [toSec, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul]
  rfl

theorem pCore_le_ker [Finite G] (h : HypF91 T V L V₁ Vp H) :
    CFSG.pCore 2 ↥H ≤ (thetaH h).ker := by
  intro q hq
  have hqQ : (q : G) ∈ pCoreOf 2 H := by
    refine ⟨q, ?_, rfl⟩
    assumption
  have hcent := (h.tilde_inf_centralizer_pCoreOf (le_rfl : H ≤ H)).symm.le
    (secMk_mem_secImg (A := N1 V₁) (B := V₁) (x := ⟨q, le_N1 h q.2⟩) ⟨q.2, hqQ⟩)
  rw [MonoidHom.mem_ker]
  ext w
  rw [MulAut.one_apply, thetaH_apply]
  have hc := Subgroup.mem_centralizer_iff.1 hcent.2 (w : SecQuot (N1 V₁) V₁) w.2
  change toSec h q * w * (toSec h q)⁻¹ = w
  have e : toSec h q = secMk (N1 V₁) V₁ ⟨q, le_N1 h q.2⟩ := rfl
  rw [e, ← hc, mul_inv_cancel_right]

@[expose] noncomputable def psiH [Finite G] (h : HypF91 T V L V₁ Vp H) :
    S126.HStar H →* MulAut ↥(UT V₁ Vp H) :=
  QuotientGroup.lift (CFSG.pCore 2 ↥H) (thetaH h) (pCore_le_ker h)

theorem psiH_mk [Finite G] (h : HypF91 T V L V₁ Vp H) (x : ↥H) :
    psiH h (QuotientGroup.mk x) = thetaH h x := rfl

theorem range_thetaH (h : HypF91 T V L V₁ Vp H) {B : Subgroup G} (hBH : B ≤ H) :
    (B.subgroupOf H).map (thetaH h) = autOn (tildeOf V₁ B) (UT V₁ Vp H) := by
  ext f
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨toSec h x, toSec_mem_normalizer h x⟩,
      Subgroup.mem_subgroupOf.2 (secMk_mem_secImg (Subgroup.mem_subgroupOf.1 hx)), rfl⟩
  · rintro ⟨⟨s, hsN⟩, hs, rfl⟩
    have hs' : s ∈ tildeOf V₁ B := Subgroup.mem_subgroupOf.1 hs
    obtain ⟨⟨b, hbN⟩, hbB, rfl⟩ := mem_secImg.1 hs'
    refine ⟨⟨b, hBH hbB⟩, Subgroup.mem_subgroupOf.2 hbB, ?_⟩
    rfl

theorem psiH_injective [Finite G] (h : HypF91 T V L V₁ Vp H) : Function.Injective (psiH h) := by
  have hrange : (psiH h).range = autOn (tildeOf V₁ H) (UT V₁ Vp H) := by
    rw [← range_thetaH h le_rfl, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
    ext f
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      exact ⟨QuotientGroup.mk x, rfl⟩
  have hcard : Nat.card (psiH h).range = Nat.card (S126.HStar H) := by
    rw [hrange, h.card_autOn_tilde le_rfl, inf_eq_right.2 (pCoreOf_le 2 H), Subgroup.relIndex,
      pCoreOf, map_subtype_subgroupOf']
    rfl
  have hk := Subgroup.card_mul_index (psiH h).ker
  rw [Subgroup.index_ker, hcard] at hk
  have hpos : 0 < Nat.card (S126.HStar H) := Nat.card_pos
  have h1 : Nat.card ↥(psiH h).ker = 1 :=
    Nat.eq_of_mul_eq_mul_right hpos (hk.trans (one_mul _).symm)
  rw [← MonoidHom.ker_eq_bot_iff]
  exact Subgroup.card_eq_one.1 h1

theorem eq_top_of_le [Finite G] (h : HypF91 T V L V₁ Vp H) (S : Subgroup ↥(UT V₁ Vp H))
    (hVS : ∀ w : ↥(UT V₁ Vp H), (w : SecQuot (N1 V₁) V₁) ∈ tildeOf V₁ Vp → w ∈ S)
    (hinv : ∀ x : ↥H, ∀ s ∈ S, thetaH h x s ∈ S) : S = ⊤ := by
  have hUN : conjClosure Vp H ≤ N1 V₁ :=
    h.conjClosure_Vp_le_pCoreOf.trans ((pCoreOf_le 2 H).trans (le_N1 h))
  have hVpN : Vp ≤ N1 V₁ := (le_conjClosure Vp H).trans hUN
  let P : Subgroup G :=
    { carrier := {g | ∃ hg : g ∈ N1 V₁, secMk (N1 V₁) V₁ ⟨g, hg⟩ ∈ S.map (UT V₁ Vp H).subtype}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨(N1 V₁).mul_mem ha hb, ?_⟩
        have : secMk (N1 V₁) V₁ ⟨a * b, (N1 V₁).mul_mem ha hb⟩ =
            secMk (N1 V₁) V₁ ⟨a, ha⟩ * secMk (N1 V₁) V₁ ⟨b, hb⟩ := by
          rw [← map_mul]; rfl
        rw [this]
        exact (S.map _).mul_mem ha' hb'
      one_mem' := ⟨(N1 V₁).one_mem, by
        have : secMk (N1 V₁) V₁ ⟨1, (N1 V₁).one_mem⟩ = 1 := map_one _
        rw [this]
        exact (S.map _).one_mem⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨(N1 V₁).inv_mem ha, ?_⟩
        have : secMk (N1 V₁) V₁ ⟨a⁻¹, (N1 V₁).inv_mem ha⟩ = (secMk (N1 V₁) V₁ ⟨a, ha⟩)⁻¹ := by
          rw [← map_inv]; rfl
        rw [this]
        exact (S.map _).inv_mem ha' }
  have hUP : conjClosure Vp H ≤ P := by
    refine conjClosure_le fun x hx v hv => ?_
    have hw : secMk (N1 V₁) V₁ ⟨v, hVpN hv⟩ ∈ UT V₁ Vp H :=
      secImg_mono (le_conjClosure Vp H) (secMk_mem_secImg hv)
    have hS := hinv ⟨x, hx⟩ _ (hVS ⟨_, hw⟩ (secMk_mem_secImg hv))
    refine ⟨hUN (Subgroup.subset_closure ⟨x, hx, v, hv, rfl⟩), ⟨_, hS, ?_⟩⟩
    rw [Subgroup.subtype_apply, thetaH_apply]
    exact thetaH_apply_secMk h ⟨x, hx⟩ (hVpN hv)
  rw [eq_top_iff]
  rintro ⟨w, hw⟩ -
  obtain ⟨⟨u, huN⟩, huU, rfl⟩ := mem_secImg.1 hw
  obtain ⟨hg, hm⟩ := hUP huU
  obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.1 hm
  have : s = ⟨secMk (N1 V₁) V₁ ⟨u, huN⟩, hw⟩ := Subtype.ext hse
  rw [← this]
  exact hs

end CFSG.Quasithin.H13.F126
