module

public import CFSG.Quasithin.Background.A1cModuleDefs
public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Quasithin Subgroup

variable {V : Type*} [CommGroup V]

@[expose] def restrictAut (U : Subgroup V) (l : MulAut V) (h1 : ∀ u ∈ U, l u ∈ U)
    (h2 : ∀ u ∈ U, l⁻¹ u ∈ U) : MulAut ↥U where
  toFun u := ⟨l (u : V), h1 u u.2⟩
  invFun u := ⟨l⁻¹ (u : V), h2 u u.2⟩
  left_inv u := Subtype.ext (by simp)
  right_inv u := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (map_mul l (x : V) (y : V))

@[expose] def resHom (L : Subgroup (MulAut V)) (U : Subgroup V) (hU : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) :
    ↥L →* MulAut ↥U where
  toFun l := restrictAut U (l : MulAut V) (hU l l.2) (hU (l : MulAut V)⁻¹ (inv_mem l.2))
  map_one' := by
    ext u
    rfl
  map_mul' a b := by
    ext u
    rfl

theorem coe_resHom_apply (L : Subgroup (MulAut V)) (U : Subgroup V)
    (hU : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U) (l : ↥L) (u : ↥U) :
    (resHom L U hU l u : V) = (l : MulAut V) (u : V) := rfl

section Restrict

variable {L : Subgroup (MulAut V)} {U : Subgroup V} (hU : ∀ l ∈ L, ∀ u ∈ U, l u ∈ U)

theorem sq_eq_one_of_subgroup (hV2 : ∀ v : V, v ^ 2 = 1) (u : ↥U) : u ^ 2 = 1 :=
  Subtype.ext (by rw [SubgroupClass.coe_pow, OneMemClass.coe_one, hV2])

theorem subgroupOf_le_fixV_resHom_range {Z : Subgroup V} (hZ : Z ≤ fixV L) :
    Z.subgroupOf U ≤ fixV (resHom L U hU).range := by
  intro z hz x hx
  obtain ⟨l, rfl⟩ := hx
  apply Subtype.ext
  rw [coe_resHom_apply]
  exact hZ (mem_subgroupOf.1 hz) _ l.2

theorem commV_resHom_range (hcomm : XMod.commOf ↥L U = U) :
    commV (resHom L U hU).range = ⊤ := by
  have hle : XMod.commOf ↥L U ≤ (commV (resHom L U hU).range).map U.subtype := by
    refine (closure_le _).2 ?_
    rintro _ ⟨a, x, hx, rfl⟩
    refine ⟨resHom L U hU a ⟨x, hx⟩ * (⟨x, hx⟩ : ↥U)⁻¹,
      subset_closure ⟨_, ⟨a, rfl⟩, ⟨x, hx⟩, rfl⟩, ?_⟩
    rfl
  rw [hcomm] at hle
  rw [eq_top_iff]
  intro u _
  obtain ⟨w, hw, hwu⟩ := hle u.2
  rw [show w = u from Subtype.ext hwu] at hw
  exact hw

theorem realizes_resHom_range (D : FFModel) {Z : Subgroup V} (h : D.Realizes L U Z) :
    D.Realizes (resHom L U hU).range ⊤ (Z.subgroupOf U) := by
  obtain ⟨π, hπs, -, hks, -, hZinv, hsec, hker, β, hβs, hβk, hβe⟩ := h
  refine ⟨(resHom L U hU).rangeRestrict.comp π,
    (MonoidHom.rangeRestrict_surjective _).comp hπs, le_top, hks, fun _ _ _ => mem_top _,
    fun x z hz => ?_, hsec, hker, β.comp (⊤ : Subgroup ↥U).subtype, fun q => ?_,
    fun u => hβk u, fun γ u m hu hm hum => hβe γ u m (hU _ (π γ).2 _ (u : ↥U).2) hm hum⟩
  · obtain ⟨l, hl⟩ := x.2
    rw [mem_subgroupOf, ← hl, coe_resHom_apply]
    exact hZinv l _ (mem_subgroupOf.1 hz)
  · obtain ⟨u, rfl⟩ := hβs q
    exact ⟨⟨u, mem_top u⟩, rfl⟩

end Restrict

theorem eq_bot_of_restrict (D : FFModel)
    (hD : ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
      ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W), Z ≤ fixV H → commV H = ⊤ →
        D.Realizes H ⊤ Z → Z = ⊥)
    {V : Type} [CommGroup V] [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)}
    (hI : commV L ∈ IrrPlus L ⊤) (h : D.Realizes L (commV L) (fixV L ⊓ commV L)) :
    fixV L ⊓ commV L = ⊥ := by
  have hU : ∀ l ∈ L, ∀ u ∈ commV L, l u ∈ commV L := fun l hl u hu => hI.2.1 ⟨l, hl⟩ u hu
  have h' := hD ↥(commV L) (sq_eq_one_of_subgroup hV2) _ _
    (subgroupOf_le_fixV_resHom_range hU inf_le_left) (commV_resHom_range hU hI.2.2.1)
    (realizes_resHom_range hU D h)
  rw [eq_bot_iff]
  intro z hz
  have hz' : (⟨z, hz.2⟩ : ↥(commV L)) ∈ (fixV L ⊓ commV L).subgroupOf (commV L) :=
    mem_subgroupOf.2 hz
  rw [h', mem_bot] at hz'
  exact mem_bot.2 (congrArg Subtype.val hz')

theorem card_le_of_restrict (D : FFModel) {c : ℕ}
    (hD : ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
      ∀ (H : Subgroup (MulAut W)) (Z : Subgroup W), Z ≤ fixV H → commV H = ⊤ →
        D.Realizes H ⊤ Z → Nat.card Z ≤ c)
    {V : Type} [CommGroup V] [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) {L : Subgroup (MulAut V)}
    (hI : commV L ∈ IrrPlus L ⊤) (h : D.Realizes L (commV L) (fixV L ⊓ commV L)) :
    Nat.card ↥(fixV L ⊓ commV L) ≤ c := by
  have hU : ∀ l ∈ L, ∀ u ∈ commV L, l u ∈ commV L := fun l hl u hu => hI.2.1 ⟨l, hl⟩ u hu
  have h' := hD ↥(commV L) (sq_eq_one_of_subgroup hV2) _ _
    (subgroupOf_le_fixV_resHom_range hU inf_le_left) (commV_resHom_range hU hI.2.2.1)
    (realizes_resHom_range hU D h)
  rwa [Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv] at h'

end CFSG.Quasithin.H13.VolI
