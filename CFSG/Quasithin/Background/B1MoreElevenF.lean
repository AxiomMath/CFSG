module

public import CFSG.Quasithin.Background.E3Transport
public import CFSG.Quasithin.Background.B1MoreQuot

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace B1Red

section FFTransport

variable {W W' : Type*} [CommGroup W] [CommGroup W']

theorem fixV_map_congr' (φ : W ≃* W') (X : Subgroup (MulAut W)) :
    fixV (X.map (MulAut.congr φ).toMonoidHom) = (fixV X).map φ.toMonoidHom :=
  fixV_map_congr_equiv φ X

theorem isFFModule_map_congr' (φ : W ≃* W') {X : Subgroup (MulAut W)} (h : IsFFModule X) :
    IsFFModule (X.map (MulAut.congr φ).toMonoidHom) :=
  CFSG.Quasithin.E3.isFFModule_map_congr φ h

theorem isFFModule_mono {X Y : Subgroup (MulAut W)} (hXY : X ≤ Y) (h : IsFFModule X) :
    IsFFModule Y := by
  obtain ⟨A, hAX, hrest⟩ := h
  exact ⟨A, hAX.trans hXY, hrest⟩

end FFTransport

section Sec

variable {V : Type*} [CommGroup V]

theorem map_subgroupOf_equivMap (U : Subgroup V) (Ib Cb : Subgroup ↥U) :
    (Cb.subgroupOf Ib).map
        (Subgroup.equivMapOfInjective Ib U.subtype U.subtype_injective).toMonoidHom =
      (Cb.map U.subtype).subgroupOf (Ib.map U.subtype) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(y : ↥U), hy, rfl⟩
  · intro hx
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨y, hyx⟩ := (Subgroup.equivMapOfInjective Ib U.subtype U.subtype_injective).surjective x
    refine ⟨y, ?_, hyx⟩
    have h1 : ((y : ↥U) : V) = ((c : ↥U) : V) := by
      have := congrArg (fun z : ↥(Ib.map U.subtype) => (z : V)) hyx
      simp only [Subgroup.coe_equivMapOfInjective_apply] at this
      exact this.trans hcx.symm
    have : (y : ↥U) = c := U.subtype_injective h1
    show (y : ↥U) ∈ Cb
    rw [this]
    exact hc

@[expose] noncomputable def secEquiv (U : Subgroup V) (Ib Cb : Subgroup ↥U) :
    Sec Ib Cb ≃* Sec (Ib.map U.subtype) (Cb.map U.subtype) :=
  QuotientGroup.congr (Cb.subgroupOf Ib) ((Cb.map U.subtype).subgroupOf (Ib.map U.subtype))
    (Subgroup.equivMapOfInjective Ib U.subtype U.subtype_injective)
    (map_subgroupOf_equivMap U Ib Cb)

theorem secEquiv_mk (U : Subgroup V) (Ib Cb : Subgroup ↥U) (w : ↥Ib) :
    secEquiv U Ib Cb (QuotientGroup.mk w) =
      QuotientGroup.mk (Subgroup.equivMapOfInjective Ib U.subtype U.subtype_injective w) := rfl

theorem mem_autSec_iff {X : Subgroup (MulAut V)} {W U' : Subgroup V} {ψ : MulAut (Sec W U')} :
    ψ ∈ autSec X W U' ↔ ∃ h : stabSub W, (h : MulAut V) ∈ X ∧
      ∃ hU : resHom W h ∈ stabSub (U'.subgroupOf W),
        quotHom (U'.subgroupOf W) ⟨resHom W h, hU⟩ = ψ := by
  unfold autSec
  rw [mem_autQuot]
  constructor
  · rintro ⟨g, hgX, hgψ⟩
    obtain ⟨h, hhX, hhg⟩ := mem_autSub.1 hgX
    have hU : resHom W h ∈ stabSub (U'.subgroupOf W) := by rw [hhg]; exact g.2
    refine ⟨h, hhX, hU, ?_⟩
    have : (⟨resHom W h, hU⟩ : stabSub (U'.subgroupOf W)) = g := Subtype.ext hhg
    rw [this]
    exact hgψ
  · rintro ⟨h, hhX, hU, hψ⟩
    exact ⟨⟨resHom W h, hU⟩, mem_autSub.2 ⟨h, hhX, rfl⟩, hψ⟩

theorem autSec_map_le {X : Subgroup (MulAut V)} {U : Subgroup V} {Ib Cb : Subgroup ↥U}
    (hCI : Cb ≤ Ib) :
    (autSec (autSub X U) Ib Cb).map (MulAut.congr (secEquiv U Ib Cb)).toMonoidHom ≤
      autSec X (Ib.map U.subtype) (Cb.map U.subtype) := by
  rintro _ ⟨ψ, hψ, rfl⟩
  obtain ⟨ĥ, hĥX, hU, hψeq⟩ := mem_autSec_iff.1 hψ
  obtain ⟨h, hhX, hhĥ⟩ := mem_autSub.1 hĥX
  have F1 : ∀ u : ↥U, ((ĥ.1 u : ↥U) : V) = h.1 (u : V) := fun u => by
    have := congrArg (fun φ : MulAut ↥U => ((φ u : ↥U) : V)) hhĥ
    exact this.symm
  have hĥI : ∀ u : ↥U, ĥ.1 u ∈ Ib ↔ u ∈ Ib := ĥ.2
  have F2 : (h : MulAut V) ∈ stabSub (Ib.map U.subtype) := by
    intro v
    constructor
    · intro hv
      have hvU : h.1 v ∈ U := Subgroup.map_subtype_le Ib hv
      have hvU' : v ∈ U := (h.2 v).1 hvU
      obtain ⟨u, rfl⟩ : ∃ u : ↥U, (u : V) = v := ⟨⟨v, hvU'⟩, rfl⟩
      obtain ⟨u', hu', hu'e⟩ := hv
      have : u' = ĥ.1 u := U.subtype_injective (hu'e.trans (F1 u).symm)
      exact ⟨u, (hĥI u).1 (this ▸ hu'), rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨ĥ.1 u, (hĥI u).2 hu, F1 u⟩
  have hĥC : ∀ u : ↥U, u ∈ Ib → (ĥ.1 u ∈ Cb ↔ u ∈ Cb) := fun u hu => hU ⟨u, hu⟩
  have F3 : (h : MulAut V) ∈ stabSub (Cb.map U.subtype) := by
    intro v
    constructor
    · intro hv
      have hvI : h.1 v ∈ Ib.map U.subtype := Subgroup.map_mono hCI hv
      have hvI' : v ∈ Ib.map U.subtype := (F2 v).1 hvI
      obtain ⟨u, hu, rfl⟩ := hvI'
      obtain ⟨c, hc, hce⟩ := hv
      have : c = ĥ.1 u := U.subtype_injective (hce.trans (F1 u).symm)
      exact ⟨u, (hĥC u hu).1 (this ▸ hc), rfl⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨ĥ.1 u, (hĥC u (hCI hu)).2 hu, F1 u⟩
  have hU' : resHom (Ib.map U.subtype) ⟨h.1, F2⟩ ∈
      stabSub ((Cb.map U.subtype).subgroupOf (Ib.map U.subtype)) := fun x => F3 (x : V)
  refine mem_autSec_iff.2 ⟨⟨h.1, F2⟩, hhX, hU', ?_⟩
  ext z
  obtain ⟨z₀, rfl⟩ := (secEquiv U Ib Cb).surjective z
  induction z₀ using QuotientGroup.induction_on with
  | H w =>
    have hR : ((MulAut.congr (secEquiv U Ib Cb)).toMonoidHom ψ)
        ((secEquiv U Ib Cb) (QuotientGroup.mk w)) =
        (secEquiv U Ib Cb) (ψ (QuotientGroup.mk w)) := by
      simp [MulAut.congr_apply]
    rw [hR, ← hψeq]
    exact congrArg QuotientGroup.mk (Subtype.ext (F1 (w : ↥U)).symm)

theorem isFFModule_autSec_of_autSub {X : Subgroup (MulAut V)} {U : Subgroup V}
    {Ib Cb : Subgroup ↥U} (hCI : Cb ≤ Ib) (hFF : IsFFModule (autSec (autSub X U) Ib Cb)) :
    IsFFModule (autSec X (Ib.map U.subtype) (Cb.map U.subtype)) :=
  isFFModule_mono (autSec_map_le hCI) (isFFModule_map_congr' (secEquiv U Ib Cb) hFF)

end Sec

end B1Red

end CFSG.Quasithin
