module

public import CFSG.Quasithin.Background.AutSubConj
public import CFSG.Quasithin.Background.F918H3
public import CFSG.Quasithin.Background.B1MoreIrr

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section AutSubFacts

variable {W : Type} [CommGroup W]

theorem autSub_sup {X Y : Subgroup (MulAut W)} {U : Subgroup W} (h : X ⊔ Y ≤ stabSub U) :
    autSub (X ⊔ Y) U = autSub X U ⊔ autSub Y U := by
  rw [autSub_eq_map_resHomOn le_rfl h, autSub_eq_map_resHomOn (le_sup_left : X ≤ X ⊔ Y) h,
    autSub_eq_map_resHomOn (le_sup_right : Y ≤ X ⊔ Y) h, ← Subgroup.map_sup,
    ← Subgroup.subgroupOf_sup (le_sup_left : X ≤ X ⊔ Y) (le_sup_right : Y ≤ X ⊔ Y)]

theorem conjAutSub_mul (a b : MulAut W) (X : Subgroup (MulAut W)) :
    conjAutSub (a * b) X = conjAutSub a (conjAutSub b X) := by
  ext x
  simp only [mem_conjAutSub_iff, mul_inv_rev, mul_assoc]

theorem autSub_map_conj {X : Subgroup (MulAut W)} {U : Subgroup W} (g : stabSub U) :
    (autSub X U).map (MulAut.conj (resHom U g)).toMonoidHom =
      autSub (conjAutSub (g : MulAut W) X) U :=
  (CFSG.Quasithin.StabLat.autSub_map_conj_eq g.2).symm

theorem autSub_commute {X Y : Subgroup (MulAut W)} {U : Subgroup W}
    (h : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    ∀ a ∈ autSub X U, ∀ b ∈ autSub Y U, a * b = b * a := by
  intro a ha b hb
  obtain ⟨x, hx, rfl⟩ := mem_autSub.mp ha
  obtain ⟨y, hy, rfl⟩ := mem_autSub.mp hb
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (h _ hx _ hy)

theorem fixV_autSub_eq {X : Subgroup (MulAut W)} {U : Subgroup W} (h : X ≤ stabSub U) :
    fixV (autSub X U) = (U ⊓ fixV X).subgroupOf U := by
  apply Subgroup.map_injective U.subtype_injective
  rw [map_subtype_fixV_autSub h, Subgroup.map_subgroupOf_eq_of_le inf_le_left]

theorem irrSec_autSub {Mp : Subgroup (MulAut W)} {V : Subgroup W}
    (hirr : V ∈ IrrPlus Mp (⊤ : Subgroup W)) :
    ∀ J : Subgroup ↥V, fixV (autSub Mp V) ≤ J → (∀ k ∈ autSub Mp V, ∀ w ∈ J, k w ∈ J) →
      J = fixV (autSub Mp V) ∨ J = ⊤ := by
  obtain ⟨hinv, -, -, hirr'⟩ := mem_irrPlus_top_iff.mp hirr
  have hMs : Mp ≤ stabSub V := le_stabSub_of_forall_mem hinv
  rw [fixV_autSub_eq hMs]
  intro J hCJ hJ
  have hJinv : ∀ m ∈ Mp, ∀ w ∈ J.map V.subtype, m w ∈ J.map V.subtype := by
    rintro m hm _ ⟨w, hw, rfl⟩
    refine ⟨resHom V ⟨m, hMs hm⟩ w, hJ _ (mem_autSub.mpr ⟨⟨m, hMs hm⟩, hm, rfl⟩) w hw, ?_⟩
    rw [Subgroup.coe_subtype, resHom_apply]
  have hfix : V ⊓ fixV Mp ≤ J.map V.subtype := by
    intro v hv
    refine ⟨⟨v, hv.1⟩, hCJ ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact hv
  rcases hirr' (J.map V.subtype) hJinv hfix (Subgroup.map_subtype_le J) with h | h
  · left
    ext u
    have e1 : u ∈ J ↔ (u : W) ∈ J.map V.subtype :=
      (Subgroup.mem_map_iff_mem V.subtype_injective).symm
    rw [e1, h, Subgroup.mem_subgroupOf]
  · right
    rw [eq_top_iff]
    intro u _
    have hu : (u : W) ∈ J.map V.subtype := by rw [h]; exact u.2
    exact (Subgroup.mem_map_iff_mem (x := u) V.subtype_injective).mp hu

end AutSubFacts

end CFSG.Quasithin
