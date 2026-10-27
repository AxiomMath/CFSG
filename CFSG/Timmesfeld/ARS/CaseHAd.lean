module

public import CFSG.Timmesfeld.ARS.CaseHSharp

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.LieType.Universal CFSG.Timmesfeld.RankOne Matrix NaturalModule FrameSL3 Sec8Field

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseH

variable {A A₀ P P' : Subgroup G}

namespace Setup

variable (S : Setup R A A₀ P P')

abbrev V (_S : Setup R A A₀ P P') : Type _ :=
  ↥P × ↥(shortRoot R P' ⁅A₀, P⁆ A) × ↥(shortRoot R P ⁅A₀, P'⁆ A) × ↥P'

@[expose] noncomputable def ad {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G)) :
    S.V →* S.V :=
  S.prodEquiv.symm.toMonoidHom.comp ((conjNQ S.hyp.root hg).comp S.prodEquiv.toMonoidHom)

@[expose] def lift (v : S.V) : ↥(M R A) :=
  ⟨v.1 * v.2.1 * v.2.2.1 * v.2.2.2, Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (S.P_le_M v.1.2) (U5_le_M v.2.1.2)) (U3_le_M v.2.2.1.2)) (S.P'_le_M v.2.2.2.2)⟩

theorem prodEquiv_eq (v : S.V) : S.prodEquiv v = QuotientGroup.mk (S.lift v) := by
  change S.prodHom v = _
  change toQuot S.P_le_M v.1 * toQuot U5_le_M v.2.1 * toQuot U3_le_M v.2.2.1 *
    toQuot S.P'_le_M v.2.2.2 = _
  simp only [toQuot_apply, ← QuotientGroup.mk_mul]
  rfl

theorem proj_lift (v : S.V) : S.proj (S.lift v) = v := by
  rw [proj_eq_iff]
  exact S.prodEquiv_eq v

theorem proj_conj_eq_ad {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G)) (x : ↥(M R A))
    (hx : g * x * g⁻¹ ∈ M R A) : S.proj ⟨g * x * g⁻¹, hx⟩ = S.ad hg (S.proj x) := by
  change _ = S.prodEquiv.symm (conjNQ S.hyp.root hg (S.prodEquiv (S.prodEquiv.symm
    (QuotientGroup.mk x))))
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem ad_apply {g : G} (hg : g ∈ Subgroup.normalizer (A : Set G)) (v : S.V) :
    S.ad hg v = S.proj ⟨g * S.lift v * g⁻¹,
      conj_mem_M_of_mem_normalizer S.hyp.root hg (S.lift v).2⟩ := by
  rw [S.proj_conj_eq_ad hg, S.proj_lift]

theorem ad_mul {g g' : G} (hg : g ∈ Subgroup.normalizer (A : Set G))
    (hg' : g' ∈ Subgroup.normalizer (A : Set G)) (v : S.V) :
    S.ad (Subgroup.mul_mem _ hg hg') v = S.ad hg (S.ad hg' v) := by
  have hx : g' * ↑(S.lift v) * g'⁻¹ ∈ M R A :=
    conj_mem_M_of_mem_normalizer S.hyp.root hg' (S.lift v).2
  rw [S.ad_apply (Subgroup.mul_mem _ hg hg') v, S.ad_apply hg' v,
    ← S.proj_conj_eq_ad hg ⟨_, hx⟩ (conj_mem_M_of_mem_normalizer S.hyp.root hg hx)]
  congr 1
  apply Subtype.ext
  simp only [_root_.mul_inv_rev]
  group

end Setup

namespace Coords

variable {S : Setup R A A₀ P P'} {F E : Type} [Field F] [Field E] (c : Coords S F E) [CharP E 2]

@[expose] noncomputable def vc (u : F) (w r : E) (v : F) : S.V :=
  (⟨c.x6 u, c.x6_mem u⟩, ⟨c.x5 w, c.x5_mem w⟩, ⟨c.x3 r, c.x3_mem r⟩, ⟨c.x2 v, c.x2_mem v⟩)

theorem vc_add (u u' : F) (w w' r r' : E) (v v' : F) :
    c.vc (u + u') (w + w') (r + r') (v + v') = c.vc u w r v * c.vc u' w' r' v' := by
  simp only [vc, c.x6_add, c.x5_add, c.x3_add, c.x2_add]
  rfl

theorem vc_zero : c.vc 0 0 0 0 = 1 := by
  simp only [vc, c.x6_zero, c.x5_zero, c.x3_zero, c.x2_zero]
  rfl

theorem vc_eq (u : F) (w r : E) (v : F) :
    c.vc u w r v = c.vc u 0 0 0 * c.vc 0 w 0 0 * c.vc 0 0 r 0 * c.vc 0 0 0 v := by
  simp only [← c.vc_add, add_zero, zero_add]

theorem vc_injective [Finite G] {u u' : F} {w w' r r' : E} {v v' : F}
    (h : c.vc u w r v = c.vc u' w' r' v') : u = u' ∧ w = w' ∧ r = r' ∧ v = v' := by
  simp only [vc, Prod.mk.injEq, Subtype.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨c.x6_injective (S.hyp.root.card_eq S.hA S.hP.2.1) h1, c.x5_injective h2,
    c.x3_injective h3, c.x2_injective (S.hyp.root.card_eq S.hA S.hP'.2.1) h4⟩

theorem vc_surjective (v : S.V) : ∃ u w r v', c.vc u w r v' = v := by
  obtain ⟨u, hu⟩ := c.x6_surjective v.1.2
  obtain ⟨w, hw⟩ := c.x5_surjective v.2.1.2
  obtain ⟨r, hr⟩ := c.x3_surjective v.2.2.1.2
  obtain ⟨v', hv'⟩ := c.x2_surjective v.2.2.2.2
  exact ⟨u, w, r, v', Prod.ext (Subtype.ext hu) (Prod.ext (Subtype.ext hw)
    (Prod.ext (Subtype.ext hr) (Subtype.ext hv')))⟩

end Coords

end CaseH

end CFSG.Timmesfeld.ARS
