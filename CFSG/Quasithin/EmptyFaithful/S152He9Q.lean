module

public import CFSG.Quasithin.EmptyFaithful.S152He9Z
public import CFSG.Quasithin.EmptyFaithful.S152He9H

public section

namespace CFSG.Quasithin.He9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure Ctx15204 (T Mc M H K₁ K₂ : Subgroup G) (π : ↥H →* W5) : Prop where
  y : YCtx T Mc M
  hs : Setting152 T Mc M
  hH : IsHStar T M H
  h1519 : Lemma1519Concl T Mc M
  wr : WrH H T K₁ K₂ π
  hT : IsSylowTwoOf T H
  hE : ∃ (e : G) (he : e ∈ H), e ∈ M ∧ π ⟨e, he⟩ = W5.incl1 W5.c3

namespace Ctx15204

variable {T Mc M H K₁ K₂ : Subgroup G} {π : ↥H →* W5} (c : Ctx15204 T Mc M H K₁ K₂ π)

include c

theorem H_le_Mc : H ≤ Mc := (c.h1519.three H c.hH).1.trans (c.h1519.three H c.hH).2

theorem inf_normalizer_rc : H ⊓ M ≤ Subgroup.normalizer (rcOf Mc M : Set G) := fun _ hx =>
  le_normalizer_pCoreOf 2 (Mc ⊓ M) ⟨c.H_le_Mc hx.1, hx.2⟩

theorem inf_normalizer_Y : H ⊓ M ≤ Subgroup.normalizer (yOf152 T Mc M : Set G) := fun _ hx =>
  c.y.normal hx.2

theorem T_le_normalizer_rc : T ≤ Subgroup.normalizer (rcOf Mc M : Set G) :=
  c.y.data.T_le_normalizer_rc

theorem T_le_normalizer_Y : T ≤ Subgroup.normalizer (yOf152 T Mc M : Set G) :=
  c.y.data.T_le.trans c.y.normal

theorem rc_le_T : rcOf Mc M ≤ T := c.y.data.rc_le_T

theorem rc_le_normalizer₁ : rcOf Mc M ≤ Subgroup.normalizer (K₁ : Set G) := by
  intro r hr
  have hrT : r ∈ T := c.rc_le_T hr
  have hrH : r ∈ H := c.hT.1 hrT
  rw [c.wr.mem_normalizer₁ hrH]
  by_contra hnb
  obtain ⟨e, heH, heM, hπe⟩ := c.hE
  have hmem : e * r * e⁻¹ * r⁻¹ ∈ rcOf Mc M := by
    have h1 : e * r * e⁻¹ ∈ rcOf Mc M :=
      (Subgroup.mem_normalizer_iff.mp (c.inf_normalizer_rc ⟨heH, heM⟩) r).mp hr
    exact (rcOf Mc M).mul_mem h1 ((rcOf Mc M).inv_mem hr)
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (Mc ⊓ M)) ⟨_, hmem⟩
  have hk' : (e * r * e⁻¹ * r⁻¹) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  let eH : ↥H := ⟨e, heH⟩
  let rH : ↥H := ⟨r, hrH⟩
  have hkH : (eH * rH * eH⁻¹ * rH⁻¹) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk')
  have hπe' : π eH = W5.incl1 W5.c3 := hπe
  have h2' : π (eH * rH * eH⁻¹ * rH⁻¹) =
      W5.incl1 W5.c3 * π rH * (W5.incl1 W5.c3)⁻¹ * (π rH)⁻¹ := by
    simp only [map_mul, map_inv]
    rw [hπe']
  have h2 : π (eH * rH * eH⁻¹ * rH⁻¹) ^ 2 ^ k = 1 := by rw [← map_pow, hkH, map_one]
  rw [h2'] at h2
  have h3 := W5.commutator_not_two_element hnb k
  apply h3
  have h4 : (π rH * W5.incl1 W5.c3 * (π rH)⁻¹ * (W5.incl1 W5.c3)⁻¹) =
      (W5.incl1 W5.c3 * π rH * (W5.incl1 W5.c3)⁻¹ * (π rH)⁻¹)⁻¹ := by group
  rw [h4, inv_pow, h2, inv_one]

end Ctx15204

end CFSG.Quasithin.He9
