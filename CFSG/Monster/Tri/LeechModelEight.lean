module

public import CFSG.Monster.Tri.LeechLongMonster
public import CFSG.Monster.Tri.LeechModelShort

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Tri.Leech

open SimpleGraph CFSG.Monster CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.B CFSG.Monster.B.Short CFSG.Monster.GMS CFSG.YGroups

section Generic

variable {G : Type*} [Group G]

@[expose] def TwoBInEight (a z₀ : G) : Prop :=
  ∀ x y t : G, IsConj a x → IsConj a y → IsConj a (x * y) → t * t = 1 → t * x = x * t →
    t * y = y * t → t ≠ 1 → t ≠ x → t ≠ y → t ≠ x * y →
      IsConj z₀ t ∨ IsConj z₀ (t * x) ∨ IsConj z₀ (t * y) ∨ IsConj z₀ (t * x * y)

theorem TwoBInEight.congr {a a' z₀ z₀' : G} (ha : IsConj a a') (hz : IsConj z₀ z₀') :
    TwoBInEight a z₀ ↔ TwoBInEight a' z₀' := by
  have h1 : ∀ w : G, IsConj a w ↔ IsConj a' w := fun w =>
    ⟨fun h => ha.symm.trans h, fun h => ha.trans h⟩
  have h2 : ∀ w : G, IsConj z₀ w ↔ IsConj z₀' w := fun w =>
    ⟨fun h => hz.symm.trans h, fun h => hz.trans h⟩
  unfold TwoBInEight
  simp only [h1, h2]

end Generic

theorem trace_eq_of_isConj_xmatG {w : Gmat} (h : IsConj xmatG w) :
    LinearMap.trace ℚ SpaceB ((w : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) = 276 := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  have h1 : ((c : SpaceB ≃ₗ[ℚ] SpaceB) * xmat * (c : SpaceB ≃ₗ[ℚ] SpaceB)⁻¹ :
      SpaceB ≃ₗ[ℚ] SpaceB) = (w : SpaceB ≃ₗ[ℚ] SpaceB) := congrArg Subtype.val hc
  rw [← h1, CFSG.Monster.B.trace_conj]
  exact trace_xmat

theorem not_isConj_xmatG_of_isConj_tStarG
    {w : Gmat} (hw : IsConj tStarG w) :
    ¬ IsConj xmatG w := by
  intro h
  have h1 := trace_eq_of_mem_shortClass (isConj_tStarG_iff.1 hw)
  rw [trace_eq_of_isConj_xmatG h] at h1
  norm_num at h1

variable {a : Gmat}

theorem isConj_xmatG_of_longTri
    (ha2 : a * a = 1) (ha1 : a ≠ 1) (ha : IsConj tStarG a)
    (hE8 : TwoBInEight a xmatG) {y u : ConjVert a}
    (hxy : (twoAGraph a).Adj (baseVertex a) y) (hxu : (twoAGraph a).Adj (baseVertex a) u)
    (hyu : (twoAGraph a).Adj y u) (hL : permClosure (longTri a) (baseVertex a) y u) :
    IsConj xmatG ((y : Gmat) * (shortMid a (baseVertex a) u : ConjVert a)) := by
  have hcxy : (a : Gmat) * y = y * a := adj_comm ha2 hxy
  have hcxu : (a : Gmat) * u = u * a := adj_comm ha2 hxu
  have hcyu : (y : Gmat) * u = u * y := adj_comm ha2 hyu
  have hlong : longTri a (baseVertex a) y u :=
    (permClosure_longTri_iff ha2 ha1 hxy hyu hxu.symm).1 hL
  have hT : ∀ w : Gmat, IsConj a w → ¬ IsConj xmatG w := fun w hw =>
    not_isConj_xmatG_of_isConj_tStarG (ha.trans hw)
  have hxy' : IsConj a ((a : Gmat) * y) := hxy.2
  have hxu' : IsConj a ((a : Gmat) * u) := hxu.2
  have hyu' : IsConj a ((y : Gmat) * u) := hyu.2
  have h1 := hE8 a y u (IsConj.refl a) y.2 hxy' (conjVert_mul_self ha2 u)
    (hcxu.symm) (hcyu.symm) (conjVert_ne_one ha1 u)
    (fun h => hxu.ne (Subtype.ext h.symm)) (fun h => hyu.ne (Subtype.ext h.symm)) hlong.2.2.2
  have e1 : IsConj a ((u : Gmat) * a) := by rw [← hcxu]; exact hxu'
  have e2 : IsConj a ((u : Gmat) * y) := by rw [← hcyu]; exact hyu'
  have hcomm : (y : Gmat) * ((a : Gmat) * u) = u * a * y := by
    calc (y : Gmat) * (a * u) = y * (u * a) := by rw [hcxu]
      _ = (y * u) * a := by rw [mul_assoc]
      _ = (u * y) * a := by rw [hcyu]
      _ = u * (y * a) := mul_assoc _ _ _
      _ = u * (a * y) := by rw [hcxy]
      _ = u * a * y := (mul_assoc _ _ _).symm
  rw [shortMid_coe hxu, coe_baseVertex a, hcomm]
  rcases h1 with h | h | h | h
  · exact absurd h (hT _ u.2)
  · exact absurd h (hT _ e1)
  · exact absurd h (hT _ e2)
  · exact h

end CFSG.Monster.Tri.Leech
