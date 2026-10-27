module

public import CFSG.RankThree.GF2n.Stroth78.Sec2Four
public import CFSG.RankThree.GF2n.Stroth78.Sec2FourteenQa2
public import CFSG.RankThree.GF2n.Stroth78.Sec2QaIndex

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a Module
open CFSG.LargeExtraspecial.Timmesfeld (Qa)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem centerIn_QaOf_le_H (S : Setting z E F) {a : G} (hza : z ∈ QaOf a) :
    centerIn (QaOf a) ≤ H z := by
  intro x hx
  obtain ⟨-, hxCent⟩ := Subgroup.mem_inf.mp hx
  rw [H, Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact Subgroup.mem_centralizer_iff.mp hxCent z hza

theorem card_centerIn_QaOf_inf_H (S : Setting z E F) {a : G} (hza : z ∈ QaOf a) :
    Nat.card (centerIn (QaOf a) ⊓ H z : Subgroup G) = Nat.card (centerIn (QaOf a)) := by
  rw [inf_eq_left.mpr (centerIn_QaOf_le_H S hza)]

theorem card_Rbar_mul_card_inf_Q_of_mem (S : Setting z E F) {a : G} (hza : z ∈ QaOf a) :
    Nat.card (Rbar S a) * Nat.card (centerIn (QaOf a) ⊓ Q z : Subgroup G) =
      Nat.card (centerIn (QaOf a)) := by
  rw [← card_centerIn_QaOf_inf_H S hza]
  exact card_Rbar_mul S a

theorem card_QaInterImage_eq_card_map (S : Setting z E F) (A : Subgroup G) (hA : A ≤ Q z) :
    Nat.card (QaInterImage S A) =
      Nat.card ↥(Subgroup.map (mkQbar S) (A.subgroupOf (Q z))) := by
  classical
  let e : ↥(QaInterImage S A) ≃ ↥(Subgroup.map (mkQbar S) (A.subgroupOf (Q z))) := {
    toFun := fun v =>
      ⟨Additive.toMul (v : Additive (QbarOf S)), by
        obtain ⟨y, hyA, hyv⟩ := (mem_QaInterImage_iff S).mp v.2
        exact Subgroup.mem_map.mpr ⟨y, Subgroup.mem_subgroupOf.mpr hyA, hyv⟩⟩
    invFun := fun w =>
      ⟨Additive.ofMul (w : QbarOf S), by
        obtain ⟨y, hy, hyw⟩ := Subgroup.mem_map.mp w.2
        rw [mem_QaInterImage_iff S]
        exact ⟨y, Subgroup.mem_subgroupOf.mp hy, by simpa using hyw⟩⟩
    left_inv := fun v => Subtype.ext (by simp)
    right_inv := fun w => Subtype.ext (by simp) }
  exact Nat.card_congr e

theorem card_map_mkQbar_mul_card_inf (S : Setting z E F) (A : Subgroup G) (hA : A ≤ Q z) :
    Nat.card ↥(Subgroup.map (mkQbar S) (A.subgroupOf (Q z))) *
      Nat.card (A ⊓ ZQ z : Subgroup G) = Nat.card A := by
  let f : ↥A →* QbarOf S := (mkQbar S).comp (Subgroup.inclusion hA)
  have hker : f.ker = (ZQ z).subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    change (QuotientGroup.mk (Subgroup.inclusion hA x) : QbarOf S) = 1 ↔
      x ∈ (ZQ z).subgroupOf A
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    rfl
  have hrange : f.range = Subgroup.map (mkQbar S) (A.subgroupOf (Q z)) := by
    rw [MonoidHom.range_comp, Subgroup.inclusion_range]
  have h := Subgroup.card_ker_mul_card_range f
  rw [hker, hrange, ← Subgroup.inf_subgroupOf_right,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : ZQ z ⊓ A ≤ A)).toEquiv,
    inf_comm, mul_comm] at h
  exact h

theorem card_QaInterImage_mul_card_inf (S : Setting z E F) (A : Subgroup G) (hA : A ≤ Q z) :
    Nat.card (QaInterImage S A) * Nat.card (A ⊓ ZQ z : Subgroup G) = Nat.card A := by
  rw [card_QaInterImage_eq_card_map S A hA]
  exact card_map_mkQbar_mul_card_inf S A hA

theorem card_ZQ_mul_card_QbarOf (S : Setting z E F) :
    Nat.card (ZQ z) * Nat.card (QbarOf S) = Nat.card (Q z) := by
  have h := Subgroup.card_ker_mul_card_of_surjective (f := mkQbar S)
    (QuotientGroup.mk'_surjective ((ZQ z).subgroupOf (Q z)))
  have hker : (mkQbar S).ker = (ZQ z).subgroupOf (Q z) := by
    ext x
    simp only [MonoidHom.mem_ker, mkQbar, QuotientGroup.mk'_apply]
    exact QuotientGroup.eq_one_iff x
  rw [hker] at h
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show ZQ z ≤ Q z from inf_le_left)).toEquiv] at h

theorem card_QbarOf_eq_pow (S : Setting z E F) {w : ℕ}
    (hw : Nat.card F = 2 ^ (2 * w + 1)) :
    Nat.card (Additive (QbarOf S)) = 2 ^ (2 * w) := by
  have h := card_ZQ_mul_card_QbarOf S
  have hQ := Q_card S
  have hZ := ZQ_card S
  have hE : 0 < Nat.card E := Nat.card_pos
  have hpow : 2 ^ (2 * w + 1) = 2 * 2 ^ (2 * w) := by
    rw [pow_succ]
    ring
  have h1 : Nat.card E * (2 * 2 ^ (2 * w)) = Nat.card (Q z) := by
    rw [hQ, hw, hpow]
  have h2 : (Nat.card E * 2) * Nat.card (QbarOf S) = Nat.card (Q z) := by
    rw [← hZ]
    exact h
  have hmain : (Nat.card E * 2) * Nat.card (QbarOf S) =
      (Nat.card E * 2) * 2 ^ (2 * w) := by
    rw [h2, ← h1]
    ring
  have hbar : Nat.card (QbarOf S) = 2 ^ (2 * w) :=
    Nat.mul_left_cancel (Nat.mul_pos hE (by norm_num)) hmain
  calc Nat.card (Additive (QbarOf S)) = Nat.card (QbarOf S) :=
        Nat.card_congr (Additive.toMul : Additive (QbarOf S) ≃ QbarOf S)
    _ = 2 ^ (2 * w) := hbar

theorem two_mul_card_Lbar_mul_card_QaInterImage_of_card_inf (S : Setting z E F) {a : G}
    (hconj : IsConj z a) (haQ : a ∈ Q z) (haZ : a ∉ ZQ z) (hza : z ∈ QaOf a)
    (hcard : Nat.card (ZQ z ⊓ QaOf a : Subgroup G) =
      Nat.card (centerIn (QaOf a) ⊓ Q z : Subgroup G)) :
    2 * Nat.card (Lbar S a) * Nat.card (QaInterImage S (QaOf a ⊓ Q z)) =
      Nat.card (Rbar S a) * Nat.card (Additive (QbarOf S)) := by
  have hzaZ : z ∉ centerIn (QaOf a) := z_not_mem_centerIn_Qa S haQ hconj haZ hza
  have hLB := two_mul_card_Lbar_mul_card_inf_Q_eq_card_Qa S hconj hza hzaZ
  have hI := card_QaInterImage_mul_card_inf S (QaOf a ⊓ Q z) inf_le_right
  have hker : Nat.card (QaOf a ⊓ Q z ⊓ ZQ z : Subgroup G) =
      Nat.card (ZQ z ⊓ QaOf a : Subgroup G) := by
    have h : (QaOf a ⊓ Q z ⊓ ZQ z : Subgroup G) = ZQ z ⊓ QaOf a := by
      ext x
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨⟨h1, -⟩, h3⟩
        exact ⟨h3, h1⟩
      · rintro ⟨h3, h1⟩
        exact ⟨⟨h1, (Subgroup.mem_inf.mp h3).1⟩, h3⟩
    rw [h]
  rw [hker] at hI
  have hR := card_Rbar_mul_card_inf_Q_of_mem S hza
  have hZA : Nat.card (centerIn (QaOf a)) = Nat.card (ZQ z) :=
    card_centerIn_QaOf_eq_card_ZQ S hconj
  have hQc := card_ZQ_mul_card_QbarOf S
  have hAq := card_QaOf_eq S hconj
  have hLHS : (2 * Nat.card (Lbar S a) * Nat.card (QaInterImage S (QaOf a ⊓ Q z))) *
      Nat.card (ZQ z ⊓ QaOf a : Subgroup G) = Nat.card (QaOf a) := by
    rw [← hLB, ← hI]
    ring
  have hRHS : (Nat.card (Rbar S a) * Nat.card (Additive (QbarOf S))) *
      Nat.card (ZQ z ⊓ QaOf a : Subgroup G) = Nat.card (QaOf a) := by
    have eX : Nat.card (ZQ z ⊓ QaOf a : Subgroup G) =
        Nat.card (centerIn (QaOf a) ⊓ Q z : Subgroup G) := hcard
    have e1 : Nat.card (Rbar S a) * Nat.card (Additive (QbarOf S)) *
        Nat.card (ZQ z ⊓ QaOf a : Subgroup G) =
        Nat.card (Rbar S a) * Nat.card (ZQ z ⊓ QaOf a : Subgroup G) *
          Nat.card (Additive (QbarOf S)) := by ring
    have e2 : Nat.card (Rbar S a) * Nat.card (ZQ z ⊓ QaOf a : Subgroup G) *
        Nat.card (Additive (QbarOf S)) =
        Nat.card (Rbar S a) * Nat.card (centerIn (QaOf a) ⊓ Q z : Subgroup G) *
          Nat.card (Additive (QbarOf S)) := by rw [eX]
    have e3 : Nat.card (Rbar S a) * Nat.card (centerIn (QaOf a) ⊓ Q z : Subgroup G) *
        Nat.card (Additive (QbarOf S)) =
        Nat.card (centerIn (QaOf a)) * Nat.card (Additive (QbarOf S)) := by rw [hR]
    have e4 : Nat.card (centerIn (QaOf a)) * Nat.card (Additive (QbarOf S)) =
        Nat.card (QaOf a) := by
      rw [hZA, Nat.card_congr (Additive.toMul : Additive (QbarOf S) ≃ QbarOf S), hQc, hAq]
    exact e1.trans (e2.trans (e3.trans e4))
  have hpos : 0 < Nat.card (ZQ z ⊓ QaOf a : Subgroup G) := Nat.card_pos
  exact Nat.mul_right_cancel hpos (hLHS.trans hRHS.symm)

end CFSG.RankThree.GF2n.Stroth78
