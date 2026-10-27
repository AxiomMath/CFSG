module

public import CFSG.RankThree.GF2n.Stroth78.Sec3Setup
public import CFSG.RankThree.GF2n.Stroth78.ConjAction

import CFSG.RankThree.GF2n.Stroth78.Sec2Eighteen
import CFSG.RankThree.GF2n.Stroth78.Sec2Eleven
import CFSG.RankThree.GF2n.Stroth78.Sec2FourIFamily
import CFSG.RankThree.GF2n.Stroth78.Sec2SixteenReverse

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

noncomputable def zqCenterMulEquiv (z : G) :
    ↥(ZQ z) ≃* ↥(Subgroup.center ↥(Q z)) :=
  (Subgroup.subgroupOfEquivOfLe (show ZQ z ≤ Q z from inf_le_left)).symm.trans
    (MulEquiv.subgroupCongr (ZQ_subgroupOf_eq_center z))

noncomputable def conjAutZQ (S : Setting z E F) : ↥(H z) →* MulAut ↥(ZQ z) where
  toFun h :=
    let e := zqCenterMulEquiv z
    (e.trans (((MulAut.characteristic (Subgroup.center ↥(Q z))) (conjAutQ S h)))).trans e.symm
  map_one' := by
    ext v
    simp [zqCenterMulEquiv, conjAutQ_one]
  map_mul' := by
    intro h h'
    ext v
    simp [zqCenterMulEquiv, conjAutQ_mul, MulAut.mul_apply]

theorem conjAutZQ_apply (S : Setting z E F) (h : ↥(H z)) (v : ↥(ZQ z)) :
    ((conjAutZQ S h v : ↥(ZQ z)) : G) = (h : G) * (v : G) * (h : G)⁻¹ := by
  simp [conjAutZQ, zqCenterMulEquiv, Subgroup.subgroupOfEquivOfLe,
    MulAut.characteristic_apply_apply_coe, conjAutQ_apply]

theorem conjAutZQ_eq_one_of_mem_Q (S : Setting z E F) {h : ↥(H z)}
    (hh : h ∈ (Q z).subgroupOf (H z)) : conjAutZQ S h = 1 := by
  have hhQ : (h : G) ∈ Q z := Subgroup.mem_subgroupOf.mp hh
  ext v
  rw [conjAutZQ_apply, MulAut.one_apply]
  have hv : (v : G) ∈ ZQ z := v.2
  have hcomm : (v : G) * (h : G) = (h : G) * (v : G) :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hv).2 (h : G) hhQ).symm
  rw [← hcomm]
  group

noncomputable def rhoZ (S : Setting z E F) : Hbar z →* MulAut ↥(ZQ z) :=
  QuotientGroup.lift ((Q z).subgroupOf (H z)) (conjAutZQ S)
    (fun _ hh => MonoidHom.mem_ker.mpr (conjAutZQ_eq_one_of_mem_Q S hh))

theorem rhoZ_mk (S : Setting z E F) (h : ↥(H z)) (v : ↥(ZQ z)) :
    ((rhoZ S (QuotientGroup.mk h) v : ↥(ZQ z)) : G) =
      (h : G) * (v : G) * (h : G)⁻¹ := by
  rw [rhoZ, QuotientGroup.lift_mk]
  exact conjAutZQ_apply S h v

theorem ZQ_mul_self (S : Setting z E F) (u : ↥(ZQ z)) : u * u = 1 := by
  apply Subtype.ext
  simpa [pow_two] using (isElemAbelian_ZQ S).2 (u : G) u.2

theorem card_centerIn_QaOf_inf_Q_eq_card_ZQ_inf_QaOf (S : Setting z E F) {a : G}
    (haQ : a ∈ Q z) (hconj : IsConj z a) (haZ : a ∉ ZQ z) (hza : z ∈ QaOf a) :
    Nat.card (centerIn (QaOf a) ⊓ Q z : Subgroup G) =
      Nat.card ↥((ZQ z).subgroupOf (QaOf a)) := by
  obtain ⟨g, hgQaz, hga⟩ := exists_conj_eq_z_of_mem_QaOf_mul_z S haQ hconj haZ hza
  have hgz : g * z * g⁻¹ = a := conj_z_eq_of_conj_a_eq S haQ hconj haZ hgQaz hga
  let φ : G ≃* G := MulAut.conj g
  let ψ : G ≃* G := φ.symm
  have hQmap : (Q z).map φ.toMonoidHom = QaOf a :=
    map_conj_Q_eq_QaOf S haQ hconj haZ hgQaz hga
  have hQamap : (QaOf a).map φ.toMonoidHom = Q z := map_conj_QaOf_eq_Q hga
  have hZamap : centerIn (QaOf a) = (ZQ z).map φ.toMonoidHom :=
    centerIn_QaOf_eq_map_of_conj_eq S hgz
  have hcomp : ψ.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id G := by
    ext x
    simp [ψ]
  have hψQ : (Q z).map ψ.toMonoidHom = QaOf a := by
    rw [← hQamap, Subgroup.map_map, hcomp, Subgroup.map_id]
  have hψQa : (QaOf a).map ψ.toMonoidHom = Q z := by
    rw [← hQmap, Subgroup.map_map, hcomp, Subgroup.map_id]
  have hZmapψ : (centerIn (QaOf a)).map ψ.toMonoidHom = ZQ z := by
    rw [hZamap, Subgroup.map_map, hcomp, Subgroup.map_id]
  have hmap : (centerIn (QaOf a) ⊓ Q z).map ψ.toMonoidHom = ZQ z ⊓ QaOf a := by
    rw [Subgroup.map_inf_eq _ _ _ ψ.injective, hZmapψ, hψQ]
  have hcard : Nat.card (ZQ z ⊓ QaOf a : Subgroup G) =
      Nat.card (centerIn (QaOf a) ⊓ Q z : Subgroup G) := by
    rw [← hmap]
    exact Subgroup.card_map_of_injective (K := centerIn (QaOf a) ⊓ Q z)
      (f := ψ.toMonoidHom) ψ.injective
  rw [← hcard, ← Subgroup.inf_subgroupOf_right (ZQ z) (QaOf a)]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (inf_le_right : ZQ z ⊓ QaOf a ≤ QaOf a)).toEquiv).symm

theorem card_ZQ_eq (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w) :
    Nat.card ↥(ZQ z) = Nat.card ↥(Rbar S a) *
      Nat.card ↥((ZQ z).subgroupOf (QaOf a)) := by
  have hR := card_Rbar_mul_card_inf_Q_of_mem S h.mem_Qa
  have hZa := card_centerIn_QaOf_eq_card_ZQ S h.isConj
  have hrad := card_centerIn_QaOf_inf_Q_eq_card_ZQ_inf_QaOf S h.mem_Q h.isConj
    h.not_mem_ZQ h.mem_Qa
  rw [hrad, hZa] at hR
  exact hR.symm

theorem rhoZ_eq_self_of_mem_inf_QaOf (S : Setting z E F) {a : G} {α : Hbar z}
    (hα : α ∈ Rbar S a) {x : ↥(ZQ z)} (hx : (x : G) ∈ QaOf a) :
    rhoZ S α x = x := by
  rw [← map_R0_eq_Rbar S a] at hα
  obtain ⟨r, hr, hrα⟩ := Subgroup.mem_map.mp hα
  have hrZ : (r : G) ∈ centerIn (QaOf a) :=
    (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hr)).1
  rw [← hrα, QuotientGroup.mk'_apply]
  apply Subtype.ext
  rw [rhoZ_mk]
  have hcomm : (r : G) * (x : G) = (x : G) * (r : G) :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hrZ).2 (x : G) hx).symm
  rw [hcomm]
  group

theorem rhoZ_diff_eq_or (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (hR : Nat.card ↥(Rbar S a) ≤ 2) {α : Hbar z} (hα : α ∈ Rbar S a) :
    ∃ c : ↥(ZQ z), ∀ u : ↥(ZQ z),
      rhoZ S α u = u ∨ rhoZ S α u = u * c := by
  classical
  let K : Subgroup ↥(ZQ z) := (ZQ z ⊓ QaOf a).subgroupOf (ZQ z)
  have hKcard : Nat.card ↥K =
      Nat.card (ZQ z ⊓ QaOf a : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : ZQ z ⊓ QaOf a ≤ ZQ z)).toEquiv
  have hsubcard : Nat.card (ZQ z ⊓ QaOf a : Subgroup G) =
      Nat.card ↥((ZQ z).subgroupOf (QaOf a)) := by
    rw [← Subgroup.inf_subgroupOf_right (ZQ z) (QaOf a)]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_right : ZQ z ⊓ QaOf a ≤ QaOf a)).toEquiv).symm
  have hKindex : K.index ≤ 2 := by
    have hmul := Subgroup.card_mul_index K
    rw [hKcard, hsubcard, card_ZQ_eq S h] at hmul
    rw [Nat.mul_comm (Nat.card ↥(Rbar S a))
      (Nat.card ↥((ZQ z).subgroupOf (QaOf a)))] at hmul
    have hidx : K.index = Nat.card ↥(Rbar S a) :=
      Nat.mul_left_cancel Nat.card_pos hmul
    exact hidx.trans_le hR
  have hfix : ∀ k : ↥(ZQ z), k ∈ K → rhoZ S α k = k := by
    intro k hk
    exact rhoZ_eq_self_of_mem_inf_QaOf S hα (Subgroup.mem_subgroupOf.mp hk).2
  have hcomm : ∀ x y : ↥(ZQ z), x * y = y * x := fun x y =>
    Subtype.ext (IsElemAbelian.comm (isElemAbelian_ZQ S) x.2 y.2)
  by_cases htop : K = ⊤
  · refine ⟨1, fun u => Or.inl ?_⟩
    exact hfix u (by rw [htop]; exact Subgroup.mem_top u)
  · have hidx : K.index = 2 := by
      have hne : K.index ≠ 1 := fun h1 => htop (Subgroup.index_eq_one.mp h1)
      have hpos : 0 < K.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      omega
    obtain ⟨t, ht⟩ := Subgroup.index_dvd_two_iff'.mp (show K.index ∣ 2 by rw [hidx])
    refine ⟨rhoZ S α t⁻¹ * t, fun u => ?_⟩
    rcases ht u with htu | hu
    · right
      calc
        rhoZ S α u = rhoZ S α (t⁻¹ * (t * u)) := by rw [inv_mul_cancel_left]
        _ = rhoZ S α t⁻¹ * rhoZ S α (t * u) := map_mul _ _ _
        _ = rhoZ S α t⁻¹ * (t * u) := by rw [hfix (t * u) htu]
        _ = (rhoZ S α t⁻¹ * t) * u := by group
        _ = u * (rhoZ S α t⁻¹ * t) := hcomm _ _
    · exact Or.inl (hfix u hu)

theorem rhoZ_conj_apply (S : Setting z E F) (x α : Hbar z) (u : ↥(ZQ z)) :
    rhoZ S (x * α * x⁻¹) u = rhoZ S x (rhoZ S α (rhoZ S x⁻¹ u)) := by
  rw [map_mul, map_mul, map_inv]
  rfl

theorem rhoZ_transvection (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (hR : Nat.card ↥(Rbar S a) ≤ 2)
    {α : Hbar z} (hα : α ∈ Rbar S a) (x : Hbar z) :
    ∃ c : ↥(ZQ z), ∀ u : ↥(ZQ z),
      rhoZ S (x * α * x⁻¹) u = u ∨
      rhoZ S (x * α * x⁻¹) u = u * c := by
  obtain ⟨c0, hc0⟩ := rhoZ_diff_eq_or S h hR hα
  refine ⟨rhoZ S x c0, fun u => ?_⟩
  let v : ↥(ZQ z) := rhoZ S x⁻¹ u
  have hv : rhoZ S x v = u := by
    dsimp [v]
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  rcases hc0 v with hv0 | hv0
  · left
    rw [rhoZ_conj_apply, hv0, hv]
  · right
    rw [rhoZ_conj_apply, hv0, map_mul, hv]

end CFSG.RankThree.GF2n.Stroth78
