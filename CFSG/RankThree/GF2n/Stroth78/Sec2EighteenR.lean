module

public import CFSG.RankThree.GF2n.Stroth78.Sec2Eighteen
public import CFSG.RankThree.GF2n.Stroth78.Sec2QaAbelian

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a Module
open CFSG.LargeExtraspecial.Timmesfeld (Qa)

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem two_mul_card_Lbar_mul_card_inf_Za (S : Setting z E F) {a : G}
    (hconj : IsConj z a) (haQ : a ∈ Q z) (haZ : a ∉ ZQ z) (hza : z ∈ QaOf a) :
    2 * Nat.card (Lbar S a) * Nat.card (QaOf a ⊓ Q z : Subgroup G) =
      Nat.card (Rbar S a) * Nat.card (Additive (QbarOf S)) *
        Nat.card (QaOf a ⊓ Q z ⊓ centerIn (QaOf a) : Subgroup G) := by
  have hzaZ : z ∉ centerIn (QaOf a) := z_not_mem_centerIn_Qa S haQ hconj haZ hza
  have hLB := two_mul_card_Lbar_mul_card_inf_Q_eq_card_Qa S hconj hza hzaZ
  have hR := card_Rbar_mul_card_inf_Q_of_mem S hza
  have hZA := card_centerIn_QaOf_eq_card_ZQ S hconj
  have hQc := card_ZQ_mul_card_QbarOf S
  have hAq := card_QaOf_eq S hconj
  have hBZ : (QaOf a ⊓ Q z ⊓ centerIn (QaOf a) : Subgroup G) =
      centerIn (QaOf a) ⊓ Q z := by
    ext x
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨(Subgroup.mem_inf.mp h.1).1, h.2⟩, h.1⟩⟩
  have hBarAdd : Nat.card (Additive (QbarOf S)) = Nat.card (QbarOf S) :=
    Nat.card_congr (Additive.toMul : Additive (QbarOf S) ≃ QbarOf S)
  rw [hBarAdd]
  calc
    2 * Nat.card (Lbar S a) * Nat.card (QaOf a ⊓ Q z : Subgroup G)
        = Nat.card (QaOf a) := hLB
    _ = Nat.card (Q z) := hAq
    _ = Nat.card (ZQ z) * Nat.card (QbarOf S) := hQc.symm
    _ = Nat.card (centerIn (QaOf a)) * Nat.card (QbarOf S) := by rw [hZA]
    _ = (Nat.card (Rbar S a) * Nat.card (centerIn (QaOf a) ⊓ Q z : Subgroup G)) *
          Nat.card (QbarOf S) := by rw [hR]
    _ = Nat.card (Rbar S a) * Nat.card (QbarOf S) *
          Nat.card (QaOf a ⊓ Q z ⊓ centerIn (QaOf a) : Subgroup G) := by
        rw [hBZ]
        ring

theorem card_Lbar_ge_of_width_r (S : Setting z E F) {a : G}
    (hconj : IsConj z a) (haQ : a ∈ Q z) (haZ : a ∉ ZQ z) (hza : z ∈ QaOf a)
    {w r : ℕ} (hw : Nat.card F = 2 ^ (2 * w + 1))
    (hr : Nat.card (Rbar S a) = 2 ^ r) :
    2 ^ (r + w - 1) ≤ Nat.card (Lbar S a) := by
  have hid := two_mul_card_Lbar_mul_card_inf_Za S hconj haQ haZ hza
  obtain ⟨g, hg⟩ := QaOf_eq_map_of_isConj S hconj
  let φ : G ≃* G := MulAut.conj g
  have hg' : QaOf a = (Q z).map φ.toMonoidHom := hg
  let ψ : G ≃* G := φ.symm
  have hcomp : ψ.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id G := by
    ext x
    simp [ψ]
  have hψQ : Q z = (QaOf a).map ψ.toMonoidHom := by
    rw [hg', Subgroup.map_map, hcomp, Subgroup.map_id]
  have hZamap : centerIn (QaOf a) = (ZQ z).map φ.toMonoidHom := by
    have hC : Subgroup.centralizer ((Q z).map φ.toMonoidHom : Set G) =
        (Subgroup.centralizer (Q z : Set G)).map φ.toMonoidHom :=
      (CFSG.Literature.GL52.map_centralizer_subgroup φ (Q z)).symm
    calc
      centerIn (QaOf a) = QaOf a ⊓ Subgroup.centralizer (QaOf a : Set G) := rfl
      _ = (Q z).map φ.toMonoidHom ⊓
            Subgroup.centralizer ((Q z).map φ.toMonoidHom : Set G) := by rw [hg']
      _ = (Q z).map φ.toMonoidHom ⊓
            (Subgroup.centralizer (Q z : Set G)).map φ.toMonoidHom := by rw [hC]
      _ = ((Q z) ⊓ Subgroup.centralizer (Q z : Set G)).map φ.toMonoidHom :=
            (Subgroup.map_inf_eq (Q z) (Subgroup.centralizer (Q z : Set G))
              φ.toMonoidHom φ.injective).symm
      _ = (ZQ z).map φ.toMonoidHom := rfl
  have hZmapψ : (centerIn (QaOf a)).map ψ.toMonoidHom = ZQ z := by
    rw [hZamap, Subgroup.map_map, hcomp, Subgroup.map_id]
  let B' : Subgroup G := (QaOf a ⊓ Q z).map ψ.toMonoidHom
  have hB'def : B' = (QaOf a ⊓ Q z).map ψ.toMonoidHom := rfl
  have hB'le : B' ≤ Q z := by
    rw [hB'def, hψQ]
    exact Subgroup.map_mono inf_le_left
  have hB'card : Nat.card B' = Nat.card (QaOf a ⊓ Q z : Subgroup G) := by
    rw [hB'def]
    exact Subgroup.card_map_of_injective (K := QaOf a ⊓ Q z) (f := ψ.toMonoidHom) ψ.injective
  have hB'Z : B' ⊓ ZQ z =
      (QaOf a ⊓ Q z ⊓ centerIn (QaOf a)).map ψ.toMonoidHom := by
    rw [hB'def,
      Subgroup.map_inf_eq (QaOf a ⊓ Q z) (centerIn (QaOf a)) ψ.toMonoidHom ψ.injective,
      hZmapψ]
  have hB'Zcard : Nat.card (B' ⊓ ZQ z : Subgroup G) =
      Nat.card (QaOf a ⊓ Q z ⊓ centerIn (QaOf a) : Subgroup G) := by
    rw [hB'Z]
    exact Subgroup.card_map_of_injective
      (K := QaOf a ⊓ Q z ⊓ centerIn (QaOf a)) (f := ψ.toMonoidHom) ψ.injective
  have hcommB' : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := by
    intro x hx y hy
    rw [hB'def] at hx hy
    obtain ⟨x0, hx0, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y0, hy0, rfl⟩ := Subgroup.mem_map.mp hy
    rw [← map_mul, ← map_mul, commute_of_mem_QaOf_inf_Q S hconj haZ hx0 hy0]
  have hI := card_QaInterImage_mul_card_inf S B' hB'le
  have hdim : finrank (ZMod 2) (QaInterImage S B') ≤ w :=
    finrank_QaInterImage_le S hcommB' hw
  have hIle : Nat.card (QaInterImage S B') ≤ 2 ^ w := by
    have hcardI : Nat.card (QaInterImage S B') =
        2 ^ finrank (ZMod 2) (QaInterImage S B') := by
      have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := QaInterImage S B')
      rwa [Nat.card_zmod] at h
    rw [hcardI]
    exact Nat.pow_le_pow_right (by norm_num) hdim
  have hBsplit : Nat.card (QaOf a ⊓ Q z : Subgroup G) =
      Nat.card (QaInterImage S B') *
        Nat.card (QaOf a ⊓ Q z ⊓ centerIn (QaOf a) : Subgroup G) := by
    rw [← hB'card, ← hI, hB'Zcard]
  rw [hBsplit] at hid
  have hposZ : 0 < Nat.card (QaOf a ⊓ Q z ⊓ centerIn (QaOf a) : Subgroup G) := Nat.card_pos
  have hkey : 2 * Nat.card (Lbar S a) * Nat.card (QaInterImage S B') =
      Nat.card (Rbar S a) * Nat.card (Additive (QbarOf S)) := by
    refine Nat.mul_right_cancel hposZ ?_
    calc
      2 * Nat.card (Lbar S a) * Nat.card (QaInterImage S B') *
          Nat.card (QaOf a ⊓ Q z ⊓ centerIn (QaOf a) : Subgroup G)
          = 2 * Nat.card (Lbar S a) *
              (Nat.card (QaInterImage S B') *
                Nat.card (QaOf a ⊓ Q z ⊓ centerIn (QaOf a) : Subgroup G)) := by ring
      _ = Nat.card (Rbar S a) * Nat.card (Additive (QbarOf S)) *
            Nat.card (QaOf a ⊓ Q z ⊓ centerIn (QaOf a) : Subgroup G) := hid
  have hQbar : Nat.card (Additive (QbarOf S)) = 2 ^ (2 * w) := card_QbarOf_eq_pow S hw
  have hle : 2 ^ (r + 2 * w) ≤ 2 * Nat.card (Lbar S a) * 2 ^ w := by
    calc
      2 ^ (r + 2 * w) = Nat.card (Rbar S a) * Nat.card (Additive (QbarOf S)) := by
        rw [hr, hQbar, ← pow_add]
      _ = 2 * Nat.card (Lbar S a) * Nat.card (QaInterImage S B') := hkey.symm
      _ ≤ 2 * Nat.card (Lbar S a) * 2 ^ w := Nat.mul_le_mul_left _ hIle
  have h3 : 2 ^ (r + w) ≤ 2 * Nat.card (Lbar S a) := by
    have hsplit : 2 ^ (r + 2 * w) = 2 ^ (r + w) * 2 ^ w := by
      rw [show r + 2 * w = (r + w) + w by ring, pow_add]
    have h2' : 2 ^ (r + w) * 2 ^ w ≤ (2 * Nat.card (Lbar S a)) * 2 ^ w := by
      rwa [hsplit] at hle
    exact Nat.le_of_mul_le_mul_right h2' (pow_pos (by norm_num) w)
  rcases Nat.eq_zero_or_pos (r + w) with h0 | hpos
  · rw [h0, Nat.zero_sub, pow_zero]
    exact Nat.succ_le_of_lt (Nat.card_pos (α := Lbar S a))
  · have hpow : 2 ^ (r + w) = 2 ^ (r + w - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel hpos]
    have h4 : 2 ^ (r + w - 1) * 2 ≤ Nat.card (Lbar S a) * 2 := by
      rw [hpow, mul_comm 2 (Nat.card (Lbar S a))] at h3
      exact h3
    exact Nat.le_of_mul_le_mul_right h4 (by norm_num)

end CFSG.RankThree.GF2n.Stroth78
