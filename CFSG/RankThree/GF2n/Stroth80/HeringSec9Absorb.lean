module

public import CFSG.RankThree.GF2n.Stroth80.Sec33Card

public section

namespace CFSG.RankThree.GF2n.Stroth80.HS9

theorem eq_of_two_power_index {G : Type} [Group G] [Finite G] {R X Y D Q : Subgroup G}
    (hXR : X ≤ R) (hYR : Y ≤ R) (hXY : X ⊔ Y = R) (hQ : X ⊓ Y = Q)
    (hXnorm : R ≤ Subgroup.normalizer (X : Set G)) (hYnorm : R ≤ Subgroup.normalizer (Y : Set G))
    (hDR : D ≤ R) (hDnorm : R ≤ Subgroup.normalizer (D : Set G)) (hXD : X ≤ D)
    (hsimple : ∃ _ : (Q.subgroupOf Y).Normal, IsSimpleGroup (↥Y ⧸ Q.subgroupOf Y))
    (hnot2 : ¬ ∃ k : ℕ, Q.relIndex Y = 2 ^ k) (hD2 : ∃ k : ℕ, X.relIndex D = 2 ^ k) :
    D = X := by
  obtain ⟨hNQ, hsim⟩ := hsimple
  have hYX : Y ≤ Subgroup.normalizer (X : Set G) := hYR.trans hXnorm
  have hXYn : X ≤ Subgroup.normalizer (Y : Set G) := hXR.trans hYnorm
  have hYD : Y ≤ Subgroup.normalizer (D : Set G) := hYR.trans hDnorm
  have hQX : Q ≤ X := by rw [← hQ]; exact inf_le_left
  have hQY : Q ≤ Y := by rw [← hQ]; exact inf_le_right
  have hQD : Q ≤ D := hQX.trans hXD
  have hdec : ∀ {r : G}, r ∈ R → ∃ x ∈ X, ∃ y ∈ Y, x * y = r := by
    intro r hr
    have hr' : r ∈ (↑(X ⊔ Y) : Set G) := by rw [hXY]; exact hr
    rw [Subgroup.coe_mul_of_left_le_normalizer_right X Y hXYn] at hr'
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.mp hr'
    exact ⟨x, hx, y, hy, hxy⟩
  have hN : ((D.subgroupOf Y).map (QuotientGroup.mk' (Q.subgroupOf Y))).Normal :=
    Subgroup.Normal.map (Subgroup.normal_subgroupOf_of_le_normalizer hYD) _
      (QuotientGroup.mk'_surjective _)
  rcases Subgroup.Normal.eq_bot_or_eq_top
      ((D.subgroupOf Y).map (QuotientGroup.mk' (Q.subgroupOf Y))) with h0 | h0
  ·
    have hDQ : ∀ y : Y, (y : G) ∈ D → (y : G) ∈ Q := by
      intro y hy
      have hmem : QuotientGroup.mk' (Q.subgroupOf Y) y ∈
          (D.subgroupOf Y).map (QuotientGroup.mk' (Q.subgroupOf Y)) :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hy)
      rw [h0, Subgroup.mem_bot, QuotientGroup.mk'_apply] at hmem
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff y).mp hmem)
    refine le_antisymm ?_ hXD
    intro d hd
    obtain ⟨x, hx, y, hy, hxy⟩ := hdec (hDR hd)
    have hyD : y ∈ D := by
      have h1 : x⁻¹ * d ∈ D := D.mul_mem (D.inv_mem (hXD hx)) hd
      rwa [← hxy, inv_mul_cancel_left] at h1
    have hyQ : y ∈ Q := hDQ ⟨y, hy⟩ hyD
    rw [← hxy]
    exact X.mul_mem hx (hQX hyQ)
  ·
    exfalso
    have hYD' : Y ≤ D := by
      intro y hy
      have hmem : QuotientGroup.mk' (Q.subgroupOf Y) (⟨y, hy⟩ : Y) ∈
          (D.subgroupOf Y).map (QuotientGroup.mk' (Q.subgroupOf Y)) := by
        rw [h0]
        exact Subgroup.mem_top _
      obtain ⟨d, hd, hdy⟩ := Subgroup.mem_map.mp hmem
      have hdD : (d : G) ∈ D := Subgroup.mem_subgroupOf.mp hd
      simp only [QuotientGroup.mk'_apply] at hdy
      have hq : (d⁻¹ * ⟨y, hy⟩ : Y) ∈ Q.subgroupOf Y := QuotientGroup.eq.mp hdy
      have hq' : ((d⁻¹ * ⟨y, hy⟩ : Y) : G) ∈ Q := Subgroup.mem_subgroupOf.mp hq
      have hyeq : y = (d : G) * ((d⁻¹ * ⟨y, hy⟩ : Y) : G) := by
        simp
      rw [hyeq]
      exact D.mul_mem hdD (hQD hq')
    have hRD : R ≤ D := by
      intro r hr
      obtain ⟨x, hx, y, hy, hxy⟩ := hdec hr
      rw [← hxy]
      exact D.mul_mem (hXD hx) (hYD' hy)
    have hDR' : D = R := le_antisymm hDR hRD
    have hrel : X.relIndex R = Q.relIndex Y := by
      have h1 := Subgroup.relIndex_mul_card (H := X) (K := R)
      have h2 := Subgroup.relIndex_mul_card (H := Q) (K := Y)
      rw [inf_eq_left.mpr hXR] at h1
      rw [inf_eq_left.mpr hQY] at h2
      have hprod := card_sup_mul_card_inf_of_le_normalizer hYX
      rw [hXY, hQ] at hprod
      have hpos : 0 < Nat.card X * Nat.card Q := mul_pos Nat.card_pos Nat.card_pos
      refine Nat.eq_of_mul_eq_mul_right hpos ?_
      calc X.relIndex R * (Nat.card X * Nat.card Q)
          = (X.relIndex R * Nat.card X) * Nat.card Q := by ring
        _ = Nat.card R * Nat.card Q := by rw [h1]
        _ = Nat.card X * Nat.card Y := hprod
        _ = Nat.card X * (Q.relIndex Y * Nat.card Q) := by rw [h2]
        _ = Q.relIndex Y * (Nat.card X * Nat.card Q) := by ring
    obtain ⟨k, hk⟩ := hD2
    rw [hDR', hrel] at hk
    exact hnot2 ⟨k, hk⟩

end CFSG.RankThree.GF2n.Stroth80.HS9
