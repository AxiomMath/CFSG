module

public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.H13.StatementsCh7

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem exists_mul_of_mem_sup {X Y : Subgroup G} (hXY : X ≤ Subgroup.normalizer (Y : Set G))
    {c : G} (hc : c ∈ X ⊔ Y) : ∃ x ∈ X, ∃ y ∈ Y, x * y = c := by
  have hc' : c ∈ ((X ⊔ Y : Subgroup G) : Set G) := hc
  rw [Subgroup.coe_mul_of_left_le_normalizer_right X Y hXY] at hc'
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hc'
  exact ⟨x, hx, y, hy, rfl⟩

omit [Finite G] in
theorem le_normalizer_of_comm {X Y : Subgroup G} (h : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    X ≤ Subgroup.normalizer (Y : Set G) := by
  refine le_trans (fun x hx => ?_) (Subgroup.centralizer_le_normalizer _)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (h x hx y hy).symm

theorem exists_c {W W' A : Subgroup G} {g' : G}
    (hV : IsElemAbelian 2 (conjSubgroup (fsuVM T L I) g'))
    (hVg : conjSubgroup (fsuVM T L I) g' = W ⊔ W') (hWW' : W ⊓ W' = ⊥)
    (hA : A = W ⊓ fsuM T L) (hk : mQuot (conjSubgroup (fsuVM T L I) g')
      (conjSubgroup (fsuVM T L I) g' ⊓ fsuM T L) = 1) {w0 : G} (hw0 : w0 ∈ W)
    (hw0A : w0 ∉ A) (hW'M : ¬ W' ≤ fsuM T L) :
    ∃ c ∈ conjSubgroup (fsuVM T L I) g' ⊓ fsuM T L, c ∉ A ⊔ W' := by
  have hWV : W ≤ conjSubgroup (fsuVM T L I) g' := hVg ▸ le_sup_left
  have hW'V : W' ≤ conjSubgroup (fsuVM T L I) g' := hVg ▸ le_sup_right
  have hAW : A ≤ W := hA ▸ inf_le_left
  have hV2 : IsPGroup 2 ↥(conjSubgroup (fsuVM T L I) g') := B2F.isPGroup_of_isElemAbelian hV
  have hAW'le : A ⊔ W' ≤ conjSubgroup (fsuVM T L I) g' := sup_le (hAW.trans hWV) hW'V
  have hAN : A ≤ Subgroup.normalizer (W' : Set G) := le_normalizer_of_comm fun a ha y hy =>
    B2F.isElemAbelian_comm hV (hWV (hAW ha)) (hW'V hy)
  have hw0' : w0 ∉ A ⊔ W' := by
    intro hw
    obtain ⟨a, ha, w', hw', hew⟩ := exists_mul_of_mem_sup hAN hw
    have hw'W : w' ∈ W := by
      have : w' = a⁻¹ * w0 := by rw [← hew]; group
      rw [this]
      exact W.mul_mem (W.inv_mem (hAW ha)) hw0
    have hw'1 : w' ∈ W ⊓ W' := ⟨hw'W, hw'⟩
    rw [hWW', Subgroup.mem_bot] at hw'1
    rw [hw'1, mul_one] at hew
    exact hw0A (hew ▸ ha)
  by_contra hcon
  push Not at hcon
  have hle : conjSubgroup (fsuVM T L I) g' ⊓ fsuM T L ≤ A ⊔ W' := hcon
  have h1 : mQuot (conjSubgroup (fsuVM T L I) g') (A ⊔ W') ≠ 0 := by
    rw [Ne, mQuot_eq_zero_iff hV2 hAW'le]
    intro heq
    exact hw0' (heq ▸ hWV hw0)
  have h2 := mQuot_add hle hAW'le
  rw [hk] at h2
  have h3 : mQuot (A ⊔ W') (conjSubgroup (fsuVM T L I) g' ⊓ fsuM T L) = 0 := by omega
  rw [mQuot_eq_zero_iff (hV2.to_le hAW'le) hle] at h3
  apply hW'M
  intro x hx
  have : x ∈ A ⊔ W' := Subgroup.mem_sup_right hx
  rw [← h3] at this
  exact this.2

omit [Finite G] in
theorem exists_u {W W' A U1 : Subgroup G} {g' : G}
    (hV : IsElemAbelian 2 (conjSubgroup (fsuVM T L I) g'))
    (hVg : conjSubgroup (fsuVM T L I) g' = W ⊔ W') (hWW' : W ⊓ W' = ⊥)
    (hUW : U1 ≤ Subgroup.normalizer (W : Set G)) (hUW' : U1 ≤ Subgroup.normalizer (W' : Set G))
    (hWU : ∀ w ∈ W, (∀ u ∈ U1, u * w * u⁻¹ = w) → w ∈ A) {c : G}
    (hcV : c ∈ conjSubgroup (fsuVM T L I) g') (hcA : c ∉ A ⊔ W') :
    ∃ u ∈ U1, c * u ≠ u * c := by
  have hWV : W ≤ conjSubgroup (fsuVM T L I) g' := hVg ▸ le_sup_left
  have hW'V : W' ≤ conjSubgroup (fsuVM T L I) g' := hVg ▸ le_sup_right
  have hWN : W ≤ Subgroup.normalizer (W' : Set G) := le_normalizer_of_comm fun a ha y hy =>
    B2F.isElemAbelian_comm hV (hWV ha) (hW'V hy)
  obtain ⟨w, hw, w', hw', rfl⟩ := exists_mul_of_mem_sup hWN (hVg ▸ hcV)
  by_contra hcon
  push Not at hcon
  apply hcA
  refine Subgroup.mul_mem_sup (hWU w hw fun u hu => ?_) hw'
  have hc := hcon u hu
  have huw : u * w * u⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hUW hu) w).mp hw
  have huw' : u * w' * u⁻¹ ∈ W' := (Subgroup.mem_normalizer_iff.mp (hUW' hu) w').mp hw'
  have e : (u * w * u⁻¹) * (u * w' * u⁻¹) = w * w' := by
    calc (u * w * u⁻¹) * (u * w' * u⁻¹) = u * (w * w') * u⁻¹ := by group
      _ = (w * w') * u * u⁻¹ := by rw [← hc]
      _ = w * w' := by group
  have hmem : w⁻¹ * (u * w * u⁻¹) ∈ W ⊓ W' := by
    refine ⟨W.mul_mem (W.inv_mem hw) huw, ?_⟩
    have : w⁻¹ * (u * w * u⁻¹) = w' * (u * w' * u⁻¹)⁻¹ := by
      calc w⁻¹ * (u * w * u⁻¹) = w⁻¹ * ((u * w * u⁻¹) * (u * w' * u⁻¹)) *
            (u * w' * u⁻¹)⁻¹ := by group
        _ = w⁻¹ * (w * w') * (u * w' * u⁻¹)⁻¹ := by rw [e]
        _ = w' * (u * w' * u⁻¹)⁻¹ := by group
    rw [this]
    exact W'.mul_mem hw' (W'.inv_mem huw')
  rw [hWW', Subgroup.mem_bot] at hmem
  calc u * w * u⁻¹ = w * (w⁻¹ * (u * w * u⁻¹)) := by group
    _ = w := by rw [hmem, mul_one]

end CFSG.Quasithin.Vol2.Ch10.SecD
