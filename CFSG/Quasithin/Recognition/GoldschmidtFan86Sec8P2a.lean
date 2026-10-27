module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2b
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2V1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F87Phi

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem prodFive_single {H : Type*} [Group H] (f : Fin 5 → H) (s : Fin 5)
    (h : ∀ r, r ≠ s → f r = 1) : prodFive f = f s := by
  fin_cases s <;> simp [prodFive, h]

theorem fcomm_inv_mul_of_comm {H : Type*} [Group H] {g₁ g₂ z : H} (h : g₁ * z = z * g₁) :
    fcomm (g₁⁻¹ * g₂) z = fcomm g₂ z := by
  have h1 : g₁ * z⁻¹ = z⁻¹ * g₁ := (Commute.inv_right (show Commute g₁ z from h)).eq
  have h' : g₁ * z⁻¹ * g₁⁻¹ = z⁻¹ := by rw [h1]; group
  unfold fcomm
  calc (g₁⁻¹ * g₂)⁻¹ * z⁻¹ * (g₁⁻¹ * g₂) * z = g₂⁻¹ * (g₁ * z⁻¹ * g₁⁻¹) * g₂ * z := by group
    _ = g₂⁻¹ * z⁻¹ * g₂ * z := by rw [h']

theorem fan_8_3a {F : FanTree Γ G} {L : ZLab Γ G} (h7 : Fan7 F L) (h81 : Fan81 F L)
    (h82 : Fan82a F L) (h512 : Fan512 F L) : Fan83a F L := by
  classical
  intro α D δ' hY
  have hα : valence Γ α = 5 := D.val
  have h71c : Fan71c F L := h7.2.2.1
  have h83b := fan_8_3b h7 h81 h512
  have hyK : ∀ k, D.y δ' k ∈ nbrStab Γ G α := D.y_mem_nbrStab' F h71c h81 hY
  apply le_antisymm
  · set H := Subgroup.closure (Set.range (D.y δ')) ⊔ (L.zGroup 2 α ⊔ D.calpha) with hH
    have hbase : ballStab Γ G 2 α ≤ H := by
      rw [(F87.fan73b_dset h7 D).1]
      exact le_sup_right
    have hy_mem : ∀ k, D.y δ' k ∈ H := fun k =>
      Subgroup.mem_sup_left (Subgroup.subset_closure ⟨k, rfl⟩)
    have hΘ : ∀ w ∈ nbrStab Γ G α, ∀ r, F87.InZ L α (fcomm w (L.z (D.alpha r))) :=
      fun w hw r => F87.fcomm_z_mem h7 h512 hα hw (by rw [D.dist_start_alpha F r])
        (D.valence_alpha F r)
    have key : ∀ n : ℕ, ∀ w ∈ nbrStab Γ G α,
        (Finset.univ.filter (fun r => fcomm w (L.z (D.alpha r)) ≠ 1)).card ≤ n → w ∈ H := by
      intro n
      induction n with
      | zero =>
        intro w hw hc
        have h0 : ∀ r, fcomm w (L.z (D.alpha r)) = 1 := by
          intro r
          by_contra hr
          have hmem : r ∈ Finset.univ.filter (fun r => fcomm w (L.z (D.alpha r)) ≠ 1) := by
            simp [hr]
          have := Finset.card_pos.2 ⟨r, hmem⟩
          omega
        exact hbase (F87.mem_ballStab_of_fcomm h7 D hw h0)
      | succ n ih =>
        intro w hw hc
        by_cases h0 : ∀ r, fcomm w (L.z (D.alpha r)) = 1
        · exact hbase (F87.mem_ballStab_of_fcomm h7 D hw h0)
        obtain ⟨s, hs⟩ := not_forall.1 h0
        have hex : ∃ t, t ≠ s ∧ fcomm w (L.z (D.alpha t)) ≠ 1 := by
          by_contra hne
          have hne' : ∀ t, t ≠ s → fcomm w (L.z (D.alpha t)) = 1 := fun t ht => by
            by_contra h
            exact hne ⟨t, ht, h⟩
          have hprod := F87.prod_fcomm_eq_one h7 h512 h82 D hw
          rw [prodFive_single (fun r => fcomm w (L.z (D.alpha r))) s (fun r hr => hne' r hr)]
            at hprod
          exact hs hprod
        obtain ⟨t, hts, ht⟩ := hex
        have hst : s ≠ t := hts.symm
        have hYK : D.y δ' s * D.y δ' t ∈ nbrStab Γ G α := mul_mem (hyK s) (hyK t)
        have hw' : (D.y δ' s * D.y δ' t)⁻¹ * w ∈ nbrStab Γ G α := mul_mem (inv_mem hYK) hw
        have hcommr : ∀ r, fcomm (D.y δ' s * D.y δ' t) (L.z (D.alpha r)) =
            if r = s ∨ r = t then L.z α else 1 := fun r =>
          F87.fcomm_pair h83b D hY hyK hα hst r
        have hΘ' : ∀ r, fcomm ((D.y δ' s * D.y δ' t)⁻¹ * w) (L.z (D.alpha r)) =
            if r = s ∨ r = t then 1 else fcomm w (L.z (D.alpha r)) := by
          intro r
          by_cases hr : r = s ∨ r = t
          · simp only [hr, ↓reduceIte]
            refine F87.fcomm_quot (L := L) hα (F.nbrStab_le_stabilizer α hYK)
              (F.nbrStab_le_stabilizer α hw) ?_ ?_
            · rw [hcommr r]
              simp only [hr, ↓reduceIte]
              exact Or.inr rfl
            · rw [hcommr r]
              simp only [hr, ↓reduceIte]
              rcases hr with h | h
              · rw [h]
                exact (hΘ w hw s).resolve_left hs
              · rw [h]
                exact (hΘ w hw t).resolve_left ht
          · simp only [hr, ↓reduceIte]
            have h1 : fcomm (D.y δ' s * D.y δ' t) (L.z (D.alpha r)) = 1 := by
              rw [hcommr r]
              simp only [hr, ↓reduceIte]
            exact fcomm_inv_mul_of_comm (F87.fcomm_eq_one_iff.1 h1)
        have hsub : Finset.univ.filter
            (fun r => fcomm ((D.y δ' s * D.y δ' t)⁻¹ * w) (L.z (D.alpha r)) ≠ 1) ⊂
            Finset.univ.filter (fun r => fcomm w (L.z (D.alpha r)) ≠ 1) := by
          rw [Finset.ssubset_iff_of_subset]
          · refine ⟨s, Finset.mem_filter.2 ⟨Finset.mem_univ s, hs⟩, fun h => ?_⟩
            exact (Finset.mem_filter.1 h).2 (by rw [hΘ' s]; simp)
          · intro r hr
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
            rw [hΘ' r] at hr
            by_cases hrst : r = s ∨ r = t
            · simp only [hrst, ↓reduceIte] at hr
              exact absurd rfl hr
            · simp only [hrst, ↓reduceIte] at hr
              exact hr
        have hlt := Finset.card_lt_card hsub
        have hw'H := ih _ hw' (by omega)
        have hweq : w = (D.y δ' s * D.y δ' t) * ((D.y δ' s * D.y δ' t)⁻¹ * w) := by group
        rw [hweq]
        exact mul_mem (mul_mem (hy_mem s) (hy_mem t)) hw'H
    exact fun w hw => key _ w hw le_rfl
  · refine sup_le ((Subgroup.closure_le _).2 (Set.range_subset_iff.2 fun k => hyK k))
      (sup_le ?_ inf_le_left)
    refine (F87.zGroup_le_ballStab h7 D).trans (fixSet_anti ?_)
    intro w hw
    show Γ.dist α w ≤ 2
    rw [dist_eq_one_iff_adj.2 hw]
    norm_num

end CFSG.Quasithin.Fan86
