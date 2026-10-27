module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Four
public import CFSG.CGT.PushingUpLit.CGT6.Emb5FourT

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16c1610_card_vtil_le_of_s_eq_two (D : Data G) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hconc : Conc4_136 D V₀ V hV L) {m : ℕ}
    (hrk : rk ↥(wTil V₀ V hV L) = m) (hs : s15 D.M V₀ V hV L = 2) :
    Nat.card (Vtil V₀ V hV) ≤ 2 ^ (2 * m) := by
  obtain ⟨t, -, -, -, -, hsup, -⟩ := hconc
  let Ts : Set (Subgroup (MulAut (Vtil V₀ V hV))) :=
    {X | ∃ φ ∈ Mbar D.M V₀ V hV, X = (lBar V₀ V hV L).map (MulAut.conj φ).toMonoidHom}
  let S : Set (Subgroup (Vtil V₀ V hV)) :=
    conjSubs (Mbar D.M V₀ V hV) (commSub ⊤ (lBar V₀ V hV L))
  have hconj : ∀ g : MulAut (Vtil V₀ V hV),
      (commSub (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L)).map g.toMonoidHom =
        commSub ⊤ ((lBar V₀ V hV L).map (MulAut.conj g).toMonoidHom) := by
    intro g
    have htop : (⊤ : Subgroup (Vtil V₀ V hV)).map g.toMonoidHom = ⊤ :=
      eq_top_iff.2 fun x _ => ⟨g.symm x, Subgroup.mem_top _, by simp⟩
    have h := s15_Core_commSub_map_conj (⊤ : Subgroup (Vtil V₀ V hV)) (lBar V₀ V hV L) g
    rw [htop] at h
    exact h.symm
  have hTs : Ts.ncard = 2 := hs
  have hTfin : Ts.Finite := Set.finite_of_ncard_ne_zero (by rw [hTs]; norm_num)
  have hSsub : S ⊆ (fun X => commSub (⊤ : Subgroup (Vtil V₀ V hV)) X) '' Ts := by
    rintro Y ⟨g, hg, rfl⟩
    exact ⟨_, ⟨g, hg, rfl⟩, (hconj g).symm⟩
  have hSfin : S.Finite := (hTfin.image _).subset hSsub
  have hSle : S.ncard ≤ 2 := by
    calc S.ncard ≤ ((fun X => commSub (⊤ : Subgroup (Vtil V₀ V hV)) X) '' Ts).ncard :=
          Set.ncard_le_ncard hSsub (hTfin.image _)
      _ ≤ Ts.ncard := Set.ncard_image_le hTfin
      _ = 2 := hTs
  have hX₀ : commSub ⊤ (lBar V₀ V hV L) ∈ S := by
    refine ⟨1, (Mbar D.M V₀ V hV).one_mem, ?_⟩
    ext x
    simp [Subgroup.mem_map]
  have hrkS : ∀ Y ∈ S, rk ↥Y = m := by
    rintro Y ⟨g, -, rfl⟩
    rw [rk_map_aut_eq]
    exact hrk
  obtain ⟨X₁, hX₁, hcover⟩ : ∃ X₁ ∈ S, ∀ Y ∈ S,
      Y = commSub ⊤ (lBar V₀ V hV L) ∨ Y = X₁ := by
    by_cases h : ∃ X₁ ∈ S, X₁ ≠ commSub ⊤ (lBar V₀ V hV L)
    · obtain ⟨X₁, hX₁, hne⟩ := h
      have hsub : ({commSub ⊤ (lBar V₀ V hV L), X₁} : Set (Subgroup (Vtil V₀ V hV))) ⊆ S := by
        intro Y hY
        rcases hY with rfl | rfl
        · exact hX₀
        · exact hX₁
      have hpair : ({commSub ⊤ (lBar V₀ V hV L), X₁} : Set (Subgroup (Vtil V₀ V hV))).ncard = 2 :=
        Set.ncard_pair hne.symm
      have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hpair]; exact hSle) hSfin
      refine ⟨X₁, hX₁, fun Y hY => ?_⟩
      rw [← heq] at hY
      exact hY
    · exact ⟨_, hX₀, fun Y hY => Or.inl (by_contra fun hne => h ⟨Y, hY, hne⟩)⟩
  have htop : commSub ⊤ (lBar V₀ V hV L) ⊔ X₁ = ⊤ := by
    refine eq_top_iff.2 ?_
    calc (⊤ : Subgroup (Vtil V₀ V hV)) = ⨆ Y ∈ S, Y := hsup.symm
      _ ≤ commSub ⊤ (lBar V₀ V hV L) ⊔ X₁ := by
        refine iSup₂_le fun Y hY => ?_
        rcases hcover Y hY with h | h
        · rw [h]
          exact le_sup_left
        · rw [h]
          exact le_sup_right
  have hsq : ∀ v : Vtil V₀ V hV, v ^ 2 = 1 := fun v => s15_Infra_vtil_sq_eq_one V₀ V hV v
  have hp : IsPGroup 2 (Vtil V₀ V hV) := isPGroup_two_of_sq_eq_one hsq
  have hr1 := rk_sup_add_rk_inf (commSub ⊤ (lBar V₀ V hV L)) X₁
  rw [htop, rk_top, hrkS _ hX₀, hrkS _ hX₁] at hr1
  rw [card_eq_two_pow_of_isPGroup hp]
  exact Nat.pow_le_pow_right (by norm_num) (by omega)

theorem s16c1610_pRank_seven_le_two_of_case168_11 (D : Data G) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hconc : Conc4_136 D V₀ V hV L)
    (h11 : Case168_11 D V₀ V hV L) :
    CFSG.Open.pRank 7 (Mbar D.M V₀ V hV) ≤ 2 := by
  haveI : Finite (MulAut (Vtil V₀ V hV)) := MulEquiv.finite_left
  have hcard : Nat.card (Vtil V₀ V hV) ≤ 256 := by
    have h := s16c1610_card_vtil_le_of_s_eq_two D hV hconc h11.2.1 h11.2.2.1
    exact h.trans (by norm_num)
  have hnd := CFSG.CGT.PushingUpLit.CGT6.not_dvd_card_mulAut_of_card_le_256
    (s15_Infra_vtil_sq_eq_one V₀ V hV) hcard
  by_contra hlt
  have h3 : 3 ≤ CFSG.Open.pRank 7 (Mbar D.M V₀ V hV) := by omega
  obtain ⟨E, -, hEc⟩ := exists_isElemAbelian_subgroupOf_of_le_pRank (by norm_num : Nat.Prime 7) h3
  have h1 : Nat.card E ∣ Nat.card ↥(Mbar D.M V₀ V hV) := Subgroup.card_subgroup_dvd_card E
  have h2 : Nat.card ↥(Mbar D.M V₀ V hV) ∣ Nat.card (MulAut (Vtil V₀ V hV)) :=
    Subgroup.card_subgroup_dvd_card _
  rw [hEc] at h1
  exact hnd (by simpa using h1.trans h2)

theorem s16c1610_false_of_case11_four (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hc : Counterex16 D V₀ V L hV) (h4 : 3 < CFSG.Open.evenRank G)
    (h11 : Case168_11 D V₀ V hV L) : False := by
  have h7σ : 7 ∈ D.sig := by
    rw [h11.2.2.2]
    exact Set.mem_singleton 7
  have h3 := s16c1610_three_le_pRank_mBar_of_four D hx h61 h127 hc.setting.hyp16 hV h4 h7σ
  have h2 := s16c1610_pRank_seven_le_two_of_case168_11 D hV hc.conc h11
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
