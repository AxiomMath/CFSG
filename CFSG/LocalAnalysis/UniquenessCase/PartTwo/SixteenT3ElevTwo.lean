module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNineBTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16t_twoConj_of_odd (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (hV : IsElemAbelian 2 V) (hc : Counterex16 D V₀ V L hV)
    (hodd : Odd (Nat.card ↥(barSub V₀ V hV L))) (hs : s15 D.M V₀ V hV L = 2) :
    ∃ g : MulAut (Vtil V₀ V hV), S16n9bTwo (Mbar D.M V₀ V hV) (lBar V₀ V hV L) g := by
  have h : Hyp151 D V₀ V L := hc.setting.hyp151
  have hL : barSub V₀ V hV L ≠ ⊥ := hc.ne_bot
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  show ∃ g : MulAut (Vtil V₀ V hV), S16n9bTwo (Mbar D.M V₀ V hV) (barSub V₀ V hV L) g
  have hS : {X : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV, X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom}.ncard = 2 :=
    hs
  obtain ⟨x, y, hxy, hSxy⟩ := Set.ncard_eq_two.1 hS
  have hAS : barSub V₀ V hV L ∈ {X : Subgroup (MulAut (Vtil V₀ V hV)) |
      ∃ φ ∈ Mbar D.M V₀ V hV, X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} :=
    ⟨1, (Mbar D.M V₀ V hV).one_mem, (s16n9b_map_conj_one _).symm⟩
  rw [hSxy] at hAS
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hAS
  obtain ⟨B, hBA, hSAB⟩ : ∃ B : Subgroup (MulAut (Vtil V₀ V hV)), B ≠ barSub V₀ V hV L ∧
      {X : Subgroup (MulAut (Vtil V₀ V hV)) | ∃ φ ∈ Mbar D.M V₀ V hV,
        X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} = {barSub V₀ V hV L, B} := by
    rcases hAS with h1 | h1
    · exact ⟨y, fun hy => hxy (h1.symm.trans hy.symm), by rw [hSxy, h1]⟩
    · exact ⟨x, fun hx => hxy (hx.trans h1), by rw [hSxy, h1, Set.pair_comm]⟩
  have hBS : B ∈ {X : Subgroup (MulAut (Vtil V₀ V hV)) | ∃ φ ∈ Mbar D.M V₀ V hV,
      X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} := by
    rw [hSAB]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  obtain ⟨φ₀, hφ₀M, hBφ₀⟩ := hBS
  obtain ⟨m₀, hm₀M, hKm₀⟩ := s16n9b_exists_conj_eq h hV hφ₀M
  have hAB : (barSub V₀ V hV L).map (MulAut.conj φ₀).toMonoidHom = B := hBφ₀.symm
  have hKB : barSub V₀ V hV (conjSubgroup L m₀) = B := hKm₀.trans hAB
  have hne1 : m₀ * (1 : G)⁻¹ ∉ nBar D.M V₀ V hV L := by
    intro hmem
    have := (s15_Infra_mul_inv_mem_nBar_iff (L := L) h.hyp125 hV D.M.one_mem hm₀M).1 hmem
    rw [conjSubgroup_one, hKB] at this
    exact hBA this
  have hne2 : (1 : G) * m₀⁻¹ ∉ nBar D.M V₀ V hV L := by
    intro hmem
    have := (s15_Infra_mul_inv_mem_nBar_iff (L := L) h.hyp125 hV hm₀M D.M.one_mem).1 hmem
    rw [conjSubgroup_one, hKB] at this
    exact hBA this.symm
  have hc1 : ⁅barSub V₀ V hV L, B⁆ = ⊥ ∧
      commSub (commSub ⊤ (barSub V₀ V hV L)) B = ⊥ := by
    have := s15_Kbar_commute_conj h (m := 1) (m' := m₀) D.M.one_mem hm₀M hne1
    rwa [conjSubgroup_one, hKB] at this
  have hc2 : commSub (commSub ⊤ B) (barSub V₀ V hV L) = ⊥ := by
    have := (s15_Kbar_commute_conj h (m := m₀) (m' := 1) hm₀M D.M.one_mem hne2).2
    rwa [conjSubgroup_one, hKB] at this
  have hWB : (commSub ⊤ (barSub V₀ V hV L)).map φ₀.toMonoidHom = commSub ⊤ B := by
    rw [← hAB, s15_Infra_commSub_top_map_conj]
  have hKcases : ∀ m : G, m ∈ D.M → barSub V₀ V hV (conjSubgroup L m) = barSub V₀ V hV L ∨
      barSub V₀ V hV (conjSubgroup L m) = B := by
    intro m hm
    have hmem : barSub V₀ V hV (conjSubgroup L m) ∈ {X : Subgroup (MulAut (Vtil V₀ V hV)) |
        ∃ φ ∈ Mbar D.M V₀ V hV, X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} :=
      ⟨(actTil V₀ V hV ⟨m, hMs hm⟩)⁻¹,
        Subgroup.inv_mem _ (actTil_mem_barSub V₀ V hV hm (hMs hm)),
        s15_Infra_barSub_conjSubgroup V₀ V hV (hMs hm) L⟩
    rw [hSAB] at hmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmem
  have hW : ∀ m : G, m ∈ D.M →
      imgTil V₀ V hV (conjSubgroup (wSub V₀ V hV L) m) =
        commSub ⊤ (barSub V₀ V hV (conjSubgroup L m)) := by
    intro m hm
    rw [← s15_Infra_wSub_conjSubgroup V₀ V L hV (hMs hm), wSub, imgTil_preTil]
    rfl
  have hfixA : ∀ a ∈ barSub V₀ V hV L, ∀ w ∈ commSub ⊤ B, a w = w := fun a ha w hw =>
    mem_fixV.1 (commSub_eq_bot_iff.1 hc2 hw) a ha
  refine ⟨φ₀, ?_⟩
  refine ⟨barSub_mono V₀ V hV h.le, hφ₀M, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [hAB]
    exact hBA
  ·
    rw [hAB]
    exact hc1.1
  ·
    intro φ hφ
    have hmem : (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom ∈
        {X : Subgroup (MulAut (Vtil V₀ V hV)) | ∃ φ ∈ Mbar D.M V₀ V hV,
          X = (barSub V₀ V hV L).map (MulAut.conj φ).toMonoidHom} := ⟨φ, hφ, rfl⟩
    rw [hSAB] at hmem
    rcases hmem with h1 | h1
    · exact Or.inl h1
    · exact Or.inr ((Set.mem_singleton_iff.1 h1).trans hAB.symm)
  ·
    intro b hb w hw
    rw [hAB] at hb
    exact mem_fixV.1 (commSub_eq_bot_iff.1 hc1.2 hw) b hb
  ·
    intro a ha w hw
    rw [hWB] at hw
    exact hfixA a ha w hw
  ·
    rw [hWB]
    have hcop := (coprime_decomp (P := barSub V₀ V hV L) hodd
      (s15_Infra_vtil_sq_eq_one V₀ V hV) (W := ⊤) (fun _ _ _ _ => Subgroup.mem_top _)).2
    rw [eq_bot_iff]
    intro x hx
    have hxfix : x ∈ fixV (barSub V₀ V hV L) := mem_fixV.2 fun a ha => hfixA a ha x hx.2
    have hmem : x ∈ commSub ⊤ (barSub V₀ V hV L) ⊓ (⊤ ⊓ fixV (barSub V₀ V hV L)) :=
      ⟨hx.1, Subgroup.mem_top _, hxfix⟩
    rw [hcop] at hmem
    exact hmem
  ·
    rw [hWB]
    have htop := s15_Two_iSup_commSub_eq_top D h1217 h hL
    refine le_antisymm le_top ?_
    calc (⊤ : Subgroup (Vtil V₀ V hV))
        = ⨆ m : D.M, commSub ⊤ (barSub V₀ V hV (conjSubgroup L (m : G))) := htop.symm
      _ ≤ commSub ⊤ (barSub V₀ V hV L) ⊔ commSub ⊤ B := by
        refine iSup_le fun m => ?_
        rcases hKcases m m.2 with h1 | h1
        · exact (congrArg (commSub ⊤) h1).le.trans le_sup_left
        · exact (congrArg (commSub ⊤) h1).le.trans le_sup_right


end CFSG.LocalAnalysis.UniquenessCase.PartTwo
