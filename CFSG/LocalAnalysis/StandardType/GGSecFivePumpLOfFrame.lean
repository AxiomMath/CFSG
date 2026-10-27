module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNarrowInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosPrimed
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthTyBridge
public import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxNotG2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.LieType.RootSystem CFSG.LieType.Universal

private lemma ct_pl_ggNbr_one_bot {G : Type} [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (y : G)
    (K : Subgroup G) : ¬ GGNbr p B 1 ⊥ ⊥ y K := by
  intro h
  obtain ⟨-, hneigh⟩ := h
  obtain ⟨-, -, hnc⟩ := hneigh
  exact hnc (by
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.commutator_bot_right]
    exact bot_le)

private lemma ct_pl_ggAInf_one_bot {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs L : Subgroup G) :
    ggAInf p B Bs 1 L ⊥ ⊥ = ggAutomizer L Bs := by
  rw [ggAInf]
  have hbot : (⨆ (y : G) (K : Subgroup G) (_ : GGNbr p B 1 ⊥ ⊥ y K), ggAutomizer K Bs) = ⊥ := by
    apply iSup_eq_bot.mpr
    intro y
    apply iSup_eq_bot.mpr
    intro K
    apply iSup_eq_bot.mpr
    intro hNbr
    exact (ct_pl_ggNbr_one_bot p B y K hNbr).elim
  rw [hbot, sup_bot_eq]

theorem ggSecFivePumpLInput_holds :
    GGSecFivePumpLInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit
  obtain ⟨t, n, f, ψ, hloc, -, htab⟩ :=
    s2jn_exists_tableBFrame G p B Bs x L D J 𝒦 hcfg hsplit
  simp only [GGTableBPos] at htab
  obtain ⟨ε, hrefl, -, -⟩ := htab
  obtain ⟨hp, _hp2, hadm, h3rank⟩ := hloc.1
  obtain ⟨_hker, _hrange, ht, _hpf⟩ := hloc.2.1
  have htype : GGIsWeylMatrixAD (coxeterMatrix (ggU t n f).D.isFiniteType) ∨
      GGIsWeylMatrixE (coxeterMatrix (ggU t n f).D.isFiniteType) := by
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨e, he⟩ := OrthF3.ggOrthTy_cox_psl (n := n) (f := f) hadm
      exact Or.inl (Or.inl ⟨n - 1, e, by simpa only [bnRank] using h3rank, he⟩)
    · have hn4 : 4 ≤ n := by
        have h := hadm
        simp only [StatedLieAdmissible] at h
        exact h.2.2
      obtain ⟨e, he⟩ := OrthF3.ggOrthTy_cox_D (n := n) (f := f) hadm
      exact Or.inl (Or.inr ⟨n, e, hn4, he⟩)
    · obtain ⟨e, he⟩ := OrthF3.ggOrthTy_cox_E (n := n) (f := f)
      exact Or.inr (Or.inl ⟨e, he⟩)
    · obtain ⟨e, he⟩ := OrthF3.ggOrthTy_cox_E7 (n := n) (f := f)
      exact Or.inr (Or.inr (Or.inl ⟨e, he⟩))
    · obtain ⟨e, he⟩ := OrthF3.ggOrthTy_cox_E8 (n := n) (f := f)
      exact Or.inr (Or.inr (Or.inr ⟨e, he⟩))
  refine ⟨⟨Fin (ggU t n f).D.rank, coxeterMatrix (ggU t n f).D.isFiniteType, ?_, ε, hrefl⟩, ?_⟩
  · rcases htype with h | h
    · exact h.isWeylMatrix
    · exact h.isWeylMatrix
  ·
    rintro ⟨e, -⟩
    have hAInf := ct_pl_ggAInf_one_bot (G := G) p B Bs L
    have hle : ggAutomizer L Bs ≤ ggAInf p B Bs 1 L ⊥ ⊥ := by rw [hAInf]
    let f' : (CoxeterMatrix.G₂).Group ≃* ↥(ggAInf p B Bs 1 L ⊥ ⊥) :=
      e.trans (MulEquiv.subgroupCongr hAInf.symm)
    have hcontra := ggRM_not_G2 (p := p) (B := B) (Bs := Bs) (x := 1) (L := L)
      (D := ⊥) (J := ⊥) (ιA := Fin 2) (M := CoxeterMatrix.G₂)
      (ιL := Fin (ggU t n f).D.rank) (ML := coxeterMatrix (ggU t n f).D.isFiniteType)
      htype ⟨ε, hrefl⟩ hle f'
    exact hcontra ⟨Equiv.refl (Fin 2), by ext i j; simp [CoxeterMatrix.reindex_apply]⟩

end CFSG.StandardType

end
