module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNarrowInputs

import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosPrimed
import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthTyBridge
import CFSG.LocalAnalysis.StandardType.GGSecFiveReflMaxNotG2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

private lemma nsPump_ggNbr_one_bot {G : Type} [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (y : G)
    (K : Subgroup G) : ¬ GGNbr p B 1 ⊥ ⊥ y K := by
  intro h
  obtain ⟨-, hneigh⟩ := h
  obtain ⟨-, -, hnc⟩ := hneigh
  exact hnc (by
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.commutator_bot_right]
    exact bot_le)

private lemma nsPump_ggAInf_one_bot {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs L : Subgroup G) :
    ggAInf p B Bs 1 L ⊥ ⊥ = ggAutomizer L Bs := by
  rw [ggAInf]
  have hbot : (⨆ (y : G) (K : Subgroup G) (_ : GGNbr p B 1 ⊥ ⊥ y K), ggAutomizer K Bs) = ⊥ := by
    apply iSup_eq_bot.mpr
    intro y
    apply iSup_eq_bot.mpr
    intro K
    apply iSup_eq_bot.mpr
    intro hNbr
    exact (nsPump_ggNbr_one_bot p B y K hNbr).elim
  rw [hbot, sup_bot_eq]

theorem ggSecFivePumpNbrInput_split :
    ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
      (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg' p B Bs x L D J 𝒦 → GGSplitLie p L →
        ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → GGSplitLie p K →
          GGWeylReflectionGroup p (ggAutomizer K Bs) ∧
            ¬ GGWeylOfType p CoxeterMatrix.G₂ (ggAutomizer K Bs) := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit y K hnb hKsplit
  obtain ⟨t, n, f, ψ, hadm, hrk, _hker, _hrange, ht, _hpf, htab⟩ :=
    s2jn_ggSecFiveKGPosNbrInput'_holds G p B Bs x L D J 𝒦 hcfg hsplit y K hnb hKsplit
  simp only [GGTableBPos] at htab
  obtain ⟨ε, hrefl, -, -⟩ := htab
  have htype : GGIsWeylMatrixAD (CFSG.LieType.RootSystem.coxeterMatrix (ggU t n f).D.isFiniteType) ∨
      GGIsWeylMatrixE (CFSG.LieType.RootSystem.coxeterMatrix (ggU t n f).D.isFiniteType) := by
    rcases ht with rfl | rfl | rfl | rfl | rfl
    · obtain ⟨e, he⟩ := OrthF3.ggOrthTy_cox_psl (n := n) (f := f) hadm
      exact Or.inl (Or.inl ⟨n - 1, e,
        by simpa only [CFSG.LieType.Universal.bnRank] using hrk, he⟩)
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
  refine ⟨⟨Fin (ggU t n f).D.rank,
    CFSG.LieType.RootSystem.coxeterMatrix (ggU t n f).D.isFiniteType, ?_, ε, hrefl⟩, ?_⟩
  · rcases htype with h | h
    · exact h.isWeylMatrix
    · exact h.isWeylMatrix
  ·
    rintro ⟨e, -⟩
    have hAInf := nsPump_ggAInf_one_bot (G := G) p B Bs K
    have hle : ggAutomizer K Bs ≤ ggAInf p B Bs 1 K ⊥ ⊥ := by rw [hAInf]
    let f' : (CoxeterMatrix.G₂).Group ≃* ↥(ggAInf p B Bs 1 K ⊥ ⊥) :=
      e.trans (MulEquiv.subgroupCongr hAInf.symm)
    have hcontra := ggRM_not_G2 (p := p) (B := B) (Bs := Bs) (x := 1) (L := K)
      (D := ⊥) (J := ⊥) (ιA := Fin 2) (M := CoxeterMatrix.G₂)
      (ιL := Fin (ggU t n f).D.rank)
      (ML := CFSG.LieType.RootSystem.coxeterMatrix (ggU t n f).D.isFiniteType)
      htype ⟨ε, hrefl⟩ hle f'
    exact hcontra ⟨Equiv.refl (Fin 2), by ext i j; simp [CoxeterMatrix.reindex_apply]⟩

end CFSG.StandardType

end
