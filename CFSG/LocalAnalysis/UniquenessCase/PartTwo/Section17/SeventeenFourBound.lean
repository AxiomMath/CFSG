module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BBarConjShape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarSubInFSq
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BBarDeltaSixteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HeJ2Local17

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem b17_4BoundA_holds (hW4 : Inputs1719.W4Lem4_16b) (h77 : Inputs1719.W4Lem7_7)
    (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V) :
    ∀ (L L₁ L₂ : Subgroup G), L ∈ calC D.M → D.T ≤ normalizer (L : Set G) →
      barSub V₀ V hV.isElemAbelian L ∈ compBar D.M V₀ V hV.isElemAbelian →
      (D.T ⊓ normalizer (L : Set G)) ≤ L₁ → (D.T ⊓ normalizer (L : Set G)) ≤ L₂ →
      L ⊔ (D.T ⊓ normalizer (L : Set G)) = L₁ ⊔ L₂ →
      Nonempty (Bar2 L₁ ≃* Equiv.Perm (Fin 3)) → Nonempty (Bar2 L₂ ≃* Equiv.Perm (Fin 3)) →
      ((L.subgroupOf D.M).Normal ∨ ACandLe (UC22.BarInf L) 2) →
      fixV (barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L)) = ⊥ →
      bBar (UC22.conjClosure D.M L) D.M V₀ V hV.isElemAbelian ≤ 2 := by
  classical
  intro L L₁ L₂ hL hTL hLbar hS1 hS2 hsup hbar1 hbar2 hNA hfix
  rcases hNA with hN | hA
  ·
    have hLM : L ≤ D.M := hL.1.le
    have hST : (D.T ⊓ Subgroup.normalizer (L : Set G)) = D.T := inf_eq_left.mpr hTL
    have hsup' : L ⊔ D.T = L₁ ⊔ L₂ := by rw [← hST]; exact hsup
    have hT1 : D.T ≤ L₁ := by simpa [hST] using hS1
    have hT2 : D.T ≤ L₂ := by simpa [hST] using hS2
    have h12M : L₁ ⊔ L₂ ≤ D.M := by rw [← hsup']; exact sup_le hLM D.sylowM.le
    have hL1M : L₁ ≤ D.M := le_sup_left.trans h12M
    have hL2M : L₂ ≤ D.M := le_sup_right.trans h12M
    have hconj : UC22.conjClosure D.M L = L :=
      Inputs1719.conjClosure_eq_self_of_normal hLM hN
    rw [hconj] at hfix ⊢
    have hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥ :=
      CFSG.Quasithin.B15P4.ne_bot_of_isComponentOf hLbar
    have hMS : D.M ≤ stabTil V₀ V :=
      le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀
    have hLstab : L ≤ stabTil V₀ V := hLM.trans hMS
    have hTstab : D.T ≤ stabTil V₀ V := D.sylowM.le.trans hMS
    have h12stab : L₁ ⊔ L₂ ≤ stabTil V₀ V := by
      rw [← hsup']; exact sup_le hLstab hTstab
    have h1stab : L₁ ≤ stabTil V₀ V := le_sup_left.trans h12stab
    have h2stab : L₂ ≤ stabTil V₀ V := le_sup_right.trans h12stab
    have hsupbar : barSub V₀ V hV.isElemAbelian L₁ ⊔ barSub V₀ V hV.isElemAbelian L₂ =
        barSub V₀ V hV.isElemAbelian L ⊔ barSub V₀ V hV.isElemAbelian D.T := by
      rw [← s16c7_barSub_sup V₀ V hV.isElemAbelian h1stab h2stab, ← hsup',
        s16c7_barSub_sup V₀ V hV.isElemAbelian hLstab hTstab]
    set Δ : Set (Subgroup (MulAut (Vtil V₀ V hV.isElemAbelian))) :=
      {barSub V₀ V hV.isElemAbelian L₁, barSub V₀ V hV.isElemAbelian L₂} with hΔdef
    have hΔfin : Δ.Finite := Set.toFinite _
    have hmem : ∀ H ∈ Δ, H = barSub V₀ V hV.isElemAbelian L₁ ∨
        H = barSub V₀ V hV.isElemAbelian L₂ := by
      intro H hH
      simpa [hΔdef] using hH
    have hΔ : ∀ H ∈ Δ, H ≤ barSub V₀ V hV.isElemAbelian L ⊔
        barSub V₀ V hV.isElemAbelian D.T ∧ barSub V₀ V hV.isElemAbelian D.T ≤ H := by
      intro H hH
      rcases hmem H hH with rfl | rfl
      · exact ⟨le_sup_left.trans (le_of_eq hsupbar), barSub_mono V₀ V hV.isElemAbelian hT1⟩
      · exact ⟨le_sup_right.trans (le_of_eq hsupbar), barSub_mono V₀ V hV.isElemAbelian hT2⟩
    have hgen : (⨆ H ∈ Δ, H) = barSub V₀ V hV.isElemAbelian L ⊔
        barSub V₀ V hV.isElemAbelian D.T := by
      have h1 : (⨆ H ∈ Δ, H) = barSub V₀ V hV.isElemAbelian L₁ ⊔
          barSub V₀ V hV.isElemAbelian L₂ := by
        refine le_antisymm (iSup₂_le ?_) (sup_le ?_ ?_)
        · intro H hH
          rcases hmem H hH with rfl | rfl
          · exact le_sup_left
          · exact le_sup_right
        · exact le_iSup₂ (f := fun H (_ : H ∈ Δ) => H)
            (barSub V₀ V hV.isElemAbelian L₁) (by simp [hΔdef])
        · exact le_iSup₂ (f := fun H (_ : H ∈ Δ) => H)
            (barSub V₀ V hV.isElemAbelian L₂) (by simp [hΔdef])
      rw [h1, ← s16c7_barSub_sup V₀ V hV.isElemAbelian h1stab h2stab, ← hsup',
        s16c7_barSub_sup V₀ V hV.isElemAbelian hLstab hTstab]
    have hι : ∀ H ∈ Δ, CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H := by
      intro H hH
      rcases hmem H hH with rfl | rfl
      · exact inFSq_one_barSub_of_bar2_perm_three hV hL1M hbar1
      · exact inFSq_one_barSub_of_bar2_perm_three hV hL2M hbar2
    have hcard : Δ.ncard ≤ 2 := by
      rw [hΔdef]
      calc (insert (barSub V₀ V hV.isElemAbelian L₁)
            {barSub V₀ V hV.isElemAbelian L₂} : Set _).ncard
          ≤ ({barSub V₀ V hV.isElemAbelian L₂} : Set _).ncard + 1 :=
            Set.ncard_insert_le _ _
        _ = 2 := by norm_num [Set.ncard_singleton]
    have hk : fIndexSum Δ ≤ (2 : ℕ∞) :=
      (fIndexSum_le_ncard_of_inFSq_one hΔfin hι).trans (by exact_mod_cast hcard)
    exact bBar_le_of_delta D hV hW4 hL hN hL1 hfix Δ 2 hΔfin hΔ hgen hk
  ·
    exact bBar_conjClosure_le_of_aCandLe hV h77 hL hA

@[expose] def R17_4AtA (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V) : Prop :=
  ∀ (L L₁ L₂ : Subgroup G), L ∈ calC D.M → D.T ≤ normalizer (L : Set G) →
    barSub V₀ V hV.isElemAbelian L ∈ compBar D.M V₀ V hV.isElemAbelian →
    (D.T ⊓ normalizer (L : Set G)) ≤ L₁ → (D.T ⊓ normalizer (L : Set G)) ≤ L₂ →
    L ⊔ (D.T ⊓ normalizer (L : Set G)) = L₁ ⊔ L₂ →
    Nonempty (Bar2 L₁ ≃* Equiv.Perm (Fin 3)) →
    Nonempty (Bar2 L₂ ≃* Equiv.Perm (Fin 3)) →
    ((L.subgroupOf D.M).Normal ∨ ACandLe (UC22.BarInf L) 2) →
    UniqueMax D.M (L ⊔ D.T) → D.k = 2

section Certified


theorem r17_4AtA_holds (D : Data G) (h111 : W3Thm111 G) (h126 : R126 D)
    (h127 : R127 D) (h618 : W3_6_18 G)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G)
    (h66 : UC6.R6_6 D) (h88 : W3Thm88 G) (h86 : W3Lem86_1 G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h183 : W3Thm183 G) {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V)
    (h93 : CFSG.LocalAnalysis.WeakClosure81.Thm93 V₀ D.T)
    (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (hW4 : Inputs1719.W4Lem4_16b) (h77 : Inputs1719.W4Lem7_7) :
    R17_4AtA D V₀ V hV :=
  fun L L₁ L₂ hL hTL hLbar hS1 hS2 hsup hbar1 hbar2 hNA hU =>
    seventeen_four_at D h111 h126 h127 h618 hTim hcat h66 h88 h86 hx h61 h1114 h162 hTor
      h1482 h183 hV h93 h1669 hL hTL hLbar hS1 hS2 hsup hbar1 hbar2 hU
      (fun _ _ hfix =>
        b17_4BoundA_holds hW4 h77 D V₀ V hV L L₁ L₂ hL hTL hLbar hS1 hS2 hsup hbar1 hbar2
          hNA hfix)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
