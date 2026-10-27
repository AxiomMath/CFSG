module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEightInputs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_He_of_calC {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hnorm : Tbar9 D ≤ Subgroup.normalizer (K1Nine D L : Set (Mbar9 D)))
    (hfact : ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y),
      Inputs1719.KYForm Y K S → Nonempty (↥K ≃* Bar2 L) →
      ∃ H₁ H₂ H₃ : Subgroup Y, S ≤ H₁ ∧ S ≤ H₂ ∧ S ≤ H₃ ∧
        CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₁ ∧
          CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₂ ∧
            CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₃ ∧
              H₁ ⊔ H₂ ⊔ H₃ = ⊤) :
    ∃ H₁ H₂ H₃ : Subgroup G, D.T ≤ H₁ ∧ D.T ≤ H₂ ∧ D.T ≤ H₃ ∧
      H₁ ≤ L ⊔ D.T ∧ H₂ ≤ L ⊔ D.T ∧ H₃ ≤ L ⊔ D.T ∧
      CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₁ ∧
        CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₂ ∧
          CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₃ ∧
            H₁ ⊔ H₂ ⊔ H₃ = L ⊔ D.T := by
  obtain ⟨Y, hYgrp, hYfin, KY, SY, f', hky, hKYe, hf'surj, hker2, -, hTmap, -⟩ :=
    exists_twoQuotient_lift hL hnorm
  obtain ⟨P₁, P₂, P₃, hSP₁, hSP₂, hSP₃, hFS₁, hFS₂, hFS₃, hsup⟩ :=
    hfact Y KY SY hky hKYe
  let H : Subgroup G := L ⊔ D.T
  have hSmap₁ : (D.T.subgroupOf H).map f' ≤ P₁ := by
    rw [show D.T.subgroupOf H = D.T.subgroupOf (L ⊔ D.T) from rfl, hTmap]
    exact hSP₁
  have hSmap₂ : (D.T.subgroupOf H).map f' ≤ P₂ := by
    rw [show D.T.subgroupOf H = D.T.subgroupOf (L ⊔ D.T) from rfl, hTmap]
    exact hSP₂
  have hSmap₃ : (D.T.subgroupOf H).map f' ≤ P₃ := by
    rw [show D.T.subgroupOf H = D.T.subgroupOf (L ⊔ D.T) from rfl, hTmap]
    exact hSP₃
  let K₁ : Subgroup ↥H := P₁.comap f'
  let K₂ : Subgroup ↥H := P₂.comap f'
  let K₃ : Subgroup ↥H := P₃.comap f'
  have hTK₁ : D.T.subgroupOf H ≤ K₁ := fun t ht =>
    Subgroup.mem_comap.mpr (hSmap₁ (Subgroup.mem_map_of_mem f' ht))
  have hTK₂ : D.T.subgroupOf H ≤ K₂ := fun t ht =>
    Subgroup.mem_comap.mpr (hSmap₂ (Subgroup.mem_map_of_mem f' ht))
  have hTK₃ : D.T.subgroupOf H ≤ K₃ := fun t ht =>
    Subgroup.mem_comap.mpr (hSmap₃ (Subgroup.mem_map_of_mem f' ht))
  have hkerle : f'.ker ≤ K₁ ⊔ K₂ ⊔ K₃ := fun x hx =>
    Subgroup.mem_sup_left (Subgroup.mem_sup_left (Subgroup.mem_comap.mpr (by
      rw [MonoidHom.mem_ker.mp hx]
      exact P₁.one_mem)))
  have hjoinK : K₁ ⊔ K₂ ⊔ K₃ = ⊤ := by
    have hmap : (K₁ ⊔ K₂ ⊔ K₃).map f' = ⊤ := by
      rw [Subgroup.map_sup, Subgroup.map_sup,
        Subgroup.map_comap_eq_self_of_surjective hf'surj,
        Subgroup.map_comap_eq_self_of_surjective hf'surj,
        Subgroup.map_comap_eq_self_of_surjective hf'surj, hsup]
    have h := Subgroup.comap_map_eq_self hkerle
    rw [hmap, Subgroup.comap_top] at h
    exact h.symm
  have hFSK₁ : CFSG.LocalAnalysis.WeakClosure81.InFSq 1 K₁ := by
    obtain ⟨e⟩ := bar2_comap_mulEquiv f' hf'surj hker2 P₁
    exact (CFSG.LocalAnalysis.WeakClosure81.inFSq_iff_bar2_inF_mulEquiv e 1).mpr hFS₁
  have hFSK₂ : CFSG.LocalAnalysis.WeakClosure81.InFSq 1 K₂ := by
    obtain ⟨e⟩ := bar2_comap_mulEquiv f' hf'surj hker2 P₂
    exact (CFSG.LocalAnalysis.WeakClosure81.inFSq_iff_bar2_inF_mulEquiv e 1).mpr hFS₂
  have hFSK₃ : CFSG.LocalAnalysis.WeakClosure81.InFSq 1 K₃ := by
    obtain ⟨e⟩ := bar2_comap_mulEquiv f' hf'surj hker2 P₃
    exact (CFSG.LocalAnalysis.WeakClosure81.inFSq_iff_bar2_inF_mulEquiv e 1).mpr hFS₃
  refine ⟨K₁.map H.subtype, K₂.map H.subtype, K₃.map H.subtype, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · calc D.T = (D.T.subgroupOf H).map H.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le (le_sup_right : D.T ≤ L ⊔ D.T)).symm
      _ ≤ K₁.map H.subtype := Subgroup.map_mono hTK₁
  · calc D.T = (D.T.subgroupOf H).map H.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le (le_sup_right : D.T ≤ L ⊔ D.T)).symm
      _ ≤ K₂.map H.subtype := Subgroup.map_mono hTK₂
  · calc D.T = (D.T.subgroupOf H).map H.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le (le_sup_right : D.T ≤ L ⊔ D.T)).symm
      _ ≤ K₃.map H.subtype := Subgroup.map_mono hTK₃
  · exact Subgroup.map_subtype_le K₁
  · exact Subgroup.map_subtype_le K₂
  · exact Subgroup.map_subtype_le K₃
  · obtain ⟨e⟩ := nonempty_bar2_mulEquiv_map_subtype K₁
    exact (CFSG.LocalAnalysis.WeakClosure81.inFSq_iff_bar2_inF_mulEquiv e 1).mp hFSK₁
  · obtain ⟨e⟩ := nonempty_bar2_mulEquiv_map_subtype K₂
    exact (CFSG.LocalAnalysis.WeakClosure81.inFSq_iff_bar2_inF_mulEquiv e 1).mp hFSK₂
  · obtain ⟨e⟩ := nonempty_bar2_mulEquiv_map_subtype K₃
    exact (CFSG.LocalAnalysis.WeakClosure81.inFSq_iff_bar2_inF_mulEquiv e 1).mp hFSK₃
  · calc K₁.map H.subtype ⊔ K₂.map H.subtype ⊔ K₃.map H.subtype =
        (K₁ ⊔ K₂ ⊔ K₃).map H.subtype := by rw [Subgroup.map_sup, Subgroup.map_sup]
      _ = (⊤ : Subgroup ↥H).map H.subtype := by rw [hjoinK]
      _ = H := by rw [Subgroup.map_top, Subgroup.range_subtype]
      _ = L ⊔ D.T := rfl

theorem exists_delta_of_isHe (hKS9 : Inputs1719.K_HeParabolics)
    (D : Data G) (V₀ V : Subgroup G) :
    ∀ L : Subgroup G, Ctx17_17 D V₀ V L → (L.subgroupOf D.M).Normal →
      IsSpor (Bar2 L) .He →
      ∃ H₁ H₂ H₃ : Subgroup G,
        D.T ≤ H₁ ∧ D.T ≤ H₂ ∧ D.T ≤ H₃ ∧
          H₁ ≤ L ⊔ D.T ∧ H₂ ≤ L ⊔ D.T ∧ H₃ ≤ L ⊔ D.T ∧
            CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₁ ∧
              CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₂ ∧
                CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₃ ∧
                  H₁ ⊔ H₂ ⊔ H₃ = L ⊔ D.T := by
  intro L c hN hspor
  exact exists_He_of_calC (D := D) (L := L) c.mem_calC
    (Tbar_le_normalizer_K1 (D := D) (L := L) hN) (fun Y _ _ K S hKY hKe => by
      obtain ⟨eK⟩ := hKe
      obtain ⟨eB⟩ := hspor
      exact hKS9 Y K hKY.1 hKY.2.1 hKY.2.2.1 ⟨eK.trans eB⟩ hKY.2.2.2.1 hKY.2.2.2.2.1 S
        hKY.2.2.2.2.2)

@[expose] def B17_23Bound (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V) : Prop :=
  ∀ L : Subgroup G, Ctx17_17 D V₀ V L → (L.subgroupOf D.M).Normal → IsSpor (Bar2 L) .He →
    D.k = 2 → barSub V₀ V hV.isElemAbelian L ≠ ⊥ → UniqueMax D.M (L ⊔ D.T) →
    (fixV (barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L)) = ⊥ ∨
      (V₀ = ⊥ ∧ ClassicalEvenAltG2Der (UC22.Bar2 L))) →
    ∀ H₁ H₂ H₃ : Subgroup G, D.T ≤ H₁ → D.T ≤ H₂ → D.T ≤ H₃ →
      H₁ ≤ L ⊔ D.T → H₂ ≤ L ⊔ D.T → H₃ ≤ L ⊔ D.T →
      CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₁ →
      CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₂ →
      CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₃ →
      H₁ ⊔ H₂ ⊔ H₃ = L ⊔ D.T →
        bBar L D.M V₀ V hV.isElemAbelian ≤ 3 ∧ 10 ≤ mBar D.M V₀ V hV.isElemAbelian

section Certified


theorem seventeen_twentythree (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (h17_20 : R17_20At D V₀ V) (h17_21 : R17_21At D V₀ V) (h17_22 : R17_22At D V₀ V)
    (h869 : F08.R869 D) (h127 : R127 D)
    (h640 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_40_2 D) (hFF : W4Thm12McClurg)
    (hx : DataExt D) (h61 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_1 D)
    (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (h126 : R126 D) (h111 : W3Thm111 G)
    (hB23 : B17_23Bound D V₀ V hV)
    (hKS9 : Inputs1719.K_HeParabolics) :
    R17_23At D V₀ V := by
  classical
  intro L c
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 L
  rcases h17_22 L P (centerOf P) c hP rfl with hHeL | ⟨hJ2, -⟩
  · exfalso
    have hk : D.k = 2 := h17_21 L c
    obtain ⟨-, hN, -⟩ := h17_20 L c
    have hnt : ¬ F08.Thin8 L := by
      refine Inputs1719.not_thin_of_pRank_three ?_
      have hm3 : pRank 3 L = 2 := (h17_20 L c).1
      rw [← CFSG.Quasithin.BlueprintB2.pRank_eq_open_pRank]
      omega
    have hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥ :=
      barSub_ne_bot_of_not_thin hV
        (ElevenNine.c117_of_hyp11 D h869 (Hyp125.hyp11 h127 hV)) c.mem_calC hnt
    have hconj : UC22.conjClosure D.M L = L :=
      Inputs1719.conjClosure_eq_self_of_normal c.mem_calC.1.le hN
    obtain ⟨H₁, H₂, H₃, hT₁, hT₂, hT₃, hH₁, hH₂, hH₃, hFS₁, hFS₂, hFS₃,
      hgen⟩ := exists_delta_of_isHe hKS9 D V₀ V L c hN hHeL
    have hHM₁ : H₁ ≤ D.M := hH₁.trans (sup_le c.mem_calC.1.le D.sylowM.le)
    have hHM₂ : H₂ ≤ D.M := hH₂.trans (sup_le c.mem_calC.1.le D.sylowM.le)
    have hHM₃ : H₃ ≤ D.M := hH₃.trans (sup_le c.mem_calC.1.le D.sylowM.le)
    have hUL : UniqueMax D.M (L ⊔ D.T) :=
      Inputs1719.uniqueMax_sup_T_of_not_thin h869 c.mem_calC hnt
    set Δ : Finset (Subgroup G) := {H₁, H₂, H₃} with hΔdef
    have hΔ : ∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M := by
      intro H hH
      simp only [Δ, Finset.mem_insert, Finset.mem_singleton] at hH
      rcases hH with rfl | rfl | rfl
      · exact ⟨hT₁, hHM₁⟩
      · exact ⟨hT₂, hHM₂⟩
      · exact ⟨hT₃, hHM₃⟩
    have hsupeq : (⨆ H ∈ Δ, H) = H₁ ⊔ H₂ ⊔ H₃ := by
      refine le_antisymm (iSup₂_le fun H hH => ?_) ?_
      · simp only [Δ, Finset.mem_insert, Finset.mem_singleton] at hH
        rcases hH with rfl | rfl | rfl
        · exact le_trans le_sup_left le_sup_left
        · exact le_trans le_sup_right le_sup_left
        · exact le_sup_right
      · refine sup_le (sup_le ?_ ?_) ?_
        · exact le_iSup₂_of_le H₁ (by simp [Δ]) le_rfl
        · exact le_iSup₂_of_le H₂ (by simp [Δ]) le_rfl
        · exact le_iSup₂_of_le H₃ (by simp [Δ]) le_rfl
    have hΔU : UniqueMax D.M (⨆ H ∈ Δ, H) := by
      rw [hsupeq, hgen]
      exact hUL
    have hι : ∀ H ∈ Δ, CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H := by
      intro H hH
      simp only [Δ, Finset.mem_insert, Finset.mem_singleton] at hH
      rcases hH with rfl | rfl | rfl
      · exact hFS₁
      · exact hFS₂
      · exact hFS₃
    obtain ⟨hb, hm⟩ := hB23 L c hN hHeL hk hL1 hUL
      (fixV_dichotomy_of_not_thin D h869 h127 h640 hFF hV c.mem_calC hnt)
      H₁ H₂ H₃ hT₁ hT₂ hT₃ hH₁ hH₂ hH₃ hFS₁ hFS₂ hFS₃ hgen
    have hsum : Δ.sum (fun _ => 1) ≤ 3 := by
      have h1 : Δ.sum (fun _ => 1) = Δ.card := by simp
      have hcard : Δ.card ≤ 3 := by
        rw [hΔdef]
        have h2 := Finset.card_insert_le H₁ ({H₂, H₃} : Finset (Subgroup G))
        have h3 := Finset.card_insert_le H₂ ({H₃} : Finset (Subgroup G))
        have h4 : ({H₃} : Finset (Subgroup G)).card = 1 := by simp
        omega
      omega
    by_cases hV0 : V₀ = ⊥
    · have h1 := twelve_twentyThree_one D hx h61 h126 h111 hV hV0
        c.mem_calC.1 c.mem_calC.2.2 hL1
        (uniqueMax_conjClosure_of_not_thin h869 c.mem_calC hnt)
      rw [hconj] at h1
      omega
    · have h2 := twelve_twentyThree_two D hx h61 h127 h1114 h162 hTor h1482 h126 hV hV0
        c.mem_calC.1 c.mem_calC.2.2 hL1 hΔ hΔU (fun _ => 1) hι
      rw [hconj] at h2
      omega
  · exact hJ2

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
