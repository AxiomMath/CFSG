module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InP11OfStrongly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.TwoQuotientTransfers
public import CFSG.GroupTheory.StronglyEmbeddedTwoResidual
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFourBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def B17_21Bound (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V) : Prop :=
  ∀ L : Subgroup G, L ∈ calC D.M → (L.subgroupOf D.M).Normal → D.k = 1 →
    (IsSpor (BarInf L) .HS ∨ IsSpor (BarInf L) .Ru) →
    bBar L D.M V₀ V hV.isElemAbelian + 3 < mBar D.M V₀ V hV.isElemAbelian

@[expose] def Gap17_21_M22 (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L : Subgroup G, Ctx17_17 D V₀ V L → D.k = 1 → IsSpor (BarInf L) .M22 → False

theorem K1_normal_of_normal {D : Data G} {L : Subgroup G}
    (hN : (L.subgroupOf D.M).Normal) : (K1Nine D L).Normal :=
  Subgroup.Normal.map hN (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))
    (QuotientGroup.mk'_surjective _)

theorem Tbar_le_normalizer_K1 {D : Data G} {L : Subgroup G}
    (hN : (L.subgroupOf D.M).Normal) :
    Tbar9 D ≤ Subgroup.normalizer (K1Nine D L : Set (Mbar9 D)) := by
  have hK1 : (K1Nine D L).Normal := K1_normal_of_normal (D := D) (L := L) hN
  exact (Subgroup.normalizer_eq_top_iff (H := K1Nine D L)).mpr hK1 ▸ le_top

theorem exists_s3_pair_of_calC_bar2_of_pow {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hnorm : Tbar9 D ≤ Subgroup.normalizer (K1Nine D L : Set (Mbar9 D))) {n : ℕ}
    (hpow : ∀ s ∈ S1Nine D L, s ^ n ∈ Subgroup.centralizer (K1Nine D L : Set (Mbar9 D)))
    (hpair : ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y),
      Inputs1719.KYForm Y K S → Nonempty (↥K ≃* Bar2 L) → (∀ s ∈ S, s ^ n = 1) →
      ∃ P₁ P₂ : Subgroup Y, S ≤ P₁ ∧ S ≤ P₂ ∧ P₁ ⊔ P₂ = ⊤ ∧
        Nonempty (Bar2 P₁ ≃* Equiv.Perm (Fin 3)) ∧
        Nonempty (Bar2 P₂ ≃* Equiv.Perm (Fin 3))) :
    ∃ L₁ L₂ : Subgroup G, D.T ≤ L₁ ∧ D.T ≤ L₂ ∧ L ⊔ D.T = L₁ ⊔ L₂ ∧
      Nonempty (Bar2 L₁ ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty (Bar2 L₂ ≃* Equiv.Perm (Fin 3)) := by
  obtain ⟨Y, hYgrp, hYfin, KY, SY, f', hky, hKYe, hf'surj, hker2, -, hTmap, hexpY⟩ :=
    exists_twoQuotient_lift hL hnorm
  obtain ⟨P₁, P₂, hSP₁, hSP₂, hsup, hq₁, hq₂⟩ :=
    hpair Y KY SY hky hKYe (hexpY n hpow)
  let H : Subgroup G := L ⊔ D.T
  have hSmap₁ : (D.T.subgroupOf H).map f' ≤ P₁ := by
    rw [show D.T.subgroupOf H = D.T.subgroupOf (L ⊔ D.T) from rfl, hTmap]
    exact hSP₁
  have hSmap₂ : (D.T.subgroupOf H).map f' ≤ P₂ := by
    rw [show D.T.subgroupOf H = D.T.subgroupOf (L ⊔ D.T) from rfl, hTmap]
    exact hSP₂
  obtain ⟨L₁, L₂, hT₁, hT₂, hsup', hq₁', hq₂'⟩ :=
    exists_s3_pair_comap f' hf'surj hker2 hSmap₁ hSmap₂ hsup hq₁ hq₂
  refine ⟨L₁.map H.subtype, L₂.map H.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · calc D.T = (D.T.subgroupOf H).map H.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le (le_sup_right : D.T ≤ L ⊔ D.T)).symm
      _ ≤ L₁.map H.subtype := Subgroup.map_mono hT₁
  · calc D.T = (D.T.subgroupOf H).map H.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le (le_sup_right : D.T ≤ L ⊔ D.T)).symm
      _ ≤ L₂.map H.subtype := Subgroup.map_mono hT₂
  · calc L ⊔ D.T = H := rfl
      _ = (⊤ : Subgroup ↥H).map H.subtype := by
          rw [Subgroup.map_top, Subgroup.range_subtype]
      _ = (L₁ ⊔ L₂).map H.subtype := by rw [hsup']
      _ = L₁.map H.subtype ⊔ L₂.map H.subtype := Subgroup.map_sup ..
  · obtain ⟨e⟩ := hq₁'
    obtain ⟨e2⟩ := nonempty_bar2_mulEquiv_map_subtype L₁
    exact ⟨e2.symm.trans e⟩
  · obtain ⟨e⟩ := hq₂'
    obtain ⟨e2⟩ := nonempty_bar2_mulEquiv_map_subtype L₂
    exact ⟨e2.symm.trans e⟩


theorem exists_s3_pair_of_calC_bar2 {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hnorm : Tbar9 D ≤ Subgroup.normalizer (K1Nine D L : Set (Mbar9 D)))
    (hpair : ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y),
      Inputs1719.KYForm Y K S → Nonempty (↥K ≃* Bar2 L) →
      ∃ P₁ P₂ : Subgroup Y, S ≤ P₁ ∧ S ≤ P₂ ∧ P₁ ⊔ P₂ = ⊤ ∧
        Nonempty (Bar2 P₁ ≃* Equiv.Perm (Fin 3)) ∧
        Nonempty (Bar2 P₂ ≃* Equiv.Perm (Fin 3))) :
    ∃ L₁ L₂ : Subgroup G, D.T ≤ L₁ ∧ D.T ≤ L₂ ∧ L ⊔ D.T = L₁ ⊔ L₂ ∧
      Nonempty (Bar2 L₁ ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty (Bar2 L₂ ≃* Equiv.Perm (Fin 3)) :=
  exists_s3_pair_of_calC_bar2_of_pow hL hnorm (n := 0) (fun _ _ => by simp)
    (fun Y _ _ K S hKY hKe _ => hpair Y K S hKY hKe)

theorem exists_HSRu_of_calC {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M)
    (hnorm : Tbar9 D ≤ Subgroup.normalizer (K1Nine D L : Set (Mbar9 D)))
    (hfact : ∀ (Y : Type) [Group Y] [Finite Y] (K S : Subgroup Y),
      Inputs1719.KYForm Y K S → Nonempty (↥K ≃* Bar2 L) →
      ∃ H₁ H₂ : Subgroup Y, S ≤ H₁ ∧ S ≤ H₂ ∧ H₁ ⊔ H₂ = ⊤ ∧
        CFSG.LocalAnalysis.WeakClosure81.InFSq 2 H₁ ∧
          CFSG.LocalAnalysis.WeakClosure81.InFSq 2 H₂ ∧
            3 ∣ Nat.card ↥H₁ ∧ 3 ∣ Nat.card ↥H₂) :
    ∃ H₁ H₂ : Subgroup G, D.T ≤ H₁ ∧ D.T ≤ H₂ ∧ H₁ ≤ L ⊔ D.T ∧ H₂ ≤ L ⊔ D.T ∧
      H₁ ⊔ H₂ = L ⊔ D.T ∧
      CFSG.LocalAnalysis.WeakClosure81.InFSq 2 H₁ ∧
        CFSG.LocalAnalysis.WeakClosure81.InFSq 2 H₂ ∧
          3 ∣ Nat.card ↥H₁ ∧ 3 ∣ Nat.card ↥H₂ := by
  exact exists_pair_of_calC_of_bar2Inv hL hnorm
    (fun X _ _ H => CFSG.LocalAnalysis.WeakClosure81.InFSq 2 H)
    (fun _ _ _ _ _ _ _ _ ⟨e⟩ =>
      CFSG.LocalAnalysis.WeakClosure81.inFSq_iff_bar2_inF_mulEquiv e 2) hfact


theorem gap17_21_M12Pair (hKS6 : Inputs1719.K_M12SThreePair)
    (D : Data G) (V₀ V : Subgroup G) :
    ∀ L : Subgroup G, Ctx17_17 D V₀ V L → (L.subgroupOf D.M).Normal →
      IsSpor (BarInf L) .M12 →
      ∃ L₁ L₂ : Subgroup G, D.T ≤ L₁ ∧ D.T ≤ L₂ ∧ L₁ ⊔ L₂ = L ⊔ D.T ∧
        Nonempty (Bar2 L₁ ≃* Equiv.Perm (Fin 3)) ∧
          Nonempty (Bar2 L₂ ≃* Equiv.Perm (Fin 3)) := by
  intro L c hN hspor
  obtain ⟨L₁, L₂, hT₁, hT₂, hsup, hq₁, hq₂⟩ :=
    exists_s3_pair_of_calC_bar2 (D := D) (L := L) c.mem_calC
      (Tbar_le_normalizer_K1 (D := D) (L := L) hN) (fun Y _ _ K S hKY hKe => by
        have hiso : IsSpor (↥K ⧸ Subgroup.center ↥K) .M12 := by
          obtain ⟨eK⟩ := hKe
          obtain ⟨eI⟩ := uc22p21k_barInf_equiv_of_calC c.mem_calC
          obtain ⟨eB⟩ := hspor
          exact ⟨(QuotientGroup.congr _ _ eK (Subgroup.map_center_eq eK)).trans
            (eI.symm.trans eB)⟩
        exact hKS6 Y K hKY.1 hKY.2.1 hKY.2.2.1 hiso hKY.2.2.2.1 hKY.2.2.2.2.1 S
          hKY.2.2.2.2.2)
  exact ⟨L₁, L₂, hT₁, hT₂, hsup.symm, hq₁, hq₂⟩

theorem gap17_21_HSRuParabolics (hKS7 : Inputs1719.K_HSRuParabolics)
    (D : Data G) (V₀ V : Subgroup G) :
    ∀ L : Subgroup G, Ctx17_17 D V₀ V L → (L.subgroupOf D.M).Normal →
      (IsSpor (BarInf L) .HS ∨ IsSpor (BarInf L) .Ru) →
      ∃ H₁ H₂ : Subgroup G, D.T ≤ H₁ ∧ D.T ≤ H₂ ∧ H₁ ≤ L ⊔ D.T ∧ H₂ ≤ L ⊔ D.T ∧
        H₁ ⊔ H₂ = L ⊔ D.T ∧
        CFSG.LocalAnalysis.WeakClosure81.InFSq 2 H₁ ∧
          CFSG.LocalAnalysis.WeakClosure81.InFSq 2 H₂ ∧
            3 ∣ Nat.card ↥H₁ ∧ 3 ∣ Nat.card ↥H₂ := by
  intro L c hN hspor
  refine exists_HSRu_of_calC (D := D) (L := L) c.mem_calC
    (Tbar_le_normalizer_K1 (D := D) (L := L) hN) (fun Y _ _ K S hKY hKe => ?_)
  obtain ⟨eK⟩ := hKe
  obtain ⟨eI⟩ := uc22p21k_barInf_equiv_of_calC c.mem_calC
  have hiso : IsSpor (↥K ⧸ Subgroup.center ↥K) .HS ∨
      IsSpor (↥K ⧸ Subgroup.center ↥K) .Ru := by
    rcases hspor with hHS | hRu
    · obtain ⟨eB⟩ := hHS
      exact Or.inl ⟨(QuotientGroup.congr _ _ eK (Subgroup.map_center_eq eK)).trans
        (eI.symm.trans eB)⟩
    · obtain ⟨eB⟩ := hRu
      exact Or.inr ⟨(QuotientGroup.congr _ _ eK (Subgroup.map_center_eq eK)).trans
        (eI.symm.trans eB)⟩
  exact hKS7 Y K hKY.1 hKY.2.1 hKY.2.2.1 hiso hKY.2.2.2.1 hKY.2.2.2.2.1 S hKY.2.2.2.2.2


section Certified


theorem seventeen_twentyone (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (h17_1 : R17_1At D V₀ V hV) (h17_4 : R17_4AtA D V₀ V hV) (h17_20 : R17_20At D V₀ V)
    (h869 : F08.R869 D) (hC117 : C117 D V₀ V)
    (hKS5 : Inputs1719.K_SporadicNine)
    (hx : DataExt D) (h61 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_1 D)
    (h127 : R127 D) (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G)
    (h1482 : W3Lem148_2 G) (h126 : R126 D) (h111 : W3Thm111 G)
    (hB21 : B17_21Bound D V₀ V hV)
    (hKS6 : Inputs1719.K_M12SThreePair)
    (hKS7 : Inputs1719.K_HSRuParabolics)
    (hM22 : Gap17_21_M22 D V₀ V) :
    R17_21At D V₀ V := by
  classical
  intro L c
  by_contra hk2
  have hk : D.k = 1 := by
    have h1 := TwelveShort.one_le_k D
    have h2 := TwelveSeven.k_le_two D
    omega
  obtain ⟨hm3, hN, s, hslist, hspor⟩ := h17_20 L c
  have hsp3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
    by_contra h
    exact hk2 ((Data.k_eq_two_iff D).2 h)
  have hnt : ¬ F08.Thin8 L := by
    refine Inputs1719.not_thin_of_pRank_three ?_
    rw [← CFSG.Quasithin.BlueprintB2.pRank_eq_open_pRank]
    omega
  have hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥ := by
    by_cases hV0 : V₀ = ⊥
    · subst hV0
      exact barSub_ne_bot_of_not_thin_bot h869 h127 hV c.mem_calC hnt
    · exact barSub_ne_bot_of_not_thin hV hC117 c.mem_calC hnt
  have hSix : ∀ t : TauCeti.SporadicName,
      (t = .M11 ∨ t = .M23 ∨ t = .M24 ∨ t = .J2 ∨ t = .He ∨ t = .J4) →
      IsSpor (BarInf L) t → False := by
    intro t ht htsp
    have hX : ∃ X : Subgroup G, F11.InP11 D X := by
      obtain ⟨X, hXM, hXne, hXp, hXexp, hXnc, hXperm⟩ :=
        exists_permutes_three_of_calC (D := D) (L := L) c.mem_calC
          (fun Y _ _ K hKn hKq hKodd hKe hcent hidx S hS => by
            refine hKS5 Y K S ⟨hKn, hKq, hKodd, hcent, hidx, hS⟩ ⟨t, ht, ?_⟩
            obtain ⟨eK⟩ := hKe
            obtain ⟨eI⟩ := uc22p21k_barInf_equiv_of_calC c.mem_calC
            obtain ⟨eB⟩ := htsp
            exact ⟨(QuotientGroup.congr _ _ eK (Subgroup.map_center_eq eK)).trans
              (eI.symm.trans eB)⟩)
      exact ⟨X, inP11_of_strongly Nat.prime_three (by norm_num) hsp3 hXM hXp hXexp hXnc hXperm⟩
    exact hk2 (h17_1.2 hX).2.1
  have hHSRu : (IsSpor (BarInf L) .HS ∨ IsSpor (BarInf L) .Ru) → False := by
    intro hsp
    obtain ⟨H₁, H₂, hT₁, hT₂, hH₁, hH₂, hsup, hFS₁, hFS₂, h3₁, h3₂⟩ :=
      gap17_21_HSRuParabolics hKS7 D V₀ V L c hN (hsp)
    have hHM₁ : H₁ ≤ D.M := hH₁.trans (sup_le c.mem_calC.1.le D.sylowM.le)
    have hHM₂ : H₂ ≤ D.M := hH₂.trans (sup_le c.mem_calC.1.le D.sylowM.le)
    have hconj : UC22.conjClosure D.M L = L :=
      Inputs1719.conjClosure_eq_self_of_normal c.mem_calC.1.le hN
    have hUL : UniqueMax D.M (L ⊔ D.T) :=
      Inputs1719.uniqueMax_sup_T_of_not_thin h869 c.mem_calC hnt
    set Δ : Finset (Subgroup G) := {H₁, H₂} with hΔdef
    have hΔ : ∀ H ∈ Δ, D.T ≤ H ∧ H ≤ D.M := by
      intro H hH
      simp only [Δ, Finset.mem_insert, Finset.mem_singleton] at hH
      rcases hH with rfl | rfl
      · exact ⟨hT₁, hHM₁⟩
      · exact ⟨hT₂, hHM₂⟩
    have hsupeq : (⨆ H ∈ Δ, H) = H₁ ⊔ H₂ := by
      refine le_antisymm (iSup₂_le fun H hH => ?_) ?_
      · simp only [Δ, Finset.mem_insert, Finset.mem_singleton] at hH
        rcases hH with rfl | rfl
        · exact le_sup_left
        · exact le_sup_right
      · exact sup_le (le_iSup₂_of_le H₁ (by simp [Δ]) le_rfl)
          (le_iSup₂_of_le H₂ (by simp [Δ]) le_rfl)
    have hΔU : UniqueMax D.M (⨆ H ∈ Δ, H) := by
      rw [hsupeq, hsup]
      exact hUL
    have hι : ∀ H ∈ Δ, CFSG.LocalAnalysis.WeakClosure81.InFSq ((fun _ => 2) H) H := by
      intro H hH
      simp only [Δ, Finset.mem_insert, Finset.mem_singleton] at hH
      rcases hH with rfl | rfl
      · exact hFS₁
      · exact hFS₂
    have hO2 : ∀ H ∈ Δ, ∀ g : G, g ∉ D.M → ¬ twoResidual H ≤ conjSubgroup D.M g := by
      intro H hH
      simp only [Δ, Finset.mem_insert, Finset.mem_singleton] at hH
      rcases hH with rfl | rfl
      · exact CFSG.GroupTheory.twoResidual_not_le_conjSubgroup_of_isStronglyPEmbedded
          Nat.prime_three (by norm_num) hHM₁ h3₁ hsp3
      · exact CFSG.GroupTheory.twoResidual_not_le_conjSubgroup_of_isStronglyPEmbedded
          Nat.prime_three (by norm_num) hHM₂ h3₂ hsp3
    have hb := hB21 L c.mem_calC hN hk (hsp)
    by_cases hV0 : V₀ = ⊥
    · have h1 := twelve_twentyThree_one D hx h61 h126 h111 hV hV0
          c.mem_calC.1 c.mem_calC.2.2 hL1
          (uniqueMax_conjClosure_of_not_thin h869 c.mem_calC hnt)
      rw [hconj] at h1
      omega
    · have h3 := twelve_twentyThree_three D hx h61 h127 h1114 h162 hTor h1482 h126 hV hV0
          c.mem_calC.1 c.mem_calC.2.2 hL1 hΔ hΔU (fun _ => 2) hι hO2
      rw [hconj] at h3
      have hsup2 : Δ.sup (fun _ => 2) ≤ 2 := Finset.sup_le fun _ _ => le_rfl
      omega

  rcases hslist with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hSix .M11 (by simp) hspor).elim
  ·
    obtain ⟨L₁, L₂, hT₁, hT₂, hsup, hb₁, hb₂⟩ :=
      gap17_21_M12Pair hKS6 D V₀ V L c hN hspor
    have hTL : D.T ≤ Subgroup.normalizer (L : Set G) :=
      D.sylowM.le.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer c.mem_calC.1.le).1 hN)
    have hST : D.T ⊓ Subgroup.normalizer (L : Set G) = D.T := inf_eq_left.mpr hTL
    have hcomp : barSub V₀ V hV.isElemAbelian L ∈ compBar D.M V₀ V hV.isElemAbelian :=
      barSub_mem_compBar_of_ne_bot hV c.mem_calC hL1
    have hU : UniqueMax D.M (L ⊔ D.T) :=
      Inputs1719.uniqueMax_sup_T_of_not_thin h869 c.mem_calC hnt
    exact (hk2 (h17_4 L L₁ L₂ c.mem_calC hTL hcomp (by rw [hST]; exact hT₁)
      (by rw [hST]; exact hT₂) (by rw [hST]; exact hsup.symm) hb₁ hb₂ (Or.inl hN) hU)).elim
  · exact (hM22 L c hk hspor).elim
  · exact (hSix .M23 (by simp) hspor).elim
  · exact (hSix .M24 (by simp) hspor).elim
  · exact (hSix .J2 (by simp) hspor).elim
  · exact (hHSRu (Or.inl hspor)).elim
  · exact (hSix .He (by simp) hspor).elim
  · exact (hHSRu (Or.inr hspor)).elim
  · exact (hSix .J4 (by simp) hspor).elim

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
