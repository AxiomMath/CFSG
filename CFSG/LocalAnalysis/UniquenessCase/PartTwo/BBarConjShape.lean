module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BBarSevenSeven
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BBarDelta
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoLift
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22v
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82A10Sym
public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.Timmesfeld.RankOne.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def ACandLe (X : Type) [Group X] (m : ℕ) : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.Open.IsQuasisimple H →
    Odd (Nat.card (Subgroup.center H)) → Nonempty ((H ⧸ Subgroup.center H) ≃* X) →
      ∀ n : ℕ, Nonempty (Inputs1719.ACandidate H n) → n ≤ m

theorem ACandLe.of_mulEquiv {X X' : Type} [Group X] [Group X'] (e : X ≃* X') {m : ℕ}
    (h : ACandLe X m) : ACandLe X' m := by
  intro H _ _ hH hodd ⟨eH⟩ n hn
  exact h H hH hodd ⟨eH.trans e.symm⟩ n hn

theorem bParam_bot_left {W : Type*} [CommGroup W] (Y : Subgroup (MulAut W)) :
    bParam (⊥ : Subgroup (MulAut W)) Y = 0 := by
  unfold bParam
  have h : {k : ℕ | 0 < k ∧ ∃ A ∈ CFSG.Quasithin.E3.aSet k Y,
      ⁅(⊥ : Subgroup (MulAut W)), A⁆ ≠ ⊥} = ∅ := by
    ext k
    simp [Subgroup.commutator_bot_left]
  rw [h]
  exact (csSup_empty : sSup (∅ : Set ℕ) = 0)

theorem bBar_conjClosure_le_of_aCandLe {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h77 : Inputs1719.W4Lem7_7) {L : Subgroup G} (hL : L ∈ calC D.M) {m : ℕ}
    (hA : ACandLe (UC22.BarInf L) m) :
    bBar (UC22.conjClosure D.M L) D.M V₀ V hV.isElemAbelian ≤ m := by
  classical
  have hMS : D.M ≤ stabTil V₀ V :=
    le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀
  have hLstab : L ≤ stabTil V₀ V := hL.1.le.trans hMS
  have hKle : ∀ g : ↥D.M, L.map (MulAut.conj (g : G)).toMonoidHom ≤ stabTil V₀ V := by
    intro g
    calc L.map (MulAut.conj (g : G)).toMonoidHom
        ≤ D.M.map (MulAut.conj (g : G)).toMonoidHom := Subgroup.map_mono hL.1.le
      _ = D.M := Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer g.2)
      _ ≤ stabTil V₀ V := hMS
  by_cases hL1 : barSub V₀ V hV.isElemAbelian L = ⊥
  · have hbar : barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L) =
        ⨆ g : ↥D.M, barSub V₀ V hV.isElemAbelian
          (L.map (MulAut.conj (g : G)).toMonoidHom) := by
      rw [UC22.uc22br4_conjClosure_eq]
      exact barSub_iSup_of_le hV.isElemAbelian hKle
    have hbot : barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L) = ⊥ := by
      rw [hbar]
      refine iSup_eq_bot.2 fun g => ?_
      rw [TwelveTwentyThree.barSub_map_conj hV.isElemAbelian hLstab (hMS g.2), hL1,
        Subgroup.map_bot]
    rw [bBar, hbot, bParam_bot_left]
    exact Nat.zero_le m
  · refine bBar_conjClosure_le_of_candidate_bound_of_hyp125 hV hL h77 hL1 fun g n hn => ?_
    obtain ⟨c⟩ := hn
    have hKC : L.map (MulAut.conj (g : G)).toMonoidHom ∈ calC D.M :=
      UC22.uc22p2214_calC_of_mem_conjSetOf hL ⟨(g : G), g.2, rfl⟩
    have hKne : barSub V₀ V hV.isElemAbelian
        (L.map (MulAut.conj (g : G)).toMonoidHom) ≠ ⊥ := by
      rw [TwelveTwentyThree.barSub_map_conj hV.isElemAbelian hLstab (hMS g.2)]
      intro hbot
      exact hL1 ((Subgroup.map_eq_bot_iff_of_injective _
        (MulAut.conj (actTil V₀ V hV.isElemAbelian ⟨(g : G), hMS g.2⟩)).injective).1 hbot)
    have hHq : CFSG.Open.IsQuasisimple
        ↥(barSub V₀ V hV.isElemAbelian (L.map (MulAut.conj (g : G)).toMonoidHom)) :=
      (barSub_mem_compBar_of_ne_bot hV hKC hKne).2.2
    have hodd : Odd (Nat.card (Subgroup.center
        ↥(barSub V₀ V hV.isElemAbelian (L.map (MulAut.conj (g : G)).toMonoidHom)))) :=
      S17.odd_center_barSub hV hKC hKne
    obtain ⟨e₁⟩ := S17.barSub_centerQuot_equiv_barInf hV hKC hKne
    obtain ⟨e₂⟩ := UC22.uc22p20c_barInf_equiv_map L (g : G)
    exact hA _ hHq hodd ⟨e₁.symm.trans e₂.symm⟩ n ⟨c⟩

theorem aCandLe_of_inGq (h106 : Inputs1719.W4Lem10_6Q) {X : Type} [Group X] {q : ℕ}
    (hq : Inputs1719.InGq X q) (h3 : 3 < q) : ACandLe X 2 := by
  intro H _ _ hH hodd ⟨e⟩ n hn
  have hq' : Inputs1719.InGq (H ⧸ Subgroup.center H) q :=
    Inputs1719.InGq.of_mulEquiv hq e.symm
  exact (aCandidate_bounds_of_inGq h106 hH hodd hq' hn.some).2 h3

theorem inGq_nine_of_mulEquiv_alt_six {X : Type} [Group X]
    (e : X ≃* alternatingGroup (Fin 6)) : Inputs1719.InGq X 9 :=
  Or.inl ⟨.PSL, 2, 3, 2, Nat.prime_three, by norm_num, by norm_num, by norm_num,
    CFSG.Blueprint.LieModel.of_mulEquiv e.symm
      CFSG.ComponentClassification.GSThmB.Catalog82A10.lieModel_alternatingGroup_six⟩

theorem aCandLe_two_of_barO2Z17_A6 (h106 : Inputs1719.W4Lem10_6Q) {M L : Subgroup G}
    (hL : L ∈ calC M) (he : Nonempty (S17.BarO2Z17 L ≃* alternatingGroup (Fin 6))) :
    ACandLe (UC22.BarInf L) 2 := by
  obtain ⟨e₁⟩ := he
  obtain ⟨e₂⟩ := S17.barO2Z17_equiv_barInf hL
  exact aCandLe_of_inGq h106 (inGq_nine_of_mulEquiv_alt_six (e₂.symm.trans e₁)) (by norm_num)

theorem bBar_conjClosure_le_two_of_A6 {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h77 : Inputs1719.W4Lem7_7) (h106 : Inputs1719.W4Lem10_6Q) {L : Subgroup G}
    (hL : L ∈ calC D.M) (he : Nonempty (S17.BarO2Z17 L ≃* alternatingGroup (Fin 6))) :
    bBar (UC22.conjClosure D.M L) D.M V₀ V hV.isElemAbelian ≤ 2 :=
  bBar_conjClosure_le_of_aCandLe hV h77 hL (aCandLe_two_of_barO2Z17_A6 h106 hL he)

theorem exists_T_conj_eq_of_two_conj (D : Data G) {L : Subgroup G}
    (htri : ∀ x ∈ D.M, ∀ y ∈ D.M, L.map (MulAut.conj x).toMonoidHom = L ∨
      L.map (MulAut.conj y).toMonoidHom = L ∨
      L.map (MulAut.conj y).toMonoidHom = L.map (MulAut.conj x).toMonoidHom) :
    ∀ g ∈ D.M, ∃ t ∈ D.T,
      L.map (MulAut.conj g).toMonoidHom = L.map (MulAut.conj t).toMonoidHom := by
  classical
  intro g hg
  by_cases hgL : L.map (MulAut.conj g).toMonoidHom = L
  · exact ⟨1, D.T.one_mem,
      hgL.trans (CFSG.Timmesfeld.RankOne.map_conj_one L).symm⟩
  · let H : Subgroup ↥D.M :=
      { carrier := {x : ↥D.M | L.map (MulAut.conj ((x : ↥D.M) : G)).toMonoidHom = L}
        one_mem' := by
          simpa using CFSG.Timmesfeld.RankOne.map_conj_one L
        mul_mem' := by
          rintro x y hx hy
          change L.map (MulAut.conj ((x : G) * (y : G))).toMonoidHom = L
          rw [CFSG.Timmesfeld.RankOne.map_conj_mul, hy, hx]
        inv_mem' := by
          rintro x hx
          change L.map (MulAut.conj ((x : G)⁻¹)).toMonoidHom = L
          exact ((CFSG.Timmesfeld.RankOne.map_conj_eq_iff (H := L) (K := L)
            (g := (x : G))).1 hx).symm }
    have hHidx : H.index = 2 := by
      refine Subgroup.index_eq_two_iff_exists_notMem_and'.2
        ⟨((⟨g, hg⟩ : ↥D.M)⁻¹), ?_, ?_⟩
      · intro hmem
        exact hgL ((CFSG.Timmesfeld.RankOne.map_conj_eq_iff (H := L) (K := L)
          (g := (g : G))).2 hmem.symm)
      · intro b
        by_cases hb : b ∈ H
        · exact Or.inr hb
        · left
          have hbne : L.map (MulAut.conj (b : G)).toMonoidHom ≠ L := hb
          rcases htri (b : G) b.2 (g : G) hg with h1 | h2 | h3
          · exact absurd h1 hbne
          · exact absurd h2 hgL
          · change L.map (MulAut.conj ((((⟨g, hg⟩ : ↥D.M)⁻¹ * b : ↥D.M) : G))).toMonoidHom = L
            rw [show (((⟨g, hg⟩ : ↥D.M)⁻¹ * b : ↥D.M) : G) = (g : G)⁻¹ * (b : G) from rfl,
              CFSG.Timmesfeld.RankOne.map_conj_mul, ← h3]
            exact CFSG.Timmesfeld.RankOne.map_conj_inv_map_conj L (g : G)
    obtain ⟨Q, hQ⟩ := D.sylowM.exists_sylow_eq_subgroupOf
    have hnotle : ¬ (Q : Subgroup ↥D.M) ≤ H :=
      CFSG.QuasiDihedralFusion.sylow_not_le_of_index_two hHidx Q
    obtain ⟨t, htQ, htH⟩ := Set.not_subset.1 hnotle
    have htT : (t : G) ∈ D.T := by
      have ht : t ∈ D.T.subgroupOf D.M := by
        rw [← hQ]
        exact htQ
      exact (Subgroup.mem_subgroupOf).1 ht
    have htL : L.map (MulAut.conj (t : G)).toMonoidHom ≠ L := htH
    refine ⟨(t : G), htT, ?_⟩
    rcases htri (t : G) (D.sylowM.le htT) (g : G) hg with h1 | h2 | h3
    · exact absurd h1 htL
    · exact absurd h2 hgL
    · exact h3

theorem barSub_conjClosure_le_sup_T_of_transitive {D : Data G} {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) {L : Subgroup G} (hLM : L ≤ D.M)
    (htr : ∀ g ∈ D.M, ∃ t ∈ D.T,
      L.map (MulAut.conj g).toMonoidHom = L.map (MulAut.conj t).toMonoidHom) :
    barSub V₀ V hV.isElemAbelian (UC22.conjClosure D.M L) ≤
      barSub V₀ V hV.isElemAbelian L ⊔ barSub V₀ V hV.isElemAbelian D.T := by
  have hMS : D.M ≤ stabTil V₀ V :=
    le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀
  have hLstab : L ≤ stabTil V₀ V := hLM.trans hMS
  have hTstab : D.T ≤ stabTil V₀ V := D.sylowM.le.trans hMS
  have hKle : ∀ g : ↥D.M, L.map (MulAut.conj (g : G)).toMonoidHom ≤ stabTil V₀ V := by
    intro g
    calc L.map (MulAut.conj (g : G)).toMonoidHom
        ≤ D.M.map (MulAut.conj (g : G)).toMonoidHom := Subgroup.map_mono hLM
      _ = D.M := Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer g.2)
      _ ≤ stabTil V₀ V := hMS
  rw [UC22.uc22br4_conjClosure_eq, barSub_iSup_of_le hV.isElemAbelian hKle]
  refine iSup_le fun g => ?_
  obtain ⟨t, htT, ht⟩ := htr (g : G) g.2
  rw [ht]
  calc barSub V₀ V hV.isElemAbelian (L.map (MulAut.conj (t : G)).toMonoidHom)
      ≤ barSub V₀ V hV.isElemAbelian (L ⊔ D.T) := by
        refine barSub_mono V₀ V hV.isElemAbelian ?_
        rintro _ ⟨l, hl, rfl⟩
        have htK : (t : G) ∈ L ⊔ D.T := Subgroup.mem_sup_right htT
        have hlK : l ∈ L ⊔ D.T := Subgroup.mem_sup_left hl
        exact (L ⊔ D.T).mul_mem ((L ⊔ D.T).mul_mem htK hlK) ((L ⊔ D.T).inv_mem htK)
    _ = barSub V₀ V hV.isElemAbelian L ⊔ barSub V₀ V hV.isElemAbelian D.T :=
        s16c7_barSub_sup V₀ V hV.isElemAbelian hLstab hTstab

theorem bParam_le_of_le_iSup_conj {W : Type} [CommGroup W] [Finite W]
    {L T X Y : Subgroup (MulAut W)}
    (hTY : T ≤ Y)
    (hX : X ≤ ⨆ t ∈ T, L.map (MulAut.conj t).toMonoidHom) :
    bParam X Y ≤ bParam L Y := by
  classical
  by_contra h
  push Not at h
  have hkpos : 0 < bParam X Y := lt_of_le_of_lt (Nat.zero_le _) h
  obtain ⟨A, hA, hne⟩ := bParam_spec X Y hkpos
  have hExist : ∃ t ∈ T, ⁅L.map (MulAut.conj t).toMonoidHom, A⁆ ≠ ⊥ := by
    by_contra h'
    push Not at h'
    apply hne
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    refine hX.trans (iSup₂_le fun t ht => ?_)
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer).1 (h' t ht)
  obtain ⟨t, htT, htne⟩ := hExist
  have htY : t ∈ Y := hTY htT
  have hYconj : CFSG.Quasithin.conjAutSub t⁻¹ Y = Y := by
    rw [CFSG.Quasithin.conjAutSub]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.1
      (Subgroup.le_normalizer (Subgroup.inv_mem _ htY))
  have hA' : CFSG.Quasithin.conjAutSub t⁻¹ A ∈ E3.aSet (bParam X Y) Y := by
    have h := aSet_conjAutSub (g := t⁻¹) hA
    rwa [hYconj] at h
  have hne' : ⁅L, CFSG.Quasithin.conjAutSub t⁻¹ A⁆ ≠ ⊥ := by
    intro hbot
    apply htne
    have hmap : (⁅L, CFSG.Quasithin.conjAutSub t⁻¹ A⁆).map
        (MulAut.conj t).toMonoidHom = ⊥ := by
      rw [hbot, Subgroup.map_bot]
    rw [Subgroup.map_commutator] at hmap
    have hfix : (CFSG.Quasithin.conjAutSub t⁻¹ A).map
        (MulAut.conj t).toMonoidHom = A := by
      simpa [CFSG.Quasithin.conjAutSub] using
        CFSG.Timmesfeld.RankOne.map_conj_map_conj_inv A t
    rwa [hfix] at hmap
  exact absurd (le_bParam hkpos hA' hne') (not_le.2 h)

theorem bBar_conjClosure_le_bParam_sup_of_transitive {D : Data G} {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) {L : Subgroup G} (hLM : L ≤ D.M)
    (htr : ∀ g ∈ D.M, ∃ t ∈ D.T,
      L.map (MulAut.conj g).toMonoidHom = L.map (MulAut.conj t).toMonoidHom) :
    bBar (UC22.conjClosure D.M L) D.M V₀ V hV.isElemAbelian ≤
      bParam (barSub V₀ V hV.isElemAbelian L)
        (barSub V₀ V hV.isElemAbelian L ⊔ barSub V₀ V hV.isElemAbelian D.T) := by
  classical
  set hbarV := hV.isElemAbelian
  have hMS : D.M ≤ stabTil V₀ V :=
    le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀
  have hLstab : L ≤ stabTil V₀ V := hLM.trans hMS
  have hXle : UC22.conjClosure D.M L ≤ D.M :=
    UC22.uc22p22v_conjClosure_le (Subgroup.le_normalizer (H := D.M)) hLM
  have hMN : D.M ≤ Subgroup.normalizer (UC22.conjClosure D.M L : Set G) :=
    UC22.uc22p22v_le_normalizer_conjClosure D.M L
  have hXbarM : barSub V₀ V hbarV (UC22.conjClosure D.M L) ≤ Mbar D.M V₀ V hbarV :=
    barSub_mono V₀ V hbarV hXle
  have hNbar : Mbar D.M V₀ V hbarV ≤ Subgroup.normalizer
      (barSub V₀ V hbarV (UC22.conjClosure D.M L) :
        Set (MulAut (Vtil V₀ V hbarV))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXbarM).1
      (barSub_subgroupOf_mbar_normal hbarV hXle hMN)
  have hT : CFSG.Quasithin.IsSylowIn 2 D.T D.M :=
    (CFSG.ABGLocalTools.isSylowOf_iff (p := 2)).1 D.sylowM
  have hTsyl : CFSG.Quasithin.IsSylowIn 2 (barSub V₀ V hbarV D.T) (Mbar D.M V₀ V hbarV) :=
    s16c1_barSub_sylow (le_stabTil hV.pairFacts.le_normalizer
      hV.pairFacts.le_normalizer₀) hT
  have hstep1 : bParam (barSub V₀ V hbarV (UC22.conjClosure D.M L)) (Mbar D.M V₀ V hbarV) ≤
      bParam (barSub V₀ V hbarV (UC22.conjClosure D.M L))
        (barSub V₀ V hbarV (UC22.conjClosure D.M L) ⊔ barSub V₀ V hbarV D.T) :=
    bParam_le_of_normal hXbarM hNbar hTsyl
  have hsup : barSub V₀ V hbarV (UC22.conjClosure D.M L) ⊔ barSub V₀ V hbarV D.T =
      barSub V₀ V hbarV L ⊔ barSub V₀ V hbarV D.T := by
    refine le_antisymm ?_ ?_
    · exact sup_le (barSub_conjClosure_le_sup_T_of_transitive hV hLM htr) le_sup_right
    · exact sup_le_sup_right (barSub_mono V₀ V hbarV
        (TwelveTwentyThree.le_conjClosure D.M L)) _
  have hbar : barSub V₀ V hbarV (UC22.conjClosure D.M L) =
      ⨆ g : ↥D.M, barSub V₀ V hbarV (L.map (MulAut.conj (g : G)).toMonoidHom) := by
    rw [UC22.uc22br4_conjClosure_eq]
    exact barSub_iSup_of_le hbarV (fun g => by
      calc L.map (MulAut.conj (g : G)).toMonoidHom
          ≤ D.M.map (MulAut.conj (g : G)).toMonoidHom := Subgroup.map_mono hLM
        _ = D.M := Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer g.2)
        _ ≤ stabTil V₀ V := hMS)
  have hXsup : barSub V₀ V hbarV (UC22.conjClosure D.M L) ≤
      ⨆ t ∈ barSub V₀ V hbarV D.T,
        (barSub V₀ V hbarV L).map (MulAut.conj t).toMonoidHom := by
    rw [hbar]
    refine iSup_le fun g => ?_
    obtain ⟨t, htT, ht⟩ := htr (g : G) g.2
    have hts : (t : G) ∈ stabTil V₀ V := hMS (D.sylowM.le htT)
    rw [ht, s16c7_barSub_map_conj V₀ V hbarV hts L]
    exact le_iSup₂_of_le (actTil V₀ V hbarV ⟨(t : G), hts⟩)
      (actTil_mem_barSub V₀ V hbarV htT hts) le_rfl
  have hstep2 : bParam (barSub V₀ V hbarV (UC22.conjClosure D.M L))
      (barSub V₀ V hbarV L ⊔ barSub V₀ V hbarV D.T) ≤
      bParam (barSub V₀ V hbarV L) (barSub V₀ V hbarV L ⊔ barSub V₀ V hbarV D.T) :=
    bParam_le_of_le_iSup_conj le_sup_right hXsup
  calc bBar (UC22.conjClosure D.M L) D.M V₀ V hbarV
      = bParam (barSub V₀ V hbarV (UC22.conjClosure D.M L)) (Mbar D.M V₀ V hbarV) := rfl
    _ ≤ bParam (barSub V₀ V hbarV (UC22.conjClosure D.M L))
          (barSub V₀ V hbarV (UC22.conjClosure D.M L) ⊔ barSub V₀ V hbarV D.T) := hstep1
    _ = bParam (barSub V₀ V hbarV (UC22.conjClosure D.M L))
          (barSub V₀ V hbarV L ⊔ barSub V₀ V hbarV D.T) := by rw [hsup]
    _ ≤ bParam (barSub V₀ V hbarV L)
          (barSub V₀ V hbarV L ⊔ barSub V₀ V hbarV D.T) := hstep2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
