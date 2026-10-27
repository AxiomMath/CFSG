module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABG
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoSyl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154LemmaMc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_sl28_seven_z_normalizer_of_C
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    (h7 : 7 ∈ D.sig)
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L)
    (hZ0 : wSub ⊥ V h.hyp151.isElemAbelian L ⊓
        conjSubgroup (wSub ⊥ V h.hyp151.isElemAbelian L) x =
      wSub ⊥ V h.hyp151.isElemAbelian L ⊓ Subgroup.centralizer (L : Set G))
    (hE : ∃ E : Subgroup G, E ≤ D.M ∧
      E ≤ Subgroup.centralizer
        ((wSub ⊥ V h.hyp151.isElemAbelian L ⊓
          Subgroup.centralizer (L : Set G)) : Set G) ∧
      IsElemAbelian 7 E ∧ Nat.card E = 7 ^ 2) :
    ∃ P : Subgroup G,
      P ≤ D.M ⊓ normalizer
        ((D.T ⊓ centralizer
          ((wSub ⊥ V h.hyp151.isElemAbelian L ⊓
            Subgroup.centralizer (L : Set G)) : Set G) : Subgroup G) : Set G) ∧
      IsPGroup 7 P ∧ ¬ IsCyclic ↥P := by
  have hV := h.hyp151.isElemAbelian
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMΓ : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  have hTΓ : D.T ≤ stabTil ⊥ V := D.sylowM.le.trans hMΓ
  have hTM : D.T.subgroupOf (stabTil ⊥ V) ≤ D.M.subgroupOf (stabTil ⊥ V) :=
    Subgroup.subgroupOf_mono (stabTil ⊥ V) D.sylowM.le
  have hT' : CFSG.ABGLocalTools.IsSylowOf 2 (D.T.subgroupOf (stabTil ⊥ V))
      (D.M.subgroupOf (stabTil ⊥ V)) := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff (stabTil ⊥ V)]
    rw [Subgroup.map_subgroupOf_eq_of_le hTΓ, Subgroup.map_subgroupOf_eq_of_le hMΓ]
    exact D.sylowM
  let Zt : Subgroup (Vtil ⊥ V hV) :=
    commSub ⊤ (lBar ⊥ V hV L) ⊓ fixV (lBar ⊥ V hV L)
  let Z : Subgroup G := wSub ⊥ V hV L ⊓ Subgroup.centralizer (L : Set G)
  have hZpre : Z = preTil ⊥ V hV Zt := s16h_wSub_inf_centralizer_eq_preTil D h
  let Tbar : Subgroup (MulAut (Vtil ⊥ V hV)) :=
    (D.T.subgroupOf (stabTil ⊥ V)).map (actTil ⊥ V hV)
  let B : Subgroup (MulAut (Vtil ⊥ V hV)) := Tbar ⊓ centSub Zt
  have hTbar : CFSG.ABGLocalTools.IsSylowOf 2 Tbar (Mbar D.M ⊥ V hV) :=
    s16c7_isSylowOf_map hT' (actTil ⊥ V hV)
  obtain ⟨E, hEMbar, hE7, hEnc, hEnorm⟩ :=
    s16h_sl28_seven_normalizer_bar D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ
      hbad hrow hZ4 h7 hxM hxn Tbar hTbar
  have hB : B ≤ Tbar := inf_le_left
  have hE : E ≤ Mbar D.M ⊥ V hV := hEMbar
  have hEB : E ≤ Subgroup.normalizer (B : Set (MulAut (Vtil ⊥ V hV))) := hEnorm
  obtain ⟨P, hPle, hP7, hPnc⟩ :=
    s16h_frattini_lift_noncyclic_seven (Γ := ↥(stabTil ⊥ V))
      (Q := MulAut (Vtil ⊥ V hV)) (actTil ⊥ V hV) hTM hT' (B := B) (E := E)
      hB hE hEB hE7 hEnc
  let H : Subgroup ↥(stabTil ⊥ V) :=
    (D.T.subgroupOf (stabTil ⊥ V)) ⊓ B.comap (actTil ⊥ V hV)
  have hPleH : P ≤ (D.M.subgroupOf (stabTil ⊥ V)) ⊓
      Subgroup.normalizer (H : Set ↥(stabTil ⊥ V)) := hPle
  have hHmap : H.map (stabTil ⊥ V).subtype = D.T ⊓ Subgroup.centralizer (Z : Set G) := by
    dsimp only [H]
    rw [Subgroup.map_inf _ _ _ (Subgroup.subtype_injective (stabTil ⊥ V)),
      Subgroup.map_subgroupOf_eq_of_le hTΓ]
    apply le_antisymm
    · intro y hy
      rw [Subgroup.mem_inf] at hy
      rw [Subgroup.mem_inf]
      refine ⟨hy.1, ?_⟩
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hy.2
      have hzcent : (actTil ⊥ V hV) z ∈ centSub Zt := by
        have hzB : (actTil ⊥ V hV) z ∈ B := hz
        exact (Subgroup.mem_inf.1 (show (actTil ⊥ V hV) z ∈ Tbar ⊓ centSub Zt from hzB)).2
      have hzy' : z = ⟨y, hTΓ hy.1⟩ := Subtype.ext hzy
      have hzcent' : (actTil ⊥ V hV) ⟨y, hTΓ hy.1⟩ ∈ centSub Zt := by
        rwa [hzy'] at hzcent
      have hyPre : y ∈ Subgroup.centralizer (preTil ⊥ V hV Zt) :=
        (s16h_mem_centralizer_preTil_iff hV hTΓ Zt hy.1).mpr hzcent'
      rwa [← hZpre] at hyPre
    · intro y hy
      rw [Subgroup.mem_inf] at hy
      rw [Subgroup.mem_inf]
      refine ⟨hy.1, ?_⟩
      have hyPre : y ∈ Subgroup.centralizer (preTil ⊥ V hV Zt) := by
        rw [hZpre] at hy
        exact hy.2
      have hycent : (actTil ⊥ V hV) ⟨y, hTΓ hy.1⟩ ∈ centSub Zt :=
        (s16h_mem_centralizer_preTil_iff hV hTΓ Zt hy.1).mp hyPre
      refine Subgroup.mem_map.2 ⟨⟨y, hTΓ hy.1⟩, ?_, rfl⟩
      show (actTil ⊥ V hV) ⟨y, hTΓ hy.1⟩ ∈ Tbar ⊓ centSub Zt
      exact ⟨Subgroup.mem_map_of_mem (actTil ⊥ V hV)
        (Subgroup.mem_subgroupOf.2 hy.1), hycent⟩
  refine ⟨P.map (stabTil ⊥ V).subtype, ?_, hP7.map (stabTil ⊥ V).subtype, ?_⟩
  · calc P.map (stabTil ⊥ V).subtype
        ≤ ((D.M.subgroupOf (stabTil ⊥ V)) ⊓
            Subgroup.normalizer (H : Set ↥(stabTil ⊥ V))).map
            (stabTil ⊥ V).subtype := Subgroup.map_mono hPleH
      _ = (D.M.subgroupOf (stabTil ⊥ V)).map (stabTil ⊥ V).subtype ⊓
            (Subgroup.normalizer (H : Set ↥(stabTil ⊥ V))).map
              (stabTil ⊥ V).subtype :=
            Subgroup.map_inf _ _ _ (Subgroup.subtype_injective (stabTil ⊥ V))
      _ ≤ (D.M.subgroupOf (stabTil ⊥ V)).map (stabTil ⊥ V).subtype ⊓
            Subgroup.normalizer (H.map (stabTil ⊥ V).subtype) :=
            inf_le_inf_left _ (Subgroup.le_normalizer_map (stabTil ⊥ V).subtype)
      _ = D.M ⊓ Subgroup.normalizer
            ((D.T ⊓ Subgroup.centralizer (Z : Set G) : Subgroup G) : Set G) := by
            rw [Subgroup.map_subgroupOf_eq_of_le hMΓ, hHmap]
  · intro hcyc
    haveI : IsCyclic ↥(P.map (stabTil ⊥ V).subtype) := hcyc
    exact hPnc (isCyclic_of_injective
      (Subgroup.equivMapOfInjective P (stabTil ⊥ V).subtype
        (Subgroup.subtype_injective (stabTil ⊥ V))).toMonoidHom
      (Subgroup.equivMapOfInjective P (stabTil ⊥ V).subtype
        (Subgroup.subtype_injective (stabTil ⊥ V))).injective)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
