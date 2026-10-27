module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeSemiBotSpan
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

section Abstract

theorem s15_semiBot_eq_iSup_components {V : Type} [CommGroup V] [Finite V]
    {H : Subgroup (MulAut V)} (hF : Fstar H = H) (hfit : fittingOf H = ⊥) :
    ⨆ K ∈ {K : Subgroup (MulAut V) | IsComponentOf K H}, K = H := by
  have htop : CFSG.Open.genFittingFStar ↥H = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    change Fstar H = (⊤ : Subgroup ↥H).map H.subtype
    rw [hF, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hfit' : CFSG.fittingSubgroup ↥H = ⊥ := by
    have h := hfit
    unfold fittingOf at h
    exact (Subgroup.map_eq_bot_iff_of_injective (CFSG.fittingSubgroup ↥H)
      H.subtype_injective).1 h
  have hlayer : CFSG.Open.genFittingLayer ↥H = ⊤ := by
    have hsup := CFSG.Open.genFittingFStar.eq_sup ↥H
    rw [htop, show CFSG.Open.genFittingFitting ↥H = CFSG.fittingSubgroup ↥H from rfl,
      hfit'] at hsup
    simpa using hsup.symm
  have hcomp : ∀ L : Subgroup ↥H, IsComponentOf L ⊤ →
      IsComponentOf (L.map H.subtype) H := by
    intro L hL
    refine ⟨Subgroup.map_subtype_le L, ?_, ?_⟩
    · have hsn := hL.2.1.map H.subtype
      rwa [show (⊤ : Subgroup ↥H).map H.subtype = H from by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]] at hsn
    · exact CFSG.Open.IsQuasisimple.of_mulEquiv
        (Subgroup.equivMapOfInjective L H.subtype H.subtype_injective).symm hL.2.2
  have hmap : H = ⨆ L ∈ {L : Subgroup ↥H | IsComponentOf L ⊤}, L.map H.subtype := by
    have h1 : (CFSG.Open.genFittingLayer ↥H).map H.subtype =
        ⨆ L ∈ {L : Subgroup ↥H | IsComponentOf L ⊤}, L.map H.subtype := by
      rw [CFSG.Open.genFittingLayer.eq_sSup, sSup_eq_iSup]
      simp only [Subgroup.map_iSup]
    calc H = (⊤ : Subgroup ↥H).map H.subtype := by
          rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      _ = (CFSG.Open.genFittingLayer ↥H).map H.subtype := by rw [hlayer]
      _ = ⨆ L ∈ {L : Subgroup ↥H | IsComponentOf L ⊤}, L.map H.subtype := h1
  apply le_antisymm
  · exact iSup₂_le fun K hK => hK.1
  · conv_lhs => rw [hmap]
    exact iSup₂_le fun L hL =>
      le_iSup₂ (f := fun K (_ : IsComponentOf K H) => K) (L.map H.subtype) (hcomp L hL)

end Abstract

section Concrete

variable {G : Type} [Group G] [Finite G] {D : Data G} {V₀ V L : Subgroup G}

theorem s15_semiBot_odd_card_iSup_barSub_of_isNilpotent (h : Hyp151 D V₀ V L)
    (hnil : Group.IsNilpotent ↥(barSub V₀ V h.isElemAbelian L)) :
    Odd (Nat.card ↥(⨆ m : D.M, barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G)))) := by
  have hV := h.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hoddL : Odd (Nat.card ↥(barSub V₀ V hV L)) :=
    s15_Lin_odd_card_of_isNilpotent hnil (s15_Kbar_no_two_quotient h)
  have hcard : ∀ m : D.M, Nat.card (barSub V₀ V hV (conjSubgroup L (m : G))) =
      Nat.card ↥(barSub V₀ V hV L) := by
    intro m
    have hm_st : (m : G) ∈ stabTil V₀ V := hMs m.2
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV hm_st L]
    exact Subgroup.card_map_of_injective
      (f := (MulAut.conj (actTil V₀ V hV ⟨(m : G), hm_st⟩)⁻¹).toMonoidHom)
      (MulAut.conj (actTil V₀ V hV ⟨(m : G), hm_st⟩)⁻¹).injective
  have hodd : ∀ m : D.M, Odd (Nat.card (barSub V₀ V hV (conjSubgroup L (m : G)))) := by
    intro m
    rw [hcard m]
    exact hoddL
  have hcomm : ∀ m m' : D.M,
      barSub V₀ V hV (conjSubgroup L (m : G)) ≠ barSub V₀ V hV (conjSubgroup L (m' : G)) →
      ∀ x ∈ barSub V₀ V hV (conjSubgroup L (m : G)),
      ∀ y ∈ barSub V₀ V hV (conjSubgroup L (m' : G)), Commute x y := by
    intro m m' hne x hx y hy
    have hne' : (m' : G) * (m : G)⁻¹ ∉ nBar D.M V₀ V hV L := fun hmem =>
      hne (((s15_Infra_mul_inv_mem_nBar_iff h.hyp125 hV m.2 m'.2).1 hmem).symm)
    have hc := (s15_Kbar_commute_conj h m.2 m'.2 hne').1
    have hmem : ⁅x, y⁆ ∈ ⁅barSub V₀ V hV (conjSubgroup L (m : G)),
        barSub V₀ V hV (conjSubgroup L (m' : G))⁆ :=
      Subgroup.commutator_mem_commutator hx hy
    rw [hc, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_commute.mp hmem
  exact s15_Lin_odd_card_iSup (A := MulAut (Vtil V₀ V hV))
    (fun m : D.M => barSub V₀ V hV (conjSubgroup L (m : G))) hodd hcomm

theorem s15_semiBot_sh_of_single_class (h : Hyp151 D V₀ V L)
    (hfit : fittingOf (barSub V₀ V h.isElemAbelian L) = ⊥)
    {C : Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))}
    (hC : IsComponentOf C (barSub V₀ V h.isElemAbelian L))
    (hcls : ∀ K, IsComponentOf K (barSub V₀ V h.isElemAbelian L) →
      K ∈ conjSet C (Mbar D.M V₀ V h.isElemAbelian ⊓
        normalizer ((barSub V₀ V h.isElemAbelian L : Subgroup _) : Set _))) :
    ∃ K ∈ compBar D.M V₀ V h.isElemAbelian,
      (⨆ m : D.M, barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))) =
        ⨆ φ ∈ Mbar D.M V₀ V h.isElemAbelian, K.map (MulAut.conj φ).toMonoidHom := by
  have hV := h.isElemAbelian
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  let Lb : Subgroup (MulAut (Vtil V₀ V hV)) := barSub V₀ V hV L
  let Mb : Subgroup (MulAut (Vtil V₀ V hV)) := Mbar D.M V₀ V hV
  let N : Subgroup (MulAut (Vtil V₀ V hV)) :=
    Mb ⊓ normalizer (Lb : Set (MulAut (Vtil V₀ V hV)))
  let Y : Subgroup (MulAut (Vtil V₀ V hV)) :=
    ⨆ m : D.M, barSub V₀ V hV (conjSubgroup L (m : G))
  let X : Subgroup (MulAut (Vtil V₀ V hV)) :=
    ⨆ φ : Mb, C.map (MulAut.conj (φ : MulAut (Vtil V₀ V hV))).toMonoidHom
  have hYleM : Y ≤ Mb := s15_Infra_iSup_barSub_le h
  have hYnorm : (Y.subgroupOf Mb).Normal := s15_Infra_iSup_barSub_normal h
  have hLbY : Lb ≤ Y := by
    have h1 := le_iSup (fun m : D.M => barSub V₀ V hV (conjSubgroup L (m : G))) (1 : D.M)
    simpa [Lb, Y, conjSubgroup_one] using h1
  have hLbM : Lb ≤ Mb := hLbY.trans hYleM
  have hXY : X ≤ Y := by
    refine iSup_le fun φ => ?_
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hx
    exact s15_Kbar_conj_mem_of_normal hYleM hYnorm φ.2 (hC.1.trans hLbY hc)
  have hLbX : Lb ≤ X := by
    have hcomp := s15_semiBot_eq_iSup_components (V := Vtil V₀ V hV) (H := Lb)
      h.fstar_eq hfit
    rw [← hcomp]
    refine iSup₂_le fun K hK => ?_
    obtain ⟨n, hn, rfl⟩ := hcls K hK
    exact le_iSup
      (fun φ : Mb => C.map (MulAut.conj (φ : MulAut (Vtil V₀ V hV))).toMonoidHom)
      ⟨n, hn.1⟩
  have hXM : X ≤ Mb := by
    refine iSup_le fun φ => ?_
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hx
    exact Mb.mul_mem (Mb.mul_mem φ.2 (hC.1.trans hLbM hc)) (Mb.inv_mem φ.2)
  have hXnorm : (X.subgroupOf Mb).Normal :=
    s15_semiBot_iSup_map_conj_normal (K := C) (B := Mb) (hC.1.trans hLbM)
  have hYXle : Y ≤ X := by
    refine iSup_le fun m => ?_
    have hm_st : (m : G) ∈ stabTil V₀ V := hMs m.2
    have hg : actTil V₀ V hV ⟨(m : G), hm_st⟩ ∈ Mb :=
      actTil_mem_barSub V₀ V hV m.2 hm_st
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV hm_st L]
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    exact s15_Kbar_conj_mem_of_normal hXM hXnorm (Mb.inv_mem hg) (hLbX hy)
  refine ⟨C, s15_semiBot_mem_compBar_of_isComponentOf h hC, ?_⟩
  exact (le_antisymm hYXle hXY).trans
    (iSup_subtype'' (Mb : Set (MulAut (Vtil V₀ V hV)))
      (fun φ => C.map (MulAut.conj φ).toMonoidHom))

theorem s15_semiBot_shape (h : Hyp151 D V₀ V L) :
    (Odd (Nat.card ↥(⨆ m : D.M, barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G)))) ∨
      ∃ K ∈ compBar D.M V₀ V h.isElemAbelian,
        (⨆ m : D.M, barSub V₀ V h.isElemAbelian (conjSubgroup L (m : G))) =
          ⨆ φ ∈ Mbar D.M V₀ V h.isElemAbelian, K.map (MulAut.conj φ).toMonoidHom) ∨
    (∃ K₁ K₂, IsComponentOf K₁ (barSub V₀ V h.isElemAbelian L) ∧
      IsComponentOf K₂ (barSub V₀ V h.isElemAbelian L) ∧
      K₂ ∉ conjSet K₁ (Mbar D.M V₀ V h.isElemAbelian ⊓
        normalizer ((barSub V₀ V h.isElemAbelian L : Subgroup _) : Set _))) ∨
    (fittingOf (barSub V₀ V h.isElemAbelian L) ≠ ⊥ ∧
      ∃ K, IsComponentOf K (barSub V₀ V h.isElemAbelian L)) := by
  rcases s15_Lin_exists_component_or_isNilpotent h.fstar_eq with ⟨C, hC⟩ | hnil
  · by_cases hfit : fittingOf (barSub V₀ V h.isElemAbelian L) = ⊥
    · by_cases hcls : ∀ K, IsComponentOf K (barSub V₀ V h.isElemAbelian L) →
          K ∈ conjSet C (Mbar D.M V₀ V h.isElemAbelian ⊓
            normalizer ((barSub V₀ V h.isElemAbelian L : Subgroup _) : Set _))
      · exact Or.inl (Or.inr (s15_semiBot_sh_of_single_class h hfit hC hcls))
      · obtain ⟨K, hK⟩ := not_forall.1 hcls
        obtain ⟨hK1, hK2⟩ := Classical.not_imp.1 hK
        exact Or.inr (Or.inl ⟨C, K, hC, hK1, hK2⟩)
    · exact Or.inr (Or.inr ⟨hfit, C, hC⟩)
  · exact Or.inl (Or.inl (s15_semiBot_odd_card_iSup_barSub_of_isNilpotent h hnil))

end Concrete

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
