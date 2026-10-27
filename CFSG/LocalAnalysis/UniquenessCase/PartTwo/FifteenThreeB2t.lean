module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeB2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeB2tH
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveFifteen
import CFSG.LocalAnalysis.UniquenessCase.UC22P22n

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Transitive

variable {D : Data G} {V₀ V L : Subgroup G}

private theorem s15_Three_mem_stabSub_iff_map {W : Type} [CommGroup W] {U : Subgroup W}
    {g : MulAut W} : g ∈ stabSub U ↔ U.map g.toMonoidHom = U := by
  constructor
  · intro hg
    refine le_antisymm ?_ ?_
    · rintro x ⟨y, hy, rfl⟩
      exact (mem_stabSub.mp hg y).2 hy
    · intro x hx
      refine Subgroup.mem_map.mpr ⟨g.symm x, ?_, by simp⟩
      exact (mem_stabSub.mp hg (g.symm x)).1 (by simpa using hx)
  · intro hmap u
    constructor
    · intro hu
      have hu' : g u ∈ U.map g.toMonoidHom := by rwa [hmap]
      obtain ⟨y, hy, hyu⟩ := Subgroup.mem_map.mp hu'
      rwa [g.injective hyu] at hy
    · intro hu
      have hu' : g u ∈ U.map g.toMonoidHom := Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
      rwa [hmap] at hu'

private theorem s15_Three_range_map_wStar (h : Hyp151 D V₀ V L) :
    Set.range (fun g : Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian =>
      (wStar D.M V₀ V h.isElemAbelian L).map (g : MulAut _).toMonoidHom) =
    wStarConj D.M V₀ V h.isElemAbelian L := by
  have hV := h.isElemAbelian
  have hMs : D.M ≤ stabTil (v1Sub D.M V₀ V hV L) V := s15_Three_M_le_stabTil_star h
  ext X
  constructor
  · rintro ⟨g, rfl⟩
    exact s15_Infra_map_wStar_mem_wStarConj h.hyp125 hV g.2
  · intro hX
    obtain ⟨m, hm, rfl⟩ := hX
    refine ⟨⟨(actTil (v1Sub D.M V₀ V hV L) V hV ⟨m, hMs hm⟩)⁻¹,
      (Mbar D.M (v1Sub D.M V₀ V hV L) V hV).inv_mem
        (actTil_mem_barSub (v1Sub D.M V₀ V hV L) V hV hm (hMs hm))⟩, ?_⟩
    rw [wStar, s15_Infra_imgTil_conjSubgroup (v1Sub D.M V₀ V hV L) V (wSub V₀ V hV L) hV
      (hMs hm)]

private theorem s15_Three_spread_abstract {V : Type} [CommGroup V]
    {W : Subgroup V} {H : Subgroup (MulAut V)} {P : Subgroup V}
    (hind : sSupIndep (Set.range fun g : H => W.map (g : MulAut V).toMonoidHom))
    (hPW : P ≤ W)
    (hstab : ∀ g ∈ H, g ∈ stabSub W → P.map (g : MulAut V).toMonoidHom = P) :
    (⨆ g : H, P.map (g : MulAut V).toMonoidHom) ⊓ W = P := by
  classical
  have hF1 : W.map ((1 : H) : MulAut V).toMonoidHom = W := by
    rw [show ((1 : H) : MulAut V) = 1 from rfl,
      show (1 : MulAut V).toMonoidHom = MonoidHom.id V from MonoidHom.ext fun x => rfl,
      Subgroup.map_id]
  have hGood : ∀ g : H, W.map (g : MulAut V).toMonoidHom = W →
      P.map (g : MulAut V).toMonoidHom = P := by
    intro g hg
    exact hstab g g.2 ((s15_Three_mem_stabSub_iff_map).2 hg)
  have hgoodsum : (⨆ g : H, ⨆ (_ : W.map (g : MulAut V).toMonoidHom = W),
      P.map (g : MulAut V).toMonoidHom) = P := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun g => iSup_le fun hg => le_of_eq (hGood g hg)
    · refine le_iSup_of_le (1 : H) (le_iSup_of_le hF1 ?_)
      rw [show ((1 : H) : MulAut V) = 1 from rfl,
        show (1 : MulAut V).toMonoidHom = MonoidHom.id V from MonoidHom.ext fun x => rfl,
        Subgroup.map_id]
  have hsplit : (⨆ g : H, P.map (g : MulAut V).toMonoidHom) =
      P ⊔ ⨆ g : H, ⨆ (_ : W.map (g : MulAut V).toMonoidHom ≠ W),
        P.map (g : MulAut V).toMonoidHom := by
    rw [iSup_split (fun g : H => P.map (g : MulAut V).toMonoidHom)
      (fun g => W.map (g : MulAut V).toMonoidHom = W)]
    rw [hgoodsum]
  let Y : Subgroup V := ⨆ g : H, ⨆ (_ : W.map (g : MulAut V).toMonoidHom ≠ W),
    P.map (g : MulAut V).toMonoidHom
  have hYW : Y ≤ sSup (Set.range (fun g : H => W.map (g : MulAut V).toMonoidHom) \ {W}) := by
    refine iSup_le fun g => iSup_le fun hg => ?_
    exact (Subgroup.map_mono hPW).trans (le_sSup ⟨⟨g, rfl⟩, by simpa using hg⟩)
  have hWmem : W ∈ Set.range (fun g : H => W.map (g : MulAut V).toMonoidHom) := ⟨1, hF1⟩
  have hdisj : Disjoint W (sSup (Set.range
      (fun g : H => W.map (g : MulAut V).toMonoidHom) \ {W})) :=
    hind.disjoint_sSup hWmem Set.sdiff_subset (by simp)
  have hYWbot : Y ⊓ W = ⊥ := by
    refine le_bot_iff.mp ?_
    calc Y ⊓ W ≤ sSup (Set.range
          (fun g : H => W.map (g : MulAut V).toMonoidHom) \ {W}) ⊓ W :=
          inf_le_inf_right W hYW
      _ = W ⊓ sSup (Set.range
          (fun g : H => W.map (g : MulAut V).toMonoidHom) \ {W}) := by rw [inf_comm]
      _ = ⊥ := hdisj.eq_bot
  rw [hsplit, sup_inf_assoc_of_le Y hPW, hYWbot, sup_bot_eq]

private theorem s15_Three_spread (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    (P₀ : Subgroup ↥(wStar D.M V₀ V h.isElemAbelian L))
    (hstab : ∀ g ∈ Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian,
      g ∈ stabSub (wStar D.M V₀ V h.isElemAbelian L) →
      (P₀.map (wStar D.M V₀ V h.isElemAbelian L).subtype).map g.toMonoidHom =
        P₀.map (wStar D.M V₀ V h.isElemAbelian L).subtype) :
    (⨆ g : Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian,
      (P₀.map (wStar D.M V₀ V h.isElemAbelian L).subtype).map
        (g : MulAut (vStar D.M V₀ V h.isElemAbelian L)).toMonoidHom) ⊓
      wStar D.M V₀ V h.isElemAbelian L =
    P₀.map (wStar D.M V₀ V h.isElemAbelian L).subtype := by
  have hV := h.isElemAbelian
  have hind : sSupIndep (Set.range fun g : Mbar D.M (v1Sub D.M V₀ V hV L) V hV =>
      (wStar D.M V₀ V hV L).map (g : MulAut _).toMonoidHom) := by
    rw [s15_Three_range_map_wStar h]
    exact sSupIndep_wStarConj D h hV hL
  exact s15_Three_spread_abstract hind (Subgroup.map_subtype_le P₀) hstab

private theorem s15_Three_hstab_of_stableUnder (h : Hyp151 D V₀ V L)
    {P : Subgroup ↥(wStar D.M V₀ V h.isElemAbelian L)}
    (hP : StableUnder (s15NW h) P) :
    ∀ g ∈ Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian,
      g ∈ stabSub (wStar D.M V₀ V h.isElemAbelian L) →
      (P.map (wStar D.M V₀ V h.isElemAbelian L).subtype).map g.toMonoidHom =
        P.map (wStar D.M V₀ V h.isElemAbelian L).subtype := by
  intro g hgH hgS
  have hV := h.isElemAbelian
  have hle : (P.map (wStar D.M V₀ V hV L).subtype).map g.toMonoidHom ≤
      P.map (wStar D.M V₀ V hV L).subtype := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.mp hy
    have hn : resHom (wStar D.M V₀ V hV L) ⟨g, hgS⟩ ∈ s15NW h := by
      rw [s15NW]
      exact mem_autSub.mpr ⟨⟨g, hgS⟩, hgH, rfl⟩
    have hp' : resHom (wStar D.M V₀ V hV L) ⟨g, hgS⟩ p ∈ P := hP _ hn p hp
    refine Subgroup.mem_map.mpr ⟨resHom (wStar D.M V₀ V hV L) ⟨g, hgS⟩ p, hp', ?_⟩
    exact (resHom_apply (wStar D.M V₀ V hV L) ⟨g, hgS⟩ p).symm
  exact Subgroup.eq_of_le_of_card_ge hle
    (le_of_eq (Subgroup.card_map_of_injective g.injective).symm)

private theorem s15_Three_iSup_map_invariant (h : Hyp151 D V₀ V L)
    (P₀ : Subgroup (vStar D.M V₀ V h.isElemAbelian L)) :
    ∀ g ∈ Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian,
      (⨆ k : Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian,
        P₀.map (k : MulAut _).toMonoidHom).map g.toMonoidHom =
      ⨆ k : Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian,
        P₀.map (k : MulAut _).toMonoidHom := by
  intro g hg
  have hV := h.isElemAbelian
  rw [Subgroup.map_iSup]
  refine le_antisymm ?_ ?_
  · refine iSup_le fun k => ?_
    let k' : MulAut (vStar D.M V₀ V hV L) := (k : MulAut (vStar D.M V₀ V hV L))
    have hk'mem : k' ∈ Mbar D.M (v1Sub D.M V₀ V hV L) V hV := k.2
    have hgk : ((P₀.map k'.toMonoidHom)).map (g : MulAut (vStar D.M V₀ V hV L)).toMonoidHom =
        P₀.map ((g : MulAut (vStar D.M V₀ V hV L)) * k').toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    exact le_iSup_of_le (⟨(g : MulAut (vStar D.M V₀ V hV L)) * k',
      (Mbar D.M (v1Sub D.M V₀ V hV L) V hV).mul_mem (show (g : MulAut _) ∈ _ from hg)
        hk'mem⟩ : Mbar D.M (v1Sub D.M V₀ V hV L) V hV) (le_of_eq hgk)
  · refine iSup_le fun k => ?_
    let k' : MulAut (vStar D.M V₀ V hV L) := (k : MulAut (vStar D.M V₀ V hV L))
    have hk'mem : k' ∈ Mbar D.M (v1Sub D.M V₀ V hV L) V hV := k.2
    have hgk : (P₀.map (((g : MulAut (vStar D.M V₀ V hV L))⁻¹ * k'))).map
        (g : MulAut (vStar D.M V₀ V hV L)).toMonoidHom = P₀.map k'.toMonoidHom := by
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [mul_assoc]
    exact le_iSup_of_le (⟨(g : MulAut (vStar D.M V₀ V hV L))⁻¹ * k',
      (Mbar D.M (v1Sub D.M V₀ V hV L) V hV).mul_mem
        ((Mbar D.M (v1Sub D.M V₀ V hV L) V hV).inv_mem
          (show (g : MulAut _) ∈ _ from hg)) hk'mem⟩ :
      Mbar D.M (v1Sub D.M V₀ V hV L) V hV) (le_of_eq hgk.symm)

private theorem s15_Three_sup_spread_eq_top (h : Hyp151 D V₀ V L) (h1217 : R1217 D)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥)
    (P Q : Subgroup ↥(wStar D.M V₀ V h.isElemAbelian L)) (hPQ : P ⊔ Q = ⊤) :
    (⨆ g : Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian,
      (P.map (wStar D.M V₀ V h.isElemAbelian L).subtype).map
        (g : MulAut (vStar D.M V₀ V h.isElemAbelian L)).toMonoidHom) ⊔
      (⨆ g : Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian,
        (Q.map (wStar D.M V₀ V h.isElemAbelian L).subtype).map
          (g : MulAut (vStar D.M V₀ V h.isElemAbelian L)).toMonoidHom) = ⊤ := by
  have hPQ' : P.map (wStar D.M V₀ V h.isElemAbelian L).subtype ⊔
      Q.map (wStar D.M V₀ V h.isElemAbelian L).subtype =
      wStar D.M V₀ V h.isElemAbelian L := by
    rw [← Subgroup.map_sup, hPQ]
    refine le_antisymm (Subgroup.map_subtype_le ⊤) ?_
    intro w hw
    exact Subgroup.mem_map.mpr ⟨⟨w, hw⟩, trivial, rfl⟩
  have htop : (⨆ g : Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian,
      (wStar D.M V₀ V h.isElemAbelian L).map (g : MulAut _).toMonoidHom) = ⊤ := by
    rw [← sSup_range, s15_Three_range_map_wStar h]
    exact (fifteen_two_directSum D h1217 h h.isElemAbelian hL).2
  have hle : (⨆ g : Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian,
        (wStar D.M V₀ V h.isElemAbelian L).map (g : MulAut _).toMonoidHom) ≤
      (⨆ g : Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian,
        (P.map (wStar D.M V₀ V h.isElemAbelian L).subtype).map (g : MulAut _).toMonoidHom) ⊔
      ⨆ g : Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L) V h.isElemAbelian,
        (Q.map (wStar D.M V₀ V h.isElemAbelian L).subtype).map (g : MulAut _).toMonoidHom := by
    refine iSup_le fun g => ?_
    have hg : (wStar D.M V₀ V h.isElemAbelian L).map (g : MulAut _).toMonoidHom =
        ((P.map (wStar D.M V₀ V h.isElemAbelian L).subtype) ⊔
          (Q.map (wStar D.M V₀ V h.isElemAbelian L).subtype)).map
            (g : MulAut _).toMonoidHom := by
      rw [hPQ']
    rw [hg, Subgroup.map_sup]
    exact sup_le
      (le_sup_of_le_left (le_iSup (fun g : Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L)
          V h.isElemAbelian =>
          (P.map (wStar D.M V₀ V h.isElemAbelian L).subtype).map
            (g : MulAut _).toMonoidHom) g))
      (le_sup_of_le_right (le_iSup (fun g : Mbar D.M (v1Sub D.M V₀ V h.isElemAbelian L)
          V h.isElemAbelian =>
          (Q.map (wStar D.M V₀ V h.isElemAbelian L).subtype).map
            (g : MulAut _).toMonoidHom) g))
  apply le_antisymm le_top
  rw [← htop]
  exact hle

theorem s15_Three_trans_AW (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h1217 : R1217 D) (h : Hyp151 D V₀ V L)
    (hL : barSub V₀ V h.isElemAbelian L ≠ ⊥) (hsemi : s15Semisimple (s15AW h))
    (I I' : Subgroup ↥(wStar D.M V₀ V h.isElemAbelian L))
    (hI : IsIrrOn (s15AW h) I ⊥) (hI' : IsIrrOn (s15AW h) I' ⊥) :
    ∃ n ∈ s15NW h, s15SecIso (s15AW h) (I.map (n : MulAut _).toMonoidHom) ⊥ I' ⊥ := by
  classical
  by_contra hcon
  push Not at hcon
  have hV := h.isElemAbelian
  have hMs : D.M ≤ stabTil (v1Sub D.M V₀ V hV L) V := s15_Three_M_le_stabTil_star h
  have hNnorm : ∀ n ∈ s15NW h, s15Normalizes n (s15AW h) :=
    fun n hn => s15_Three_NW_normalizes h1217 h hn
  obtain ⟨P, Q, hAP, hAQ, hNP, hNQ, hPQ, hPQtop, hIP, hIQ⟩ :=
    s15_Three_homog_split hNnorm hsemi hI hI' hcon
  have hPbot : P ≠ ⊥ := fun hb => hI.1.ne' (le_bot_iff.mp (hIP.trans (le_of_eq hb)))
  have hQbot : Q ≠ ⊥ := fun hb => hI'.1.ne' (le_bot_iff.mp (hIQ.trans (le_of_eq hb)))
  have hPtop : P ≠ ⊤ := by
    intro hP
    have hQ : Q = P ⊓ Q := by rw [hP, top_inf_eq]
    exact hQbot (hQ.trans hPQ)
  have hQtop : Q ≠ ⊤ := by
    intro hQ
    have hP : P = P ⊓ Q := by rw [hQ, inf_top_eq]
    exact hPbot (hP.trans hPQ)
  let Wc : Subgroup (vStar D.M V₀ V hV L) := wStar D.M V₀ V hV L
  let H : Subgroup (MulAut (vStar D.M V₀ V hV L)) :=
    Mbar D.M (v1Sub D.M V₀ V hV L) V hV
  have hP₀Q₀bot : P.map Wc.subtype ⊓ Q.map Wc.subtype = ⊥ := by
    rw [← Subgroup.map_inf P Q Wc.subtype Wc.subtype_injective, hPQ, Subgroup.map_bot]
  have hP₀Q₀ : P.map Wc.subtype ⊔ Q.map Wc.subtype = Wc := by
    rw [← Subgroup.map_sup, hPQtop]
    refine le_antisymm (Subgroup.map_subtype_le ⊤) ?_
    intro w hw
    exact Subgroup.mem_map.mpr ⟨⟨w, hw⟩, trivial, rfl⟩
  let S : Subgroup (vStar D.M V₀ V hV L) :=
    ⨆ g : H, (P.map Wc.subtype).map (g : MulAut _).toMonoidHom
  let T : Subgroup (vStar D.M V₀ V hV L) :=
    ⨆ g : H, (Q.map Wc.subtype).map (g : MulAut _).toMonoidHom
  have hPspread : S ⊓ Wc = P.map Wc.subtype :=
    s15_Three_spread h hL P (s15_Three_hstab_of_stableUnder h hNP)
  have hQspread : T ⊓ Wc = Q.map Wc.subtype :=
    s15_Three_spread h hL Q (s15_Three_hstab_of_stableUnder h hNQ)
  have hPbigsup : S ⊔ T = ⊤ :=
    s15_Three_sup_spread_eq_top h h1217 hL P Q hPQtop
  have hSa : imgTil (v1Sub D.M V₀ V hV L) V hV
      (preTil (v1Sub D.M V₀ V hV L) V hV S) = S := imgTil_preTil _ _ _ _
  have hTb : imgTil (v1Sub D.M V₀ V hV L) V hV
      (preTil (v1Sub D.M V₀ V hV L) V hV T) = T := imgTil_preTil _ _ _ _
  have hVaV : preTil (v1Sub D.M V₀ V hV L) V hV S ≤ V := preTil_le _ _ _ _
  have hVbV : preTil (v1Sub D.M V₀ V hV L) V hV T ≤ V := preTil_le _ _ _ _
  have hMVa : D.M ≤ normalizer
      (preTil (v1Sub D.M V₀ V hV L) V hV S : Set G) := by
    intro m hm
    refine (conjSubgroup_eq_iff_mem_normalizer).mp ?_
    have hms : m ∈ stabTil (v1Sub D.M V₀ V hV L) V := hMs hm
    have hinv := s15_Three_iSup_map_invariant h (P.map Wc.subtype)
      (actTil (v1Sub D.M V₀ V hV L) V hV ⟨m, hms⟩)
      (actTil_mem_barSub (v1Sub D.M V₀ V hV L) V hV hm hms)
    have hinv' : S.map ((actTil (v1Sub D.M V₀ V hV L) V hV ⟨m, hms⟩)⁻¹).toMonoidHom = S := by
      have h2 := congrArg (Subgroup.map
        ((actTil (v1Sub D.M V₀ V hV L) V hV ⟨m, hms⟩)⁻¹).toMonoidHom) hinv
      rw [Subgroup.map_map, show
        ((actTil (v1Sub D.M V₀ V hV L) V hV ⟨m, hms⟩)⁻¹).toMonoidHom.comp
          (actTil (v1Sub D.M V₀ V hV L) V hV ⟨m, hms⟩).toMonoidHom = MonoidHom.id _ from by
          ext x; simp, Subgroup.map_id] at h2
      exact h2.symm
    rw [← s15_Infra_preTil_map_actTil (v1Sub D.M V₀ V hV L) V hV hms S, hinv']
  have hMVb : D.M ≤ normalizer
      (preTil (v1Sub D.M V₀ V hV L) V hV T : Set G) := by
    intro m hm
    refine (conjSubgroup_eq_iff_mem_normalizer).mp ?_
    have hms : m ∈ stabTil (v1Sub D.M V₀ V hV L) V := hMs hm
    have hinv := s15_Three_iSup_map_invariant h (Q.map Wc.subtype)
      (actTil (v1Sub D.M V₀ V hV L) V hV ⟨m, hms⟩)
      (actTil_mem_barSub (v1Sub D.M V₀ V hV L) V hV hm hms)
    have hinv' : T.map ((actTil (v1Sub D.M V₀ V hV L) V hV ⟨m, hms⟩)⁻¹).toMonoidHom = T := by
      have h2 := congrArg (Subgroup.map
        ((actTil (v1Sub D.M V₀ V hV L) V hV ⟨m, hms⟩)⁻¹).toMonoidHom) hinv
      rw [Subgroup.map_map, show
        ((actTil (v1Sub D.M V₀ V hV L) V hV ⟨m, hms⟩)⁻¹).toMonoidHom.comp
          (actTil (v1Sub D.M V₀ V hV L) V hV ⟨m, hms⟩).toMonoidHom = MonoidHom.id _ from by
          ext x; simp, Subgroup.map_id] at h2
      exact h2.symm
    rw [← s15_Infra_preTil_map_actTil (v1Sub D.M V₀ V hV L) V hV hms T, hinv']
  have hVaNe : preTil (v1Sub D.M V₀ V hV L) V hV S ≠ ⊥ := by
    intro hb
    have hSbot : S = ⊥ := by
      rw [← hSa, hb, s15_Core_imgTil_eq_bot_of_le hV bot_le]
    have hP₀bot : P.map Wc.subtype = ⊥ := by rw [← hPspread, hSbot, bot_inf_eq]
    exact hPbot ((Subgroup.map_eq_bot_iff_of_injective P Wc.subtype_injective).1 hP₀bot)
  have hVbNe : preTil (v1Sub D.M V₀ V hV L) V hV T ≠ ⊥ := by
    intro hb
    have hTbot : T = ⊥ := by
      rw [← hTb, hb, s15_Core_imgTil_eq_bot_of_le hV bot_le]
    have hQ₀bot : Q.map Wc.subtype = ⊥ := by rw [← hQspread, hTbot, bot_inf_eq]
    exact hQbot ((Subgroup.map_eq_bot_iff_of_injective Q Wc.subtype_injective).1 hQ₀bot)
  have hVasup : V = preTil (v1Sub D.M V₀ V hV L) V hV S ⊔
      preTil (v1Sub D.M V₀ V hV L) V hV T := by
    symm
    refine s15_Two_eq_of_imgTil_eq_top (V₀ := v1Sub D.M V₀ V hV L) hV
      (sup_le hVaV hVbV) ?_ ?_
    · have hmono : preTil (v1Sub D.M V₀ V hV L) V hV ⊥ ≤
          preTil (v1Sub D.M V₀ V hV L) V hV S :=
        Subgroup.map_mono (Subgroup.comap_mono bot_le)
      have hpt : preTil (v1Sub D.M V₀ V hV L) V hV ⊥ = v1Sub D.M V₀ V hV L := by
        rw [preTil_bot, inf_eq_right.mpr (s15_Infra_v1Sub_le h.hyp125 hV)]
      have hV₁S : v1Sub D.M V₀ V hV L ≤ preTil (v1Sub D.M V₀ V hV L) V hV S :=
        (le_of_eq hpt.symm).trans hmono
      exact le_sup_of_le_left hV₁S
    · rw [s15_Core_imgTil_sup hV hVaV hVbV, hSa, hTb]
      exact hPbigsup
  rcases twelve_fifteen D hx h61 h127 h1214 h.hyp125
    ⟨hVaNe, hVaV.trans h.hyp125.pairFacts.le_M, hMVa,
      uc22p22n_isElemAbelian_of_le hVaV hV⟩
    ⟨hVbNe, hVbV.trans h.hyp125.pairFacts.le_M, hMVb,
      uc22p22n_isElemAbelian_of_le hVbV hV⟩ hVasup with hVaV' | hVbV'
  · have hStop : S = ⊤ := by
      rw [← hSa, ← hVaV', s15_Infra_imgTil_top (v1Sub D.M V₀ V hV L) V hV]
    have hP₀W : P.map Wc.subtype = Wc := by rw [← hPspread, hStop, top_inf_eq]
    have hQ₀le : Q.map Wc.subtype ≤ P.map Wc.subtype := by
      rw [hP₀W]; exact Subgroup.map_subtype_le Q
    have hQ₀bot : Q.map Wc.subtype = ⊥ := by
      rw [← inf_eq_right.mpr hQ₀le, hP₀Q₀bot]
    exact hQbot ((Subgroup.map_eq_bot_iff_of_injective Q Wc.subtype_injective).1 hQ₀bot)
  · have hTtop : T = ⊤ := by
      rw [← hTb, ← hVbV', s15_Infra_imgTil_top (v1Sub D.M V₀ V hV L) V hV]
    have hQ₀W : Q.map Wc.subtype = Wc := by rw [← hQspread, hTtop, top_inf_eq]
    have hP₀le : P.map Wc.subtype ≤ Q.map Wc.subtype := by
      rw [hQ₀W]; exact Subgroup.map_subtype_le P
    have hP₀bot : P.map Wc.subtype = ⊥ := by
      rw [← inf_eq_left.mpr hP₀le, hP₀Q₀bot]
    exact hPbot ((Subgroup.map_eq_bot_iff_of_injective P Wc.subtype_injective).1 hP₀bot)

end Transitive

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
