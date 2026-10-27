module

public import CFSG.Timmesfeld.ARS.Sec13Basic

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec13Restrict

variable {H : Subgroup G}

theorem sup_subgroupOf {X Y : Subgroup G} (hX : X ≤ H) (hY : Y ≤ H) :
    (X ⊔ Y).subgroupOf H = X.subgroupOf H ⊔ Y.subgroupOf H := by
  apply Subgroup.map_injective H.subtype_injective
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (sup_le hX hY),
    Subgroup.map_subgroupOf_eq_of_le hX, Subgroup.map_subgroupOf_eq_of_le hY]

theorem mem_restrict_iff {X' : Subgroup H} : X' ∈ restrict R H ↔ X'.map H.subtype ∈ R := by
  constructor
  · rintro ⟨B, ⟨hB, hBH⟩, rfl⟩
    rwa [Subgroup.map_subgroupOf_eq_of_le hBH]
  · intro h
    exact ⟨_, ⟨h, Subgroup.map_subtype_le X'⟩, CFSG.subgroupOf_map_subtype_eq X'⟩

theorem subgroupOf_mem_restrict_iff {X : Subgroup G} (hX : X ≤ H) :
    X.subgroupOf H ∈ restrict R H ↔ X ∈ R := by
  rw [mem_restrict_iff, Subgroup.map_subgroupOf_eq_of_le hX]

theorem commuting_subgroupOf_iff' {X Y : Subgroup G} (hX : X ≤ H) (hY : Y ≤ H) :
    Commuting (X.subgroupOf H) (Y.subgroupOf H) ↔ Commuting X Y := by
  rw [Restrict.commuting_subgroupOf_iff, inf_of_le_left hX, inf_of_le_left hY]

theorem commuting_iff_map {X' Y' : Subgroup H} :
    Commuting X' Y' ↔ Commuting (X'.map H.subtype) (Y'.map H.subtype) := by
  rw [← commuting_subgroupOf_iff' (Subgroup.map_subtype_le X') (Subgroup.map_subtype_le Y'),
    CFSG.subgroupOf_map_subtype_eq, CFSG.subgroupOf_map_subtype_eq]

theorem conjSub_subgroupOf (X : Subgroup G) (b : H) :
    conjSub (X.subgroupOf H) b = (conjSub X b).subgroupOf H :=
  map_conj_subgroupOf_mk b.2

theorem coveredBy_subgroupOf_iff {T : Subgroup G} (hT : T ≤ H) :
    CoveredBy (restrict R H) (T.subgroupOf H) ↔ CoveredBy R T := by
  constructor
  · intro h x hx hx1
    obtain ⟨C', hC', hC'T, hxC'⟩ := h ⟨x, hT hx⟩ hx (fun e => hx1 (congrArg Subtype.val e))
    refine ⟨C'.map H.subtype, mem_restrict_iff.1 hC', ?_, ⟨⟨x, hT hx⟩, hxC', rfl⟩⟩
    have := Subgroup.map_mono (f := H.subtype) hC'T
    rwa [Subgroup.map_subgroupOf_eq_of_le hT] at this
  · intro h x' hx' hx'1
    obtain ⟨C, hC, hCT, hxC⟩ := h x' hx' (fun e => hx'1 (Subtype.ext e))
    exact ⟨C.subgroupOf H, (subgroupOf_mem_restrict_iff (hCT.trans hT)).2 hC,
      fun y hy => hCT hy, hxC⟩

theorem opposite_subgroupOf_iff {X Y : Subgroup G} (hX : X ≤ H) (hY : Y ≤ H) :
    Opposite (X.subgroupOf H) (Y.subgroupOf H) ↔ Opposite X Y := by
  refine ⟨fun h => ⟨fun e => h.1 (e ▸ rfl), fun a ha ha1 => ?_, fun b hb hb1 => ?_⟩,
    Restrict.opposite_subgroupOf hX hY⟩
  · obtain ⟨b, hb, hb1, hab⟩ := h.2.1 ⟨a, hX ha⟩ ha (fun e => ha1 (congrArg Subtype.val e))
    refine ⟨b, hb, fun e => hb1 (Subtype.ext e), ?_⟩
    rw [conjSub_subgroupOf, conjSub_subgroupOf] at hab
    exact (subgroupOf_inj_of_le (conjSub_le hX b.2) (conjSub_le hY (hX ha))).1 hab
  · obtain ⟨a, ha, ha1, hba⟩ := h.2.2 ⟨b, hY hb⟩ hb (fun e => hb1 (congrArg Subtype.val e))
    refine ⟨a, ha, fun e => ha1 (Subtype.ext e), ?_⟩
    rw [conjSub_subgroupOf, conjSub_subgroupOf] at hba
    exact (subgroupOf_inj_of_le (conjSub_le hY a.2) (conjSub_le hX (hY hb))).1 hba

theorem special_subgroupOf_iff {X Y : Subgroup G} (hX : X ≤ H) (hY : Y ≤ H) :
    Special (restrict R H) (X.subgroupOf H) (Y.subgroupOf H) ↔ Special R X Y := by
  have hXY : ⁅X, Y⁆ ≤ H := QD.commutator_le_of_le hX hY
  rw [Special, Special, Restrict.commutator_subgroupOf hX hY, subgroupOf_mem_restrict_iff hXY,
    commuting_subgroupOf_iff' hXY hX, commuting_subgroupOf_iff' hXY hY]

theorem lambdaSet_subgroupOf_iff {X Y : Subgroup G} (hX : X ≤ H) (hY : Y ≤ H) :
    Y.subgroupOf H ∈ lambdaSet (restrict R H) (X.subgroupOf H) ↔ Y ∈ lambdaSet R X := by
  simp only [lambdaSet, sigmaSet, Set.mem_ofPred_eq, ne_eq]
  rw [subgroupOf_mem_restrict_iff hY, subgroupOf_inj_of_le hY hX, commuting_subgroupOf_iff' hX hY,
    ← sup_subgroupOf hX hY, coveredBy_subgroupOf_iff (sup_le hX hY)]

theorem map_gen (S : Set (Subgroup H)) :
    (gen S).map H.subtype = gen ((fun X => X.map H.subtype) '' S) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine gen_le fun X hX => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_gen ⟨X, hX, rfl⟩
  · refine gen_le ?_
    rintro _ ⟨X, hX, rfl⟩
    exact Subgroup.map_mono (le_gen hX)

theorem image_lambdaSet {X : Subgroup G} (hX : X ≤ H) :
    (fun Y => Y.map H.subtype) '' lambdaSet (restrict R H) (X.subgroupOf H) =
      {Y | Y ≤ H ∧ Y ∈ lambdaSet R X} := by
  ext Y
  constructor
  · rintro ⟨Y', hY', rfl⟩
    have hYH : Y'.map H.subtype ≤ H := Subgroup.map_subtype_le Y'
    refine ⟨hYH, (lambdaSet_subgroupOf_iff hX hYH).1 ?_⟩
    rwa [CFSG.subgroupOf_map_subtype_eq]
  · rintro ⟨hYH, hY⟩
    exact ⟨Y.subgroupOf H, (lambdaSet_subgroupOf_iff hX hYH).2 hY,
      Subgroup.map_subgroupOf_eq_of_le hYH⟩

end Sec13Restrict

open Sec13Restrict

namespace Sec13

variable {A A₀ : Subgroup G} (hS : Sec13 R A A₀)
include hS

omit hS in
theorem le_levi {X : Subgroup G} (hX : X ∈ leviSet R A A₀) : X ≤ levi R A A₀ := le_gen hX

theorem mem_leviSet_iff {X : Subgroup G} (hX : X ∈ R) :
    X ∈ leviSet R A A₀ ↔ X ≤ levi R A A₀ :=
  ⟨fun h => le_gen h, Levi.mem_leviSet_of_le_levi hS.hyp.root hS.mem hS.opp hX⟩

theorem isRootClass_restrict : IsRootClass (restrict R (levi R A A₀)) := by
  obtain ⟨E₀, hE₀, -⟩ := hS.nondeg
  refine ARS.isRootClass_restrict hS.hyp.root hE₀.1.1 (le_gen hE₀) (fun B hB hBV => ?_) ?_
  · have hBΔ := (hS.mem_leviSet_iff hB).2 hBV
    obtain ⟨g, hg, hgB⟩ := Sec3.exists_conjSub_eq_of_reflTransGen hS.hyp.root
      (fun X hX => hX.1.1) (hS.conn E₀ hE₀ B hBΔ)
    have hle : (⨆ D ∈ {D | Relation.ReflTransGen (oppGraph (leviSet R A A₀)) E₀ D}, D) ≤
        levi R A A₀ := by
      refine iSup₂_le fun D hD => ?_
      change Relation.ReflTransGen (oppGraph (leviSet R A A₀)) E₀ D at hD
      cases hD with
      | refl => exact le_gen hE₀
      | tail _ hcd => exact le_gen hcd.2.1
    exact ⟨g, hle hg, hgB⟩
  · exact gen_le fun X hX =>
      le_iSup₂ (f := fun B (_ : B ∈ {B | B ∈ R ∧ B ≤ levi R A A₀}) => B) X ⟨hX.1.1, le_gen hX⟩

theorem noIsolated_restrict : NoIsolated (restrict R (levi R A A₀)) := by
  refine ARS.noIsolated_restrict fun B hB hBV => ?_
  obtain ⟨C, hC, hBC⟩ := Levi.exists_opposite_mem_leviSet hS.hyp hS.mem hS.sec8.2 hS.opp
    ((hS.mem_leviSet_iff hB).2 hBV)
  exact ⟨C, hC.1.1, le_gen hC, hBC⟩

theorem isNondegenerate_restrict : IsNondegenerate (restrict R (levi R A A₀)) := by
  obtain ⟨E, hE, F, hF, hEF⟩ := hS.nondeg
  exact ⟨E.subgroupOf _, (subgroupOf_mem_restrict_iff (le_levi hE)).2 hE.1.1, F.subgroupOf _,
    (subgroupOf_mem_restrict_iff (le_levi hF)).2 hF.1.1,
    (special_subgroupOf_iff (le_levi hE) (le_levi hF)).2 hEF⟩

theorem image_lambdaSet_levi {F : Subgroup G} (hF : F ∈ leviSet R A A₀) :
    (fun Y => Y.map (levi R A A₀).subtype) ''
        lambdaSet (restrict R (levi R A A₀)) (F.subgroupOf (levi R A A₀)) =
      leviSet R A A₀ ∩ lambdaSet R F := by
  rw [image_lambdaSet (le_levi hF)]
  ext Y
  exact ⟨fun ⟨hYV, hY⟩ => ⟨(hS.mem_leviSet_iff hY.1.1).2 hYV, hY⟩,
    fun ⟨hYΔ, hY⟩ => ⟨le_gen hYΔ, hY⟩⟩

theorem gen_inter_lambdaSet_sup_eq_levi {F L : Subgroup G} (hF : F ∈ leviSet R A A₀)
    (hL : L ∈ leviSet R A A₀) (hFL : Opposite F L) :
    gen (leviSet R A A₀ ∩ lambdaSet R F) ⊔ L = levi R A A₀ := by
  have := hS.hyp.finite
  have hFV : F ≤ levi R A A₀ := le_levi hF
  have hLV : L ≤ levi R A A₀ := le_levi hL
  have key := gen_lambdaSet_sup_eq_top_of hS.isRootClass_restrict hS.noIsolated_restrict
    hS.isNondegenerate_restrict ((subgroupOf_mem_restrict_iff hFV).2 hF.1.1)
    ⟨(subgroupOf_mem_restrict_iff hLV).2 hL.1.1, (opposite_subgroupOf_iff hFV hLV).2 hFL⟩
  have hmap := congrArg (Subgroup.map (levi R A A₀).subtype) key
  rwa [Subgroup.map_sup, map_gen, hS.image_lambdaSet_levi hF,
    Subgroup.map_subgroupOf_eq_of_le hLV, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at hmap

theorem exists_mem_inter_lambdaSet_conjSub_eq {Y P Q Q' : Subgroup G}
    (hY : Y ∈ leviSet R A A₀) (hP : P ∈ leviSet R A A₀) (hYP : P ∈ lambdaSet R Y)
    (hQ : Q ∈ R) (hQle : Q ≤ Y ⊔ P) (hQY : Q ≠ Y) (hQ' : Q' ∈ R) (hQ'le : Q' ≤ Y ⊔ P)
    (hQ'Y : Q' ≠ Y) :
    ∃ U ∈ leviSet R A A₀ ∩ lambdaSet R Y, ∃ u ∈ U, conjSub Q u = Q' := by
  have := hS.hyp.finite
  set V := levi R A A₀
  have hYV : Y ≤ V := le_levi hY
  have hPV : P ≤ V := le_levi hP
  have hYPV : Y ⊔ P ≤ V := sup_le hYV hPV
  have hQV : Q ≤ V := hQle.trans hYPV
  have hQ'V : Q' ≤ V := hQ'le.trans hYPV
  have hle : ∀ {X : Subgroup G}, X ≤ Y ⊔ P → X.subgroupOf V ≤ Y.subgroupOf V ⊔ P.subgroupOf V :=
    fun {X} hX => by rw [← sup_subgroupOf hYV hPV]; exact fun x hx => hX hx
  obtain ⟨U', hU', u, hu, hQu⟩ := exists_mem_lambdaSet_conjSub_eq hS.isRootClass_restrict
    hS.noIsolated_restrict ((subgroupOf_mem_restrict_iff hYV).2 hY.1.1)
    ((lambdaSet_subgroupOf_iff hYV hPV).2 hYP) ((subgroupOf_mem_restrict_iff hQV).2 hQ)
    (hle hQle) (fun e => hQY ((subgroupOf_inj_of_le hQV hYV).1 e))
    ((subgroupOf_mem_restrict_iff hQ'V).2 hQ') (hle hQ'le)
    (fun e => hQ'Y ((subgroupOf_inj_of_le hQ'V hYV).1 e))
  have hUR : U'.map V.subtype ∈ R := mem_restrict_iff.1 hU'.1.1
  have hU'm : U' = (U'.map V.subtype).subgroupOf V := (CFSG.subgroupOf_map_subtype_eq U').symm
  have hUV : U'.map V.subtype ≤ V := Subgroup.map_subtype_le U'
  rw [hU'm] at hU' hu
  refine ⟨U'.map V.subtype, ⟨(hS.mem_leviSet_iff hUR).2 hUV,
    (lambdaSet_subgroupOf_iff hYV hUV).1 hU'⟩, u, hu, ?_⟩
  rw [conjSub_subgroupOf] at hQu
  exact (subgroupOf_inj_of_le (conjSub_le hQV u.2) hQ'V).1 hQu

theorem eq_of_commuting_of_rootClosure
    (h813 : ∀ E ∈ leviSet R A A₀, ∀ E' ∈ leviSet R A A₀,
      (∀ X ∈ leviSet R A A₀, Commuting E X ↔ Commuting E' X) → E = E')
    {E F : Subgroup G} (hE : E ∈ leviSet R A A₀) (hF : F ∈ leviSet R A A₀)
    (hFE : Commuting F E) (hFΛ : ∀ D ∈ leviSet R A A₀ ∩ lambdaSet R E, Commuting F D) :
    F = E := by
  have := hS.hyp.finite
  set V := levi R A A₀
  set R' := restrict R V
  have hR' := hS.isRootClass_restrict
  have hEV : E ≤ V := le_levi hE
  have hFV : F ≤ V := le_levi hF
  have hRad : ∀ X ∈ R', rootClosure R' X = {X} := by
    intro X' hX'
    refine Set.Subset.antisymm (fun B' hB' => ?_) (Set.singleton_subset_iff.2
      (mem_rootClosure_self hX'))
    rw [Set.mem_singleton_iff]
    obtain ⟨B, ⟨hB, hBV⟩, rfl⟩ := hB'.1
    obtain ⟨X, ⟨hX, hXV⟩, rfl⟩ := hX'
    have hBΔ := (hS.mem_leviSet_iff hB).2 hBV
    have hXΔ := (hS.mem_leviSet_iff hX).2 hXV
    congr 1
    refine h813 B hBΔ X hXΔ fun Y hY => ?_
    have hYV : Y ≤ V := le_levi hY
    have hY' : Y.subgroupOf V ∈ R' := (subgroupOf_mem_restrict_iff hYV).2 hY.1.1
    have hc := congrArg (fun S : Set (Subgroup V) => Y.subgroupOf V ∈ S) hB'.2
    simp only [centralSet, Set.mem_ofPred_eq, eq_iff_iff] at hc
    rw [← commuting_subgroupOf_iff' hBV hYV, ← commuting_subgroupOf_iff' hXV hYV]
    exact ⟨fun h => (hc.1 ⟨hY', h⟩).2, fun h => (hc.2 ⟨hY', h⟩).2⟩
  obtain ⟨-, -, -, hcent, -⟩ := Q_eq_M_of_rootClosure hR' hS.noIsolated_restrict
    hS.isNondegenerate_restrict hRad ((subgroupOf_mem_restrict_iff hEV).2 hE.1.1)
  have hMmap : (M R' (E.subgroupOf V)).map V.subtype =
      E ⊔ gen (leviSet R A A₀ ∩ lambdaSet R E) := by
    change (E.subgroupOf V ⊔ gen (lambdaSet R' (E.subgroupOf V))).map V.subtype = _
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hEV, map_gen,
      hS.image_lambdaSet_levi hE]
  have hFM : Commuting (F.subgroupOf V) (M R' (E.subgroupOf V)) := by
    rw [commuting_iff_map, Subgroup.map_subgroupOf_eq_of_le hFV, hMmap]
    refine Commuting.sup_right hFE (commuting_iff_le_centralizer.2 (gen_le fun D hD =>
      commuting_iff_le_centralizer.1 (hFΛ D hD)))
  have hmem : F.subgroupOf V ∈ {B | B ∈ R' ∧ Commuting B (M R' (E.subgroupOf V))} :=
    ⟨(subgroupOf_mem_restrict_iff hFV).2 hF.1.1, hFM⟩
  rw [hcent, Set.mem_singleton_iff] at hmem
  exact (subgroupOf_inj_of_le hFV hEV).1 hmem

theorem exists_mem_inter_lambdaSet_not_commuting
    (h813 : ∀ E ∈ leviSet R A A₀, ∀ E' ∈ leviSet R A A₀,
      (∀ X ∈ leviSet R A A₀, Commuting E X ↔ Commuting E' X) → E = E')
    {E F : Subgroup G} (hE : E ∈ leviSet R A A₀) (hF : F ∈ leviSet R A A₀) (hFE : F ≠ E)
    (hcomm : Commuting F E) :
    ∃ D ∈ leviSet R A A₀ ∩ lambdaSet R E, ¬ Commuting F D := by
  by_contra! hall
  exact hFE (hS.eq_of_commuting_of_rootClosure h813 hE hF hcomm hall)

end Sec13

end CFSG.Timmesfeld.ARS
