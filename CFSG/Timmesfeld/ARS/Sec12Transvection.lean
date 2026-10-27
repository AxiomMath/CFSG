module

public import CFSG.Timmesfeld.ARS.Sec12Center
public import CFSG.Timmesfeld.ARS.Sec12Meets
public import CFSG.Timmesfeld.Transvection.Lines

public section

namespace CFSG.Timmesfeld.ARS

open Transvection Sec13Restrict

variable {G : Type} [Group G] {R : Set (Subgroup G)}

namespace Sec12

variable {A A₀ : Subgroup G} (hS : Sec12 R A A₀)
include hS

theorem restrict_leviSet_eq :
    restrict (leviSet R A A₀) (levi R A A₀) = restrict R (levi R A A₀) := by
  change (fun B : Subgroup G => B.subgroupOf (levi R A A₀)) '' _ =
    (fun B : Subgroup G => B.subgroupOf (levi R A A₀)) '' _
  congr 1
  ext B
  exact ⟨fun h => ⟨h.1.1.1, h.2⟩,
    fun h => ⟨Levi.mem_leviSet_of_le_levi hS.hyp.root hS.mem hS.opp h.1 h.2, h.2⟩⟩

theorem isTransvectionClass_restrict (hconn : LeviConnected R A A₀) :
    IsTransvectionClass (restrict (leviSet R A A₀) (levi R A A₀)) := by
  have hR := hS.hyp.root
  obtain ⟨E, C, P, Q, hfr⟩ := hS.exists_isSubframe
  have hE₀ := (hfr.memP 0).1
  rw [hS.restrict_leviSet_eq]
  refine ⟨ARS.isRootClass_restrict hR hE₀.1.1 (le_gen hE₀) (fun B hB hBV => ?_) ?_, ?_⟩
  · have hBΔ := Levi.mem_leviSet_of_le_levi hR hS.mem hS.opp hB hBV
    obtain ⟨g, hg, hgB⟩ := Sec3.exists_conjSub_eq_of_reflTransGen hR
      (fun X hX => hX.1.1) (hconn _ hE₀ B hBΔ)
    have hle : (⨆ D ∈ {D | Relation.ReflTransGen (oppGraph (leviSet R A A₀)) (P 0) D}, D) ≤
        levi R A A₀ := by
      refine iSup₂_le fun D hD => ?_
      change Relation.ReflTransGen (oppGraph (leviSet R A A₀)) (P 0) D at hD
      cases hD with
      | refl => exact le_gen hE₀
      | tail _ hcd => exact le_gen hcd.2.1
    exact ⟨g, hle hg, hgB⟩
  · exact gen_le fun X hX =>
      le_iSup₂ (f := fun B (_ : B ∈ {B | B ∈ R ∧ B ≤ levi R A A₀}) => B) X ⟨hX.1.1, le_gen hX⟩
  · rintro _ ⟨X, ⟨hX, hXV⟩, rfl⟩ _ ⟨Y, ⟨hY, hYV⟩, rfl⟩ hs
    rw [special_subgroupOf_iff hXV hYV] at hs
    exact hS.deg X (Levi.mem_leviSet_of_le_levi hR hS.mem hS.opp hX hXV) Y
      (Levi.mem_leviSet_of_le_levi hR hS.mem hS.opp hY hYV) hs

theorem pointsDetermined_restrict :
    PointsDetermined (restrict (leviSet R A A₀) (levi R A A₀)) := by
  rintro _ ⟨X, ⟨hX, hXV⟩, rfl⟩ _ ⟨Y, ⟨hY, hYV⟩, rfl⟩ h
  congr 1
  refine Levi.eq_of_commuting_iff_of_mem_leviSet' hS.hyp hS.mem hS.sec8.2 hS.opp hX hY
    fun Z hZ => ?_
  have hZV : Z ≤ levi R A A₀ := le_gen hZ
  have h' := h _ ⟨Z, ⟨hZ, hZV⟩, rfl⟩
  rwa [commuting_subgroupOf_iff' hXV hZV, commuting_subgroupOf_iff' hYV hZV] at h'

theorem exists_ne_commuting_restrict :
    ∃ X ∈ restrict (leviSet R A A₀) (levi R A A₀), ∃ Y ∈ restrict (leviSet R A A₀) (levi R A A₀),
      X ≠ Y ∧ Commuting X Y := by
  have hR := hS.hyp.root
  obtain ⟨E, C, P, Q, hfr⟩ := hS.exists_isSubframe
  have h0 := (hfr.memQ 0).1
  have h1 := (hfr.memQ 1).1
  have hc : Commuting (Q 0) (Q 1) :=
    hS.commuting_of_mem_deltaSet' hfr.memE (hfr.memQ 0) (hfr.memQ 1)
  have hne : Q 0 ≠ Q 1 := by
    intro h
    refine (hfr.opposite 0).not_commuting (hR.ne_bot _ (hfr.memP 0).1.1.1) ?_
    rw [h]
    exact (hfr.commuting 0 1 (by decide)).mono le_sup_left le_sup_right
  exact ⟨_, ⟨Q 0, ⟨h0, le_gen h0⟩, rfl⟩, _, ⟨Q 1, ⟨h1, le_gen h1⟩, rfl⟩,
    fun e => hne ((subgroupOf_inj_of_le (le_gen h0) (le_gen h1)).1 e),
    (commuting_subgroupOf_iff' (le_gen h0) (le_gen h1)).2 hc⟩

theorem card_eq_two_of_exists_restrict
    (h : ∃ X ∈ restrict (leviSet R A A₀) (levi R A A₀), Nat.card X = 2) : Nat.card A = 2 := by
  obtain ⟨_, ⟨X, ⟨hX, hXV⟩, rfl⟩, h2⟩ := h
  rw [← h2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXV).toEquiv]
  exact hS.hyp.root.card_eq hS.mem hX.1.1

theorem transvectionHyp_restrict (hconn : LeviConnected R A A₀)
    (hsmall : (∃ X ∈ restrict (leviSet R A A₀) (levi R A A₀), Nat.card X = 2) →
      IsSimpleGroup (commutator (levi R A A₀)) ∧
        ThickLines (restrict (leviSet R A A₀) (levi R A A₀))) :
    TransvectionHyp (levi R A A₀) (restrict (leviSet R A A₀) (levi R A A₀)) where
  finite := by
    have := hS.hyp.finite
    infer_instance
  cls := hS.isTransvectionClass_restrict hconn
  points := hS.pointsDetermined_restrict
  center := hS.center_levi_eq_bot
  rank := hS.exists_ne_commuting_restrict
  small := hsmall

theorem meetsLines : MeetsLines (leviSet R A A₀) := by
  intro X hX Y hY hXY hc W hW
  obtain ⟨Z, hZ, hZW, hZline⟩ := hS.exists_commuting_mem_line hX hY hXY hc hW
  exact ⟨Z, ⟨hZ, hZline⟩, hZW.symm⟩

theorem le_sup_of_isSubframe {E C : Subgroup G} {P Q : Fin 3 → Subgroup G}
    (hfr : IsSubframe R A A₀ E C P Q) {X : Subgroup G} (hX : X ∈ leviSet R A A₀)
    (h0 : Commuting X (P 0)) (h0' : Commuting X (Q 0)) (h1 : Commuting X (P 1))
    (h1' : Commuting X (Q 1)) : X ≤ P 2 ⊔ Q 2 := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  obtain ⟨f, -, hf, -⟩ := hS.opp.2.exists_mulEquiv_SL2' hR hS.mem
  set S := {X | X ∈ leviSet R A A₀ ∧ Commuting X (P 0) ∧ Commuting X (Q 0) ∧
    Commuting X (P 1) ∧ Commuting X (Q 1)} with hSdef
  set T : Set (Subgroup G) := insert (P 2) ((fun x => conjSub (Q 2) x) '' (P 2 : Set G))
    with hTdef
  have hle : S.ncard ≤ 2 ^ f + 1 := hS.ncard_perp_le hfr hf
  have hcomm : ∀ Y, Y ≤ P 2 ⊔ Q 2 → Commuting Y (P 0) ∧ Commuting Y (Q 0) ∧
      Commuting Y (P 1) ∧ Commuting Y (Q 1) := by
    intro Y hY
    have c0 := (hfr.commuting 2 0 (by decide)).mono hY le_rfl
    have c1 := (hfr.commuting 2 1 (by decide)).mono hY le_rfl
    exact ⟨c0.mono le_rfl le_sup_left, c0.mono le_rfl le_sup_right, c1.mono le_rfl le_sup_left,
      c1.mono le_rfl le_sup_right⟩
  have hTS : T ⊆ S := by
    rintro Y (rfl | ⟨x, hx, rfl⟩)
    · exact ⟨(hfr.memP 2).1, hcomm _ le_sup_left⟩
    · exact ⟨Levi.conjSub_mem_leviSet_of_mem_levi hR (hfr.memQ 2).1 (le_gen (hfr.memP 2).1 hx),
        hcomm _ (conjSub_le le_sup_right (Subgroup.mem_sup_left hx))⟩
  have hinj : Set.InjOn (fun x => conjSub (Q 2) x) (P 2 : Set G) := by
    intro x hx y hy hxy
    have h := (hfr.opposite 2).eq_one_of_conjSub_eq (a := y⁻¹ * x)
      ((P 2).mul_mem ((P 2).inv_mem hy) hx) (by
        change conjSub (Q 2) x = conjSub (Q 2) y at hxy
        rw [conjSub_mul, hxy, ← conjSub_mul, inv_mul_cancel, conjSub_one])
    exact (inv_mul_eq_one.1 h).symm
  have hnot : P 2 ∉ (fun x => conjSub (Q 2) x) '' (P 2 : Set G) := by
    rintro ⟨x, hx, hxe⟩
    apply (hfr.opposite 2).ne
    have hQ : Q 2 = conjSub (P 2) x⁻¹ := by
      change conjSub (Q 2) x = P 2 at hxe
      rw [← hxe, ← conjSub_mul, inv_mul_cancel, conjSub_one]
    rw [hQ, conjSub_of_mem ((P 2).inv_mem hx)]
  have hTcard : T.ncard = 2 ^ f + 1 := by
    rw [hTdef, Set.ncard_insert_of_notMem hnot, hinj.ncard_image,
      ← Nat.card_coe_set_eq, SetLike.coe_sort_coe, hR.card_eq (hfr.memP 2).1.1.1 hS.mem, hf]
  have hST : T = S := Set.eq_of_subset_of_ncard_le hTS (by omega)
  have hXS : X ∈ S := ⟨hX, h0, h0', h1, h1'⟩
  rw [← hST] at hXS
  rcases hXS with rfl | ⟨x, hx, rfl⟩
  · exact le_sup_left
  · exact conjSub_le le_sup_right (Subgroup.mem_sup_left hx)

end Sec12

end CFSG.Timmesfeld.ARS
