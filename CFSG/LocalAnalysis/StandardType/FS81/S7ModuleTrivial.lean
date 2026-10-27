module

public import CFSG.LocalAnalysis.StandardType.FS81.S7E7Incl
public import CFSG.LocalAnalysis.StandardType.FS81.S7CentDefs
import CFSG.LocalAnalysis.StandardType.FS81.S7E7InclRange
import CFSG.LocalAnalysis.SeitzReduction.EPilotHeisIrr
import CFSG.LocalAnalysis.SeitzReduction.EnKLHeis
import CFSG.Mathlib.Decide.Bounded

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction CFSG.QuasithinUnique
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped commutatorElement

local notation "tθ" => EPilot.pinnedElt Tag.E8 (highRoot Tag.E8) (1 : GaloisField 2 1)
local notation "Qθ" => EPilot.highRadical Tag.E8 (GaloisField 2 1)
local notation "s₇" => EPilot.pinnedElt Tag.E7 (highRoot Tag.E7) (1 : ZMod 2)
local notation "Q₇" => EPilot.highRadical Tag.E7 (ZMod 2)

private noncomputable abbrev E8G := adjointGroup Tag.E8 (GaloisField 2 1)

private noncomputable abbrev E8M := ModGL Tag.E8 (GaloisField 2 1)

private noncomputable abbrev E7G := adjointGroup Tag.E7 (ZMod 2)

private noncomputable abbrev E7M := ModGL Tag.E7 (ZMod 2)

private def e7Theta : Fin (Tag.rank .E8) → ℤ := E8Pilot.e7Embed (highRoot .E7)

private def Tset : Set (Fin (Tag.rank .E8) → ℤ) :=
  {ν | ν ∈ rootFinset .E8 ∧ ν (highNode .E8) = 1 ∧ ν - e7Theta ∈ rootFinset .E8}

section E7Model

open scoped CFSG.Decide.Bounded in
private theorem e7Embed_add_not_root :
    ∀ μ ∈ rootFinset .E8, μ (highNode .E8) = 1 →
      μ - E8Pilot.e7Embed (highRoot .E7) ∈ rootFinset .E8 →
      ∀ β ∈ rootFinset .E7,
        0 < CFSG.LieType.Steinberg.Adjoint.iform β (highRoot .E7) →
        μ + E8Pilot.e7Embed β ∉ rootFinset .E8 := by
  decide +kernel

private noncomputable abbrev QθM : Subgroup E8M :=
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis.Qθ Tag.E8 (GaloisField 2 1)

private noncomputable abbrev Dθ : Subgroup E8G := EPilot.perpLevi Tag.E8 (GaloisField 2 1)

private def QT : Subgroup E8G where
  carrier := {q | q ∈ Qθ ∧ ∀ ν, ν ∉ Tset → heisCoord .E8 (GaloisField 2 1) (q : E8M) ν = 0}
  mul_mem' := by
    rintro q q' ⟨hq, hqs⟩ ⟨hq', hqs'⟩
    refine ⟨mul_mem hq hq', fun ν hν => ?_⟩
    have hqQ := EPilot.HeisIrr.mem_Qθ_of_mem_highRadical rfl hq
    have hq'Q := EPilot.HeisIrr.mem_Qθ_of_mem_highRadical rfl hq'
    rw [show ((q * q' : E8G) : E8M) = (q : E8M) * (q' : E8M) from rfl,
      (heisCoord_spec .E8 (GaloisField 2 1)).mul _ hqQ _ hq'Q, Pi.add_apply,
      hqs ν hν, hqs' ν hν, add_zero]
  one_mem' := by
    refine ⟨one_mem _, fun ν _ => ?_⟩
    rw [show ((1 : E8G) : E8M) = 1 from rfl]
    exact congrFun (heisCoord_one (τ := .E8) (K := GaloisField 2 1)) ν
  inv_mem' := by
    rintro q ⟨hq, hqs⟩
    refine ⟨inv_mem hq, fun ν hν => ?_⟩
    have hqQ := EPilot.HeisIrr.mem_Qθ_of_mem_highRadical rfl hq
    rw [show ((q⁻¹ : E8G) : E8M) = (q : E8M)⁻¹ from rfl, heisCoord_inv hqQ,
      Pi.neg_apply, hqs ν hν, neg_zero]

private theorem tθ_mem_QT : tθ ∈ QT := by
  refine ⟨pinnedElt_highRoot_mem_highRadical, fun ν _ => ?_⟩
  rw [show (tθ : E8M) = pinnedX .E8 (GaloisField 2 1) (highRoot .E8) 1 from rfl]
  exact congrFun ((heisCoord_spec .E8 (GaloisField 2 1)).pinnedX_highRoot 1) ν

private theorem mem_zpowers_of_orderOf_eq_two {G : Type*} [Group G] {t x : G}
    (ht : orderOf t = 2) : x ∈ Subgroup.zpowers t ↔ x = 1 ∨ x = t := by
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_mod_orderOf, ht, Nat.cast_ofNat]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [h, zpow_zero]
    · right
      rw [h, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

private theorem e7Incl_s7_eq :
    e7Incl s₇ = EPilot.pinnedElt .E8 e7Theta (1 : GaloisField 2 1) := by
  rw [e7Incl_pinnedElt (isRoot_highRoot .E7) 1, map_one]
  rfl

private theorem orderOf_e7Incl_s7 : orderOf (e7Incl s₇) = 2 := by
  rw [e7Incl_s7_eq]
  exact orderOf_pinnedElt_one e7Theta

private theorem heisCoord_conj_eq_of_forall (β : Fin (Tag.rank .E8) → ℤ)
    (hβ : IsRoot .E8 β) (hβ0 : β (iθ .E8) = 0) (s : GaloisField 2 1) (w : E8G)
    (hw : (w : E8M) ∈ QθM)
    (hfix : ∀ ν, ν ∈ rootFinset .E8 →
      heisCoord .E8 (GaloisField 2 1) (w : E8M) (ν - β) = 0) :
    heisCoord .E8 (GaloisField 2 1)
        ((EPilot.pinnedElt .E8 β s * w * (EPilot.pinnedElt .E8 β s)⁻¹ : E8G) : E8M) =
      heisCoord .E8 (GaloisField 2 1) (w : E8M) := by
  funext ν
  have hconj := (EPilot.heisCoord_conj_pinnedX_of_deg_zero (τ := .E8)
    (K := GaloisField 2 1) (Or.inr (Or.inr rfl)) hβ hβ0 s hw).2 ν
  rw [show ((EPilot.pinnedElt .E8 β s * w * (EPilot.pinnedElt .E8 β s)⁻¹ : E8G) : E8M) =
      pinnedX .E8 (GaloisField 2 1) β s * (w : E8M) *
        (pinnedX .E8 (GaloisField 2 1) β s)⁻¹ from rfl, hconj]
  by_cases hν : ν ∈ rootFinset .E8
  · rw [if_pos hν, hfix ν hν, mul_zero, add_zero]
  · rw [if_neg hν, add_zero]

private theorem commutator_eq_mul_conj_inv (q : E8G) :
    ⁅q, EPilot.pinnedElt .E8 e7Theta 1⁆ =
      q * (EPilot.pinnedElt .E8 e7Theta 1 * q *
        (EPilot.pinnedElt .E8 e7Theta 1)⁻¹)⁻¹ := by
  rw [commutatorElement_def]
  group

private theorem heisCoord_commutator_e7Incl_s7 {q : E8G} (hq : q ∈ Qθ) :
    ∀ ν, ν ∉ Tset →
      heisCoord .E8 (GaloisField 2 1) ((⁅q, e7Incl s₇⁆ : E8G) : E8M) ν = 0 := by
  have hqM := EPilot.HeisIrr.mem_Qθ_of_mem_highRadical rfl hq
  have hγ : IsRoot .E8 e7Theta := E8Pilot.isRoot_e7Embed (isRoot_highRoot .E7)
  have hγ0 : e7Theta (iθ .E8) = 0 := E8Pilot.e7Embed_highNode (highRoot .E7)
  have hform := (EPilot.heisCoord_conj_pinnedX_of_deg_zero (τ := .E8)
    (K := GaloisField 2 1) (Or.inr (Or.inr rfl)) hγ hγ0 (1 : GaloisField 2 1) hqM)
  intro ν hνT
  rw [e7Incl_s7_eq, commutator_eq_mul_conj_inv q]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [(heisCoord_spec .E8 (GaloisField 2 1)).mul _ hqM _ (inv_mem hform.1),
    Pi.add_apply, heisCoord_inv hform.1, Pi.neg_apply, hform.2 ν]
  by_cases hν : ν ∈ rootFinset .E8
  · rw [if_pos hν, one_mul]
    have hzero : heisCoord .E8 (GaloisField 2 1) (q : E8M) (ν - e7Theta) = 0 := by
      by_contra hne
      have hD : ν - e7Theta ∈ Deg1 .E8 := by
        by_contra hnot
        exact hne ((heisCoord_spec .E8 (GaloisField 2 1)).support q hqM (ν - e7Theta) hnot)
      have hν1 : ν (highNode .E8) = 1 := by
        have hdeg := (CoordAux.mem_Deg1.1 hD).2
        rw [Pi.sub_apply, hγ0] at hdeg
        have hnode : iθ .E8 = highNode .E8 := rfl
        rw [hnode, sub_zero] at hdeg
        exact hdeg
      exact hνT ⟨hν, hν1, mem_rootFinset.2 (CoordAux.mem_Deg1.1 hD).1⟩
    rw [hzero, add_zero, add_neg_cancel]
  · rw [if_neg hν, add_zero, add_neg_cancel]

private theorem commutator_e7Incl_s7_mem_highRadical {q : E8G} (hq : q ∈ Qθ) :
    ⁅q, e7Incl s₇⁆ ∈ Qθ := by
  have hqM := EPilot.HeisIrr.mem_Qθ_of_mem_highRadical rfl hq
  have hγ : IsRoot .E8 e7Theta := E8Pilot.isRoot_e7Embed (isRoot_highRoot .E7)
  have hγ0 : e7Theta (iθ .E8) = 0 := E8Pilot.e7Embed_highNode (highRoot .E7)
  have hform := (EPilot.heisCoord_conj_pinnedX_of_deg_zero (τ := .E8)
    (K := GaloisField 2 1) (Or.inr (Or.inr rfl)) hγ hγ0 (1 : GaloisField 2 1) hqM)
  have hconj_mem : (EPilot.pinnedElt .E8 e7Theta 1 * q *
      (EPilot.pinnedElt .E8 e7Theta 1)⁻¹ : E8G) ∈ Qθ :=
    Subgroup.mem_subgroupOf.2 hform.1
  rw [e7Incl_s7_eq, commutator_eq_mul_conj_inv q]
  exact mul_mem hq (inv_mem hconj_mem)

private theorem commutator_e7Incl_s7_mem_QT {q : E8G} (hq : q ∈ Qθ) :
    ⁅q, e7Incl s₇⁆ ∈ QT :=
  ⟨commutator_e7Incl_s7_mem_highRadical hq, heisCoord_commutator_e7Incl_s7 hq⟩

private theorem modW_le_QT : modW Qθ tθ (e7Incl s₇) ≤ QT := by
  refine sup_le ?_ (Subgroup.zpowers_le.2 tθ_mem_QT)
  refine Subgroup.commutator_le.2 fun q hq z hz => ?_
  rcases (mem_zpowers_of_orderOf_eq_two orderOf_e7Incl_s7).1 hz with rfl | rfl
  · simp
  · exact commutator_e7Incl_s7_mem_QT hq

private theorem commutator_pinnedElt_mem_zpowers (β : Fin (Tag.rank .E8) → ℤ)
    (hβ : IsRoot .E8 β) (hβ0 : β (iθ .E8) = 0) (s : GaloisField 2 1) (w : E8G)
    (hw : w ∈ QT) (hfin : ∀ μ, μ ∈ Tset → μ + β ∉ rootFinset .E8) :
    EPilot.pinnedElt .E8 β s * w * (EPilot.pinnedElt .E8 β s)⁻¹ * w⁻¹ ∈
      Subgroup.zpowers tθ := by
  have hwQ : w ∈ Qθ := hw.1
  have hwM := EPilot.HeisIrr.mem_Qθ_of_mem_highRadical rfl hwQ
  have hfix : ∀ ν, ν ∈ rootFinset .E8 →
      heisCoord .E8 (GaloisField 2 1) (w : E8M) (ν - β) = 0 := by
    intro ν hν
    by_contra hne
    have hmem : ν - β ∈ Tset := by
      by_contra hnot
      exact hne (hw.2 (ν - β) hnot)
    have := hfin (ν - β) hmem
    rw [sub_add_cancel] at this
    exact this hν
  have hconj := heisCoord_conj_eq_of_forall β hβ hβ0 s w hwM hfix
  have hform := (EPilot.heisCoord_conj_pinnedX_of_deg_zero (τ := .E8)
    (K := GaloisField 2 1) (Or.inr (Or.inr rfl)) hβ hβ0 s hwM)
  have hcoord : heisCoord .E8 (GaloisField 2 1)
      ((EPilot.pinnedElt .E8 β s * w * (EPilot.pinnedElt .E8 β s)⁻¹ * w⁻¹ : E8G) : E8M) = 0 := by
    funext ν
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [(heisCoord_spec .E8 (GaloisField 2 1)).mul _ hform.1 _ (inv_mem hwM), Pi.add_apply,
      heisCoord_inv hwM, Pi.neg_apply,
      show pinnedX .E8 (GaloisField 2 1) β s * (w : E8M) *
          (pinnedX .E8 (GaloisField 2 1) β s)⁻¹ =
        ((EPilot.pinnedElt .E8 β s * w * (EPilot.pinnedElt .E8 β s)⁻¹ : E8G) : E8M)
        from rfl,
      hconj]
    exact add_neg_cancel _
  have hconj_mem : (EPilot.pinnedElt .E8 β s * w *
      (EPilot.pinnedElt .E8 β s)⁻¹ : E8G) ∈ Qθ :=
    Subgroup.mem_subgroupOf.2 hform.1
  exact EPilot.HeisIrr.mem_zpowers_of_heisCoord_eq_zero rfl natCard_galoisField_two_one
    (mul_mem hconj_mem (inv_mem hwQ)) hcoord

private theorem mem_centralizer_tθ_of_mem_Dθ {x : E8G} (hx : x ∈ Dθ) :
    x ∈ Subgroup.centralizer ({tθ} : Set E8G) := by
  have h := (centralizer_pinnedElt_highRoot_E8 (K := GaloisField 2 1)).1
  rw [h]
  exact (le_sup_right : Dθ ≤ Qθ ⊔ Dθ) hx

private theorem commute_tθ_of_mem_Dθ {x : E8G} (hx : x ∈ Dθ) : x * tθ = tθ * x :=
  (Subgroup.mem_centralizer_iff.1 (mem_centralizer_tθ_of_mem_Dθ hx) tθ
    (Set.mem_singleton tθ)).symm

private theorem commute_zpowers_of_mem_Dθ {x : E8G} (hx : x ∈ Dθ) {c : E8G}
    (hc : c ∈ Subgroup.zpowers tθ) : x * c = c * x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  exact (Commute.zpow_right (commute_tθ_of_mem_Dθ hx) k).eq

private def S : Subgroup E8G where
  carrier := {x | x ∈ Dθ ∧ ∀ w ∈ QT, x * w * x⁻¹ * w⁻¹ ∈ Subgroup.zpowers tθ}
  mul_mem' := by
    rintro x y ⟨hxD, hxS⟩ ⟨hyD, hyS⟩
    refine ⟨mul_mem hxD hyD, fun w hw => ?_⟩
    have hid : (x * y) * w * (x * y)⁻¹ * w⁻¹ =
        x * (y * w * y⁻¹ * w⁻¹) * x⁻¹ * (x * w * x⁻¹ * w⁻¹) := by group
    rw [hid]
    have hc : x * (y * w * y⁻¹ * w⁻¹) * x⁻¹ = y * w * y⁻¹ * w⁻¹ := by
      rw [commute_zpowers_of_mem_Dθ hxD (hyS w hw)]
      group
    rw [hc]
    exact mul_mem (hyS w hw) (hxS w hw)
  one_mem' := by
    refine ⟨one_mem Dθ, fun w _ => ?_⟩
    rw [show (1 : E8G) * w * 1⁻¹ * w⁻¹ = 1 from by group]
    exact one_mem _
  inv_mem' := by
    rintro x ⟨hxD, hxS⟩
    refine ⟨inv_mem hxD, fun w hw => ?_⟩
    have hid : x⁻¹ * w * (x⁻¹)⁻¹ * w⁻¹ =
        x⁻¹ * (x * w * x⁻¹ * w⁻¹)⁻¹ * x := by group
    rw [hid]
    have hc : x⁻¹ * (x * w * x⁻¹ * w⁻¹)⁻¹ * x = (x * w * x⁻¹ * w⁻¹)⁻¹ := by
      have h := commute_zpowers_of_mem_Dθ hxD (inv_mem (hxS w hw))
      calc x⁻¹ * (x * w * x⁻¹ * w⁻¹)⁻¹ * x
          = x⁻¹ * ((x * w * x⁻¹ * w⁻¹)⁻¹ * x) := by rw [mul_assoc]
        _ = x⁻¹ * (x * (x * w * x⁻¹ * w⁻¹)⁻¹) := by rw [← h]
        _ = (x * w * x⁻¹ * w⁻¹)⁻¹ := by group
    rw [hc]
    exact inv_mem (hxS w hw)

private theorem mem_S_iff {x : E8G} :
    x ∈ S ↔ x ∈ Dθ ∧ ∀ w ∈ QT, x * w * x⁻¹ * w⁻¹ ∈ Subgroup.zpowers tθ := Iff.rfl

private theorem e7Incl_pinnedElt_mem_S {α : Fin (Tag.rank .E7) → ℤ}
    (hα : α ∈ parabolicRadicalRoots .E7 (EPilot.perpNodes .E7)) (c : ZMod 2) :
    e7Incl (EPilot.pinnedElt .E7 α c) ∈ S := by
  have hα' := (EPilot.mem_parabolicRadicalRoots_perpNodes_iff_iform
    (Or.inr (Or.inl rfl))).1 hα
  have hfin : ∀ μ, μ ∈ Tset → μ + E8Pilot.e7Embed α ∉ rootFinset .E8 := by
    intro μ hμ
    exact e7Embed_add_not_root μ hμ.1 hμ.2.1 hμ.2.2 α (mem_rootFinset.2 hα'.1) hα'.2
  have hβ : IsRoot .E8 (E8Pilot.e7Embed α) := E8Pilot.isRoot_e7Embed hα'.1
  have hβ0 : E8Pilot.e7Embed α (iθ .E8) = 0 := E8Pilot.e7Embed_highNode α
  rw [e7Incl_pinnedElt hα'.1 c]
  exact ⟨EPilot.pinnedElt_mem_perpLevi (E8Pilot.e7Embed_mem_perpRoots hα'.1)
      (zmodTwoEquivGalois c),
    fun w hw => commutator_pinnedElt_mem_zpowers (E8Pilot.e7Embed α) hβ hβ0
      (zmodTwoEquivGalois c) w hw hfin⟩

private theorem parabolicRadical_E7_le_S_comap :
    parabolicRadical .E7 (ZMod 2) (EPilot.perpNodes .E7) ≤
      (S.comap e7Incl).map E7G.subtype := by
  refine iSup₂_le fun α hα => ?_
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  refine Subgroup.mem_map.2 ⟨EPilot.pinnedElt .E7 α c, ?_, ?_⟩
  · exact Subgroup.mem_comap.mpr (e7Incl_pinnedElt_mem_S hα c)
  · rfl

theorem highRadical_E7_trivial_on_modW :
    ∀ x ∈ (Q₇).map e7Incl, ∀ w ∈ modW Qθ tθ (e7Incl s₇),
      x * w * x⁻¹ * w⁻¹ ∈ Subgroup.zpowers tθ := by
  have hmap : (Q₇).map e7Incl ≤ S := by
    rw [Subgroup.map_le_iff_le_comap]
    intro g hg
    have hgR : (g : E7M) ∈ parabolicRadical .E7 (ZMod 2) (EPilot.perpNodes .E7) :=
      Subgroup.mem_subgroupOf.1 hg
    obtain ⟨h, hh, hhe⟩ := parabolicRadical_E7_le_S_comap hgR
    have : h = g := Subtype.ext hhe
    rwa [this] at hh
  intro x hx w hw
  exact (mem_S_iff.1 (hmap hx)).2 w (modW_le_QT hw)

end E7Model

end CFSG.StandardType.FrameRoute.FS81

end
