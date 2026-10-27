module

public import CFSG.LocalAnalysis.StandardType.FS81.S7E7Incl
import CFSG.LocalAnalysis.StandardType.FS81.S7E7InclRange
import CFSG.LocalAnalysis.StandardType.FS81.S7RootSL2
import CFSG.LocalAnalysis.SeitzReduction.E7PilotNeighbourLevi
import CFSG.LocalAnalysis.SeitzReduction.E8PilotQ2SwapDescent
import CFSG.GroupTheory.PCore.PCoreOfMulEquiv
import CFSG.LocalAnalysis.SeitzReduction.E8PilotSwapLift
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotWeakCTGlobal
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotUniqueTypeGraph

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.SeitzReduction CFSG.QuasithinUnique

local notation "GF₂" => GaloisField 2 1
local notation "tθ" => EPilot.pinnedElt Tag.E8 (highRoot Tag.E8) (1 : GaloisField 2 1)
local notation "Qθ" => EPilot.highRadical Tag.E8 (GaloisField 2 1)
local notation "s₇" => EPilot.pinnedElt Tag.E7 (highRoot Tag.E7) (1 : ZMod 2)
local notation "Q₇" => EPilot.highRadical Tag.E7 (ZMod 2)

section E7Model


private theorem canonicalRep_conj_pinnedX_E8 (w : WeylGroup .E8)
    {γ : Fin (Tag.rank .E8) → ℤ} (hγ : IsRoot .E8 γ) (c : GF₂) :
    canonicalRep (coxeterSystem .E8) GF₂ w * pinnedX .E8 GF₂ γ c *
        (canonicalRep (coxeterSystem .E8) GF₂ w)⁻¹ = pinnedX .E8 GF₂ (w • γ) c := by
  obtain ⟨ε, hε, h⟩ :=
    CFSG.LieType.Chevalley.exists_canonicalRep_mul_pinnedX_mul_inv GF₂ w hγ
  have hε1 : ε = 1 := by
    have h2 : (2 : GF₂) = 0 := CharTwo.two_eq_zero
    have : (ε - 1) * (ε - 1) = 0 := by linear_combination hε + (1 - ε) * h2
    exact sub_eq_zero.1 (mul_self_eq_zero.1 this)
  have hc := h c
  rwa [hε1, one_mul] at hc

private theorem e7Incl_conj (x a : ↥(adjointGroup .E7 (ZMod 2))) :
    e7Incl ((MulAut.conj x).toMonoidHom a) =
      (MulAut.conj (e7Incl x)).toMonoidHom (e7Incl a) := by
  change e7Incl (MulAut.conj x a) = MulAut.conj (e7Incl x) (e7Incl a)
  simp only [MulAut.conj_apply, map_mul, map_inv]

private theorem map_conj_map_le_conj {A : Subgroup ↥(adjointGroup .E7 (ZMod 2))}
    {B : Subgroup ↥(adjointGroup .E8 GF₂)} {x : ↥(adjointGroup .E7 (ZMod 2))}
    {y : ↥(adjointGroup .E8 GF₂)}
    (h : A.map e7Incl ≤ B.map (MulAut.conj y).toMonoidHom) :
    (A.map (MulAut.conj x).toMonoidHom).map e7Incl ≤
      B.map (MulAut.conj (e7Incl x * y)).toMonoidHom := by
  intro z hz
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hz
  obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.1 ha
  obtain ⟨b, hb, hb'⟩ := Subgroup.mem_map.1 (h ⟨a₀, ha₀, rfl⟩)
  refine Subgroup.mem_map.2 ⟨b, hb, ?_⟩
  rw [e7Incl_conj x a₀, ← hb']
  change MulAut.conj (e7Incl x * y) b = MulAut.conj (e7Incl x) (MulAut.conj y b)
  simp only [MulAut.conj_apply]
  group

private theorem map_e7Incl_highRadical_le (B : Subgroup ↥(adjointGroup .E8 GF₂))
    (hgen : ∀ δ ∈ CFSG.LieType.Chevalley.parabolicRadicalRoots .E7 (EPilot.perpNodes .E7),
      ∀ c : ZMod 2,
      e7Incl (EPilot.pinnedElt .E7 δ c) ∈ B) :
    (Q₇).map e7Incl ≤ B := by
  rw [Subgroup.map_le_iff_le_comap]
  have hgen' : CFSG.LieType.Chevalley.parabolicRadical .E7 (ZMod 2) (EPilot.perpNodes .E7) ≤
      (B.comap e7Incl).map (adjointGroup .E7 (ZMod 2)).subtype := by
    rw [CFSG.LieType.Chevalley.parabolicRadical, CFSG.Blueprint.Chevalley.rootSpan]
    refine iSup_le fun δ => iSup_le fun hδ => ?_
    rw [CFSG.Blueprint.Chevalley.rootSubgroup]
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨c, rfl⟩
    exact ⟨EPilot.pinnedElt .E7 δ c, hgen δ hδ c, rfl⟩
  intro y hy
  rw [Subgroup.mem_comap]
  have hyS : (y : ModGL .E7 (ZMod 2)) ∈
      CFSG.LieType.Chevalley.parabolicRadical .E7 (ZMod 2) (EPilot.perpNodes .E7) := by
    rwa [EPilot.highRadical, Subgroup.mem_subgroupOf] at hy
  obtain ⟨k, hk, hkval⟩ := hgen' hyS
  have hky : k = y := Subtype.ext hkval
  rw [← hky]
  exact hk

private theorem pCoreOf_centralizer_pinnedElt_E7 :
    pCoreOf 2 (Subgroup.centralizer ({s₇} : Set ↥(adjointGroup .E7 (ZMod 2)))) = Q₇ := by
  obtain ⟨-, -, -, hQ⟩ := KGExc.centralizer_decomp_highRoot (K := ZMod 2)
    (Or.inr (Or.inl rfl)) E7Pilot.isQuasisimple_perpLevi_E7 E7Pilot.center_perpLevi_E7_eq_bot
  exact hQ

private theorem exists_conj_pinnedElt_e7Incl_pinnedElt :
    ∃ m : ↥(adjointGroup .E8 GF₂), m * tθ * m⁻¹ = e7Incl s₇ ∧
      (Q₇).map e7Incl ≤ (Qθ).map (MulAut.conj m).toMonoidHom := by
  obtain ⟨w, hw⟩ := EPilot.exists_smul_highRoot_eq (Or.inr (Or.inr rfl))
    (E8Pilot.isRoot_e7Embed (isRoot_highRoot .E7))
  set m : ↥(adjointGroup .E8 GF₂) :=
    ⟨canonicalRep (coxeterSystem .E8) GF₂ w, canonicalRep_mem_adjointGroup _ GF₂ w⟩ with hmdef
  have hm : m * tθ * m⁻¹ = e7Incl s₇ := by
    have hs7 : e7Incl s₇ =
        EPilot.pinnedElt .E8 (E8Pilot.e7Embed (highRoot .E7)) (1 : GF₂) := by
      rw [e7Incl_pinnedElt (isRoot_highRoot .E7) (1 : ZMod 2), map_one]
    rw [hs7]
    refine Subtype.ext ?_
    show (canonicalRep (coxeterSystem .E8) GF₂ w : ModGL .E8 GF₂) *
        pinnedX .E8 GF₂ (highRoot .E8) 1 *
        (canonicalRep (coxeterSystem .E8) GF₂ w : ModGL .E8 GF₂)⁻¹ =
      pinnedX .E8 GF₂ (E8Pilot.e7Embed (highRoot .E7)) 1
    rw [← hw]
    exact canonicalRep_conj_pinnedX_E8 w (isRoot_highRoot .E8) 1
  refine ⟨m, hm, ?_⟩
  refine map_e7Incl_highRadical_le ((Qθ).map (MulAut.conj m).toMonoidHom) ?_
  intro δ hδ c
  obtain ⟨hδroot, hδpos⟩ :=
    (EPilot.mem_parabolicRadicalRoots_perpNodes_iff_iform (Or.inr (Or.inl rfl))).1 hδ
  have hμroot : IsRoot .E8 (w⁻¹ • E8Pilot.e7Embed δ) :=
    IsRoot.smul (E8Pilot.isRoot_e7Embed hδroot) w⁻¹
  have hμpos : 0 < CFSG.LieType.Steinberg.Adjoint.iform (w⁻¹ • E8Pilot.e7Embed δ)
      (highRoot .E8) := by
    have hθ : (highRoot .E8) = w⁻¹ • (w • highRoot .E8) := (inv_smul_smul w _).symm
    rw [hθ, CFSG.LieType.Chevalley.iform_smul w⁻¹, hw, E8Pilot.iform_e7Embed]
    exact hδpos
  have hμmem : (w⁻¹ • E8Pilot.e7Embed δ) ∈
      CFSG.LieType.Chevalley.parabolicRadicalRoots .E8 (EPilot.perpNodes .E8) :=
    (EPilot.mem_parabolicRadicalRoots_perpNodes_iff_iform (Or.inr (Or.inr rfl))).2
      ⟨hμroot, hμpos⟩
  have hq : EPilot.pinnedElt .E8 (w⁻¹ • E8Pilot.e7Embed δ) (zmodTwoEquivGalois c) ∈ Qθ := by
    rw [EPilot.highRadical, Subgroup.mem_subgroupOf, CFSG.LieType.Chevalley.parabolicRadical]
    exact CFSG.LieType.Chevalley.rootSubgroup_le_rootSpan hμmem
      (Subgroup.subset_closure ⟨zmodTwoEquivGalois c, rfl⟩)
  have hconjval : m * EPilot.pinnedElt .E8 (w⁻¹ • E8Pilot.e7Embed δ) (zmodTwoEquivGalois c) *
        m⁻¹ = EPilot.pinnedElt .E8 (E8Pilot.e7Embed δ) (zmodTwoEquivGalois c) := by
    refine Subtype.ext ?_
    show (canonicalRep (coxeterSystem .E8) GF₂ w : ModGL .E8 GF₂) *
        pinnedX .E8 GF₂ (w⁻¹ • E8Pilot.e7Embed δ) (zmodTwoEquivGalois c) *
        (canonicalRep (coxeterSystem .E8) GF₂ w : ModGL .E8 GF₂)⁻¹ =
      pinnedX .E8 GF₂ (E8Pilot.e7Embed δ) (zmodTwoEquivGalois c)
    have h := canonicalRep_conj_pinnedX_E8 w hμroot (zmodTwoEquivGalois c)
    rwa [smul_inv_smul w (E8Pilot.e7Embed δ)] at h
  have hconj : EPilot.pinnedElt .E8 (E8Pilot.e7Embed δ) (zmodTwoEquivGalois c) =
      (MulAut.conj m).toMonoidHom
        (EPilot.pinnedElt .E8 (w⁻¹ • E8Pilot.e7Embed δ) (zmodTwoEquivGalois c)) := by
    show EPilot.pinnedElt .E8 (E8Pilot.e7Embed δ) (zmodTwoEquivGalois c) =
      m * EPilot.pinnedElt .E8 (w⁻¹ • E8Pilot.e7Embed δ) (zmodTwoEquivGalois c) * m⁻¹
    exact hconjval.symm
  rw [e7Incl_pinnedElt hδroot c, hconj]
  exact ⟨EPilot.pinnedElt .E8 (w⁻¹ • E8Pilot.e7Embed δ) (zmodTwoEquivGalois c), hq, rfl⟩

theorem exists_conj_pinnedElt_e7Incl (s : ↥(adjointGroup .E7 (ZMod 2)))
    (hs : (s : ModGL .E7 (ZMod 2)) ∈ EPilot.highRootSL2 .E7 (ZMod 2)) (hs2 : orderOf s = 2) :
    ∃ m : ↥(adjointGroup .E8 GF₂), m * tθ * m⁻¹ = e7Incl s ∧
      (pCoreOf 2 (Subgroup.centralizer ({s} : Set ↥(adjointGroup .E7 (ZMod 2))))).map e7Incl ≤
        (Qθ).map (MulAut.conj m).toMonoidHom := by
  obtain ⟨h, _, hhs⟩ := exists_conj_pinnedElt_of_mem_highRootSL2 s hs hs2
  obtain ⟨m, hm, hmle⟩ := exists_conj_pinnedElt_e7Incl_pinnedElt
  refine ⟨e7Incl h * m, ?_, ?_⟩
  · calc e7Incl h * m * tθ * (e7Incl h * m)⁻¹
        = e7Incl h * (m * tθ * m⁻¹) * (e7Incl h)⁻¹ := by group
      _ = e7Incl h * e7Incl s₇ * (e7Incl h)⁻¹ := by rw [hm]
      _ = e7Incl (h * s₇ * h⁻¹) := by rw [map_mul, map_mul, map_inv]
      _ = e7Incl s := by rw [hhs]
  · have hC : Subgroup.centralizer ({s} : Set ↥(adjointGroup .E7 (ZMod 2))) =
        (Subgroup.centralizer ({s₇} : Set ↥(adjointGroup .E7 (ZMod 2)))).map
          (MulAut.conj h).toMonoidHom := by
      rw [← hhs, CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv (MulAut.conj h)
        ({s₇} : Set ↥(adjointGroup .E7 (ZMod 2))), Set.image_singleton]
      rfl
    have hpC : pCoreOf 2 (Subgroup.centralizer ({s} : Set ↥(adjointGroup .E7 (ZMod 2)))) =
        (Q₇).map (MulAut.conj h).toMonoidHom := by
      rw [hC, CFSG.GroupTheory.map_pCoreOf_mulEquiv 2 (MulAut.conj h)
        (Subgroup.centralizer ({s₇} : Set ↥(adjointGroup .E7 (ZMod 2)))),
        pCoreOf_centralizer_pinnedElt_E7]
    calc (pCoreOf 2 (Subgroup.centralizer ({s} : Set ↥(adjointGroup .E7 (ZMod 2))))).map e7Incl
        = ((Q₇).map (MulAut.conj h).toMonoidHom).map e7Incl := by rw [hpC]
      _ ≤ (Qθ).map (MulAut.conj (e7Incl h * m)).toMonoidHom := map_conj_map_le_conj hmle

end E7Model

end CFSG.StandardType.FrameRoute.FS81

end
