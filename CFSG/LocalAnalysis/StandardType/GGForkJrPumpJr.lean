module

public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpDefs
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpAgree
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenLabels
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRootGenLift
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Transfer

variable {G : Type} [Group G] [Finite G]

theorem ggForkJr_of_known (hKG : GGForkRootSL2KGInput) (hRig : GGLabelRigidInput) :
    GGForkJr := by
  intro G _ _ p B Bs x L D J hcfg hInn hNT hp5 r hrL hrr
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hLsub : IsSubnormal L (Subgroup.centralizer ({x} : Set G)) := hS.2.2.2.1.2.1
  have hM : GGInnerDiagOnLabel GGForkRootSL2Label p Bs L := by
    have hmarkL := hcfg.1.2.2.2.2.2.2.2.1
    obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hH⟩ := largeEvenMarking_exists_hasLabel hmarkL
    have hsplit : LargeEvenSplit p lab := hH.1
    have hmark := ggInnerDiagOn_relabel hRig hInn.1 hlab hhas
    refine largeEvenMarking_mono ?_ hmark
    rintro lab' R' _ I' F' θ' ⟨h1, h2, h3⟩
    subst h1
    exact ⟨⟨hp5, hsplit⟩, h2, h3⟩
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll
    (S := fun lab => GGForkRootSL2Label p lab)
    (fun lab hlab hs => hKG p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨hs, hBsN, h3⟩, r₀, hlift, hT⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨hr₀, h3'⟩ := card_range_ggGamma_bstar_ge hcfg hL θ hBsN hlift
  have hTB := ggTorusTBGroup_of_marking hp hBs hSC hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) hr₀ h3'
  obtain ⟨n₀, hn₀, hov₀, hrefl₀, hmem₀⟩ := ggReflection_overGamma_of_induced hp hp2 hBs hBsN hrL hrr
  obtain ⟨n, hn, J', hW, hnφ, hnJ', hcomp, hpJ', hlayer⟩ :=
    hT L (ggQuotHom θ) (ggGamma L hBsN).range hTB _ hmem₀ hrefl₀
  obtain ⟨m, hg, htr, hover⟩ := exists_pow_isReflection_overGamma_of_weylElt hp hp2 hBs hSC hBsN
    hW hn (hnφ ▸ hrefl₀)
  have hgL : (n : G) ^ m ∈ L := L.pow_mem n.2 m
  have hrt : r = ggConjAut Bs hg := by
    refine ggReflection_eq_of_agree_mod hp2 hBs hNT (Z := Subgroup.centralizer (L : Set G))
      hrr htr ?_ ?_ ?_ ?_ ?_
    · obtain ⟨g', hg'L, hg'N, hg'⟩ := hrL
      exact ⟨g', trivial, hg'N, hg'⟩
    · exact ⟨(n : G) ^ m, trivial, hg, fun b => rfl⟩
    · obtain ⟨g', hg'L, -, hg'⟩ := hrL
      intro b hb
      apply Subtype.ext
      rw [hg' b, Subgroup.mem_centralizer_iff.mp hb g' hg'L]
      group
    · intro b hb
      apply Subtype.ext
      rw [ggConjAut_apply Bs hg, Subgroup.mem_centralizer_iff.mp hb ((n : G) ^ m) hgL]
      group
    · intro b
      have h1 : (ggGamma L hBsN).rangeRestrict ((r b)⁻¹ * (ggConjAut Bs hg) b) = 1 := by
        rw [map_mul, map_inv, hov₀ b, hover b, ← hnφ]
        exact inv_mul_cancel _
      have h2 := (ggGamma_eq_one_iff L hBsN ((r b)⁻¹ * (ggConjAut Bs hg) b)).mp (by
        have := congrArg Subtype.val h1
        simpa using this)
      simpa using h2
  have hxt : x ∈ ggFixG Bs (ggConjAut Bs hg) := by
    have hnx : (n : G) ^ m * x * ((n : G) ^ m)⁻¹ = x := by
      have hc := Subgroup.mem_centralizer_singleton_iff.mp (hLx hgL)
      rw [hc, mul_inv_cancel_right]
    refine ⟨⟨x, hxBs⟩, ?_, rfl⟩
    apply Subtype.ext
    rw [ggConjAut_apply Bs hg]
    simpa using hnx
  have hCx : Subgroup.centralizer (ggFixG Bs (ggConjAut Bs hg) : Set G) ≤
      Subgroup.centralizer ({x} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hxt)
  have hsub : IsSubnormal (L ⊓ Subgroup.centralizer (ggFixG Bs (ggConjAut Bs hg) : Set G))
      (Subgroup.centralizer (ggFixG Bs (ggConjAut Bs hg) : Set G)) := by
    have h := hLsub.inf (Subgroup.centralizer (ggFixG Bs (ggConjAut Bs hg) : Set G))
    rwa [inf_eq_right.mpr hCx] at h
  have hmap := map_ggHypCent_eq hp hp2 hBs hBsN hn hgL hg htr.1 (hnφ ▸ hover)
  have hJc : IsComponentOf (J'.map L.subtype)
      (L ⊓ Subgroup.centralizer (ggFixG Bs (ggConjAut Bs hg) : Set G)) := by
    exact hmap ▸ isComponentOf_map_of_injective L.subtype L.subtype_injective hcomp
  have hJC : IsComponentOf (J'.map L.subtype)
      (Subgroup.centralizer (ggFixG Bs (ggConjAut Bs hg) : Set G)) :=
    ⟨hJc.1.trans inf_le_right, hJc.2.1.trans hsub, hJc.2.2⟩
  have hpJ'' : p ∣ Nat.card (J'.map L.subtype) := by
    rwa [Subgroup.card_map_of_injective L.subtype_injective]
  have hrJ : ggConjAut Bs hg ∈ ggInduced (J'.map L.subtype) Bs :=
    ⟨(n : G) ^ m, ⟨n ^ m, J'.pow_mem hnJ' m, by simp⟩, hg, fun b => rfl⟩
  subst hrt
  refine ⟨⟨J'.map L.subtype, hrJ, hJC.1, isPComponent_subgroupOf_of_isComponentOf_of_dvd hJC hpJ''⟩,
    fun hD => ?_⟩
  obtain ⟨y, K', hsH, hnbr⟩ := (hcfg.1.2.2.2.2.2.2.2.2.2.2 D J hcfg.2.2).1
  have hDxy : D = Subgroup.closure {x, y} := hnbr.1
  have hyBs : y ∈ Bs := hcfg.2.1.1 hsH.2.1
  have hJL : J = LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hcfg.2.2.1.2.2.2.2.1
  have hyD : y ∈ D := by
    rw [hDxy]
    exact Subgroup.subset_closure (by simp)
  have hyFix : y ∈ ggFixG Bs (ggConjAut Bs hg) := hD hyD
  obtain ⟨b, hb, hby⟩ := hyFix
  have hty : (ggConjAut Bs hg) ⟨y, hyBs⟩ = ⟨y, hyBs⟩ := by
    have hby' : (⟨y, hyBs⟩ : ↥Bs) = b := Subtype.ext hby.symm
    rw [hby']
    exact hb
  have hfixa : (ggConjAut (ggGamma L hBsN).range hn₀)
        ⟨ggGamma L hBsN ⟨y, hyBs⟩, ⟨⟨y, hyBs⟩, rfl⟩⟩ =
      ⟨ggGamma L hBsN ⟨y, hyBs⟩, ⟨⟨y, hyBs⟩, rfl⟩⟩ := by
    rw [← hnφ]
    have h := hover ⟨y, hyBs⟩
    rw [hty] at h
    exact h.symm
  have hnLayer : n ∈ LargeEvenLayer (ggFix (ggGamma L hBsN ⟨y, hyBs⟩)) :=
    hlayer (ggGamma L hBsN ⟨y, hyBs⟩) ⟨⟨y, hyBs⟩, rfl⟩ hfixa
  have hcent : L ⊓ Subgroup.centralizer (D : Set G) =
      L ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hDxy, Subgroup.centralizer_closure]
    ext l
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, Set.mem_insert_iff,
      Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    constructor
    · rintro ⟨hl, -, hy⟩
      exact ⟨hl, hy⟩
    · rintro ⟨hl, hy⟩
      exact ⟨hl, Subgroup.mem_centralizer_iff.mp (hLx hl) x (by simp), hy⟩
  have hfixmap : (ggFix (ggGamma L hBsN ⟨y, hyBs⟩)).map L.subtype =
      L ⊓ Subgroup.centralizer (D : Set G) := by
    rw [hcent]
    exact map_ggFix_ggGamma L hBsN ⟨y, hyBs⟩
  have hnL : (n : G) ∈ LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G)) := by
    rw [← hfixmap, largeEvenLayer_map_of_injective L.subtype L.subtype_injective]
    exact ⟨n, hnLayer, rfl⟩
  have hgJ : (n : G) ^ m ∈ J := by
    rw [hJL]
    exact (LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G))).pow_mem hnL m
  exact ⟨(n : G) ^ m, hgJ, hg, fun b => rfl⟩

end Transfer

end CFSG.StandardType
