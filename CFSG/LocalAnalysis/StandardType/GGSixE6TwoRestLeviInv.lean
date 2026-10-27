module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestDefs
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestFrame
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestBasic
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestInvQV
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestLevi
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalRoots

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint

private theorem e6li_zmod_two (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x; decide

private theorem e6li_F2_cases (x : F2) : x = 0 ∨ x = 1 := by
  rcases e6li_zmod_two (GaloisField.equivZmodP (p := 2) x) with h | h
  · left
    apply (GaloisField.equivZmodP (p := 2)).injective
    rw [h, map_zero]
  · right
    apply (GaloisField.equivZmodP (p := 2)).injective
    rw [h, map_one]

private theorem e6li_F2_units_subsingleton : Subsingleton F2ˣ := by
  have hcard : Nat.card F2 = 2 := by
    rw [show F2 = GaloisField 2 1 from rfl, GaloisField.card 2 1 (by norm_num)]
    norm_num
  have h1 : Nat.card F2ˣ = 1 := by rw [Nat.card_units, hcard]
  exact (Nat.card_eq_one_iff_unique.mp h1).1

private theorem e6li_xr_mul_self
    (β : Fin Tag.E6.rank → ℤ) : xr β * xr β = 1 := by
  apply Subtype.ext
  change pinnedX .E6 F2 β 1 * pinnedX .E6 F2 β 1 = (1 : ModGL .E6 F2)
  rw [← pinnedX_add .E6 F2 β 1 1]
  rw [show (1 : F2) + 1 = 0 from by
    rw [show (1 : F2) + 1 = (2 : F2) from by norm_num, gf2_two]]
  rw [pinnedX_zero .E6 F2 β]

private theorem e6li_qE_le_normalizer_of_coord
    {T : Subgroup EC} {U : Submodule (ZMod 2) e6TwoRestQV}
    {c : ↥qE →* Multiplicative e6TwoRestQV} (hc : IsQCoord c)
    (hTle : T ≤ qE)
    (hTU : ∀ q : ↥qE, Multiplicative.toAdd (c q) ∈ U ↔ (q : EC) ∈ T) :
    qE ≤ Subgroup.normalizer (T : Set EC) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ (g : EC) (hg : g ∈ qE) (y : EC) (hy : y ∈ qE),
      g * y * g⁻¹ ∈ T ↔ y ∈ T := by
    intro g hg y hy
    have hgy : g * y * g⁻¹ ∈ qE := qE.mul_mem (qE.mul_mem hg hy) (qE.inv_mem hg)
    have hcoord : Multiplicative.toAdd (c ⟨g * y * g⁻¹, hgy⟩) =
        Multiplicative.toAdd (c ⟨y, hy⟩) := by
      have hcast : (⟨g * y * g⁻¹, hgy⟩ : ↥qE) =
          ⟨g, hg⟩ * ⟨y, hy⟩ * ⟨g, hg⟩⁻¹ := by
        apply Subtype.ext; rfl
      rw [hcast, map_mul c, map_mul c, map_inv c, toAdd_mul, toAdd_mul, toAdd_inv]
      abel
    rw [← hTU ⟨g * y * g⁻¹, hgy⟩, ← hTU ⟨y, hy⟩, hcoord]
  intro x
  constructor
  · intro hx
    exact (key g hg x (hTle hx)).mpr hx
  · intro hx
    have hxq : g * x * g⁻¹ ∈ qE := hTle hx
    have hstep := (key g⁻¹ (qE.inv_mem hg) (g * x * g⁻¹) hxq).mpr hx
    rwa [show g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ = x by group] at hstep

private theorem e6li_uMu1_le_qE :
    uMu1 ≤ qE := by
  have hmem : ∀ β ∈ mu1List.toFinset, β ∈ rootFinset .E6 ∧ 0 < iform β lamE := by
    decide +kernel
  rw [uMu1, qE]
  refine Subgroup.subgroupOf_mono _ ?_
  rw [rootSpan_eq_closure, rootSpan_eq_closure]
  refine Subgroup.closure_mono ?_
  rintro g ⟨β, hβ, c, rfl⟩
  rcases e6li_F2_cases c with rfl | rfl
  · exact ⟨β, ⟨mem_rootFinset.1 (hmem β (List.mem_toFinset.2 hβ)).1,
      (hmem β (List.mem_toFinset.2 hβ)).2⟩, 0, rfl⟩
  · exact ⟨β, ⟨mem_rootFinset.1 (hmem β (List.mem_toFinset.2 hβ)).1,
      (hmem β (List.mem_toFinset.2 hβ)).2⟩, 1, rfl⟩

private theorem e6li_uMu2_le_qE :
    uMu2 ≤ qE := by
  have hmem : ∀ β ∈ mu2List.toFinset, β ∈ rootFinset .E6 ∧ 0 < iform β lamE := by
    decide +kernel
  rw [uMu2, qE]
  refine Subgroup.subgroupOf_mono _ ?_
  rw [rootSpan_eq_closure, rootSpan_eq_closure]
  refine Subgroup.closure_mono ?_
  rintro g ⟨β, hβ, c, rfl⟩
  rcases e6li_F2_cases c with rfl | rfl
  · exact ⟨β, ⟨mem_rootFinset.1 (hmem β (List.mem_toFinset.2 hβ)).1,
      (hmem β (List.mem_toFinset.2 hβ)).2⟩, 0, rfl⟩
  · exact ⟨β, ⟨mem_rootFinset.1 (hmem β (List.mem_toFinset.2 hβ)).1,
      (hmem β (List.mem_toFinset.2 hβ)).2⟩, 1, rfl⟩

private theorem e6li_xr_normalizes_rootSpan
    (S : Set (Fin Tag.E6.rank → ℤ)) (δ : Fin Tag.E6.rank → ℤ)
    (hS : ∀ β ∈ S, IsRoot .E6 β)
    (hlev : ∀ β ∈ S, iform β lamE ≠ 0)
    (hclosed : ∀ β ∈ S, IsRoot .E6 (β + δ) → β + δ ∈ S)
    (hδ : IsRoot .E6 δ) (hδ0 : iform δ lamE = 0) :
    xr δ ∈ Subgroup.normalizer
      ((rootSpan .E6 F2 S).subgroupOf (adjointGroup .E6 F2) : Set EC) := by
  classical
  have hne : ∀ β ∈ S, β ≠ δ := by
    intro β hβ h
    have := hlev β hβ
    rw [h, hδ0] at this
    exact this rfl
  have hne' : ∀ β ∈ S, β ≠ -δ := by
    intro β hβ h
    have hh := hlev β hβ
    rw [h, iform_neg_left, hδ0] at hh
    exact hh (by norm_num)
  let T : Set (ModGL .E6 F2) := {g | ∃ α ∈ S, ∃ c : F2, pinnedX .E6 F2 α c = g}
  have hroot : rootSpan .E6 F2 S = Subgroup.closure T := rootSpan_eq_closure F2 S
  have hconj_gen : ∀ g ∈ T,
      pinnedX .E6 F2 δ 1 * g * (pinnedX .E6 F2 δ 1)⁻¹ ∈ Subgroup.closure T := by
    rintro g ⟨β, hβ, c, rfl⟩
    rcases e6li_F2_cases c with rfl | rfl
    · have h1 : pinnedX .E6 F2 δ 1 * pinnedX .E6 F2 β 0 * (pinnedX .E6 F2 δ 1)⁻¹ = 1 := by
        rw [pinnedX_zero .E6 F2 β, mul_one]
        group
      rw [h1]
      exact Subgroup.one_mem _
    · have hbδ : β ≠ δ := hne β hβ
      have hbδ' : β ≠ -δ := hne' β hβ
      by_cases hadd : IsRoot .E6 (δ + β)
      · have hne1 : δ ≠ β := fun h => hbδ h.symm
        have hne2 : δ ≠ -β := by
          intro h
          have h2 : -δ = β := by rw [h, neg_neg]
          exact hbδ' h2.symm
        have hc := CFSG.LieType.Chevalley.EvenOddRadical.pinnedX_conj_of_isRoot
          (τ := .E6) (Or.inr (Or.inl rfl)) gf2_two hδ (hS β hβ) hne1 hne2 hadd (1 : F2) 1
        rw [hc, one_mul]
        have hSadd : β + δ ∈ S := hclosed β hβ (by simpa [add_comm] using hadd)
        have hrootmem : δ + β ∈ S := by rwa [add_comm] at hSadd
        exact mul_mem (Subgroup.subset_closure ⟨δ + β, hrootmem, 1, rfl⟩)
          (Subgroup.subset_closure ⟨β, hβ, 1, rfl⟩)
      · have hne1 : δ ≠ β := fun h => hbδ h.symm
        have hne2 : δ ≠ -β := by
          intro h
          have h2 : -δ = β := by rw [h, neg_neg]
          exact hbδ' h2.symm
        have hc := CFSG.LieType.Chevalley.EvenOddRadical.pinnedX_conj_of_not
          (τ := .E6) (Or.inr (Or.inl rfl)) hδ (hS β hβ) hne1 hne2 hadd (1 : F2) 1
        rw [hc]
        exact Subgroup.subset_closure ⟨β, hβ, 1, rfl⟩
  have hle : ∀ y ∈ rootSpan .E6 F2 S,
      pinnedX .E6 F2 δ 1 * y * (pinnedX .E6 F2 δ 1)⁻¹ ∈ rootSpan .E6 F2 S := by
    rw [hroot]
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx => exact hconj_gen x hx
    | one =>
        have h1 : pinnedX .E6 F2 δ 1 * (1 : ModGL .E6 F2) * (pinnedX .E6 F2 δ 1)⁻¹ = 1 := by
          group
        rw [h1]
        exact Subgroup.one_mem _
    | mul a b ha hb iha ihb =>
        rw [show pinnedX .E6 F2 δ 1 * (a * b) * (pinnedX .E6 F2 δ 1)⁻¹ =
            (pinnedX .E6 F2 δ 1 * a * (pinnedX .E6 F2 δ 1)⁻¹) *
              (pinnedX .E6 F2 δ 1 * b * (pinnedX .E6 F2 δ 1)⁻¹) from by group]
        exact mul_mem iha ihb
    | inv a ha iha =>
        rw [show pinnedX .E6 F2 δ 1 * a⁻¹ * (pinnedX .E6 F2 δ 1)⁻¹ =
            (pinnedX .E6 F2 δ 1 * a * (pinnedX .E6 F2 δ 1)⁻¹)⁻¹ from by group]
        exact inv_mem iha
  refine Subgroup.mem_normalizer_iff.mpr ?_
  intro x
  constructor
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa [Subgroup.coe_mul, Subgroup.coe_inv, xr] using hle (x : ModGL .E6 F2) hx
  · intro hx
    have hxH : (xr δ * x * (xr δ)⁻¹ : EC) ∈
        (rootSpan .E6 F2 S).subgroupOf (adjointGroup .E6 F2) := hx
    have hx' : (xr δ * (xr δ * x * (xr δ)⁻¹) * (xr δ)⁻¹ : EC) ∈
        (rootSpan .E6 F2 S).subgroupOf (adjointGroup .E6 F2) := by
      rw [Subgroup.mem_subgroupOf] at hxH ⊢
      simpa [Subgroup.coe_mul, Subgroup.coe_inv, xr] using
        hle ((xr δ * x * (xr δ)⁻¹ : EC) : ModGL .E6 F2) hxH
    have hg2 : xr δ * xr δ = 1 := e6li_xr_mul_self δ
    have hginv : (xr δ)⁻¹ = xr δ := inv_eq_of_mul_eq_one_right hg2
    have heq : xr δ * (xr δ * x * (xr δ)⁻¹) * (xr δ)⁻¹ = x := by
      rw [hginv]
      calc xr δ * (xr δ * x * xr δ) * xr δ
          = (xr δ * xr δ) * x * (xr δ * xr δ) := by group
        _ = 1 * x * 1 := by rw [hg2]
        _ = x := by group
    rwa [heq] at hx'

private theorem e6li_mu1_levels :
    ∀ β ∈ mu1List.toFinset, β ∈ rootFinset .E6 ∧ iform β lamE = 1 := by
  decide +kernel

private theorem e6li_mu2_levels :
    ∀ β ∈ mu2List.toFinset, β ∈ rootFinset .E6 ∧ iform β lamE = 1 := by
  decide +kernel

private theorem e6li_mu1_level0_closed :
    ∀ δ ∈ rootFinset .E6, iform δ lamE = 0 →
      ∀ β ∈ mu1List.toFinset, β + δ ∈ rootFinset .E6 → β + δ ∈ mu1List.toFinset := by
  decide +kernel

private theorem e6li_mu2_level0_closed :
    ∀ δ ∈ rootFinset .E6, iform δ lamE = 0 →
      ∀ β ∈ mu2List.toFinset, β + δ ∈ rootFinset .E6 → β + δ ∈ mu2List.toFinset := by
  decide +kernel

private theorem e6li_zRoots_closed
    (δ : Fin Tag.E6.rank → ℤ) (hδ0 : iform δ lamE = 0) :
    ∀ β ∈ zRoots, IsRoot .E6 (β + δ) → β + δ ∈ zRoots := by
  intro β hβ hroot
  have hβ2 : iform β lamE = 2 := hβ.2
  refine ⟨hroot, ?_⟩
  rw [iform_add_left β δ lamE, hβ2, hδ0]
  norm_num

private theorem e6li_xr_mem_normalizer_sup_uMu1
    (δ : Fin Tag.E6.rank → ℤ) (hδ : IsRoot .E6 δ) (hδ0 : iform δ lamE = 0) :
    xr δ ∈ Subgroup.normalizer ((z0E ⊔ uMu1 : Subgroup EC) : Set EC) := by
  have hz : xr δ ∈ Subgroup.normalizer (z0E : Set EC) :=
    e6li_xr_normalizes_rootSpan zRoots δ (fun β hβ => hβ.1)
      (fun β hβ => by rw [hβ.2]; norm_num)
      (fun β hβ hr => e6li_zRoots_closed δ hδ0 β hβ hr) hδ hδ0
  have hu : xr δ ∈ Subgroup.normalizer (uMu1 : Set EC) := by
    have hS : ∀ β ∈ ({β : Fin Tag.E6.rank → ℤ | β ∈ mu1List} : Set _), IsRoot .E6 β :=
      fun β hβ => mem_rootFinset.1 (e6li_mu1_levels β (List.mem_toFinset.2 hβ)).1
    have hlv : ∀ β ∈ ({β : Fin Tag.E6.rank → ℤ | β ∈ mu1List} : Set _),
        iform β lamE ≠ 0 := by
      intro β hβ
      rw [(e6li_mu1_levels β (List.mem_toFinset.2 hβ)).2]; norm_num
    have hcl : ∀ β ∈ ({β : Fin Tag.E6.rank → ℤ | β ∈ mu1List} : Set _),
        IsRoot .E6 (β + δ) → β + δ ∈ ({β : Fin Tag.E6.rank → ℤ | β ∈ mu1List} : Set _) := by
      intro β hβ hroot
      exact List.mem_toFinset.1 (e6li_mu1_level0_closed δ (mem_rootFinset.2 hδ) hδ0 β
        (List.mem_toFinset.2 hβ) (mem_rootFinset.2 hroot))
    exact e6li_xr_normalizes_rootSpan {β : Fin Tag.E6.rank → ℤ | β ∈ mu1List} δ hS hlv hcl hδ hδ0
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hz hu ⊢
  rw [Subgroup.map_sup, hz, hu]

private theorem e6li_xr_mem_normalizer_sup_uMu2
    (δ : Fin Tag.E6.rank → ℤ) (hδ : IsRoot .E6 δ) (hδ0 : iform δ lamE = 0) :
    xr δ ∈ Subgroup.normalizer ((z0E ⊔ uMu2 : Subgroup EC) : Set EC) := by
  have hz : xr δ ∈ Subgroup.normalizer (z0E : Set EC) :=
    e6li_xr_normalizes_rootSpan zRoots δ (fun β hβ => hβ.1)
      (fun β hβ => by rw [hβ.2]; norm_num)
      (fun β hβ hr => e6li_zRoots_closed δ hδ0 β hβ hr) hδ hδ0
  have hu : xr δ ∈ Subgroup.normalizer (uMu2 : Set EC) := by
    have hS : ∀ β ∈ ({β : Fin Tag.E6.rank → ℤ | β ∈ mu2List} : Set _), IsRoot .E6 β :=
      fun β hβ => mem_rootFinset.1 (e6li_mu2_levels β (List.mem_toFinset.2 hβ)).1
    have hlv : ∀ β ∈ ({β : Fin Tag.E6.rank → ℤ | β ∈ mu2List} : Set _),
        iform β lamE ≠ 0 := by
      intro β hβ
      rw [(e6li_mu2_levels β (List.mem_toFinset.2 hβ)).2]; norm_num
    have hcl : ∀ β ∈ ({β : Fin Tag.E6.rank → ℤ | β ∈ mu2List} : Set _),
        IsRoot .E6 (β + δ) → β + δ ∈ ({β : Fin Tag.E6.rank → ℤ | β ∈ mu2List} : Set _) := by
      intro β hβ hroot
      exact List.mem_toFinset.1 (e6li_mu2_level0_closed δ (mem_rootFinset.2 hδ) hδ0 β
        (List.mem_toFinset.2 hβ) (mem_rootFinset.2 hroot))
    exact e6li_xr_normalizes_rootSpan {β : Fin Tag.E6.rank → ℤ | β ∈ mu2List} δ hS hlv hcl hδ hδ0
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hz hu ⊢
  rw [Subgroup.map_sup, hz, hu]

private theorem e6li_single_yLamAS_zero
    (j : Fin Tag.E6.rank) (hj : j ∈ E6Pilot.nodes16) :
    iform (Pi.single j 1) E6Pilot.yLamAS = 0 := by
  have hmem : Pi.single j 1 ∈
      ({γ : Fin Tag.E6.rank → ℤ | IsRoot .E6 γ ∧ iform γ E6Pilot.yLamAS = 0} : Set _) := by
    rw [← E6Pilot.parabolicRoots_nodes16]
    refine ⟨isRoot_single .E6 j, ?_⟩
    intro i hi
    have hji : i ≠ j := fun h => hi (h ▸ hj)
    rw [Pi.single_apply, if_neg hji]
  exact hmem.2

private theorem e6li_single_level0
    (j : Fin Tag.E6.rank) (hj : j ∈ E6Pilot.nodes16) :
    iform (wQ • Pi.single j 1) lamE = 0 := by
  rw [← wQ_smul_yLamAS, iform_smul]
  exact e6li_single_yLamAS_zero j hj

private theorem e6li_neg_single_level0
    (j : Fin Tag.E6.rank) (hj : j ∈ E6Pilot.nodes16) :
    iform (wQ • (-(Pi.single j 1))) lamE = 0 := by
  rw [← wQ_smul_yLamAS, iform_smul, iform_neg_left, e6li_single_yLamAS_zero j hj]
  norm_num

private theorem e6li_lamLevi_le_normalizer
    
    (T : Subgroup EC)
    (hN : ∀ δ, IsRoot .E6 δ → iform δ lamE = 0 →
      xr δ ∈ Subgroup.normalizer (T : Set EC)) :
    lamLevi ≤ Subgroup.normalizer (T : Set EC) := by
  let A : Subgroup (ModGL .E6 F2) := adjointGroup .E6 F2
  let N : Subgroup EC := Subgroup.normalizer (T : Set EC)
  let f : EC →* EC := (MulAut.conj nQ).toMonoidHom
  set K : Subgroup (ModGL .E6 F2) := Subgroup.map A.subtype (Subgroup.comap f N) with hK
  have hgen : ∀ (j : Fin Tag.E6.rank) (hj : j ∈ E6Pilot.nodes16) (c : F2),
      xUnit .E6 F2 j c ∈ K := by
    intro j hj c
    rw [hK, Subgroup.mem_map]
    refine ⟨⟨xUnit .E6 F2 j c, xUnit_mem_adjointGroup j c⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    rcases e6li_F2_cases c with rfl | rfl
    · have h0 : xUnit .E6 F2 j 0 = 1 := by rw [← pinnedX_single .E6 F2 j 0, pinnedX_zero]
      have h1 : (⟨xUnit .E6 F2 j 0, xUnit_mem_adjointGroup j 0⟩ : EC) = 1 :=
        Subtype.ext h0
      rw [h1, map_one]
      exact N.one_mem
    · have hxr : (⟨xUnit .E6 F2 j 1, xUnit_mem_adjointGroup j 1⟩ : EC)
          = xr (Pi.single j 1) := by
        apply Subtype.ext
        show xUnit .E6 F2 j 1 = pinnedX .E6 F2 (Pi.single j 1) 1
        exact (pinnedX_single .E6 F2 j 1).symm
      have hconj : f (⟨xUnit .E6 F2 j 1, xUnit_mem_adjointGroup j 1⟩ : EC)
          = xr (wQ • Pi.single j 1) := by
        show (MulAut.conj nQ) _ = _
        rw [hxr, MulAut.conj_apply]
        exact conj_nQ_xr (isRoot_single .E6 j)
      rw [hconj]
      exact hN _ (CFSG.LieType.Chevalley.IsRoot.smul (isRoot_single .E6 j) wQ)
        (e6li_single_level0 j hj)
  have hgeny : ∀ (j : Fin Tag.E6.rank) (hj : j ∈ E6Pilot.nodes16) (c : F2),
      yUnit .E6 F2 j c ∈ K := by
    intro j hj c
    rw [hK, Subgroup.mem_map]
    refine ⟨⟨yUnit .E6 F2 j c, yUnit_mem_adjointGroup j c⟩, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    rcases e6li_F2_cases c with rfl | rfl
    · have h0 : yUnit .E6 F2 j 0 = 1 := by
        rw [← pinnedX_neg_single .E6 F2 j 0, pinnedX_zero]
      have h1 : (⟨yUnit .E6 F2 j 0, yUnit_mem_adjointGroup j 0⟩ : EC) = 1 :=
        Subtype.ext h0
      rw [h1, map_one]
      exact N.one_mem
    · have hxr : (⟨yUnit .E6 F2 j 1, yUnit_mem_adjointGroup j 1⟩ : EC)
          = xr (-(Pi.single j 1)) := by
        apply Subtype.ext
        show yUnit .E6 F2 j 1 = pinnedX .E6 F2 (-(Pi.single j 1)) 1
        exact (pinnedX_neg_single .E6 F2 j 1).symm
      have hconj : f (⟨yUnit .E6 F2 j 1, yUnit_mem_adjointGroup j 1⟩ : EC)
          = xr (wQ • (-(Pi.single j 1))) := by
        show (MulAut.conj nQ) _ = _
        rw [hxr, MulAut.conj_apply]
        exact conj_nQ_xr (isRoot_neg_single .E6 j)
      rw [hconj]
      exact hN _ (CFSG.LieType.Chevalley.IsRoot.smul (isRoot_neg_single .E6 j) wQ)
        (e6li_neg_single_level0 j hj)
  have hpar : parabolicLevi .E6 F2 E6Pilot.nodes16 ≤ K := by
    rw [parabolicLevi]
    refine sup_le ?_ ?_
    · rw [torusGroup, Subgroup.closure_le]
      rintro _ ⟨⟨i, t⟩, rfl⟩
      change torusElt .E6 F2 i t ∈ K
      rw [hK, Subgroup.mem_map]
      refine ⟨⟨torusElt .E6 F2 i t, torusElt_mem_adjointGroup i t⟩, ?_, rfl⟩
      rw [Subgroup.mem_comap]
      haveI : Subsingleton F2ˣ := e6li_F2_units_subsingleton
      have ht : t = 1 := Subsingleton.elim t 1
      have h1 : (⟨torusElt .E6 F2 i t, torusElt_mem_adjointGroup i t⟩ : EC) = 1 := by
        apply Subtype.ext
        show torusElt .E6 F2 i t = 1
        rw [ht]
        exact torusElt_one i
      rw [h1, map_one]
      exact N.one_mem
    · rw [Subgroup.closure_le]
      rintro _ ⟨j, hj, c, rfl | rfl⟩
      · exact hgen j hj c
      · exact hgeny j hj c
  rw [lamLevi, Subgroup.map_le_iff_le_comap]
  intro m hm
  rw [Subgroup.mem_comap]
  have hmpar : (m : ModGL .E6 F2) ∈ parabolicLevi .E6 F2 E6Pilot.nodes16 :=
    Subgroup.mem_subgroupOf.1 hm
  have hmK : (m : ModGL .E6 F2) ∈ K := hpar hmpar
  rw [hK, Subgroup.mem_map] at hmK
  obtain ⟨m', hm'N, hm'eq⟩ := hmK
  have hmm : m' = m := Subtype.ext hm'eq
  rw [hmm] at hm'N
  exact hm'N


theorem normalizer_qE_le_normalizer_z0E_sup_uMu1 :
    Subgroup.normalizer (qE : Set EC) ≤ Subgroup.normalizer ((z0E ⊔ uMu1 : Subgroup EC) : Set EC) := by
  obtain ⟨c, hc⟩ := exists_qcoord
  have hQ : qE ≤ Subgroup.normalizer ((z0E ⊔ uMu1 : Subgroup EC) : Set EC) :=
    e6li_qE_le_normalizer_of_coord hc (sup_le z0E_le_qE e6li_uMu1_le_qE)
      (fun q => qcoord_mem_U1_iff hc q)
  have hL : lamLevi ≤ Subgroup.normalizer ((z0E ⊔ uMu1 : Subgroup EC) : Set EC) :=
    e6li_lamLevi_le_normalizer _ (fun δ hδ hδ0 => e6li_xr_mem_normalizer_sup_uMu1 δ hδ hδ0)
  exact normalizer_qE_le_sup_lamLevi.trans (sup_le hQ hL)

theorem normalizer_qE_le_normalizer_z0E_sup_uMu2 :
    Subgroup.normalizer (qE : Set EC) ≤ Subgroup.normalizer ((z0E ⊔ uMu2 : Subgroup EC) : Set EC) := by
  obtain ⟨c, hc⟩ := exists_qcoord
  have hQ : qE ≤ Subgroup.normalizer ((z0E ⊔ uMu2 : Subgroup EC) : Set EC) :=
    e6li_qE_le_normalizer_of_coord hc (sup_le z0E_le_qE e6li_uMu2_le_qE)
      (fun q => qcoord_mem_U2_iff hc q)
  have hL : lamLevi ≤ Subgroup.normalizer ((z0E ⊔ uMu2 : Subgroup EC) : Set EC) :=
    e6li_lamLevi_le_normalizer _ (fun δ hδ hδ0 => e6li_xr_mem_normalizer_sup_uMu2 δ hδ hδ0)
  exact normalizer_qE_le_sup_lamLevi.trans (sup_le hQ hL)

end CFSG.StandardType.GGSixE6Two
