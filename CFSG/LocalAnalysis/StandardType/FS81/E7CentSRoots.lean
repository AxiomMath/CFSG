module

public import CFSG.LocalAnalysis.StandardType.FS81.E7CentPieces
public import CFSG.LocalAnalysis.StandardType.FS81.E7CentHeis
public import CFSG.LocalAnalysis.SeitzReduction.E7PilotQ2OverlapCent

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.SeitzReduction CFSG.SeitzReduction.EPilot CFSG.SeitzReduction.EPilot.HeisIrr
open CFSG.SeitzReduction.E7Pilot CFSG.QuasithinUnique
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped commutatorElement


private theorem e7Cent_shift_eq_zero_of_fixed {K : Type} [Field K] [CharP K 2]
    {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (hγ0 : γ 0 = 0)
    {q : ModGL .E7 K} (hq : q ∈ Qθ .E7 K)
    (hfix : pinnedX .E7 K γ (1 : K) * q * (pinnedX .E7 K γ (1 : K))⁻¹ = q) :
    shiftRoot K γ (heisCoord .E7 K q) = 0 := by
  have h := (e7Cent_conj_of_deg_zero (K := K) hγ hγ0 hq).2
  rw [hfix] at h
  exact (add_left_cancel_iff (a := heisCoord .E7 K q)).1 (by simpa using h.symm)

private theorem e7Cent_coord_eq_zero_of_shift {K : Type} [Field K]
    {γ μ : Fin (Tag.rank .E7) → ℤ} {q : ModGL .E7 K}
    (hshift : shiftRoot K γ (heisCoord .E7 K q) = 0) (hroot : IsRoot .E7 (μ + γ)) :
    heisCoord .E7 K q μ = 0 := by
  have h := congrFun hshift (μ + γ)
  have hν : μ + γ ∈ rootFinset .E7 := mem_rootFinset.2 hroot
  rw [shiftRoot, if_pos hν, Pi.zero_apply] at h
  rwa [show μ + γ - γ = μ by abel] at h

private theorem e7CentSR_shift_eq_zero_of_mem_rootPerp {K : Type} [Field K] [CharP K 2]
    {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ perpRoots .E7) {q : ModGL .E7 K}
    (hq : q ∈ Qθ .E7 K) (hqβ : q ∈ rootSpan .E7 K (rootPerp .E7 β)) :
    shiftRoot K β (heisCoord .E7 K q) = 0 ∧
      shiftRoot K (-β) (heisCoord .E7 K q) = 0 := by
  have hβr : IsRoot .E7 β := hβ.1
  have hcent := rootSpan_le_centralizer_rootPair_E7 (K := K) hβr
    (fun α hα => hα)
  have hqcent := hcent hqβ
  have hmemβ : pinnedX .E7 K β (1 : K) ∈
      (rootSubgroup .E7 K β ⊔ rootSubgroup .E7 K (-β) : Subgroup (ModGL .E7 K)) :=
    Subgroup.mem_sup_left (Subgroup.subset_closure ⟨(1 : K), rfl⟩)
  have hmemβ' : pinnedX .E7 K (-β) (1 : K) ∈
      (rootSubgroup .E7 K β ⊔ rootSubgroup .E7 K (-β) : Subgroup (ModGL .E7 K)) :=
    Subgroup.mem_sup_right (Subgroup.subset_closure ⟨(1 : K), rfl⟩)
  have hfixβ : pinnedX .E7 K β (1 : K) * q * (pinnedX .E7 K β (1 : K))⁻¹ = q := by
    rw [Subgroup.mem_centralizer_iff.1 hqcent _ hmemβ, mul_assoc, mul_inv_cancel, mul_one]
  have hfixβ' : pinnedX .E7 K (-β) (1 : K) * q * (pinnedX .E7 K (-β) (1 : K))⁻¹ = q := by
    rw [Subgroup.mem_centralizer_iff.1 hqcent _ hmemβ', mul_assoc, mul_inv_cancel, mul_one]
  have hβ0 : β 0 = 0 := by
    simpa [show highNode .E7 = 0 from rfl] using hβ.2
  have hneg0 : (-β) 0 = 0 := by
    simpa [Pi.neg_apply, neg_eq_zero] using hβ0
  exact ⟨e7Cent_shift_eq_zero_of_fixed hβr hβ0 hq hfixβ,
    e7Cent_shift_eq_zero_of_fixed (IsRoot.neg hβr) hneg0 hq hfixβ'⟩

private theorem e7Cent_coord_eq_zero_of_centralizes_rootPair {K : Type} [Field K] [CharP K 2]
    {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ perpRoots .E7) {q : ModGL .E7 K}
    (hq : q ∈ Qθ .E7 K) (hqβ : q ∈ rootSpan .E7 K (rootPerp .E7 β))
    {μ : Fin (Tag.rank .E7) → ℤ} (hμ : μ ∈ Deg1 .E7) (hne : iform μ β ≠ 0) :
    heisCoord .E7 K q μ = 0 := by
  obtain ⟨hshiftβ, hshiftβ'⟩ := e7CentSR_shift_eq_zero_of_mem_rootPerp hβ hq hqβ
  have hself : iform β β = 2 :=
    iform_self_eq_two (τ := .E7) (Or.inr (Or.inl rfl)) hβ.1
  rcases e7Cent_deg1_iform_perp hμ hβ with h | h | h
  · have hlt : iform μ β < 0 := by omega
    have hne' : μ ≠ -β := by
      intro e
      rw [e, iform_neg_left, hself] at h
      omega
    exact e7Cent_coord_eq_zero_of_shift hshiftβ
      (isRoot_add_of_iform_neg hμ.1 hβ.1 hne' hlt)
  · exact absurd h hne
  · have hgt : 0 < iform μ β := by omega
    have hne' : μ ≠ β := by
      intro e
      rw [e, hself] at h
      omega
    have hroot : IsRoot .E7 (μ + -β) := by
      have h' := isRoot_sub_of_iform_pos hμ.1 hβ.1 hne' hgt
      simpa [sub_eq_add_neg] using h'
    exact e7Cent_coord_eq_zero_of_shift hshiftβ' hroot

private theorem e7Cent_mem_rootSpan_inter_of_mem_Qθ_rootPerp {K : Type} [Field K] [CharP K 2]
    {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ perpRoots .E7) {q : ModGL .E7 K}
    (hq : q ∈ Qθ .E7 K) (hqβ : q ∈ rootSpan .E7 K (rootPerp .E7 β)) :
    q ∈ rootSpan .E7 K (radicalRoots .E7 (highRoot .E7) ∩ rootPerp .E7 β) := by
  have hθr : IsRoot .E7 (highRoot .E7) := isRoot_highRoot .E7
  refine e7Cent_mem_rootSpan_of_coord_support (S :=
    radicalRoots .E7 (highRoot .E7) ∩ rootPerp .E7 β) (fun μ hμ => hμ.1.1) ?_ hq ?_
  · refine ⟨⟨hθr, ?_⟩, ⟨hθr, ?_⟩⟩
    · rw [iform_highRoot_self (Or.inr (Or.inl rfl))]
      norm_num
    · calc iform (highRoot .E7) β = β 0 := iform_highRoot_E7 β
        _ = 0 := hβ.2
  · intro μ hne
    have hμD : μ ∈ Deg1 .E7 := by
      by_contra h
      exact hne ((heisCoord_spec .E7 K).support q hq μ h)
    refine ⟨⟨hμD.1, ?_⟩, ⟨hμD.1, ?_⟩⟩
    · rw [iform_comm, iform_highRoot_E7]
      have hdeg : μ 0 = 1 := hμD.2
      omega
    · by_contra hb
      exact hne (e7Cent_coord_eq_zero_of_centralizes_rootPair hβ hq hqβ hμD hb)

private theorem e7CentSR_exists_weyl_transport :
    ∃ (w : WeylGroup .E7) (β : Fin (Tag.rank .E7) → ℤ),
      w • highRoot .E7 = d6HighRoot ∧ w • β = highRoot .E7 ∧ β ∈ perpRoots .E7 := by
  obtain ⟨w, hw⟩ := exists_smul_highRoot_eq (τ := .E7) (Or.inr (Or.inl rfl)) isRoot_d6HighRoot
  have hβP : w⁻¹ • highRoot .E7 ∈ perpRoots .E7 := by
    refine ⟨?_, ?_⟩
    · simpa using IsRoot.smul (isRoot_highRoot .E7) w⁻¹
    · change (w⁻¹ • highRoot .E7) (0 : Fin (Tag.rank .E7)) = 0
      rw [← iform_highRoot_E7 (w⁻¹ • highRoot .E7)]
      calc iform (highRoot .E7) (w⁻¹ • highRoot .E7)
          = iform (w • highRoot .E7) (w • (w⁻¹ • highRoot .E7)) := by rw [iform_smul]
        _ = iform (w • highRoot .E7) (highRoot .E7) := by rw [smul_inv_smul]
        _ = iform d6HighRoot (highRoot .E7) := by rw [hw]
        _ = 0 := by rw [iform_comm, iform_highRoot_d6HighRoot]
  exact ⟨w, w⁻¹ • highRoot .E7, hw, smul_inv_smul w (highRoot .E7), hβP⟩

private theorem e7CentSR_image_radicalRoots_inter_rootPerp {w : WeylGroup .E7}
    (hw : w • highRoot .E7 = d6HighRoot) {β : Fin (Tag.rank .E7) → ℤ}
    (hwβ : w • β = highRoot .E7) :
    (fun δ => w • δ) '' (radicalRoots .E7 (highRoot .E7) ∩ rootPerp .E7 β) =
      radicalRoots .E7 d6HighRoot ∩ perpRoots .E7 := by
  have hImA : (fun δ => w • δ) '' radicalRoots .E7 (highRoot .E7) =
      radicalRoots .E7 d6HighRoot := by
    rw [image_smul_radicalRoots, hw]
  have hImP : (fun δ => w • δ) '' rootPerp .E7 β = perpRoots .E7 := by
    rw [image_smul_rootPerp, hwβ, rootPerp_highRoot (Or.inr (Or.inl rfl))]
  ext δ
  constructor
  · rintro ⟨γ, ⟨hA, hP⟩, rfl⟩
    exact ⟨hImA ▸ Set.mem_image_of_mem _ hA, hImP ▸ Set.mem_image_of_mem _ hP⟩
  · rintro ⟨hA, hP⟩
    have hA' : δ ∈ (fun δ => w • δ) '' radicalRoots .E7 (highRoot .E7) := by
      rw [hImA]; exact hA
    have hP' : δ ∈ (fun δ => w • δ) '' rootPerp .E7 β := by
      rw [hImP]; exact hP
    obtain ⟨γ, hγ, rfl⟩ := hA'
    obtain ⟨γ', hγ', hγ'eq⟩ := hP'
    have hγγ : γ' = γ := by
      have := congrArg (fun z => w⁻¹ • z) hγ'eq
      simpa using this
    subst γ'
    exact ⟨γ, ⟨hγ, hγ'⟩, rfl⟩

private theorem e7CentSR_mem_map_rootSpan_inter {K : Type} [Field K] [CharP K 2]
    {β : Fin (Tag.rank .E7) → ℤ} (hβ : β ∈ perpRoots .E7) {n : ModGL .E7 K}
    {g : ModGL .E7 K}
    (hgR : g ∈ (rootSpan .E7 K (radicalRoots .E7 (highRoot .E7))).map
      (MulAut.conj n).toMonoidHom)
    (hgD : g ∈ (rootSpan .E7 K (rootPerp .E7 β)).map (MulAut.conj n).toMonoidHom)
    (hQ : rootSpan .E7 K (radicalRoots .E7 (highRoot .E7)) =
      parabolicRadical .E7 K (perpNodes .E7)) :
    g ∈ (rootSpan .E7 K (radicalRoots .E7 (highRoot .E7) ∩ rootPerp .E7 β)).map
      (MulAut.conj n).toMonoidHom := by
  obtain ⟨gA, hgA, hgAeq⟩ := Subgroup.mem_map.1 hgR
  obtain ⟨gP, hgP, hgPeq⟩ := Subgroup.mem_map.1 hgD
  have hgg : gA = gP := (MulAut.conj n).injective (by
    simpa using hgAeq.trans hgPeq.symm)
  have hgAQ : gA ∈ Qθ .E7 K := by
    rw [show Qθ .E7 K = parabolicRadical .E7 K (perpNodes .E7) from rfl, ← hQ]
    exact hgA
  have hgAP : gA ∈ rootSpan .E7 K (rootPerp .E7 β) := hgg.symm ▸ hgP
  have hmem := e7Cent_mem_rootSpan_inter_of_mem_Qθ_rootPerp (K := K) hβ hgAQ hgAP
  rw [← hgAeq]
  exact Subgroup.mem_map.2 ⟨gA, hmem, rfl⟩

private theorem e7Cent_rootSpan_inter_eq (K : Type) [Field K] [CharP K 2] :
    rootSpan .E7 K (radicalRoots .E7 d6HighRoot ∩ perpRoots .E7) =
      rootSpan .E7 K (radicalRoots .E7 d6HighRoot) ⊓
        rootSpan .E7 K (perpRoots .E7) := by
  have hτ : Tag.E7 = Tag.E6 ∨ Tag.E7 = Tag.E7 ∨ Tag.E7 = Tag.E8 := Or.inr (Or.inl rfl)
  obtain ⟨w, β, hw, hwβ, hβP⟩ := e7CentSR_exists_weyl_transport
  let n := canonicalRep (coxeterSystem .E7) K w
  have hQ : rootSpan .E7 K (radicalRoots .E7 (highRoot .E7)) =
      parabolicRadical .E7 K (perpNodes .E7) := by
    rw [parabolicRadical, ← radicalRoots_highRoot hτ]
  have hImI := e7CentSR_image_radicalRoots_inter_rootPerp hw hwβ
  have hmapA : (rootSpan .E7 K (radicalRoots .E7 (highRoot .E7))).map
      (MulAut.conj n).toMonoidHom = rootSpan .E7 K (radicalRoots .E7 d6HighRoot) := by
    rw [hQ, map_conj_parabolicRadical_perpNodes hτ w, hw]
  have hmapP : (rootSpan .E7 K (rootPerp .E7 β)).map
      (MulAut.conj n).toMonoidHom = rootSpan .E7 K (perpRoots .E7) := by
    rw [(canonical_weyl_root_transport .E7 K).1 w (rootPerp .E7 β) (fun α hα => hα.1),
      image_smul_rootPerp, hwβ, rootPerp_highRoot hτ]
  have hmapI : (rootSpan .E7 K (radicalRoots .E7 (highRoot .E7) ∩ rootPerp .E7 β)).map
      (MulAut.conj n).toMonoidHom =
      rootSpan .E7 K (radicalRoots .E7 d6HighRoot ∩ perpRoots .E7) := by
    rw [(canonical_weyl_root_transport .E7 K).1 w _
      (fun α hα => hα.1.1), hImI]
  refine le_antisymm (le_inf (rootSpan_mono Set.inter_subset_left)
    (rootSpan_mono Set.inter_subset_right)) ?_
  intro g hg
  obtain ⟨hgR, hgD⟩ := Subgroup.mem_inf.1 hg
  rw [← hmapA] at hgR
  rw [← hmapP] at hgD
  rw [← hmapI]
  exact e7CentSR_mem_map_rootSpan_inter (K := K) hβP hgR hgD hQ

theorem e7CentSRoots_holds :
    E7CentSRoots := by
  have h := e7Cent_rootSpan_inter_eq (ZMod 2)
  unfold E7CentSRoots e7CentS perpLevi
  rw [← subgroupOf_inf_subgroupOf, ← h]

end CFSG.StandardType.FrameRoute.FS81
