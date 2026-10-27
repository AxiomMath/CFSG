module

public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestDefs
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestFrame
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestBasic
public import CFSG.LocalAnalysis.StandardType.GGSixE6TwoRestInvLin

public section

namespace CFSG.StandardType.GGSixE6Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open CFSG.SeitzReduction
  CFSG.StandardType.GGHalf CFSG.Timmesfeld.LieEmbed CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

@[expose] def l1Root (i : Fin 16) : Fin Tag.E6.rank → ℤ :=
  (mu1List ++ mu2List).getD (i : ℕ) 0

private lemma e6iq_zmod_two (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x; decide

private lemma e6iq_F2_two (x : F2) : x = 0 ∨ x = 1 := by
  rcases e6iq_zmod_two (GaloisField.equivZmodP (p := 2) x) with h | h
  · left
    apply (GaloisField.equivZmodP (p := 2)).injective
    rw [h, map_zero]
  · right
    apply (GaloisField.equivZmodP (p := 2)).injective
    rw [h, map_one]

private lemma e6iq_subgroupOf_closure_image {G : Type*} [Group G] {C : Subgroup G} (S : Set C) :
    (Subgroup.closure (C.subtype '' S)).subgroupOf C = Subgroup.closure S := by
  rw [← MonoidHom.map_closure]
  exact Subgroup.comap_map_eq_self_of_injective C.subtype_injective _

private lemma e6iq_subgroupOf_sup_of_le {G : Type*} [Group G] {C : Subgroup G}
    {A B : Subgroup G} (hA : A ≤ C) (hB : B ≤ C) :
    (A ⊔ B).subgroupOf C = A.subgroupOf C ⊔ B.subgroupOf C := by
  apply Subgroup.map_injective C.subtype_injective
  rw [Subgroup.subgroupOf_map_subtype, Subgroup.map_sup, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (sup_le hA hB), inf_eq_left.2 hA,
    inf_eq_left.2 hB]

private lemma e6iq_rootSpan_eq_closure_xr
    (S : Set (Fin Tag.E6.rank → ℤ)) :
    rootSpan .E6 F2 S = Subgroup.closure {g | ∃ β ∈ S, pinnedX .E6 F2 β 1 = g} := by
  rw [rootSpan_eq_closure]
  refine le_antisymm ?_ ?_
  · refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨β, hβ, c, rfl⟩
    rcases e6iq_F2_two c with rfl | rfl
    · rw [pinnedX_zero]; exact Subgroup.one_mem _
    · exact Subgroup.subset_closure ⟨β, hβ, rfl⟩
  · refine (Subgroup.closure_le _).mpr ?_
    rintro g ⟨β, hβ, rfl⟩
    exact Subgroup.subset_closure ⟨β, hβ, 1, rfl⟩

private lemma e6iq_closure_xr_eq
    (S : Set (Fin Tag.E6.rank → ℤ)) :
    Subgroup.closure {x : EC | ∃ β ∈ S, xr β = x} =
      (rootSpan .E6 F2 S).subgroupOf (adjointGroup .E6 F2) := by
  have himg : (adjointGroup .E6 F2).subtype '' {x : EC | ∃ β ∈ S, xr β = x} =
      {g : ModGL .E6 F2 | ∃ β ∈ S, pinnedX .E6 F2 β 1 = g} := by
    ext g
    constructor
    · rintro ⟨y, ⟨β, hβ, rfl⟩, rfl⟩
      exact ⟨β, hβ, rfl⟩
    · rintro ⟨β, hβ, rfl⟩
      exact ⟨xr β, ⟨β, hβ, rfl⟩, rfl⟩
  rw [← e6iq_subgroupOf_closure_image (C := adjointGroup .E6 F2)
      (S := {x : EC | ∃ β ∈ S, xr β = x}), himg,
    ← e6iq_rootSpan_eq_closure_xr]

private lemma e6iq_qE_eq_closure :
    qE = Subgroup.closure {x : EC | ∃ β ∈ qRoots, xr β = x} := by
  rw [qE, e6iq_closure_xr_eq]

private lemma e6iq_subgroupOf_closure_xr_eq
    {S : Set (Fin Tag.E6.rank → ℤ)} (hS : S ⊆ qRoots) :
    (Subgroup.closure {x : EC | ∃ β ∈ S, xr β = x}).subgroupOf qE =
      Subgroup.closure {x : ↥qE | ∃ β ∈ S, xr β = (x : EC)} := by
  have hle : Subgroup.closure {x : EC | ∃ β ∈ S, xr β = x} ≤ qE := by
    rw [e6iq_qE_eq_closure]
    exact Subgroup.closure_mono (by
      rintro x ⟨β, hβ, rfl⟩
      exact ⟨β, hS hβ, rfl⟩)
  have himg : qE.subtype '' {x : ↥qE | ∃ β ∈ S, xr β = (x : EC)} =
      {x : EC | ∃ β ∈ S, xr β = x} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hle (Subgroup.subset_closure hx)⟩, hx, rfl⟩
  have h := e6iq_subgroupOf_closure_image (C := qE)
    (S := {x : ↥qE | ∃ β ∈ S, xr β = (x : EC)})
  rw [himg] at h
  exact h

private lemma e6iq_ofFn_l1Root :
    List.ofFn l1Root = mu1List ++ mu2List := by
  decide +kernel

private lemma e6iq_mem_l1List_iff 
    (β : Fin Tag.E6.rank → ℤ) :
    β ∈ mu1List ++ mu2List ↔ ∃ i : Fin 16, l1Root i = β := by
  rw [← e6iq_ofFn_l1Root]
  exact List.mem_ofFn

private lemma e6iq_l1Root_mem_list 
    (i : Fin 16) : l1Root i ∈ mu1List ++ mu2List :=
  (e6iq_mem_l1List_iff _).2 ⟨i, rfl⟩

private lemma e6iq_l1Root_facts
    (i : Fin 16) : IsRoot .E6 (l1Root i) ∧ iform (l1Root i) lamE = 1 := by
  refine ⟨?_, ?_⟩
  · rw [← mem_rootFinset]; fin_cases i <;> decide +kernel
  · fin_cases i <;> decide +kernel

private lemma e6iq_mu1_mem :
    ∀ β ∈ mu1List.toFinset, β ∈ rootFinset Tag.E6 ∧ iform β lamE = 1 := by
  decide +kernel

private lemma e6iq_l1List_mem :
    ∀ β ∈ (mu1List ++ mu2List).toFinset, β ∈ rootFinset Tag.E6 ∧ iform β lamE = 1 := by
  decide +kernel

private lemma e6iq_levelOne_mem :
    ∀ β ∈ rootFinset Tag.E6, iform β lamE = 1 → β ∈ (mu1List ++ mu2List).toFinset := by
  decide +kernel

private lemma e6iq_level_cases :
    ∀ β ∈ rootFinset Tag.E6, 0 < iform β lamE → iform β lamE = 1 ∨ iform β lamE = 2 := by
  decide +kernel

private lemma e6iq_yLamAS_le_two :
    ∀ β ∈ rootFinset Tag.E6, iform β E6Pilot.yLamAS ≤ 2 := by
  decide +kernel

private lemma e6iq_l1Root_mem_mu1 :
    ∀ i : Fin 16, (i : ℕ) < 8 → l1Root i ∈ mu1List := by
  decide +kernel

private lemma e6iq_l1Root_mem_mu2 :
    ∀ i : Fin 16, 8 ≤ (i : ℕ) → l1Root i ∈ mu2List := by
  decide +kernel

private lemma e6iq_mu1_index :
    ∀ β ∈ mu1List.toFinset, ∃ i : Fin 16, (i : ℕ) < 8 ∧ l1Root i = β := by
  decide +kernel

private lemma e6iq_mu2_index :
    ∀ β ∈ mu2List.toFinset, ∃ i : Fin 16, 8 ≤ (i : ℕ) ∧ l1Root i = β := by
  decide +kernel

private lemma e6iq_l1_sum_level :
    ∀ β ∈ (mu1List ++ mu2List).toFinset, ∀ γ ∈ (mu1List ++ mu2List).toFinset,
      (β + γ) ∈ rootFinset Tag.E6 → iform (β + γ) lamE = 2 := by
  decide +kernel

private lemma e6iq_stdQRoots_ncard :
    stdQRoots.ncard = 24 := by
  have h : stdQRoots =
      ↑((rootFinset Tag.E6).filter (fun γ => 0 < iform γ E6Pilot.yLamAS)) := by
    ext γ
    simp only [stdQRoots, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_coe, mem_rootFinset]
  rw [h, Set.ncard_coe_finset]
  decide +kernel

private lemma e6iq_stdZRoots_ncard :
    stdZRoots.ncard = 8 := by
  have h : stdZRoots =
      ↑((rootFinset Tag.E6).filter (fun γ => iform γ E6Pilot.yLamAS = 2)) := by
    ext γ
    simp only [stdZRoots, Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_coe, mem_rootFinset]
  rw [h, Set.ncard_coe_finset]
  decide +kernel

private lemma e6iq_xr_mem_qE
    {β : Fin Tag.E6.rank → ℤ} (hβ : β ∈ qRoots) : xr β ∈ qE := by
  rw [qE]
  exact Subgroup.mem_subgroupOf.2 (pinnedX_mem_rootSpan hβ 1)

private lemma e6iq_xr_mem_z0E
    {β : Fin Tag.E6.rank → ℤ} (hβ : β ∈ rootFinset Tag.E6) (h2 : iform β lamE = 2) :
    xr β ∈ z0E := by
  have h : β ∈ zRoots := ⟨mem_rootFinset.1 hβ, h2⟩
  rw [z0E]
  exact Subgroup.mem_subgroupOf.2 (pinnedX_mem_rootSpan h 1)

private lemma e6iq_xr_mem_uMu1
    {β : Fin Tag.E6.rank → ℤ} (hβ : β ∈ mu1List) : xr β ∈ uMu1 := by
  rw [uMu1]
  exact Subgroup.mem_subgroupOf.2 (pinnedX_mem_rootSpan (by simpa using hβ) 1)

private lemma e6iq_xr_mem_uMu2
    {β : Fin Tag.E6.rank → ℤ} (hβ : β ∈ mu2List) : xr β ∈ uMu2 := by
  rw [uMu2]
  exact Subgroup.mem_subgroupOf.2 (pinnedX_mem_rootSpan (by simpa using hβ) 1)

private lemma e6iq_uMu1_le_qE :
    uMu1 ≤ qE := by
  have hsub : ({β : Fin Tag.E6.rank → ℤ | β ∈ mu1List} : Set _) ⊆ qRoots := by
    intro β hβ
    have h := e6iq_mu1_mem β (List.mem_toFinset.2 hβ)
    exact ⟨mem_rootFinset.1 h.1, by rw [h.2]; norm_num⟩
  rw [uMu1, qE]
  exact Subgroup.subgroupOf_mono _ (by
    rw [e6iq_rootSpan_eq_closure_xr, e6iq_rootSpan_eq_closure_xr]
    exact Subgroup.closure_mono (by
      rintro g ⟨β, hβ, rfl⟩
      exact ⟨β, hsub hβ, rfl⟩))

private lemma e6iq_uMu2_le_qE :
    uMu2 ≤ qE := by
  have hsub : ({β : Fin Tag.E6.rank → ℤ | β ∈ mu2List} : Set _) ⊆ qRoots := by
    intro β hβ
    have h : β ∈ mu2List.toFinset := List.mem_toFinset.2 hβ
    have h' : β ∈ (mu1List ++ mu2List).toFinset := by
      rw [List.toFinset_append]; exact Finset.mem_union_right _ h
    have h2 := e6iq_l1List_mem β h'
    exact ⟨mem_rootFinset.1 h2.1, by rw [h2.2]; norm_num⟩
  rw [uMu2, qE]
  exact Subgroup.subgroupOf_mono _ (by
    rw [e6iq_rootSpan_eq_closure_xr, e6iq_rootSpan_eq_closure_xr]
    exact Subgroup.closure_mono (by
      rintro g ⟨β, hβ, rfl⟩
      exact ⟨β, hsub hβ, rfl⟩))

private lemma e6iq_closure_qE_top :
    Subgroup.closure {x : ↥qE | ∃ β ∈ qRoots, xr β = (x : EC)} = ⊤ := by
  have h := e6iq_subgroupOf_closure_xr_eq (S := qRoots) (fun _ h => h)
  rw [← e6iq_qE_eq_closure, Subgroup.subgroupOf_self] at h
  exact h.symm

private lemma e6iq_uMu1_closure :
    uMu1.subgroupOf qE =
      Subgroup.closure {x : ↥qE | ∃ β ∈ mu1List, xr β = (x : EC)} := by
  have h := e6iq_subgroupOf_closure_xr_eq (S := {β : Fin Tag.E6.rank → ℤ | β ∈ mu1List})
    (by
      intro β hβ
      have h' := e6iq_mu1_mem β (List.mem_toFinset.2 hβ)
      exact ⟨mem_rootFinset.1 h'.1, by rw [h'.2]; norm_num⟩)
  rwa [show Subgroup.closure {x : EC | ∃ β ∈ ({β : Fin Tag.E6.rank → ℤ | β ∈ mu1List} : Set _),
      xr β = x} = uMu1 from (e6iq_closure_xr_eq _).trans rfl] at h

private lemma e6iq_uMu2_closure :
    uMu2.subgroupOf qE =
      Subgroup.closure {x : ↥qE | ∃ β ∈ mu2List, xr β = (x : EC)} := by
  have h := e6iq_subgroupOf_closure_xr_eq (S := {β : Fin Tag.E6.rank → ℤ | β ∈ mu2List})
    (by
      intro β hβ
      have h' : β ∈ (mu1List ++ mu2List).toFinset := by
        rw [List.toFinset_append]; exact Finset.mem_union_right _ (List.mem_toFinset.2 hβ)
      have h2 := e6iq_l1List_mem β h'
      exact ⟨mem_rootFinset.1 h2.1, by rw [h2.2]; norm_num⟩)
  rwa [show Subgroup.closure {x : EC | ∃ β ∈ ({β : Fin Tag.E6.rank → ℤ | β ∈ mu2List} : Set _),
      xr β = x} = uMu2 from (e6iq_closure_xr_eq _).trans rfl] at h

private lemma e6iq_commutator_l1
    {β γ : Fin Tag.E6.rank → ℤ} (hβ : β ∈ (mu1List ++ mu2List).toFinset)
    (hγ : γ ∈ (mu1List ++ mu2List).toFinset) :
    xr β * xr γ * (xr β)⁻¹ * (xr γ)⁻¹ ∈ z0E := by
  have hβf := e6iq_l1List_mem β hβ
  have hγf := e6iq_l1List_mem γ hγ
  have hβr : IsRoot .E6 β := mem_rootFinset.1 hβf.1
  have hγr : IsRoot .E6 γ := mem_rootFinset.1 hγf.1
  by_cases hEq : β = γ
  · subst hEq
    rw [show xr β * xr β * (xr β)⁻¹ * (xr β)⁻¹ = 1 from by group]
    exact Subgroup.one_mem _
  have hne' : β ≠ -γ := by
    intro h
    have h1 : iform β lamE = iform (-γ) lamE := by rw [h]
    have h2 : iform (-γ) lamE = -iform γ lamE := by
      calc iform (-γ) lamE = iform ((-1 : ℤ) • γ) lamE := by rw [neg_one_smul]
        _ = (-1 : ℤ) * iform γ lamE := iform_smul_left (-1) γ lamE
        _ = -iform γ lamE := by ring
    rw [h2, hγf.2, hβf.2] at h1
    norm_num at h1
  by_cases hab : (β + γ) ∈ rootFinset Tag.E6
  · obtain ⟨hsign, hformula⟩ := (simply_laced_root_commutator_unit .E6 (Or.inr (Or.inl rfl))
      hβr hγr hEq hne').1 (mem_rootFinset.1 hab)
    have hcast : (commConst .E6 β γ (1, 1) : F2) = 1 := by
      rcases hsign with h | h
      · rw [h]; norm_num
      · rw [h, Int.cast_neg, Int.cast_one]
        exact CFSG.LieType.Chevalley.E6GraphLevi.neg_eq_self_of_two CharTwo.two_eq_zero (1 : F2)
    have hc : ⁅pinnedX .E6 F2 β 1, pinnedX .E6 F2 γ 1⁆ = pinnedX .E6 F2 (β + γ) 1 := by
      have h := hformula F2 (1 : F2) (1 : F2)
      rwa [show (commConst .E6 β γ (1, 1) : F2) * 1 * 1 = 1 from by
        rw [hcast, mul_one, mul_one]] at h
    have heq : xr β * xr γ * (xr β)⁻¹ * (xr γ)⁻¹ = xr (β + γ) := by
      apply Subtype.ext
      show pinnedX .E6 F2 β 1 * pinnedX .E6 F2 γ 1 * (pinnedX .E6 F2 β 1)⁻¹ *
          (pinnedX .E6 F2 γ 1)⁻¹ = pinnedX .E6 F2 (β + γ) 1
      rw [← commutatorElement_def]
      exact hc
    rw [heq]
    exact e6iq_xr_mem_z0E hab (e6iq_l1_sum_level β hβ γ hγ hab)
  · have hcommP : Commute (pinnedX .E6 F2 β 1) (pinnedX .E6 F2 γ 1) :=
      (simply_laced_root_commutator_unit .E6 (Or.inr (Or.inl rfl)) hβr hγr hEq hne').2
        (fun h => hab (mem_rootFinset.2 h)) F2 _
        (Subgroup.subset_closure ⟨(1 : F2), rfl⟩) _
        (Subgroup.subset_closure ⟨(1 : F2), rfl⟩)
    have hc : Commute (xr β) (xr γ) := by
      rw [Commute] at hcommP ⊢
      exact Subtype.ext hcommP
    rw [show xr β * xr γ * (xr β)⁻¹ * (xr γ)⁻¹ = 1 from by
      rw [hc.eq]; group]
    exact Subgroup.one_mem _

private lemma e6iq_card_qE :
    Nat.card qE = 2 ^ 24 := by
  have hstd : Nat.card (rootSpan .E6 F2 stdQRoots) = 2 ^ 24 := by
    rw [show stdQRoots = parabolicRadicalRoots .E6 E6Pilot.nodes16 from
      E6Pilot.parabolicRadicalRoots_nodes16.symm]
    change Nat.card ↥(parabolicRadical .E6 F2 E6Pilot.nodes16) = 2 ^ 24
    rw [card_parabolicRadical (K := F2) E6Pilot.nodes16,
      show parabolicRadicalRoots .E6 E6Pilot.nodes16 = stdQRoots from
        E6Pilot.parabolicRadicalRoots_nodes16,
      e6iq_stdQRoots_ncard]
    rw [GaloisField.card 2 1 (by norm_num)]; norm_num
  have hqstd : Nat.card qStd = 2 ^ 24 := by
    have hle : rootSpan .E6 F2 stdQRoots ≤ adjointGroup .E6 F2 :=
      rootSpan_le_adjointGroup F2 stdQRoots
    calc Nat.card qStd = Nat.card (Subgroup.map (adjointGroup .E6 F2).subtype qStd) :=
          (Subgroup.card_subtype (adjointGroup .E6 F2) qStd).symm
      _ = Nat.card (rootSpan .E6 F2 stdQRoots) := by
          rw [show qStd = (rootSpan .E6 F2 stdQRoots).subgroupOf (adjointGroup .E6 F2)
              from rfl,
            Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hle]
      _ = 2 ^ 24 := hstd
  rw [qE_eq_map_qStd, Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj nQ))]
  exact hqstd

private lemma e6iq_card_z0E :
    Nat.card z0E = 2 ^ 8 := by
  have hstd : Nat.card (rootSpan .E6 F2 stdZRoots) = 2 ^ 8 := by
    have hS : ∀ α ∈ stdZRoots, IsRoot .E6 α ∧ 0 < height α := by
      intro α hα
      have hαr : α ∈ rootFinset Tag.E6 := mem_rootFinset.2 hα.1
      have hiff := (E6Pilot.yLamAS_check.1 α hαr).2.1
      exact ⟨hα.1, (hiff.mp (by rw [hα.2]; norm_num)).1⟩
    have hclosed : ∀ α ∈ stdZRoots, ∀ β ∈ stdZRoots, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b →
        IsRoot .E6 (a • α + b • β) → a • α + b • β ∈ stdZRoots := by
      intro α hα β hβ a b ha hb hr
      exfalso
      have h1 : iform (a • α + b • β) E6Pilot.yLamAS = (a : ℤ) * 2 + (b : ℤ) * 2 := by
        rw [← Nat.cast_smul_eq_nsmul ℤ a α, ← Nat.cast_smul_eq_nsmul ℤ b β,
          iform_add_left, iform_smul_left, iform_smul_left, hα.2, hβ.2]
      have h2 : iform (a • α + b • β) E6Pilot.yLamAS ≤ 2 :=
        e6iq_yLamAS_le_two _ (mem_rootFinset.2 hr)
      have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
      have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
      nlinarith
    rw [card_rootSpan (K := F2) (τ := .E6) hS hclosed, e6iq_stdZRoots_ncard]
    rw [GaloisField.card 2 1 (by norm_num)]; norm_num
  have hzstd : Nat.card z0Std = 2 ^ 8 := by
    have hle : rootSpan .E6 F2 stdZRoots ≤ adjointGroup .E6 F2 :=
      rootSpan_le_adjointGroup F2 stdZRoots
    calc Nat.card z0Std = Nat.card (Subgroup.map (adjointGroup .E6 F2).subtype z0Std) :=
          (Subgroup.card_subtype (adjointGroup .E6 F2) z0Std).symm
      _ = Nat.card (rootSpan .E6 F2 stdZRoots) := by
          rw [show z0Std = (rootSpan .E6 F2 stdZRoots).subgroupOf (adjointGroup .E6 F2)
              from rfl,
            Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hle]
      _ = 2 ^ 8 := hstd
  rw [z0E_eq_map_z0Std, Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj nQ))]
  exact hzstd

private lemma e6iq_xr_mul_self
    (β : Fin Tag.E6.rank → ℤ) : xr β * xr β = 1 := by
  apply Subtype.ext
  simp only [xr]
  change pinnedX .E6 F2 β 1 * pinnedX .E6 F2 β 1 = (1 : ModGL .E6 F2)
  rw [← pinnedX_add, show (1 : F2) + 1 = 0 from by
    rw [show (1 : F2) + 1 = (2 : F2) from by norm_num, CharTwo.two_eq_zero], pinnedX_zero]

private lemma e6iq_exists_piHom {G : Type*} [Group G] (g : Fin 16 → G)
    (hg2 : ∀ i, g i * g i = 1) (hcomm : ∀ i j, Commute (g i) (g j)) :
    ∃ φ : Multiplicative e6TwoRestQV →* G,
      ∀ i, φ (Multiplicative.ofAdd (Pi.single i 1)) = g i := by
  classical
  have key : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd 1 := by
    intro x; revert x; decide
  have h2 : (1 : ZMod 2) + 1 = 0 := by decide
  let f : ∀ i : Fin 16, Multiplicative (ZMod 2) →* G := fun i =>
    MonoidHom.mk' (fun x => if x.toAdd = 0 then 1 else g i)
      (by
        intro x y
        rcases key x with rfl | rfl <;> rcases key y with rfl | rfl <;>
          simp [ofAdd_zero, ofAdd_eq_one, toAdd_ofAdd, toAdd_mul, h2, hg2 i])
  have hcomm' : Pairwise fun i j : Fin 16 =>
      ∀ (x : Multiplicative (ZMod 2)) (y : Multiplicative (ZMod 2)),
        Commute ((f i) x) ((f j) y) := by
    intro i j hij x y
    rcases key x with rfl | rfl <;> rcases key y with rfl | rfl <;>
      simp [f, ofAdd_zero, ofAdd_eq_one, toAdd_ofAdd, hcomm i j]
  refine ⟨(MonoidHom.noncommPiCoprod f hcomm').comp
    (MulEquiv.piMultiplicative (fun _ : Fin 16 => ZMod 2)).toMonoidHom, ?_⟩
  intro i
  rw [MonoidHom.comp_apply]
  have hx : (MulEquiv.piMultiplicative (fun _ : Fin 16 => ZMod 2))
      (Multiplicative.ofAdd (Pi.single i 1)) =
        Pi.mulSingle (M := fun _ : Fin 16 => Multiplicative (ZMod 2)) i
          (Multiplicative.ofAdd (1 : ZMod 2)) := by
    ext j
    rw [MulEquiv.piMultiplicative_apply, Pi.mulSingle_apply]
    by_cases hj : j = i
    · subst hj; simp [toAdd_ofAdd]
    · simp [toAdd_ofAdd, Pi.single_eq_of_ne hj, if_neg hj, ofAdd_zero]
  change (MonoidHom.noncommPiCoprod f hcomm')
    ((MulEquiv.piMultiplicative (fun _ : Fin 16 => ZMod 2))
      (Multiplicative.ofAdd (Pi.single i 1))) = g i
  rw [hx, MonoidHom.noncommPiCoprod_mulSingle]
  simp [f, toAdd_ofAdd]

private def e6iq_mulSubgroup (M : Submodule (ZMod 2) e6TwoRestQV) : Subgroup (Multiplicative e6TwoRestQV) where
  carrier := {x | Multiplicative.toAdd x ∈ M}
  mul_mem' := by
    intro a b ha hb
    show Multiplicative.toAdd (a * b) ∈ M
    rw [toAdd_mul]
    exact M.add_mem ha hb
  one_mem' := by
    show Multiplicative.toAdd (1 : Multiplicative e6TwoRestQV) ∈ M
    simpa using M.zero_mem
  inv_mem' := by
    intro a ha
    show Multiplicative.toAdd (a⁻¹) ∈ M
    rw [toAdd_inv]
    exact M.neg_mem ha

private lemma e6iq_sum_single_eq (v : e6TwoRestQV) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin 16 => v i = 1),
      Pi.single (M := fun _ : Fin 16 => ZMod 2) i (1 : ZMod 2)) = v := by
  funext j
  rw [Finset.sum_apply]
  have key : ∀ i : Fin 16,
      (Pi.single (M := fun _ : Fin 16 => ZMod 2) i (1 : ZMod 2)) j =
        if i = j then 1 else 0 := by
    intro i
    rw [Pi.single_apply]
    by_cases h : j = i <;> simp [h, eq_comm]
  simp only [key, Finset.sum_ite_eq']
  by_cases hj : j ∈ Finset.univ.filter (fun i : Fin 16 => v i = 1)
  · rw [if_pos hj]; exact ((Finset.mem_filter.1 hj).2).symm
  · rw [if_neg hj]
    rcases e6iq_zmod_two (v j) with h | h
    · exact h.symm
    · exact absurd h (fun hv => hj (Finset.mem_filter.2 ⟨Finset.mem_univ j, hv⟩))

private lemma e6iq_list_sum_single (L : List (Fin 16)) (hL : L.Nodup) (v : e6TwoRestQV)
    (h : ∀ i, i ∈ L ↔ v i = 1) :
    (L.map (fun i => Pi.single (M := fun _ : Fin 16 => ZMod 2) i (1 : ZMod 2))).sum = v := by
  rw [← List.sum_toFinset (fun i => Pi.single (M := fun _ : Fin 16 => ZMod 2) i (1 : ZMod 2)) hL]
  have hS : L.toFinset = Finset.univ.filter (fun i : Fin 16 => v i = 1) := by
    ext i
    rw [List.mem_toFinset, h i, Finset.mem_filter]
    exact ⟨fun h => ⟨Finset.mem_univ i, h⟩, fun h => h.2⟩
  rw [hS, e6iq_sum_single_eq v]


theorem xr_l1Root_mem_qE
    (i : Fin 16) : xr (l1Root i) ∈ qE := by
  refine e6iq_xr_mem_qE ⟨(e6iq_l1Root_facts i).1, ?_⟩
  rw [(e6iq_l1Root_facts i).2]; norm_num

theorem xr_l1Root_mem_uMu1
    (i : Fin 16) (hi : (i : ℕ) < 8) : xr (l1Root i) ∈ uMu1 :=
  e6iq_xr_mem_uMu1 (e6iq_l1Root_mem_mu1 i hi)

theorem xr_l1Root_mem_uMu2
    (i : Fin 16) (hi : 8 ≤ (i : ℕ)) : xr (l1Root i) ∈ uMu2 :=
  e6iq_xr_mem_uMu2 (e6iq_l1Root_mem_mu2 i hi)

@[expose] def IsQCoord
    (c : ↥qE →* Multiplicative e6TwoRestQV) : Prop :=
  Function.Surjective c ∧ c.ker = z0E.subgroupOf qE ∧
    ∀ i : Fin 16, c ⟨xr (l1Root i), xr_l1Root_mem_qE i⟩ = Multiplicative.ofAdd (Pi.single i 1)

theorem exists_qcoord :
    ∃ c : ↥qE →* Multiplicative e6TwoRestQV, IsQCoord c := by
  classical
  let K : Subgroup ↥qE := z0E.subgroupOf qE
  have hKnormal : K.Normal := by
    apply Subgroup.normal_of_le_center
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx' : (x : EC) ∈ z0E := Subgroup.mem_subgroupOf.1 hx
    have hcomm := Subgroup.mem_centralizer_iff.1 (z0E_central hx') (y : EC) y.2
    exact Subtype.ext hcomm
  haveI := hKnormal
  let π : ↥qE →* (↥qE ⧸ K) := QuotientGroup.mk' K
  let g : Fin 16 → (↥qE ⧸ K) := fun i => π ⟨xr (l1Root i), xr_l1Root_mem_qE i⟩
  have hg : ∀ i, g i = π ⟨xr (l1Root i), xr_l1Root_mem_qE i⟩ := fun _ => rfl
  have hg2 : ∀ i, g i * g i = 1 := by
    intro i
    rw [hg i, ← map_mul,
      show (⟨xr (l1Root i), xr_l1Root_mem_qE i⟩ : ↥qE) *
        ⟨xr (l1Root i), xr_l1Root_mem_qE i⟩ = 1 from
        Subtype.ext (e6iq_xr_mul_self (l1Root i)), map_one]
  have hcommg : ∀ i j, Commute (g i) (g j) := by
    intro i j
    have hmem : (⟨xr (l1Root i), xr_l1Root_mem_qE i⟩ : ↥qE) *
        ⟨xr (l1Root j), xr_l1Root_mem_qE j⟩ *
        (⟨xr (l1Root i), xr_l1Root_mem_qE i⟩ : ↥qE)⁻¹ *
        (⟨xr (l1Root j), xr_l1Root_mem_qE j⟩ : ↥qE)⁻¹ ∈ K := by
      rw [show K = z0E.subgroupOf qE from rfl]
      refine Subgroup.mem_subgroupOf.2 ?_
      exact e6iq_commutator_l1 (List.mem_toFinset.2 (e6iq_l1Root_mem_list i))
        (List.mem_toFinset.2 (e6iq_l1Root_mem_list j))
    have h1 : π ((⟨xr (l1Root i), xr_l1Root_mem_qE i⟩ : ↥qE) *
        ⟨xr (l1Root j), xr_l1Root_mem_qE j⟩ *
        (⟨xr (l1Root i), xr_l1Root_mem_qE i⟩ : ↥qE)⁻¹ *
        (⟨xr (l1Root j), xr_l1Root_mem_qE j⟩ : ↥qE)⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).2 hmem
    have h2 : g i * g j * (g i)⁻¹ * (g j)⁻¹ = 1 := by
      rw [hg i, hg j]
      simp only [map_mul, map_inv] at h1
      exact h1
    rw [Commute]
    calc g i * g j = g i * g j * (g i)⁻¹ * (g j)⁻¹ * (g j * g i) := by group
      _ = 1 * (g j * g i) := by rw [h2]
      _ = g j * g i := one_mul _
  obtain ⟨φ, hφ⟩ := e6iq_exists_piHom g hg2 hcommg
  let S : Set ↥qE := {x : ↥qE | ∃ β ∈ qRoots, xr β = (x : EC)}
  have hgen : Subgroup.closure (Set.range g) = ⊤ := by
    have hsub : π '' S ⊆ Subgroup.closure (Set.range g) := by
      rintro y ⟨x, hx, rfl⟩
      obtain ⟨β, hβ, hxβ⟩ := hx
      have hx' : x = ⟨xr β, e6iq_xr_mem_qE hβ⟩ := Subtype.ext hxβ.symm
      subst hx'
      obtain ⟨hβr, hβpos⟩ := hβ
      rcases e6iq_level_cases β (mem_rootFinset.2 hβr) hβpos with hlev | hlev
      · obtain ⟨i, rfl⟩ := (e6iq_mem_l1List_iff β).1
          (List.mem_toFinset.1 (e6iq_levelOne_mem β (mem_rootFinset.2 hβr) hlev))
        exact Subgroup.subset_closure ⟨i, rfl⟩
      · have hz : xr β ∈ z0E := e6iq_xr_mem_z0E (mem_rootFinset.2 hβr) hlev
        have h1 : π ⟨xr β, e6iq_xr_mem_qE ⟨hβr, hβpos⟩⟩ = 1 :=
          (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hz)
        rw [h1]
        exact Subgroup.one_mem _
    refine top_le_iff.mp ?_
    calc (⊤ : Subgroup (↥qE ⧸ K)) = Subgroup.map π ⊤ :=
          (Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective K)).symm
      _ = Subgroup.map π (Subgroup.closure S) := by
          rw [show Subgroup.closure S = ⊤ from e6iq_closure_qE_top]
      _ = Subgroup.closure (π '' S) := MonoidHom.map_closure π S
      _ ≤ Subgroup.closure (Set.range g) := (Subgroup.closure_le _).mpr hsub
  have hsurjφ : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top]
    refine le_antisymm le_top ?_
    calc ⊤ = Subgroup.closure (Set.range g) := hgen.symm
      _ ≤ φ.range := by
          refine (Subgroup.closure_le _).mpr ?_
          rintro y ⟨i, rfl⟩
          exact ⟨Multiplicative.ofAdd (Pi.single i 1), hφ i⟩
  have hKcard : Nat.card K = 2 ^ 8 := by
    calc Nat.card K = Nat.card (Subgroup.map qE.subtype K) := (Subgroup.card_subtype qE K).symm
      _ = Nat.card z0E := by
          rw [show K = z0E.subgroupOf qE from rfl, Subgroup.subgroupOf_map_subtype,
            inf_eq_left.mpr z0E_le_qE]
      _ = 2 ^ 8 := e6iq_card_z0E
  have hquot : Nat.card (↥qE ⧸ K) = 2 ^ 16 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup K
    rw [e6iq_card_qE, hKcard] at h
    norm_num at h
    omega
  have hQV : Nat.card (Multiplicative e6TwoRestQV) = 2 ^ 16 := by
    change Nat.card (Fin 16 → ZMod 2) = 2 ^ 16
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hbijφ : Function.Bijective φ :=
    hsurjφ.bijective_of_nat_card_le (le_of_eq (hQV.trans hquot.symm))
  refine ⟨(MulEquiv.ofBijective φ hbijφ).symm.toMonoidHom.comp π, ?_, ?_, ?_⟩
  · exact (MulEquiv.ofBijective φ hbijφ).symm.surjective.comp (QuotientGroup.mk'_surjective K)
  · ext x
    rw [MonoidHom.mem_ker]
    change (MulEquiv.ofBijective φ hbijφ).symm (π x) = 1 ↔ x ∈ K
    rw [MulEquiv.symm_apply_eq, map_one]
    exact QuotientGroup.eq_one_iff x
  · intro i
    change (MulEquiv.ofBijective φ hbijφ).symm (π ⟨xr (l1Root i), xr_l1Root_mem_qE i⟩) =
      Multiplicative.ofAdd (Pi.single i 1)
    rw [show π ⟨xr (l1Root i), xr_l1Root_mem_qE i⟩ = g i from rfl, ← hφ i]
    exact MulEquiv.symm_apply_apply (MulEquiv.ofBijective φ hbijφ)
      (Multiplicative.ofAdd (Pi.single i 1))

theorem qcoord_mem_U1_iff 
    
    
    
    
    
    
    
    
    
    {c : ↥qE →* Multiplicative e6TwoRestQV} (hc : IsQCoord c) (q : ↥qE) :
    Multiplicative.toAdd (c q) ∈ invU1 ↔ (q : EC) ∈ z0E ⊔ uMu1 := by
  obtain ⟨-, hker, hval⟩ := hc
  constructor
  · intro hq
    let L : List (Fin 16) := (List.finRange 16).filter (fun i => decide ((c q).toAdd i = 1))
    let y : ↥qE := (L.map fun i => (⟨xr (l1Root i), xr_l1Root_mem_qE i⟩ : ↥qE)).prod
    have hLnodup : L.Nodup := (List.nodup_finRange 16).filter _
    have hLmem : ∀ i, i ∈ L ↔ (c q).toAdd i = 1 := by
      intro i
      rw [List.mem_filter]
      exact ⟨fun h => of_decide_eq_true h.2,
        fun h => ⟨List.mem_finRange i, decide_eq_true_eq.mpr h⟩⟩
    have hy : c y = c q := by
      rw [show y = (L.map fun i => (⟨xr (l1Root i), xr_l1Root_mem_qE i⟩ : ↥qE)).prod from
        rfl, MonoidHom.map_list_prod, List.map_map]
      have h1 : (L.map ((⇑c) ∘ fun i => (⟨xr (l1Root i), xr_l1Root_mem_qE i⟩ : ↥qE))) =
          L.map (fun i => Multiplicative.ofAdd (Pi.single i (1 : ZMod 2))) :=
        List.map_congr_left (fun i _ => hval i)
      rw [h1]
      have h2 : (L.map (fun i => Multiplicative.ofAdd (Pi.single i (1 : ZMod 2)))).prod =
          Multiplicative.ofAdd
            ((L.map fun i => Pi.single (M := fun _ : Fin 16 => ZMod 2) i (1 : ZMod 2))).sum := by
        rw [← ofAdd_toAdd
            ((L.map (fun i => Multiplicative.ofAdd (Pi.single i (1 : ZMod 2)))).prod),
          toAdd_list_sum]
        rw [List.map_map]
        exact congrArg Multiplicative.ofAdd (congrArg List.sum
          (List.map_congr_left
            (f := fun i => Multiplicative.toAdd (Multiplicative.ofAdd (Pi.single i (1 : ZMod 2))))
            (g := fun i => Pi.single (M := fun _ : Fin 16 => ZMod 2) i (1 : ZMod 2))
            (fun i _ => toAdd_ofAdd (Pi.single (M := fun _ : Fin 16 => ZMod 2) i (1 : ZMod 2)))))
      rw [h2, e6iq_list_sum_single L hLnodup (Multiplicative.toAdd (c q)) hLmem, ofAdd_toAdd]
    have hyu : (y : EC) ∈ uMu1 := by
      have hyS : y ∈ uMu1.subgroupOf qE := by
        rw [e6iq_uMu1_closure,
          show y = (L.map fun i => (⟨xr (l1Root i), xr_l1Root_mem_qE i⟩ : ↥qE)).prod from rfl]
        refine Subgroup.list_prod_mem _ ?_
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
        refine Subgroup.subset_closure ⟨l1Root i, ?_, rfl⟩
        apply e6iq_l1Root_mem_mu1
        by_contra hlt
        have hlt' : 8 ≤ (i : ℕ) := not_lt.mp hlt
        have h0 : (c q).toAdd i = 0 := hq i hlt'
        have h1 : (c q).toAdd i = 1 := (hLmem i).1 hi
        rw [h0] at h1
        exact zero_ne_one h1
      exact Subgroup.mem_subgroupOf.1 hyS
    have hq' : q * y⁻¹ ∈ z0E.subgroupOf qE := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hy]
      exact mul_inv_cancel _
    have hsplit : (q : EC) = (q * y⁻¹ : EC) * (y : EC) :=
      (congrArg qE.subtype (show q * y⁻¹ * y = q from by group)).symm
    rw [hsplit]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hq'))
      (Subgroup.mem_sup_right hyu)
  · intro hq
    have hsub : (z0E ⊔ uMu1).subgroupOf qE ≤ Subgroup.comap c (e6iq_mulSubgroup invU1) := by
      rw [e6iq_subgroupOf_sup_of_le z0E_le_qE e6iq_uMu1_le_qE]
      refine sup_le ?_ ?_
      · intro x hx
        rw [Subgroup.mem_comap]
        rw [← hker, MonoidHom.mem_ker] at hx
        rw [hx]
        simpa using invU1.zero_mem
      · rw [e6iq_uMu1_closure]
        refine (Subgroup.closure_le _).mpr ?_
        rintro z ⟨β, hβ, hzβ⟩
        obtain ⟨k, hk, hkβ⟩ := e6iq_mu1_index β (List.mem_toFinset.2 hβ)
        have hx : z = ⟨xr (l1Root k), xr_l1Root_mem_qE k⟩ := by
          apply Subtype.ext
          change (z : EC) = xr (l1Root k)
          rw [hkβ, hzβ]
        rw [hx]
        change c ⟨xr (l1Root k), xr_l1Root_mem_qE k⟩ ∈ e6iq_mulSubgroup invU1
        rw [hval k]
        change Multiplicative.toAdd
          (Multiplicative.ofAdd (Pi.single k (1 : ZMod 2))) ∈ invU1
        rw [toAdd_ofAdd]
        intro j hj
        rw [Pi.single_apply, if_neg (by omega : ¬ j = k)]
    exact hsub (Subgroup.mem_subgroupOf.2 hq)

theorem qcoord_mem_U2_iff 
    
    
    
    
    
    
    
    
    
    {c : ↥qE →* Multiplicative e6TwoRestQV} (hc : IsQCoord c) (q : ↥qE) :
    Multiplicative.toAdd (c q) ∈ invU2 ↔ (q : EC) ∈ z0E ⊔ uMu2 := by
  obtain ⟨-, hker, hval⟩ := hc
  constructor
  · intro hq
    let L : List (Fin 16) := (List.finRange 16).filter (fun i => decide ((c q).toAdd i = 1))
    let y : ↥qE := (L.map fun i => (⟨xr (l1Root i), xr_l1Root_mem_qE i⟩ : ↥qE)).prod
    have hLnodup : L.Nodup := (List.nodup_finRange 16).filter _
    have hLmem : ∀ i, i ∈ L ↔ (c q).toAdd i = 1 := by
      intro i
      rw [List.mem_filter]
      exact ⟨fun h => of_decide_eq_true h.2,
        fun h => ⟨List.mem_finRange i, decide_eq_true_eq.mpr h⟩⟩
    have hy : c y = c q := by
      rw [show y = (L.map fun i => (⟨xr (l1Root i), xr_l1Root_mem_qE i⟩ : ↥qE)).prod from
        rfl, MonoidHom.map_list_prod, List.map_map]
      have h1 : (L.map ((⇑c) ∘ fun i => (⟨xr (l1Root i), xr_l1Root_mem_qE i⟩ : ↥qE))) =
          L.map (fun i => Multiplicative.ofAdd (Pi.single i (1 : ZMod 2))) :=
        List.map_congr_left (fun i _ => hval i)
      rw [h1]
      have h2 : (L.map (fun i => Multiplicative.ofAdd (Pi.single i (1 : ZMod 2)))).prod =
          Multiplicative.ofAdd
            ((L.map fun i => Pi.single (M := fun _ : Fin 16 => ZMod 2) i (1 : ZMod 2))).sum := by
        rw [← ofAdd_toAdd
            ((L.map (fun i => Multiplicative.ofAdd (Pi.single i (1 : ZMod 2)))).prod),
          toAdd_list_sum]
        rw [List.map_map]
        exact congrArg Multiplicative.ofAdd (congrArg List.sum
          (List.map_congr_left
            (f := fun i => Multiplicative.toAdd (Multiplicative.ofAdd (Pi.single i (1 : ZMod 2))))
            (g := fun i => Pi.single (M := fun _ : Fin 16 => ZMod 2) i (1 : ZMod 2))
            (fun i _ => toAdd_ofAdd (Pi.single (M := fun _ : Fin 16 => ZMod 2) i (1 : ZMod 2)))))
      rw [h2, e6iq_list_sum_single L hLnodup (Multiplicative.toAdd (c q)) hLmem, ofAdd_toAdd]
    have hyu : (y : EC) ∈ uMu2 := by
      have hyS : y ∈ uMu2.subgroupOf qE := by
        rw [e6iq_uMu2_closure,
          show y = (L.map fun i => (⟨xr (l1Root i), xr_l1Root_mem_qE i⟩ : ↥qE)).prod from rfl]
        refine Subgroup.list_prod_mem _ ?_
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
        refine Subgroup.subset_closure ⟨l1Root i, ?_, rfl⟩
        apply e6iq_l1Root_mem_mu2
        by_contra hlt
        have hlt' : (i : ℕ) < 8 := not_le.mp hlt
        have h0 : (c q).toAdd i = 0 := hq i hlt'
        have h1 : (c q).toAdd i = 1 := (hLmem i).1 hi
        rw [h0] at h1
        exact zero_ne_one h1
      exact Subgroup.mem_subgroupOf.1 hyS
    have hq' : q * y⁻¹ ∈ z0E.subgroupOf qE := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hy]
      exact mul_inv_cancel _
    have hsplit : (q : EC) = (q * y⁻¹ : EC) * (y : EC) :=
      (congrArg qE.subtype (show q * y⁻¹ * y = q from by group)).symm
    rw [hsplit]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hq'))
      (Subgroup.mem_sup_right hyu)
  · intro hq
    have hsub : (z0E ⊔ uMu2).subgroupOf qE ≤ Subgroup.comap c (e6iq_mulSubgroup invU2) := by
      rw [e6iq_subgroupOf_sup_of_le z0E_le_qE e6iq_uMu2_le_qE]
      refine sup_le ?_ ?_
      · intro x hx
        rw [Subgroup.mem_comap]
        rw [← hker, MonoidHom.mem_ker] at hx
        rw [hx]
        simpa using invU2.zero_mem
      · rw [e6iq_uMu2_closure]
        refine (Subgroup.closure_le _).mpr ?_
        rintro z ⟨β, hβ, hzβ⟩
        obtain ⟨k, hk, hkβ⟩ := e6iq_mu2_index β (List.mem_toFinset.2 hβ)
        have hx : z = ⟨xr (l1Root k), xr_l1Root_mem_qE k⟩ := by
          apply Subtype.ext
          change (z : EC) = xr (l1Root k)
          rw [hkβ, hzβ]
        rw [hx]
        change c ⟨xr (l1Root k), xr_l1Root_mem_qE k⟩ ∈ e6iq_mulSubgroup invU2
        rw [hval k]
        change Multiplicative.toAdd
          (Multiplicative.ofAdd (Pi.single k (1 : ZMod 2))) ∈ invU2
        rw [toAdd_ofAdd]
        intro j hj
        rw [Pi.single_apply, if_neg (by omega : ¬ j = k)]
    exact hsub (Subgroup.mem_subgroupOf.2 hq)

end CFSG.StandardType.GGSixE6Two
