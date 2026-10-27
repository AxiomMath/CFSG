module

public import CFSG.Monster.B.Geometry.InitialIsometryModels
public import CFSG.Monster.B.Geometry.F4Extension
public import CFSG.Monster.B.Geometry.F4Stabilizer
public import Certificates.Certificate113
public import Certificates.Certificate114
public import CFSG.LieType.Chevalley.C2E6MinusSixStabilizer
public import CFSG.Monster.B.Geometry.InitialIsometryGlue
public import TauCeti.GroupTheory.Coxeter.Matsumoto

public noncomputable section

namespace CFSG.Monster.B.Geometry

open CoxeterSystem CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.E6.StdF4

local notation "cs4" => coxeterSystem Tag.F4

section Generic

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
  {C : Type*} {δ : C → C → W} {C' : Type*} {δ' : C' → C' → W}

theorem resProj_resProj (hδ : IsWeylDistanceBuilding cs δ) {J K : Set ι} (hKJ : K ⊆ J)
    (x d : C) : resProj cs δ K x (resProj cs δ J x d) = resProj cs δ K x d := by
  refine resProj_eq hδ ⟨resProj_mem hδ K x d, fun r hr hne => ?_⟩
  have hp := isProjection_resProj hδ J x d
  have h1 := (hp.gate hδ (residue_mono hKJ x (resProj_mem hδ K x d))).2
  have h2 := (hp.gate hδ (residue_mono hKJ x hr)).2
  have h3 := (isProjection_resProj hδ K x d).2 r hr hne
  omega

theorem isometry_residue_of_subset (hδ : IsWeylDistanceBuilding cs δ)
    (hδ' : IsWeylDistanceBuilding cs δ') {J K : Set ι} (hJK : J ⊆ K) {c : C} {c' : C'}
    {f : C → C'} (hf : IsTypeIso cs δ δ' (residue cs δ K c) (residue cs δ' K c') f)
    (hfc : f c = c') :
    Set.BijOn f (residue cs δ J c) (residue cs δ' J c') ∧
      ∀ x ∈ residue cs δ J c, ∀ y ∈ residue cs δ J c, δ' (f x) (f y) = δ x y := by
  have hfi := hf.isWeylIsometry hδ hδ'
  exact ⟨hfi.bijOn_residue hδ hδ' (self_mem_residue K c) hfc (residue_mono hJK c)
    (residue_mono hJK c'), fun x hx y hy => hfi.2 x (residue_mono hJK c hx) y
      (residue_mono hJK c hy)⟩

theorem map_resProj_of_subset [Finite W] (hδ : IsWeylDistanceBuilding cs δ)
    (hδ' : IsWeylDistanceBuilding cs δ') {J K : Set ι} (hJK : J ⊆ K) {c d : C} {c' d' : C'}
    {f : C → C'} (hf : IsTypeIso cs δ δ' (residue cs δ K c) (residue cs δ' K c') f)
    (hfc : f c = c') (hfp : f (resProj cs δ K c d) = resProj cs δ' K c' d') :
    f (resProj cs δ J c d) = resProj cs δ' J c' d' := by
  obtain ⟨hbij, -⟩ := isometry_residue_of_subset hδ hδ' hJK hf hfc
  have hp := resProj_mem hδ K c d
  rw [← resProj_resProj hδ hJK c d, ← resProj_map hδ hδ' (y := resProj cs δ K c d) hbij
    fun q hq => hf.dist_eq hδ hδ' hp (residue_mono hJK c hq), hfp, resProj_resProj hδ' hJK]

theorem dist_resProj_of_opposite [Finite W] (hδ : IsWeylDistanceBuilding cs δ) {c d : C}
    (hcd : δ c d = longest cs Set.univ) (J : Set ι) :
    δ c (resProj cs δ J c d) = longest cs J ∧
      δ d (resProj cs δ J c d) = longest cs Set.univ * longest cs J := by
  rw [resProj_eq hδ (isProjection_oppChamber_longest hδ hcd J)]
  obtain ⟨h1, h2⟩ := oppChamber_spec hδ hcd (longest cs J)
  refine ⟨h1, ?_⟩
  rw [dist_inv hδ, h2, mul_inv_rev, inv_inv, isLongest_univ.inv_eq]

end Generic

abbrev unitTypes : Set (Fin Tag.F4.rank) := {j | j ≠ 0}

abbrev orthTypes : Set (Fin Tag.F4.rank) := {j | j ≠ 3}

theorem f4_M (i j : Fin Tag.F4.rank) :
    CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .F4) i j =
      ![![1, 3, 2, 2], ![3, 1, 4, 2], ![2, 4, 1, 3], ![2, 2, 3, 1]] i j := by
  rcases fin_f4_cases i with rfl | rfl | rfl | rfl <;>
    rcases fin_f4_cases j with rfl | rfl | rfl | rfl <;>
    · simp only [CFSG.LieType.RootSystem.coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply,
        RootWalk.coxeterOrder_eq_braidLength]
      decide

theorem f4_M32 :
    CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .F4) 3 2 = 3 := by
  rw [f4_M]; rfl

theorem f4_M21 :
    CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .F4) 2 1 = 4 := by
  rw [f4_M]; rfl

theorem f4_M31 :
    CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .F4) 3 1 = 2 := by
  rw [f4_M]; rfl

theorem f4_M01 :
    CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .F4) 0 1 = 3 := by
  rw [f4_M]; rfl

theorem f4_M12 :
    CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .F4) 1 2 = 4 := by
  rw [f4_M]; rfl

theorem f4_M02 :
    CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_cartan .F4) 0 2 = 2 := by
  rw [f4_M]; rfl

variable {C : Type*} {δ : C → C → WeylGroup .F4} {C' : Type*} {δ' : C' → C' → WeylGroup .F4}

variable (δ) in
structure HasClassicalEnds : Prop where
  unit : ∀ x : C, ∃ f : residue cs4 δ unitTypes x → PFlag UData,
    IsChamberModel cs4 (resDist cs4 δ unitTypes x) (polarChamber UData 3 2 1) f
  orth : ∀ x : C, ∃ f : residue cs4 δ orthTypes x → PFlag OData,
    IsChamberModel cs4 (resDist cs4 δ orthTypes x) (polarChamber OData 0 1 2) f

theorem unitTypes_cases : ∀ i : unitTypes,
    i = ⟨3, by decide⟩ ∨ i = ⟨2, by decide⟩ ∨ i = ⟨1, by decide⟩ := by
  rintro ⟨i, hi⟩
  revert i
  decide

theorem orthTypes_cases : ∀ i : orthTypes,
    i = ⟨0, by decide⟩ ∨ i = ⟨1, by decide⟩ ∨ i = ⟨2, by decide⟩ := by
  rintro ⟨i, hi⟩
  revert i
  decide

section Ends

variable (hδ : IsWeylDistanceBuilding cs4 δ) (hδ' : IsWeylDistanceBuilding cs4 δ')
include hδ hδ'

theorem foundationExtension_unitTypes {c : C} {c' : C'}
    {f : residue cs4 δ unitTypes c → PFlag UData} {f' : residue cs4 δ' unitTypes c' → PFlag UData}
    (hf : IsChamberModel cs4 (resDist cs4 δ unitTypes c) (polarChamber UData 3 2 1) f)
    (hf' : IsChamberModel cs4 (resDist cs4 δ' unitTypes c') (polarChamber UData 3 2 1) f') :
    FoundationExtension (parCS _ unitTypes)
      (fun x y : residue cs4 δ unitTypes c => parDist cs4 δ unitTypes x y)
      (fun x y : residue cs4 δ' unitTypes c' => parDist cs4 δ' unitTypes x y) :=
  foundationExtension_unitary hδ hδ' (u := ⟨3, by decide⟩) (t := ⟨2, by decide⟩)
    (s := ⟨1, by decide⟩) (by decide) (by decide) (by decide) unitTypes_cases
    f4_M32 f4_M21 f4_M31 hf hf'

theorem foundationExtension_orthTypes {c : C} {c' : C'}
    {f : residue cs4 δ orthTypes c → PFlag OData} {f' : residue cs4 δ' orthTypes c' → PFlag OData}
    (hf : IsChamberModel cs4 (resDist cs4 δ orthTypes c) (polarChamber OData 0 1 2) f)
    (hf' : IsChamberModel cs4 (resDist cs4 δ' orthTypes c') (polarChamber OData 0 1 2) f') :
    FoundationExtension (parCS _ orthTypes)
      (fun x y : residue cs4 δ orthTypes c => parDist cs4 δ orthTypes x y)
      (fun x y : residue cs4 δ' orthTypes c' => parDist cs4 δ' orthTypes x y) :=
  foundationExtension_orth hδ hδ' (u := ⟨0, by decide⟩) (t := ⟨1, by decide⟩)
    (s := ⟨2, by decide⟩) (by decide) (by decide) (by decide) orthTypes_cases
    f4_M01 f4_M12 f4_M02 hf hf'

theorem exists_unit_iso (hM : HasClassicalEnds δ) (hM' : HasClassicalEnds δ') {c d : C}
    {c' d' : C'} (hcd : δ c d = longest cs4 Set.univ) (hcd' : δ' c' d' = longest cs4 Set.univ) :
    ∃ A : C → C', IsTypeIso cs4 δ δ' (residue cs4 δ unitTypes c) (residue cs4 δ' unitTypes c') A ∧
      A c = c' ∧ A (resProj cs4 δ unitTypes c d) = resProj cs4 δ' unitTypes c' d' := by
  obtain ⟨f, hf⟩ := hM.unit c
  obtain ⟨f', hf'⟩ := hM'.unit c'
  exact exists_typeIso_unitary hδ hδ' (u := ⟨3, by decide⟩) (t := ⟨2, by decide⟩)
    (s := ⟨1, by decide⟩) (by decide) (by decide) (by decide) unitTypes_cases
    f4_M32 f4_M21 f4_M31 hf hf' (resProj_mem hδ _ c d) (resProj_mem hδ' _ c' d')
    (dist_resProj_of_opposite hδ hcd _).1 (dist_resProj_of_opposite hδ' hcd' _).1

theorem exists_orth_iso (hM : HasClassicalEnds δ) (hM' : HasClassicalEnds δ') {c d : C}
    {c' d' : C'} (hcd : δ c d = longest cs4 Set.univ) (hcd' : δ' c' d' = longest cs4 Set.univ) :
    ∃ A : C → C', IsTypeIso cs4 δ δ' (residue cs4 δ orthTypes c) (residue cs4 δ' orthTypes c') A ∧
      A c = c' ∧ A (resProj cs4 δ orthTypes c d) = resProj cs4 δ' orthTypes c' d' := by
  obtain ⟨f, hf⟩ := hM.orth c
  obtain ⟨f', hf'⟩ := hM'.orth c'
  exact exists_typeIso_orth hδ hδ' (u := ⟨0, by decide⟩) (t := ⟨1, by decide⟩)
    (s := ⟨2, by decide⟩) (by decide) (by decide) (by decide) orthTypes_cases
    f4_M01 f4_M12 f4_M02 hf hf' (resProj_mem hδ _ c d) (resProj_mem hδ' _ c' d')
    (dist_resProj_of_opposite hδ hcd _).1 (dist_resProj_of_opposite hδ' hcd' _).1

theorem ext₃At_unitTypes (hM : HasClassicalEnds δ) (hM' : HasClassicalEnds δ') :
    Ext₃At cs4 δ δ' unitTypes :=
  ext₃At_of_foundationExtension hδ hδ' _ fun a a' => by
    obtain ⟨f, hf⟩ := hM.unit a
    obtain ⟨f', hf'⟩ := hM'.unit a'
    exact foundationExtension_unitTypes hδ hδ' hf hf'

theorem ext₃At_orthTypes (hM : HasClassicalEnds δ) (hM' : HasClassicalEnds δ') :
    Ext₃At cs4 δ δ' orthTypes :=
  ext₃At_of_foundationExtension hδ hδ' _ fun a a' => by
    obtain ⟨f, hf⟩ := hM.orth a
    obtain ⟨f', hf'⟩ := hM'.orth a'
    exact foundationExtension_orthTypes hδ hδ' hf hf'

end Ends

theorem eq_setOf_ne_of_ncard_eq_three {J : Set (Fin Tag.F4.rank)} (hJ : J.ncard = 3) :
    ∃ i : Fin Tag.F4.rank, J = {j | j ≠ i} := by
  have h := Set.ncard_add_ncard_compl J
  rw [hJ, card_f4_index] at h
  obtain ⟨i, hi⟩ := Set.ncard_eq_one.mp (by omega : Jᶜ.ncard = 1)
  refine ⟨i, ?_⟩
  ext j
  have := congrArg (j ∈ ·) hi
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, eq_iff_iff] at this
  simp only [Set.mem_ofPred_eq]
  tauto

theorem rig₂_of_hasClassicalEnds (hδ : IsWeylDistanceBuilding cs4 δ) (hM : HasClassicalEnds δ) :
    Rig₂ cs4 δ := by
  refine rig₂_of_rig₂At fun i j hij => ?_
  by_cases hU : i ≠ 0 ∧ j ≠ 0
  · exact rig₂At_of_rig₂_parDist hδ (J := unitTypes) hU.1 hU.2 hij fun a => by
      obtain ⟨f, hf⟩ := hM.unit a
      exact (foundationExtension_unitTypes hδ hδ hf hf).1
  by_cases hO : i ≠ 3 ∧ j ≠ 3
  · exact rig₂At_of_rig₂_parDist hδ (J := orthTypes) hO.1 hO.2 hij fun a => by
      obtain ⟨f, hf⟩ := hM.orth a
      exact (foundationExtension_orthTypes hδ hδ hf hf).1
  · refine rig₂At_of_commute hδ hij ?_
    rw [f4_M]
    rcases fin_f4_cases i with rfl | rfl | rfl | rfl <;>
      rcases fin_f4_cases j with rfl | rfl | rfl | rfl <;>
      first | rfl | (exfalso; revert hij hU hO; decide)

theorem ext₃_of_hasClassicalEnds (hδ : IsWeylDistanceBuilding cs4 δ)
    (hδ' : IsWeylDistanceBuilding cs4 δ') (hM : HasClassicalEnds δ) (hM' : HasClassicalEnds δ') :
    Ext₃ cs4 δ δ' := by
  refine ext₃_of_ext₃At fun J hJ => ?_
  obtain ⟨i, rfl⟩ := eq_setOf_ne_of_ncard_eq_three hJ
  have h1 : {j : Fin Tag.F4.rank | j ≠ 1} = insert 0 {2, 3} := by
    ext j
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases fin_f4_cases j with rfl | rfl | rfl | rfl <;> decide
  have h2 : {j : Fin Tag.F4.rank | j ≠ 2} = insert 3 {0, 1} := by
    ext j
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases fin_f4_cases j with rfl | rfl | rfl | rfl <;> decide
  have hpair : ∀ a b : Fin Tag.F4.rank, ({a, b} : Set (Fin Tag.F4.rank)).encard ≤ 2 :=
    fun a b => encard_pair_le_two a b
  rcases fin_f4_cases i with rfl | rfl | rfl | rfl
  · exact ext₃At_unitTypes hδ hδ' hM hM'
  · rw [h1]
    exact ext₃At_of_commute hδ hδ' (by decide) (fun k hk => by
      rcases hk with rfl | hk
      · rw [f4_M]; rfl
      · rw [Set.mem_singleton_iff.mp hk, f4_M]; rfl) (hpair 2 3)
  · rw [h2]
    exact ext₃At_of_commute hδ hδ' (by decide) (fun k hk => by
      rcases hk with rfl | hk
      · rw [f4_M]; rfl
      · rw [Set.mem_singleton_iff.mp hk, f4_M]; rfl) (hpair 0 1)
  · exact ext₃At_orthTypes hδ hδ' hM hM'

end CFSG.Monster.B.Geometry
