module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.Basic

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

@[expose] def Wn (x : Geo H M) : Subgroup G := ⨆ (δ : Geo H M) (_ : δ ∈ nbrs x), Vn δ

@[expose] def Wnn (x : Geo H M) : Subgroup G := ⨆ (ν : Geo H M) (_ : ν ∈ nbrs x), Wn ν

omit [Finite G] in
theorem Vn_le_Wn {x δ : Geo H M} (h : δ ∈ nbrs x) : Vn δ ≤ Wn x :=
  le_iSup₂_of_le (f := fun (δ : Geo H M) (_ : δ ∈ nbrs x) => Vn δ) δ h le_rfl

omit [Finite G] in
theorem Wn_le_Wnn {x ν : Geo H M} (h : ν ∈ nbrs x) : Wn ν ≤ Wnn x :=
  le_iSup₂_of_le (f := fun (ν : Geo H M) (_ : ν ∈ nbrs x) => Wn ν) ν h le_rfl

omit [Finite G] in
theorem Vn_le_Wnn {x ν δ : Geo H M} (hν : ν ∈ nbrs x) (hδ : δ ∈ nbrs ν) : Vn δ ≤ Wnn x :=
  (Vn_le_Wn hδ).trans (Wn_le_Wnn hν)

omit [Finite G] in
theorem Vn_le_Wnn_self (x : Geo H M) : Vn x ≤ Wnn x := by
  obtain ⟨ν, hν⟩ := exists_adj x
  exact Vn_le_Wnn (show ν ∈ nbrs x from hν) (mem_nbrs_comm hν)

omit [Finite G] in
theorem Wn_smul (g : ↥(H ⊔ M)) (x : Geo H M) : Wn (g • x) = conjSub (g : G) (Wn x) := by
  unfold Wn
  apply le_antisymm
  · refine iSup₂_le fun δ hδ => ?_
    obtain ⟨δ', rfl⟩ : ∃ δ', δ = g • δ' := ⟨g⁻¹ • δ, by simp⟩
    have hδ' : δ' ∈ nbrs x := (smul_adj g).mp hδ
    rw [Vn_smul]
    exact conjSub_mono _ (le_iSup₂_of_le (f := fun (δ : Geo H M) (_ : δ ∈ nbrs x) => Vn δ)
      δ' hδ' le_rfl)
  · rw [conjSub_le_iff]
    refine iSup₂_le fun δ hδ => ?_
    rw [← conjSub_le_iff, ← Vn_smul]
    exact le_iSup₂_of_le (f := fun (δ : Geo H M) (_ : δ ∈ nbrs (g • x)) => Vn δ)
      (g • δ) ((smul_adj g).mpr hδ) le_rfl

omit [Finite G] in
theorem Wnn_smul (g : ↥(H ⊔ M)) (x : Geo H M) : Wnn (g • x) = conjSub (g : G) (Wnn x) := by
  unfold Wnn
  apply le_antisymm
  · refine iSup₂_le fun ν hν => ?_
    obtain ⟨ν', rfl⟩ : ∃ ν', ν = g • ν' := ⟨g⁻¹ • ν, by simp⟩
    have hν' : ν' ∈ nbrs x := (smul_adj g).mp hν
    rw [Wn_smul]
    exact conjSub_mono _ (le_iSup₂_of_le (f := fun (ν : Geo H M) (_ : ν ∈ nbrs x) => Wn ν)
      ν' hν' le_rfl)
  · rw [conjSub_le_iff]
    refine iSup₂_le fun ν hν => ?_
    rw [← conjSub_le_iff, ← Wn_smul]
    exact le_iSup₂_of_le (f := fun (ν : Geo H M) (_ : ν ∈ nbrs (g • x)) => Wn ν)
      (g • ν) ((smul_adj g).mpr hν) le_rfl

omit [Finite G] in
theorem stab_le_normalizer_Wn (x : Geo H M) : stab x ≤ Subgroup.normalizer (Wn x : Set G) := by
  intro g hg
  obtain ⟨hmem, hfix⟩ := mem_stab.mp hg
  apply mem_normalizer_of_conjSub_eq
  have := Wn_smul (⟨g, hmem⟩ : ↥(H ⊔ M)) x
  rw [hfix] at this
  exact this.symm

omit [Finite G] in
theorem stab_le_normalizer_Wnn (x : Geo H M) : stab x ≤ Subgroup.normalizer (Wnn x : Set G) := by
  intro g hg
  obtain ⟨hmem, hfix⟩ := mem_stab.mp hg
  apply mem_normalizer_of_conjSub_eq
  have := Wnn_smul (⟨g, hmem⟩ : ↥(H ⊔ M)) x
  rw [hfix] at this
  exact this.symm

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem Vn_le_centralizer_Vn {δ δ' : Geo H M} (hδ' : vtype δ' = false)
    (h : dist δ δ' + 3 ≤ bMin H M) : Vn δ ≤ Subgroup.centralizer (Vn δ' : Set G) := by
  refine iSup₂_le fun ℓ hℓ => ?_
  have hd : dist δ' ℓ + 2 ≤ bMin H M := by
    have := dist_le_dist_nbr hℓ δ'
    rw [CosetGeom.dist_comm δ' δ] at this
    omega
  have hVQ : Vn δ' ≤ Qv ℓ := C.Vn_le_Qv_of_dist hδ' hd
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  exact (Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv C.hA ℓ hz).2) v (hVQ hv)

theorem comm_Vn_Vn {δ δ' : Geo H M} (hδ' : vtype δ' = false)
    (h : dist δ δ' + 3 ≤ bMin H M) : ⁅Vn δ, Vn δ'⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro x hx y hy
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_centralizer_iff.mp (C.Vn_le_centralizer_Vn hδ' h hx) y hy).symm

theorem Wn_le_Qv {ν : Geo H M} (hν : vtype ν = true) : Wn ν ≤ Qv ν := by
  refine iSup₂_le fun δ hδ => ?_
  have hvδ := vtype_false_of_mem_nbrs_true hδ hν
  refine C.Vn_le_Qv_of_dist hvδ ?_
  rw [dist_eq_one_iff_adj.mpr (mem_nbrs_comm hδ)]
  have := C.hb5
  omega

theorem Wnn_le_Qv_of_dist {β' x : Geo H M} (hβ : vtype β' = false)
    (h : dist β' x + 4 ≤ bMin H M) : Wnn β' ≤ Qv x := by
  refine iSup₂_le fun ν hν => iSup₂_le fun δ hδ => ?_
  have hvν := vtype_true_of_mem_nbrs_false hν hβ
  have hvδ := vtype_false_of_mem_nbrs_true hδ hvν
  refine C.Vn_le_Qv_of_dist hvδ ?_
  have h1 := dist_le_dist_nbr hν x
  have h2 := dist_le_dist_nbr hδ x
  rw [CosetGeom.dist_comm x ν, CosetGeom.dist_comm x β'] at h1
  rw [CosetGeom.dist_comm x δ, CosetGeom.dist_comm x ν] at h2
  omega

theorem Wnn_le_stab_of_dist {β' x : Geo H M} (hβ : vtype β' = false)
    (h : dist β' x + 3 ≤ bMin H M) : Wnn β' ≤ stab x := by
  refine iSup₂_le fun ν hν => iSup₂_le fun δ hδ => ?_
  have hvν := vtype_true_of_mem_nbrs_false hν hβ
  have hvδ := vtype_false_of_mem_nbrs_true hδ hvν
  refine C.Vn_le_stab_of_dist hvδ ?_
  have h1 := dist_le_dist_nbr hν x
  have h2 := dist_le_dist_nbr hδ x
  rw [CosetGeom.dist_comm x ν, CosetGeom.dist_comm x β'] at h1
  rw [CosetGeom.dist_comm x δ, CosetGeom.dist_comm x ν] at h2
  omega

theorem Wnn_le_Qv {β' : Geo H M} (hβ : vtype β' = false) : Wnn β' ≤ Qv β' :=
  C.Wnn_le_Qv_of_dist hβ (by rw [CosetGeom.dist_self]; have := C.hb5; omega)

theorem Wnn_le_centralizer_Vn {β' : Geo H M} (hβ : vtype β' = false) :
    Wnn β' ≤ Subgroup.centralizer (Vn β' : Set G) := by
  refine iSup₂_le fun ν hν => iSup₂_le fun δ hδ => ?_
  refine C.Vn_le_centralizer_Vn hβ ?_
  have h1 := dist_le_dist_nbr hδ β'
  rw [dist_eq_one_iff_adj.mpr hν] at h1
  have := C.hb5
  rw [CosetGeom.dist_comm]
  omega

theorem isElemAbelian_Wn {ν : Geo H M} (hν : vtype ν = true) : IsElemAbelian 2 (Wn ν) := by
  have e : Wn ν = ⨆ δ : {δ : Geo H M // δ ∈ nbrs ν}, Vn δ.1 := by
    unfold Wn; exact iSup_subtype'
  rw [e]
  refine isElemAbelian_iSup _ (fun δ => isElemAbelian_Vn C.hA C.hb3 δ.1) ?_
  intro δ δ' x hx y hy
  have hvδ' := vtype_false_of_mem_nbrs_true δ'.2 hν
  have hd : dist δ.1 δ'.1 + 3 ≤ bMin H M := by
    have h1 := dist_le_dist_nbr δ'.2 δ.1
    rw [CosetGeom.dist_comm δ.1 ν, dist_eq_one_iff_adj.mpr δ.2] at h1
    have := C.hb5
    omega
  exact (Subgroup.mem_centralizer_iff.mp (C.Vn_le_centralizer_Vn hvδ' hd hx) y hy).symm

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36
