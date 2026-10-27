module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5E6Lift

public section

namespace CFSG.StandardType.SmallExc.E6Node

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne CFSG.StandardType.TableBExc.E6Three CFSG.SeitzReduction

section Group

variable {G : Type} [Group G]

theorem comp_le_or_comm [Finite G] {B H N : Subgroup G} (hB : CFSG.Assembly.IsComponentOf B H)
    (hNH : N ≤ H) (hN : H ≤ Subgroup.normalizer (N : Set G)) : B ≤ N ∨ ⁅B, N⁆ = ⊥ := by
  have hBH := hB.1
  have hc := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hBH).1 hB
  have hNn : (N.subgroupOf H).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNH).2 hN
  rcases CFSG.LocalCores.component_normal_subgroup hc hNn with h | h
  · left
    intro x hx
    have := h (Subgroup.mem_subgroupOf.mpr hx : (⟨x, hBH hx⟩ : H) ∈ B.subgroupOf H)
    exact Subgroup.mem_subgroupOf.mp this
  · right
    have := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hBH h
    rwa [inf_eq_left.2 hNH] at this

theorem commute_of_commutator_eq_bot {B N : Subgroup G} (h : ⁅B, N⁆ = ⊥) {s : G} (hs : s ∈ N) :
    ∀ j ∈ B, s * j = j * s := fun _ hj =>
  Subgroup.mem_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hj) s hs

theorem comm_of_double_dichotomy [Finite G] {M : Type} [Group M] {θ : G →* M}
    (hθ : Function.Injective θ) {E H : Subgroup G} {R R₀ : Subgroup M}
    (hE : CFSG.Assembly.IsComponentOf E H)
    (hH : H ≤ Subgroup.normalizer ((R.comap θ ⊓ H : Subgroup G) : Set G))
    (hR : R ≤ Subgroup.normalizer (R₀ : Set M)) (h0 : R₀ ≤ R) {w t : G} (hw : w ∈ H)
    (hθw : θ w ∈ R₀) (ht : θ t ∈ Subgroup.centralizer (R₀ : Set M)) :
    (∀ j ∈ E, w * j = j * w) ∨ ∀ j ∈ E, t * j = j * t := by
  have hwQ : w ∈ R.comap θ ⊓ H := Subgroup.mem_inf.2 ⟨Subgroup.mem_comap.2 (h0 hθw), hw⟩
  rcases comp_le_or_comm hE inf_le_right hH with h | h
  · have hN := le_normalizer_inf (inf_le_left.trans
      ((Subgroup.comap_mono hR).trans (Subgroup.le_normalizer_comap θ)) :
        R.comap θ ⊓ H ≤ Subgroup.normalizer ((R₀.comap θ : Subgroup G) : Set G))
    rcases comp_le_or_comm (hE.of_le_of_le h inf_le_right) inf_le_right hN with h' | h'
    · refine Or.inr fun j hj => hθ ?_
      rw [map_mul, map_mul]
      exact (Subgroup.mem_centralizer_iff.mp ht (θ j) (Subgroup.mem_inf.1 (h' hj)).1).symm
    · exact Or.inl (commute_of_commutator_eq_bot h'
        (Subgroup.mem_inf.2 ⟨Subgroup.mem_comap.2 hθw, hwQ⟩))
  · exact Or.inl (commute_of_commutator_eq_bot h hwQ)

end Group

@[expose] def isoRoots : List (Fin Tag.E6.rank → ℤ) :=
  [![1, 1, 1, 1, 0, 0], ![0, 0, 1, 1, 1, 1], ![1, 1, 2, 2, 1, 1], ![1, 0, 1, 1, 1, 0],
    ![0, 1, 0, 1, 1, 1], ![1, 1, 1, 2, 2, 1], ![-1, -1, -1, -1, 0, 0], ![0, 0, -1, -1, -1, -1],
    ![-1, -1, -2, -2, -1, -1], ![-1, 0, -1, -1, -1, 0], ![0, -1, 0, -1, -1, -1],
    ![-1, -1, -1, -2, -2, -1]]

@[expose] def eIso : Fin Tag.E6.rank → ℤ := ![0, 1, 0, 1, 1, 1]

@[expose] def bIso : Fin Tag.E6.rank → ℤ := ![0, 0, 1, 1, 1, 1]

theorem isoRoots_spec : ∀ δ ∈ isoRoots, RootOps.isRootB .E6 δ = true ∧
    (iform (bE6 0) δ + iform (bE6 1) δ + iform (bE6 2) δ) % 3 = 0 ∧
      iform (bE6 3) δ = 0 ∧ iform (-bE6 3) δ = 0 := by
  decide +kernel

theorem mem_isoRoots : eIso ∈ isoRoots ∧ -eIso ∈ isoRoots ∧ bIso ∈ isoRoots ∧ -bIso ∈ isoRoots := by
  decide +kernel

theorem iform_sub_iso : ∀ j : Fin Tag.E6.rank, iform (bE6 0) (Pi.single j 1) -
    iform (bE6 1) (Pi.single j 1) = iform eIso (Pi.single j 1) - iform bIso (Pi.single j 1) := by
  decide +kernel

@[expose] def isoTest (γ : Fin Tag.E6.rank → ℤ) : Bool :=
  decide ((iform (bE6 0) γ + iform (bE6 1) γ + iform (bE6 2) γ) % 3 = 0 →
    γ ∈ isoRoots ∨ ∀ δ ∈ isoRoots, iform γ δ = 0)

theorem isoTest_roots : (List.range Tag.E6.rootCertificate.roots.length).all
    (fun k => isoTest (Tag.E6.rootCertificate.root k)) = true := by
  decide +kernel

theorem mem_isoRoots_or_perp {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot .E6 γ) (h : (iform (bE6 0) γ + iform (bE6 1) γ + iform (bE6 2) γ) % 3 = 0) :
    γ ∈ isoRoots ∨ ∀ δ ∈ isoRoots, iform γ δ = 0 := by
  obtain ⟨k, hk, rfl⟩ := (RootCertificate.isRoot_iff (Tag.rootCertificate_check _)).1 hγ
  have hc := isoTest_roots
  simp only [List.all_eq_true, List.mem_range, isoTest, decide_eq_true_eq] at hc
  exact hc k hk h

@[expose] def chiIso {L : Type} [Field L] (l : Lˣ) : Fin Tag.E6.rank → Lˣ :=
  hChar (bE6 0) l * hChar (bE6 1) l * hChar (bE6 2) l

theorem mem_rootCharKernel_chiIso {L : Type} [Field L] {l : Lˣ} (hl : orderOf l = 3)
    {γ : Fin Tag.E6.rank → ℤ} : γ ∈ rootCharKernel (chiIso l) ↔
      IsRoot .E6 γ ∧ (iform (bE6 0) γ + iform (bE6 1) γ + iform (bE6 2) γ) % 3 = 0 := by
  simp only [rootCharKernel, Set.mem_setOf_eq, chiIso, rootChar_mul_left, rootChar_hChar,
    ← zpow_add]
  rw [← orderOf_dvd_iff_zpow_eq_one, hl, Nat.cast_ofNat, Int.dvd_iff_emod_eq_zero]

section Certs


theorem isRoot_of_mem_isoRoots {δ : Fin Tag.E6.rank → ℤ} (h : δ ∈ isoRoots) : IsRoot .E6 δ :=
  RootOps.isRootB_iff.mp (isoRoots_spec δ h).1

theorem rootSpan_isoRoots_le {L : Type} [Field L] {l : Lˣ} (hl : orderOf l = 3) :
    rootSpan .E6 L {γ | γ ∈ isoRoots} ≤ rootSpan .E6 L (rootCharKernel (chiIso l)) :=
  iSup₂_le fun δ hδ => le_iSup₂_of_le δ ((mem_rootCharKernel_chiIso hl).2
    ⟨isRoot_of_mem_isoRoots hδ, (isoRoots_spec δ hδ).2.1⟩) le_rfl

section S


section Orth

variable {L : Type} [Field L]

theorem rootSubgroup_le_centralizer_rootSpan {γ : Fin Tag.E6.rank → ℤ}
    {Ψ : Set (Fin Tag.E6.rank → ℤ)} (hγ : IsRoot .E6 γ) (hΨ : ∀ δ ∈ Ψ, IsRoot .E6 δ)
    (h : ∀ δ ∈ Ψ, iform γ δ = 0) :
    rootSubgroup .E6 L γ ≤ Subgroup.centralizer (rootSpan .E6 L Ψ : Set (ModGL .E6 L)) := by
  rw [Subgroup.le_centralizer_iff]
  refine iSup₂_le fun δ hδ y hy => Subgroup.mem_centralizer_iff.2 fun x hx => ?_
  exact (simply_laced_orthogonal_root_commutation .E6 (Or.inr (Or.inl rfl))).2 L γ δ hγ (hΨ δ hδ)
    ((dotProduct_mulVec_symmetrizedCartan_eq_sum γ δ).trans (h δ hδ)) x hx y hy

theorem rootSL2_mem_centralizer_rootSpan {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β)
    (hβ' : IsRoot .E6 (-β)) {Ψ : Set (Fin Tag.E6.rank → ℤ)} (hΨ : ∀ δ ∈ Ψ, IsRoot .E6 δ)
    (h : ∀ δ ∈ Ψ, iform β δ = 0 ∧ iform (-β) δ = 0) (A : SL2 L) :
    rootSL2 .E6 L β A ∈ Subgroup.centralizer (rootSpan .E6 L Ψ : Set (ModGL .E6 L)) := by
  have h' : rootSL2 .E6 L β A ∈ rootRankOneGroup .E6 L β := ⟨A, rfl⟩
  rw [(exceptional_Lang_root_rank_one_torus_transport .E6 L hβ).1] at h'
  exact sup_le (rootSubgroup_le_centralizer_rootSpan hβ hΨ fun δ hδ => (h δ hδ).1)
    (rootSubgroup_le_centralizer_rootSpan hβ' hΨ fun δ hδ => (h δ hδ).2) h'

theorem rootSpan_le_normalizer_rootSpan {S Ψ : Set (Fin Tag.E6.rank → ℤ)}
    (hΨ : ∀ δ ∈ Ψ, IsRoot .E6 δ)
    (h : ∀ γ ∈ S, γ ∈ Ψ ∨ (IsRoot .E6 γ ∧ ∀ δ ∈ Ψ, iform γ δ = 0)) :
    rootSpan .E6 L S ≤ Subgroup.normalizer (rootSpan .E6 L Ψ : Set (ModGL .E6 L)) := by
  refine iSup₂_le fun γ hγ => ?_
  rcases h γ hγ with h1 | ⟨h1, h3⟩
  · exact (le_iSup₂_of_le γ h1 le_rfl : rootSubgroup .E6 L γ ≤ rootSpan .E6 L Ψ).trans
      Subgroup.le_normalizer
  · exact (rootSubgroup_le_centralizer_rootSpan h1 hΨ h3).trans
      (Subgroup.centralizer_le_normalizer _)

theorem rootSpan_kernel_le_normalizer {l : Lˣ} (hl : orderOf l = 3) :
    rootSpan .E6 L (rootCharKernel (chiIso l)) ≤
      Subgroup.normalizer (rootSpan .E6 L {γ | γ ∈ isoRoots} : Set (ModGL .E6 L)) :=
  rootSpan_le_normalizer_rootSpan (fun _ hδ => isRoot_of_mem_isoRoots hδ) fun γ hγ => by
    obtain ⟨hr, h3⟩ := (mem_rootCharKernel_chiIso hl).1 hγ
    exact (mem_isoRoots_or_perp hr h3).imp id fun h => ⟨hr, h⟩

end Orth

end S

end Certs

end CFSG.StandardType.SmallExc.E6Node

end
