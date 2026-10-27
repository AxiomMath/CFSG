module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcShapeFourKac
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcE6
import CFSG.HardMathSupport.Timmesfeld.LangTorus.ExcKacCount

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE6
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.StandardType.GGFinModel CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag IsElemAbelian)

theorem rck_iform_eq_sum {τ : Tag}
    (γ α : Fin τ.rank → ℤ) : iform γ α = ∑ j, α j * iform γ (Pi.single j 1) := by
  conv_lhs => rw [← Finset.univ_sum_single α]
  rw [iform_finset_sum_right]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h : (Pi.single j (α j) : Fin τ.rank → ℤ) = α j • (Pi.single j 1 : Fin τ.rank → ℤ) := by
    rw [← Pi.single_smul]
    simp
  rw [h, iform_comm, iform_smul_left, iform_comm]

@[expose] def rckE6PermLists : List (List ℤ) :=
  [[0, 0, 0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0, 0, -1], [2, 3, 4, 6, 5, 4, 3, 2],
    [-2, -3, -4, -6, -5, -4, -3, -2], [2, 3, 4, 6, 5, 4, 3, 1], [-2, -3, -4, -6, -5, -4, -3, -1]]

@[expose] def rckE6Perp : Finset (Fin Tag.E8.rank → ℤ) :=
  (rckE6PermLists.map fun l => fun k : Fin Tag.E8.rank => l.getD k 0).toFinset

theorem rckE6Perp_card : rckE6Perp.card = 6 := by
  decide +kernel

theorem rckE6Perp_orth :
    ∀ l ∈ rckE6PermLists, ∀ j : Fin Tag.E8.rank, j.val ≤ 5 →
      iform (τ := Tag.E8) (fun k : Fin Tag.E8.rank => l.getD k 0) (Pi.single j 1) = 0 := by
  decide +kernel

theorem rckE6Perp_root :
    ∀ l ∈ rckE6PermLists, List.ofFn (fun k : Fin Tag.E8.rank => l.getD k 0) ∈
      Tag.E8.artifactRoots := by
  decide +kernel

theorem rckE6Perp_eq :
    {β : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 β ∧
      ∀ α ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8), iform β α = 0} = ↑rckE6Perp := by
  ext β
  simp only [Set.mem_setOf_eq, Finset.mem_coe, rckE6Perp, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨hβ, hperp⟩
    have hl := isRoot_iff_mem_artifactRoots.1 hβ
    have hfun : (fun k : Fin Tag.E8.rank => (List.ofFn β).getD k 0) = β := by
      funext k
      rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact k.2), List.getElem_ofFn]
    have hmem := orth_e6_E8 _ hl (fun j => by
      rw [hfun]
      exact hperp _ (single_mem_parabolicRoots_e6 _ (by simp only [Fin.val_castLE]; omega)))
    exact ⟨List.ofFn β, hmem, hfun⟩
  · rintro ⟨l, hl, rfl⟩
    refine ⟨isRoot_iff_mem_artifactRoots.2 (rckE6Perp_root l hl), fun α hα => ?_⟩
    obtain ⟨-, hsupp⟩ := hα
    rw [rck_iform_eq_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j.val ≤ 5
    · rw [rckE6Perp_orth l hl j hj, mul_zero]
    · rw [hsupp j (by simpa [e6Nodes] using hj), zero_mul]

theorem rckE6_perp_image_ncard
    (v : WeylGroup Tag.E8) :
    {β : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 β ∧
      ∀ α ∈ (fun α => v • α) '' parabolicRoots Tag.E8 (e6Nodes Tag.E8),
        iform β α = 0}.ncard = 6 := by
  have h : {β : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 β ∧
        ∀ α ∈ (fun α => v • α) '' parabolicRoots Tag.E8 (e6Nodes Tag.E8), iform β α = 0} =
      (fun β => v • β) '' {β : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 β ∧
        ∀ α ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8), iform β α = 0} := by
    ext β
    constructor
    · rintro ⟨hβ, hperp⟩
      refine ⟨v⁻¹ • β, ⟨IsRoot.smul hβ _, fun α hα => ?_⟩, smul_inv_smul v β⟩
      rw [← iform_smul v, smul_inv_smul]
      exact hperp _ ⟨α, hα, rfl⟩
    · rintro ⟨β', ⟨hβ', hperp'⟩, rfl⟩
      refine ⟨IsRoot.smul hβ' v, ?_⟩
      rintro _ ⟨α, hα, rfl⟩
      rw [iform_smul]
      exact hperp' α hα
  rw [h, Set.ncard_image_of_injective _ (MulAction.injective v), rckE6Perp_eq,
    Set.ncard_coe_finset, rckE6Perp_card]

theorem rckExc_not_shape_E6
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {a : Fin Tag.E8.rank → GGLˣ}
    (hpa : rootDiagUnit Tag.E8 a ^ p = 1) {ρ : Equiv.Perm (Fin Tag.E8.rank → ℤ)}
    (hroot : ∀ γ, IsRoot Tag.E8 (ρ γ) ↔ IsRoot Tag.E8 γ) (hneg : ∀ γ, ρ (-γ) = -ρ γ)
    (hform : ∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ)
    (hsq : ∀ γ, IsRoot Tag.E8 γ → ρ (ρ γ) = -γ)
    (hstab : ∀ γ ∈ kernelRoots (rootCharHom a), ρ γ ∈ kernelRoots (rootCharHom a))
    (i : KernelComponent (rootCharHom a)) :
    ¬ (compRank (componentRoots (rootCharHom a) i) = 6 ∧
      (componentRoots (rootCharHom a) i).ncard = 72) := by
  rintro ⟨hr, hc⟩
  obtain ⟨v, C, hΨ, hrank, hncard⟩ := rckExc_kac_comp hp hp2 hpa i
  have hCeq := kacCount_E8_six C (hrank.symm.trans hr) (hncard.symm.trans hc)
  have hΨ' : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots Tag.E8 (e6Nodes Tag.E8) := by
    rw [hΨ, hCeq, kacE8.rootsOf_eq_parabolicRoots (by decide)]
    congr 2
    ext j
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
      Option.some.injEq, Set.mem_setOf_eq, e6Nodes]
    revert j
    decide
  have hΨroot : ∀ γ ∈ componentRoots (rootCharHom a) i, IsRoot Tag.E8 γ := fun γ hγ => hγ.1.1
  have hfinΨ : (componentRoots (rootCharHom a) i).Finite :=
    (finite_setOf_isRoot Tag.E8).subset hΨroot
  have hperp6 : {β : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 β ∧
      ∀ α ∈ componentRoots (rootCharHom a) i, iform β α = 0}.ncard = 6 := by
    rw [hΨ']
    exact rckE6_perp_image_ncard v
  have hfinPerp : {β : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 β ∧
      ∀ α ∈ componentRoots (rootCharHom a) i, iform β α = 0}.Finite :=
    (finite_setOf_isRoot Tag.E8).subset fun β hβ => hβ.1
  have hρ4 : ∀ γ, IsRoot Tag.E8 γ → ρ (ρ (ρ (ρ γ))) = γ := by
    intro γ hγ
    rw [hsq γ hγ, hneg γ, hneg (ρ γ), hsq γ hγ, neg_neg]
  rcases rck_comp_dichotomy hform hstab i with hst | hdis
  · have hperpst : ∀ β ∈ {β : Fin Tag.E8.rank → ℤ | IsRoot Tag.E8 β ∧
        ∀ α ∈ componentRoots (rootCharHom a) i, iform β α = 0}, ρ β ∈ {β : Fin Tag.E8.rank → ℤ |
          IsRoot Tag.E8 β ∧ ∀ α ∈ componentRoots (rootCharHom a) i, iform β α = 0} := by
      rintro β ⟨hβ, hβperp⟩
      refine ⟨(hroot β).2 hβ, fun α hα => ?_⟩
      have hα3 : ρ (ρ (ρ α)) ∈ componentRoots (rootCharHom a) i := hst _ (hst _ (hst _ hα))
      have h := hform β (ρ (ρ (ρ α)))
      rw [hρ4 α (hΨroot α hα)] at h
      rw [h]
      exact hβperp _ hα3
    have h4 := rck_four_dvd_ncard hfinPerp (fun β hβ => hβ.1) hroot hneg hsq hperpst
    rw [hperp6] at h4
    omega
  · have hsub : ρ '' componentRoots (rootCharHom a) i ⊆ {β : Fin Tag.E8.rank → ℤ |
        IsRoot Tag.E8 β ∧ ∀ α ∈ componentRoots (rootCharHom a) i, iform β α = 0} := by
      rintro _ ⟨α, hα, rfl⟩
      refine ⟨(hroot α).2 (hΨroot α hα), fun α' hα' => ?_⟩
      have h0 := rck_iform_eq_zero_of_not_mem hα' (hstab α hα.1) (hdis α hα)
      rw [iform_comm]
      exact h0
    have hle := Set.ncard_le_ncard hsub hfinPerp
    rw [Set.ncard_image_of_injective _ ρ.injective, hc, hperp6] at hle
    omega

end CFSG.StandardType.RCKRP
