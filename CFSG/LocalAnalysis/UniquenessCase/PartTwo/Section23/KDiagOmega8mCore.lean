module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagOmega8m
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KDiagOmega8mArith
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNonsolv3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
public import CFSG.Monster.B.Fischer.Fi22Order

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
open QuadraticMap Module
open scoped Pointwise

variable {K : Type} [Field K] [Finite K] {b c : K} {a₀ : Fin 2 → K}

abbrev omegaTailU (K : Type) [Field K] (b c : K) : Subgroup (omegaTailE K b c) :=
  (tailUnipotent 3 (minusTailForm K b c)).subgroupOf (omegaTailE K b c)

theorem omegaTailU_isPGroup [CharP K 2] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsPGroup 2 (omegaTailU K b c) := by
  have hani : (minusTailForm K b c).Anisotropic := anisotropic_minusTailForm hirr
  simpa [omegaTailU, omegaTailE, omegaTailQ] using
    (isPGroup_tailUnipotent (p := 2) (r := 3) (qA := minusTailForm K b c) hani)

theorem omegaTailU_not_dvd_index [CharP K 2] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ¬ 2 ∣ (omegaTailU K b c).index := by
  have hani : (minusTailForm K b c).Anisotropic := anisotropic_minusTailForm hirr
  have hreg : (polarBilin (minusTailForm K b c)).Nondegenerate :=
    nondegenerate_minusTailForm hirr
  have hm : finrank K (Fin 2 → K) = 1 ∨ finrank K (Fin 2 → K) = 2 := by
    right
    simp
  simpa [omegaTailU, omegaTailE, omegaTailQ] using
    (not_dvd_index_tailUnipotent (p := 2) (r := 3) (qA := minusTailForm K b c)
      (by norm_num) hani hreg hm)

def omegaTailSylow [CharP K 2] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Sylow 2 (omegaTailE K b c) :=
  (omegaTailU_isPGroup (b := b) (c := c) hirr).toSylow
    (omegaTailU_not_dvd_index (b := b) (c := c) hirr)

@[simp]
theorem omegaTailSylow_coe [CharP K 2] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (omegaTailSylow (K := K) (b := b) (c := c) hirr : Subgroup (omegaTailE K b c)) =
      omegaTailU K b c := by
  rw [omegaTailSylow, IsPGroup.toSylow_coe]

theorem omegaTail_normalizer_U (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Subgroup.normalizer ((omegaTailU K b c : Subgroup (omegaTailE K b c)) :
        Set (omegaTailE K b c)) =
      (omegaTailBorel K b c).subgroupOf (omegaTailE K b c) := by
  have hani : (minusTailForm K b c).Anisotropic := anisotropic_minusTailForm hirr
  have hA : ∃ a : Fin 2 → K, a ≠ 0 :=
    ⟨fun _ => 1, by intro h; simpa using congrFun h 0⟩
  simpa [omegaTailU, omegaTailBorel, omegaTailE, omegaTailQ] using
    (normalizer_tailUnipotent (r := 3) (qA := minusTailForm K b c) hani hA)

theorem omegaTailParabolic_eq_stabilizer (i : Fin 3) :
    omegaTailParabolic (K := K) b c i =
      MulAction.stabilizer (omegaTailE K b c) (omegaTailFlag (K := K) i) := by
  rw [omegaTailParabolic, MulAction.stabilizer_subgroupOf]

theorem omegaTail_borel_le_parabolic (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin 3) :
    (omegaTailBorel K b c).subgroupOf (omegaTailE K b c) ≤
      omegaTailParabolic (K := K) b c i := by
  intro x hx
  have hx' : (x : omegaTailV K ≃ₗ[K] omegaTailV K) ∈ tailBorel 3 (minusTailForm K b c) := hx
  have hmem := (mem_tailBorel.1 hx').2 (i + 1) (by omega) (by have := i.isLt; omega)
  rw [omegaTailParabolic_eq_stabilizer, MulAction.mem_stabilizer_iff, MulAction.subgroup_smul_def]
  change Submodule.map ((x : omegaTailV K ≃ₗ[K] omegaTailV K) : omegaTailV K →ₗ[K] omegaTailV K)
    (omegaTailFlag (K := K) i) = omegaTailFlag (K := K) i
  simpa [omegaTailFlag, omegaTailV, omegaTailQ] using hmem


def omegaTailMissing (M : Subgroup (omegaTailE K b c)) : Set (Fin 3) :=
  {i | omegaTailN (K := K) b c a₀ i ∉ M}

theorem omegaTail_overgroup_eq_iInf' (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (ha₀ : a₀ ≠ 0)
    {M : Subgroup (omegaTailE K b c)}
    (hB : (omegaTailBorel K b c).subgroupOf (omegaTailE K b c) ≤ M) :
    M = ⨅ i ∈ omegaTailMissing (K := K) (b := b) (c := c) (a₀ := a₀) M,
      omegaTailParabolic (K := K) b c i :=
  omegaTail_overgroup_eq_iInf (K := K) b c hirr a₀ ha₀ M hB

section Overgroups



theorem omegaTail_le_parabolic_iff (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (ha₀ : a₀ ≠ 0)
    {M : Subgroup (omegaTailE K b c)}
    (hB : (omegaTailBorel K b c).subgroupOf (omegaTailE K b c) ≤ M) (i : Fin 3) :
    M ≤ omegaTailParabolic (K := K) b c i ↔ omegaTailN (K := K) b c a₀ i ∉ M := by
  constructor
  · intro hle hni
    exact (omegaTail_weylElt_mem_parabolic (K := K) b c hirr a₀ ha₀ i i).1
      (hle hni) rfl
  · intro hni
    have hM := omegaTail_overgroup_eq_iInf' (K := K) hirr ha₀ hB
    rw [hM]
    exact iInf₂_le_of_le i hni le_rfl

theorem omegaTail_iInf_le_iff (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (ha₀ : a₀ ≠ 0)
    (J J' : Set (Fin 3)) :
    (⨅ i ∈ J, omegaTailParabolic (K := K) b c i) ≤
      (⨅ i ∈ J', omegaTailParabolic (K := K) b c i) ↔ J' ⊆ J := by
  constructor
  · intro hle i hi
    by_contra hiJ
    have hniJ : omegaTailN (K := K) b c a₀ i ∈
        ⨅ i ∈ J, omegaTailParabolic (K := K) b c i := by
      refine Subgroup.mem_iInf.2 fun j => Subgroup.mem_iInf.2 fun hj => ?_
      exact (omegaTail_weylElt_mem_parabolic (K := K) b c hirr a₀ ha₀ j i).2
        (fun h => hiJ (h ▸ hj))
    have hniJ' : omegaTailN (K := K) b c a₀ i ∈
        ⨅ i ∈ J', omegaTailParabolic (K := K) b c i := hle hniJ
    have hPi : omegaTailN (K := K) b c a₀ i ∈ omegaTailParabolic (K := K) b c i :=
      Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hniJ' i) hi
    exact (omegaTail_weylElt_mem_parabolic (K := K) b c hirr a₀ ha₀ i i).1 hPi rfl
  · intro hJ
    refine le_iInf₂ fun i hi => ?_
    exact iInf₂_le_of_le i (hJ hi) le_rfl

theorem omegaTail_iInf_ne_top (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (ha₀ : a₀ ≠ 0)
    {J : Set (Fin 3)} (hJ : J.Nonempty) :
    (⨅ i ∈ J, omegaTailParabolic (K := K) b c i) ≠ ⊤ := by
  obtain ⟨k, hk⟩ := hJ
  intro htop
  have hmem : omegaTailN (K := K) b c a₀ k ∈
      ⨅ i ∈ J, omegaTailParabolic (K := K) b c i := by
    rw [htop]
    exact Subgroup.mem_top _
  have hPk : omegaTailN (K := K) b c a₀ k ∈ omegaTailParabolic (K := K) b c k :=
    Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hmem k) hk
  exact (omegaTail_weylElt_mem_parabolic (K := K) b c hirr a₀ ha₀ k k).1 hPk rfl

theorem omegaTail_exists_missing (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (ha₀ : a₀ ≠ 0)
    {M : Subgroup (omegaTailE K b c)}
    (hB : (omegaTailBorel K b c).subgroupOf (omegaTailE K b c) ≤ M) (hM : M ≠ ⊤) :
    ∃ i : Fin 3, omegaTailN (K := K) b c a₀ i ∉ M := by
  by_contra h
  push Not at h
  apply hM
  have hJ : {i : Fin 3 | omegaTailN (K := K) b c a₀ i ∉ M} = ∅ := by
    ext i
    simp [h i]
  rw [omegaTail_overgroup_eq_iInf (K := K) b c hirr a₀ ha₀ M hB, hJ]
  simp

theorem omegaTail_parabolic_maximal (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (ha₀ : a₀ ≠ 0)
    (i : Fin 3) :
    ∀ M' : Subgroup (omegaTailE K b c),
      (omegaTailBorel K b c).subgroupOf (omegaTailE K b c) ≤ M' →
      omegaTailParabolic (K := K) b c i ≤ M' →
      M' = omegaTailParabolic (K := K) b c i ∨ M' = ⊤ := by
  intro M' hB' hle
  have hMeq := omegaTail_overgroup_eq_iInf' (K := K) hirr ha₀ hB'
  have hle' : (⨅ k ∈ ({i} : Set (Fin 3)), omegaTailParabolic (K := K) b c k) ≤
      ⨅ k ∈ omegaTailMissing (K := K) (b := b) (c := c) (a₀ := a₀) M',
        omegaTailParabolic (K := K) b c k := by
    calc (⨅ k ∈ ({i} : Set (Fin 3)), omegaTailParabolic (K := K) b c k)
        ≤ omegaTailParabolic (K := K) b c i := iInf₂_le_of_le i rfl le_rfl
      _ ≤ M' := hle
      _ = ⨅ k ∈ omegaTailMissing (K := K) (b := b) (c := c) (a₀ := a₀) M',
          omegaTailParabolic (K := K) b c k := hMeq
  have hsub : omegaTailMissing (K := K) (b := b) (c := c) (a₀ := a₀) M' ⊆ {i} := by
    have hiff := omegaTail_iInf_le_iff (K := K) (b := b) (c := c) (a₀ := a₀) hirr ha₀
      ({i} : Set (Fin 3)) (omegaTailMissing (K := K) (b := b) (c := c) (a₀ := a₀) M')
    exact hiff.1 hle'
  rcases Set.subset_singleton_iff_eq.1 hsub with h | h
  · right
    calc M' = ⨅ k ∈ omegaTailMissing (K := K) (b := b) (c := c) (a₀ := a₀) M',
          omegaTailParabolic (K := K) b c k := hMeq
      _ = ⨅ k ∈ (∅ : Set (Fin 3)), omegaTailParabolic (K := K) b c k := by rw [h]
      _ = ⊤ := top_unique (le_iInf₂ fun k hk => absurd hk ((Set.mem_empty_iff_false k).1))
  · left
    calc M' = ⨅ k ∈ omegaTailMissing (K := K) (b := b) (c := c) (a₀ := a₀) M',
          omegaTailParabolic (K := K) b c k := hMeq
      _ = ⨅ k ∈ ({i} : Set (Fin 3)), omegaTailParabolic (K := K) b c k := by rw [h]
      _ = omegaTailParabolic (K := K) b c i := by
        apply le_antisymm
        · exact iInf₂_le_of_le i rfl le_rfl
        · refine le_iInf₂ ?_
          intro k hk
          rw [Set.mem_singleton_iff] at hk
          subst hk
          exact le_rfl

theorem omegaTail_iInf_singleton (i : Fin 3) :
    (⨅ k ∈ ({i} : Set (Fin 3)), omegaTailParabolic (K := K) b c k) =
      omegaTailParabolic (K := K) b c i := by
  apply le_antisymm
  · exact iInf₂_le_of_le i rfl le_rfl
  · refine le_iInf₂ ?_
    intro k hk
    rw [Set.mem_singleton_iff] at hk
    subst hk
    exact le_rfl

theorem omegaTail_exists_parabolic_of_maximal (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (ha₀ : a₀ ≠ 0) {M : Subgroup (omegaTailE K b c)}
    (hB : (omegaTailBorel K b c).subgroupOf (omegaTailE K b c) ≤ M) (hM : M ≠ ⊤)
    (hmax : ∀ M' : Subgroup (omegaTailE K b c),
      (omegaTailBorel K b c).subgroupOf (omegaTailE K b c) ≤ M' →
      M ≤ M' → M' = M ∨ M' = ⊤) :
    ∃ i : Fin 3, M = omegaTailParabolic (K := K) b c i := by
  have hMeq := omegaTail_overgroup_eq_iInf' (K := K) hirr ha₀ hB
  obtain ⟨i, hi⟩ := omegaTail_exists_missing (K := K) (a₀ := a₀) hirr ha₀ hB hM
  refine ⟨i, ?_⟩
  have hsingle : omegaTailMissing (K := K) (b := b) (c := c) (a₀ := a₀) M = {i} := by
    refine Set.Subset.antisymm ?_ ?_
    · intro j hj
      by_contra hji
      set J : Set (Fin 3) := omegaTailMissing (K := K) (b := b) (c := c) (a₀ := a₀) M with hJ
      set J' : Set (Fin 3) := J \ {j} with hJ'
      have hJ'sub : J' ⊆ J := Set.diff_subset
      have hJ'ne : J'.Nonempty :=
        ⟨i, Set.mem_diff _ |>.2 ⟨hi, by simpa using fun h => hji h.symm⟩⟩
      have hle : M ≤ ⨅ k ∈ J', omegaTailParabolic (K := K) b c k := by
        calc M = ⨅ k ∈ J, omegaTailParabolic (K := K) b c k := hMeq
          _ ≤ ⨅ k ∈ J', omegaTailParabolic (K := K) b c k :=
            (omegaTail_iInf_le_iff (K := K) (a₀ := a₀) hirr ha₀ J J').2 hJ'sub
      have hlt : (⨅ k ∈ J', omegaTailParabolic (K := K) b c k) ≠ M := by
        intro heq
        have hsub : J ⊆ J' :=
          (omegaTail_iInf_le_iff (K := K) (a₀ := a₀) hirr ha₀ J' J).1 (by rw [heq, hMeq])
        exact (Set.mem_diff j).1 (hsub hj) |>.2 (by simp)
      have htop : (⨅ k ∈ J', omegaTailParabolic (K := K) b c k) = ⊤ := by
        rcases hmax _ (le_iInf₂ fun k _ => omegaTail_borel_le_parabolic (K := K) hirr k) hle
          with h | h
        · exact absurd h hlt
        · exact h
      exact omegaTail_iInf_ne_top (K := K) (a₀ := a₀) hirr ha₀ hJ'ne htop
    · intro k hk
      rw [Set.mem_singleton_iff] at hk
      subst hk
      exact hi
  calc M = ⨅ k ∈ omegaTailMissing (K := K) (b := b) (c := c) (a₀ := a₀) M,
        omegaTailParabolic (K := K) b c k := hMeq
    _ = ⨅ k ∈ ({i} : Set (Fin 3)), omegaTailParabolic (K := K) b c k := by rw [hsingle]
    _ = omegaTailParabolic (K := K) b c i := omegaTail_iInf_singleton (K := K) i

end Overgroups


section IndexAndMain

theorem omegaTail_parabolic_index (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (i : Fin 3) :
    ((omegaTailParabolic (K := K) b c i).index : ℚ) =
      tailCount (Nat.card K : ℚ) 3 2 (i.val + 1) := by
  have hani : (minusTailForm K b c).Anisotropic := anisotropic_minusTailForm hirr
  have hreg : (polarBilin (minusTailForm K b c)).Nondegenerate :=
    nondegenerate_minusTailForm hirr
  have hA : ∃ a : Fin 2 → K, a ≠ 0 :=
    ⟨fun _ => 1, by intro h; simpa using congrFun h 0⟩
  have hk : i.val + 1 ≤ 3 := by have := i.isLt; omega
  have hW : omegaTailFlag (K := K) i ∈ singularSubspaces (omegaTailQ K b c) (i.val + 1) := by
    refine ⟨?_, ?_⟩
    · show finrank K (tailFlag K (Fin 2 → K) (4 - 1) (i.val + 1)) = i.val + 1
      exact finrank_tailFlag hk
    · intro x hx
      exact quadTail_eq_zero_of_mem_tailFlag hx
  have hidx : (omegaTailParabolic (K := K) b c i).index =
      Nat.card (singularSubspaces (omegaTailQ K b c) (i.val + 1)) := by
    show (MulAction.stabilizer (omegaTailE K b c) (omegaTailFlag (K := K) i)).index =
      Nat.card (singularSubspaces (quadTail 3 (minusTailForm K b c)) (i.val + 1))
    exact index_stabilizer_eq_card hani hA hk hW
  rw [hidx]
  push_cast
  rw [card_singularSubspaces_tail (A := Fin 2 → K) (qA := minusTailForm K b c) (r := 3) hani hreg hk]
  simp [tailCount]

theorem omegaTail_map_eq_of_normalizer (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (ha₀ : a₀ ≠ 0)
    {θ : MulAut (omegaTailE K b c)}
    (hBmap : ((omegaTailBorel K b c).subgroupOf (omegaTailE K b c)).map θ.toMonoidHom =
      (omegaTailBorel K b c).subgroupOf (omegaTailE K b c)) :
    ∀ M : Subgroup (omegaTailE K b c),
      (omegaTailBorel K b c).subgroupOf (omegaTailE K b c) ≤ M →
      M.map θ.toMonoidHom = M := by
  intro M hBM
  have hcomp_symm : θ.symm.toMonoidHom.comp θ.toMonoidHom = MonoidHom.id _ :=
    MonoidHom.ext fun y => θ.symm_apply_apply y
  have hcomp_theta : θ.toMonoidHom.comp θ.symm.toMonoidHom = MonoidHom.id _ :=
    MonoidHom.ext fun y => θ.apply_symm_apply y
  have hfix : ∀ i : Fin 3,
      (omegaTailParabolic (K := K) b c i).map θ.toMonoidHom =
        omegaTailParabolic (K := K) b c i := by
    intro i
    have hBθ : (omegaTailBorel K b c).subgroupOf (omegaTailE K b c) ≤
        (omegaTailParabolic (K := K) b c i).map θ.toMonoidHom := by
      rw [← hBmap]
      exact Subgroup.map_mono (omegaTail_borel_le_parabolic (K := K) hirr i)
    have hne : (omegaTailParabolic (K := K) b c i).map θ.toMonoidHom ≠ ⊤ := by
      intro htop
      have hPi : omegaTailParabolic (K := K) b c i = ⊤ := by
        have := congrArg (Subgroup.map θ.symm.toMonoidHom) htop
        rwa [Subgroup.map_map, hcomp_symm, Subgroup.map_id,
          Subgroup.map_top_of_surjective _ θ.symm.surjective] at this
      have hni : omegaTailN (K := K) b c a₀ i ∈ omegaTailParabolic (K := K) b c i := by
        rw [hPi]; exact Subgroup.mem_top _
      exact (omegaTail_weylElt_mem_parabolic (K := K) b c hirr a₀ ha₀ i i).1 hni rfl
    have hmax : ∀ M' : Subgroup (omegaTailE K b c),
        (omegaTailBorel K b c).subgroupOf (omegaTailE K b c) ≤ M' →
        (omegaTailParabolic (K := K) b c i).map θ.toMonoidHom ≤ M' → M' =
          (omegaTailParabolic (K := K) b c i).map θ.toMonoidHom ∨ M' = ⊤ := by
      intro M' hB' hle'
      have hle : omegaTailParabolic (K := K) b c i ≤ M'.map θ.symm.toMonoidHom := by
        have h := Subgroup.map_mono (f := θ.symm.toMonoidHom) hle'
        rwa [Subgroup.map_map, hcomp_symm, Subgroup.map_id] at h
      have hB'' : (omegaTailBorel K b c).subgroupOf (omegaTailE K b c) ≤
          M'.map θ.symm.toMonoidHom := by
        have h := Subgroup.map_mono (f := θ.symm.toMonoidHom) hB'
        rw [← hBmap, Subgroup.map_map, hcomp_symm, Subgroup.map_id] at h
        exact h
      rcases omegaTail_parabolic_maximal (K := K) (a₀ := a₀) hirr ha₀ i _
        hB'' hle with h | h
      · left
        have h' := congrArg (Subgroup.map θ.toMonoidHom) h
        rwa [Subgroup.map_map, hcomp_theta, Subgroup.map_id] at h'
      · right
        have h' := congrArg (Subgroup.map θ.toMonoidHom) h
        rwa [Subgroup.map_map, hcomp_theta, Subgroup.map_id,
          Subgroup.map_top_of_surjective _ θ.surjective] at h'
    obtain ⟨j, hj⟩ := omegaTail_exists_parabolic_of_maximal (K := K) (a₀ := a₀) hirr ha₀
      hBθ hne hmax
    have hq : 2 ≤ Nat.card K := by have := Finite.one_lt_card (α := K); omega
    have hidxeq : ((omegaTailParabolic (K := K) b c i).index : ℚ) =
        ((omegaTailParabolic (K := K) b c j).index : ℚ) := by
      have h : (omegaTailParabolic (K := K) b c j).index =
          (omegaTailParabolic (K := K) b c i).index := by
        rw [← hj]
        exact Subgroup.index_map_equiv (omegaTailParabolic (K := K) b c i)
          (θ : omegaTailE K b c ≃* omegaTailE K b c)
      rw [h]
    rw [omegaTail_parabolic_index (K := K) hirr i,
      omegaTail_parabolic_index (K := K) hirr j] at hidxeq
    have hpair := tailCount_three_two_pairwise (Nat.card K) hq
    have hval : i.val + 1 = j.val + 1 := by
      have hi3 : i.val < 3 := i.isLt
      have hj3 : j.val < 3 := j.isLt
      interval_cases i.val <;> interval_cases j.val <;> simp_all
    have hij : i = j := Fin.ext (by omega)
    rw [hj, hij]
  have hBθM : (omegaTailBorel K b c).subgroupOf (omegaTailE K b c) ≤
      M.map θ.toMonoidHom := by
    rw [← hBmap]
    exact Subgroup.map_mono hBM
  have hmissing : omegaTailMissing (K := K) (b := b) (c := c) (a₀ := a₀)
      (M.map θ.toMonoidHom) = omegaTailMissing (K := K) (b := b) (c := c) (a₀ := a₀) M := by
    ext i
    have hiff1 := omegaTail_le_parabolic_iff (K := K) (a₀ := a₀) hirr ha₀ hBθM i
    have hiff2 := omegaTail_le_parabolic_iff (K := K) (a₀ := a₀) hirr ha₀ hBM i
    have hleiff : M.map θ.toMonoidHom ≤ omegaTailParabolic (K := K) b c i ↔
        M ≤ omegaTailParabolic (K := K) b c i := by
      have h := (MulEquiv.mapSubgroup θ).map_rel_iff (a := M)
        (b := omegaTailParabolic (K := K) b c i)
      simpa only [MulEquiv.coe_mapSubgroup, hfix i] using h
    simp only [omegaTailMissing, Set.mem_setOf_eq]
    rw [← hiff1, ← hiff2, hleiff]
  calc M.map θ.toMonoidHom
      = ⨅ i ∈ omegaTailMissing (K := K) (b := b) (c := c) (a₀ := a₀) (M.map θ.toMonoidHom),
          omegaTailParabolic (K := K) b c i :=
        omegaTail_overgroup_eq_iInf' (K := K) hirr ha₀ hBθM
    _ = ⨅ i ∈ omegaTailMissing (K := K) (b := b) (c := c) (a₀ := a₀) M,
          omegaTailParabolic (K := K) b c i := by rw [hmissing]
    _ = M := (omegaTail_overgroup_eq_iInf' (K := K) hirr ha₀ hBM).symm


theorem kDiag_omegaTail [CharP K 2] (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∀ (θ : MulAut (omegaTailE K b c)),
    ∀ S : Sylow 2 (omegaTailE K b c),
      (∀ x ∈ (S : Subgroup (omegaTailE K b c)),
        θ x ∈ (S : Subgroup (omegaTailE K b c))) →
    ∀ P : Subgroup (omegaTailE K b c), IsParabolicTwo (omegaTailE K b c) P →
      (S : Subgroup (omegaTailE K b c)) ≤
        Subgroup.normalizer (P : Set (omegaTailE K b c)) →
      ∀ x ∈ P, θ x ∈ P := by
  intro θ S hSθ P hPpar hSP x hx
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSP' : (S : Subgroup (omegaTailE K b c)) ≤ P :=
    hPpar.le_of_le_normalizer S.isPGroup' hSP
  have hNSP : Subgroup.normalizer ((S : Subgroup (omegaTailE K b c)) :
      Set (omegaTailE K b c)) ≤ P := hPpar.normalizer_le S hSP'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (omegaTailE K b c)
    (omegaTailSylow (K := K) (b := b) (c := c) hirr) S
  have hScoe : (S : Subgroup (omegaTailE K b c)) =
      (omegaTailU K b c).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, omegaTailSylow_coe]
    rfl
  let e : omegaTailE K b c ≃* omegaTailE K b c := MulAut.conj g
  let θ' : MulAut (omegaTailE K b c) := MulAut.congr e.symm θ
  have hcomp_symm : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ :=
    MonoidHom.ext fun y => e.symm_apply_apply y
  have hcomp_theta : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ :=
    MonoidHom.ext fun y => e.apply_symm_apply y
  have hcomp'' : θ'.toMonoidHom =
      e.symm.toMonoidHom.comp (θ.toMonoidHom.comp e.toMonoidHom) := by
    refine MonoidHom.ext fun y => ?_
    change (MulAut.congr e.symm θ) y = e.symm (θ (e y))
    rw [MulAut.congr_apply]
    rfl
  have hSmap : (S : Subgroup (omegaTailE K b c)).map θ.toMonoidHom = S := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hSθ y hy
    · rw [Subgroup.card_map_of_injective θ.injective]
  have heU : (omegaTailU K b c).map e.toMonoidHom = (S : Subgroup (omegaTailE K b c)) := by
    rw [hScoe]
  have heS : (S : Subgroup (omegaTailE K b c)).map e.symm.toMonoidHom = omegaTailU K b c := by
    rw [← heU, Subgroup.map_map, hcomp_symm, Subgroup.map_id]
  have hθ'U : (omegaTailU K b c).map θ'.toMonoidHom = omegaTailU K b c := by
    rw [hcomp'', ← Subgroup.map_map, ← Subgroup.map_map, heU, hSmap, heS]
  have hBmap : ((omegaTailBorel K b c).subgroupOf (omegaTailE K b c)).map θ'.toMonoidHom =
      (omegaTailBorel K b c).subgroupOf (omegaTailE K b c) := by
    rw [← omegaTail_normalizer_U (K := K) (b := b) (c := c) hirr,
      Subgroup.map_equiv_normalizer_eq, hθ'U]
  have hB' : (omegaTailBorel K b c).subgroupOf (omegaTailE K b c) ≤
      P.map e.symm.toMonoidHom := by
    have h := Subgroup.map_mono (f := e.symm.toMonoidHom) hNSP
    rw [Subgroup.map_equiv_normalizer_eq (S : Subgroup (omegaTailE K b c)) e.symm, heS,
      omegaTail_normalizer_U (K := K) (b := b) (c := c) hirr] at h
    exact h
  have ha₀ : (fun _ : Fin 2 => (1 : K)) ≠ 0 := by
    intro h
    simpa using congrFun h 0
  have hfixP : (P.map e.symm.toMonoidHom).map θ'.toMonoidHom = P.map e.symm.toMonoidHom :=
    omegaTail_map_eq_of_normalizer (K := K) (b := b) (c := c)
      (a₀ := fun _ : Fin 2 => (1 : K)) hirr ha₀ hBmap _ hB'
  have hcongr : ∀ Q : Subgroup (omegaTailE K b c),
      (Q.map e.symm.toMonoidHom).map θ'.toMonoidHom =
        (Q.map θ.toMonoidHom).map e.symm.toMonoidHom := by
    intro Q
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun y => ?_
    show e.symm (θ (e (e.symm y))) = e.symm (θ y)
    rw [e.apply_symm_apply]
  have hPmap : P.map θ.toMonoidHom = P := by
    have h1 : (P.map θ.toMonoidHom).map e.symm.toMonoidHom = P.map e.symm.toMonoidHom := by
      rw [← hcongr P, hfixP]
    exact Subgroup.map_injective (f := e.symm.toMonoidHom) e.symm.injective h1
  rw [← hPmap]
  exact Subgroup.mem_map_of_mem θ.toMonoidHom hx

end IndexAndMain

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
