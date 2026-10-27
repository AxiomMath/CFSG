module

public import CFSG.LieType.HighestRoot.CentChevalleyCenter
public import CFSG.LieType.Chevalley.GraphFixedD4TorusWords
public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCore

public section

namespace CFSG.StandardType

namespace LayerExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


variable {τ : Tag} {K : Type} [Field K] {M : Type*} [CommGroup M]
  {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {i : KernelComponent χ}

theorem pinnedX_mem_commutator_of_sq_ne_one {α : Fin τ.rank → ℤ} (hα : α ∈ componentRoots χ i)
    {t : Kˣ} (ht : (t : K) ^ 2 ≠ 1) (c : K) :
    pinnedX τ K α c ∈ ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ := by
  have hαr := isRoot_of_mem_componentRoots hα
  obtain ⟨w, k, hwk⟩ := isRoot_iff_exists_smul_single.1 hαr
  have hh := componentTorus_le_componentRootSpan K χ i
    (canonicalRep_conj_torusElt_mem (K := K) (by rw [hwk]; exact hα) t)
  have hm : ∑ l, τ.cartan k l * (w⁻¹ • α) l = 2 := by
    rw [← corootPair_smul_single, hwk, corootPair]
    exact Int.mul_ediv_cancel _ (iform_self_pos_of_isRoot hαr).ne'
  set h := canonicalRep (coxeterSystem τ) K w * torusElt τ K k t *
    (canonicalRep (coxeterSystem τ) K w)⁻¹ with hh_def
  have hconj : ∀ d, h * pinnedX τ K α d * h⁻¹ = pinnedX τ K α ((t : K) ^ 2 * d) := fun d => by
    rw [hh_def, canonicalRep_conj_torusElt_conj_pinnedX w k t hαr d, hm]
    norm_cast
  have hne : (t : K) ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr ht
  have e : pinnedX τ K α c = h * pinnedX τ K α (c / ((t : K) ^ 2 - 1)) * h⁻¹ *
      (pinnedX τ K α (c / ((t : K) ^ 2 - 1)))⁻¹ := by
    rw [hconj, pinnedX_neg, ← pinnedX_add]
    congr 1
    field_simp
    ring
  rw [e, ← commutatorElement_def]
  exact Subgroup.commutator_mem_commutator hh (pinnedX_mem_rootSpan hα _)

theorem commutator_componentRootSpan_eq {t : Kˣ} (ht : (t : K) ^ 2 ≠ 1) :
    ⁅componentRootSpan K χ i, componentRootSpan K χ i⁆ = componentRootSpan K χ i := by
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  refine iSup₂_le fun α hα => (Subgroup.closure_le _).2 ?_
  rintro _ ⟨c, rfl⟩
  exact pinnedX_mem_commutator_of_sq_ne_one hα ht c

theorem isQuasisimple_componentRootSpan_of_sq_ne_one {t : Kˣ} (ht : (t : K) ^ 2 ≠ 1) :
    CFSG.IsQuasisimple (componentRootSpan K χ i) := by
  have hperf : Group.IsPerfect (componentRootSpan K χ i) :=
    LayerFacts.ggIsPerfect_of_commutator_eq (commutator_componentRootSpan_eq ht)
  obtain ⟨⟨α, hα⟩, rfl⟩ := Quotient.exists_rep i
  have : Nontrivial (componentRootSpan K χ ⟦⟨α, hα⟩⟧) := by
    refine (Subgroup.nontrivial_iff_ne_bot _).2 fun h => ?_
    have h1 : pinnedX τ K α 1 ∈ componentRootSpan K χ ⟦⟨α, hα⟩⟧ :=
      pinnedX_mem_rootSpan (show α ∈ componentRoots χ ⟦⟨α, hα⟩⟧ from ⟨hα, rfl⟩) 1
    rw [h, Subgroup.mem_bot, ← pinnedX_zero τ K α] at h1
    exact one_ne_zero (pinnedX_injective τ K α h1)
  refine CFSG.LieType.TitsSimplicity.isQuasisimple_of_forall hperf fun N hN => ?_
  by_cases hZ : N ≤ Subgroup.center (componentRootSpan K χ ⟦⟨α, hα⟩⟧)
  · exact Or.inl hZ
  · have := hN
    exact Or.inr (CFSG.LieType.TitsSimplicity.eq_top_of_sup_eq_top hperf
      isSolvable_componentBorel_subgroupOf (sup_componentBorel_eq_top hN hZ))

theorem pow_eq_one_of_mem_torusGroup [Finite K] {x : ModGL τ K} (hx : x ∈ torusGroup τ K) :
    x ^ Nat.card Kˣ = 1 := by
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hx
  have h1 : l ^ Nat.card Kˣ = 1 := funext fun j => pow_card_eq_one'
  change (rootDiagUnitHom τ K l) ^ Nat.card Kˣ = 1
  rw [← map_pow, h1, map_one]

theorem eq_one_of_commute_componentRootSpan {m : ℕ} (hm : Odd m)
    (hT : ∀ x ∈ torusGroup τ K, x ^ m = 1) {n : ModGL τ K}
    (hn : n ∈ rootSpan τ K (kernelRoots χ))
    (hc : ∀ i, ∀ s ∈ componentRootSpan K χ i, n * s = s * n) (h2 : n ^ 2 = 1) : n = 1 := by
  classical
  obtain ⟨-, -, -, -, ⟨μ, hμ1, hμs, -⟩, -⟩ :=
    root_character_kernel_orthogonal_central_product τ K χ
  obtain ⟨f, hf⟩ := hμs ⟨n, hn⟩
  have hfc : ∀ i, f i ∈ Subgroup.center (componentRootSpan K χ i) := by
    intro i
    rw [Subgroup.mem_center_iff]
    intro x
    set g := f * (Pi.mulSingle i (f i))⁻¹ with hg_def
    have hg : g * Pi.mulSingle i x = Pi.mulSingle i x * g := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [hg_def]
      · simp [hg_def, Pi.mulSingle_eq_of_ne hj]
    have hfg : f = g * Pi.mulSingle i (f i) := by
      rw [hg_def, inv_mul_cancel_right]
    have e1 : ((μ g : rootSpan τ K (kernelRoots χ)) : ModGL τ K) * x =
        x * ((μ g : rootSpan τ K (kernelRoots χ)) : ModGL τ K) := by
      have h1 := congrArg (fun y => ((μ y : rootSpan τ K (kernelRoots χ)) : ModGL τ K)) hg
      simpa only [map_mul, Subgroup.coe_mul, hμ1] using h1
    have e3 : n = ((μ g : rootSpan τ K (kernelRoots χ)) : ModGL τ K) * (f i : ModGL τ K) := by
      have h1 := congrArg (fun y => ((μ y : rootSpan τ K (kernelRoots χ)) : ModGL τ K)) hfg
      simp only [map_mul, Subgroup.coe_mul, hμ1, hf] at h1
      exact h1
    have e2 : n * x = x * n := hc i x x.2
    rw [e3] at e2
    refine Subtype.ext ?_
    change (x : ModGL τ K) * f i = f i * x
    have e4 : ((μ g : rootSpan τ K (kernelRoots χ)) : ModGL τ K) * (f i * x) =
        ((μ g : rootSpan τ K (kernelRoots χ)) : ModGL τ K) * (x * f i) := by
      calc ((μ g : rootSpan τ K (kernelRoots χ)) : ModGL τ K) * (f i * x) =
            ((μ g : rootSpan τ K (kernelRoots χ)) : ModGL τ K) * f i * x := by group
        _ = x * (((μ g : rootSpan τ K (kernelRoots χ)) : ModGL τ K) * f i) := e2
        _ = ((μ g : rootSpan τ K (kernelRoots χ)) : ModGL τ K) * (x * f i) := by
          rw [← mul_assoc, ← e1, mul_assoc]
    exact (mul_left_cancel e4).symm
  have hfm : f ^ m = 1 := by
    funext i
    refine Subtype.ext ?_
    rw [Pi.pow_apply, Pi.one_apply, Subgroup.coe_pow, Subgroup.coe_one]
    exact hT _ (componentTorus_le_torusGroup K χ i
      (CFSG.LieType.HighestRoot.coe_mem_componentTorus_of_mem_center (hfc i)))
  have hnm : n ^ m = 1 := by
    have h1 := congrArg (fun y => ((μ y : rootSpan τ K (kernelRoots χ)) : ModGL τ K)) hfm
    simpa only [map_pow, map_one, hf, Subgroup.coe_pow, Subgroup.coe_one] using h1
  obtain ⟨k, rfl⟩ := hm
  rw [pow_succ, pow_mul, h2, one_pow, one_mul] at hnm
  exact hnm

end LayerExc

end CFSG.StandardType
