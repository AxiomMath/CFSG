module

public import CFSG.RankThree.PartOne.KF4.StrNative
public import CFSG.RankThree.PartOne.KE.E7A2Native

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
open scoped Pointwise

variable {τ : Tag} {n : ℕ} {J : Set (Fin τ.rank)} {w : Fin n → Fin τ.rank → ℤ}

structure StrNativeBruhat (D : StrNativeData τ n J w) (k₀ : Fin n) : Prop where
  precedes : ∀ i j : Fin n, (D.label i).Precedes (D.label j) ↔ i < j
  outside : ∀ k : Fin n, ∀ i, i ∉ J → w k i = w k₀ i
  perm_closed : ∀ β : Fin τ.rank → ℤ, IsRoot τ β → (∀ i, i ∉ J → β i = w k₀ i) →
    ∃ k, w k = β
  single_eq_sub : ∀ i ∈ J, ∃ k l : Fin n, (Pi.single i 1 : Fin τ.rank → ℤ) = w k - w l

namespace StrNativeBruhat

variable {D : StrNativeData τ n J w} {k₀ : Fin n} (B : StrNativeBruhat D k₀)

include B in
theorem exists_weight_smul {x : WeylGroup τ} (hx : x ∈ parabolicWeylGroup τ J) (k : Fin n) :
    ∃ k', w k' = x • w k := by
  refine B.perm_closed _ (IsRoot.smul (D.isRoot k) x) (fun i hi => ?_)
  rw [smul_apply_of_mem_parabolicWeylGroup hx _ hi, B.outside k i hi]

include B in
theorem smul_weight_eq_of_not_lt {x : WeylGroup τ} (hx : x ∈ parabolicWeylGroup τ J)
    (hprec : ∀ j j' : Fin n, w j' = x • w j → ¬j < j') (j : Fin n) : x • w j = w j := by
  by_contra hj
  classical
  set M : Finset (Fin n) := Finset.univ.filter fun k => x • w k ≠ w k
  have hM : M.Nonempty := ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩⟩
  obtain ⟨k, hkM, hmin⟩ := M.exists_min_image id hM
  have hk : x • w k ≠ w k := (Finset.mem_filter.mp hkM).2
  obtain ⟨k', hk'⟩ := B.exists_weight_smul hx k
  have hne : k' ≠ k := fun h => hk (by rw [← hk', h])
  have hlt : k' < k := lt_of_le_of_ne (not_lt.1 (hprec k k' hk')) hne
  have hk'M : k' ∈ M := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun h => hne ?_⟩
    apply D.injective
    apply smul_left_cancel x
    rw [h]
    exact hk'
  exact absurd (hmin k' hk'M) (not_le.mpr hlt)

include B in
theorem eq_one_of_smul_weight
    {x : WeylGroup τ} (hx : x ∈ parabolicWeylGroup τ J)
    (h : ∀ k, x • w k = w k) : x = 1 := by
  refine eq_one_of_forall_height_pos fun i => ?_
  by_cases hi : i ∈ J
  · obtain ⟨k, l, hkl⟩ := B.single_eq_sub i hi
    have hfix : x • (Pi.single i 1 : Fin τ.rank → ℤ) = Pi.single i 1 := by
      rw [hkl, smul_sub, h, h]
    rw [hfix, height_single]
    exact one_pos
  · have hroot := IsRoot.smul (isRoot_single τ i) x
    have hcoord : (x • (Pi.single i 1 : Fin τ.rank → ℤ)) i = 1 := by
      rw [smul_apply_of_mem_parabolicWeylGroup hx _ hi, Pi.single_eq_same]
    refine (IsRoot.height_pos_iff hroot).2 ?_
    rcases hroot.nonneg_or_nonpos with hs | hs
    · exact hs
    · have := hs i
      omega

section Triangular

variable {K : Type} [Field K]

include B in
theorem borel_apply_vec_eq_zero {c : ModGL τ K} (hc : c ∈ borelGroup τ K) {j j' : Fin n}
    (h : j < j') :
    (c : Module.End K (RootModule τ K)) (D.vec K j) (D.label j') = 0 :=
  (triangular_borel_structure.{0, 0} τ K).2.2.2.2.2.2.2.2.2.1 c hc (D.label j') (D.label j)
    ((B.precedes j j').2 h)

end Triangular

section Bruhat

variable
  {K : Type} [Field K]

include B in
theorem Mat_eq_one
    (hrec : ∀ t ∈ subsystemTorus τ K J, ∀ u ∈ parabolicLeviUnipotent τ K J,
      D.Mat (t * u) = 1 → t = 1 ∧ u = 1)
    {g : ModGL τ K} (hg : g ∈ subsystemGroup τ K J) (hmat : D.Mat g = 1) : g = 1 := by
  have hfixv : ∀ k, (g : Module.End K (RootModule τ K)) (D.vec K k) = D.vec K k := by
    intro k
    rw [D.apply_vec hg, hmat]
    simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true]
  have hfix : ∀ m ∈ D.module K, (g : Module.End K (RootModule τ K)) m = m := by
    intro m hm
    have e := D.eq_sum_of_mem_module hm
    calc (g : Module.End K (RootModule τ K)) m =
        (g : Module.End K (RootModule τ K)) (∑ k, m (D.label k) • D.vec K k) := by rw [← e]
      _ = ∑ k, m (D.label k) • D.vec K k := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun k _ => by rw [map_smul, hfixv]
      _ = m := e.symm
  have hgS : g ∈ (subsystemGroup τ K J : Set (ModGL τ K)) := hg
  rw [(subsystem_root_group_bruhat (τ := τ) (K := K) (A := J)).2.2.1] at hgS
  simp only [Set.mem_iUnion] at hgS
  obtain ⟨w', hw, hgw⟩ := hgS
  obtain ⟨_, ⟨b, hb, _, rfl, rfl⟩, v, hv, hgbv⟩ := hgw
  beta_reduce at hgbv
  have hbB : b ∈ borelGroup τ K := subsystemBorel_le_borelGroup hb
  have hvU : v ∈ posUnipotent τ K :=
    rootSpan_le_posUnipotent (fun _ h => inversionSet_pos h) hv
  have hvB : v ∈ borelGroup τ K := Subgroup.mem_sup_right hvU
  have hvS : v ∈ subsystemGroup τ K J :=
    parabolicLeviUnipotent_le_subsystemGroup (τ := τ) (K := K) (A := J)
      (rootSpan_mono (inversionSet_subset_parabolicPosRoots hw) hv)
  have hn : ∀ j, (canonicalRep (coxeterSystem τ) K w' : Module.End K (RootModule τ K))
      (D.vec K j) = ((b⁻¹ * v⁻¹ : ModGL τ K) : Module.End K (RootModule τ K)) (D.vec K j) := by
    intro j
    have hn' : canonicalRep (coxeterSystem τ) K w' = b⁻¹ * (g : ModGL τ K) * v⁻¹ := by
      rw [← hgbv]
      group
    rw [hn', Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
      hfix _ (D.mem_module_of_mem (inv_mem hvS) (D.vec_mem j)), Units.val_mul,
      Module.End.mul_apply]
  have hprec : ∀ j j' : Fin n, w j' = w' • w j → ¬j < j' := by
    intro j j' hj' hlt
    obtain ⟨ε, hε, hne⟩ := KE.canonicalRep_rootVec_of_isRoot (K := K) w' (D.isRoot j)
    have h0 := B.borel_apply_vec_eq_zero (mul_mem (inv_mem hbB) (inv_mem hvB)) hlt
    rw [← hn j, ← D.rootVec_w K j, hne, ← hj', D.rootVec_w K j', Finsupp.smul_apply, D.vec_apply,
      ite_eq_left rfl, smul_eq_mul, mul_one] at h0
    exact hε h0
  have hw1 : w' = 1 := B.eq_one_of_smul_weight hw (B.smul_weight_eq_of_not_lt hw hprec)
  subst hw1
  have hv1 : v = 1 := by
    rw [inversionSet_one, show rootSpan τ K (∅ : Set (Fin τ.rank → ℤ)) = ⊥ by
      simp [rootSpan]] at hv
    exact hv
  rw [canonicalRep_one, hv1, mul_one, mul_one] at hgbv
  have hb' : b ∈ (subsystemTorus τ K J : Set (ModGL τ K)) *
      (parabolicLeviUnipotent τ K J : Set (ModGL τ K)) :=
    (Set.ext_iff.mp (coe_subsystemBorel (τ := τ) (K := K) (A := J)) b).mp hb
  obtain ⟨t, ht, u, hu, rfl⟩ := hb'
  beta_reduce at hgbv
  have h1 := hrec t ht u hu (by rw [hgbv]; exact hmat)
  rw [← hgbv, h1.1, h1.2, mul_one]

end Bruhat

end StrNativeBruhat

end CFSG.RankThree.PartOne.KF4
