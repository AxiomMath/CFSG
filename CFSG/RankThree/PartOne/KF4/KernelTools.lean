module

public import CFSG.RankThree.PartOne.KE.EDualStabilizer

public noncomputable section

namespace CFSG.RankThree.PartOne.KF4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley RootSpace
open CFSG.RankThree.E6 (charVal charVal_single)
open CFSG.RankThree.PartOne.KE (rootKernel dualWeylStabilizer avgColumn intLift dualVector
  charVal_avgColumn_eq_zero_iff rootReflection_mem_dualWeylStabilizer card_subgroup_ne_zero
  inner_ofLattice_dualVector)

variable {τ : Tag}

theorem inner_root_eq_zero_iff_of_dominant {y : RootSpace τ} (hy : y ∈ dominantCone τ)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    inner ℝ (ofLattice α) y = 0 ↔
      ∀ i, inner ℝ (ofLattice (Pi.single i 1)) y ≠ 0 → α i = 0 := by
  rw [inner_ofLattice_eq_sum]
  have key : ∀ (c : Fin τ.rank → ℤ), (∀ i, 0 ≤ c i) →
      ((∑ i, (c i : ℝ) * inner ℝ (ofLattice (Pi.single i 1)) y) = 0 ↔
        ∀ i, inner ℝ (ofLattice (Pi.single i 1)) y ≠ 0 → c i = 0) := by
    intro c hc
    rw [Finset.sum_eq_zero_iff_of_nonneg fun i _ => mul_nonneg (by exact_mod_cast hc i) (hy i)]
    refine ⟨fun h i hi => ?_, fun h i _ => ?_⟩
    · exact_mod_cast (mul_eq_zero.1 (h i (Finset.mem_univ i))).resolve_right hi
    · by_cases hi : inner ℝ (ofLattice (Pi.single i 1)) y = 0
      · rw [hi, mul_zero]
      · rw [h i hi, Int.cast_zero, zero_mul]
  rcases hα.nonneg_or_nonpos with hs | hs
  · exact key α hs
  · have h := key (-α) fun i => by simp only [Pi.neg_apply]; linarith [hs i]
    simp only [Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, neg_eq_zero,
      neg_eq_zero] at h
    exact h

theorem exists_smul_rootKernel_eq_parabolicRoots {p : ℕ} [Fact p.Prime]
    (hord : ¬p ∣ Nat.card (WeylGroup τ)) (z : Fin τ.rank → ZMod p) :
    ∃ u : WeylGroup τ, ∃ J : Set (Fin τ.rank),
      (u • ·) '' rootKernel z = parabolicRoots τ J ∧ (z ≠ 0 → J ≠ Set.univ) := by
  classical
  have : Fintype (dualWeylStabilizer z) := Fintype.ofFinite _
  set r := avgColumn (dualWeylStabilizer z) (intLift z)
  have hkey : ∀ α, IsRoot τ α → (charVal r α = 0 ↔ α ∈ rootKernel z) := fun α hα =>
    charVal_avgColumn_eq_zero_iff le_rfl (fun _ h => rootReflection_mem_dualWeylStabilizer h)
      (card_subgroup_ne_zero hord _) hα
  obtain ⟨w₁, Y, hY, hy'⟩ := exists_weylAct_mem_dominantCone (dualVector r)
  set u := w₁⁻¹ with hu
  have huy : weylAct τ u (dualVector r) = Y := by
    rw [hy', ← weylAct_mul_apply, hu, inv_mul_cancel, map_one, LinearIsometryEquiv.coe_one, id]
  set J : Set (Fin τ.rank) := {i | inner ℝ (ofLattice (Pi.single i 1)) Y = 0} with hJdef
  have hinner : ∀ α : Fin τ.rank → ℤ,
      inner ℝ (ofLattice (u • α)) Y = ((charVal r α : ℤ) : ℝ) := fun α => by
    rw [← huy, ← weylAct_ofLattice, LinearIsometryEquiv.inner_map_map,
      inner_ofLattice_dualVector]
  have hΦ : (u • ·) '' rootKernel z = parabolicRoots τ J := by
    ext β
    constructor
    · rintro ⟨α, hα, rfl⟩
      refine ⟨IsRoot.smul hα.1 u, fun i hi => ?_⟩
      have h0 : inner ℝ (ofLattice (u • α)) Y = 0 := by
        rw [hinner, (hkey α hα.1).2 hα, Int.cast_zero]
      exact (inner_root_eq_zero_iff_of_dominant hY (IsRoot.smul hα.1 u)).1 h0 i hi
    · rintro ⟨hβ, hsupp⟩
      have h0 : inner ℝ (ofLattice β) Y = 0 :=
        (inner_root_eq_zero_iff_of_dominant hY hβ).2 fun i hi => hsupp i hi
      refine ⟨u⁻¹ • β, ?_, smul_inv_smul u β⟩
      have hα : IsRoot τ (u⁻¹ • β) := IsRoot.smul hβ u⁻¹
      refine (hkey _ hα).1 ?_
      have := hinner (u⁻¹ • β)
      rw [smul_inv_smul, h0] at this
      exact_mod_cast this.symm
  refine ⟨u, J, hΦ, fun hz hJ => hz ?_⟩
  have hall : ∀ γ, IsRoot τ γ → γ ∈ rootKernel z := by
    intro γ hγ
    have hmem : u • γ ∈ parabolicRoots τ J :=
      ⟨IsRoot.smul hγ u, fun i hi => absurd (hJ ▸ Set.mem_univ i) hi⟩
    rw [← hΦ] at hmem
    obtain ⟨α, hα, he⟩ := hmem
    rw [smul_left_cancel_iff] at he
    exact he ▸ hα
  funext i
  rw [Pi.zero_apply, ← charVal_single z i]
  exact (hall _ (isRoot_single τ i)).2

theorem even_card_of_sq_add_self_add_one {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ}
    (hM : M * M + M + 1 = 0) (J : Finset (Fin n)) (hJ : ∀ a ∉ J, ∀ c ∈ J, M a c = 0) :
    Even J.card := by
  classical
  let N : Matrix J J ℤ := fun a c => M a c
  have hN : N * N + N + 1 = 0 := by
    ext a c
    have h := congrFun (congrFun hM a) c
    simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply, Matrix.zero_apply] at h ⊢
    have hsum : ∑ b : Fin n, M a b * M b c = ∑ b : J, N a b * N b c := by
      rw [← Finset.sum_subset (Finset.subset_univ J) fun b _ hb => by
        rw [hJ b hb c c.2, mul_zero]]
      exact (Finset.sum_coe_sort J fun b => M a b * M b c).symm
    rw [hsum] at h
    have e : ((a : Fin n) = c) ↔ a = c := Subtype.ext_iff.symm
    simpa only [e] using h
  have hNN : N * N = -N - 1 := by
    rw [← sub_eq_zero, ← hN]
    abel
  have h3 : ((2 : ℤ) • N + 1) * ((2 : ℤ) • N + 1) = (-3 : ℤ) • (1 : Matrix J J ℤ) := by
    rw [add_mul, mul_add, mul_add, mul_one, one_mul, mul_one, smul_mul_smul_comm, hNN]
    module
  have hdet := congrArg Matrix.det h3
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_coe] at hdet
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  rw [Odd.neg_pow hodd] at hdet
  have h1 : 0 ≤ ((2 : ℤ) • N + 1).det * ((2 : ℤ) • N + 1).det := mul_self_nonneg _
  have h2 : (0 : ℤ) < 3 ^ J.card := by positivity
  linarith

theorem three_dvd_ncard_of_free {τ : Tag} {S : Set (Fin τ.rank → ℤ)} (hS : S.Finite)
    {w : WeylGroup τ} (hw3 : w ^ 3 = 1) (hmaps : ∀ x ∈ S, w • x ∈ S)
    (hfree : ∀ x ∈ S, w • x ≠ x) : 3 ∣ S.ncard := by
  classical
  have : Fintype S := hS.fintype
  have hthree : ∀ x : Fin τ.rank → ℤ, w • w • w • x = x := fun x => by
    rw [smul_smul, smul_smul, ← pow_three', hw3, one_smul]
  have hmem : ∀ x, w • x ∈ S ↔ x ∈ S := fun x =>
    ⟨fun h => by
      have h2 := hmaps _ (hmaps _ h)
      rwa [hthree] at h2, fun h => hmaps x h⟩
  let σ : Equiv.Perm S := (MulAction.toPerm w).subtypePerm fun x => hmem x
  have hσ : ∀ x : S, (σ x : Fin τ.rank → ℤ) = w • (x : Fin τ.rank → ℤ) := fun x => rfl
  have hσ3 : σ ^ 3 ^ 1 = 1 := by
    refine Equiv.ext fun x => Subtype.ext ?_
    rw [pow_one, pow_succ, pow_succ, pow_one, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hσ, hσ,
      hσ, hthree]
    rfl
  have hsupp : σ.supportᶜ.card = 0 := by
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    intro x hx
    rw [Finset.mem_compl, Equiv.Perm.mem_support, not_not] at hx
    exact hfree x x.2 (congrArg Subtype.val hx ▸ (hσ x).symm)
  have hmod := Equiv.Perm.card_compl_support_modEq (p := 3) (n := 1) hσ3
  rw [hsupp] at hmod
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  exact (Nat.modEq_zero_iff_dvd.1 hmod.symm)

end CFSG.RankThree.PartOne.KF4
