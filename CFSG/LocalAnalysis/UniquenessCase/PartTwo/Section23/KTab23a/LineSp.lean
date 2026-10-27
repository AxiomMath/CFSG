module

public import CFSG.Open.StatedDefs
import CFSG.ClassicalGroups.Symplectic.Model

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA

open CFSG.Open
open scoped Matrix

private def spVec (K : Type) [Field K] (m : ℕ) [NeZero m] : Fin m ⊕ Fin m → K :=
  Pi.single (Sum.inl 0) (1 : K)

private def spPerp (K : Type) [Field K] (m : ℕ) [NeZero m] :
    Submodule K (Fin m ⊕ Fin m → K) :=
  LinearMap.ker (LinearMap.proj (Sum.inr (0 : Fin m)))

private def spLine (K : Type) [Field K] (m : ℕ) [NeZero m] :
    Submodule K (Fin m ⊕ Fin m → K) :=
  Submodule.span K {spVec K m}

private lemma spVec_mem_perp (K : Type) [Field K] (m : ℕ) [NeZero m] :
    spVec K m ∈ spPerp K m := by
  rw [spPerp, LinearMap.mem_ker]
  simp [spVec]

private lemma spVec_mem_line (K : Type) [Field K] (m : ℕ) [NeZero m] :
    spVec K m ∈ spLine K m :=
  Submodule.subset_span (Set.mem_singleton _)

private lemma spLine_le_perp (K : Type) [Field K] (m : ℕ) [NeZero m] :
    spLine K m ≤ spPerp K m := by
  rw [spLine, Submodule.span_le]
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  rw [hw]
  exact spVec_mem_perp K m

private lemma mem_spPerp_iff (K : Type) [Field K] (m : ℕ) [NeZero m]
    (v : Fin m ⊕ Fin m → K) : v ∈ spPerp K m ↔ v (Sum.inr 0) = 0 := by
  rw [spPerp, LinearMap.mem_ker]
  simp

private lemma single_inl_mem_perp (K : Type) [Field K] (m : ℕ) [NeZero m] (i : Fin m) :
    Pi.single (Sum.inl i) (1 : K) ∈ spPerp K m := by
  rw [mem_spPerp_iff]
  simp

private lemma single_inr_mem_perp (K : Type) [Field K] (m : ℕ) [NeZero m]
    (j : Fin m) (hj : j ≠ 0) : Pi.single (Sum.inr j) (1 : K) ∈ spPerp K m := by
  rw [mem_spPerp_iff]
  simp [hj]

private def spFlagPred (K : Type) [Field K] (m : ℕ) [NeZero m]
    (M : GL (Fin m ⊕ Fin m) K) : Prop :=
  (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ spVec K m = spVec K m ∧
    (∀ v, ((M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1) *ᵥ v ∈ spPerp K m) ∧
    (∀ v, v ∈ spPerp K m →
      ((M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1) *ᵥ v ∈ spLine K m)

private lemma spFlagPred_mul (K : Type) [Field K] (m : ℕ) [NeZero m]
    {M1 M2 : GL (Fin m ⊕ Fin m) K} (h1 : spFlagPred K m M1) (h2 : spFlagPred K m M2) :
    spFlagPred K m (M1 * M2) := by
  obtain ⟨ha1, ha2, ha3⟩ := h1
  obtain ⟨hb1, hb2, hb3⟩ := h2
  let N1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
    (M1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1
  let N2 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
    (M2 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1
  have hN1eq : (M1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = 1 + N1 := by
    show (M1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      1 + ((M1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1)
    abel
  have hN2eq : (M2 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = 1 + N2 := by
    show (M2 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      1 + ((M2 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1)
    abel
  have hdec : (M1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
      (M2 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1 = N1 * N2 + N1 + N2 := by
    rw [hN1eq, hN2eq]
    noncomm_ring
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec, hb1, ha1]
  · intro v
    rw [Units.val_mul, hdec, Matrix.add_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
    exact add_mem (add_mem (spLine_le_perp K m (ha3 _ (hb2 v))) (ha2 v)) (hb2 v)
  · intro v hv
    rw [Units.val_mul, hdec, Matrix.add_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
    exact add_mem (add_mem (ha3 _ (spLine_le_perp K m (hb3 v hv))) (ha3 v hv)) (hb3 v hv)

private lemma spFlagPred_one (K : Type) [Field K] (m : ℕ) [NeZero m] :
    spFlagPred K m (1 : GL (Fin m ⊕ Fin m) K) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Units.val_one, Matrix.one_mulVec]
  · intro v
    rw [Units.val_one, sub_self, Matrix.zero_mulVec]
    exact Submodule.zero_mem _
  · intro v hv
    rw [Units.val_one, sub_self, Matrix.zero_mulVec]
    exact Submodule.zero_mem _

private lemma spFlagPred_inv (K : Type) [Field K] (m : ℕ) [NeZero m]
    {x : GL (Fin m ⊕ Fin m) K} (hx : spFlagPred K m x) : spFlagPred K m x⁻¹ := by
  obtain ⟨ha1, ha2, ha3⟩ := hx
  have hu_inv : (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
      ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hNinv_eq : ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1 =
      -(((x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1) *
        ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) := by
    rw [Matrix.sub_mul, Matrix.one_mul, hu_inv, neg_sub]
  refine ⟨?_, ?_, ?_⟩
  · calc ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ spVec K m
        = ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
            ((x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ spVec K m) := by
          rw [ha1]
      _ = (((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
            (x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) *ᵥ spVec K m := by
          rw [Matrix.mulVec_mulVec]
      _ = spVec K m := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  · intro v
    rw [hNinv_eq, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]
    exact neg_mem (ha2 _)
  · intro v hv
    have hperp : (((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1) *ᵥ
        v ∈ spPerp K m := by
      rw [hNinv_eq, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]
      exact neg_mem (ha2 _)
    have hmem : ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
        v ∈ spPerp K m := by
      have hsplit : ((x⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
          v = v + (((x⁻¹ : GL (Fin m ⊕ Fin m) K) :
            Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1) *ᵥ v := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]
        abel
      rw [hsplit]
      exact add_mem hv hperp
    rw [hNinv_eq, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]
    exact neg_mem (ha3 _ hmem)

private def spFlag (K : Type) [Field K] (m : ℕ) [NeZero m] :
    Subgroup (GL (Fin m ⊕ Fin m) K) where
  carrier := {M | spFlagPred K m M}
  mul_mem' := spFlagPred_mul K m
  one_mem' := spFlagPred_one K m
  inv_mem' := fun h => spFlagPred_inv K m h

private def spU (K : Type) [Field K] (m : ℕ) [NeZero m] :
    Subgroup ↥(StatedSp m K) :=
  (spFlag K m).comap (StatedSp m K).subtype

private def flagN (K : Type) [Field K] (m : ℕ) [NeZero m]
    (u : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
  (u : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1

private lemma pow_eq_one_of_flag (K : Type) [Field K] (m : ℕ) [NeZero m] (p : ℕ)
    [Fact p.Prime] [CharP K p] (u : GL (Fin m ⊕ Fin m) K)
    (ha1 : (u : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ spVec K m = spVec K m)
    (ha2 : ∀ v, flagN K m u *ᵥ v ∈ spPerp K m)
    (ha3 : ∀ v, v ∈ spPerp K m → flagN K m u *ᵥ v ∈ spLine K m) :
    u ^ (p ^ 2) = 1 := by
  have hNvec : flagN K m u *ᵥ spVec K m = 0 := by
    rw [flagN, Matrix.sub_mulVec, Matrix.one_mulVec, ha1, sub_self]
  have hkill : ∀ w ∈ spLine K m, flagN K m u *ᵥ w = 0 := by
    intro w hw
    rw [spLine, Submodule.mem_span_singleton] at hw
    obtain ⟨c, rfl⟩ := hw
    rw [Matrix.mulVec_smul, hNvec, smul_zero]
  have hN3 : flagN K m u ^ 3 = 0 := by
    have h3 : flagN K m u * flagN K m u * flagN K m u = 0 := by
      ext i j
      have h1 : flagN K m u *ᵥ Pi.single j (1 : K) ∈ spPerp K m := ha2 _
      have h2 : flagN K m u *ᵥ (flagN K m u *ᵥ Pi.single j (1 : K)) ∈ spLine K m :=
        ha3 _ h1
      have hv : (flagN K m u * flagN K m u * flagN K m u) *ᵥ Pi.single j (1 : K) = 0 := by
        calc (flagN K m u * flagN K m u * flagN K m u) *ᵥ Pi.single j (1 : K)
            = flagN K m u *ᵥ (flagN K m u *ᵥ (flagN K m u *ᵥ Pi.single j (1 : K))) := by
              rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
          _ = 0 := hkill _ h2
      have := congrFun hv i
      simpa [Matrix.mulVec_single_one] using this
    rw [show flagN K m u ^ 3 = flagN K m u * flagN K m u * flagN K m u by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two]]
    exact h3
  have hNpow : flagN K m u ^ (p ^ 2) = 0 := by
    have hp2 : 3 ≤ p ^ 2 := by
      have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
      calc (3 : ℕ) ≤ 2 ^ 2 := by norm_num
        _ ≤ p ^ 2 := Nat.pow_le_pow_left hp 2
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hp2
    rw [hk, pow_add, hN3, zero_mul]
  have h1 : (u : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = 1 + flagN K m u := by
    rw [flagN]
    abel
  have hmat : ((u : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) ^ (p ^ 2) = 1 := by
    rw [h1, add_pow_char_pow_of_commute (p := p) (n := 2) (Commute.one_left (flagN K m u)),
      one_pow, hNpow, add_zero]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one]
  exact hmat

private lemma spFlag_isPGroup (K : Type) [Field K] (m : ℕ) [NeZero m] (p : ℕ)
    [Fact p.Prime] [CharP K p] : IsPGroup p ↥(spFlag K m) := by
  intro M
  refine ⟨2, ?_⟩
  have ha1 : ((M : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
      spVec K m = spVec K m :=
    M.property.1
  have ha2 : ∀ v, flagN K m (M : GL (Fin m ⊕ Fin m) K) *ᵥ v ∈ spPerp K m := by
    intro v
    simpa only [flagN] using M.property.2.1 v
  have ha3 : ∀ v, v ∈ spPerp K m →
      flagN K m (M : GL (Fin m ⊕ Fin m) K) *ᵥ v ∈ spLine K m := by
    intro v hv
    simpa only [flagN] using M.property.2.2 v hv
  have h := pow_eq_one_of_flag K m p (M : GL (Fin m ⊕ Fin m) K) ha1 ha2 ha3
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact h

private lemma spU_isPGroup (K : Type) [Field K] (m : ℕ) [NeZero m] (p : ℕ)
    [Fact p.Prime] [CharP K p] : IsPGroup p ↥(spU K m) := by
  have hW : IsPGroup p ↥(spFlag K m) := spFlag_isPGroup K m p
  refine hW.of_injective
    { toFun := fun A =>
        (⟨((A : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K), A.2⟩ : ↥(spFlag K m))
      map_one' := Subtype.ext rfl
      map_mul' := fun A B => Subtype.ext rfl } ?_
  intro A B hAB
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun y : ↥(spFlag K m) => (y : GL (Fin m ⊕ Fin m) K)) hAB

private noncomputable def genA (K : Type) [Field K] (m : ℕ) [NeZero m] :
    GL (Fin m ⊕ Fin m) K :=
  TauCeti.GLSymplectic.ofSymplecticGroup (Fin m) K
    ⟨Matrix.fromBlocks 1 (Matrix.single (0 : Fin m) 0 (1 : K)) 0 1,
      SymplecticGroup.fromBlocks_upper_mem (by simp)⟩

private lemma genA_mat_blocks (K : Type) [Field K] (m : ℕ) [NeZero m] :
    ((genA K m : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      Matrix.fromBlocks 1 (Matrix.single (0 : Fin m) 0 (1 : K)) 0 1 := by
  rw [genA, TauCeti.GLSymplectic.coe_ofSymplecticGroup]

private lemma genA_mat' (K : Type) [Field K] (m : ℕ) [NeZero m] :
    ((genA K m : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      1 + Matrix.single (Sum.inl (0 : Fin m)) (Sum.inr 0) (1 : K) := by
  rw [genA_mat_blocks]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.one_apply, Matrix.single_apply, Sum.inl.injEq, Sum.inr.injEq]

private lemma genA_sub_one_mulVec (K : Type) [Field K] (m : ℕ) [NeZero m]
    (v : Fin m ⊕ Fin m → K) :
    (((genA K m : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1) *ᵥ v =
      v (Sum.inr 0) • spVec K m := by
  have h : ((genA K m : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1 =
      Matrix.single (Sum.inl (0 : Fin m)) (Sum.inr 0) (1 : K) := by
    rw [genA_mat']
    abel
  rw [h, Matrix.single_mulVec_eq]
  simp [spVec]

private lemma genA_flag (K : Type) [Field K] (m : ℕ) [NeZero m] : genA K m ∈ spFlag K m := by
  refine ⟨?_, ?_, ?_⟩
  · rw [genA_mat', Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec_eq]
    rw [one_mul]
    have h0 : spVec K m (Sum.inr 0) = 0 := by simp [spVec]
    rw [h0, zero_smul, add_zero]
  · intro v
    rw [genA_sub_one_mulVec]
    exact Submodule.smul_mem _ _ (spVec_mem_perp K m)
  · intro v hv
    rw [genA_sub_one_mulVec]
    exact Submodule.smul_mem _ _ (spVec_mem_line K m)

private lemma genA_mem_StatedSp (K : Type) [Field K] (m : ℕ) [NeZero m] :
    genA K m ∈ StatedSp m K := by
  rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic, genA]
  exact TauCeti.GLSymplectic.ofSymplecticGroup_mem (l := Fin m) (R := K) _

private noncomputable def spGenA (K : Type) [Field K] (m : ℕ) [NeZero m] :
    ↥(StatedSp m K) :=
  ⟨genA K m, genA_mem_StatedSp K m⟩

private lemma genA_mem_spU (K : Type) [Field K] (m : ℕ) [NeZero m] :
    spGenA K m ∈ spU K m := by
  rw [spU, Subgroup.mem_comap]
  exact genA_flag K m

private noncomputable def genB (K : Type) [Field K] (m : ℕ) [NeZero m] (j : Fin m) :
    GL (Fin m ⊕ Fin m) K :=
  TauCeti.GLSymplectic.ofSymplecticGroup (Fin m) K
    ⟨Matrix.fromBlocks 1
        (Matrix.single (0 : Fin m) j (1 : K) + Matrix.single j (0 : Fin m) (1 : K)) 0 1,
      SymplecticGroup.fromBlocks_upper_mem (by
        rw [Matrix.transpose_add, Matrix.transpose_single, Matrix.transpose_single]
        abel)⟩

private lemma genB_mat_blocks (K : Type) [Field K] (m : ℕ) [NeZero m] (j : Fin m) :
    ((genB K m j : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      Matrix.fromBlocks 1
        (Matrix.single (0 : Fin m) j (1 : K) + Matrix.single j (0 : Fin m) (1 : K)) 0 1 := by
  rw [genB, TauCeti.GLSymplectic.coe_ofSymplecticGroup]

private lemma genB_mat' (K : Type) [Field K] (m : ℕ) [NeZero m] (j : Fin m) :
    ((genB K m j : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      1 + Matrix.single (Sum.inl (0 : Fin m)) (Sum.inr j) (1 : K) +
        Matrix.single (Sum.inl j) (Sum.inr 0) (1 : K) := by
  rw [genB_mat_blocks]
  ext i j'
  rcases i with i | i <;> rcases j' with j' | j' <;>
    simp [Matrix.one_apply, Matrix.single_apply, Sum.inl.injEq, Sum.inr.injEq]

private lemma genB_sub_one_mulVec (K : Type) [Field K] (m : ℕ) [NeZero m] (j : Fin m)
    (v : Fin m ⊕ Fin m → K) :
    (((genB K m j : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1) *ᵥ v =
      v (Sum.inr j) • spVec K m + v (Sum.inr 0) • Pi.single (Sum.inl j) (1 : K) := by
  have h : ((genB K m j : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1 =
      Matrix.single (Sum.inl (0 : Fin m)) (Sum.inr j) (1 : K) +
        Matrix.single (Sum.inl j) (Sum.inr 0) (1 : K) := by
    rw [genB_mat']
    abel
  rw [h, Matrix.add_mulVec, Matrix.single_mulVec_eq, Matrix.single_mulVec_eq]
  simp [spVec]

private lemma genB_flag (K : Type) [Field K] (m : ℕ) [NeZero m] (j : Fin m) :
    genB K m j ∈ spFlag K m := by
  refine ⟨?_, ?_, ?_⟩
  · rw [genB_mat', Matrix.add_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.single_mulVec_eq, Matrix.single_mulVec_eq]
    rw [one_mul, one_mul]
    have h0 : spVec K m (Sum.inr 0) = 0 := by simp [spVec]
    have hj0 : spVec K m (Sum.inr j) = 0 := by simp [spVec]
    rw [h0, hj0, zero_smul, zero_smul, add_zero, add_zero]
  · intro v
    rw [genB_sub_one_mulVec]
    exact add_mem (Submodule.smul_mem _ _ (spVec_mem_perp K m))
      (Submodule.smul_mem _ _ (single_inl_mem_perp K m j))
  · intro v hv
    rw [mem_spPerp_iff] at hv
    rw [genB_sub_one_mulVec, hv, zero_smul]
    simpa using Submodule.smul_mem _ _ (spVec_mem_line K m)

private lemma genB_mem_StatedSp (K : Type) [Field K] (m : ℕ) [NeZero m] (j : Fin m) :
    genB K m j ∈ StatedSp m K := by
  rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic, genB]
  exact TauCeti.GLSymplectic.ofSymplecticGroup_mem (l := Fin m) (R := K) _

private noncomputable def spGenB (K : Type) [Field K] (m : ℕ) [NeZero m] (j : Fin m) :
    ↥(StatedSp m K) :=
  ⟨genB K m j, genB_mem_StatedSp K m j⟩

private lemma genB_mem_spU (K : Type) [Field K] (m : ℕ) [NeZero m] (j : Fin m) :
    spGenB K m j ∈ spU K m := by
  rw [spU, Subgroup.mem_comap]
  exact genB_flag K m j

private lemma genC_block (K : Type) [Field K] (m : ℕ) [NeZero m] (j : Fin m) (hj : j ≠ 0) :
    (1 + Matrix.single (0 : Fin m) j (1 : K))ᵀ * (1 - Matrix.single j (0 : Fin m) (1 : K)) =
      1 := by
  rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]
  have hXX : Matrix.single j (0 : Fin m) (1 : K) * Matrix.single j (0 : Fin m) (1 : K) = 0 := by
    simp [hj, Ne.symm hj]
  rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
    Matrix.mul_one, hXX]
  abel

private noncomputable def genC (K : Type) [Field K] (m : ℕ) [NeZero m] (j : Fin m)
    (hj : j ≠ 0) : GL (Fin m ⊕ Fin m) K :=
  TauCeti.GLSymplectic.ofSymplecticGroup (Fin m) K
    ⟨Matrix.fromBlocks (1 + Matrix.single (0 : Fin m) j (1 : K)) 0 0
        (1 - Matrix.single j (0 : Fin m) (1 : K)),
      SymplecticGroup.fromBlocks_diagonal_mem (genC_block K m j hj)⟩

private lemma genC_mat_blocks (K : Type) [Field K] (m : ℕ) [NeZero m] (j : Fin m)
    (hj : j ≠ 0) :
    ((genC K m j hj : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      Matrix.fromBlocks (1 + Matrix.single (0 : Fin m) j (1 : K)) 0 0
        (1 - Matrix.single j (0 : Fin m) (1 : K)) := by
  rw [genC, TauCeti.GLSymplectic.coe_ofSymplecticGroup]

private lemma genC_mat' (K : Type) [Field K] (m : ℕ) [NeZero m] (j : Fin m) (hj : j ≠ 0) :
    ((genC K m j hj : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      1 + Matrix.single (Sum.inl (0 : Fin m)) (Sum.inl j) (1 : K) -
        Matrix.single (Sum.inr j) (Sum.inr 0) (1 : K) := by
  rw [genC_mat_blocks]
  ext i j'
  rcases i with i | i <;> rcases j' with j' | j' <;>
    simp [Matrix.one_apply, Matrix.single_apply, Sum.inl.injEq, Sum.inr.injEq]

private lemma genC_sub_one_mulVec (K : Type) [Field K] (m : ℕ) [NeZero m] (j : Fin m)
    (hj : j ≠ 0) (v : Fin m ⊕ Fin m → K) :
    (((genC K m j hj : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1) *ᵥ v =
      v (Sum.inl j) • spVec K m - v (Sum.inr 0) • Pi.single (Sum.inr j) (1 : K) := by
  have h : ((genC K m j hj : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1 =
      Matrix.single (Sum.inl (0 : Fin m)) (Sum.inl j) (1 : K) -
        Matrix.single (Sum.inr j) (Sum.inr 0) (1 : K) := by
    rw [genC_mat']
    abel
  rw [h, Matrix.sub_mulVec, Matrix.single_mulVec_eq, Matrix.single_mulVec_eq]
  simp [spVec]

private lemma genC_flag (K : Type) [Field K] (m : ℕ) [NeZero m] (j : Fin m) (hj : j ≠ 0) :
    genC K m j hj ∈ spFlag K m := by
  refine ⟨?_, ?_, ?_⟩
  · rw [genC_mat', Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.single_mulVec_eq, Matrix.single_mulVec_eq]
    rw [one_mul, one_mul]
    have h0 : spVec K m (Sum.inr 0) = 0 := by simp [spVec]
    have hj0 : spVec K m (Sum.inl j) = 0 := by simp [spVec, hj]
    rw [h0, hj0, zero_smul, zero_smul, sub_zero, add_zero]
  · intro v
    rw [genC_sub_one_mulVec]
    exact sub_mem (Submodule.smul_mem _ _ (spVec_mem_perp K m))
      (Submodule.smul_mem _ _ (single_inr_mem_perp K m j hj))
  · intro v hv
    rw [mem_spPerp_iff] at hv
    rw [genC_sub_one_mulVec, hv, zero_smul]
    simpa using Submodule.smul_mem _ _ (spVec_mem_line K m)

private lemma genC_mem_StatedSp (K : Type) [Field K] (m : ℕ) [NeZero m] (j : Fin m)
    (hj : j ≠ 0) : genC K m j hj ∈ StatedSp m K := by
  rw [CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic, genC]
  exact TauCeti.GLSymplectic.ofSymplecticGroup_mem (l := Fin m) (R := K) _

private noncomputable def spGenC (K : Type) [Field K] (m : ℕ) [NeZero m] (j : Fin m)
    (hj : j ≠ 0) : ↥(StatedSp m K) :=
  ⟨genC K m j hj, genC_mem_StatedSp K m j hj⟩

private lemma genC_mem_spU (K : Type) [Field K] (m : ℕ) [NeZero m] (j : Fin m) (hj : j ≠ 0) :
    spGenC K m j hj ∈ spU K m := by
  rw [spU, Subgroup.mem_comap]
  exact genC_flag K m j hj

private lemma mem_span_spVec_of_fixed (K : Type) [Field K] (m : ℕ) [NeZero m]
    (v : Fin m ⊕ Fin m → K)
    (hA : (genA K m : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v = v)
    (hB : ∀ j : Fin m, (genB K m j : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v = v)
    (hC : ∀ (j : Fin m) (hj : j ≠ 0),
      (genC K m j hj : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v = v) :
    v ∈ Submodule.span K {spVec K m} := by
  have hA0 : v (Sum.inr 0) • spVec K m = 0 := by
    have h := genA_sub_one_mulVec K m v
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hA, sub_self] at h
    exact h.symm
  have hy0 : v (Sum.inr 0) = 0 := by
    have := congrFun hA0 (Sum.inl (0 : Fin m))
    simpa [spVec] using this
  have hx : ∀ i : Fin m, i ≠ 0 → v (Sum.inl i) = 0 := by
    intro i hi
    have h0 : v (Sum.inl i) • spVec K m - v (Sum.inr 0) • Pi.single (Sum.inr i) (1 : K) = 0 := by
      have h := genC_sub_one_mulVec K m i hi v
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hC i hi, sub_self] at h
      exact h.symm
    have := congrFun h0 (Sum.inl (0 : Fin m))
    simpa [spVec, hy0] using this
  have hy : ∀ j : Fin m, j ≠ 0 → v (Sum.inr j) = 0 := by
    intro j hj
    have h0 : v (Sum.inr j) • spVec K m + v (Sum.inr 0) • Pi.single (Sum.inl j) (1 : K) = 0 := by
      have h := genB_sub_one_mulVec K m j v
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, hB j, sub_self] at h
      exact h.symm
    have := congrFun h0 (Sum.inl (0 : Fin m))
    simpa [spVec, hy0, hj] using this
  have hv_eq : v = v (Sum.inl 0) • spVec K m := by
    funext i
    rcases i with i | j
    · by_cases hi : i = 0
      · subst hi
        simp [spVec]
      · rw [hx i hi]
        simp [spVec, hi]
    · by_cases hj : j = 0
      · subst hj
        rw [hy0]
        simp [spVec]
      · rw [hy j hj]
        simp [spVec]
  rw [hv_eq]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

private theorem exists_fixedLine_statedSp_aux (K : Type) [Field K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (m : ℕ) [NeZero m] :
    ∃ (U : Subgroup ↥(StatedSp m K)) (e : Fin m ⊕ Fin m → K), IsPGroup p ↥U ∧
      ∀ v : Fin m ⊕ Fin m → K,
        (∀ u ∈ U, ((u : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K) *ᵥ v = v) →
          v ∈ Submodule.span K {e} := by
  refine ⟨spU K m, spVec K m, spU_isPGroup K m p, ?_⟩
  intro v hv
  exact mem_span_spVec_of_fixed K m v
    (by simpa [spGenA] using hv (spGenA K m) (genA_mem_spU K m))
    (fun j => by simpa [spGenB] using hv (spGenB K m j) (genB_mem_spU K m j))
    (fun j hj => by simpa [spGenC] using hv (spGenC K m j hj) (genC_mem_spU K m j hj))

theorem exists_fixedLine_statedSp {K : Type} [Field K] [Finite K] (p : ℕ) [Fact p.Prime]
    [CharP K p] (m : ℕ) :
    ∃ (U : Subgroup ↥(StatedSp m K)) (e : Fin m ⊕ Fin m → K), IsPGroup p ↥U ∧
      ∀ v : Fin m ⊕ Fin m → K,
        (∀ u ∈ U, ((u : GL (Fin m ⊕ Fin m) K) : Matrix _ _ K) *ᵥ v = v) →
          v ∈ Submodule.span K {e} := by
  rcases m with _ | m
  · refine ⟨⊥, 0, ?_, ?_⟩
    · exact IsPGroup.of_bot
    · intro v hv
      have hv0 : v = 0 := by
        funext i
        rcases i with i | i <;> exact Fin.elim0 i
      rw [hv0]
      exact Submodule.zero_mem _
  · exact exists_fixedLine_statedSp_aux K p (m + 1)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KTabA
