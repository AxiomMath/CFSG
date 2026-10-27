module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotBlocks
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticTorus
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitSpBasic

public section

namespace CFSG.StandardType

open CFSG CFSG.SeitzReduction.SymplecticPilot
open CFSG.Open (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)

private theorem swapCoord_singleton {m : ℕ} (i : Fin m) :
    WitSp.swapCoord {i} = ⇑(TableBSymp.pairSwap i) := by
  funext a
  rcases a with a | a <;> by_cases ha : a = i <;>
    simp [WitSp.swapCoord, TableBSymp.pairSwap, Equiv.swap_apply_def, ha]

private theorem spSwapSp_eq_swapSp_singleton {K : Type} [Field K] {m : ℕ} [CharP K 2]
    (i : Fin m) : TableBSymp.spSwapSp (K := K) (m := m) i = WitSp.swapSp {i} := by
  refine mat_injective (n := m) (F := K) ?_
  rw [WitSp.mat_swapSp, mat_apply, TableBSymp.spSwapSp_coe, TauCeti.permutationGL_coe]
  ext a b
  rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_eq, Matrix.submatrix_apply,
    Matrix.one_apply, WitSp.swapMat_apply, swapCoord_singleton, TableBSymp.pairSwap,
    Equiv.swap_inv]
  exact if_congr eq_comm rfl rfl

private theorem flipU_singleton {K : Type} [Field K] {m : ℕ} (i : Fin m) (t : Fin m → Kˣ) :
    WitSp.flipU {i} t = Function.update t i (t i)⁻¹ := by
  funext k
  by_cases hk : k = i
  · subst hk
    simp [WitSp.flipU]
  · simp [WitSp.flipU, hk]

theorem spSwapSp_conj_diagSp {K : Type} [Field K] {m : ℕ} [CharP K 2] (i : Fin m)
    (t : Fin m → Kˣ) :
    TableBSymp.spSwapSp i * diagSp K m t * (TableBSymp.spSwapSp i)⁻¹ =
      diagSp K m (Function.update t i (t i)⁻¹) := by
  rw [spSwapSp_eq_swapSp_singleton, WitSp.swapSp_conj_diagSp, flipU_singleton]

@[expose] noncomputable def spSignedPermSp (K : Type) [Field K] (m : ℕ) [CharP K 2] :
    Subgroup (StatedSp m K) :=
  Subgroup.closure (Set.range (permSp K) ∪ Set.range (TableBSymp.spSwapSp (K := K) (m := m)))

private noncomputable def signedConjClosureSp (K : Type) [Field K] (m : ℕ) [CharP K 2]
    (x : Fin m → Kˣ) : Subgroup (StatedSp m K) :=
  Subgroup.closure (⋃ w ∈ spSignedPermSp K m,
    (fun z => w * z * w⁻¹) '' (Subgroup.zpowers (diagSp K m x) : Set (StatedSp m K)))

private theorem diagSp_mem_signedConjClosure {K : Type} [Field K] {m : ℕ} [CharP K 2]
    (x : Fin m → Kˣ) : diagSp K m x ∈ signedConjClosureSp K m x := by
  refine Subgroup.subset_closure ?_
  simp only [Set.mem_iUnion, Set.mem_image, exists_prop]
  exact ⟨1, Subgroup.one_mem _, diagSp K m x, Subgroup.mem_zpowers _, by simp⟩

private theorem conj_mem_signedConjClosure {K : Type} [Field K] {m : ℕ} [CharP K 2]
    {x : Fin m → Kˣ} {w' : StatedSp m K} (hw' : w' ∈ spSignedPermSp K m)
    {z : StatedSp m K} (hz : z ∈ signedConjClosureSp K m x) :
    w' * z * w'⁻¹ ∈ signedConjClosureSp K m x := by
  have key : ∀ y ∈ (⋃ w ∈ spSignedPermSp K m,
      (fun z => w * z * w⁻¹) '' (Subgroup.zpowers (diagSp K m x) : Set (StatedSp m K))),
      w' * y * w'⁻¹ ∈ signedConjClosureSp K m x := by
    intro y hy
    simp only [Set.mem_iUnion, Set.mem_image, exists_prop] at hy
    obtain ⟨w, hw, z, hz, rfl⟩ := hy
    refine Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨w' * w,
      Set.mem_iUnion.mpr ⟨Subgroup.mul_mem _ hw' hw, z, hz, ?_⟩⟩)
    group
  change z ∈ Subgroup.closure (⋃ w ∈ spSignedPermSp K m,
    (fun z => w * z * w⁻¹) '' (Subgroup.zpowers (diagSp K m x) : Set (StatedSp m K))) at hz
  induction hz using Subgroup.closure_induction with
  | mem y hy => exact key y hy
  | one => simp
  | mul a b _ _ ha hb =>
    rw [show w' * (a * b) * w'⁻¹ = (w' * a * w'⁻¹) * (w' * b * w'⁻¹) by group]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    rw [show w' * a⁻¹ * w'⁻¹ = (w' * a * w'⁻¹)⁻¹ by group]
    exact Subgroup.inv_mem _ ha

private theorem diagSp_update_inv_mem {K : Type} [Field K] {m : ℕ} [CharP K 2]
    (x : Fin m → Kˣ) (j : Fin m) :
    diagSp K m (Function.update x j (x j)⁻¹) ∈ signedConjClosureSp K m x := by
  have hperm : TableBSymp.spSwapSp (K := K) (m := m) j ∈ spSignedPermSp K m :=
    Subgroup.subset_closure (Set.mem_union_right _ ⟨j, rfl⟩)
  have hmem : TableBSymp.spSwapSp (K := K) (m := m) j * diagSp K m x *
      (TableBSymp.spSwapSp j)⁻¹ ∈ signedConjClosureSp K m x :=
    Subgroup.subset_closure (Set.mem_iUnion.mpr ⟨TableBSymp.spSwapSp j,
      Set.mem_iUnion.mpr ⟨hperm, diagSp K m x, Subgroup.mem_zpowers _, rfl⟩⟩)
  rwa [spSwapSp_conj_diagSp j x] at hmem

private theorem diagSp_mulSingle_sq_mem {K : Type} [Field K] {m : ℕ} [CharP K 2]
    (x : Fin m → Kˣ) (j : Fin m) :
    diagSp K m (Pi.mulSingle j ((x j) ^ 2)) ∈ signedConjClosureSp K m x := by
  have h1 := diagSp_mem_signedConjClosure (K := K) (m := m) x
  have h2 := diagSp_update_inv_mem (K := K) (m := m) x j
  have h3 : diagSp K m (Pi.mulSingle j ((x j) ^ 2)) =
      diagSp K m x * (diagSp K m (Function.update x j (x j)⁻¹))⁻¹ := by
    rw [← map_inv, ← map_mul]
    congr 1
    ext a
    by_cases ha : a = j
    · subst ha
      simp [Pi.mulSingle_eq_same, pow_two]
    · simp [ha]
  rw [h3]
  exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)

private theorem zpowers_sq_eq {K : Type} [Field K] [Finite K] [CharP K 2] (a : Kˣ) :
    Subgroup.zpowers (a ^ 2) = Subgroup.zpowers a := by
  refine le_antisymm (Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers a 2)) ?_
  refine Subgroup.zpowers_le.mpr (mem_zpowers_pow_iff.mpr ?_)
  have hcard : Odd (Nat.card Kˣ) := by
    have h := odd_card_rootTorusSp (K := K) (n := 1) 0
    rwa [card_rootTorusSp, ← Nat.card_units] at h
  exact Nat.coprime_two_left.mpr
    (Odd.of_dvd_nat hcard (orderOf_dvd_natCard a))

private theorem diagSp_mulSingle_mem {K : Type} [Field K] {m : ℕ} [Finite K] [CharP K 2]
    (x : Fin m → Kˣ) (j : Fin m) {u : Kˣ} (hu : u ∈ Subgroup.zpowers (x j)) :
    diagSp K m (Pi.mulSingle j u) ∈ signedConjClosureSp K m x := by
  have hle : Subgroup.zpowers ((x j) ^ 2) ≤
      Subgroup.comap (rootTorusHom K m j) (signedConjClosureSp K m x) := by
    rw [Subgroup.zpowers_le]
    simpa [rootTorusHom_apply] using diagSp_mulSingle_sq_mem (K := K) (m := m) x j
  rw [zpowers_sq_eq (x j)] at hle
  exact hle hu

theorem diagSp_mem_closure_signedConj {K : Type} [Field K] {m : ℕ} [Finite K] [CharP K 2]
    (x y : Fin m → Kˣ) (j : Fin m) (hy : ∀ i, y i ∈ Subgroup.zpowers (x j)) :
    diagSp K m y ∈ Subgroup.closure (⋃ w ∈ spSignedPermSp K m,
      (fun z => w * z * w⁻¹) '' (Subgroup.zpowers (diagSp K m x) : Set (StatedSp m K))) := by
  change diagSp K m y ∈ signedConjClosureSp K m x
  have hsingle : ∀ i, diagSp K m (Pi.mulSingle i (y i)) ∈ signedConjClosureSp K m x := by
    intro i
    have hbase := diagSp_mulSingle_mem (K := K) (m := m) x j (hy i)
    have hperm : permSp K (Equiv.swap j i) ∈ spSignedPermSp K m :=
      Subgroup.subset_closure (Set.mem_union_left _ ⟨Equiv.swap j i, rfl⟩)
    have hconj := conj_mem_signedConjClosure (K := K) (m := m) hperm hbase
    rwa [conj_permSp_diagSp, mulSingle_comp_symm, Equiv.swap_apply_left] at hconj
  have hprod : ∀ s : Finset (Fin m),
      diagSp K m (s.prod fun i => Pi.mulSingle i (y i)) ∈ signedConjClosureSp K m x := by
    intro s
    refine Finset.induction ?_ ?_ s
    · rw [Finset.prod_empty, map_one]
      exact Subgroup.one_mem _
    · intro a s ha ih
      rw [Finset.prod_insert ha, map_mul]
      exact Subgroup.mul_mem _ (hsingle a) ih
  rw [show diagSp K m y =
    diagSp K m (Finset.univ.prod fun i => Pi.mulSingle i (y i)) by
      rw [Finset.univ_prod_mulSingle]]
  exact hprod Finset.univ

end CFSG.StandardType
