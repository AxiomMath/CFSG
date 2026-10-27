module

public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiagDiag

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley

namespace TableB

section Torus

theorem zpow_finset_sum {G : Type*} [CommGroup G] (s : G) {ι : Type*} (t : Finset ι)
    (f : ι → ℤ) : s ^ (∑ i ∈ t, f i) = ∏ i ∈ t, s ^ f i := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, zpow_add, ih]

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (K : Type) [Field K]

@[expose] def torusChar (i : Fin r) (t : Kˣ) : Fin r → Kˣ :=
  fun j => t ^ A i j

@[expose] def torusSubgroup : Subgroup (Fin r → Kˣ) :=
  Subgroup.closure (Set.range fun p : Fin r × Kˣ => torusChar A K p.1 p.2)

theorem torusChar_mem (i : Fin r) (t : Kˣ) : torusChar A K i t ∈ torusSubgroup A K :=
  Subgroup.subset_closure ⟨(i, t), rfl⟩

theorem prod_torusChar (m : Fin r → ℤ) (s : Kˣ) :
    ∏ i, torusChar A K i (s ^ m i) = fun j => s ^ (∑ i, m i * A i j) := by
  funext j
  rw [Finset.prod_apply, zpow_finset_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [torusChar, ← zpow_mul]

theorem zpow_sum_mem_torusSubgroup (m : Fin r → ℤ) (s : Kˣ) :
    (fun j => s ^ (∑ i, m i * A i j)) ∈ torusSubgroup A K := by
  rw [← prod_torusChar]
  exact Subgroup.prod_mem _ fun i _ => torusChar_mem A K i _

theorem mulSingle_pow_mem_torusSubgroup {M : Matrix (Fin r) (Fin r) ℤ} {d : ℤ}
    (hM : M * A = d • (1 : Matrix (Fin r) (Fin r) ℤ)) (j : Fin r) (s : Kˣ) :
    Pi.mulSingle j (s ^ d) ∈ torusSubgroup A K := by
  have h := zpow_sum_mem_torusSubgroup A K (M j) s
  convert h using 1
  funext j'
  have hj := congrFun (congrFun hM j) j'
  rw [Matrix.mul_apply] at hj
  rw [hj, Pi.mulSingle_apply, Matrix.smul_apply, Matrix.one_apply]
  by_cases h' : j' = j
  · subst h'
    simp
  · simp [h', Ne.symm h']

end Torus

section Transport

@[expose] noncomputable def markDiag {r : ℕ} (S : (Fin r → ℤ) → Prop) (K : Type) [Field K]
    (a : Fin r → Kˣ) : Module.End K (MarkChev.Space S K) :=
  Finsupp.linearCombination K fun b =>
    match b with
    | Sum.inl i => MarkChev.hVec S K i
    | Sum.inr α => ((∏ i, a i ^ α.1 i : Kˣ) : K) • Finsupp.single (Sum.inr α) 1

theorem largeEvenDiagMap_eq_markDiag {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (K : Type) [Field K]
    (a : Fin r → Kˣ) : LargeEvenDiagMap A K a = markDiag (LargeEvenIsRoot A) K a := by
  unfold LargeEvenDiagMap markDiag
  congr 1
  funext b
  cases b <;> rfl


theorem coe_torusElt_eq_markDiag (τ : Tag) (K : Type) [Field K] (i : Fin τ.rank) (t : Kˣ) :
    (torusElt τ K i t : Module.End K (RootModule τ K)) =
      markDiag (IsRoot τ) K (torusChar τ.cartan K i t) := by
  apply Finsupp.lhom_ext
  rintro (j | α) c
  · have h := torusElt_hVec (R := K) i j t
    rw [hVec] at h
    rw [show (Finsupp.single (Sum.inl j) c : RootModule τ K) =
      c • Finsupp.single (Sum.inl j) 1 by simp, map_smul, h]
    simp [markDiag, MarkChev.hVec]
  · have h := torusElt_rootVec (R := K) i t α.2
    have hrv : rootVec τ K α.1 = Finsupp.single (Sum.inr α) 1 := by simp [rootVec, α.2]
    rw [hrv] at h
    rw [show (Finsupp.single (Sum.inr α) c : RootModule τ K) =
      c • Finsupp.single (Sum.inr α) 1 by simp, map_smul, h]
    simp only [markDiag, map_smul, Finsupp.linearCombination_single, smul_smul]
    have e : (t ^ ∑ j, τ.cartan i j * α.1 j : Kˣ) = ∏ j, torusChar τ.cartan K i t j ^ α.1 j := by
      rw [zpow_finset_sum]
      exact Finset.prod_congr rfl fun j _ => by rw [torusChar, ← zpow_mul]
    rw [one_mul, e]

theorem exists_mem_chevGroup_markDiag (τ : Tag) (K : Type) [Field K] (S : (Fin τ.rank → ℤ) → Prop)
    (hS : S = IsRoot τ) (i : Fin τ.rank) (t : Kˣ) :
    ∃ g ∈ MarkChev.chevGroup τ.cartan S K,
      (g : Module.End K (MarkChev.Space S K)) = markDiag S K (torusChar τ.cartan K i t) := by
  subst hS
  refine ⟨torusElt τ K i t, ?_, coe_torusElt_eq_markDiag τ K i t⟩
  rw [← adjointGroup_eq_markChev]
  exact torusElt_mem_adjointGroup i t

theorem diagHom_torusChar_mem (τ : Tag) (K : Type) [Field K] (i : Fin τ.rank) (t : Kˣ) :
    diagHom τ.cartan K (torusChar τ.cartan K i t) ∈ LargeEvenChevGroup τ.cartan K := by
  obtain ⟨g, hg, hgd⟩ := exists_mem_chevGroup_markDiag τ K (LargeEvenIsRoot τ.cartan)
    (largeEvenIsRoot_eq_isRoot τ) i t
  rw [← largeEvenChevGroup_eq] at hg
  convert hg using 1
  apply Units.ext
  rw [coe_diagHom, hgd, largeEvenDiagMap_eq_markDiag]

theorem diagHom_mem_of_mem_torusSubgroup (τ : Tag) (K : Type) [Field K]
    {a : Fin τ.rank → Kˣ} (ha : a ∈ torusSubgroup τ.cartan K) :
    diagHom τ.cartan K a ∈ LargeEvenChevGroup τ.cartan K := by
  have hle : torusSubgroup τ.cartan K ≤
      (LargeEvenChevGroup τ.cartan K).comap (diagHom τ.cartan K) := by
    rw [torusSubgroup, Subgroup.closure_le]
    rintro _ ⟨⟨i, t⟩, rfl⟩
    exact diagHom_torusChar_mem τ K i t
  exact hle ha

end Transport

end TableB

end CFSG.StandardType
